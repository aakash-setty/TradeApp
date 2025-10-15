# app.py
from flask import Flask, render_template_string, jsonify, request
import requests, json, re, pytz
from icalendar import Calendar
from datetime import datetime, date, time, timedelta
from collections import defaultdict

app = Flask(__name__)

# Load calendars config
with open("calendars.json") as f:
    calendars = json.load(f)

EASTERN = pytz.timezone("America/New_York")

# -------------------------------
# Datetime helpers (with minute rounding)
# -------------------------------
def round_to_minute(dt: datetime) -> datetime:
    return dt.replace(second=0, microsecond=0)

def to_eastern(dt):
    """Return tz-aware datetime in Eastern. Date-only becomes midnight Eastern, then round to minute."""
    if isinstance(dt, date) and not isinstance(dt, datetime):
        naive_midnight = datetime.combine(dt, time(0, 0))
        localized = EASTERN.localize(naive_midnight)
    else:
        if dt.tzinfo is None:
            localized = EASTERN.localize(dt)
        else:
            localized = dt.astimezone(EASTERN)
    return round_to_minute(localized)

def iso(dt):
    return dt.astimezone(EASTERN).isoformat()

def future_cutoff():
    """
    Start-of-day (00:00) *tomorrow* in Eastern.
    Only shifts that START on/after this will be loaded/considered.
    """
    now_et = datetime.now(EASTERN)
    start_of_today = now_et.replace(hour=0, minute=0, second=0, microsecond=0)
    return start_of_today + timedelta(days=1)

# -------------------------------
# Eligibility rules
# -------------------------------
EXCLUDE_PATTERNS = [
    re.compile(r"trauma", re.IGNORECASE),
    re.compile(r"ultrasound", re.IGNORECASE),
    re.compile(r"\bUS\b", re.IGNORECASE),
    re.compile(r"sick\s*call", re.IGNORECASE),
]

ALLOW_PATTERNS = [
    r"\bday\s*[- ]?\s*([123])\b",
    r"\bd([123])\b",
    r"\beve?(ning)?\s*[- ]?\s*([123])\b",
    r"\be([123])\b",
    r"\bnight\s*[- ]?\s*([123])\b",
    r"\bn([123])\b",
    r"\bpod\s*[- ]?\s*a\s*[- ]?\s*([12])\b",
    r"\bpod\s*[- ]?\s*b\s*[- ]?\s*([12])\b",
    r"\bpoda\s*[- ]?\s*([12])\b",
    r"\bpodb\s*[- ]?\s*([12])\b",
    r"\bside\b",
    r"\b([abc])\s*([12])\b",
]
ALLOW_REGEXES = [re.compile(p, re.IGNORECASE) for p in ALLOW_PATTERNS]

def is_eligible_title(title: str) -> bool:
    if not title:
        return False
    for pat in EXCLUDE_PATTERNS:
        if pat.search(title):
            return False
    return any(rx.search(title) for rx in ALLOW_REGEXES)

# -------------------------------
# Normalize all shifts (FILTERS TO FUTURE—starts on/after tomorrow 00:00 ET)
# Robust to missing DTEND/DURATION and per-calendar failures.
# -------------------------------
def normalize_shifts(start_cutoff=None):
    """
    Returns:
      people: list[str]
      flat: list[shift dict] (ONLY future shifts whose *start* >= tomorrow 00:00 ET)
      schedules: dict[str, list[shift]]
    Shift dict:
      { id, person, title, start, end, eligible }
    """
    if start_cutoff is None:
        start_cutoff = future_cutoff()

    flat = []
    names = []

    for cal in calendars:
        names.append(cal["name"])
        try:
            resp = requests.get(cal["url"], timeout=15)
            resp.raise_for_status()
        except Exception as e:
            # Skip this calendar if fetch fails
            app.logger.warning(f"Calendar fetch failed for {cal.get('name')}: {e}")
            continue

        try:
            cal_obj = Calendar.from_ical(resp.text)
        except Exception as e:
            app.logger.warning(f"Calendar parse failed for {cal.get('name')}: {e}")
            continue

        for comp in cal_obj.walk():
            if comp.name != "VEVENT":
                continue

            try:
                dtstart_field = comp.get("dtstart")
                if not dtstart_field:
                    continue  # no start, skip
                start = to_eastern(dtstart_field.dt)

                # Try DTEND; if missing, use DURATION; fallback +1 hour
                dtend_field = comp.get("dtend")
                if dtend_field:
                    end = to_eastern(dtend_field.dt)
                else:
                    duration_field = comp.get("duration")
                    if duration_field:
                        # iCalendar duration -> timedelta
                        td = duration_field.dt if hasattr(duration_field, "dt") else duration_field
                        if not isinstance(td, timedelta):
                            # Defensive: if weird type, default
                            td = timedelta(hours=1)
                        end = to_eastern(start + td)
                    else:
                        end = to_eastern(start + timedelta(hours=1))

                # Ensure non-empty interval
                if end <= start:
                    continue

                # Only future shifts whose START >= cutoff
                if start < start_cutoff:
                    continue

                title = str(comp.get("summary", "") or "")
                shift = {
                    "id": f'{cal["name"]}|{iso(start)}|{iso(end)}|{title}',
                    "person": cal["name"],
                    "title": title,
                    "start": start,
                    "end": end,
                    "eligible": is_eligible_title(title),
                }
                flat.append(shift)
            except Exception as e:
                # Skip problematic event
                app.logger.warning(f"Skipping event in {cal.get('name')} due to error: {e}")
                continue

    schedules = defaultdict(list)
    for s in flat:
        schedules[s["person"]].append(s)
    for p in schedules:
        schedules[p].sort(key=lambda x: x["start"])

    people = sorted(set(names))
    return people, flat, schedules

# -------------------------------
# Interval and rules
# -------------------------------
def intervals_overlap(a_start, a_end, b_start, b_end):
    return (a_start < b_end) and (b_start < a_end)

def is_free_for_interval(person_shifts, interval_start, interval_end, exclude_id=None):
    for s in person_shifts:
        if exclude_id and s["id"] == exclude_id:
            continue
        if intervals_overlap(s["start"], s["end"], interval_start, interval_end):
            return False
    return True

def local_break_ok(sorted_shifts, idx):
    """
    Localized rest rule around the affected shift only:
      - gap(prev → cur) >= duration(prev)
      - gap(cur  → next) >= duration(cur)
    """
    cur = sorted_shifts[idx]
    prev = sorted_shifts[idx - 1] if idx > 0 else None
    nxt  = sorted_shifts[idx + 1] if idx + 1 < len(sorted_shifts) else None

    if prev:
        gap_prev = cur["start"] - prev["end"]
        dur_prev = prev["end"] - prev["start"]
        if gap_prev < dur_prev:
            return False

    if nxt:
        gap_cur = nxt["start"] - cur["end"]
        dur_cur = cur["end"] - cur["start"]
        if gap_cur < dur_cur:
            return False

    return True

# -------------------------------
# Swap helpers
# -------------------------------
def clone_for(new_person, s):
    return {
        **s,
        "person": new_person,
        "id": f'{new_person}|{iso(s["start"])}|{iso(s["end"])}|{s["title"]}',
    }

def swapped_schedules(schedules, trader_shift, tradee_shift):
    """
    Return (A_prime, B_prime, sB_for_A, sA_for_B) schedules after hypothetically swapping these two shifts.
    """
    A = trader_shift["person"]
    B = tradee_shift["person"]
    sA = trader_shift
    sB = tradee_shift

    A_sched = schedules[A]
    B_sched = schedules[B]

    sB_for_A = clone_for(A, sB)
    sA_for_B = clone_for(B, sA)

    A_prime = [x for x in A_sched if x["id"] != sA["id"]] + [sB_for_A]
    B_prime = [x for x in B_sched if x["id"] != sB["id"]] + [sA_for_B]
    A_prime.sort(key=lambda x: x["start"])
    B_prime.sort(key=lambda x: x["start"])
    return A_prime, B_prime, sB_for_A, sA_for_B

# -------------------------------
# 5+ off-day run detection (advisory)
# -------------------------------
def shift_start_dates_set(schedule_list):
    """Return a set of date() (ET) when shifts start."""
    return { s["start"].astimezone(EASTERN).date() for s in schedule_list }

def is_in_five_day_offrun(schedule_list, date_to_check):
    """
    date_to_check: a datetime.date (Eastern) to evaluate.
    We consider a day 'off' if the person has NO shift that STARTS on that date.
    We check the maximal consecutive off-days run containing date_to_check.
    """
    start_dates = shift_start_dates_set(schedule_list)

    # If they START a shift on this date, it's not an off day -> cannot be in an off-run.
    if date_to_check in start_dates:
        return False

    # Count backward/forward consecutive off days.
    run_len = 1
    # backward
    d = date_to_check
    while True:
        d = d - timedelta(days=1)
        if d in start_dates:
            break
        run_len += 1
        if run_len >= 12:  # guardrail
            break

    # forward
    d = date_to_check
    while True:
        d = d + timedelta(days=1)
        if d in start_dates:
            break
        run_len += 1
        if run_len >= 24:  # guardrail
            break

    return run_len >= 5

# -------------------------------
# Trade simulation (uses localized break rule)
# -------------------------------
def simulate_swap_ok(schedules, trader_shift, tradee_shift):
    # Eligibility
    if not (trader_shift["eligible"] and tradee_shift["eligible"]):
        return False, "ineligible-title"

    A = trader_shift["person"]
    B = tradee_shift["person"]
    if A == B:
        return False, "same-person"

    sA = trader_shift
    sB = tradee_shift

    A_sched = schedules[A]
    B_sched = schedules[B]

    # Availability before swap (ignore the shift they're giving up)
    if not is_free_for_interval(B_sched, sA["start"], sA["end"], exclude_id=sB["id"]):
        return False, "B-not-free-for-A"
    if not is_free_for_interval(A_sched, sB["start"], sB["end"], exclude_id=sA["id"]):
        return False, "A-not-free-for-B"

    # Simulate swap
    A_prime, B_prime, sB_for_A, sA_for_B = swapped_schedules(schedules, sA, sB)

    # Localized break checks only around the inserted shifts
    a_idx = A_prime.index(sB_for_A)
    b_idx = B_prime.index(sA_for_B)

    if not local_break_ok(A_prime, a_idx):
        return False, "A-break-rule"
    if not local_break_ok(B_prime, b_idx):
        return False, "B-break-rule"

    return True, "ok"

def advisory_offrun_flags_after_swap(schedules, trader_shift, tradee_shift):
    """
    Returns:
      (tradee_receives_on_offrun, trader_receives_on_offrun)
      Each True/False indicates whether the recipient receives their new shift
      on a date that belongs to a >=5-day off run (post-trade schedule).
    """
    A_prime, B_prime, sB_for_A, sA_for_B = swapped_schedules(schedules, trader_shift, tradee_shift)

    # Date to evaluate for each side is the START DATE (ET) of the received shift
    date_for_A = sB_for_A["start"].astimezone(EASTERN).date()
    date_for_B = sA_for_B["start"].astimezone(EASTERN).date()

    trader_receives_on_offrun = is_in_five_day_offrun(A_prime, date_for_A)
    tradee_receives_on_offrun = is_in_five_day_offrun(B_prime, date_for_B)

    return tradee_receives_on_offrun, trader_receives_on_offrun

# -------------------------------
# API: shifts (future only)
# -------------------------------
@app.route("/shifts.json")
def shifts_json():
    try:
        people, flat, _ = normalize_shifts()
    except Exception as e:
        app.logger.error(f"/shifts.json failed: {e}")
        # Never 500 to the client; return empty set so UI can render a friendly state
        return jsonify({"people": [], "shifts": []})

    out = []
    for s in flat:
        out.append({
            "id": s["id"],
            "person": s["person"],
            "title": s["title"],
            "start": iso(s["start"]),
            "end": iso(s["end"]),
            "eligible": s["eligible"],
        })
    return jsonify({"people": people, "shifts": out})

# -------------------------------
# API: trade options (future only) + advisory off-run flags
# -------------------------------
@app.route("/trade-options", methods=["POST"])
def trade_options():
    data = request.get_json(force=True, silent=True) or {}
    trader_person = data.get("trader_person")
    trader_shift_id = data.get("trader_shift_id")

    if not trader_person or not trader_shift_id:
        return jsonify({"error": "missing trader_person or trader_shift_id"}), 400

    _, flat, schedules = normalize_shifts()

    trader_shift = next((s for s in flat if s["id"] == trader_shift_id and s["person"] == trader_person), None)
    if not trader_shift:
        return jsonify({"error": "trader_shift not found"}), 404

    candidates = []
    for sB in flat:
        if sB["person"] == trader_person:
            continue
        ok, reason = simulate_swap_ok(schedules, trader_shift, sB)
        if ok:
            offrun_tradee, offrun_trader = advisory_offrun_flags_after_swap(schedules, trader_shift, sB)
            candidates.append({
                "tradee_person": sB["person"],
                "tradee_shift": {
                    "id": sB["id"],
                    "person": sB["person"],
                    "title": sB["title"],
                    "start": iso(sB["start"]),
                    "end": iso(sB["end"]),
                    "eligible": sB["eligible"],
                },
                "reason": reason,
                "vacation_hint": bool(offrun_tradee or offrun_trader),
                "vacation_detail": {
                    "tradee_receives_on_offrun": bool(offrun_tradee),
                    "trader_receives_on_offrun": bool(offrun_trader),
                }
            })

    candidates.sort(key=lambda c: (c["tradee_shift"]["start"], c["tradee_person"]))

    return jsonify({
        "trader_shift": {
            "id": trader_shift["id"],
            "person": trader_shift["person"],
            "title": trader_shift["title"],
            "start": iso(trader_shift["start"]),
            "end": iso(trader_shift["end"]),
            "eligible": trader_shift["eligible"],
        },
        "candidates": candidates
    })

# -------------------------------
# API: final recheck (future only)
# -------------------------------
@app.route("/trade-recheck", methods=["POST"])
def trade_recheck():
    data = request.get_json(force=True, silent=True) or {}
    trader_shift_id = data.get("trader_shift_id")
    tradee_shift_id = data.get("tradee_shift_id")
    if not trader_shift_id or not tradee_shift_id:
        return jsonify({"error": "missing ids"}), 400

    _, flat, schedules = normalize_shifts()
    sA = next((s for s in flat if s["id"] == trader_shift_id), None)
    sB = next((s for s in flat if s["id"] == tradee_shift_id), None)
    if not sA or not sB:
        return jsonify({"ok": False, "reason": "not-found"}), 404

    ok, reason = simulate_swap_ok(schedules, sA, sB)
    return jsonify({"ok": ok, "reason": reason})

# -------------------------------
# UI (Apple-inspired, theme toggle, loader, weekend badge, orange "?" off-run hint)
# -------------------------------
INDEX_HTML = """
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <title>JMH/HCH Shift Trading</title>
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <style>
    /* ===== Design tokens: light (default) ===== */
    :root{
      --bg: #fbfbfd;
      --fg: #1d1d1f;
      --muted: #6e6e73;
      --sep: rgba(60,60,67,0.12);
      --card: #ffffff;
      --accent: #0a84ff;
      --accent-pressed: #006bdf;
      --ring: rgba(10,132,255,.35);
      --shadow: 0 8px 30px rgba(0,0,0,.06);
      --radius: 14px;
      --success: #34c759;
      --danger: #ff3b30;
      --orange: #ff9f0a;
    }
    body.theme-dark{
      --bg: #000000;
      --fg: #f5f5f7;
      --muted: #a1a1a6;
      --sep: rgba(255,255,255,0.12);
      --card: #111113;
      --accent: #0a84ff;
      --accent-pressed: #3b99ff;
      --ring: rgba(10,132,255,.45);
      --shadow: 0 8px 30px rgba(0,0,0,.45);
      --success: #30d158;
      --danger: #ff453a;
      --orange: #ff9f0a;
    }

    html,body{height:100%}
    *{box-sizing:border-box}
    body{
      margin:0;
      font-family:-apple-system, BlinkMacSystemFont, "SF Pro Text", "SF Pro Display", system-ui, Segoe UI, Roboto, Helvetica, Arial, "Apple Color Emoji", "Segoe UI Emoji";
      color:var(--fg);
      background:var(--bg);
      -webkit-font-smoothing:antialiased; -moz-osx-font-smoothing:grayscale;
    }
    a{color:var(--accent); text-decoration:none}
    a:hover{opacity:.9}

    header{
      position:sticky; top:0; z-index:20;
      backdrop-filter:saturate(1.5) blur(18px);
      background:color-mix(in oklab, var(--bg) 80%, transparent);
      border-bottom:1px solid var(--sep);
    }
    .wrap{max-width:1080px; margin:0 auto; padding:18px 20px}
    .brand{display:flex; align-items:center; gap:12px;}
    .brand-badge{width:28px; height:28px; border-radius:8px; background:linear-gradient(135deg, var(--accent), #7cc3ff); box-shadow:0 4px 12px rgba(10,132,255,.35);}
    h1{margin:0; font-size:17px; font-weight:600; letter-spacing:.2px}

    .controls{
      display:grid; grid-template-columns:1fr 1.6fr auto auto; gap:12px; margin-top:12px; align-items:end;
    }
    @media (max-width: 900px){ .controls{grid-template-columns:1fr 1fr auto auto} }

    label{display:block; margin:0 0 6px 2px; font-size:12px; color:var(--muted); font-weight:600; letter-spacing:.02em;}
    select{
      width:100%; appearance:none;
      padding:10px 12px; border-radius:12px;
      color:var(--fg); background:var(--card);
      border:1px solid var(--sep); outline:none;
      box-shadow: var(--shadow);
      transition:border-color .2s, box-shadow .2s;
      background-image:url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 20 20" fill="%236e6e73"><path d="M5.5 7.5l4.5 4.5 4.5-4.5"/></svg>');
      background-repeat:no-repeat; background-position:right 10px center; background-size:14px;
    }
    select:focus{border-color:var(--accent); box-shadow:0 0 0 4px var(--ring)}
    .btn{
      padding:10px 14px; border-radius:12px; border:1px solid var(--sep);
      background:var(--card); color:var(--fg); font-weight:600; cursor:pointer;
      box-shadow: var(--shadow);
      transition: transform .06s ease, background .2s;
    }
    .btn:hover{background:color-mix(in oklab, var(--card) 85%, var(--fg) 15%)}
    .btn:active{transform: translateY(1px)}

    /* Theme segmented control (SVG day/night switch) */
    .seg{ display:inline-flex; border:1px solid var(--sep); border-radius:12px; overflow:hidden; background:var(--bg); align-self:end; padding:4px 8px }
    #theme-toggle-button{font-size: 17px; position:relative; display:inline-flex; align-items:center; width:7em; cursor:pointer}
    #toggle{opacity:0; width:0; height:0}
    #container, #patches, #stars, #button, #sun, #moon, #cloud{
      transition-property: all;
      transition-timing-function: cubic-bezier(0.4, 0, 0.2, 1);
      transition-duration: 0.25s;
    }
    #toggle:checked + svg #container { fill:#2b4360; }
    #toggle:checked + svg #button { transform: translate(28px, 2.333px); }
    #sun { opacity:1; }  #toggle:checked + svg #sun { opacity:0; }
    #moon{ opacity:0; }  #toggle:checked + svg #moon{ opacity:1; }
    #cloud{ opacity:1; } #toggle:checked + svg #cloud{ opacity:0; }
    #stars{ opacity:0; } #toggle:checked + svg #stars{ opacity:1; }

    main .wrap{display:grid; grid-template-columns:1.2fr 1.8fr; gap:16px; margin-top:18px}
    @media (max-width: 900px){ main .wrap{grid-template-columns:1fr} }

    .panel{background:var(--card); border:1px solid var(--sep); border-radius:var(--radius); box-shadow: var(--shadow); padding:16px 14px}
    .section-title{margin:0 0 10px 4px; font-size:15px; font-weight:700; letter-spacing:.2px}

    .legend{display:flex; gap:14px; align-items:center; margin-top:8px; color:var(--muted); font-size:12px; border-top:1px solid var(--sep); padding-top:10px}
    .legend span{white-space:nowrap}

    .shift-list{display:grid; gap:8px; max-height:58vh; overflow:auto; padding-right:4px}
    .card{
      display:flex; align-items:center; justify-content:space-between; gap:12px;
      background:linear-gradient(180deg, color-mix(in oklab, var(--card) 96%, transparent), color-mix(in oklab, var(--card) 92%, transparent));
      border:1px solid var(--sep); border-radius:12px; padding:12px 12px;
      transition: background .2s, transform .06s ease;
    }
    .card:hover{background:color-mix(in oklab, var(--card) 84%, white 16%)}
    .card:active{transform: translateY(1px)}
    .card.selectable{cursor:pointer}
    .card.is-selected{outline:2px solid var(--accent); outline-offset:2px}
    .meta{display:flex; flex-direction:column; gap:3px; min-width:0}
    .title{font-weight:600; font-size:14px; overflow:hidden; text-overflow:ellipsis; white-space:nowrap}
    .sub{color:var(--muted); font-size:12.5px}
    .chip{padding:6px 10px; border-radius:999px; border:1px solid var(--sep); background:var(--bg); font-size:12px; color:var(--muted)}
    .wk-badge{margin-left:8px; border:1px solid var(--danger); color:var(--danger); padding:3px 8px; border-radius:999px; font-size:11px; letter-spacing:.3px; text-transform:uppercase}

    .offer{padding:9px 12px; border-radius:12px; border:1px solid transparent; background:var(--accent); color:#fff; font-weight:700; cursor:pointer; box-shadow:0 6px 20px rgba(10,132,255,.35); transition: transform .06s ease, background .15s ease}
    .offer:hover{background:var(--accent-pressed)}
    .offer:active{transform: translateY(1px)}

    /* Orange “?” info badge */
    .info-badge{
      display:inline-flex; align-items:center; justify-content:center;
      width:22px; height:22px; border-radius:50%;
      background:var(--orange); color:#fff; font-weight:900; font-size:13px;
      border:none; margin-left:8px; cursor:pointer;
    }
    .info-badge:focus{outline:2px solid var(--ring); outline-offset:2px}

    .empty, .muted{color:var(--muted); font-size:13px; padding:10px 4px}

    /* Modal (Offer) */
    .modal-backdrop{position:fixed; inset:0; background:rgba(0,0,0,.22); display:none; align-items:center; justify-content:center; z-index:30}
    .modal{width:min(560px,94vw); border-radius:20px; border:1px solid var(--sep); background:var(--card); box-shadow:0 30px 80px rgba(0,0,0,.25); padding:20px 18px; animation: pop .18s ease}
    @keyframes pop{from{transform:scale(.98); opacity:0} to{transform:scale(1); opacity:1}}
    .modal h3{margin:0 0 12px; font-size:17px}
    .modal p{margin:6px 0; color:var(--fg); font-size:14px; line-height:1.38}
    .close{float:right; cursor:pointer; color:var(--muted); font-weight:700}
    .close:hover{color:var(--fg)}

    .seg-small{display:inline-flex; border:1px solid var(--sep); border-radius:12px; overflow:hidden; background:var(--bg)}
    .seg-small button{appearance:none; border:0; padding:8px 12px; background:transparent; color:var(--fg); font-weight:600; cursor:pointer}
    .seg-small button[aria-pressed="true"]{background:var(--accent); color:#fff}
    .msgbox{width:100%; min-height:120px; resize:vertical; padding:10px 12px; border-radius:12px; border:1px solid var(--sep); background:var(--card); color:var(--fg); font-size:14px; line-height:1.38; box-shadow: var(--shadow)}
    .copybtn{padding:8px 12px; border-radius:12px; border:1px solid var(--sep); background:var(--card); color:var(--fg); font-weight:700; cursor:pointer}
    .copybtn.copied{border-color: var(--success); color: var(--success)}

    /* Loader overlay + hamster animation (initial + during offer recheck) */
    .loader{position:fixed; inset:0; z-index:40; display:flex; align-items:center; justify-content:center; background:color-mix(in oklab, var(--bg) 70%, transparent); backdrop-filter: blur(22px) saturate(1.4)}
    .loader-card{width:min(520px,90vw); padding:18px; border-radius:20px; background:var(--card); border:1px solid var(--sep); box-shadow: var(--shadow)}
    .loader-head{display:flex; align-items:center; justify-content:space-between; margin-bottom:10px}
    .loader-title{font-weight:700}
    .loader-sub{color:var(--muted); font-size:12.5px; margin-top:8px}
    .loader-bar{height:10px; border-radius:999px; background:color-mix(in oklab, var(--bg) 60%, transparent); border:1px solid var(--sep); overflow:hidden}
    .loader-fill{height:100%; width:0%; background:linear-gradient(90deg, #0a84ff, #64d2ff); transition:width .2s ease}
    .loader-error .loader-fill{background:linear-gradient(90deg, #ff3b30, #ff6961)}
    .fade-out{animation:fadeOut .28s ease forwards}
    @keyframes fadeOut{to{opacity:0; visibility:hidden}}

    /* Hamster spinner (Uiverse by Nawsome) — FIXED keyframes */
    .wheel-and-hamster { --dur: 1s; position: relative; width: 12em; height: 12em; font-size: 14px; margin: 10px auto 0; }
    .wheel, .hamster, .hamster div, .spoke { position: absolute; }
    .wheel, .spoke { border-radius: 50%; top: 0; left: 0; width: 100%; height: 100%; }
    .wheel { background: radial-gradient(100% 100% at center,hsla(0,0%,60%,0) 47.8%,hsl(0,0%,60%) 48%); z-index: 2; }
    .hamster { animation: hamster var(--dur) ease-in-out infinite; top: 50%; left: calc(50% - 3.5em); width: 7em; height: 3.75em; transform: rotate(4deg) translate(-0.8em,1.85em); transform-origin: 50% 0; z-index: 1; }
    .hamster__head { animation: hamsterHead var(--dur) ease-in-out infinite; background: hsl(30,90%,55%); border-radius: 70% 30% 0 100% / 40% 25% 25% 60%; box-shadow: 0 -0.25em 0 hsl(30,90%,80%) inset, 0.75em -1.55em 0 hsl(30,90%,90%) inset; top: 0; left: -2em; width: 2.75em; height: 2.5em; transform-origin: 100% 50%; }
    .hamster__ear { animation: hamsterEar var(--dur) ease-in-out infinite; background: hsl(0,90%,85%); border-radius: 50%; box-shadow: -0.25em 0 hsl(30,90%,55%) inset; top: -0.25em; right: -0.25em; width: 0.75em; height: 0.75em; transform-origin: 50% 75%; }
    .hamster__eye { animation: hamsterEye var(--dur) linear infinite; background-color: hsl(0,0%,0%); border-radius: 50%; top: 0.375em; left: 1.25em; width: 0.5em; height: 0.5em; }
    .hamster__nose { background: hsl(0,90%,75%); border-radius: 35% 65% 85% 15% / 70% 50% 50% 30%; top: 0.75em; left: 0; width: 0.2em; height: 0.25em; }
    .hamster__body { animation: hamsterBody var(--dur) ease-in-out infinite; background: hsl(30,90%,90%); border-radius: 50% 30% 50% 30% / 15% 60% 40% 40%; box-shadow: 0.1em 0.75em 0 hsl(30,90%,55%) inset, 0.15em -0.5em 0 hsl(30,90%,80%) inset; top: 0.25em; left: 2em; width: 4.5em; height: 3em; transform-origin: 17% 50%; transform-style: preserve-3d; }
    .hamster__limb--fr, .hamster__limb--fl { clip-path: polygon(0 0,100% 0,70% 80%,60% 100%,0% 100%,40% 80%); top: 2em; left: 0.5em; width: 1em; height: 1.5em; transform-origin: 50% 0; }
    .hamster__limb--fr { animation: hamsterFRLimb var(--dur) linear infinite; background: linear-gradient(hsl(30,90%,80%) 80%,hsl(0,90%,75%) 80%); transform: rotate(15deg) translateZ(-1px); }
    .hamster__limb--fl { animation: hamsterFLLimb var(--dur) linear infinite; background: linear-gradient(hsl(30,90%,90%) 80%,hsl(0,90%,85%) 80%); transform: rotate(15deg); }
    .hamster__limb--br, .hamster__limb--bl { border-radius: 0.75em 0.75em 0 0; clip-path: polygon(0 0,100% 0,100% 30%,70% 90%,70% 100%,30% 100%,40% 90%,0% 30%); top: 1em; left: 2.8em; width: 1.5em; height: 2.5em; transform-origin: 50% 30%; }
    .hamster__limb--br { animation: hamsterBRLimb var(--dur) linear infinite; background: linear-gradient(hsl(30,90%,80%) 90%,hsl(0,90%,75%) 90%); transform: rotate(-25deg) translateZ(-1px); }
    .hamster__limb--bl { animation: hamsterBLLimb var(--dur) linear infinite; background: linear-gradient(hsl(30,90%,90%) 90%,hsl(0,90%,85%) 90%); transform: rotate(-25deg); }
    .hamster__tail { animation: hamsterTail var(--dur) linear infinite; background: hsl(0,90%,85%); border-radius: 0.25em 50% 50% 0.25em; box-shadow: 0 -0.2em 0 hsl(0,90%,75%) inset; top: 1.5em; right: -0.5em; width: 1em; height: 0.5em; transform: rotate(30deg) translateZ(-1px); transform-origin: 0.25em 0.25em; }
    .spoke { animation: spoke var(--dur) linear infinite; background: radial-gradient(100% 100% at center,hsl(0,0%,60%) 4.8%,hsla(0,0%,60%,0) 5%), linear-gradient(hsla(0,0%,55%,0) 46.9%,hsl(0,0%,65%) 47% 52.9%,hsla(0,0%,65%,0) 53%) 50% 50% / 99% 99% no-repeat; }

    @keyframes hamster {
      from, to { transform: rotate(4deg) translate(-0.8em,1.85em); }
      50%      { transform: rotate(0) translate(-0.8em,1.85em); }
    }
    @keyframes hamsterHead {
      from, 25%, 50%, 75%, to { transform: rotate(0); }
      12.5%, 37.5%, 62.5%, 87.5% { transform: rotate(8deg); }
    }
    @keyframes hamsterEye {
      from, 90%, to { transform: scaleY(1); }
      95%           { transform: scaleY(0); }
    }
    @keyframes hamsterEar {
      from, 25%, 50%, 75%, to { transform: rotate(0); }
      12.5%, 37.5%, 62.5%, 87.5% { transform: rotate(12deg); }
    }
    @keyframes hamsterBody {
      from, 25%, 50%, 75%, to { transform: rotate(0); }
      12.5%, 37.5%, 62.5%, 87.5% { transform: rotate(-2deg); }
    }
    @keyframes hamsterFRLimb {
      from, 25%, 50%, 75%, to { transform: rotate(50deg) translateZ(-1px); }
      12.5%, 37.5%, 62.5%, 87.5% { transform: rotate(-30deg) translateZ(-1px); }
    }
    @keyframes hamsterFLLimb {
      from, 25%, 50%, 75%, to { transform: rotate(-30deg); }
      12.5%, 37.5%, 62.5%, 87.5% { transform: rotate(50deg); }
    }
    @keyframes hamsterBRLimb {
      from, 25%, 50%, 75%, to { transform: rotate(-60deg) translateZ(-1px); }
      12.5%, 37.5%, 62.5%, 87.5% { transform: rotate(20deg) translateZ(-1px); }
    }
    @keyframes hamsterBLLimb {
      from, 25%, 50%, 75%, to { transform: rotate(20deg); }
      12.5%, 37.5%, 62.5%, 87.5% { transform: rotate(-60deg); }
    }
    @keyframes hamsterTail {
      from, 25%, 50%, 75%, to { transform: rotate(30deg) translateZ(-1px); }
      12.5%, 37.5%, 62.5%, 87.5% { transform: rotate(10deg) translateZ(-1px); }
    }
    @keyframes spoke {
      from { transform: rotate(0); }
      to   { transform: rotate(-1turn); }
    }
  </style>
</head>

<body class="theme-light">
  <!-- Loader -->
  <div id="loader" class="loader" role="status" aria-live="polite" aria-label="Loading schedules">
    <div class="loader-card" id="loaderCard">
      <div class="loader-head">
        <div class="brand" style="gap:10px;">
          <div class="brand-badge"></div>
          <div class="loader-title">Preparing Shift Trading</div>
        </div>
        <div id="loaderPct" class="loader-title">0%</div>
      </div>
      <div class="loader-bar"><div id="loaderFill" class="loader-fill"></div></div>
      <div class="loader-sub" id="loaderSub">Fetching calendars and building options…</div>

      <!-- cute spinner -->
      <div class="wheel-and-hamster" aria-hidden="true">
        <div class="wheel"></div>
        <div class="hamster">
          <div class="hamster__body">
            <div class="hamster__head">
              <div class="hamster__ear"></div>
              <div class="hamster__eye"></div>
              <div class="hamster__nose"></div>
            </div>
            <div class="hamster__limb hamster__limb--fr"></div>
            <div class="hamster__limb hamster__limb--fl"></div>
            <div class="hamster__limb hamster__limb--br"></div>
            <div class="hamster__limb hamster__limb--bl"></div>
            <div class="hamster__tail"></div>
          </div>
        </div>
        <div class="spoke"></div>
      </div>
    </div>
  </div>

  <header>
    <div class="wrap">
      <div class="brand">
        <div class="brand-badge"></div>
        <h1>JMH/HCH Shift Trading</h1>
      </div>

      <div class="controls">
        <div>
          <label for="me">Your Name</label>
          <select id="me"></select>
        </div>
        <div>
          <label for="myshift">Your Tradable Shift</label>
          <select id="myshift"></select>
        </div>
        <div style="justify-self:end">
          <button id="refresh" class="btn" aria-label="Refresh schedules">Refresh</button>
        </div>

        <!-- Theme switch (SVG) -->
        <div class="seg">
          <label id="theme-toggle-button">
            <input id="toggle" type="checkbox" aria-label="Toggle theme">
            <!-- SVG adapted to container -->
            <svg viewBox="0 0 80 32" width="112" height="32" aria-hidden="true">
              <rect id="container" x="0" y="0" width="80" height="32" rx="16" fill="#e6f0ff"/>
              <g id="patches">
                <circle id="sun" cx="20" cy="16" r="6" fill="#FFD60A"/>
                <circle id="moon" cx="60" cy="16" r="6" fill="#F2F2F7"/>
              </g>
              <g id="cloud">
                <ellipse cx="28" cy="12" rx="4" ry="2" fill="#fff"/>
                <ellipse cx="32" cy="12" rx="4" ry="2" fill="#fff"/>
                <ellipse cx="30" cy="11" rx="5" ry="3" fill="#fff"/>
              </g>
              <g id="stars" fill="#fff">
                <circle cx="52" cy="10" r="1"/>
                <circle cx="58" cy="8"  r="1"/>
                <circle cx="66" cy="12" r="1"/>
              </g>
              <rect id="button" x="2" y="2" width="28" height="28" rx="14" fill="#fff"/>
            </svg>
          </label>
        </div>
      </div>

      <div class="legend">
        <span>Select your name and click a shift you want to trade away.</span>
        <span>Excluded: Trauma / Ultrasound / “US” / Sick Call</span>
        <span>Hopefully this is accurate but may contain errors</span>
      </div>
    </div>
  </header>

  <main>
    <div class="wrap">
      <section class="panel">
        <h2 class="section-title">Your Tradable Shifts</h2>
        <div class="shift-list" id="mine"></div>
      </section>

      <section class="panel">
        <h2 class="section-title">Valid Trade Options</h2>
        <div id="results"></div>
      </section>
    </div>
  </main>

  <!-- Offer modal -->
  <div class="modal-backdrop" id="mb" aria-modal="true" role="dialog">
    <div class="modal">
      <span class="close" id="closex" aria-label="Close">✕</span>
      <h3>Propose Trade</h3>
      <p id="modaldesc" class="muted" style="margin-top:-4px"></p>
      <div style="display:flex; align-items:center; justify-content:space-between; margin:10px 0 8px;">
        <div class="seg-small" role="tablist" aria-label="Message tone">
          <button id="tonePro" role="tab" aria-pressed="true">Professional</button>
          <button id="toneDes" role="tab" aria-pressed="false">Desperate</button>
          <button id="toneSil" role="tab" aria-pressed="false">Silly</button>
        </div>
        <button id="copyBtn" class="copybtn" aria-label="Copy message">Copy</button>
      </div>
      <textarea id="msgbox" class="msgbox" readonly></textarea>
      <p class="muted" style="color:var(--muted)">Copy and paste this into your preferred channel to complete the trade privately.</p>
    </div>
  </div>

  <!-- Orange “?” info modal -->
  <div class="modal-backdrop" id="infoBackdrop" aria-modal="true" role="dialog">
    <div class="modal" id="infoModal">
      <span class="close" id="infoClose" aria-label="Close">✕</span>
      <h3>About this “?”</h3>
      <p id="infoText">
        This orange question mark indicates that the received shift would fall on a stretch of at least
        five consecutive off days (no shifts starting that day) for the recipient, based on the hypothetical
        post-trade schedules in Eastern time.
      </p>
    </div>
  </div>

  <script>
    const $ = (sel) => document.querySelector(sel);

    // Fail-safe: surface JS errors on the loader so it never "silently" hangs
    window.addEventListener('error', (e)=>{
      const loader = document.getElementById('loader');
      const loaderSub = document.getElementById('loaderSub');
      const loaderCard = document.getElementById('loaderCard');
      if(loader && loaderSub && loaderCard){
        loader.style.display = 'flex';
        loaderCard.classList.add('loader-error');
        loaderSub.textContent = 'JS Error: ' + (e.message || 'Unknown error');
      }
    });

    /* Loader */
    const loader = $("#loader");
    const loaderFill = $("#loaderFill");
    const loaderPct = $("#loaderPct");
    const loaderSub = $("#loaderSub");
    const loaderCard = $("#loaderCard");
    let loaderTimer = null, loaderProgress = 0;

    function setLoader(p){
      loaderProgress = Math.max(0, Math.min(100, Math.floor(p)));
      loaderFill.style.width = loaderProgress + "%";
      loaderPct.textContent = loaderProgress + "%";
    }
    function showLoader(msg){
      loader.style.display = "flex";
      if (msg) loaderSub.textContent = msg;
      setLoader(6);
      clearInterval(loaderTimer);
      loaderTimer = setInterval(()=>{
        if (loaderProgress < 90) setLoader(loaderProgress + Math.max(1, Math.ceil((90 - loaderProgress)/14)));
      }, 160);
    }
    function hideLoader(){
      clearInterval(loaderTimer);
      setLoader(100);
      setTimeout(()=>{
        loader.classList.add("fade-out");
        setTimeout(()=>{ loader.style.display = "none"; loader.classList.remove("fade-out"); setLoader(0); }, 300);
      }, 150);
    }
    function showLoaderError(msg){
      clearInterval(loaderTimer);
      loaderCard.classList.add("loader-error");
      loaderSub.textContent = msg || "Something went wrong while loading schedules.";
      setLoader(100);
    }

    /* Theme: default day, remember choice */
    const themeToggle = $("#toggle");
    function applyThemeFromToggle(){
      const isNight = themeToggle.checked;
      document.body.classList.toggle("theme-dark", isNight);
      document.body.classList.toggle("theme-light", !isNight);
      try { localStorage.setItem("shift-theme", isNight ? "night" : "day"); } catch(e){}
    }
    function initTheme(){
      let saved = null;
      try { saved = localStorage.getItem("shift-theme"); } catch(e){}
      const useNight = (saved === "night");
      themeToggle.checked = useNight;
      applyThemeFromToggle();
    }
    themeToggle.addEventListener("change", applyThemeFromToggle);

    /* App els */
    const meSel = $("#me");
    const myShiftSel = $("#myshift");
    const mineList = $("#mine");
    const results = $("#results");
    const modal = $("#mb");
    const closex = $("#closex");
    const modaldesc = $("#modaldesc");
    const msgbox = $("#msgbox");
    const copyBtn = $("#copyBtn");
    const tonePro = $("#tonePro");
    const toneDes = $("#toneDes");
    const toneSil = $("#toneSil");

    // Info modal elements
    const infoBackdrop = $("#infoBackdrop");
    const infoClose = $("#infoClose");
    const infoText = $("#infoText");

    let SHIFTS = [];
    let PEOPLE = [];
    let CURRENT_TRADE = null;

    function fmt(dtiso){
      const d = new Date(dtiso);
      const opts = {weekday:'short', month:'short', day:'numeric'};
      const dstr = d.toLocaleDateString(undefined, opts);
      const t = d.toLocaleTimeString(undefined, {hour:'numeric', minute:'2-digit'});
      return { d, dstr, t };
    }
    function hoursBetweenISO(a,b){ return (new Date(b) - new Date(a))/3600000; }
    function escapeHTML(s){ return s.replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c])); }
    function isWeekendStart(isoStr){
      const d = new Date(isoStr);
      const dow = d.getDay(); // 0=Sun, 5=Fri, 6=Sat
      const hr = d.getHours();
      return (dow === 5 && hr >= 19) || dow === 6 || dow === 0;
    }
    function weekendBadgeEl(isoStr){
      if (!isWeekendStart(isoStr)) return null;
      const badge = document.createElement("span");
      badge.className = "wk-badge";
      badge.textContent = "Weekend";
      return badge;
    }

    function selectMyShift(shiftId){
      if(!shiftId) return;
      myShiftSel.value = shiftId;
      document.querySelectorAll('#mine .card.selectable').forEach(c => {
        c.classList.toggle('is-selected', c.dataset.shiftId === shiftId);
      });
      fetchOptions();
    }

    async function loadShifts(){
      showLoader("Starting up…");
      try{
        setLoader(12);
        loaderSub.textContent = "Contacting server…";
        const r = await fetch("/shifts.json");
        setLoader(42);
        if (!r.ok){
          showLoaderError("Server error while fetching schedules.");
          return;
        }
        loaderSub.textContent = "Parsing data…";
        const data = await r.json();
        setLoader(72);

        loaderSub.textContent = "Preparing interface…";
        PEOPLE = data.people;
        SHIFTS = data.shifts; // server already filters to future
        setLoader(86);

        populatePeople();
        populateMyShifts();
        await fetchOptions();
        hideLoader();
      } catch (e){
        console.error(e);
        showLoaderError("Network error while loading schedules.");
      }
    }

    function populatePeople(){
      meSel.innerHTML = "";
      PEOPLE.forEach(p=>{
        const opt = document.createElement("option");
        opt.value = p; opt.textContent = p;
        meSel.appendChild(opt);
      });
    }

    function myEligibleShifts(person){
      return SHIFTS.filter(s => s.person === person && s.eligible);
    }

    function populateMyShifts(){
      const person = meSel.value;
      const mine = myEligibleShifts(person).sort((a,b)=>a.start.localeCompare(b.start));
      myShiftSel.innerHTML = "";
      mine.forEach(s=>{
        const f1 = fmt(s.start), f2 = fmt(s.end);
        const dur = hoursBetweenISO(s.start, s.end).toFixed(1);
        const opt = document.createElement("option");
        opt.value = s.id;
        opt.textContent = `${s.title} • ${f1.dstr} ${f1.t} → ${f2.t} (${dur}h)`;
        myShiftSel.appendChild(opt);
      });

      mineList.innerHTML = "";
      mine.forEach(s=>{
        const f1 = fmt(s.start), f2 = fmt(s.end);
        const dur = hoursBetweenISO(s.start, s.end).toFixed(1);
        const card = document.createElement("div");
        card.className = "card selectable";
        card.dataset.shiftId = s.id;
        card.tabIndex = 0;
        card.setAttribute("role","button");
        card.setAttribute("aria-label", `Choose ${s.title} ${f1.dstr} ${f1.t} to ${f2.t}`);

        const meta = document.createElement("div");
        meta.className = "meta";
        const title = document.createElement("div");
        title.className = "title"; title.textContent = s.title;
        const subRow = document.createElement("div");
        subRow.className = "sub"; subRow.textContent = `${f1.dstr} ${f1.t} · ${f2.t} • ${dur}h`;
        const wk = weekendBadgeEl(s.start);
        if (wk){ subRow.appendChild(document.createTextNode(" ")); subRow.appendChild(wk); }
        meta.appendChild(title); meta.appendChild(subRow);

        const chip = document.createElement("div");
        chip.className = "chip"; chip.textContent = s.eligible ? "Eligible" : "Not eligible";

        card.appendChild(meta); card.appendChild(chip);

        const choose = ()=> selectMyShift(s.id);
        card.addEventListener("click", choose);
        card.addEventListener("keydown", (e)=>{ if (e.key === "Enter" || e.key === " ") { e.preventDefault(); choose(); } });
        mineList.appendChild(card);
      });

      const firstId = mine[0]?.id;
      const current = myShiftSel.value || firstId;
      if (current) selectMyShift(current);
    }

    // Outreach message builder
    function buildMessage(tone, me, partner, myShift, theirShift){
      const myF1 = fmt(myShift.start), myF2 = fmt(myShift.end);
      const thF1 = fmt(theirShift.start), thF2 = fmt(theirShift.end);
      const giveLine = `${myShift.title} — ${myF1.dstr} ${myF1.t} → ${myF2.t}`;
      const getLine  = `${theirShift.title} — ${thF1.dstr} ${thF1.t} → ${thF2.t}`;

      const baseFooter = "If that works for you, I’ll send a quick confirm. Thanks!";
      const professional =
`Hi ${partner},
Would you be open to a shift trade? It would be greatly appreciated.

I’d trade you my:
• ${giveLine}
And take your:
• ${getLine}

The swap passes our scheduling rules. ${baseFooter}
— ${me}`;
      const desperate =
`Hey ${partner} 🙏
Any chance you'd swap with me?

I’d give you:
• ${giveLine}

And I’d take:
• ${getLine}
You’d be saving my week — and it should be fully valid per the rules. Please say yes! 🤞
— ${me}`;
      const silly =
`yo ${partner} 🎉

You down for a trade-sie-poo?

I give you:
• ${giveLine}
you present to me your:
• ${getLine}

computers say it’s legit (i'm p sure) ✅
lmk and I’ll make it official 😎
— ${me}`;

      if (tone === "desperate") return desperate;
      if (tone === "silly") return silly;
      return professional;
    }

    function setTone(active){
      [tonePro, toneDes, toneSil].forEach(btn => btn.setAttribute("aria-pressed", "false"));
      if (active === "professional") tonePro.setAttribute("aria-pressed","true");
      if (active === "desperate")    toneDes.setAttribute("aria-pressed","true");
      if (active === "silly")        toneSil.setAttribute("aria-pressed","true");

      if (CURRENT_TRADE){
        const { me, partner, myShift, theirShift } = CURRENT_TRADE;
        msgbox.value = buildMessage(
          active === "desperate" ? "desperate" : active === "silly" ? "silly" : "professional",
          me, partner, myShift, theirShift
        );
      }
    }

    function setCopyState(ok){
      copyBtn.classList.toggle("copied", !!ok);
      copyBtn.textContent = ok ? "Copied ✓" : "Copy";
    }

    async function fetchOptions(){
      const person = meSel.value;
      const shiftId = myShiftSel.value;
      if (!shiftId){
        results.innerHTML = `<div class="empty">Select a shift above.</div>`;
        return;
      }
      results.innerHTML = `<div class="muted">Finding valid trades…</div>`;
      const r = await fetch("/trade-options",{
        method:"POST",
        headers: {"Content-Type":"application/json"},
        body: JSON.stringify({ trader_person: person, trader_shift_id: shiftId })
      });
      if(!r.ok){
        const t = await r.text();
        results.innerHTML = `<div class="empty">Error: ${escapeHTML(t)}</div>`;
        return;
      }
      const data = await r.json();
      const all = data.candidates
        .map(c => ({ partner: c.tradee_person, shift: c.tradee_shift, vacation: c.vacation_hint, vdetail: c.vacation_detail }))
        .sort((a,b)=> a.shift.start.localeCompare(b.shift.start));

      results.innerHTML = "";
      if (all.length === 0){
        results.innerHTML = `<div class="empty">No valid trades found right now.</div>`;
        return;
      }

      const personName = meSel.value;
      const mine = SHIFTS.find(x => x.id === shiftId);

      all.forEach(({partner, shift: s, vacation, vdetail})=>{
        const f1 = fmt(s.start), f2 = fmt(s.end);
        const dur = hoursBetweenISO(s.start, s.end).toFixed(1);

        const card = document.createElement("div");
        card.className = "card";

        const meta = document.createElement("div");
        meta.className = "meta";
        const title = document.createElement("div");
        title.className = "title";
        title.textContent = s.title;

        const subRow = document.createElement("div");
        subRow.className = "sub";
        subRow.textContent = `${f1.dstr} ${f1.t} · ${f2.t} • ${dur}h`;

        const wk = weekendBadgeEl(s.start);
        if (wk){ subRow.appendChild(document.createTextNode(" ")); subRow.appendChild(wk); }

        meta.appendChild(title); meta.appendChild(subRow);

        const rightWrap = document.createElement("div");
        rightWrap.style.display = "flex";
        rightWrap.style.alignItems = "center";

        if (vacation){
          const infoBtn = document.createElement("button");
          infoBtn.className = "info-badge";
          infoBtn.type = "button";
          infoBtn.title = "Possible vacation/off-service context";
          infoBtn.textContent = "?";
          infoBtn.addEventListener("click", ()=>{
            const parts = [];
            if (vdetail?.tradee_receives_on_offrun) parts.push(`${partner} would receive your shift during a ≥5-day off stretch.`);
            if (vdetail?.trader_receives_on_offrun) parts.push(`You would receive their shift during a ≥5-day off stretch.`);
            const extra = parts.length ? "\\n\\nDetails:\\n– " + parts.join("\\n– ") : "";
            infoText.textContent =
`This orange question mark indicates that the received shift falls on a stretch of at least five consecutive off days (no shifts starting that day) for the recipient, based on the hypothetical post-trade schedules in Eastern time.${extra}`;
            $("#infoBackdrop").style.display = "flex";
          });
          rightWrap.appendChild(infoBtn);
        }

        const offer = document.createElement("button");
        offer.className = "offer";
        offer.textContent = "Offer";
        offer.onclick = async ()=>{
          // Show loader overlay while rechecking
          showLoader("Rechecking rules…");
          const r2 = await fetch("/trade-recheck",{
            method:"POST",
            headers: {"Content-Type":"application/json"},
            body: JSON.stringify({ trader_shift_id: mine.id, tradee_shift_id: s.id })
          });
          const data2 = await r2.json();
          hideLoader();
          if (data2.ok){
            CURRENT_TRADE = { me: personName, partner, myShift: mine, theirShift: s };
            modal.style.display = "flex";
            const myF1b = fmt(mine.start), myF2b = fmt(mine.end);
            const thF1b = fmt(s.start), thF2b = fmt(s.end);
            modaldesc.textContent = `${personName} → ${partner} • Offer: ${mine.title} (${myF1b.dstr} ${myF1b.t} → ${myF2b.t}) ↔ Receive: ${s.title} (${thF1b.dstr} ${thF1b.t} → ${thF2b.t})`;
            setTone("professional");
            setCopyState(false);
          } else {
            alert("This pair failed recheck: " + data2.reason);
          }
        };

        rightWrap.appendChild(offer);

        card.appendChild(meta);
        card.appendChild(rightWrap);
        results.appendChild(card);
      });
    }

    /* Listeners */
    meSel.addEventListener("change", ()=>{ populateMyShifts(); });
    myShiftSel.addEventListener("change", ()=> selectMyShift(myShiftSel.value));
    $("#refresh").addEventListener("click", loadShifts);

    // Offer modal close
    closex.addEventListener("click", ()=> modal.style.display = "none");
    modal.addEventListener("click", (e)=>{ if(e.target === modal) modal.style.display = "none"; });

    // Info modal close
    infoClose.addEventListener("click", ()=> $("#infoBackdrop").style.display = "none");
    $("#infoBackdrop").addEventListener("click", (e)=>{ if(e.target === $("#infoBackdrop")) $("#infoBackdrop").style.display = "none"; });

    // Tone + Copy
    tonePro.addEventListener("click", ()=> setTone("professional"));
    toneDes.addEventListener("click", ()=> setTone("desperate"));
    toneSil.addEventListener("click", ()=> setTone("silly"));

    copyBtn.addEventListener("click", async ()=>{
      try{
        await navigator.clipboard.writeText(msgbox.value || "");
        setCopyState(true);
        setTimeout(()=> setCopyState(false), 1600);
      } catch(e){
        setCopyState(false);
        alert("Copy failed. You can still select and copy manually.");
      }
    });

    (function init(){
      initTheme();
      loadShifts();
    })();
  </script>
</body>
</html>
"""

@app.route("/")
def index():
    return render_template_string(INDEX_HTML)

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5002, debug=True)
