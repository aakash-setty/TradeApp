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

# -------------------------------------------------
# Small in-memory cache to speed repeated requests
# -------------------------------------------------
_CACHE = None
_CACHE_TTL_SECONDS = 120  # adjust as desired


# -------------------------------
# Datetime helpers
# -------------------------------
def round_to_minute(dt: datetime) -> datetime:
    return dt.replace(second=0, microsecond=0)

def to_eastern(dt):
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
    """Start-of-day (00:00) *tomorrow* in Eastern; only shifts starting on/after will be loaded."""
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
# Normalize all shifts (FUTURE ONLY: start >= tomorrow 00:00 ET)
# -------------------------------
def normalize_shifts(start_cutoff=None):
    """
    Returns:
      people: list[str]
      flat: list[shift dict]  (future-only)
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
        resp = requests.get(cal["url"], timeout=12)
        resp.raise_for_status()
        cal_obj = Calendar.from_ical(resp.text)

        for comp in cal_obj.walk():
            if comp.name != "VEVENT":
                continue

            start = to_eastern(comp.decoded("dtstart"))
            end = to_eastern(comp.decoded("dtend"))  # exclusive by spec
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

    schedules = defaultdict(list)
    for s in flat:
        schedules[s["person"]].append(s)
    for p in schedules:
        schedules[p].sort(key=lambda x: x["start"])

    people = sorted(set(names))
    return people, flat, schedules


def load_data_cached():
    """Return (people, flat, schedules), using a short-lived in-memory cache."""
    global _CACHE
    now = datetime.now(EASTERN)
    if _CACHE is not None:
        ts = _CACHE.get("ts")
        if ts and (now - ts).total_seconds() < _CACHE_TTL_SECONDS:
            return _CACHE["people"], _CACHE["flat"], _CACHE["schedules"]
    people, flat, schedules = normalize_shifts()
    _CACHE = {"ts": now, "people": people, "flat": flat, "schedules": schedules}
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
    Localized rest rule around affected shift only:
      - gap(prev→cur) >= duration(prev)
      - gap(cur →next) >= duration(cur)
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
# Trade simulation (+ 60h cap rule after swap)
# -------------------------------
def simulate_swap_ok(schedules, trader_shift, tradee_shift):
    # Titles must be eligible (allow-list) and not excluded
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

    # Availability (ignore the shift they are giving up)
    if not is_free_for_interval(B_sched, sA["start"], sA["end"], exclude_id=sB["id"]):
        return False, "B-not-free-for-A"
    if not is_free_for_interval(A_sched, sB["start"], sB["end"], exclude_id=sA["id"]):
        return False, "A-not-free-for-B"

    # Simulate swap (change owners)
    def clone_for(new_person, s):
        return {
            **s,
            "person": new_person,
            "id": f'{new_person}|{iso(s["start"])}|{iso(s["end"])}|{s["title"]}',
        }

    sB_for_A = clone_for(A, sB)
    sA_for_B = clone_for(B, sA)

    A_prime = [x for x in A_sched if x["id"] != sA["id"]] + [sB_for_A]
    B_prime = [x for x in B_sched if x["id"] != sB["id"]] + [sA_for_B]
    A_prime.sort(key=lambda x: x["start"])
    B_prime.sort(key=lambda x: x["start"])

    # Localized rest checks
    a_idx = A_prime.index(sB_for_A)
    b_idx = B_prime.index(sA_for_B)

    if not local_break_ok(A_prime, a_idx):
        return False, "A-break-rule"
    if not local_break_ok(B_prime, b_idx):
        return False, "B-break-rule"

    # Weekly cap (<= 60h) check for both around the new shift's week
    def week_caps_ok(prime_sched, new_shift):
        start = new_shift["start"]
        weekday = start.weekday()  # Monday=0
        week_start = (start - timedelta(days=weekday)).replace(hour=0, minute=0, second=0, microsecond=0)
        week_end = week_start + timedelta(days=7)
        total = 0.0
        for s in prime_sched:
            if week_start <= s["start"] < week_end:
                total += (s["end"] - s["start"]).total_seconds() / 3600.0
        return total <= 60.0

    if not week_caps_ok(A_prime, sB_for_A):
        return False, "A-weekly-cap"
    if not week_caps_ok(B_prime, sA_for_B):
        return False, "B-weekly-cap"

    return True, "ok"


# -------------------------------
# API: shifts (future only)
# -------------------------------
@app.route("/shifts.json")
def shifts_json():
    people, flat, _ = load_data_cached()
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
# API: trade options (future only)
# -------------------------------
@app.route("/trade-options", methods=["POST"])
def trade_options():
    data = request.get_json(force=True, silent=True) or {}
    trader_person = data.get("trader_person")
    trader_shift_id = data.get("trader_shift_id")

    if not trader_person or not trader_shift_id:
        return jsonify({"error": "missing trader_person or trader_shift_id"}), 400

    _, flat, schedules = load_data_cached()

    trader_shift = next((s for s in flat if s["id"] == trader_shift_id and s["person"] == trader_person), None)
    if not trader_shift:
        return jsonify({"error": "trader_shift not found"}), 404

    candidates = []
    for sB in flat:
        if sB["person"] == trader_person:
            continue
        ok, reason = simulate_swap_ok(schedules, trader_shift, sB)
        if ok:
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
                "reason": reason
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

    _, flat, schedules = load_data_cached()
    sA = next((s for s in flat if s["id"] == trader_shift_id), None)
    sB = next((s for s in flat if s["id"] == tradee_shift_id), None)
    if not sA or not sB:
        return jsonify({"ok": False, "reason": "not-found"}), 404

    ok, reason = simulate_swap_ok(schedules, sA, sB)
    return jsonify({"ok": ok, "reason": reason})


# -------------------------------
# UI (Apple-inspired, day-night SVG toggle, weekend badge,
# hamster loader, Option A two-column comparison in modal)
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
      --amber: #ff9f0a;
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
      --amber: #ffd60a;
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
    @media (max-width: 900px){
      .controls{grid-template-columns:1fr 1fr auto auto}
    }
    label{display:block; margin:0 0 6px 2px; font-size:12px; color:var(--muted); font-weight:600; letter-spacing:.02em;}
    select{
      width:100%; appearance:none; padding:10px 12px; border-radius:12px;
      color:var(--fg); background:var(--card); border:1px solid var(--sep); outline:none;
      box-shadow: var(--shadow); transition:border-color .2s, box-shadow .2s;
      background-image:url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="14" height="14" viewBox="0 0 20 20" fill="%236e6e73"><path d="M5.5 7.5l4.5 4.5 4.5-4.5"/></svg>');
      background-repeat:no-repeat; background-position:right 10px center; background-size:14px;
    }
    select:focus{border-color:var(--accent); box-shadow:0 0 0 4px var(--ring)}
    .btn{
      padding:10px 14px; border-radius:12px; border:1px solid var(--sep);
      background:var(--card); color:var(--fg); font-weight:600; cursor:pointer;
      box-shadow: var(--shadow); transition: transform .06s ease, background .2s;
    }
    .btn:hover{background:color-mix(in oklab, var(--card) 85%, var(--fg) 15%)}
    .btn:active{transform: translateY(1px)}

    /* Day/Night fancy toggle */
    #theme-toggle-button{font-size:16px; position:relative; display:inline-flex; align-items:center; width:7em; cursor:pointer; user-select:none}
    #toggle{opacity:0; width:0; height:0; position:absolute}
    #theme-toggle-button svg{width:7em; height:2.6em; display:block}
    #container, #patches, #stars, #button, #sun, #moon, #cloud{
      transition-property: all;
      transition-timing-function: cubic-bezier(0.4, 0, 0.2, 1);
      transition-duration: 0.25s;
    }
    #toggle:checked + svg #container { fill: #2b4360; }
    #toggle:checked + svg #button { transform: translate(28px, 2.333px); }
    #sun { opacity: 1; }
    #toggle:checked + svg #sun { opacity: 0; }
    #moon { opacity: 0; }
    #toggle:checked + svg #moon { opacity: 1; }
    #cloud { opacity: 1; }
    #toggle:checked + svg #cloud { opacity: 0; }
    #stars { opacity: 0; }
    #toggle:checked + svg #stars { opacity: 1; }

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
    .empty, .muted{color:var(--muted); font-size:13px; padding:10px 4px}

    /* Modal & OPTION A: Two-column comparison panels */
    .modal-backdrop{position:fixed; inset:0; background:rgba(0,0,0,.22); display:none; align-items:center; justify-content:center; z-index:30}
    .modal{
      width:min(900px,94vw); border-radius:20px; border:1px solid var(--sep); background:var(--card);
      box-shadow: 0 30px 80px rgba(0,0,0,.25);
      padding:20px 18px;
      animation: pop .18s ease;
    }
    @keyframes pop{from{transform:scale(.98); opacity:0} to{transform:scale(1); opacity:1}}
    .close{float:right; cursor:pointer; color:var(--muted); font-weight:700}
    .close:hover{color:var(--fg)}
    .modal h3{margin:0 0 12px; font-size:17px}

    .compare-wrap{display:grid; grid-template-columns:1fr 1fr; gap:12px; margin-bottom:12px}
    @media (max-width: 720px){ .compare-wrap{grid-template-columns:1fr} }
    .compare-card{
      border:1px solid var(--sep); border-radius:16px; background:var(--card);
      padding:12px 12px 10px;
    }
    .cc-head{display:flex; align-items:center; justify-content:space-between; margin-bottom:8px}
    .cc-name{font-weight:800}
    .cc-badge{
      padding:6px 10px; border-radius:999px; font-size:12px; font-weight:700;
      border:1px solid var(--sep); background:var(--bg); color:var(--muted);
    }
    .cc-badge.good{border-color:rgba(52,199,89,.35); color:var(--success)}
    .cc-badge.warn{border-color:rgba(255,159,10,.45); color:var(--amber)}
    .big-num{font-size:24px; font-weight:900; letter-spacing:.2px}
    .cc-meta{
      display:grid; grid-template-columns:repeat(3, 1fr); gap:8px; margin-top:8px;
    }
    .cc-cell{border:1px solid var(--sep); border-radius:12px; padding:10px; text-align:center}
    .cc-cell .lab{font-size:11px; color:var(--muted); margin-bottom:4px}
    .pill-row{display:flex; gap:6px; align-items:center; margin-top:10px; flex-wrap:wrap}
    .pill{border:1px solid var(--sep); border-radius:999px; padding:6px 10px; font-size:12px; background:var(--bg); white-space:nowrap; max-width:100%; overflow:hidden; text-overflow:ellipsis}
    .pill.new{background:var(--accent); color:#fff; border-color:transparent}
    .cc-table{
      width:100%; border-collapse:collapse; margin-top:8px; font-size:12.5px
    }
    .cc-table th, .cc-table td{border-top:1px solid var(--sep); padding:6px 4px; text-align:left}
    .cc-note{color:var(--muted); font-size:12px; margin-top:6px}

    .msgarea{margin-top:12px}
    .seg-small{display:inline-flex; border:1px solid var(--sep); border-radius:12px; overflow:hidden; background:var(--bg)}
    .seg-small button{appearance:none; border:0; padding:8px 12px; background:transparent; color:var(--fg); font-weight:600; cursor:pointer}
    .seg-small button[aria-pressed="true"]{background:var(--accent); color:#fff}
    .msgbox{width:100%; min-height:120px; resize:vertical; padding:10px 12px; border-radius:12px; border:1px solid var(--sep); background:var(--card); color:var(--fg); font-size:14px; line-height:1.38; box-shadow: var(--shadow)}
    .copybtn{padding:8px 12px; border-radius:12px; border:1px solid var(--sep); background:var(--card); color:var(--fg); font-weight:700; cursor:pointer}
    .copybtn.copied{border-color: var(--success); color: var(--success)}

    /* Loader with hamster */
    .loader{
      position:fixed; inset:0; z-index:40; display:flex; align-items:center; justify-content:center;
      background:color-mix(in oklab, var(--bg) 70%, transparent); backdrop-filter: blur(22px) saturate(1.4)
    }
    .loader-card{width:min(520px,90vw); padding:18px; border-radius:20px; background:var(--card); border:1px solid var(--sep); box-shadow: var(--shadow)}
    .loader-head{display:flex; align-items:center; justify-content:space-between; margin-bottom:10px}
    .loader-title{font-weight:700}
    .loader-sub{color:var(--muted); font-size:12.5px; margin-top:8px}
    .loader-bar{height:10px; border-radius:999px; background:color-mix(in oklab, var(--bg) 60%, transparent); border:1px solid var(--sep); overflow:hidden; margin-top:10px}
    .loader-fill{height:100%; width:0%; background:linear-gradient(90deg, #0a84ff, #64d2ff); transition:width .2s ease}
    .loader-error .loader-fill{background:linear-gradient(90deg, #ff3b30, #ff6961)}
    .fade-out{animation:fadeOut .28s ease forwards}
    @keyframes fadeOut{to{opacity:0; visibility:hidden}}

    /* Hamster animation (Uiverse by Nawsome) */
    .wheel-and-hamster{ --dur: 1s; position: relative; width: 12em; height: 12em; font-size: 14px; margin: 6px auto 0; }
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
    .hamster__limb--br, .hamster__limb--bl { border-radius: 0.75em 0.75em 0 0; clip-path: polygon(0 0,100% 0,100% 30%,70% 90%,70% 100%,30% 100%,40% 90%,0 30%); top: 1em; left: 2.8em; width: 1.5em; height: 2.5em; transform-origin: 50% 30%; }
    .hamster__limb--br { animation: hamsterBRLimb var(--dur) linear infinite; background: linear-gradient(hsl(30,90%,80%) 90%,hsl(0,90%,75%) 90%); transform: rotate(-25deg) translateZ(-1px); }
    .hamster__limb--bl { animation: hamsterBLLimb var(--dur) linear infinite; background: linear-gradient(hsl(30,90%,90%) 90%,hsl(0,90%,85%) 90%); transform: rotate(-25deg); }
    .hamster__tail { animation: hamsterTail var(--dur) linear infinite; background: hsl(0,90%,85%); border-radius: 0.25em 50% 50% 0.25em; box-shadow: 0 -0.2em 0 hsl(0,90%,75%) inset; top: 1.5em; right: -0.5em; width: 1em; height: 0.5em; transform: rotate(30deg) translateZ(-1px); transform-origin: 0.25em 0.25em; }
    .spoke { animation: spoke var(--dur) linear infinite; background: radial-gradient(100% 100% at center,hsl(0,0%,60%) 4.8%,hsla(0,0%,60%,0) 5%), linear-gradient(hsla(0,0%,55%,0) 46.9%,hsl(0,0%,65%) 47% 52.9%,hsla(0,0%,65%,0) 53%) 50% 50% / 99% 99% no-repeat; }
    @keyframes hamster{ from, to{ transform: rotate(4deg) translate(-0.8em,1.85em); } 50%{ transform: rotate(0) translate(-0.8em,1.85em); } }
    @keyframes hamsterHead{ from, 25%, 50%, 75%, to{ transform: rotate(0); } 12.5%, 37.5%, 62.5%, 87.5%{ transform: rotate(8deg); } }
    @keyframes hamsterEye{ from, 90%, to{ transform: scaleY(1); } 95%{ transform: scaleY(0); } }
    @keyframes hamsterEar{ from, 25%, 50%, 75%, to{ transform: rotate(0); } 12.5%, 37.5%, 62.5%, 87.5%{ transform: rotate(12deg); } }
    @keyframes hamsterBody{ from, 25%, 50%, 75%, to{ transform: rotate(0); } 12.5%, 37.5%, 62.5%, 87.5%{ transform: rotate(-2deg); } }
    @keyframes hamsterFRLimb{ from, 25%, 50%, 75%, to{ transform: rotate(50deg) translateZ(-1px); } 12.5%, 37.5%, 62.5%, 87.5%{ transform: rotate(-30deg) translateZ(-1px); } }
    @keyframes hamsterFLLimb{ from, 25%, 50%, 75%, to{ transform: rotate(-30deg); } 12.5%, 37.5%, 62.5%, 87.5%{ transform: rotate(50deg); } }
    @keyframes hamsterBRLimb{ from, 25%, 50%, 75%, to{ transform: rotate(-60deg) translateZ(-1px); } 12.5%, 37.5%, 62.5%, 87.5%{ transform: rotate(20deg) translateZ(-1px); } }
    @keyframes hamsterBLLimb{ from, 25%, 50%, 75%, to{ transform: rotate(20deg); } 12.5%, 37.5%, 62.5%, 87.5%{ transform: rotate(-60deg); } }
    @keyframes hamsterTail{ from, 25%, 50%, 75%, to{ transform: rotate(30deg) translateZ(-1px); } 12.5%, 37.5%, 62.5%, 87.5%{ transform: rotate(10deg) translateZ(-1px); } }
    @keyframes spoke{ from{ transform: rotate(0); } to{ transform: rotate(-1turn); } }
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

      <!-- Hamster animation -->
      <div class="wheel-and-hamster">
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

      <div class="loader-sub" id="loaderSub">Fetching calendars and building options…</div>
      <div class="loader-bar"><div id="loaderFill" class="loader-fill"></div></div>
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

        <!-- Day/Night switch -->
        <label id="theme-toggle-button" title="Toggle theme">
          <input id="toggle" type="checkbox" aria-label="Theme toggle"/>
          <svg viewBox="0 0 60 24">
            <defs>
              <clipPath id="buttonClip"><rect x="2" y="2" width="56" height="20" rx="10"/></clipPath>
            </defs>
            <rect id="container" x="0" y="0" width="60" height="24" rx="12" fill="#e9eef7"/>
            <g id="patches" clip-path="url(#buttonClip)">
              <circle id="cloud" cx="40" cy="8" r="4" fill="#cfe2ff"/>
              <g id="stars" fill="#ffd27d">
                <circle cx="20" cy="7" r="1"/>
                <circle cx="25" cy="11" r="0.8"/>
                <circle cx="15" cy="13" r="0.6"/>
              </g>
            </g>
            <g id="button">
              <circle cx="12" cy="12" r="10" fill="#fff"/>
              <circle id="sun" cx="12" cy="12" r="6" fill="#ffd054"/>
              <circle id="moon" cx="12" cy="12" r="5" fill="#dfe7ff"/>
            </g>
          </svg>
        </label>
      </div>

      <div class="legend">
        <span>Select your name and click a shift you want to trade away.</span>
        <span>Excluded: Trauma / Ultrasound / “US” / Sick Call</span>
        <span>Future shifts only</span>
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

  <!-- Offer Modal -->
  <div class="modal-backdrop" id="mb" aria-modal="true" role="dialog">
    <div class="modal">
      <span class="close" id="closex" aria-label="Close">✕</span>
      <h3>Propose Trade</h3>

      <!-- OPTION A: Two-column comparison panels -->
      <div class="compare-wrap" id="compareWrap">
        <!-- populated dynamically -->
      </div>
      <div class="cc-note">Week = Mon–Sun by shift start • Rest rule: gap ≥ prior shift duration • 60h max per week</div>

      <!-- Message composer -->
      <div class="msgarea">
        <div style="display:flex; align-items:center; justify-content:space-between; margin:8px 0 8px;">
          <div class="seg-small" role="tablist" aria-label="Message tone">
            <button id="tonePro" role="tab" aria-pressed="true">Professional</button>
            <button id="toneDes" role="tab" aria-pressed="false">Desperate</button>
            <button id="toneSil" role="tab" aria-pressed="false">Silly</button>
          </div>
          <button id="copyBtn" class="copybtn" aria-label="Copy message">Copy</button>
        </div>
        <textarea id="msgbox" class="msgbox" readonly></textarea>
      </div>
    </div>
  </div>

  <script>
    const $ = (sel) => document.querySelector(sel);

    // Surface JS errors on the loader so it never silently hangs
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

    /* Loader logic (progressive to 90%, then finish to 100% on ready) */
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

    /* Theme */
    const themeCheckbox = $("#toggle");
    function applyTheme(theme){
      const isNight = theme === "night";
      document.body.classList.toggle("theme-dark", isNight);
      document.body.classList.toggle("theme-light", !isNight);
      if (themeCheckbox) themeCheckbox.checked = isNight;
      try { localStorage.setItem("shift-theme", theme); } catch(e){}
    }
    function initTheme(){
      let saved = null;
      try { saved = localStorage.getItem("shift-theme"); } catch(e){}
      applyTheme(saved === "night" ? "night" : "day");
    }
    if (themeCheckbox){
      themeCheckbox.addEventListener("change", ()=>{
        applyTheme(themeCheckbox.checked ? "night" : "day");
      });
    }

    /* App els */
    const meSel = $("#me");
    const myShiftSel = $("#myshift");
    const mineList = $("#mine");
    const results = $("#results");
    const modal = $("#mb");
    const closex = $("#closex");
    const compareWrap = $("#compareWrap");
    const msgbox = $("#msgbox");
    const copyBtn = $("#copyBtn");
    const tonePro = $("#tonePro");
    const toneDes = $("#toneDes");
    const toneSil = $("#toneSil");

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
        SHIFTS = data.shifts; // already filtered to future by server
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
        title.className = "title";
        title.textContent = s.title;
        const subRow = document.createElement("div");
        subRow.className = "sub";
        subRow.textContent = `${f1.dstr} ${f1.t} · ${f2.t} • ${dur}h`;
        const wk = weekendBadgeEl(s.start);
        if (wk){ subRow.appendChild(document.createTextNode(" ")); subRow.appendChild(wk); }
        meta.appendChild(title); meta.appendChild(subRow);

        const chip = document.createElement("div");
        chip.className = "chip";
        chip.textContent = s.eligible ? "Eligible" : "Not eligible";

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

    // Build outreach message text
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

computers say it’s legit (i'm p sure)✅
lmk and I’ll make it official 😎
— ${me}`;

      if (tone === "desperate") return desperate;
      if (tone === "silly") return silly;
      return professional;
    }

    function setTone(active){
      [tonePro, toneDes, toneSil].forEach(btn => btn.setAttribute("aria-pressed", "false"));
      if (active === "professional") tonePro.setAttribute("aria-pressed","true");
      if (active === "desperate") toneDes.setAttribute("aria-pressed","true");
      if (active === "silly") toneSil.setAttribute("aria-pressed","true");
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

    // Helpers for comparison data
    function weekStart(d){ // Monday 00:00
      const wd = d.getDay(); // 0=Sun
      const offset = (wd === 0 ? -6 : 1 - wd);
      const start = new Date(d);
      start.setHours(0,0,0,0);
      start.setDate(start.getDate() + offset);
      return start;
    }
    function weekEnd(d){ const ws = weekStart(d); const we = new Date(ws); we.setDate(ws.getDate() + 7); return we; }
    function cloneScheduleFor(person){ return SHIFTS.filter(s => s.person === person).map(s => ({...s})); }
    function insertSwapAndSort(schedule, removeId, addShiftForPerson){
      const kept = schedule.filter(s => s.id !== removeId);
      kept.push(addShiftForPerson);
      kept.sort((a,b)=> a.start.localeCompare(b.start));
      return kept;
    }
    function findPrevNext(sortedSchedule, anchorShiftId){
      const idx = sortedSchedule.findIndex(s => s.id === anchorShiftId);
      return { prev: idx>0 ? sortedSchedule[idx-1] : null, next: (idx>=0 && idx+1<sortedSchedule.length) ? sortedSchedule[idx+1] : null };
    }
    function durationHours(s){ return hoursBetweenISO(s.start, s.end); }
    function gapHours(aEndISO, bStartISO){ return (new Date(bStartISO) - new Date(aEndISO))/3600000; }
    function sumWeekHours(schedule, whenDateISO){
      const d = new Date(whenDateISO);
      const ws = weekStart(d);
      const we = weekEnd(d);
      let total = 0;
      for (const s of schedule){
        const sd = new Date(s.start);
        if (sd >= ws && sd < we){ total += durationHours(s); }
      }
      return total;
    }
    function pillText(s){
      const f1 = fmt(s.start), f2 = fmt(s.end);
      return `${s.title} • ${f1.dstr} • ${f1.t}–${f2.t}`;
    }

    function renderOptionAComparison({me, partner, myShift, theirShift}){
      // Build swapped clones
      const mineOrig = cloneScheduleFor(me);
      const theirsOrig = cloneScheduleFor(partner);
      const sB_for_A = {...theirShift, person: me, id: `${me}|${theirShift.start}|${theirShift.end}|${theirShift.title}`};
      const sA_for_B = {...myShift, person: partner, id: `${partner}|${myShift.start}|${myShift.end}|${myShift.title}`};
      const mineNew = insertSwapAndSort(mineOrig, myShift.id, sB_for_A);
      const theirsNew = insertSwapAndSort(theirsOrig, theirShift.id, sA_for_B);
      const aPos = findPrevNext(mineNew, sB_for_A.id);
      const bPos = findPrevNext(theirsNew, sA_for_B.id);

      const aPrevGap = aPos.prev ? gapHours(aPos.prev.end, sB_for_A.start) : null;
      const aNextGap = aPos.next ? gapHours(sB_for_A.end, aPos.next.start) : null;
      const bPrevGap = bPos.prev ? gapHours(bPos.prev.end, sA_for_B.start) : null;
      const bNextGap = bPos.next ? gapHours(sA_for_B.end, bPos.next.start) : null;

      const aWeekTotal = sumWeekHours(mineNew, sB_for_A.start);
      const bWeekTotal = sumWeekHours(theirsNew, sA_for_B.start);
      const aCapOk = aWeekTotal <= 60.0;
      const bCapOk = bWeekTotal <= 60.0;

      function row(s){ if(!s) return "—"; const f1 = fmt(s.start), f2 = fmt(s.end); return `${s.title} • ${f1.dstr} • ${f1.t}–${f2.t}`; }

      function cardHTML(personName, newShift, pos, prevGap, nextGap, weekTotal, capOk){
        const prevOK = pos.prev ? (prevGap >= (durationHours(pos.prev))) : true;
        const nextOK = pos.next ? (nextGap >= (durationHours(newShift))) : true;
        const fOK = capOk && prevOK && nextOK;
        return `
          <div class="compare-card">
            <div class="cc-head">
              <div class="cc-name">${personName}</div>
              <div class="cc-badge ${fOK ? "good" : "warn"}">${fOK ? "✅ All clear" : "⚠ Review gaps/weekly cap"}</div>
            </div>
            <div class="big-num" title="Weekly total (Mon–Sun)">${weekTotal.toFixed(1)}h / 60h</div>

            <div class="cc-meta">
              <div class="cc-cell">
                <div class="lab">Prev gap</div>
                <div>${prevGap !== null ? prevGap.toFixed(1) + "h" : "—"}</div>
              </div>
              <div class="cc-cell">
                <div class="lab">Next gap</div>
                <div>${nextGap !== null ? nextGap.toFixed(1) + "h" : "—"}</div>
              </div>
              <div class="cc-cell">
                <div class="lab">New duration</div>
                <div>${durationHours(newShift).toFixed(1)}h</div>
              </div>
            </div>

            <div class="pill-row">
              ${pos.prev ? `<span class="pill">${pillText(pos.prev)}</span>` : `<span class="pill">—</span>`}
              <span class="pill new">${pillText(newShift)}</span>
              ${pos.next ? `<span class="pill">${pillText(pos.next)}</span>` : `<span class="pill">—</span>`}
            </div>

            <table class="cc-table" aria-label="Nearby shifts">
              <thead><tr><th style="width:28%">When</th><th>Shift</th><th style="width:28%">Time</th></tr></thead>
              <tbody>
                <tr><td>Prev</td><td>${row(pos.prev)}</td><td>${pos.prev ? fmt(pos.prev.start).t + " – " + fmt(pos.prev.end).t : "—"}</td></tr>
                <tr><td><strong>New</strong></td><td><strong>${pillText(newShift)}</strong></td><td><strong>${fmt(newShift.start).t} – ${fmt(newShift.end).t}</strong></td></tr>
                <tr><td>Next</td><td>${row(pos.next)}</td><td>${pos.next ? fmt(pos.next.start).t + " – " + fmt(pos.next.end).t : "—"}</td></tr>
              </tbody>
            </table>
          </div>
        `;
      }

      compareWrap.innerHTML = [
        cardHTML(me, sB_for_A, aPos, aPrevGap, aNextGap, aWeekTotal, aCapOk),
        cardHTML(partner, sA_for_B, bPos, bPrevGap, bNextGap, bWeekTotal, bCapOk)
      ].join("");
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
        .map(c => ({ partner: c.tradee_person, shift: c.tradee_shift }))
        .sort((a,b)=> a.shift.start.localeCompare(b.shift.start));

      results.innerHTML = "";
      if (all.length === 0){
        results.innerHTML = `<div class="empty">No valid trades found right now.</div>`;
        return;
      }

      const mine = SHIFTS.find(x => x.id === shiftId);

      all.forEach(({partner, shift: s})=>{
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

        const offer = document.createElement("button");
        offer.className = "offer";
        offer.textContent = "Offer";
        offer.onclick = async ()=>{
          // Keep your global loader during validation for now
          showLoader("Validating trade…");

          const r2 = await fetch("/trade-recheck",{
            method:"POST",
            headers: {"Content-Type":"application/json"},
            body: JSON.stringify({ trader_shift_id: mine.id, tradee_shift_id: s.id })
          });
          const data2 = await r2.json();

          if (data2.ok){
            const me = meSel.value;
            CURRENT_TRADE = { me, partner, myShift: mine, theirShift: s };

            // Build comparison (Option A) and message
            renderOptionAComparison(CURRENT_TRADE);
            msgbox.value = buildMessage("professional", me, partner, mine, s);
            [tonePro, toneDes, toneSil].forEach(btn => btn.setAttribute("aria-pressed", "false"));
            tonePro.setAttribute("aria-pressed","true");
            setCopyState(false);

            hideLoader();
            modal.style.display = "flex";
          } else {
            hideLoader();
            alert("This pair failed recheck: " + data2.reason);
          }
        };

        card.appendChild(meta);
        card.appendChild(offer);
        results.appendChild(card);
      });
    }

    /* Listeners */
    meSel.addEventListener("change", ()=>{ populateMyShifts(); });
    myShiftSel.addEventListener("change", ()=> selectMyShift(myShiftSel.value));
    $("#refresh").addEventListener("click", loadShifts);
    closex.addEventListener("click", ()=> modal.style.display = "none");
    modal.addEventListener("click", (e)=>{ if(e.target === modal) modal.style.display = "none"; });

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

    (function init(){ initTheme(); loadShifts(); })();
  </script>
</body>
</html>
"""

@app.route("/")
def index():
    return render_template_string(INDEX_HTML)

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=5002, debug=True)
