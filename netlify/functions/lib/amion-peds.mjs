// Pediatric ER shifts from the UM peds Amion schedule.
//
// How access works (verified Oct 2026):
//   1. GET  ocs?Lo=<login>            -> page whose links carry a fresh token, e.g.
//                                        ./ocs?File=!1a4bd2c8humi_peds&Page=Shift&Adb=1
//   2. GET  that Shift link           -> "All shifts, 10/12 to 11/15, 2026" grid (one rotation)
//   3. Each grid page links to its neighbours with
//        <a href="./ocs?...Yjd=NNNNN..."><IMG SRC="../oci/frame_rt.gif" ... TITLE="Next rotation">
//      We follow those links rather than computing Yjd ourselves.
// No cookies are needed; the token in the URL is the session.
//
// Grid layout: one <table border=1>. A header row (<TR BGCOLOR=#f6deac>) starts each
// Sun-Sat week: [label col][Su][Mo]...[Sa]. Header cells hold the day number followed by
// a weekday ("Mo"), a month name on Sundays/the 1st ("November"), or a holiday ("Thxgiving").
// Data rows follow: [<i>ER* 9p-7a</i>][7 cells]. A cell holds a name like "ED 2 - Setty",
// optionally followed by a footnote marker (<a><img title="Trade with ..."></a><font>3</font>).
// Out-of-range days are "&nbsp;" and empty slots are "--".

const BASE = "https://www.amion.com/cgi-bin/";
const UA = "Mozilla/5.0 (compatible; ShiftExchange/1.0; resident schedule viewer)";
const TZ = "America/New_York";

// ---------------- Small helpers ----------------

function decodeEntities(s) {
  return s
    .replace(/&nbsp;/gi, " ")
    .replace(/&amp;/gi, "&")
    .replace(/&lt;/gi, "<")
    .replace(/&gt;/gi, ">")
    .replace(/&quot;/gi, '"')
    .replace(/&#39;/gi, "'");
}

function stripTags(s) {
  return decodeEntities(s.replace(/<[^>]*>/g, " ")).replace(/\s+/g, " ").trim();
}

const pad = (n) => String(n).padStart(2, "0");
const ymd = (y, m, d) => `${y}-${pad(m)}-${pad(d)}`;

// Calendar-date arithmetic in UTC so it never depends on the server's timezone.
function addDays(dateStr, n) {
  const [y, m, d] = dateStr.split("-").map(Number);
  const t = new Date(Date.UTC(y, m - 1, d + n));
  return ymd(t.getUTCFullYear(), t.getUTCMonth() + 1, t.getUTCDate());
}
function dayOfWeek(dateStr) {
  const [y, m, d] = dateStr.split("-").map(Number);
  return new Date(Date.UTC(y, m - 1, d)).getUTCDay(); // 0 = Sun
}
function dayOfMonth(dateStr) {
  return Number(dateStr.slice(8, 10));
}

// Wall-clock time in America/New_York -> UTC ISO string. DST-correct: a 9p-7a shift on
// the night clocks fall back is 11 real hours, and the rest/60h rules see it that way.
const _fmt = new Intl.DateTimeFormat("en-US", {
  timeZone: TZ, hourCycle: "h23",
  year: "numeric", month: "2-digit", day: "2-digit", hour: "2-digit", minute: "2-digit", second: "2-digit",
});
function tzOffsetMs(utcMs) {
  const p = Object.fromEntries(_fmt.formatToParts(new Date(utcMs)).map((x) => [x.type, x.value]));
  const asUtc = Date.UTC(+p.year, +p.month - 1, +p.day, +p.hour, +p.minute, +p.second);
  return asUtc - utcMs;
}
export function easternToUtcISO(dateStr, minutes) {
  const [y, m, d] = dateStr.split("-").map(Number);
  const wall = Date.UTC(y, m - 1, d, 0, minutes);
  let utc = wall - tzOffsetMs(wall);
  utc = wall - tzOffsetMs(utc); // second pass settles the DST edge
  return new Date(utc).toISOString();
}

// ---------------- Parsing: row labels ----------------

// "ER* 9p-7a" -> {startMin: 1260, endMin: 420}; "ER* 3PM - 11PM"; "ER* JN 11a-11p".
// Returns null when the label carries no time range (e.g. "Red Senior PGY-3").
export function parseLabelTimes(label) {
  const m = label.match(
    /(\d{1,2})(?::(\d{2}))?\s*([ap])\.?\s*m?\.?\s*[-–]\s*(\d{1,2})(?::(\d{2}))?\s*([ap])\.?\s*m?\.?(?![a-z])/i
  );
  if (!m) return null;
  const toMin = (h, mm, ap) => {
    let hh = Number(h) % 12;
    if (ap.toLowerCase() === "p") hh += 12;
    return hh * 60 + Number(mm || 0);
  };
  const startMin = toMin(m[1], m[2], m[3]);
  const endMin = toMin(m[4], m[5], m[6]);
  if (Number(m[1]) > 12 || Number(m[4]) > 12) return null;
  return { startMin, endMin };
}

// Only ER rows are imported. Ward rows ("Red Senior PGY-3", "Blue Senior") are skipped.
export function isErRowLabel(label) {
  return /^\s*ER\b/i.test(label) && parseLabelTimes(label) !== null;
}

// "ER* 9p-7a" -> "Peds ER 9p-7a"; "ER-1 Weekend 8p-8a" -> "Peds ER-1 Weekend 8p-8a"
export function pedsTitle(label) {
  return "Peds " + label.replace(/\*/g, "").replace(/\s+/g, " ").trim();
}

// ---------------- Parsing: names ----------------

// "ED 2 - Setty" -> {program: "ED", pgy: 2, last: "Setty"}; "ER 3 - Garza Cantu" likewise.
// Anything else (MP1 - X, FM1 - X, CHI 3 - X, bare peds names) returns null.
export function parseEmName(text) {
  const m = text.match(/^\s*(ED|ER)\s*-?\s*([1-4])\s*-\s*(.+?)\s*$/i);
  if (!m) return null;
  return { program: m[1].toUpperCase(), pgy: Number(m[2]), last: m[3] };
}

export function normName(s) {
  return String(s)
    .normalize("NFD")
    .replace(/[̀-ͯ]/g, "")
    .toLowerCase()
    .replace(/[^a-z]/g, "");
}

// Cell HTML -> list of display names, with footnote markers removed.
export function cellNames(cellHtml) {
  let h = cellHtml;
  // footnote: <a href=#><img ... title="Trade with Dr. X"></a><font style='font-size:8px;...'>3</font>
  h = h.replace(/<a\b[^>]*>\s*<img[^>]*pnote[^>]*>\s*<\/a>/gi, "");
  h = h.replace(/<img[^>]*>/gi, "");
  h = h.replace(/<font[^>]*font-size:\s*8px[^>]*>[^<]*<\/font>/gi, "");
  return h
    .split(/<br\s*\/?>/i)
    .map(stripTags)
    .filter((t) => t && t !== "--");
}

// ---------------- Parsing: one grid page ----------------

// "All shifts, 12/7 to 1/10, 2027" -> {start: "2026-12-07", end: "2027-01-10"}.
// The year printed is the END date's year.
export function parseRange(html) {
  const m = html.match(/All shifts,\s*(\d{1,2})\/(\d{1,2})\s+to\s+(\d{1,2})\/(\d{1,2}),\s*(\d{4})/i);
  if (!m) return null;
  const [sm, sd, em, ed, ey] = m.slice(1).map(Number);
  const sy = sm > em ? ey - 1 : ey;
  return { start: ymd(sy, sm, sd), end: ymd(ey, em, ed) };
}

function navLink(html, gif) {
  const re = new RegExp(`href="\\.\\/(ocs\\?[^"]*)"\\s*>\\s*<IMG SRC="\\.\\.\\/oci\\/${gif}"`, "i");
  const m = html.match(re);
  return m ? BASE + decodeEntities(m[1]) : null;
}

function splitCells(rowHtml) {
  const parts = rowHtml.split(/<td\b[^>]*>/i);
  parts.shift(); // text before the first <td>
  return parts.map((c) => c.replace(/<\/td>[\s\S]*$/i, "").replace(/<\/tr>[\s\S]*$/i, ""));
}

// Returns {range, next, prev, entries:[{date, label, name}], warnings}
// Throws if the grid structure does not line up with the title's date range, so a layout
// change produces a visible error instead of shifts silently landing on the wrong days.
export function parseShiftPage(html) {
  const range = parseRange(html);
  if (!range) throw new Error("Amion page has no 'All shifts, M/D to M/D, YYYY' title");

  const gridStart = html.search(/<table[^>]*border=1[^>]*>\s*<TR BGCOLOR=#f6deac>/i);
  if (gridStart < 0) throw new Error("Amion page: shift grid not found");
  const gridEnd = html.indexOf("</table>", gridStart);
  const grid = html.slice(gridStart, gridEnd < 0 ? undefined : gridEnd);

  const rows = grid.split(/<tr\b/i).slice(1);
  const entries = [];
  const warnings = [];
  let weekDates = null; // dates for the 7 day columns of the current week block
  let sunday = addDays(range.start, -dayOfWeek(range.start));
  let firstBlock = true;
  let lastSeen = null;

  for (const row of rows) {
    const isHeader = /^[^>]*BGCOLOR=#f6deac/i.test(row);
    const cells = splitCells(row);

    if (isHeader) {
      if (!firstBlock) sunday = addDays(sunday, 7);
      firstBlock = false;
      if (cells.length < 8) throw new Error(`Amion header row has ${cells.length} cells, expected 8`);
      weekDates = [];
      for (let j = 0; j < 7; j++) {
        const date = addDays(sunday, j);
        const txt = stripTags(cells[1 + j]);
        const dm = txt.match(/^(\d{1,2})\b/);
        const inRange = date >= range.start && date <= range.end;
        if (dm) {
          if (Number(dm[1]) !== dayOfMonth(date)) {
            throw new Error(`Amion header mismatch: column shows day ${dm[1]} but expected ${date}`);
          }
          if (!inRange) throw new Error(`Amion header shows day ${dm[1]} outside ${range.start}..${range.end}`);
          lastSeen = date;
        } else if (inRange) {
          throw new Error(`Amion header missing day number for ${date}`);
        }
        weekDates.push(inRange ? date : null);
      }
      continue;
    }

    if (!weekDates || cells.length < 8) continue; // separator rows (colspan=99) etc.
    const label = stripTags(cells[0]);
    if (!isErRowLabel(label)) continue;

    for (let j = 0; j < 7; j++) {
      const date = weekDates[j];
      if (!date) continue;
      for (const name of cellNames(cells[1 + j])) entries.push({ date, label, name });
    }
  }

  if (lastSeen !== range.end) {
    throw new Error(`Amion grid ended at ${lastSeen}, title says ${range.end}`);
  }

  return { range, next: navLink(html, "frame_rt\\.gif"), prev: navLink(html, "frame_left\\.gif"), entries, warnings };
}

// ---------------- Fetching ----------------

async function getText(url, fetchImpl) {
  const resp = await fetchImpl(url, {
    headers: { "User-Agent": UA, Accept: "text/html" },
    signal: AbortSignal.timeout(15000),
    redirect: "follow",
  });
  if (!resp.ok) throw new Error(`Amion HTTP ${resp.status}`);
  return resp.text();
}

export function shiftLinkFromLogin(html) {
  const m = html.match(/href="\.\/(ocs\?File=![^"]*?Page=Shift[^"]*)"/i);
  return m ? BASE + decodeEntities(m[1]) : null;
}

// Fetch every rotation page that overlaps [fromDate, toDate] (YYYY-MM-DD, Eastern).
export async function fetchPedsGrid({ login, fromDate, toDate, fetchImpl = fetch, maxPages = 8 }) {
  const loginHtml = await getText(`${BASE}ocs?Lo=${encodeURIComponent(login)}`, fetchImpl);
  const shiftUrl = shiftLinkFromLogin(loginHtml);
  if (!shiftUrl) throw new Error("Amion login page had no Shift link (login changed or schedule unpublished?)");

  const pages = [];
  const seen = new Set();
  const first = parseShiftPage(await getText(shiftUrl, fetchImpl));
  pages.push(first);
  seen.add(first.range.start);

  // Backwards, only as far as the lookback needs.
  let cur = first;
  while (cur.range.start > fromDate && cur.prev && pages.length < maxPages) {
    const p = parseShiftPage(await getText(cur.prev, fetchImpl));
    if (seen.has(p.range.start) || p.range.start >= cur.range.start) break;
    seen.add(p.range.start);
    pages.push(p);
    cur = p;
  }
  // Forwards to the horizon.
  cur = first;
  while (cur.range.end < toDate && cur.next && pages.length < maxPages) {
    const p = parseShiftPage(await getText(cur.next, fetchImpl));
    if (seen.has(p.range.start) || p.range.start <= cur.range.start) break;
    seen.add(p.range.start);
    pages.push(p);
    cur = p;
  }

  // Rotation pages overlap by a week. Merge per date, preferring the page whose own
  // range is centred on that date (the overlap weeks are usually identical anyway).
  const byDate = new Map(); // date -> {page, entries[]}
  for (const p of pages) {
    const perDate = new Map();
    for (const e of p.entries) {
      if (!perDate.has(e.date)) perDate.set(e.date, []);
      perDate.get(e.date).push(e);
    }
    for (let d = p.range.start; d <= p.range.end; d = addDays(d, 1)) {
      const prev = byDate.get(d);
      const margin = Math.min(daysBetween(p.range.start, d), daysBetween(d, p.range.end));
      if (!prev || margin > prev.margin) byDate.set(d, { margin, entries: perDate.get(d) || [] });
    }
  }

  const covered = [...byDate.keys()].sort();
  const entries = [];
  for (const d of covered) if (d >= fromDate && d <= toDate) entries.push(...byDate.get(d).entries);
  return {
    entries,
    coveredFrom: covered[0] || null,
    coveredTo: covered[covered.length - 1] || null,
    pages: pages.length,
  };
}

function daysBetween(a, b) {
  return Math.round((Date.parse(b + "T00:00:00Z") - Date.parse(a + "T00:00:00Z")) / 86400000);
}

// ---------------- Matching to app people ----------------

// QGenda titles end with "[Setty EM28]". Use the most common bracket name per person.
export function lastNamesFromQgenda(shifts) {
  const counts = new Map(); // person -> Map(last -> n)
  for (const s of shifts) {
    const m = String(s.title || "").match(/\[([^\]]+?)\s+EM\s*\d+\s*\]/i);
    if (!m) continue;
    if (!counts.has(s.person)) counts.set(s.person, new Map());
    const c = counts.get(s.person);
    c.set(m[1].trim(), (c.get(m[1].trim()) || 0) + 1);
  }
  const out = new Map();
  for (const [person, c] of counts) {
    out.set(person, [...c.entries()].sort((a, b) => b[1] - a[1])[0][0]);
  }
  return out;
}

// entries -> app shift objects. `lastNames` is Map(person -> last name).
export function toAppShifts(entries, lastNames) {
  const byNorm = new Map();
  const collisions = new Set();
  for (const [person, last] of lastNames) {
    const k = normName(last);
    if (byNorm.has(k) && byNorm.get(k) !== person) collisions.add(k);
    byNorm.set(k, person);
  }

  const shifts = [];
  const unmatched = new Set();
  const seen = new Set();
  for (const e of entries) {
    const em = parseEmName(e.name);
    if (!em) continue; // not an EM resident (MP, FM, CHI, peds categorical...)
    const k = normName(em.last);
    if (collisions.has(k)) { unmatched.add(`${e.name} (ambiguous last name)`); continue; }
    const person = byNorm.get(k);
    if (!person) { unmatched.add(e.name); continue; }

    const t = parseLabelTimes(e.label);
    const endDate = t.endMin <= t.startMin ? addDays(e.date, 1) : e.date;
    const start = easternToUtcISO(e.date, t.startMin);
    const end = easternToUtcISO(endDate, t.endMin);
    const title = `${pedsTitle(e.label)} [${em.last} ${em.program}${em.pgy}]`;
    const key = `${person}|${start}|${end}`;
    if (seen.has(key)) continue;
    seen.add(key);
    shifts.push({ person, title, dateOnly: false, start, end, source: "amion-peds" });
  }
  return { shifts, unmatched: [...unmatched].sort() };
}

export const _test = { addDays, dayOfWeek, stripTags };
