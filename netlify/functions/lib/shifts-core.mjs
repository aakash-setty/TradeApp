import ical from "node-ical";
import CALENDARS from "./calendars.data.mjs";

// How far back to include events. Recent-past shifts give the client full
// Mon-Sun week context (ED/Tra badge, week timelines) even for the current week.
const LOOKBACK_DAYS = 21;

function loadCalendars() {
  if (process.env.CALENDARS_JSON) {
    return JSON.parse(process.env.CALENDARS_JSON);
  }
  return CALENDARS;
}

// node-ical builds date-only (all-day) values with server-local Date parts,
// so read them back with local getters to recover the calendar date.
function localYMD(d) {
  const p = (n) => String(n).padStart(2, "0");
  return `${d.getFullYear()}-${p(d.getMonth() + 1)}-${p(d.getDate())}`;
}

async function fetchCalendar(cal, cutoffMs) {
  const resp = await fetch(cal.url, { signal: AbortSignal.timeout(15000) });
  if (!resp.ok) throw new Error(`${cal.name}: HTTP ${resp.status}`);
  const text = await resp.text();
  const parsed = ical.sync.parseICS(text);

  const shifts = [];
  for (const key of Object.keys(parsed)) {
    const ev = parsed[key];
    if (!ev || ev.type !== "VEVENT" || !ev.start || !ev.end) continue;
    if (ev.end.getTime() <= ev.start.getTime()) continue;
    if (ev.end.getTime() < cutoffMs) continue;

    const title = String(ev.summary ?? "");
    if (ev.datetype === "date") {
      shifts.push({
        person: cal.name,
        title,
        dateOnly: true,
        startDate: localYMD(ev.start),
        endDate: localYMD(ev.end),
      });
    } else {
      shifts.push({
        person: cal.name,
        title,
        dateOnly: false,
        start: ev.start.toISOString(),
        end: ev.end.toISOString(),
      });
    }
  }
  return shifts;
}

export async function getShifts() {
  const calendars = loadCalendars();
  const cutoffMs = Date.now() - LOOKBACK_DAYS * 24 * 3600 * 1000;

  const results = await Promise.allSettled(
    calendars.map((cal) => fetchCalendar(cal, cutoffMs))
  );

  const shifts = [];
  const errors = [];
  results.forEach((r, i) => {
    if (r.status === "fulfilled") {
      shifts.push(...r.value);
    } else {
      errors.push({ person: calendars[i].name, error: String(r.reason && r.reason.message ? r.reason.message : r.reason) });
    }
  });

  return {
    people: calendars.map((c) => c.name).sort(),
    shifts,
    errors,
    fetchedAt: new Date().toISOString(),
  };
}
