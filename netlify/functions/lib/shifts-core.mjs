import ical from "node-ical";
import CALENDARS from "./calendars.data.mjs";
import { fetchPedsGrid, lastNamesFromQgenda, toAppShifts } from "./amion-peds.mjs";

// How far back to include events. Recent-past shifts give the client full
// Mon-Sun week context (badges, weekly hour totals) even for the current week.
const LOOKBACK_DAYS = 21;
// How far ahead to pull the peds Amion schedule.
const PEDS_HORIZON_DAYS = 92;
// Amion is only re-fetched this often per warm server instance (QGenda stays live).
const PEDS_CACHE_MS = 10 * 60 * 1000;
// Login code for the UM peds Amion ("Lo=" value). Override with AMION_PEDS_LOGIN;
// set AMION_PEDS_LOGIN=off to disable the peds import entirely.
const DEFAULT_PEDS_LOGIN = "umipe";

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

function easternYMD(ms) {
  return new Intl.DateTimeFormat("en-CA", { timeZone: "America/New_York" }).format(new Date(ms));
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
        source: "qgenda",
      });
    } else {
      shifts.push({
        person: cal.name,
        title,
        dateOnly: false,
        start: ev.start.toISOString(),
        end: ev.end.toISOString(),
        source: "qgenda",
      });
    }
  }
  return shifts;
}

let _pedsCache = null; // {at, key, value}

async function getPedsGrid(nowMs) {
  const login = process.env.AMION_PEDS_LOGIN || DEFAULT_PEDS_LOGIN;
  if (login.toLowerCase() === "off") return null;
  const fromDate = easternYMD(nowMs - LOOKBACK_DAYS * 86400000);
  const toDate = easternYMD(nowMs + PEDS_HORIZON_DAYS * 86400000);
  const key = `${login}|${fromDate}|${toDate}`;
  if (_pedsCache && _pedsCache.key === key && nowMs - _pedsCache.at < PEDS_CACHE_MS) return _pedsCache.value;
  const value = await fetchPedsGrid({ login, fromDate, toDate });
  _pedsCache = { at: nowMs, key, value };
  return value;
}

// Drop Amion shifts that QGenda already lists for the same person at the same times,
// and flag (but keep) ones that overlap a QGenda shift without matching it exactly.
function reconcile(pedsShifts, qgendaShifts) {
  const exact = new Set();
  const byPerson = new Map();
  for (const s of qgendaShifts) {
    if (s.dateOnly) continue;
    exact.add(`${s.person}|${Date.parse(s.start)}|${Date.parse(s.end)}`);
    if (!byPerson.has(s.person)) byPerson.set(s.person, []);
    byPerson.get(s.person).push([Date.parse(s.start), Date.parse(s.end), s.title]);
  }
  const kept = [];
  const conflicts = [];
  for (const p of pedsShifts) {
    const a = Date.parse(p.start), b = Date.parse(p.end);
    if (exact.has(`${p.person}|${a}|${b}`)) continue;
    const clash = (byPerson.get(p.person) || []).find(([s, e]) => s < b && a < e);
    if (clash) conflicts.push(`${p.person}: ${p.title} overlaps QGenda "${clash[2]}"`);
    kept.push(p);
  }
  return { kept, conflicts };
}

export async function getShifts() {
  const calendars = loadCalendars();
  const nowMs = Date.now();
  const cutoffMs = nowMs - LOOKBACK_DAYS * 24 * 3600 * 1000;

  const [qResults, pedsResult] = await Promise.all([
    Promise.allSettled(calendars.map((cal) => fetchCalendar(cal, cutoffMs))),
    getPedsGrid(nowMs).then((v) => ({ ok: true, v }), (e) => ({ ok: false, e })),
  ]);

  const shifts = [];
  const errors = [];
  qResults.forEach((r, i) => {
    if (r.status === "fulfilled") {
      shifts.push(...r.value);
    } else {
      errors.push({ person: calendars[i].name, error: String(r.reason && r.reason.message ? r.reason.message : r.reason) });
    }
  });

  let peds = { enabled: false };
  if (!pedsResult.ok) {
    errors.push({ person: "Peds ER (Amion)", error: String(pedsResult.e && pedsResult.e.message ? pedsResult.e.message : pedsResult.e) });
    peds = { enabled: true, ok: false };
  } else if (pedsResult.v) {
    // Last names: explicit `lastName` in the calendar config wins, else QGenda "[Setty EM28]".
    const lastNames = lastNamesFromQgenda(shifts);
    for (const c of calendars) if (c.lastName) lastNames.set(c.name, c.lastName);

    const { shifts: pedsShifts, unmatched } = toAppShifts(pedsResult.v.entries, lastNames);
    const { kept, conflicts } = reconcile(pedsShifts, shifts);
    shifts.push(...kept);
    peds = {
      enabled: true,
      ok: true,
      count: kept.length,
      coveredFrom: pedsResult.v.coveredFrom,
      coveredTo: pedsResult.v.coveredTo,
      unmatchedEmNames: unmatched,
      peopleWithoutLastName: calendars.map((c) => c.name).filter((n) => !lastNames.has(n)),
      conflicts,
    };
  }

  return {
    people: calendars.map((c) => c.name).sort(),
    shifts,
    errors,
    peds,
    fetchedAt: new Date().toISOString(),
  };
}
