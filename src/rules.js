// Trade-rules engine — faithful port of the Flask app's Python logic.
// All datetimes are JS Dates in the browser's local timezone (Eastern for this group).

// ---------------- Eligibility ----------------

const EXCLUDE_PATTERNS = [/trauma/i, /ultrasound/i, /\bUS\b/i, /sick\s*call/i];

const ALLOW_PATTERNS = [
  /\bday\s*[- ]?\s*([123])\b/i,
  /\bd([123])\b/i,
  /\beve?(ning)?\s*[- ]?\s*([123])\b/i,
  /\be([123])\b/i,
  /\bnight\s*[- ]?\s*([123])\b/i,
  /\bn([123])\b/i,
  /\bngt\s*[- ]?\s*([123])\b/i,
  /\bpod\s*[- ]?\s*a\s*[- ]?\s*([12])\b/i,
  /\bpod\s*[- ]?\s*b\s*[- ]?\s*([12])\b/i,
  /\bpoda\s*[- ]?\s*([12])\b/i,
  /\bpodb\s*[- ]?\s*([12])\b/i,
  /\bside\b/i,
  /\b([abc])\s*([12])\b/i,
  /\bdaytr\b/i,
  /\bngttr\b/i,
  /\bpeds\b/i,
];

export function isEligibleTitle(title) {
  if (!title) return false;
  if (EXCLUDE_PATTERNS.some((p) => p.test(title))) return false;
  return ALLOW_PATTERNS.some((p) => p.test(title));
}

// ---------------- Site / category detection (for the ED/Tra badge) ----------------
// Z1/Z2/Z3 = Jackson ED zones; Day/Eve/Night/Ngt 1-3, PODB, B Side,
// lettered Eve/Ngt A-C = Holy Cross ED; DayTr/NgtTr/TrSenior = Trauma.

export function isEdTraTitle(title) {
  const t = (title || "").toLowerCase();
  if (/trauma|\bdaytr\b|\bngttr\b|\btrsenior\b/.test(t)) return true;
  if (/^\s*z[123]\b/.test(t)) return true;
  if (/^\s*(day|eve|night|ngt)\s*[123]\b/.test(t)) return true;
  if (/^\s*podb\s*[12]\b/.test(t)) return true;
  if (/\bb side\b/.test(t)) return true;
  if (/^\s*(eve|ngt)\s+[abc][12]\b/.test(t)) return true;
  return false;
}

// ---------------- Time helpers ----------------

export function futureCutoff() {
  const d = new Date();
  d.setHours(0, 0, 0, 0);
  d.setDate(d.getDate() + 1);
  return d;
}

export function weekStart(d) {
  const wd = d.getDay(); // 0 = Sun
  const offset = wd === 0 ? -6 : 1 - wd;
  const ws = new Date(d);
  ws.setHours(0, 0, 0, 0);
  ws.setDate(ws.getDate() + offset);
  return ws;
}

export function weekEnd(d) {
  const ws = weekStart(d);
  const we = new Date(ws);
  we.setDate(ws.getDate() + 7);
  return we;
}

export function durationHours(s) {
  return (s.end - s.start) / 3600000;
}

export function gapHours(aEnd, bStart) {
  return (bStart - aEnd) / 3600000;
}

export function isWeekendStart(d) {
  const dow = d.getDay();
  return (dow === 5 && d.getHours() >= 19) || dow === 6 || dow === 0;
}

// ---------------- Data building ----------------

function parseShift(raw) {
  let start, end;
  if (raw.dateOnly) {
    const [ys, ms, ds] = raw.startDate.split("-").map(Number);
    const [ye, me, de] = raw.endDate.split("-").map(Number);
    start = new Date(ys, ms - 1, ds);
    end = new Date(ye, me - 1, de);
  } else {
    start = new Date(raw.start);
    end = new Date(raw.end);
  }
  return { person: raw.person, title: raw.title, start, end };
}

export function buildData(payload) {
  const all = payload.shifts
    .map(parseShift)
    .filter((s) => s.end > s.start)
    .sort((a, b) => a.start - b.start);

  const cutoff = futureCutoff();

  // Future-only tradable universe (matches the Flask engine exactly:
  // rule checks only consider shifts starting on/after tomorrow 00:00).
  const flat = all
    .filter((s) => s.start >= cutoff)
    .map((s) => ({
      ...s,
      id: `${s.person}|${s.start.getTime()}|${s.end.getTime()}|${s.title}`,
      eligible: isEligibleTitle(s.title),
    }));

  const schedules = new Map();
  for (const s of flat) {
    if (!schedules.has(s.person)) schedules.set(s.person, []);
    schedules.get(s.person).push(s);
  }
  for (const arr of schedules.values()) arr.sort((a, b) => a.start - b.start);

  return { all, flat, schedules, people: payload.people, fetchedAt: payload.fetchedAt, errors: payload.errors || [] };
}

// ---------------- Rules ----------------

function intervalsOverlap(aStart, aEnd, bStart, bEnd) {
  return aStart < bEnd && bStart < aEnd;
}

function isFreeForInterval(personShifts, start, end, excludeId) {
  for (const s of personShifts) {
    if (excludeId && s.id === excludeId) continue;
    if (intervalsOverlap(s.start, s.end, start, end)) return false;
  }
  return true;
}

function localBreakOk(sorted, idx) {
  const cur = sorted[idx];
  const prev = idx > 0 ? sorted[idx - 1] : null;
  const next = idx + 1 < sorted.length ? sorted[idx + 1] : null;

  if (prev) {
    const gapPrev = cur.start - prev.end;
    const durPrev = prev.end - prev.start;
    if (gapPrev < durPrev) return false;
  }
  if (next) {
    const gapCur = next.start - cur.end;
    const durCur = cur.end - cur.start;
    if (gapCur < durCur) return false;
  }
  return true;
}

function weekCapsOk(primeSched, newShift) {
  const ws = weekStart(newShift.start);
  const we = weekEnd(newShift.start);
  let total = 0;
  for (const s of primeSched) {
    if (s.start >= ws && s.start < we) total += durationHours(s);
  }
  return total <= 60.0;
}

// The atomic per-person check every trade is built from: can the owner of
// `giveShift` give it up and take on `receiveShift` instead, while keeping
// their own schedule valid (availability, rest rule, 60h weekly cap)?
export function personCanTake(schedules, giveShift, receiveShift) {
  if (!(giveShift.eligible && receiveShift.eligible)) return false;
  const P = giveShift.person;
  if (P === receiveShift.person) return false;

  const sched = schedules.get(P) || [];
  if (!isFreeForInterval(sched, receiveShift.start, receiveShift.end, giveShift.id)) return false;

  const clone = {
    ...receiveShift,
    person: P,
    id: `${P}|${receiveShift.start.getTime()}|${receiveShift.end.getTime()}|${receiveShift.title}`,
  };
  const prime = sched.filter((x) => x.id !== giveShift.id).concat([clone]).sort((a, b) => a.start - b.start);
  const idx = prime.indexOf(clone);

  if (!localBreakOk(prime, idx)) return false;
  if (!weekCapsOk(prime, clone)) return false;
  return true;
}

// 2-way swap: A gives sA and receives sB; B gives sB and receives sA.
// Both people must independently stay valid — the same as two personCanTake checks.
export function simulateSwapOk(schedules, traderShift, tradeeShift) {
  if (!(traderShift.eligible && tradeeShift.eligible)) return [false, "ineligible-title"];
  if (traderShift.person === tradeeShift.person) return [false, "same-person"];
  if (!personCanTake(schedules, tradeeShift, traderShift)) return [false, "B-side"];
  if (!personCanTake(schedules, traderShift, tradeeShift)) return [false, "A-side"];
  return [true, "ok"];
}

export function tradeOptions(flat, schedules, traderShift) {
  const candidates = [];
  for (const sB of flat) {
    if (sB.person === traderShift.person) continue;
    const [ok] = simulateSwapOk(schedules, traderShift, sB);
    if (ok) candidates.push(sB);
  }
  candidates.sort((a, b) => a.start - b.start || a.person.localeCompare(b.person));
  return candidates;
}

// ---------------- 3-way (cycle) trades ----------------
// A valid loop A -> B -> C -> A: you (A) give `yourShift` and receive some sC;
// B receives your shift and gives sB; C receives sB and gives sC. Because no
// rule spans people, the loop is valid exactly when all three personCanTake
// checks pass. Results are grouped by the shift YOU acquire (sC), each with the
// list of possible middle shifts sB (owned by B) that complete the loop.
export function threeWayOptions(flat, schedules, yourShift) {
  if (!yourShift || !yourShift.eligible) return [];
  const A = yourShift.person;

  // Middle candidates: owners who can take YOUR shift (B gives sB, receives yourShift).
  const OUT = flat.filter((v) => v.eligible && v.person !== A && personCanTake(schedules, v, yourShift));
  // Acquire candidates: shifts YOU can take (you give yourShift, receive sC).
  const IN = flat.filter((u) => u.eligible && u.person !== A && personCanTake(schedules, yourShift, u));

  const results = [];
  for (const sC of IN) {
    const C = sC.person;
    const middles = [];
    for (const sB of OUT) {
      if (sB.person === C || sB.id === sC.id) continue;
      if (personCanTake(schedules, sC, sB)) middles.push(sB); // C gives sC, receives sB
    }
    if (middles.length) {
      middles.sort((a, b) => a.start - b.start || a.person.localeCompare(b.person));
      results.push({ acquire: sC, from: C, middles });
    }
  }
  results.sort((a, b) => a.acquire.start - b.acquire.start || a.from.localeCompare(b.from));
  return results;
}

// ---------------- ED/Tra badge ----------------
// True if `person` works any ED (JMH/HCH) or Trauma shift during the Mon-Sun
// week containing `anchorDate`. Uses the full dataset (incl. recent past) so
// current-week context is complete.

export function personWorksEdTraInWeek(all, person, anchorDate) {
  const ws = weekStart(anchorDate);
  const we = weekEnd(anchorDate);
  return all.some(
    (s) => s.person === person && s.start >= ws && s.start < we && isEdTraTitle(s.title)
  );
}
