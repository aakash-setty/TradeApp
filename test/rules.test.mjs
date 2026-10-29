// Rules engine checks. Run under TZ=America/New_York (npm test sets it), like the browser.
import test from "node:test";
import assert from "node:assert/strict";
import { buildData, simulateSwapOk, weekHours, inferBlock, personWorksPedsInWeek, isEdTraTitle } from "../src/rules.js";

const iso = (s) => new Date(s).toISOString();
const sh = (person, title, start, end, extra = {}) => ({ person, title, dateOnly: false, start: iso(start), end: iso(end), ...extra });

// Freeze "today" so the future cutoff is predictable: Oct 29 2026 noon Eastern.
const RealDate = Date;
function withNow(nowIso, fn) {
  const fixed = new RealDate(nowIso).getTime();
  global.Date = class extends RealDate {
    constructor(...a) { super(...(a.length ? a : [fixed])); }
    static now() { return fixed; }
  };
  try { return fn(); } finally { global.Date = RealDate; }
}

test("screenshot case: peds night Oct 29 blocks taking Z1 Day Oct 30 7a", () => {
  withNow("2026-10-29T16:00:00Z", () => {
    const payload = {
      people: ["Aakash", "Priscilla"],
      shifts: [
        sh("Aakash", "Peds ER 9p-7a [Setty ED2]", "2026-10-29T21:00:00-04:00", "2026-10-30T07:00:00-04:00", { source: "amion-peds" }),
        sh("Aakash", "Eve1 2p-10p [Setty EM28]", "2026-11-16T14:00:00-05:00", "2026-11-16T22:00:00-05:00"),
        sh("Priscilla", "Z1 Day 2/3 7a-3p [Lozano EM28]", "2026-10-30T07:00:00-04:00", "2026-10-30T15:00:00-04:00"),
      ],
    };
    const D = buildData(payload);
    const mine = D.flat.find((s) => s.person === "Aakash" && /Eve1/.test(s.title));
    const theirs = D.flat.find((s) => s.person === "Priscilla");
    // The peds shift started today, so it is not tradable, but it still counts for rest.
    assert.equal(D.flat.some((s) => /Peds/.test(s.title)), false);
    assert.equal(simulateSwapOk(D.schedules, mine, theirs)[0], false);
  });
});

test("weekly hours include earlier days of the current week and skip all-day entries", () => {
  withNow("2026-10-29T16:00:00Z", () => {
    const D = buildData({
      people: ["A"],
      shifts: [
        sh("A", "Z1 Day 7a-3p [A EM28]", "2026-10-26T07:00:00-04:00", "2026-10-26T15:00:00-04:00"), // Monday, past
        sh("A", "Z1 Day 7a-3p [A EM28]", "2026-10-31T07:00:00-04:00", "2026-10-31T15:00:00-04:00"), // Saturday
        { person: "A", title: "Vacation", dateOnly: true, startDate: "2026-10-27", endDate: "2026-10-28" },
      ],
    });
    const anchor = new Date("2026-10-31T12:00:00-04:00");
    assert.equal(weekHours(D.schedules.get("A"), anchor), 16);
    assert.equal(inferBlock(D.schedules.get("A"), anchor), "JMH ED + Vacation");
  });
});

test("block inference and badges", () => {
  withNow("2026-10-29T16:00:00Z", () => {
    const D = buildData({
      people: ["A"],
      shifts: [
        sh("A", "Peds ER 3PM - 11PM [A ED2]", "2026-11-02T15:00:00-05:00", "2026-11-02T23:00:00-05:00", { source: "amion-peds" }),
        sh("A", "Peds ER 9p-7a [A ED2]", "2026-11-04T21:00:00-05:00", "2026-11-05T07:00:00-05:00", { source: "amion-peds" }),
        sh("A", "Day1 7a-3p [A EM28]", "2026-11-06T07:00:00-05:00", "2026-11-06T15:00:00-05:00"),
      ],
    });
    const anchor = new Date("2026-11-03T12:00:00-05:00");
    assert.equal(inferBlock(D.schedules.get("A"), anchor), "Peds ED + HCH ED");
    assert.equal(personWorksPedsInWeek(D.all, "A", anchor), true);
    assert.equal(isEdTraTitle("Peds ER 9p-7a [A ED2]"), false);
    assert.equal(inferBlock(D.schedules.get("A"), new Date("2026-12-01T12:00:00-05:00")), "No shifts on calendar");
    // Peds shifts are tradable titles.
    assert.equal(D.flat.find((s) => /9p-7a/.test(s.title)).eligible, true);
  });
});

test("no 7 days in a row: a swap creating a 7-day run is rejected, 6 is allowed", () => {
  withNow("2026-10-29T16:00:00Z", () => {
    const day = (d) => [`2026-11-${String(d).padStart(2, "0")}T07:00:00-05:00`, `2026-11-${String(d).padStart(2, "0")}T15:00:00-05:00`];
    const shifts = [];
    // A works Nov 2-7 (Mon-Sat, 6 days) plus a far-away Eve shift to give away.
    for (const d of [2, 3, 4, 5, 6, 7]) shifts.push(sh("A", "Z1 Day 7a-3p [A EM28]", ...day(d)));
    shifts.push(sh("A", "Eve1 2p-10p [A EM28]", "2026-11-20T14:00:00-05:00", "2026-11-20T22:00:00-05:00"));
    // B offers Nov 8 (would be A's 7th day) and Nov 10 (one day gap, fine).
    shifts.push(sh("B", "Z2 Day 2/3 7a-3p [B EM28]", ...day(8)));
    shifts.push(sh("B", "Z2 Day 2/3 7a-3p [B EM28]", ...day(10)));
    const D = buildData({ people: ["A", "B"], shifts });
    const give = D.flat.find((s) => s.person === "A" && /Eve1/.test(s.title));
    const nov8 = D.flat.find((s) => s.person === "B" && s.start.getDate() === 8);
    const nov10 = D.flat.find((s) => s.person === "B" && s.start.getDate() === 10);
    assert.equal(simulateSwapOk(D.schedules, give, nov8)[0], false);
    assert.equal(simulateSwapOk(D.schedules, give, nov10)[0], true);
  });
});

test("overnight shifts count for the day they start; all-day entries do not count", async () => {
  const { consecutiveDaysRun } = await import("../src/rules.js");
  const mk = (s, e, extra = {}) => ({ start: new Date(s), end: new Date(e), dateOnly: false, ...extra });
  const sched = [
    mk("2026-11-02T21:00:00-05:00", "2026-11-03T07:00:00-05:00"), // Mon night
    mk("2026-11-03T21:00:00-05:00", "2026-11-04T07:00:00-05:00"), // Tue night
    { start: new Date(2026, 10, 4), end: new Date(2026, 10, 5), dateOnly: true },   // all-day Wed
    mk("2026-11-05T07:00:00-05:00", "2026-11-05T15:00:00-05:00"), // Thu
  ];
  // Nov 4 is a Wednesday, so it counts as worked regardless of the all-day entry:
  // Mon + Tue + Wed + Thu = 4.
  assert.equal(consecutiveDaysRun(sched, new Date("2026-11-02T21:00:00-05:00")), 4);
  assert.equal(consecutiveDaysRun(sched, new Date("2026-11-05T07:00:00-05:00")), 4);
});

test("Wednesdays always count toward the 7-day run, except Nov 25 and Dec 23", async () => {
  const { consecutiveDaysRun, isMandatoryWednesday } = await import("../src/rules.js");
  const at = (ymd) => ({ start: new Date(`${ymd}T07:00:00-05:00`), end: new Date(`${ymd}T15:00:00-05:00`), dateOnly: false });
  const run = (dates, anchor) => consecutiveDaysRun(dates.map(at), new Date(`${anchor}T07:00:00-05:00`));

  assert.equal(isMandatoryWednesday(new Date(2026, 10, 18)), true);
  assert.equal(isMandatoryWednesday(new Date(2026, 10, 25)), false);
  assert.equal(isMandatoryWednesday(new Date(2026, 11, 23)), false);

  // Mon-Tue and Thu-Sun worked, Wed Nov 18 off but counts: 7 in a row.
  assert.equal(run(["2026-11-16", "2026-11-17", "2026-11-19", "2026-11-20", "2026-11-21", "2026-11-22"], "2026-11-22"), 7);
  // Same pattern over Thanksgiving week: Wed Nov 25 is exempt, so the run splits.
  assert.equal(run(["2026-11-23", "2026-11-24", "2026-11-26", "2026-11-27", "2026-11-28", "2026-11-29"], "2026-11-29"), 4);
  // Christmas week: Wed Dec 23 is exempt.
  assert.equal(run(["2026-12-21", "2026-12-22", "2026-12-24", "2026-12-25", "2026-12-26", "2026-12-27"], "2026-12-21"), 2);
  // An exempt Wednesday still counts if a shift is actually worked that day.
  assert.equal(run(["2026-11-24", "2026-11-25", "2026-11-26"], "2026-11-25"), 3);
});

test("a swap is rejected when an unworked Wednesday makes the 7th day", () => {
  withNow("2026-10-29T16:00:00Z", () => {
    const day = (d) => [`2026-11-${String(d).padStart(2, "0")}T07:00:00-05:00`, `2026-11-${String(d).padStart(2, "0")}T15:00:00-05:00`];
    const shifts = [];
    // A works Mon 16, Tue 17, Thu 19, Fri 20, Sat 21 (Wed 18 off but counts = 6 days).
    for (const d of [16, 17, 19, 20, 21]) shifts.push(sh("A", "Z1 Day 2/3 7a-3p [A EM28]", ...day(d)));
    shifts.push(sh("A", "Eve1 2p-10p [A EM28]", "2026-11-03T14:00:00-05:00", "2026-11-03T22:00:00-05:00"));
    shifts.push(sh("B", "Z2 Day 2/3 7a-3p [B EM28]", ...day(22))); // would be the 7th day
    const D = buildData({ people: ["A", "B"], shifts });
    const give = D.flat.find((s) => s.person === "A" && /Eve1/.test(s.title));
    const sun = D.flat.find((s) => s.person === "B");
    assert.equal(simulateSwapOk(D.schedules, give, sun)[0], false);
  });
});
