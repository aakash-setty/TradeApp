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
