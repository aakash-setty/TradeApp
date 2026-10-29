// Run with: npm test
// Fixtures reproduce the real Amion markup (captured Oct 29 2026): header rows with
// weekday / month / holiday labels, footnote markers after names, ward rows, "--" and
// "&nbsp;" cells, and a title whose year belongs to the end date.
import test from "node:test";
import assert from "node:assert/strict";
import {
  parseShiftPage, parseLabelTimes, parseEmName, cellNames, parseRange, easternToUtcISO,
  toAppShifts, lastNamesFromQgenda, fetchPedsGrid, isErRowLabel, pedsTitle,
} from "../netlify/functions/lib/amion-peds.mjs";

const hdrCell = (txt) => `<td><a class=plain href="./ocs?Fi=!x&Page=OnSh&Adb=1&Jdo=0"><i>${txt}</i></a></TD>`;
const nb = `<td >&nbsp;</td>`;
const name = (n, note) =>
  `<td></font><font color=#ff0000>${n}${note ? `<a href=#><img src="../oci/pnote0.gif" width=13 height=13 border=0 title="${note}" onclick='alert("${note}");'"></a><font style='font-size:8px; vertical-align:50%;'>3</font>` : ""}</TD>`;
const dash = `<td class=gc>--</TD>`;
const row = (label, cells) => `<TR class=grbg><td><i>${label}</i></TD>${cells.join("")}</tr>\n<tr bgcolor=#bbbbbb><td colspan=99 height=2 style='padding: 0; border: 0px; '></td></tr>\n`;

function page({ title, weeks, prev = "Yjd=1", next = "Yjd=2" }) {
  let grid = `<table cellspacing=0 border=1 cellpadding=2 >\n`;
  for (const w of weeks) {
    grid += `<TR BGCOLOR=#f6deac><td> </TD>${w.header.map((h) => (h ? hdrCell(h) : nb)).join("")}</tr>\n`;
    for (const r of w.rows) grid += row(r[0], r[1]);
  }
  grid += `</table>`;
  return `<html><body>
<a href="./ocs?File=!tok&amp;Page=Shift&Skill=0&${prev}&Adb=1"><IMG SRC="../oci/frame_left.gif" WIDTH=15 HEIGHT=14 BORDER=0 TITLE="Previous rotation"></a>&nbsp;<a href="./ocs?File=!tok&Page=Shift&Skill=0&${next}&Adb=1"><IMG SRC="../oci/frame_rt.gif" WIDTH=15 HEIGHT=14 BORDER=0 TITLE="Next rotation"></a>
<font size=+2>${title}</font><br>${grid}<table><tr><td>notes</td></tr></table></body></html>`;
}

// 11/23 (Mon) to 11/29 (Sun), with Thanksgiving labels, as on the real Nov page.
const thanksgiving = page({
  title: "All shifts, 11/23 to 11/29, 2026",
  weeks: [
    {
      header: [null, "23 <font style='font-size:80%'>Mo", "24 Tu", "25 We", "26 Thxgiving", "27 Holiday", "28 Sa"],
      rows: [
        ["ER* 9p-7a", [nb, name("ED 2 - Setty", "Trade with Dr. Perron"), dash, name("Islam"), name("ER 3 - Garza Cantu"), dash, name("MP1 - Chang")]],
        ["ER* 3PM - 11PM", [nb, dash, name("ED 2 - Setty"), dash, dash, dash, dash]],
        ["Red Senior PGY-3", [nb, name("ED 2 - Setty"), dash, dash, dash, dash, dash]],
      ],
    },
    {
      header: ["29 Su", null, null, null, null, null, null],
      rows: [["ER-2 weekend 7p-7a", [name("ED 2 - Setty"), nb, nb, nb, nb, nb, nb]]],
    },
  ],
});

test("label times: am/pm forms, overnight, holiday and ward rows", () => {
  assert.deepEqual(parseLabelTimes("ER* 9p-7a"), { startMin: 21 * 60, endMin: 7 * 60 });
  assert.deepEqual(parseLabelTimes("ER* 3PM - 11PM"), { startMin: 15 * 60, endMin: 23 * 60 });
  assert.deepEqual(parseLabelTimes("ER* JN 11a-11p"), { startMin: 11 * 60, endMin: 23 * 60 });
  assert.deepEqual(parseLabelTimes("ER* 12p-10p"), { startMin: 12 * 60, endMin: 22 * 60 });
  assert.deepEqual(parseLabelTimes("ER-1 Weekend 8p-8a"), { startMin: 20 * 60, endMin: 8 * 60 });
  assert.equal(parseLabelTimes("Red Senior PGY-3"), null);
  assert.equal(isErRowLabel("ER 7a-7p"), true);
  assert.equal(isErRowLabel("Blue Senior"), false);
  assert.equal(pedsTitle("ER-1* 8p-6a"), "Peds ER-1 8p-6a");
});

test("EM name prefixes", () => {
  assert.deepEqual(parseEmName("ED 2 - Setty"), { program: "ED", pgy: 2, last: "Setty" });
  assert.deepEqual(parseEmName("ER 3 - Garza Cantu"), { program: "ER", pgy: 3, last: "Garza Cantu" });
  assert.equal(parseEmName("MP- 3 Bowen"), null);
  assert.equal(parseEmName("CHI 3 - Theis-Higuera"), null);
  assert.equal(parseEmName("FM1 - Dalling"), null);
  assert.equal(parseEmName("Islam"), null);
});

test("footnote markers are stripped from names", () => {
  const html = `</font><font color=#ff0000>ER 3 - Dooley<a href=#><img src="../oci/pnote0.gif" width=13 height=13 border=0 title="Trade with Dr. Perron" onclick='alert("Trade with Dr. Perron");'"></a><font style='font-size:8px; vertical-align:50%;'>3</font>`;
  assert.deepEqual(cellNames(html), ["ER 3 - Dooley"]);
  assert.deepEqual(cellNames(`<em>A</em><br>ED 1 - B`), ["A", "ED 1 - B"]);
  assert.deepEqual(cellNames(`--`), []);
});

test("title year belongs to the end date", () => {
  assert.deepEqual(parseRange("All shifts, 12/7 to 1/10, 2027"), { start: "2026-12-07", end: "2027-01-10" });
  assert.deepEqual(parseRange("All shifts, 10/12 to 11/15, 2026"), { start: "2026-10-12", end: "2026-11-15" });
});

test("grid parsing maps columns to dates, skips ward rows, survives holiday labels", () => {
  const p = parseShiftPage(thanksgiving);
  const setty = p.entries.filter((e) => /Setty/.test(e.name)).map((e) => `${e.date} ${e.label}`);
  assert.deepEqual(setty, ["2026-11-23 ER* 9p-7a", "2026-11-24 ER* 3PM - 11PM", "2026-11-29 ER-2 weekend 7p-7a"]);
  assert.ok(p.entries.some((e) => e.date === "2026-11-26" && e.name === "ER 3 - Garza Cantu"));
  assert.match(p.next, /^https:\/\/www\.amion\.com\/cgi-bin\/ocs\?File=!tok&Page=Shift.*Yjd=2/);
  assert.match(p.prev, /File=!tok&Page=Shift/); // &amp; decoded
});

test("a header that disagrees with the title throws instead of shifting dates", () => {
  const bad = thanksgiving.replace("24 Tu", "25 Tu");
  assert.throws(() => parseShiftPage(bad), /mismatch/);
});

test("Eastern wall clock -> UTC across the Nov 1 2026 DST change", () => {
  assert.equal(easternToUtcISO("2026-10-31", 21 * 60), "2026-11-01T01:00:00.000Z"); // EDT
  assert.equal(easternToUtcISO("2026-11-01", 7 * 60), "2026-11-01T12:00:00.000Z"); // EST
  assert.equal(easternToUtcISO("2027-03-14", 7 * 60), "2027-03-14T11:00:00.000Z"); // EDT again
});

test("matching to app people by QGenda last name; overnight ends next day", () => {
  const q = [
    { person: "Aakash", title: "Eve1 2p-10p [Setty EM28]" },
    { person: "Aakash", title: "Z1 Day [Setty EM28]" },
    { person: "Priscilla", title: "Z1 Day 2/3 7a-3p [Lozano EM28]" },
  ];
  const names = lastNamesFromQgenda(q);
  assert.equal(names.get("Aakash"), "Setty");
  const entries = [
    { date: "2026-10-31", label: "ER* 9p-7a", name: "ED 2 - Setty" },
    { date: "2026-10-31", label: "ER* 9p-7a", name: "ED 2 - Rhee" },
    { date: "2026-10-31", label: "ER* 9p-7a", name: "Islam" },
  ];
  const { shifts, unmatched } = toAppShifts(entries, names);
  assert.equal(shifts.length, 1);
  assert.deepEqual(shifts[0], {
    person: "Aakash",
    title: "Peds ER 9p-7a [Setty ED2]",
    dateOnly: false,
    start: "2026-11-01T01:00:00.000Z",
    end: "2026-11-01T12:00:00.000Z", // 11 real hours: clocks fell back
    source: "amion-peds",
  });
  assert.deepEqual(unmatched, ["ED 2 - Rhee"]);
});

test("fetch flow: login -> Shift link -> follow Next rotation, merge overlap", async () => {
  const p1 = page({
    title: "All shifts, 11/23 to 11/29, 2026",
    next: "Yjd=200",
    weeks: [
      { header: [null, "23 Mo", "24 Tu", "25 We", "26 Th", "27 Fr", "28 Sa"], rows: [["ER* 7a-3p", [nb, name("ED 2 - Setty"), dash, dash, dash, dash, dash]]] },
      { header: ["29 Su", null, null, null, null, null, null], rows: [["ER* 7a-3p", [name("ED 1 - Old"), nb, nb, nb, nb, nb, nb]]] },
    ],
  });
  const p2 = page({
    title: "All shifts, 11/29 to 12/5, 2026",
    next: "Yjd=300",
    weeks: [
      { header: ["29 Su", "30 Mo", "1 December", "2 We", "3 Th", "4 Fr", "5 Sa"], rows: [["ER* 7a-3p", [name("ED 1 - New"), dash, name("ED 2 - Setty"), dash, dash, dash, dash]]] },
    ],
  });
  const calls = [];
  const fakeFetch = async (url) => {
    calls.push(url);
    let body;
    if (url.includes("Lo=umipe")) body = `<a href="./ocs?File=!1a4bd2c8humi_peds&Page=Shift&Adb=1">Shift</a>`;
    else if (url.includes("Yjd=200")) body = p2;
    else if (url.includes("Page=Shift")) body = p1;
    else throw new Error("unexpected " + url);
    return { ok: true, status: 200, text: async () => body };
  };
  const r = await fetchPedsGrid({ login: "umipe", fromDate: "2026-11-23", toDate: "2026-12-05", fetchImpl: fakeFetch });
  assert.equal(calls.length, 3);
  assert.equal(r.coveredFrom, "2026-11-23");
  assert.equal(r.coveredTo, "2026-12-05");
  const nov29 = r.entries.filter((e) => e.date === "2026-11-29").map((e) => e.name);
  assert.equal(nov29.length, 1); // overlap day not double counted
  assert.ok(r.entries.some((e) => e.date === "2026-12-01" && e.name === "ED 2 - Setty"));
});
