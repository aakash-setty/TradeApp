// Spot checks of the block-schedule transcription against the PGY-II / PGY-III grids.
import test from "node:test";
import assert from "node:assert/strict";
import { awayInWeek, BLOCK_ROWS } from "../src/blocks.js";

const wk = (y, m, d) => [new Date(y, m - 1, d), new Date(y, m - 1, d + 7)];
const names = (g, t) => g[t].map((p) => p.name);

test("week of Nov 16 2026", () => {
  const g = awayInWeek(...wk(2026, 11, 16));
  assert.deepEqual(names(g, "Vacation"), ["Lozano", "Morgan", "Cozart", "Frantz", "Gorman", "Johansson"]); // PGY-2 first
  assert.deepEqual(names(g, "Elective"), ["Rhee"]);
  assert.deepEqual(names(g, "Ultrasound"), []);
});

test("week of Mar 22 2027 (busy week)", () => {
  const g = awayInWeek(...wk(2027, 3, 22));
  assert.deepEqual(names(g, "Vacation"), ["McClain", "Rhee", "Ruiz", "Tummings"]);
  assert.deepEqual(names(g, "Elective"), ["Cuevas", "King"]);
  assert.deepEqual(names(g, "Ultrasound"), ["Saxena"]);
});

test("Vac variants are Vacation, and the long June columns cover their days", () => {
  assert.ok(BLOCK_ROWS.some(([s, , n, , t]) => s === "2027-01-11" && n === "Lynch" && t === "Vacation")); // "Vac UM"
  const june = awayInWeek(...wk(2027, 6, 21)); // spans the 06/14 (to 6/23) and 6/24-6/30 columns
  assert.deepEqual(names(june, "Ultrasound"), ["Lynch"]);
  assert.ok(names(june, "Vacation").includes("Saxena"));
});
