// Live check of the peds Amion import. Run: npm run check:amion
// Prints the pages walked, the date range covered, and every EM (ED/ER) resident's shifts.
// Pass a last name to filter, e.g. `npm run check:amion -- Setty`.
import { fetchPedsGrid, parseEmName, parseLabelTimes } from "../netlify/functions/lib/amion-peds.mjs";

const login = process.env.AMION_PEDS_LOGIN || "umipe";
const filter = (process.argv[2] || "").toLowerCase();
const fmt = (d) => d.toISOString().slice(0, 10);
const now = Date.now();
const r = await fetchPedsGrid({ login, fromDate: fmt(new Date(now - 21 * 864e5)), toDate: fmt(new Date(now + 92 * 864e5)) });
console.log(`Pages: ${r.pages}  Covered: ${r.coveredFrom} to ${r.coveredTo}`);
const em = r.entries.filter((e) => parseEmName(e.name) && (!filter || e.name.toLowerCase().includes(filter)));
for (const e of em.sort((a, b) => a.name.localeCompare(b.name) || a.date.localeCompare(b.date))) {
  const t = parseLabelTimes(e.label);
  console.log(`${e.name.padEnd(24)} ${e.date}  ${e.label}${t ? "" : "  (no time!)"}`);
}
