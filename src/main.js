import "@fontsource-variable/inter";
import "@fontsource-variable/fraunces/opsz.css";
import "@fontsource-variable/fraunces/opsz-italic.css";
import "./style.css";

import { createIcons, RefreshCw, Moon, Sun, X, Feather } from "lucide";
import { animate, stagger } from "motion";
import confetti from "canvas-confetti";

import {
  buildData,
  tradeOptions,
  threeWayOptions,
  simulateSwapOk,
  personWorksEdTraInWeek,
  personWorksPedsInWeek,
  isPedsTitle,
  weekHours,
  inferBlock,
  isWeekendStart,
  weekStart,
  weekEnd,
  durationHours,
  gapHours,
} from "./rules.js";

const $ = (s) => document.querySelector(s);
const ICONS = { RefreshCw, Moon, Sun, X, Feather };
const refreshIcons = () => createIcons({ icons: ICONS });

// ---------------- State ----------------

let DATA = null;
let ME = null;
let SELECTED = null;
let TRADE = null;
let OPTION_INDEX = new Map();
let INCLUDE_3WAY = false;
let _threeTimer = null;
let SHEET3 = null;

// ---------------- Formatting ----------------

function esc(s) {
  return String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
}
const fmtTime = (d) => d.toLocaleTimeString("en-US", { hour: "numeric", minute: "2-digit" });
const fmtDayFull = (d) => d.toLocaleDateString("en-US", { weekday: "short", month: "short", day: "numeric" });
const fmtMonDay = (d) => d.toLocaleDateString("en-US", { month: "short", day: "numeric" });
const dow = (d) => d.toLocaleDateString("en-US", { weekday: "short" });
const mon = (d) => d.toLocaleDateString("en-US", { month: "short" });
function fmtDur(s) {
  const h = durationHours(s);
  return (h % 1 ? h.toFixed(1) : String(h)) + "h";
}
// Compact clock for the date tile: 9:00 AM -> "9a", 3:30 PM -> "3:30p"
function compactTime(d) {
  let h = d.getHours();
  const m = d.getMinutes();
  const ap = h >= 12 ? "p" : "a";
  h = h % 12 || 12;
  return (m ? `${h}:${String(m).padStart(2, "0")}` : `${h}`) + ap;
}
function compactRange(s) {
  return `${compactTime(s.start)}–${compactTime(s.end)}`;
}

// ---------------- Theme ----------------

function applyTheme(theme, persist = true) {
  if (theme === "dark") document.documentElement.dataset.theme = "dark";
  else delete document.documentElement.dataset.theme;
  const icon = $("#theme i") || $("#theme svg");
  if (icon) icon.setAttribute("data-lucide", theme === "dark" ? "sun" : "moon");
  refreshIcons();
  if (persist) {
    try { localStorage.setItem("ink-theme", theme); } catch (e) {}
  }
}

// ---------------- Loading ----------------

function skeletons(n) {
  return Array.from({ length: n }, () => `<div class="skeleton"></div>`).join("");
}

async function load() {
  const refreshBtn = $("#refresh");
  refreshBtn.classList.add("spinning");
  $("#me").disabled = true;
  $("#mine").innerHTML = skeletons(4);
  $("#trades").innerHTML = skeletons(5);

  try {
    const r = await fetch("/api/shifts");
    if (!r.ok) throw new Error(`server responded ${r.status}`);
    const payload = await r.json();
    if (payload.error) throw new Error(payload.error);

    DATA = buildData(payload);
    if (!ME || !DATA.people.includes(ME)) ME = DATA.people[0];

    renderPeople();
    renderMine();

    const at = fmtTime(new Date(payload.fetchedAt || Date.now()));
    const failed = DATA.errors.length ? ` · ${DATA.errors.length} feed${DATA.errors.length > 1 ? "s" : ""} unreachable` : "";
    $("#freshness").textContent = `Updated ${at}${failed}`;
    const tip = DATA.errors.map((e) => `${e.person}: ${e.error}`);
    const p = DATA.peds;
    if (p && p.ok) {
      tip.push(`Peds ER (Amion): ${p.count} shifts, ${p.coveredFrom} to ${p.coveredTo}`);
      if (p.peopleWithoutLastName && p.peopleWithoutLastName.length) tip.push(`No last name found for: ${p.peopleWithoutLastName.join(", ")}`);
      if (p.conflicts && p.conflicts.length) tip.push(...p.conflicts);
    }
    $("#freshness").title = tip.join("\n");
  } catch (e) {
    const msg = esc(e && e.message ? e.message : String(e));
    $("#mine").innerHTML = `<div class="error-note">Couldn&rsquo;t load the schedules (${msg}).<button id="retryBtn">Try again</button></div>`;
    $("#trades").innerHTML = `<div class="empty"><span class="fleuron">&#10086;</span>Waiting on schedules.</div>`;
    const retry = $("#retryBtn");
    if (retry) retry.addEventListener("click", load);
  } finally {
    refreshBtn.classList.remove("spinning");
    $("#me").disabled = !DATA;
  }
}

// ---------------- Rendering ----------------

function renderPeople() {
  const sel = $("#me");
  sel.innerHTML = DATA.people.map((p) => `<option value="${esc(p)}" ${p === ME ? "selected" : ""}>${esc(p)}</option>`).join("");
}

function myShifts() {
  return DATA.flat.filter((s) => s.person === ME && s.eligible);
}

function groupByWeek(shifts) {
  const groups = new Map();
  for (const s of shifts) {
    const k = weekStart(s.start).getTime();
    if (!groups.has(k)) groups.set(k, []);
    groups.get(k).push(s);
  }
  return groups;
}

function dateTile(s) {
  const wkndTile = s.start.getDay() === 0 || s.start.getDay() === 6;
  return `<div class="date-tile ${wkndTile ? "wkend" : ""}">
    <span class="dow">${dow(s.start)}</span>
    <span class="dom">${s.start.getDate()}</span>
    <span class="tt">${compactRange(s)}</span>
  </div>`;
}

function stampRow(stamps) {
  if (!stamps.length) return "";
  return `<div class="stamps">${stamps.join("")}</div>`;
}

function weekendStamp(s) {
  return isWeekendStart(s.start) ? `<span class="stamp stamp-red">Weekend</span>` : "";
}

function enterAnimate(scope) {
  const els = document.querySelectorAll(`${scope} .card.enter`);
  if (!els.length) return;
  const reveal = () => els.forEach((el) => { el.style.opacity = "1"; el.style.transform = "none"; });
  // Cap total stagger so long lists (e.g. 3-way results) don't crawl in.
  const step = Math.min(0.035, 0.8 / els.length);
  try {
    const anim = animate(
      els,
      { opacity: [0, 1], transform: ["translateY(9px)", "translateY(0px)"] },
      { delay: stagger(step), duration: 0.4, ease: "easeOut" }
    );
    if (anim && anim.finished && typeof anim.finished.then === "function") anim.finished.then(reveal).catch(() => {});
  } catch (e) {
    reveal();
  }
  // Safety net: guarantee visibility even if the animation is throttled or interrupted.
  setTimeout(reveal, (step * els.length + 0.5) * 1000);
}

function renderMine() {
  const mine = myShifts();
  const box = $("#mine");

  if (!mine.length) {
    box.innerHTML = `<div class="empty"><span class="fleuron">&#10086;</span>No tradable shifts on ${esc(ME)}&rsquo;s calendar.</div>`;
    SELECTED = null;
    renderTrades();
    return;
  }

  if (!mine.some((s) => s.id === SELECTED)) SELECTED = mine[0].id;

  let html = "";
  for (const [ws, shifts] of groupByWeek(mine)) {
    html += `<div class="week-head">Week of ${fmtMonDay(new Date(Number(ws)))}</div>`;
    for (const s of shifts) {
      const durPct = Math.min(100, (durationHours(s) / 12) * 100);
      html += `<div class="card clickable enter ${s.id === SELECTED ? "selected" : ""}" data-id="${esc(s.id)}" tabindex="0" role="button"
        aria-label="Trade away ${esc(s.title)}, ${fmtDayFull(s.start)}">
        ${dateTile(s)}
        <div class="card-body">
          <div class="card-title">${esc(s.title)}</div>
          <div class="dur-bar"><div class="dur-fill" style="width:${durPct.toFixed(0)}%"></div></div>
          ${stampRow([weekendStamp(s)].filter(Boolean))}
        </div>
      </div>`;
    }
  }
  box.innerHTML = html;
  enterAnimate("#mine");
  renderTrades();
}

function emptyMsg(text) {
  return `<div class="empty"><span class="fleuron">&#10086;</span>${text}</div>`;
}

function renderTrades() {
  const box = $("#trades");
  OPTION_INDEX = new Map();
  clearTimeout(_threeTimer);

  const mineShift = DATA && DATA.flat.find((s) => s.id === SELECTED);
  if (!mineShift) {
    box.innerHTML = emptyMsg("Choose one of your shifts to see who can take it.");
    return;
  }

  if (INCLUDE_3WAY) {
    // 3-way search is heavier; paint a loader first, then compute on the next tick.
    box.innerHTML = `<div class="trades-loading"><span class="spin" aria-hidden="true"></span>Finding 2-way &amp; 3-way trades&hellip;</div>`;
    _threeTimer = setTimeout(() => buildTradesList(mineShift, true), 20);
  } else {
    buildTradesList(mineShift, false);
  }
}

function buildTradesList(mineShift, include3) {
  const box = $("#trades");

  const direct = tradeOptions(DATA.flat, DATA.schedules, mineShift);
  const directIds = new Set(direct.map((s) => s.id));
  const entries = direct.map((s) => ({ type: "direct", acquire: s }));

  if (include3) {
    for (const g of threeWayOptions(DATA.flat, DATA.schedules, mineShift)) {
      if (directIds.has(g.acquire.id)) continue; // a simpler direct route already covers this shift
      entries.push({ type: "3way", acquire: g.acquire, from: g.from, middles: g.middles });
    }
  }

  if (!entries.length) {
    box.innerHTML = emptyMsg(
      include3 ? "No 2-way or 3-way trades for that shift right now." : "No valid trades for that shift right now &mdash; try another."
    );
    return;
  }

  entries.sort((a, b) => a.acquire.start - b.acquire.start || a.acquire.person.localeCompare(b.acquire.person));

  const weekGroups = new Map();
  for (const e of entries) {
    const k = weekStart(e.acquire.start).getTime();
    if (!weekGroups.has(k)) weekGroups.set(k, []);
    weekGroups.get(k).push(e);
  }

  let html = "";
  for (const [ws, group] of weekGroups) {
    html += `<div class="week-head">Week of ${fmtMonDay(new Date(Number(ws)))}</div>`;
    for (const e of group) {
      const s = e.acquire;
      OPTION_INDEX.set(s.id, e);
      const person = e.type === "3way" ? e.from : s.person;
      const edtra = personWorksEdTraInWeek(DATA.all, person, mineShift.start)
        ? `<span class="stamp stamp-amber">ED/Tra</span>` : "";
      const pedsStamp = personWorksPedsInWeek(DATA.all, person, mineShift.start)
        ? `<span class="stamp stamp-peds">Peds</span>` : "";
      const typeStamp = e.type === "3way" ? `<span class="stamp stamp-3way">3-way</span>` : "";
      const chain =
        e.type === "3way"
          ? `<div class="chain-hint">${esc(e.middles[0].person)} takes yours${e.middles.length > 1 ? ` &middot; +${e.middles.length - 1} route${e.middles.length - 1 > 1 ? "s" : ""}` : ""}</div>`
          : "";
      html += `<div class="card enter" data-id="${esc(s.id)}">
        ${dateTile(s)}
        <div class="card-body">
          <div class="card-title"><span class="with">with ${esc(person)}</span> &middot; ${esc(s.title)}</div>
          ${chain}
          ${stampRow([weekendStamp(s), edtra, pedsStamp, typeStamp].filter(Boolean))}
        </div>
        <button class="review-btn" data-id="${esc(s.id)}">Review</button>
      </div>`;
    }
  }
  box.innerHTML = html;
  enterAnimate("#trades");
}

// ---------------- The sheet (trade memo) ----------------
// One column per shift that changes hands. Under each shift: the Mon-Sun week it falls
// in, and for both people involved (giver and receiver) their inferred block and total
// hours that week after the whole trade.

const LOW_HOURS = 20;

const cloneFor = (person, s) => ({ ...s, person, id: `${person}|${s.start.getTime()}|${s.end.getTime()}|${s.title}` });

// legs: [{shift, from, to}] — every shift that moves in this trade.
function postSchedule(person, legs) {
  const giving = new Set(legs.filter((l) => l.from === person).map((l) => l.shift.id));
  const receiving = legs.filter((l) => l.to === person).map((l) => cloneFor(person, l.shift));
  return (DATA.schedules.get(person) || [])
    .filter((s) => !giving.has(s.id))
    .concat(receiving)
    .sort((a, b) => a.start - b.start);
}

function restCheck(sched, shiftId) {
  const idx = sched.findIndex((s) => s.id === shiftId);
  const prev = idx > 0 ? sched[idx - 1] : null;
  const cur = sched[idx];
  const next = idx >= 0 && idx + 1 < sched.length ? sched[idx + 1] : null;
  const out = [];
  if (prev) {
    const gap = gapHours(prev.end, cur.start), need = durationHours(prev);
    out.push({ label: "Rest before", gap, need, ok: gap >= need });
  }
  if (next) {
    const gap = gapHours(cur.end, next.start), need = durationHours(cur);
    out.push({ label: "Rest after", gap, need, ok: gap >= need });
  }
  return out;
}

const fmtH = (h) => (Math.abs(h % 1) > 1e-9 ? h.toFixed(1) : String(Math.round(h))) + "h";

function personRow(person, leg, legs) {
  const before = DATA.schedules.get(person) || [];
  const after = postSchedule(person, legs);
  const anchor = leg.shift.start;
  const hAfter = weekHours(after, anchor);
  const hBefore = weekHours(before, anchor);
  const block = inferBlock(before, anchor);
  const isMe = person === ME;
  const role = person === leg.from ? "gives this shift" : "takes this shift";
  const delta = hAfter === hBefore ? "no change" : `was ${fmtH(hBefore)}`;
  const capCls = hAfter > 60 ? "bad" : hAfter < LOW_HOURS ? "low" : "";

  let rest = "";
  if (person === leg.to) {
    const id = cloneFor(person, leg.shift).id;
    rest = restCheck(after, id)
      .map((r) => `<span class="rest-chip ${r.ok ? "" : "bad"}">${r.label} ${fmtH(r.gap)} ${r.ok ? "✓" : "✗"}<span class="hint"> needs ${fmtH(r.need)}</span></span>`)
      .join("");
    if (!rest) rest = `<span class="rest-chip">No shifts nearby</span>`;
  }

  const low = hAfter < LOW_HOURS
    ? `<div class="low-note" role="alert"><span class="low-icon" aria-hidden="true">!</span><div><strong>Check manually.</strong> ${esc(person)} is either on a non-EM/trauma rotation or on a vacation week (or that week isn&rsquo;t published yet).</div></div>`
    : "";

  return `<div class="pw-row ${person === leg.from ? "is-old" : ""}">
    <div class="pw-head">
      <span class="pw-name">${esc(person)}${isMe ? '<span class="you-chip">you</span>' : ""}</span>
      <span class="pw-role">${role}</span>
    </div>
    <div class="pw-grid">
      <div class="pw-cell"><div class="lab">Block <span class="soft">(inferred)</span></div><div class="val">${esc(block)}</div></div>
      <div class="pw-cell"><div class="lab">Hours this week</div><div class="val ${capCls}">${fmtH(hAfter)} <span class="hint">${delta} &middot; cap 60h</span></div></div>
    </div>
    ${rest ? `<div class="rest-chips">${rest}</div>` : ""}
    ${low}
  </div>`;
}

// The shift cards on top, in their own box. The shift leaving your schedule is grayed out.
function shiftCard(leg, heading, old) {
  const s = leg.shift;
  const peds = isPedsTitle(s.title) ? `<span class="stamp stamp-peds">Peds ER</span>` : "";
  return `<div class="leg-shift ${old ? "is-old" : "is-new"}">
    <div class="leg-kicker">${heading}${old ? '<span class="old-tag">leaves your schedule</span>' : ""}</div>
    <div class="what">${esc(s.title)} ${peds}</div>
    <div class="when">${fmtDayFull(s.start)} &middot; ${fmtTime(s.start)}&ndash;${fmtTime(s.end)} &middot; ${fmtDur(s)}</div>
    <div class="flow">${esc(leg.from)} &rarr; ${esc(leg.to)}</div>
  </div>`;
}

// One panel per shift: that shift's Mon-Sun week, for both people involved.
function legColumn(leg, legs, heading) {
  const s = leg.shift;
  const ws = weekStart(s.start), we = weekEnd(s.start);
  return `<div class="leg">
    <div class="leg-week">${heading} &middot; week of ${fmtMonDay(ws)} &ndash; ${fmtMonDay(new Date(we - 1))} <span class="soft">(after trade)</span></div>
    ${personRow(leg.from, leg, legs)}
    ${personRow(leg.to, leg, legs)}
  </div>`;
}

function renderLegs(columns) {
  const legs = columns.map((c) => c.leg);
  const n = columns.length;
  const compare = $("#compare");
  compare.className = "review";
  compare.innerHTML =
    `<div class="swap-box legs-${n}">${columns.map((c) => shiftCard(c.leg, c.heading, c.leg.from === ME)).join("")}</div>` +
    `<div class="compare legs-${n}">${columns.map((c) => legColumn(c.leg, legs, c.heading)).join("")}</div>`;
}

function animateSheet() {
  requestAnimationFrame(() => {
    document.querySelectorAll("#compare .ledger-fill").forEach((el) => {
      el.style.width = el.dataset.width + "%";
    });
    document.querySelectorAll("#compare .count").forEach((el) => {
      const target = parseFloat(el.dataset.count);
      try {
        animate(0, target, { duration: 0.8, ease: "easeOut", onUpdate: (v) => (el.textContent = v.toFixed(1)) });
      } catch (e) {
        el.textContent = target.toFixed(1);
      }
    });
  });
}

function showBackdrop() {
  $("#backdrop").hidden = false;
  document.body.style.overflow = "hidden";
  refreshIcons();
}

function openSheet(theirShift) {
  const mineShift = DATA.flat.find((s) => s.id === SELECTED);
  if (!mineShift) return;

  const [ok] = simulateSwapOk(DATA.schedules, mineShift, theirShift);
  if (!ok) { renderTrades(); return; }

  const partner = theirShift.person;
  TRADE = { kind: "direct", me: ME, partner, myShift: mineShift, theirShift };

  $("#sheetTitle").innerHTML = `An exchange with <em>${esc(partner)}</em>`;
  $("#loopArea").innerHTML = "";
  renderLegs([
    { heading: "You give", leg: { shift: mineShift, from: ME, to: partner } },
    { heading: "You get", leg: { shift: theirShift, from: partner, to: ME } },
  ]);

  fillSummary();
  setCopied(false);
  animateSheet();
  showBackdrop();
}

// ---------------- 3-way sheet ----------------

function open3Way(entry) {
  SHEET3 = { entry, midIdx: 0 };
  setCopied(false);
  render3Way();
  showBackdrop();
}

function render3Way() {
  const { entry, midIdx } = SHEET3;
  const mineShift = DATA.flat.find((s) => s.id === SELECTED);
  const sC = entry.acquire;
  const C = entry.from;
  const sB = entry.middles[midIdx];
  const B = sB.person;

  TRADE = { kind: "3way", me: ME, myShift: mineShift, acquire: sC, bPerson: B, bShift: sB, cPerson: C };

  $("#sheetTitle").innerHTML = `A 3-way loop with <em>${esc(B)}</em> &amp; <em>${esc(C)}</em>`;
  $("#loopArea").innerHTML = loopDiagram(ME, mineShift, B, sB, C, sC) + (entry.middles.length > 1 ? middleSelector(entry, midIdx) : "");

  renderLegs([
    { heading: "You give", leg: { shift: mineShift, from: ME, to: B } },
    { heading: "You get", leg: { shift: sC, from: C, to: ME } },
    { heading: "Middle leg", leg: { shift: sB, from: B, to: C } },
  ]);

  fillSummary();
  animateSheet();
  refreshIcons();
}

function loopNode(name, role) {
  return `<div class="loop-node"><div class="loop-name">${esc(name)}</div>${role ? `<div class="loop-role">${role}</div>` : ""}</div>`;
}
function loopArrow(s) {
  return `<div class="loop-arrow"><span class="loop-pass">${esc(s.title)}</span><span class="loop-line"></span><span class="loop-when">${fmtMonDay(s.start)}</span></div>`;
}
function loopDiagram(me, sA, B, sB, C, sC) {
  return `<div class="loop-diagram" aria-label="Trade loop">
    ${loopNode(me + " (you)", "give")}
    ${loopArrow(sA)}
    ${loopNode(B, "")}
    ${loopArrow(sB)}
    ${loopNode(C, "")}
    ${loopArrow(sC)}
    ${loopNode(me + " (you)", "receive")}
  </div>`;
}
function middleSelector(entry, midIdx) {
  const chips = entry.middles
    .map((sB, i) => `<button class="mid-chip ${i === midIdx ? "on" : ""}" data-mid="${i}">${esc(sB.person)} &middot; ${fmtMonDay(sB.start)}</button>`)
    .join("");
  return `<div class="mid-select"><span class="mid-label">Middle person &mdash; ${entry.middles.length} options:</span><div class="mid-chips">${chips}</div></div>`;
}

function closeSheet() {
  $("#backdrop").hidden = true;
  document.body.style.overflow = "";
}

// ---------------- Trade summary ----------------

// "Z2 Eve 1 3p-11p [Setty EM28]" -> "Z2 Eve 1 3p-11p"
function summaryTitle(s) {
  return s.title.replace(/\s*\[.*$/, "").trim();
}
// Date -> "Friday August 24"
function summaryDate(d) {
  return `${d.toLocaleDateString("en-US", { weekday: "long" })} ${d.toLocaleDateString("en-US", { month: "long" })} ${d.getDate()}`;
}
function takesLine(receiver, giver, shift) {
  return `${receiver} will take ${giver}'s shift on ${summaryDate(shift.start)} ${summaryTitle(shift)}.`;
}

function buildSummary() {
  if (!TRADE) return "";
  if (TRADE.kind === "3way") {
    const { me, myShift, acquire, bPerson, bShift, cPerson } = TRADE;
    return [
      takesLine(me, cPerson, acquire),     // you take C's shift
      takesLine(bPerson, me, myShift),      // B takes your shift
      takesLine(cPerson, bPerson, bShift),  // C takes B's shift
    ].join(" ");
  }
  const { me, partner, myShift, theirShift } = TRADE;
  return [
    takesLine(me, partner, theirShift),   // you take partner's shift
    takesLine(partner, me, myShift),       // partner takes your shift
  ].join(" ");
}

function fillSummary() {
  $("#msg").value = buildSummary();
}

function setCopied(on) {
  $("#copyBtn").classList.toggle("copied", on);
  $("#copyLabel").textContent = on ? "Copied" : "Copy summary";
}

async function copyNote() {
  try {
    await navigator.clipboard.writeText($("#msg").value || "");
    setCopied(true);
    const rect = $("#copyBtn").getBoundingClientRect();
    confetti({
      particleCount: 70,
      spread: 65,
      startVelocity: 28,
      scalar: 0.85,
      ticks: 130,
      colors: ["#9a4515", "#b98a2f", "#3f6f4f", "#ece2cc", "#211c14"],
      origin: { x: (rect.left + rect.width / 2) / innerWidth, y: rect.top / innerHeight },
    });
    setTimeout(() => setCopied(false), 1800);
  } catch (e) {
    $("#msg").focus();
    $("#msg").select();
  }
}

// ---------------- Wiring ----------------

function init() {
  $("#dateline").textContent = new Date().toLocaleDateString("en-US", {
    weekday: "long", year: "numeric", month: "long", day: "numeric",
  });

  applyTheme(document.documentElement.dataset.theme === "dark" ? "dark" : "light", false);

  $("#theme").addEventListener("click", () => {
    applyTheme(document.documentElement.dataset.theme === "dark" ? "light" : "dark");
  });

  $("#me").addEventListener("change", (e) => {
    ME = e.target.value;
    SELECTED = null;
    renderMine();
  });

  $("#refresh").addEventListener("click", load);

  $("#mine").addEventListener("click", (e) => {
    const card = e.target.closest(".card.clickable");
    if (!card) return;
    SELECTED = card.dataset.id;
    document.querySelectorAll("#mine .card").forEach((c) => c.classList.toggle("selected", c.dataset.id === SELECTED));
    renderTrades();
  });
  $("#mine").addEventListener("keydown", (e) => {
    if (e.key !== "Enter" && e.key !== " ") return;
    const card = e.target.closest(".card.clickable");
    if (!card) return;
    e.preventDefault();
    card.click();
  });

  $("#trades").addEventListener("click", (e) => {
    const btn = e.target.closest(".review-btn");
    if (!btn) return;
    const entry = OPTION_INDEX.get(btn.dataset.id);
    if (!entry) return;
    if (entry.type === "3way") open3Way(entry);
    else openSheet(entry.acquire);
  });

  $("#threeWayToggle").addEventListener("click", () => {
    INCLUDE_3WAY = !INCLUDE_3WAY;
    const btn = $("#threeWayToggle");
    btn.setAttribute("aria-pressed", INCLUDE_3WAY ? "true" : "false");
    btn.classList.toggle("on", INCLUDE_3WAY);
    $("#threeWayLabel").textContent = INCLUDE_3WAY ? "Showing 2 + 3-way" : "Show 3-way trades";
    renderTrades();
  });

  $("#loopArea").addEventListener("click", (e) => {
    const chip = e.target.closest(".mid-chip");
    if (!chip || !SHEET3) return;
    SHEET3.midIdx = Number(chip.dataset.mid);
    render3Way();
  });

  $("#closeSheet").addEventListener("click", closeSheet);
  $("#backdrop").addEventListener("click", (e) => {
    if (e.target === $("#backdrop")) closeSheet();
  });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && !$("#backdrop").hidden) closeSheet();
  });

  $("#copyBtn").addEventListener("click", copyNote);

  refreshIcons();
  load();
}

init();
