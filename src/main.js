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
    $("#freshness").title = DATA.errors.map((e) => `${e.person}: ${e.error}`).join("\n");
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
          ${stampRow([weekendStamp(s), edtra, typeStamp].filter(Boolean))}
        </div>
        <button class="review-btn" data-id="${esc(s.id)}">Review</button>
      </div>`;
    }
  }
  box.innerHTML = html;
  enterAnimate("#trades");
}

// ---------------- The sheet (trade memo) ----------------

function folioHTML(o) {
  const ws = weekStart(o.gets.start);
  const we = weekEnd(o.gets.start);
  const span = we - ws;
  const pct = (t) => Math.max(0, Math.min(100, ((t - ws) / span) * 100));

  const seg = (s, cls) => {
    const l = pct(s.start), r = pct(s.end);
    if (r <= l) return "";
    const tip = esc(`${s.title} · ${fmtDayFull(s.start)} ${fmtTime(s.start)}–${fmtTime(s.end)}`);
    return `<div class="tl-seg ${cls}" style="left:${l.toFixed(2)}%;width:${Math.max(r - l, 1.4).toFixed(2)}%" title="${tip}"></div>`;
  };

  let segs = "";
  for (const s of o.schedule) if (s.id !== o.gets.id) segs += seg(s, "other");
  const removedInWeek = o.removed.end > ws && o.removed.start < we;
  if (removedInWeek) segs += seg(o.removed, "removed");
  segs += seg(o.gets, "new");

  let days = "", grid = "";
  for (let i = 0; i < 7; i++) {
    const d = new Date(ws);
    d.setDate(ws.getDate() + i);
    days += `<div><span class="dw">${dow(d)}</span><span class="dt">${d.getDate()}</span></div>`;
    grid += `<div class="${i >= 5 ? "we" : ""}"></div>`;
  }

  const prevOK = o.pos.prev ? o.prevGap >= durationHours(o.pos.prev) : true;
  const nextOK = o.pos.next ? o.nextGap >= durationHours(o.gets) : true;
  const capOk = o.weekTotal <= 60.0;
  const fOK = capOk && prevOK && nextOK;

  const loadPct = Math.min(100, (o.weekTotal / 60) * 100);
  const loadCls = !capOk ? "bad" : o.weekTotal > 54 ? "warn" : "ok";

  const line = (cls, sign, verb, s) =>
    `<div class="swap-line ${cls}">
      <span class="sign">${sign}</span><span class="verb">${verb}</span>
      <span class="what">${esc(s.title)}</span>
      <span class="when">${fmtDayFull(s.start)} &middot; ${fmtTime(s.start)}&ndash;${fmtTime(s.end)} &middot; ${fmtDur(s)}</span>
    </div>`;

  const restCell = (label, neighbor, gap, needed, ok) => {
    if (!neighbor) return `<div class="rest-cell"><div class="lab">${label}</div><div class="val">&mdash; <span class="hint">no adjacent shift</span></div></div>`;
    return `<div class="rest-cell ${ok ? "" : "bad"}"><div class="lab">${label}</div>
      <div class="val">${gap.toFixed(1)}h <span class="${ok ? "okmark" : "badmark"}">${ok ? "✓" : "✗"}</span>
      <span class="hint">needs &ge; ${needed.toFixed(1)}h</span></div></div>`;
  };

  const weekLabel = `${fmtMonDay(ws)} &ndash; ${fmtMonDay(new Date(we - 1))}`;

  return `<div class="folio">
    <div class="folio-head">
      <div class="folio-name">${esc(o.name)}${o.isMe ? '<span class="you-chip">you</span>' : ""}</div>
      <div class="verdict ${fOK ? "good" : "warn"}">${fOK ? "All rules pass" : "Review"}</div>
    </div>
    ${line("gives", "&minus;", "Gives", o.gives)}
    ${line("gets", "+", "Gets", o.gets)}
    <div class="tl-block">
      <div class="tl-cap">Week of ${weekLabel} <span class="soft">(after swap)</span></div>
      <div class="tl-days">${days}</div>
      <div class="tl-strip"><div class="tl-grid">${grid}</div>${segs}</div>
      <div class="tl-key">
        <span><span class="k new"></span>New shift</span>
        <span><span class="k other"></span>Existing</span>
        ${removedInWeek ? '<span><span class="k removed"></span>Given away</span>' : ""}
      </div>
    </div>
    <div class="ledger">
      <div class="ledger-head"><span>Weekly hours after swap</span>
        <strong class="${capOk ? "" : "over"}"><span class="count" data-count="${o.weekTotal.toFixed(1)}">0.0</span>h <span class="of">/ 60h</span></strong>
      </div>
      <div class="ledger-bar"><div class="ledger-fill ${loadCls}" data-width="${loadPct.toFixed(1)}"></div></div>
    </div>
    <div class="rest-row">
      ${restCell("Rest before", o.pos.prev, o.prevGap, o.pos.prev ? durationHours(o.pos.prev) : null, prevOK)}
      ${restCell("Rest after", o.pos.next, o.nextGap, durationHours(o.gets), nextOK)}
    </div>
  </div>`;
}

function findPrevNext(sorted, id) {
  const idx = sorted.findIndex((s) => s.id === id);
  return {
    prev: idx > 0 ? sorted[idx - 1] : null,
    next: idx >= 0 && idx + 1 < sorted.length ? sorted[idx + 1] : null,
  };
}

const cloneFor = (person, s) => ({ ...s, person, id: `${person}|${s.start.getTime()}|${s.end.getTime()}|${s.title}` });

function sumWeek(sched, anchor) {
  const ws = weekStart(anchor), we = weekEnd(anchor);
  let t = 0;
  for (const s of sched) if (s.start >= ws && s.start < we) t += durationHours(s);
  return t;
}

// Build the folioHTML input for one participant who gives up `giveShift`
// (a real shift on their calendar) and takes on `receiveShift`.
function buildFolio(name, isMe, giveShift, receiveShift) {
  const clone = cloneFor(name, receiveShift);
  const sched = (DATA.schedules.get(name) || []).filter((x) => x.id !== giveShift.id).concat([clone]).sort((a, b) => a.start - b.start);
  const pos = findPrevNext(sched, clone.id);
  return {
    name, isMe, gives: giveShift, gets: clone, removed: giveShift, schedule: sched, pos,
    prevGap: pos.prev ? gapHours(pos.prev.end, clone.start) : null,
    nextGap: pos.next ? gapHours(clone.end, pos.next.start) : null,
    weekTotal: sumWeek(sched, clone.start),
  };
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
  const compare = $("#compare");
  compare.className = "compare";
  compare.innerHTML =
    folioHTML(buildFolio(ME, true, mineShift, theirShift)) +
    folioHTML(buildFolio(partner, false, theirShift, mineShift));

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

  const compare = $("#compare");
  compare.className = "compare compare-3";
  compare.innerHTML =
    folioHTML(buildFolio(ME, true, mineShift, sC)) + // you give yours, get C's
    folioHTML(buildFolio(B, false, sB, mineShift)) + // B gives theirs, gets yours
    folioHTML(buildFolio(C, false, sC, sB));         // C gives theirs, gets B's

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
