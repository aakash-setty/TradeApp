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
let TONE = "professional";
let TRADE = null;
let OPTION_INDEX = new Map();

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
    <span class="mon">${mon(s.start)}</span>
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
  try {
    animate(els, { opacity: [0, 1], transform: ["translateY(9px)", "translateY(0px)"] }, { delay: stagger(0.035), duration: 0.4, ease: "easeOut" });
  } catch (e) {
    els.forEach((el) => (el.style.opacity = 1));
  }
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
          <div class="card-sub">${fmtTime(s.start)} &ndash; ${fmtTime(s.end)} &middot; ${fmtDur(s)}</div>
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

function renderTrades() {
  const box = $("#trades");
  OPTION_INDEX = new Map();

  const mineShift = DATA && DATA.flat.find((s) => s.id === SELECTED);
  if (!mineShift) {
    box.innerHTML = `<div class="empty"><span class="fleuron">&#10086;</span>Choose one of your shifts to see who can take it.</div>`;
    return;
  }

  const opts = tradeOptions(DATA.flat, DATA.schedules, mineShift);
  if (!opts.length) {
    box.innerHTML = `<div class="empty"><span class="fleuron">&#10086;</span>No valid trades for that shift right now &mdash; try another.</div>`;
    return;
  }

  let html = "";
  for (const [ws, shifts] of groupByWeek(opts)) {
    html += `<div class="week-head">Week of ${fmtMonDay(new Date(Number(ws)))}</div>`;
    for (const s of shifts) {
      OPTION_INDEX.set(s.id, s);
      const edtra = personWorksEdTraInWeek(DATA.all, s.person, mineShift.start)
        ? `<span class="stamp stamp-amber">ED/Tra</span>` : "";
      html += `<div class="card enter" data-id="${esc(s.id)}">
        ${dateTile(s)}
        <div class="card-body">
          <div class="card-title"><span class="with">with ${esc(s.person)}</span> &middot; ${esc(s.title)}</div>
          <div class="card-sub">${fmtTime(s.start)} &ndash; ${fmtTime(s.end)} &middot; ${fmtDur(s)}</div>
          ${stampRow([weekendStamp(s), edtra].filter(Boolean))}
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

function openSheet(theirShift) {
  const mineShift = DATA.flat.find((s) => s.id === SELECTED);
  if (!mineShift) return;

  const [ok] = simulateSwapOk(DATA.schedules, mineShift, theirShift);
  if (!ok) {
    renderTrades();
    return;
  }

  const partner = theirShift.person;
  TRADE = { me: ME, partner, myShift: mineShift, theirShift };

  const cloneFor = (person, s) => ({ ...s, person, id: `${person}|${s.start.getTime()}|${s.end.getTime()}|${s.title}` });
  const sBforA = cloneFor(ME, theirShift);
  const sAforB = cloneFor(partner, mineShift);

  const mineNew = (DATA.schedules.get(ME) || []).filter((x) => x.id !== mineShift.id).concat([sBforA]).sort((a, b) => a.start - b.start);
  const theirsNew = (DATA.schedules.get(partner) || []).filter((x) => x.id !== theirShift.id).concat([sAforB]).sort((a, b) => a.start - b.start);

  const aPos = findPrevNext(mineNew, sBforA.id);
  const bPos = findPrevNext(theirsNew, sAforB.id);

  const sumWeek = (sched, anchor) => {
    const ws = weekStart(anchor), we = weekEnd(anchor);
    let t = 0;
    for (const s of sched) if (s.start >= ws && s.start < we) t += durationHours(s);
    return t;
  };

  $("#sheetTitle").innerHTML = `An exchange with <em>${esc(partner)}</em>`;
  $("#compare").innerHTML =
    folioHTML({
      name: ME, isMe: true, gives: mineShift, gets: sBforA, removed: mineShift, schedule: mineNew, pos: aPos,
      prevGap: aPos.prev ? gapHours(aPos.prev.end, sBforA.start) : null,
      nextGap: aPos.next ? gapHours(sBforA.end, aPos.next.start) : null,
      weekTotal: sumWeek(mineNew, sBforA.start),
    }) +
    folioHTML({
      name: partner, isMe: false, gives: theirShift, gets: sAforB, removed: theirShift, schedule: theirsNew, pos: bPos,
      prevGap: bPos.prev ? gapHours(bPos.prev.end, sAforB.start) : null,
      nextGap: bPos.next ? gapHours(sAforB.end, bPos.next.start) : null,
      weekTotal: sumWeek(theirsNew, sAforB.start),
    });

  setTone("professional");
  setCopied(false);

  const backdrop = $("#backdrop");
  backdrop.hidden = false;
  document.body.style.overflow = "hidden";
  refreshIcons();

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

function closeSheet() {
  $("#backdrop").hidden = true;
  document.body.style.overflow = "";
}

// ---------------- Message composer ----------------

function buildMessage(tone) {
  const { me, partner, myShift, theirShift } = TRADE;
  const give = `${myShift.title} — ${fmtDayFull(myShift.start)} ${fmtTime(myShift.start)} → ${fmtTime(myShift.end)}`;
  const get = `${theirShift.title} — ${fmtDayFull(theirShift.start)} ${fmtTime(theirShift.start)} → ${fmtTime(theirShift.end)}`;

  if (tone === "desperate") {
    return `Hey ${partner} 🙏
Any chance you'd swap with me?

I'd give you:
• ${give}

And I'd take:
• ${get}

You'd be saving my week — and it should be fully valid per the rules. Please say yes! 🤞
— ${me}`;
  }
  if (tone === "silly") {
    return `yo ${partner} 🎉

You down for a trade-sie-poo?

I give you:
• ${give}
you present to me your:
• ${get}

computers say it's legit (i'm p sure) ✅
lmk and I'll make it official 😎
— ${me}`;
  }
  return `Hi ${partner},
Would you be open to a shift trade? It would be greatly appreciated.

I'd trade you my:
• ${give}
And take your:
• ${get}

The swap passes our scheduling rules. If that works for you, I'll send a quick confirm. Thanks!
— ${me}`;
}

function setTone(tone) {
  TONE = tone;
  document.querySelectorAll(".tones button").forEach((b) => {
    b.setAttribute("aria-pressed", b.dataset.tone === tone ? "true" : "false");
  });
  if (TRADE) $("#msg").value = buildMessage(tone);
}

function setCopied(on) {
  $("#copyBtn").classList.toggle("copied", on);
  $("#copyLabel").textContent = on ? "Copied" : "Copy note";
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
    const shift = OPTION_INDEX.get(btn.dataset.id);
    if (shift) openSheet(shift);
  });

  $("#closeSheet").addEventListener("click", closeSheet);
  $("#backdrop").addEventListener("click", (e) => {
    if (e.target === $("#backdrop")) closeSheet();
  });
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape" && !$("#backdrop").hidden) closeSheet();
  });

  document.querySelectorAll(".tones button").forEach((b) => {
    b.addEventListener("click", () => setTone(b.dataset.tone));
  });
  $("#copyBtn").addEventListener("click", copyNote);

  refreshIcons();
  load();
}

init();
