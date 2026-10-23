'use strict';

/**
 * TIKAN — moteur de football arcade 1 contre 1, autoritatif côté serveur.
 *
 * Module PUR : aucune dépendance au réseau, aux timers ni à Date.now(). Le
 * serveur (server.js) fournit les entrées des deux joueurs et un pas de temps
 * fixe ; ce module rend l'état et les évènements (but, carton, ballon libre…).
 * Les clients n'envoient jamais une position : seulement ce que leurs doigts
 * font (direction du joystick, tir, dégagement, sprint). Un client modifié ne
 * peut donc ni se téléporter, ni aller plus vite, ni marquer sans toucher la
 * balle.
 *
 * Le terrain est logique (360 × 640) et identique pour tous ; chaque client le
 * met à l'échelle de son écran. La place 1 attaque vers le HAUT (but y = FY),
 * la place 2 vers le BAS. Le joueur 2 voit le terrain retourné de 180° côté
 * client : le moteur, lui, ne connaît qu'un seul repère.
 *
 * Règles reprises de la version solo : premier à 5 buts, joystick + tir +
 * dégagement + sprint limité, balle bloquée dans un coin 5 s = ballon libre
 * pour l'adversaire, coincer l'adversaire dans un coin = carton jaune, deuxième
 * jaune = carton rouge (but offert à l'adversaire).
 * Ajouts propres au jeu en ligne : durée maximale (but en or puis match nul)
 * pour qu'une partie à enjeu ne puisse jamais rester suspendue.
 */

const FIELD = Object.freeze({
  W: 360, H: 640,
  FX: 20, FY: 24, FW: 320, FH: 592,
  GW: 86, GH: 37,
  PR: 14, BR: 9
});

const RULES = Object.freeze({
  MAX_GOALS: 5,
  PSPD: 192,
  SPRINT_MULT: 1.45,
  SPRINT_DRAIN: 28,
  SPRINT_REGEN: 14,
  FRIC: 0.964,
  DEG: 430,
  KSHOT: 580,
  ABSORB: 0.22,
  DRAG: 0.28,
  CORNER_TIMEOUT: 5,
  CORNER_SIZE: 60,
  FORCE_DIST: 55,
  DEAD: 0.11,
  KICK_REACH: 22,
  // Durées des phases, en millisecondes.
  OPENING_MS: 3000,
  GOAL_MS: 1500,
  KICKOFF_MS: 1200,
  CARD_MS: 2200,
  FREEBALL_MS: 5000,
  // Une partie à enjeu ne reste jamais suspendue.
  MAX_MATCH_MS: 10 * 60 * 1000,
  GOLDEN_MS: 3 * 60 * 1000
});

const STEP = 1 / 60;
const TAU = Math.PI * 2;

const clamp = (v, lo, hi) => Math.max(lo, Math.min(hi, v));
const dist = (a, b) => Math.hypot(a.x - b.x, a.y - b.y);
const other = slot => (slot === 1 ? 2 : 1);
/** Sens d'attaque en y : la place 1 monte (-1), la place 2 descend (+1). */
const attackDir = slot => (slot === 1 ? -1 : 1);

function makePlayer(slot) {
  const cx = FIELD.FX + FIELD.FW / 2;
  return {
    x: cx,
    y: FIELD.FY + FIELD.FH * (slot === 1 ? 0.70 : 0.30),
    vx: 0, vy: 0, kcd: 0,
    dir: slot === 1 ? -Math.PI / 2 : Math.PI / 2
  };
}

function createState(rng = Math.random) {
  const state = {
    phase: 'kickoff', phaseT: RULES.OPENING_MS, after: null,
    sc: [0, 0], cards: [0, 0], corner: [0, 0],
    sprint: [100, 100], locked: [false, false],
    p: [makePlayer(1), makePlayer(2)],
    b: { x: FIELD.FX + FIELD.FW / 2, y: FIELD.FY + FIELD.FH / 2, vx: 0, vy: 0, spin: 0, rot: 0 },
    fb: null,
    elapsed: 0, golden: false,
    over: null,
    tick: 0,
    stats: { shots: [0, 0], onTarget: [0, 0], poss: [0, 0] }
  };
  state.b.vx = (rng() - 0.5) * 30;
  state.b.vy = (rng() - 0.5) * 30;
  return state;
}

function resetPositions(s, rng) {
  s.p = [makePlayer(1), makePlayer(2)];
  s.b = { x: FIELD.FX + FIELD.FW / 2, y: FIELD.FY + FIELD.FH / 2, vx: (rng() - 0.5) * 30, vy: (rng() - 0.5) * 30, spin: 0, rot: 0 };
  s.corner = [0, 0];
  s.fb = null;
}

/** Entrée d'un joueur, bornée : jamais plus que « joystick à fond ». */
function sanitizeInput(raw) {
  const r = raw && typeof raw === 'object' ? raw : {};
  let dx = Number(r.dx), dy = Number(r.dy);
  if (!Number.isFinite(dx)) dx = 0;
  if (!Number.isFinite(dy)) dy = 0;
  const mg = Math.hypot(dx, dy);
  if (mg > 1) { dx /= mg; dy /= mg; }
  return { dx, dy, mg: Math.min(1, mg), kick: r.kick === true, deg: r.deg === true, spr: r.spr === true };
}

const NO_INPUT = Object.freeze({ dx: 0, dy: 0, mg: 0, kick: false, deg: false, spr: false });

// ── Tirs ───────────────────────────────────────────────────

function doShot(s, slot, rng, events) {
  const i = slot - 1, P = s.p[i], B = s.b;
  const gcx = FIELD.FX + FIELD.FW / 2;
  const lat = (P.x - gcx) * 0.20;
  const ax = clamp(gcx - lat, gcx - FIELD.GW * 0.40, gcx + FIELD.GW * 0.40);
  const ay = slot === 1 ? FIELD.FY - 2 : FIELD.FY + FIELD.FH + 2;
  const fx = ax - P.x, fy = ay - P.y;
  const pwr = RULES.KSHOT * (0.90 + rng() * 0.10);
  const ang = Math.atan2(fy, fx) + (rng() - 0.5) * 0.06;
  B.vx = Math.cos(ang) * pwr;
  B.vy = Math.sin(ang) * pwr;
  B.spin = Math.sign(P.vx || 0) * Math.min(1.8, Math.abs(P.vx) * 0.010);
  P.kcd = 0.22;
  s.stats.shots[i]++;
  if (Math.abs(ax - gcx) < FIELD.GW / 2) s.stats.onTarget[i]++;
  events.push({ t: 'kick', slot, kind: 'shot', x: P.x, y: P.y, power: pwr });
  if (s.fb) endFreeball(s);
}

function doClear(s, slot, rng, events) {
  const P = s.p[slot - 1], B = s.b;
  // La place 1 dégage vers le haut, la place 2 vers le bas.
  const centre = slot === 1 ? -Math.PI / 2 : Math.PI / 2;
  const ang = centre + (rng() - 0.5) * (Math.PI * 0.78);
  B.vx = Math.cos(ang) * RULES.DEG;
  B.vy = Math.sin(ang) * RULES.DEG;
  B.spin = (rng() - 0.5) * 4;
  P.kcd = 0.34;
  events.push({ t: 'kick', slot, kind: 'clear', x: P.x, y: P.y, power: RULES.DEG });
  if (s.fb) endFreeball(s);
}

// ── Collisions ─────────────────────────────────────────────

function clampEntity(e) {
  const m = FIELD.PR + 4;
  e.x = clamp(e.x, FIELD.FX + m, FIELD.FX + FIELD.FW - m);
  e.y = clamp(e.y, FIELD.FY + m, FIELD.FY + FIELD.FH - m);
}

function separate(a, b) {
  const dx = b.x - a.x, dy = b.y - a.y, d = Math.hypot(dx, dy), mn = FIELD.PR * 2;
  if (d < mn && d > 0.01) {
    const p = (mn - d) / 2 + 0.5;
    a.x -= dx / d * p; a.y -= dy / d * p;
    b.x += dx / d * p; b.y += dy / d * p;
    clampEntity(a); clampEntity(b);
  }
}

function ballSoft(B, e) {
  const dx = B.x - e.x, dy = B.y - e.y, d = Math.hypot(dx, dy), mn = FIELD.PR + FIELD.BR;
  if (d < mn && d > 0.01) {
    const nx = dx / d, ny = dy / d;
    B.x = e.x + nx * mn; B.y = e.y + ny * mn;
    const rn = (B.vx - e.vx) * nx + (B.vy - e.vy) * ny;
    if (rn < 0) { B.vx -= rn * nx * RULES.ABSORB; B.vy -= rn * ny * RULES.ABSORB; }
    B.vx = B.vx * (1 - RULES.DRAG) + e.vx * RULES.DRAG;
    B.vy = B.vy * (1 - RULES.DRAG) + e.vy * RULES.DRAG;
  }
}

// ── Phases ─────────────────────────────────────────────────

function endFreeball(s) {
  s.fb = null;
}

function startFreeball(s, forSlot, rng) {
  const cx = FIELD.FX + FIELD.FW / 2;
  const bx = cx + (rng() - 0.5) * FIELD.FW * 0.18;
  const by = FIELD.FY + FIELD.FH * (forSlot === 1 ? 0.72 : 0.28);
  s.corner = [0, 0];
  s.b = { x: bx, y: by, vx: 0, vy: 0, spin: 0, rot: 0 };
  const me = s.p[forSlot - 1], op = s.p[other(forSlot) - 1];
  // Le bénéficiaire se place DERRIÈRE le ballon, face au but adverse.
  me.x = bx; me.y = by - attackDir(forSlot) * (FIELD.PR + FIELD.BR + 6);
  me.vx = 0; me.vy = 0; me.kcd = 0; me.dir = attackDir(forSlot) * Math.PI / 2;
  op.x = cx + (rng() - 0.5) * FIELD.FW * 0.30;
  op.y = FIELD.FY + FIELD.FH * (forSlot === 1 ? 0.15 : 0.85);
  op.vx = 0; op.vy = 0; op.kcd = 0;
  s.fb = { for: forSlot, t: 0 };
  s.phase = 'playing'; s.phaseT = 0; s.after = null;
}

function finish(s, winnerSlot, reason, events) {
  if (s.over) return;
  s.over = { winnerSlot, reason };
  s.phase = 'over'; s.phaseT = 0; s.fb = null;
  events.push({ t: 'over', winnerSlot, reason, sc: [...s.sc] });
}

function scoreGoal(s, scorer, rng, events, viaRed) {
  s.sc[scorer - 1]++;
  s.fb = null; s.corner = [0, 0];
  events.push({ t: 'goal', slot: scorer, sc: [...s.sc], red: viaRed === true });
  if (s.sc[scorer - 1] >= RULES.MAX_GOALS) return finish(s, scorer, 'normal', events);
  // But en or : le premier but met fin au match.
  if (s.golden) return finish(s, scorer, 'normal', events);
  if (viaRed) { startFreeball(s, scorer, rng); return; }
  s.phase = 'goal'; s.phaseT = RULES.GOAL_MS; s.after = { type: 'kickoff' };
}

function giveCard(s, offender, rng, events) {
  const i = offender - 1, victim = other(offender);
  s.cards[i]++;
  s.corner = [0, 0];
  if (s.cards[i] >= 2) {
    events.push({ t: 'card', slot: offender, level: 2, cards: [...s.cards] });
    s.phase = 'card'; s.phaseT = RULES.CARD_MS; s.after = { type: 'red', scorer: victim };
  } else {
    events.push({ t: 'card', slot: offender, level: 1, cards: [...s.cards] });
    s.phase = 'card'; s.phaseT = RULES.CARD_MS; s.after = { type: 'freeball', for: victim };
  }
}

function advancePhase(s, dtMs, rng, events) {
  s.phaseT -= dtMs;
  if (s.phaseT > 0) return;
  const after = s.after;
  s.phaseT = 0; s.after = null;
  if (s.phase === 'kickoff') { s.phase = 'playing'; return; }
  if (s.phase === 'goal') {
    resetPositions(s, rng);
    s.phase = 'kickoff'; s.phaseT = RULES.KICKOFF_MS;
    return;
  }
  if (s.phase === 'card') {
    if (after?.type === 'red') return scoreGoal(s, after.scorer, rng, events, true);
    if (after?.type === 'freeball') return startFreeball(s, after.for, rng);
    s.phase = 'playing';
  }
}

// ── Pas de simulation ──────────────────────────────────────

/**
 * Avance le jeu de `dt` secondes (pas fixe conseillé : STEP).
 * @param {object} s       état (modifié sur place)
 * @param {object[]} inputs entrées [place 1, place 2] — voir sanitizeInput
 * @param {number} dt
 * @param {() => number} rng
 * @returns {object[]} évènements survenus pendant ce pas
 */
function step(s, inputs, dt = STEP, rng = Math.random) {
  const events = [];
  if (s.over) return events;
  s.tick++;
  const f = dt * 60; // facteur de cadence : les frictions sont réglées pour 60 pas/s

  if (s.phase === 'kickoff' || s.phase === 'goal' || s.phase === 'card') {
    advancePhase(s, dt * 1000, rng, events);
    return events;
  }

  // ── Durée maximale ──
  s.elapsed += dt * 1000;
  if (!s.golden && s.elapsed >= RULES.MAX_MATCH_MS) {
    if (s.sc[0] !== s.sc[1]) {
      finish(s, s.sc[0] > s.sc[1] ? 1 : 2, 'normal', events);
      return events;
    }
    s.golden = true;
    events.push({ t: 'golden' });
  }
  if (s.golden && s.elapsed >= RULES.MAX_MATCH_MS + RULES.GOLDEN_MS) {
    finish(s, 0, 'draw', events);
    return events;
  }

  // Le ballon libre expire de lui-même : personne ne reste figé.
  if (s.fb) {
    s.fb.t += dt * 1000;
    if (s.fb.t >= RULES.FREEBALL_MS) endFreeball(s);
  }

  const ins = [inputs?.[0] || NO_INPUT, inputs?.[1] || NO_INPUT];

  for (let i = 0; i < 2; i++) {
    const slot = i + 1, P = s.p[i], inp = ins[i];
    // Pendant un ballon libre, l'adversaire du bénéficiaire est figé.
    const frozen = !!s.fb && s.fb.for !== slot;
    P.kcd = Math.max(0, P.kcd - dt);
    if (frozen) { P.vx = 0; P.vy = 0; continue; }

    // Sprint limité : se vide en courant, se recharge au repos, verrou à 0.
    const canSprint = inp.spr && !s.locked[i] && s.sprint[i] > 0 && inp.mg > RULES.DEAD;
    if (canSprint) {
      s.sprint[i] = Math.max(0, s.sprint[i] - dt * RULES.SPRINT_DRAIN);
      if (s.sprint[i] === 0) s.locked[i] = true;
    } else {
      s.sprint[i] = Math.min(100, s.sprint[i] + dt * RULES.SPRINT_REGEN);
      if (s.locked[i] && s.sprint[i] >= 100) s.locked[i] = false;
    }
    const mult = canSprint ? RULES.SPRINT_MULT : 1;

    if (inp.mg > RULES.DEAD) {
      P.vx = inp.dx * RULES.PSPD * mult;
      P.vy = inp.dy * RULES.PSPD * mult;
      P.dir = Math.atan2(inp.dy, inp.dx);
    } else {
      const k = Math.pow(0.56, f);
      P.vx *= k; P.vy *= k;
    }
    P.x += P.vx * dt; P.y += P.vy * dt;

    const rep = 18;
    if (P.x < FIELD.FX + rep) P.vx += 120 * dt;
    if (P.x > FIELD.FX + FIELD.FW - rep) P.vx -= 120 * dt;
    if (P.y < FIELD.FY + rep) P.vy += 120 * dt;
    if (P.y > FIELD.FY + FIELD.FH - rep) P.vy -= 120 * dt;
    clampEntity(P);
  }

  const B = s.b;
  const [P1, P2] = s.p;

  // Possession (statistique de fin de match).
  const d1 = dist(P1, B), d2 = dist(P2, B);
  if (d1 < FIELD.PR + FIELD.BR + 13) s.stats.poss[0]++;
  else if (d2 < FIELD.PR + FIELD.BR + 13) s.stats.poss[1]++;

  // ── Coins : garder la balle ou coincer l'autre trop longtemps se paie ──
  if (!s.fb) {
    const near = FIELD.PR + FIELD.BR + 28;
    const has = [d1 < near && d1 <= d2, d2 < near && d2 < d1];
    const inCorner = s.p.map(e =>
      (e.x < FIELD.FX + RULES.CORNER_SIZE || e.x > FIELD.FX + FIELD.FW - RULES.CORNER_SIZE) &&
      (e.y < FIELD.FY + RULES.CORNER_SIZE || e.y > FIELD.FY + FIELD.FH - RULES.CORNER_SIZE));
    const close = dist(P1, P2) < RULES.FORCE_DIST;
    for (let i = 0; i < 2; i++) {
      const blocked = inCorner[i] && close;
      if (inCorner[i] && (has[i] || blocked)) s.corner[i] += dt;
      else s.corner[i] = Math.max(0, s.corner[i] - dt * 2);
    }
    for (let i = 0; i < 2; i++) {
      if (s.corner[i] < RULES.CORNER_TIMEOUT) continue;
      const slot = i + 1, blocked = inCorner[i] && close;
      s.corner[i] = 0;
      // Coincé par l'adversaire : c'est lui qui est sanctionné ; sinon la
      // balle gardée trop longtemps dans le coin passe à l'adversaire.
      if (blocked) giveCard(s, other(slot), rng, events);
      else { events.push({ t: 'freeball', for: other(slot) }); startFreeball(s, other(slot), rng); }
      return events;
    }
  }

  // ── Tirs et dégagements ──
  for (let i = 0; i < 2; i++) {
    const slot = i + 1, P = s.p[i], inp = ins[i];
    const frozen = !!s.fb && s.fb.for !== slot;
    if (frozen || P.kcd > 0) continue;
    if (dist(P, B) >= FIELD.PR + FIELD.BR + RULES.KICK_REACH) continue;
    if (inp.kick) doShot(s, slot, rng, events);
    else if (inp.deg) doClear(s, slot, rng, events);
  }

  separate(P1, P2);

  // ── Ballon ──
  B.spin *= Math.pow(0.972, f);
  const sp = Math.hypot(B.vx, B.vy);
  if (sp > 8 && Math.abs(B.spin) > 0.04) {
    B.vx += (-B.vy / (sp || 1)) * B.spin * sp * 0.012 * f;
    B.vy += (B.vx / (sp || 1)) * B.spin * sp * 0.012 * f;
  }
  B.rot += sp * dt * 0.08;
  const fr = Math.pow(RULES.FRIC, f);
  B.vx *= fr; B.vy *= fr;
  B.x += B.vx * dt; B.y += B.vy * dt;

  const gcx = FIELD.FX + FIELD.FW / 2;
  const gL = gcx - FIELD.GW / 2, gR = gcx + FIELD.GW / 2;
  const { FX, FY, FW, FH, GH, BR } = FIELD;
  const backTop = FY - GH, backBot = FY + FH + GH;

  // Murs latéraux et fond des cages.
  if (B.x - BR < FX) { B.x = FX + BR; B.vx = Math.abs(B.vx) * 0.65; B.spin *= -0.4; }
  if (B.x + BR > FX + FW) { B.x = FX + FW - BR; B.vx = -Math.abs(B.vx) * 0.65; B.spin *= -0.4; }
  if (B.y - BR < backTop) { B.y = backTop + BR; B.vy = Math.abs(B.vy) * 0.55; }
  if (B.y + BR > backBot) { B.y = backBot - BR; B.vy = -Math.abs(B.vy) * 0.55; }

  // Cage du haut : but de la place 1.
  if (B.y >= FY - GH && B.y <= FY && B.x - BR < gL && B.x + BR > gL - 2) { B.x = gL + BR; B.vx = Math.abs(B.vx) * 0.60; }
  if (B.y >= FY - GH && B.y <= FY && B.x + BR > gR && B.x - BR < gR + 2) { B.x = gR - BR; B.vx = -Math.abs(B.vx) * 0.60; }
  if (B.y - BR < FY) {
    if (B.x >= gL && B.x <= gR) {
      if (B.y + BR < FY) { scoreGoal(s, 1, rng, events, false); return events; }
      if (B.x - BR < gL) { B.x = gL + BR; B.vx = Math.abs(B.vx) * 0.60; }
      if (B.x + BR > gR) { B.x = gR - BR; B.vx = -Math.abs(B.vx) * 0.60; }
    } else {
      B.y = FY + BR; B.vy = Math.abs(B.vy) * 0.68;
      if (B.x + BR > gL && B.x < gL) { B.x = gL - BR; B.vx = -Math.abs(B.vx) * 0.60; }
      if (B.x - BR < gR && B.x > gR) { B.x = gR + BR; B.vx = Math.abs(B.vx) * 0.60; }
    }
  }

  // Cage du bas : but de la place 2.
  if (B.y >= FY + FH && B.y <= FY + FH + GH && B.x - BR < gL && B.x + BR > gL - 2) { B.x = gL + BR; B.vx = Math.abs(B.vx) * 0.60; }
  if (B.y >= FY + FH && B.y <= FY + FH + GH && B.x + BR > gR && B.x - BR < gR + 2) { B.x = gR - BR; B.vx = -Math.abs(B.vx) * 0.60; }
  if (B.y + BR > FY + FH) {
    if (B.x >= gL && B.x <= gR) {
      if (B.y - BR > FY + FH) { scoreGoal(s, 2, rng, events, false); return events; }
      if (B.x - BR < gL) { B.x = gL + BR; B.vx = Math.abs(B.vx) * 0.60; }
      if (B.x + BR > gR) { B.x = gR - BR; B.vx = -Math.abs(B.vx) * 0.60; }
    } else {
      B.y = FY + FH - BR; B.vy = -Math.abs(B.vy) * 0.68;
      if (B.x + BR > gL && B.x < gL) { B.x = gL - BR; B.vx = -Math.abs(B.vx) * 0.60; }
      if (B.x - BR < gR && B.x > gR) { B.x = gR + BR; B.vx = Math.abs(B.vx) * 0.60; }
    }
  }

  ballSoft(B, P1);
  ballSoft(B, P2);
  return events;
}

// ── Réseau ─────────────────────────────────────────────────

const r1 = v => Math.round(v * 10) / 10;

/** Instantané compact envoyé aux clients (valeurs arrondies). */
function snapshot(s) {
  return {
    k: s.tick,
    ph: s.phase,
    pt: Math.max(0, Math.round(s.phaseT)),
    sc: [...s.sc],
    cd: [...s.cards],
    cn: [r1(s.corner[0]), r1(s.corner[1])],
    sp: [Math.round(s.sprint[0]), Math.round(s.sprint[1])],
    lk: [s.locked[0] ? 1 : 0, s.locked[1] ? 1 : 0],
    p: s.p.map(e => [r1(e.x), r1(e.y), r1(e.vx), r1(e.vy), Math.round(e.dir * 100) / 100]),
    b: [r1(s.b.x), r1(s.b.y), r1(s.b.vx), r1(s.b.vy), Math.round(s.b.rot * 100) / 100],
    fb: s.fb ? s.fb.for : 0,
    el: Math.round(s.elapsed),
    go: s.golden ? 1 : 0
  };
}

module.exports = { FIELD, RULES, STEP, createState, step, snapshot, sanitizeInput, NO_INPUT, attackDir, other };
