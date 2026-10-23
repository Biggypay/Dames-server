'use strict';
/*
 * TIKAN — le moteur autoritatif (lib/tikan-engine.js), sans réseau.
 * Un générateur pseudo-aléatoire fixe rend chaque scénario reproductible.
 */
const assert = require('assert');
const E = require('../lib/tikan-engine.js');
const { FIELD, RULES, STEP } = E;

function rng(seed = 7) {
  let a = seed;
  return () => { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; };
}
const idle = () => [E.NO_INPUT, E.NO_INPUT];
const inp = (o) => E.sanitizeInput(o);

/** Fait tourner `seconds` ; renvoie tous les évènements. */
function run(s, seconds, inputs = idle, r = rng()) {
  const events = [];
  for (let i = 0; i < Math.round(seconds / STEP); i++) events.push(...E.step(s, inputs(s, i), STEP, r));
  return events;
}

/** Une partie prête : compte à rebours passé, balle immobile au centre. */
function ready() {
  const s = E.createState(rng());
  run(s, RULES.OPENING_MS / 1000 + 0.1);
  assert.strictEqual(s.phase, 'playing');
  s.b.vx = 0; s.b.vy = 0;
  return s;
}

let passed = 0;
const test = (name, fn) => { fn(); passed++; console.log('  ✓', name); };

test('compte à rebours : rien ne bouge avant le coup d’envoi', () => {
  const s = E.createState(rng());
  const x0 = s.p[0].x, y0 = s.p[0].y;
  run(s, 1, () => [inp({ dx: 1, dy: 0 }), E.NO_INPUT]);
  assert.strictEqual(s.phase, 'kickoff');
  assert.strictEqual(s.p[0].x, x0); assert.strictEqual(s.p[0].y, y0);
});

test('entrées bornées : un client ne peut pas dépasser le joystick à fond', () => {
  const i = inp({ dx: 50, dy: 50, kick: 'oui', spr: 1 });
  assert.ok(Math.hypot(i.dx, i.dy) <= 1.0000001);
  assert.strictEqual(i.kick, false); assert.strictEqual(i.spr, false);
  assert.deepStrictEqual(inp({ dx: NaN, dy: 'x' }).mg, 0);
  assert.deepStrictEqual(inp(null).kick, false);
});

test('vitesse : 192 px/s, 1,45 × en sprint, jamais plus', () => {
  let s = ready(); s.b.x = 9999; // ballon hors de portée : on mesure le joueur seul
  const x0 = s.p[0].x;
  run(s, 0.5, () => [inp({ dx: 0, dy: 1 }), E.NO_INPUT]);
  assert.ok(Math.abs(s.p[0].y - (FIELD.FY + FIELD.FH * 0.70 + RULES.PSPD * 0.5)) < 2 || s.p[0].y <= FIELD.FY + FIELD.FH - FIELD.PR - 4);
  assert.strictEqual(s.p[0].x, x0);
  s = ready(); s.p[0].x = FIELD.FX + 40; s.p[0].y = FIELD.FY + 300; s.b.x = 9999;
  const xa = s.p[0].x;
  run(s, 0.5, () => [inp({ dx: 1, dy: 0, spr: true }), E.NO_INPUT]);
  assert.ok(Math.abs((s.p[0].x - xa) - RULES.PSPD * RULES.SPRINT_MULT * 0.5) < 3);
});

test('sprint : se vide, se verrouille à 0, ne revient qu’une fois rechargé à 100', () => {
  const s = ready(); s.p[0].x = FIELD.FX + 20; s.p[0].y = FIELD.FY + 300; s.b.x = 9999;
  const sprintInput = () => [inp({ dx: 1, dy: 0, spr: true }), E.NO_INPUT];
  run(s, 2, sprintInput);
  assert.ok(s.sprint[0] < 100 && s.sprint[0] > 0, 'la jauge se vide');
  assert.strictEqual(s.locked[0], false);
  run(s, 2, sprintInput); // 100 / 28 ≈ 3,6 s : la jauge est vide
  assert.strictEqual(s.locked[0], true, 'verrou une fois la jauge à 0');
  const lockedAt = s.sprint[0];
  assert.ok(lockedAt < 10);
  // Maintenu verrouillé : plus de sprint même en le demandant, la jauge se recharge.
  const xa = s.p[0].x;
  run(s, 0.3, () => [inp({ dx: -1, dy: 0, spr: true }), E.NO_INPUT]);
  assert.ok(Math.abs((xa - s.p[0].x) - RULES.PSPD * 0.3) < 4, 'vitesse normale pendant le verrou');
  run(s, 3, () => idle());
  assert.strictEqual(s.locked[0], true, 'encore verrouillé tant que la jauge n’est pas pleine');
  run(s, 8, () => idle());
  assert.strictEqual(s.locked[0], false);
  assert.strictEqual(s.sprint[0], 100);
});

test('tir de la place 1 vers le HAUT : but pour la place 1', () => {
  const s = ready();
  s.p[1].x = FIELD.FX + 30; s.p[1].y = FIELD.FY + 80; // l'autre joueur n'est pas sur la trajectoire
  s.p[0].x = FIELD.FX + FIELD.FW / 2; s.p[0].y = FIELD.FY + 160;
  s.b.x = s.p[0].x; s.b.y = s.p[0].y - 26; s.b.vx = 0; s.b.vy = 0;
  const ev = run(s, 2, () => [inp({ kick: true }), E.NO_INPUT]);
  assert.ok(ev.some(e => e.t === 'kick' && e.slot === 1 && e.kind === 'shot'));
  const goal = ev.find(e => e.t === 'goal');
  assert.ok(goal, 'un but doit être marqué');
  assert.strictEqual(goal.slot, 1);
  assert.deepStrictEqual(s.sc, [1, 0]);
  assert.strictEqual(s.stats.shots[0], 1);
});

test('tir de la place 2 vers le BAS : but pour la place 2 (symétrie)', () => {
  const s = ready();
  s.p[0].x = FIELD.FX + 30; s.p[0].y = FIELD.FY + FIELD.FH - 80;
  s.p[1].x = FIELD.FX + FIELD.FW / 2; s.p[1].y = FIELD.FY + FIELD.FH - 160;
  s.b.x = s.p[1].x; s.b.y = s.p[1].y + 26; s.b.vx = 0; s.b.vy = 0;
  const ev = run(s, 2, () => [E.NO_INPUT, inp({ kick: true })]);
  const goal = ev.find(e => e.t === 'goal');
  assert.ok(goal && goal.slot === 2);
  assert.deepStrictEqual(s.sc, [0, 1]);
});

test('on ne tire pas à distance : le ballon doit être à portée', () => {
  const s = ready();
  s.p[0].x = FIELD.FX + 60; s.p[0].y = FIELD.FY + 300; s.b.x = FIELD.FX + FIELD.FW - 60; s.b.y = FIELD.FY + 100;
  const ev = run(s, 1, () => [inp({ kick: true, deg: true }), E.NO_INPUT]);
  assert.ok(!ev.some(e => e.t === 'kick'));
});

test('après un but : pause, remise au centre, puis la partie reprend', () => {
  const s = ready();
  s.p[1].x = FIELD.FX + 30; s.p[1].y = FIELD.FY + 80;
  s.p[0].x = FIELD.FX + FIELD.FW / 2; s.p[0].y = FIELD.FY + 160; s.b.x = s.p[0].x; s.b.y = s.p[0].y - 26;
  run(s, 2, () => [inp({ kick: true }), E.NO_INPUT]);
  run(s, 2, () => idle());
  // Pendant la pause du but ou juste après : on finit toujours par rejouer.
  run(s, (RULES.GOAL_MS + RULES.KICKOFF_MS) / 1000 + 0.5, () => idle());
  assert.strictEqual(s.phase, 'playing');
  assert.ok(Math.abs(s.b.y - (FIELD.FY + FIELD.FH / 2)) < 40, 'ballon revenu près du centre');
  assert.deepStrictEqual(s.sc, [1, 0]);
});

test('premier à 5 buts : fin de partie, une seule fois', () => {
  const s = ready();
  s.sc = [4, 3];
  s.p[1].x = FIELD.FX + 30; s.p[1].y = FIELD.FY + 80;
  s.p[0].x = FIELD.FX + FIELD.FW / 2; s.p[0].y = FIELD.FY + 160; s.b.x = s.p[0].x; s.b.y = s.p[0].y - 26;
  const ev = run(s, 2, () => [inp({ kick: true }), E.NO_INPUT]);
  assert.strictEqual(ev.filter(e => e.t === 'over').length, 1);
  assert.deepStrictEqual(s.over, { winnerSlot: 1, reason: 'normal' });
  assert.strictEqual(s.phase, 'over');
  assert.deepStrictEqual(run(s, 1), [], 'plus aucun évènement après la fin');
});

test('dégagement : la place 2 dégage vers le bas', () => {
  const s = ready();
  s.p[1].x = FIELD.FX + 100; s.p[1].y = FIELD.FY + 150; s.b.x = s.p[1].x; s.b.y = s.p[1].y + 20;
  run(s, 0.1, () => [E.NO_INPUT, inp({ deg: true })]);
  assert.ok(s.b.vy > 0, 'la balle part vers le camp de la place 1');
});

test('coin : garder la balle 5 s dans le coin donne un ballon libre à l’adversaire', () => {
  const s = ready();
  s.p[0].x = FIELD.FX + 25; s.p[0].y = FIELD.FY + 25;
  s.b.x = s.p[0].x + 14; s.b.y = s.p[0].y + 14; s.b.vx = 0; s.b.vy = 0;
  s.p[1].x = FIELD.FX + FIELD.FW - 40; s.p[1].y = FIELD.FY + FIELD.FH - 40;
  const ev = run(s, RULES.CORNER_TIMEOUT + 0.5, () => idle());
  assert.ok(ev.some(e => e.t === 'freeball' && e.for === 2), 'ballon libre pour la place 2');
  assert.deepStrictEqual(s.fb && s.fb.for, 2);
});

test('coin : l’adversaire qui coince est sanctionné — jaune puis rouge = but offert', () => {
  const s = ready();
  const cornerSetup = () => {
    s.p[0].x = FIELD.FX + 25; s.p[0].y = FIELD.FY + 25;
    s.p[1].x = FIELD.FX + 25 + 30; s.p[1].y = FIELD.FY + 25;
    s.b.x = s.p[0].x; s.b.y = s.p[0].y; s.b.vx = 0; s.b.vy = 0;
  };
  cornerSetup();
  let ev = run(s, RULES.CORNER_TIMEOUT + 0.3, () => { s.p[0].x = FIELD.FX + 25; s.p[0].y = FIELD.FY + 25; s.p[1].x = FIELD.FX + 55; s.p[1].y = FIELD.FY + 25; return idle(); });
  const yellow = ev.find(e => e.t === 'card');
  assert.ok(yellow && yellow.slot === 2 && yellow.level === 1, 'jaune pour celui qui coince');
  assert.strictEqual(s.phase, 'card');
  run(s, RULES.CARD_MS / 1000 + 0.2, () => idle());
  assert.strictEqual(s.fb && s.fb.for, 1, 'ballon libre pour la victime');
  // Deuxième faute : rouge, but pour la place 1.
  s.fb = null; s.phase = 'playing'; cornerSetup();
  ev = run(s, RULES.CORNER_TIMEOUT + 0.3, () => { s.p[0].x = FIELD.FX + 25; s.p[0].y = FIELD.FY + 25; s.p[1].x = FIELD.FX + 55; s.p[1].y = FIELD.FY + 25; return idle(); });
  assert.ok(ev.some(e => e.t === 'card' && e.slot === 2 && e.level === 2));
  const after = run(s, RULES.CARD_MS / 1000 + 0.2, () => idle());
  assert.ok(after.some(e => e.t === 'goal' && e.slot === 1 && e.red === true), 'but offert sur carton rouge');
  assert.deepStrictEqual(s.sc, [1, 0]);
});

test('ballon libre : l’adversaire est figé, puis libéré au tir ou après 5 s', () => {
  const s = ready();
  s.fb = null;
  // Provoque un ballon libre pour la place 1.
  s.p[1].x = FIELD.FX + 25; s.p[1].y = FIELD.FY + 25;
  s.b.x = s.p[1].x; s.b.y = s.p[1].y; s.b.vx = 0; s.b.vy = 0;
  s.p[0].x = FIELD.FX + FIELD.FW - 40; s.p[0].y = FIELD.FY + FIELD.FH - 40;
  run(s, RULES.CORNER_TIMEOUT + 0.3, () => idle());
  assert.strictEqual(s.fb && s.fb.for, 1);
  const frozen = { x: s.p[1].x, y: s.p[1].y };
  run(s, 1, () => [E.NO_INPUT, inp({ dx: 1, dy: 1, kick: true })]);
  assert.deepStrictEqual({ x: s.p[1].x, y: s.p[1].y }, frozen, 'figé pendant le ballon libre');
  const ev = run(s, 0.3, () => [inp({ kick: true }), E.NO_INPUT]);
  assert.ok(ev.some(e => e.t === 'kick' && e.slot === 1));
  assert.strictEqual(s.fb, null, 'le tir libère l’adversaire');

  // Sans tir : libéré de lui-même.
  const t = ready();
  t.p[1].x = FIELD.FX + 25; t.p[1].y = FIELD.FY + 25; t.b.x = t.p[1].x; t.b.y = t.p[1].y;
  t.p[0].x = FIELD.FX + FIELD.FW - 40; t.p[0].y = FIELD.FY + FIELD.FH - 40;
  run(t, RULES.CORNER_TIMEOUT + 0.3, () => idle());
  assert.ok(t.fb);
  run(t, RULES.FREEBALL_MS / 1000 + 0.3, () => idle());
  assert.strictEqual(t.fb, null);
});

test('durée maximale : le mieux placé gagne ; à égalité but en or, puis nul', () => {
  let s = ready(); s.sc = [2, 1]; s.elapsed = RULES.MAX_MATCH_MS - 10;
  run(s, 0.2, () => idle());
  assert.deepStrictEqual(s.over, { winnerSlot: 1, reason: 'normal' });

  s = ready(); s.sc = [2, 2]; s.elapsed = RULES.MAX_MATCH_MS - 10;
  const ev = run(s, 0.2, () => idle());
  assert.ok(ev.some(e => e.t === 'golden'));
  assert.strictEqual(s.over, null, 'la partie continue en but en or');
  s.elapsed = RULES.MAX_MATCH_MS + RULES.GOLDEN_MS - 10;
  run(s, 0.2, () => idle());
  assert.deepStrictEqual(s.over, { winnerSlot: 0, reason: 'draw' });

  s = ready(); s.sc = [2, 2]; s.elapsed = RULES.MAX_MATCH_MS + 5; s.golden = true;
  s.p[0].x = FIELD.FX + 30; s.p[0].y = FIELD.FY + FIELD.FH - 80;
  s.p[1].y = FIELD.FY + FIELD.FH - 160; s.p[1].x = FIELD.FX + FIELD.FW / 2; s.b.x = s.p[1].x; s.b.y = s.p[1].y + 26;
  run(s, 2, () => [E.NO_INPUT, inp({ kick: true })]);
  assert.deepStrictEqual(s.over, { winnerSlot: 2, reason: 'normal' }, 'le but en or met fin au match');
});

test('terrain : jamais de sortie de joueur ni de balle hors des limites', () => {
  const s = ready(); const r = rng(99);
  for (let i = 0; i < 60 * 60; i++) {
    const ins = [inp({ dx: r() * 2 - 1, dy: r() * 2 - 1, kick: r() < 0.1, deg: r() < 0.05, spr: r() < 0.5 }),
                 inp({ dx: r() * 2 - 1, dy: r() * 2 - 1, kick: r() < 0.1, deg: r() < 0.05, spr: r() < 0.5 })];
    E.step(s, ins, STEP, r);
    for (const p of s.p) {
      assert.ok(p.x >= FIELD.FX && p.x <= FIELD.FX + FIELD.FW && p.y >= FIELD.FY && p.y <= FIELD.FY + FIELD.FH, 'joueur dans le terrain');
    }
    assert.ok(s.b.x >= 0 && s.b.x <= FIELD.W && s.b.y >= 0 && s.b.y <= FIELD.H, 'balle dans la scène');
    assert.ok(Number.isFinite(s.b.x) && Number.isFinite(s.b.y));
    if (s.over) break;
  }
});

test('déterminisme : mêmes entrées, même graine, même partie', () => {
  const play = () => {
    const s = E.createState(rng(3)); const r = rng(5), c = rng(11);
    for (let i = 0; i < 60 * 30; i++) E.step(s, [inp({ dx: c() * 2 - 1, dy: c() * 2 - 1, kick: c() < .1 }), inp({ dx: c() * 2 - 1, dy: c() * 2 - 1, kick: c() < .1 })], STEP, r);
    return JSON.stringify(E.snapshot(s));
  };
  assert.strictEqual(play(), play());
});

test('instantané réseau compact et complet', () => {
  const snap = E.snapshot(ready());
  for (const key of ['k', 'ph', 'pt', 'sc', 'cd', 'cn', 'sp', 'lk', 'p', 'b', 'fb', 'el', 'go']) assert.ok(key in snap, key);
  assert.strictEqual(snap.p.length, 2);
  assert.ok(JSON.stringify(snap).length < 400, 'instantané < 400 octets');
});

console.log(`\n${passed} tests TIKAN (moteur) réussis`);
