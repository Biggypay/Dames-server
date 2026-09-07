'use strict';

// Pendule d'échecs Fischer, tenue par le serveur.
//
// Le plateau d'échecs partageait jusqu'ici le chronomètre générique des autres
// jeux : 30 secondes par coup, puis 60 secondes de grâce. Ça convient à une
// partie de dames ; ça ne veut rien dire aux échecs, où le temps est un budget
// pour toute la partie. Une cadence 10+5 signifie : dix minutes chacun, et cinq
// secondes rendues après chaque coup VALIDE. Un coup illégal ne rend rien.
//
// Tout est ici, en fonctions pures, pour que la logique se teste sans socket :
// le serveur ne fait qu'appeler ces fonctions au bon moment et armer un
// setTimeout sur le temps restant.
//
// Slot 1 = Blancs (trait initial), slot 2 = Noirs. C'est la convention déjà
// établie par la base (games.player1_id joue les Blancs) et par le moteur
// (state.t vaut 0 pour les Blancs).

const WP = 1, WN = 2, WB = 3, WR = 4, WQ = 5, WK = 6;

const MIN_MS = 1000;             // une pendule d'une seconde n'a pas de sens
const MAX_MS = 3 * 60 * 60_000;  // trois heures : au-delà, c'est une faute de saisie
const MAX_INCREMENT_MS = 60_000;

const clampMs = (value, fallback) => {
  const n = Number(value);
  if (!Number.isFinite(n)) return fallback;
  return Math.min(MAX_MS, Math.max(MIN_MS, Math.round(n)));
};

/**
 * Cadence officielle d'une partie, lue dans `games.game_settings`.
 *
 * Le navigateur n'a aucune prise dessus : cette structure est écrite par la
 * base au moment de créer la partie, et le serveur la relit avec sa clé de
 * service. Retourne null pour une partie sans cadence déclarée — les parties
 * libres gardent alors le chronomètre par tour d'origine.
 */
function readTimeControl(gameSettings) {
  const raw = gameSettings && typeof gameSettings === 'object' ? gameSettings.chess_time_control : null;
  if (!raw || typeof raw !== 'object') return null;

  const white = Number(raw.white_seconds);
  const black = Number(raw.black_seconds);
  const base = Number(raw.base_seconds);
  if (!Number.isFinite(white) && !Number.isFinite(black) && !Number.isFinite(base)) return null;

  const fallback = Number.isFinite(base) ? base * 1000 : 600_000;
  const increment = Number(raw.increment_seconds);
  return {
    whiteMs: clampMs(Number.isFinite(white) ? white * 1000 : fallback, fallback),
    blackMs: clampMs(Number.isFinite(black) ? black * 1000 : fallback, fallback),
    incrementMs: Math.min(MAX_INCREMENT_MS, Math.max(0, Number.isFinite(increment) ? Math.round(increment * 1000) : 0)),
    armageddon: raw.armageddon === true,
    label: typeof raw.label === 'string' ? raw.label.slice(0, 32) : null
  };
}

function createClock(timeControl) {
  if (!timeControl) return null;
  return {
    remaining: { 1: timeControl.whiteMs, 2: timeControl.blackMs },
    incrementMs: timeControl.incrementMs,
    armageddon: timeControl.armageddon === true,
    label: timeControl.label || null,
    // Slot dont la pendule tourne, et depuis quand. `null` = les deux pendules
    // sont arrêtées (partie pas encore lancée, pause, déconnexion).
    runningSlot: null,
    lastTickAt: null
  };
}

/**
 * Une pendule qui revient de la persistance a traversé du JSON, et peut-être un
 * redémarrage de Render. On la revalide toujours, et on l'arrête : le temps
 * pendant lequel le serveur était absent n'est facturé à personne.
 */
function sanitizeClock(raw) {
  if (!raw || typeof raw !== 'object') return null;
  const one = Number(raw.remaining?.[1] ?? raw.remaining?.['1']);
  const two = Number(raw.remaining?.[2] ?? raw.remaining?.['2']);
  if (!Number.isFinite(one) || !Number.isFinite(two)) return null;
  return {
    remaining: {
      1: Math.min(MAX_MS, Math.max(0, Math.round(one))),
      2: Math.min(MAX_MS, Math.max(0, Math.round(two)))
    },
    incrementMs: Math.min(MAX_INCREMENT_MS, Math.max(0, Math.round(Number(raw.incrementMs) || 0))),
    armageddon: raw.armageddon === true,
    label: typeof raw.label === 'string' ? raw.label.slice(0, 32) : null,
    runningSlot: null,
    lastTickAt: null
  };
}

/** Temps restant d'un slot à l'instant `now`, pendule en marche comprise. */
function remainingFor(clock, slot, now) {
  if (!clock) return null;
  const stored = Math.max(0, Number(clock.remaining?.[slot]) || 0);
  // `lastTickAt` peut valoir 0 : on compare à null, jamais par falsy.
  if (clock.runningSlot !== slot || clock.lastTickAt === null || clock.lastTickAt === undefined) return stored;
  return Math.max(0, stored - Math.max(0, now - clock.lastTickAt));
}

/**
 * Arrête les deux pendules et facture au slot en marche le temps écoulé.
 * Appelée avant chaque bascule, à chaque pause et à chaque déconnexion.
 */
function chargeElapsed(clock, now) {
  if (!clock || clock.runningSlot === null) return clock;
  const slot = clock.runningSlot;
  clock.remaining[slot] = remainingFor(clock, slot, now);
  clock.runningSlot = null;
  clock.lastTickAt = null;
  return clock;
}

/** L'incrément Fischer, dû seulement après un coup accepté. */
function addIncrement(clock, slot) {
  if (!clock || !clock.incrementMs) return clock;
  clock.remaining[slot] = Math.min(MAX_MS, (Number(clock.remaining[slot]) || 0) + clock.incrementMs);
  return clock;
}

function startSlot(clock, slot, now) {
  if (!clock) return clock;
  chargeElapsed(clock, now);
  clock.runningSlot = slot;
  clock.lastTickAt = now;
  return clock;
}

/** Ce que le client affiche : deux compteurs et le slot qui tourne. */
function clockSnapshot(clock, now) {
  if (!clock) return null;
  return {
    white: remainingFor(clock, 1, now),
    black: remainingFor(clock, 2, now),
    incrementMs: clock.incrementMs,
    armageddon: clock.armageddon === true,
    label: clock.label || null,
    runningSlot: clock.runningSlot,
    serverTime: now
  };
}

/**
 * Le camp `side` (0 = Blancs, 1 = Noirs) peut-il encore mater, par une suite de
 * coups légaux quelconque ?
 *
 * Un pion, une tour ou une dame suffisent. Deux pièces mineures aussi : le mat
 * avec fou et cavalier existe, et même avec deux cavaliers il est possible sans
 * être forçable — or l'article 6.9 parle bien de « toute suite de coups
 * légaux ». Roi seul, roi et fou, roi et cavalier : mat impossible.
 */
function hasMatingMaterial(board, side) {
  if (!Array.isArray(board) && !ArrayBuffer.isView(board)) return true;
  let minors = 0;
  for (let i = 0; i < 64; i++) {
    const piece = Number(board[i]) || 0;
    if (piece === 0) continue;
    const isWhite = piece > 0;
    if ((side === 0) !== isWhite) continue;
    const kind = piece < 0 ? -piece : piece;
    if (kind === WP || kind === WR || kind === WQ) return true;
    if (kind === WN || kind === WB) minors += 1;
  }
  return minors >= 2;
}

/**
 * Verdict d'un drapeau tombé, article 6.9 : le joueur au temps écoulé perd,
 * SAUF si son adversaire ne peut mater par aucune suite de coups légaux —
 * auquel cas la partie est nulle.
 *
 * Retourne { winnerSlot, reason } ; winnerSlot vaut 0 pour une nulle.
 */
function flagFallOutcome(state, flaggedSlot) {
  const opponentSlot = flaggedSlot === 1 ? 2 : 1;
  const opponentSide = opponentSlot === 1 ? 0 : 1;
  const board = state && state.b ? state.b : null;
  if (board && !hasMatingMaterial(board, opponentSide)) {
    return { winnerSlot: 0, reason: 'draw', detail: 'timeout_insufficient_material' };
  }
  return { winnerSlot: opponentSlot, reason: 'timeout', detail: 'timeout' };
}

module.exports = {
  readTimeControl,
  createClock,
  sanitizeClock,
  remainingFor,
  chargeElapsed,
  addIncrement,
  startSlot,
  clockSnapshot,
  hasMatingMaterial,
  flagFallOutcome
};
