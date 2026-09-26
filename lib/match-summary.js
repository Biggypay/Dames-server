'use strict';

/**
 * Résumé d'un match pour sa carte publique (page joueur de l'application) :
 * combien de coups chacun a joués, le score, les manches.
 *
 * `games` ne garde que le vainqueur et la durée ; le reste n'existe que dans
 * la room. On le compte pendant la partie (countMove, à chaque coup ACCEPTÉ)
 * et on l'envoie une fois le résultat réglé — sans jamais retarder ni faire
 * échouer ce règlement.
 *
 * Les joueurs sont désignés par leur id Supabase, jamais par leur place : la
 * base vérifie que ce sont bien les deux joueurs de la partie
 * (public.record_match_summary).
 */

const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;

/** Jeux où un « coup » a un sens de plateau (pas un choix simultané). */
const BOARD_GAMES = new Set(['dames', 'echecs', 'tictactoe', 'quoridor', 'gomoku']);
/** Jeux à choix simultanés : un choix par joueur et par manche. */
const CHOICE_GAMES = new Set(['penalty', 'chifoumi']);

const toCount = value => {
  const n = Number(value);
  return Number.isFinite(n) && n >= 0 ? Math.floor(n) : 0;
};

/** À appeler une fois par coup accepté par le serveur, jamais sur un refus. */
function countMove(room, slot) {
  if (!room || (slot !== 1 && slot !== 2)) return;
  if (!room.movesPlayed || typeof room.movesPlayed !== 'object') room.movesPlayed = { 1: 0, 2: 0 };
  room.movesPlayed[slot] = toCount(room.movesPlayed[slot]) + 1;
}

/** Score par place, quand le jeu en a un. */
function scoresFor(game, room) {
  switch (game) {
    case 'tictactoe': {
      const s = room.gameState || {};
      return { 1: toCount(s.matchW), 2: toCount(s.matchR) };
    }
    case 'gomoku': {
      const wins = room.series?.wins;
      return wins ? { 1: toCount(wins[1]), 2: toCount(wins[2]) } : null;
    }
    case 'penalty':
      return room.scores ? { 1: toCount(room.scores.p1), 2: toCount(room.scores.p2) } : null;
    case 'chifoumi':
      return Array.isArray(room.scores) ? { 1: toCount(room.scores[0]), 2: toCount(room.scores[1]) } : null;
    default:
      return null;
  }
}

function roundsFor(game, room, moves) {
  switch (game) {
    case 'tictactoe': return toCount(room.gameState?.manchesDone);
    case 'gomoku': return toCount(room.series?.roundsPlayed);
    case 'chifoumi': return Array.isArray(room.history) ? room.history.length : null;
    // Une manche de penalty = un tir : les deux joueurs ont choisi.
    case 'penalty': return Math.min(moves[1], moves[2]);
    default: return null;
  }
}

/**
 * @param {string} game   clé du serveur ('dames', 'echecs', …)
 * @param {object} room   la room terminée
 * @param {string} reason raison de fin ('checkmate', 'timeout', 'forfeit', …)
 * @returns {object|null} null quand les deux joueurs ne sont pas identifiés
 */
function buildMatchSummary(game, room, reason) {
  if (!room || !room.players) return null;
  const ids = { 1: room.players[1]?.supabaseId, 2: room.players[2]?.supabaseId };
  if (!UUID.test(String(ids[1] || '')) || !UUID.test(String(ids[2] || '')) || ids[1] === ids[2]) return null;

  const counted = BOARD_GAMES.has(game) || CHOICE_GAMES.has(game);
  const moves = { 1: toCount(room.movesPlayed?.[1]), 2: toCount(room.movesPlayed?.[2]) };
  const scores = scoresFor(game, room);

  const summary = { players: {} };
  for (const slot of [1, 2]) {
    const entry = {};
    if (counted) entry.moves = moves[slot];
    if (scores) entry.score = scores[slot];
    summary.players[ids[slot]] = entry;
  }
  if (counted) summary.moves_total = moves[1] + moves[2];
  const rounds = roundsFor(game, room, moves);
  if (rounds !== null && rounds !== undefined) summary.rounds = rounds;
  const cleanReason = String(reason || '').toLowerCase().replace(/[^a-z_]/g, '').slice(0, 40);
  if (cleanReason) summary.reason = cleanReason;
  return summary;
}

module.exports = { countMove, buildMatchSummary, scoresFor, BOARD_GAMES, CHOICE_GAMES };
