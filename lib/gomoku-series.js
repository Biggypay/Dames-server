'use strict';

const REGULAR_ROUNDS = 6;
const MAX_DECISIVE_SHOWN = 12;

/* Le nombre de manches prévues d'une salle : 6 par défaut (Morpion à 5) ; une salle peut en annoncer un autre
   (`room.regularRounds`) — Quoridor se joue en UNE partie depuis le 2026-11-20 (propriétaire : « pas 6 manches,
   une seule comme celui de dames »). La série le garde : une salle restaurée finit avec le nombre de son début. */
function roundsOf(value) {
  const n = Math.floor(Number(value));
  return n >= 1 ? n : REGULAR_ROUNDS;
}
function regularOf(series) { return roundsOf(series && series.regularRounds); }

function ensureSeriesState(room) {
  if (!room.series || typeof room.series !== 'object') {
    room.series = {
      regularRounds: roundsOf(room.regularRounds),
      roundsPlayed: 0,
      currentRound: 1,
      wins: { 1: 0, 2: 0 },
      draws: 0,
      history: [],
      suddenDeath: false,
      decisive: [],
      roundStarter: room.currentSlot === 2 ? 2 : 1
    };
  }
  if (!room.series.wins) room.series.wins = { 1: 0, 2: 0 };
  if (!Array.isArray(room.series.history)) room.series.history = [];
  if (!Array.isArray(room.series.decisive)) room.series.decisive = [];
  return room.series;
}

function seriesPayload(room) {
  const s = ensureSeriesState(room);
  return {
    regularRounds: regularOf(s),
    roundsPlayed: s.roundsPlayed || 0,
    currentRound: s.currentRound || 1,
    wins: { 1: Number(s.wins[1]) || 0, 2: Number(s.wins[2]) || 0 },
    draws: Number(s.draws) || 0,
    history: s.history.slice(0, regularOf(s)),
    // Les manches décisives (mort subite), au-delà des manches prévues : les
    // pages les montrent sur leur propre rangée, sous les autres.
    decisive: s.decisive.slice(0, MAX_DECISIVE_SHOWN),
    suddenDeath: !!s.suddenDeath,
    roundStarter: s.roundStarter === 2 ? 2 : 1
  };
}

function recordRoundResult(room, winnerSlot) {
  const s = ensureSeriesState(room);
  const winner = winnerSlot === 1 || winnerSlot === 2 ? winnerSlot : 0;
  const regular = regularOf(s);
  s.roundsPlayed += 1;
  if (winner) s.wins[winner] = (Number(s.wins[winner]) || 0) + 1;
  else s.draws = (Number(s.draws) || 0) + 1;
  if (s.history.length < regular) s.history.push(winner);
  else if (s.decisive.length < MAX_DECISIVE_SHOWN) s.decisive.push(winner);

  let matchOver = false;
  let matchWinner = 0;
  const w1 = Number(s.wins[1]) || 0;
  const w2 = Number(s.wins[2]) || 0;

  if (s.suddenDeath) {
    if (winner) {
      matchOver = true;
      matchWinner = winner;
    }
  } else if (s.roundsPlayed < regular) {
    const remaining = regular - s.roundsPlayed;
    if (Math.abs(w1 - w2) > remaining) {
      matchOver = true;
      matchWinner = w1 > w2 ? 1 : 2;
    }
  } else {
    if (w1 !== w2) {
      matchOver = true;
      matchWinner = w1 > w2 ? 1 : 2;
    } else {
      s.suddenDeath = true;
    }
  }

  if (!matchOver) s.currentRound = s.roundsPlayed + 1;

  return {
    matchOver,
    matchWinner,
    roundWinner: winner,
    series: seriesPayload(room)
  };
}

function advanceRoundStarter(room) {
  const s = ensureSeriesState(room);
  s.roundStarter = s.roundStarter === 1 ? 2 : 1;
  return s.roundStarter;
}

module.exports = {
  REGULAR_ROUNDS,
  ensureSeriesState,
  seriesPayload,
  recordRoundResult,
  advanceRoundStarter
};
