'use strict';

const REGULAR_ROUNDS = 6;

function ensureSeriesState(room) {
  if (!room.series || typeof room.series !== 'object') {
    room.series = {
      regularRounds: REGULAR_ROUNDS,
      roundsPlayed: 0,
      currentRound: 1,
      wins: { 1: 0, 2: 0 },
      draws: 0,
      history: [],
      suddenDeath: false,
      roundStarter: room.currentSlot === 2 ? 2 : 1
    };
  }
  if (!room.series.wins) room.series.wins = { 1: 0, 2: 0 };
  if (!Array.isArray(room.series.history)) room.series.history = [];
  return room.series;
}

function seriesPayload(room) {
  const s = ensureSeriesState(room);
  return {
    regularRounds: s.regularRounds || REGULAR_ROUNDS,
    roundsPlayed: s.roundsPlayed || 0,
    currentRound: s.currentRound || 1,
    wins: { 1: Number(s.wins[1]) || 0, 2: Number(s.wins[2]) || 0 },
    draws: Number(s.draws) || 0,
    history: s.history.slice(0, REGULAR_ROUNDS),
    suddenDeath: !!s.suddenDeath,
    roundStarter: s.roundStarter === 2 ? 2 : 1
  };
}

function recordRoundResult(room, winnerSlot) {
  const s = ensureSeriesState(room);
  const winner = winnerSlot === 1 || winnerSlot === 2 ? winnerSlot : 0;
  s.roundsPlayed += 1;
  if (winner) s.wins[winner] = (Number(s.wins[winner]) || 0) + 1;
  else s.draws = (Number(s.draws) || 0) + 1;
  if (s.history.length < REGULAR_ROUNDS) s.history.push(winner);

  let matchOver = false;
  let matchWinner = 0;
  const w1 = Number(s.wins[1]) || 0;
  const w2 = Number(s.wins[2]) || 0;

  if (s.suddenDeath) {
    if (winner) {
      matchOver = true;
      matchWinner = winner;
    }
  } else if (s.roundsPlayed < REGULAR_ROUNDS) {
    const remaining = REGULAR_ROUNDS - s.roundsPlayed;
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
