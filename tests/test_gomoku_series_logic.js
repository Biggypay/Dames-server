'use strict';

const assert = require('assert');
const { ensureSeriesState, recordRoundResult, advanceRoundStarter, seriesPayload } = require('../lib/gomoku-series');

function room() {
  return { currentSlot: 1 };
}

{
  const r = room();
  ensureSeriesState(r);
  assert.deepStrictEqual(r.series.wins, { 1: 0, 2: 0 });
  assert.strictEqual(r.series.currentRound, 1);
}

{
  const r = room();
  ensureSeriesState(r);
  let result;
  result = recordRoundResult(r, 1);
  assert.strictEqual(result.matchOver, false);
  result = recordRoundResult(r, 1);
  assert.strictEqual(result.matchOver, false);
  result = recordRoundResult(r, 1);
  assert.strictEqual(result.matchOver, false);
  result = recordRoundResult(r, 1);
  assert.strictEqual(result.matchOver, true);
  assert.strictEqual(result.matchWinner, 1);
  assert.deepStrictEqual(result.series.wins, { 1: 4, 2: 0 });
}

{
  const r = room();
  ensureSeriesState(r);
  [1, 2, 1, 2, 1, 2].forEach(winner => recordRoundResult(r, winner));
  assert.strictEqual(r.series.suddenDeath, true);
  assert.strictEqual(r.series.currentRound, 7);
  const final = recordRoundResult(r, 2);
  assert.strictEqual(final.matchOver, true);
  assert.strictEqual(final.matchWinner, 2);
}

{
  const r = room();
  ensureSeriesState(r);
  [1, 2, 1, 2, 0, 0].forEach(winner => recordRoundResult(r, winner));
  assert.strictEqual(r.series.suddenDeath, true);
  const stillTied = recordRoundResult(r, 0);
  assert.strictEqual(stillTied.matchOver, false);
  // Les manches décisives ont leur propre historique : les pages les
  // dessinent sur une rangée à part, sous les six manches prévues.
  assert.deepStrictEqual(stillTied.series.history, [1, 2, 1, 2, 0, 0]);
  assert.deepStrictEqual(stillTied.series.decisive, [0]);
  const final = recordRoundResult(r, 1);
  assert.strictEqual(final.matchOver, true);
  assert.strictEqual(final.matchWinner, 1);
  assert.deepStrictEqual(final.series.decisive, [0, 1]);
}

{
  // Une salle restaurée d'avant ce champ : la série se répare d'elle-même.
  const r = room();
  r.series = { regularRounds: 6, roundsPlayed: 0, currentRound: 1, wins: { 1: 0, 2: 0 }, draws: 0, history: [], suddenDeath: false };
  assert.deepStrictEqual(seriesPayload(r).decisive, []);
}

{
  const r = room();
  ensureSeriesState(r).roundStarter = 1;
  assert.strictEqual(advanceRoundStarter(r), 2);
  assert.strictEqual(advanceRoundStarter(r), 1);
}

{
  // Quoridor en une seule partie (2026-11-20) : la salle annonce une manche ; le premier arrivé gagne le match.
  const r = { currentSlot: 1, regularRounds: 1 };
  assert.strictEqual(seriesPayload(r).regularRounds, 1);
  const end = recordRoundResult(r, 2);
  assert.strictEqual(end.matchOver, true);
  assert.strictEqual(end.matchWinner, 2);
  assert.deepStrictEqual(end.series.history, [2]);
  assert.strictEqual(end.series.suddenDeath, false);
  // Une salle sans ce champ garde ses six manches (Morpion à 5), et une série déjà commencée garde son nombre.
  assert.strictEqual(seriesPayload({ currentSlot: 1 }).regularRounds, 6);
  const restored = { currentSlot: 1, regularRounds: 1, series: { regularRounds: 6, roundsPlayed: 2, currentRound: 3, wins: { 1: 1, 2: 1 }, draws: 0, history: [1, 2], suddenDeath: false } };
  assert.strictEqual(recordRoundResult(restored, 1).matchOver, false, 'a 6-round match restored after the change ends as it began');
}

console.log('OK Gomoku series logic');
