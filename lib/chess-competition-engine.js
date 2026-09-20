'use strict';

// ATTENTION : CE MODULE N'EST BRANCHE NULLE PART.
// server.js ne le requiert pas et il n'existe aucun handler de reclamation de
// nulle. Les parties reellement servies suivent la regle de
// public/echecs-engine.js, qui conclut AUTOMATIQUEMENT des la 3e repetition
// (ligne 357) ou au 50e coup. Seuls tests/test_chess_competition_rules.js et
// tests/test_chess_clock.js exercent ce fichier, en isolation.
//
// Le brancher demande trois choses ENSEMBLE : confier la conclusion des
// parties a `competitionOutcome` dans server.js, ajouter le handler
// `echecs_claim_draw` emettant `echecs_draw_claimed`, et offrir un bouton
// « reclamer la nulle » aux joueurs — sans lui, une nulle seulement
// reclamable ne serait jamais reclamee et la partie trainerait jusqu'a la 5e
// repetition. C'est un changement de regles du jeu qui decide quand une
// partie se termine, donc quand la mise est reglee : il demande une decision
// du proprietaire du projet, pas une initiative technique.
//
// Competition wrapper around the shared chess engine.
// It keeps move legality identical to the battle-tested base engine while
// applying the FIDE distinction between claimable and automatic draws:
//   - 3 repetitions / 50 moves => a player may CLAIM a draw;
//   - 5 repetitions / 75 moves => draw is AUTOMATIC.
// It also removes a phantom en-passant square from the repetition key when no
// legal en-passant capture actually exists (notably when the adjacent pawn is
// pinned to its king).
const { ChessEngineFactory: BaseChessEngineFactory } = require('../public/echecs-engine.js');

function createCompetitionFacade(base) {
  function normalizeEpAndRepetition(previous, next, light) {
    if (!next || next.ep < 0) return next;

    const hasLegalEnPassant = base.legalMoves(next).some((move) => move && move.ep === true);
    if (hasLegalEnPassant) return next;

    const oldKey = next.key;
    next.ep = -1;
    next.key = base.positionKey(next);

    if (!light && next.reps && oldKey !== next.key) {
      const reps = {};
      for (const key in next.reps) reps[key] = next.reps[key];
      if (reps[oldKey]) {
        reps[oldKey] -= 1;
        if (reps[oldKey] <= 0) delete reps[oldKey];
      }
      reps[next.key] = (reps[next.key] || 0) + 1;
      next.reps = reps;
    }
    return next;
  }

  function applyMove(state, move, light) {
    return normalizeEpAndRepetition(state, base.applyMove(state, move, light), !!light);
  }

  function claimableDraw(state) {
    if (!state) return null;
    const repetitions = state.reps && state.key ? Number(state.reps[state.key] || 0) : 0;
    if (Number(state.h || 0) >= 100) return 'fifty';
    if (repetitions >= 3) return 'repetition';
    return null;
  }

  function gameStatus(state, precomputedMoves) {
    const moves = precomputedMoves || base.legalMoves(state);
    if (moves.length === 0) {
      if (base.inCheck(state, state.t)) return { over: true, winner: 1 - state.t, reason: 'checkmate', claimable: null };
      return { over: true, winner: null, reason: 'stalemate', claimable: null };
    }

    // FIDE 9.6: these are automatic draws. Checkmate/stalemate are evaluated
    // first, so a mating last move is never overridden by the 75-move rule.
    const repetitions = state.reps && state.key ? Number(state.reps[state.key] || 0) : 0;
    if (Number(state.h || 0) >= 150) return { over: true, winner: null, reason: 'seventyfive', claimable: null };
    if (repetitions >= 5) return { over: true, winner: null, reason: 'fivefold', claimable: null };
    if (base.insufficientMaterial(state.b)) return { over: true, winner: null, reason: 'insufficient', claimable: null };

    return { over: false, winner: null, reason: null, claimable: claimableDraw(state) };
  }

  return Object.assign({}, base, {
    applyMove,
    gameStatus,
    claimableDraw,
  });
}

function ChessEngineFactory() {
  return createCompetitionFacade(BaseChessEngineFactory());
}

module.exports = { ChessEngineFactory, createCompetitionFacade };
