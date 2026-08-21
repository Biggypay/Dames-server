'use strict';

const { ChessEngineFactory } = require('../lib/chess-competition-engine.js');
const Chess = ChessEngineFactory();

let failures = 0;
function check(label, cond, detail) {
  if (cond) console.log('  ✅ ' + label);
  else {
    failures++;
    console.log('  ❌ ' + label + (detail !== undefined ? ' → ' + JSON.stringify(detail) : ''));
  }
}

function play(state, from, to, promo) {
  const mv = Chess.findMove(state, Chess.fromAlg(from), Chess.fromAlg(to), promo || 0);
  if (!mv) throw new Error('coup introuvable: ' + from + '-' + to);
  return Chess.applyMove(state, mv);
}

console.log('— FIDE: 3 répétitions réclamables, 5 automatiques —');
{
  let s = Chess.initialState();
  const cycle = [['g1', 'f3'], ['g8', 'f6'], ['f3', 'g1'], ['f6', 'g8']];
  for (let round = 0; round < 2; round++) {
    for (const [from, to] of cycle) s = play(s, from, to);
  }
  let st = Chess.gameStatus(s);
  check('3e occurrence: partie continue', st.over === false, st);
  check('3e occurrence: nulle réclamable', st.claimable === 'repetition', st);

  for (let round = 0; round < 2; round++) {
    for (const [from, to] of cycle) s = play(s, from, to);
  }
  st = Chess.gameStatus(s);
  check('5e occurrence: nulle automatique', st.over === true && st.reason === 'fivefold', st);
}

console.log('— FIDE: 50 coups réclamables, 75 automatiques —');
{
  const fifty = Chess.fromFEN('k7/8/1K6/8/8/8/8/6R1 w - - 100 80');
  const st50 = Chess.gameStatus(fifty);
  check('50 coups: partie continue', st50.over === false, st50);
  check('50 coups: nulle réclamable', st50.claimable === 'fifty', st50);

  const seventyFive = Chess.fromFEN('k7/8/1K6/8/8/8/8/6R1 w - - 150 80');
  const st75 = Chess.gameStatus(seventyFive);
  check('75 coups: nulle automatique', st75.over === true && st75.reason === 'seventyfive', st75);
}

console.log('— répétition: case en-passant seulement si prise légalement possible —');
{
  // Roi blanc a5, pion blanc b5, tour noire h5. Après ...c7-c5, bxc6 e.p.
  // exposerait le roi blanc à la tour h5 : la prise en passant est donc
  // illégale et c6 ne doit PAS faire partie de la clé de répétition FIDE.
  let s = Chess.fromFEN('4k3/2p5/8/KP5r/8/8/8/8 b - - 0 1');
  s = play(s, 'c7', 'c5');
  check('case e.p. fantôme supprimée', s.ep === -1, Chess.toFEN(s));
  check('aucun coup e.p. légal généré', !Chess.legalMoves(s).some(m => m.ep), Chess.toFEN(s));
}

console.log('— sécurité: mat prioritaire sur règle des 75 coups —');
{
  // Position matée, compteur artificiellement à 150 : le mat doit prévaloir.
  const s = Chess.fromFEN('7k/6Q1/6K1/8/8/8/8/8 b - - 150 80');
  const st = Chess.gameStatus(s);
  check('mat prioritaire', st.over === true && st.reason === 'checkmate' && st.winner === 0, st);
}

console.log('');
console.log(failures === 0 ? '✅ RÈGLES FIDE COMPÉTITION VALIDÉES' : '💥 ' + failures + ' échec(s)');
process.exit(failures === 0 ? 0 : 1);
