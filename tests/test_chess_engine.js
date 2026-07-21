// Tests du moteur d'échecs partagé (public/echecs-engine.js).
//  1. perft — comptage exhaustif de coups sur des positions de référence
//     (roque, prise en passant, promotions, clouages, échecs) ;
//  2. règles FIDE — mat, pat, 50 coups, triple répétition, matériel insuffisant ;
//  3. recherche — l'IA trouve un mat en 1 et ne joue jamais un coup illégal.
const { ChessEngineFactory } = require('../public/echecs-engine.js');
const Chess = ChessEngineFactory();

let failures = 0;
function check(label, cond, detail) {
  if (cond) console.log('  ✅ ' + label);
  else { failures++; console.log('  ❌ ' + label + (detail !== undefined ? ' → ' + JSON.stringify(detail) : '')); }
}

console.log('— perft (positions de référence) —');
const PERFT_CASES = [
  { name: 'position initiale', fen: 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1', depths: [20, 400, 8902, 197281] },
  { name: 'kiwipete', fen: 'r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1', depths: [48, 2039, 97862] },
  { name: 'finale e.p. (pos 3)', fen: '8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1', depths: [14, 191, 2812, 43238] },
  { name: 'promotions (pos 4)', fen: 'r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1', depths: [6, 264, 9467] },
  { name: 'promotions massives', fen: 'n1n5/PPPk4/8/8/8/8/4Kppp/5N1N b - - 0 1', depths: [24, 496, 9483] },
  { name: 'position 5 (talkchess)', fen: 'rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8', depths: [44, 1486, 62379] }
];
for (const tc of PERFT_CASES) {
  const s = Chess.fromFEN(tc.fen);
  check(tc.name + ' — FEN importée', !!s);
  if (!s) continue;
  check(tc.name + ' — FEN round-trip', Chess.toFEN(s).startsWith(tc.fen.split(' ').slice(0, 4).join(' ')), Chess.toFEN(s));
  for (let d = 1; d <= tc.depths.length; d++) {
    const got = Chess.perft(s, d);
    check(`${tc.name} — perft(${d}) = ${tc.depths[d - 1]}`, got === tc.depths[d - 1], got);
  }
}

console.log('— règles de fin de partie —');
{
  // Mat du berger : 1.e4 e5 2.Fc4 Cc6 3.Dh5 Cf6?? 4.Dxf7#
  let s = Chess.initialState();
  const play = (from, to) => {
    const mv = Chess.findMove(s, Chess.fromAlg(from), Chess.fromAlg(to));
    if (!mv) throw new Error('coup illégal dans le test: ' + from + '-' + to);
    s = Chess.applyMove(s, mv);
  };
  play('e2', 'e4'); play('e7', 'e5');
  play('f1', 'c4'); play('b8', 'c6');
  play('d1', 'h5'); play('g8', 'f6');
  play('h5', 'f7');
  const st = Chess.gameStatus(s);
  check('mat du berger détecté', st.over && st.reason === 'checkmate' && st.winner === 0, st);
  check('le camp maté est en échec', Chess.inCheck(s, 1) === true);
}
{
  // Pat classique : roi noir a8, dame blanche c7, roi blanc c6 — trait aux Noirs.
  const s = Chess.fromFEN('k7/2Q5/2K5/8/8/8/8/8 b - - 0 1');
  const st = Chess.gameStatus(s);
  check('pat détecté (nulle)', st.over && st.reason === 'stalemate' && st.winner === null, st);
}
{
  // Règle des 50 coups : compteur à 100 demi-coups.
  const s = Chess.fromFEN('k7/8/1K6/8/8/8/8/6R1 w - - 100 80');
  const st = Chess.gameStatus(s);
  check('règle des 50 coups détectée', st.over && st.reason === 'fifty', st);
}
{
  // Triple répétition : navette des deux cavaliers.
  let s = Chess.initialState();
  const shuttle = [['g1', 'f3'], ['g8', 'f6'], ['f3', 'g1'], ['f6', 'g8']];
  for (let round = 0; round < 2; round++) {
    for (const [from, to] of shuttle) {
      const mv = Chess.findMove(s, Chess.fromAlg(from), Chess.fromAlg(to));
      s = Chess.applyMove(s, mv);
    }
  }
  const st = Chess.gameStatus(s);
  check('triple répétition détectée', st.over && st.reason === 'repetition', st);
}
{
  const cases = [
    ['k7/8/8/8/8/8/8/7K w - - 0 1', true, 'roi contre roi'],
    ['k7/8/8/8/8/8/8/6BK w - - 0 1', true, 'roi + fou contre roi'],
    ['k7/8/8/8/8/8/8/6NK w - - 0 1', true, 'roi + cavalier contre roi'],
    ['kn6/8/8/8/8/8/8/6NK w - - 0 1', false, 'cavalier contre cavalier ≠ nul auto'],
    ['k7/8/8/8/8/8/8/6RK w - - 0 1', false, 'tour présente'],
    ['k7/p7/8/8/8/8/8/7K w - - 0 1', false, 'pion présent']
  ];
  for (const [fen, expected, label] of cases) {
    const s = Chess.fromFEN(fen);
    check('matériel insuffisant — ' + label, Chess.insufficientMaterial(s.b) === expected);
  }
  // Deux fous de MÊME couleur de case = nul (b8 et g1 sont tous deux des cases sombres... vérifions h8/a1 sombres)
  const same = Chess.fromFEN('k1b5/8/8/8/8/8/8/2B4K w - - 0 1'); // c8 (case claire) et c1 (case sombre) → opposées
  check('fous cases opposées ≠ nul', Chess.insufficientMaterial(same.b) === false);
  const same2 = Chess.fromFEN('k1b5/8/8/8/8/8/8/1B5K w - - 0 1'); // c8 claire et b1 claire → même couleur
  check('fous même couleur de case = nul', Chess.insufficientMaterial(same2.b) === true);
}

console.log('— droits de roque & en passant —');
{
  let s = Chess.fromFEN('r3k2r/8/8/8/8/8/8/R3K2R w KQkq - 0 1');
  const kingside = Chess.findMove(s, Chess.fromAlg('e1'), Chess.fromAlg('g1'));
  check('roque blanc O-O généré', !!kingside && kingside.castle === 1);
  const queenside = Chess.findMove(s, Chess.fromAlg('e1'), Chess.fromAlg('c1'));
  check('roque blanc O-O-O généré', !!queenside && queenside.castle === 2);
  const after = Chess.applyMove(s, kingside);
  check('roque exécuté : tour en f1', after.b[Chess.fromAlg('f1')] === 4 && after.b[Chess.fromAlg('g1')] === 6);
  check('droits blancs perdus après roque', (after.c & 3) === 0 && (after.c & 12) === 12);
  // Tour a1 bouge → perte O-O-O seulement.
  const rookMove = Chess.findMove(s, Chess.fromAlg('a1'), Chess.fromAlg('a2'));
  const afterRook = Chess.applyMove(s, rookMove);
  check('tour a1 jouée → O-O-O perdu, O-O conservé', (afterRook.c & 2) === 0 && (afterRook.c & 1) === 1);
  // Roque interdit à travers un échec : tour noire contrôle f1.
  const blocked = Chess.fromFEN('4k3/8/8/8/8/8/5r2/R3K2R w KQ - 0 1');
  check('roque O-O interdit (case f1 attaquée)', !Chess.findMove(blocked, Chess.fromAlg('e1'), Chess.fromAlg('g1')));
  check('roque O-O-O interdit (roi arrive en échec ? non : d1 attaquée ? non) → autorisé',
    !!Chess.findMove(blocked, Chess.fromAlg('e1'), Chess.fromAlg('c1')));
}
{
  // Prise en passant obligatoire de légalité : le pion b5 blanc peut prendre a6 e.p. ?
  let s = Chess.fromFEN('rnbqkbnr/1ppppppp/8/pP6/8/8/P1PPPPPP/RNBQKBNR w KQkq a6 0 3');
  const ep = Chess.findMove(s, Chess.fromAlg('b5'), Chess.fromAlg('a6'));
  check('prise en passant générée', !!ep && ep.ep === true);
  const after = Chess.applyMove(s, ep);
  check('pion noir a5 retiré après e.p.', after.b[Chess.fromAlg('a5')] === 0 && after.b[Chess.fromAlg('a6')] === 1);
  // e.p. illégale si elle expose le roi (clouage horizontal).
  const pinned = Chess.fromFEN('8/8/8/KPp4r/8/8/8/4k3 w - c6 0 2');
  check('e.p. refusée si elle expose le roi', !Chess.findMove(pinned, Chess.fromAlg('b5'), Chess.fromAlg('c6')));
}

console.log('— promotion —');
{
  const s = Chess.fromFEN('8/P6k/8/8/8/8/8/K7 w - - 0 1');
  const moves = Chess.legalMoves(s).filter(m => m.f === Chess.fromAlg('a7'));
  check('4 choix de promotion générés', moves.length === 4 && moves.every(m => m.p >= 2 && m.p <= 5));
  const toKnight = Chess.findMove(s, Chess.fromAlg('a7'), Chess.fromAlg('a8'), 'n');
  check('promotion cavalier retrouvée', !!toKnight && toKnight.p === 2);
  const dflt = Chess.findMove(s, Chess.fromAlg('a7'), Chess.fromAlg('a8'));
  check('promotion par défaut = dame', !!dflt && dflt.p === 5);
  const after = Chess.applyMove(s, dflt);
  check('dame blanche posée en a8', after.b[Chess.fromAlg('a8')] === 5);
}

console.log('— état JSON & sanitisation —');
{
  const s = Chess.initialState();
  const roundTrip = Chess.sanitizeState(JSON.parse(JSON.stringify(Chess.exportState(s))));
  check('export/import JSON stable', !!roundTrip && Chess.positionKey(roundTrip) === Chess.positionKey(s));
  check('état invalide rejeté (2 rois blancs)', Chess.sanitizeState({ b: s.b.map(p => (p === -6 ? 6 : p)), t: 0 }) === null);
  check('état invalide rejeté (mauvaise taille)', Chess.sanitizeState({ b: [1, 2, 3], t: 0 }) === null);
}

console.log('— recherche IA —');
{
  // Mat en 1 : dame h5 prend f7 (position du mat du berger, trait aux Blancs).
  const s = Chess.fromFEN('r1bqkb1r/pppp1ppp/2n2n2/4p2Q/2B1P3/8/PPPP1PPP/RNB1K1NR w KQkq - 4 4');
  const res = Chess.rankRoot(Chess.exportState(s), 1500, 8);
  const moves = Chess.legalMoves(s);
  check('rankRoot renvoie un index valide', res.idx >= 0 && res.idx < moves.length, res.idx);
  const chosen = moves[res.idx];
  const after = Chess.applyMove(s, chosen);
  const st = Chess.gameStatus(after);
  check('l\'IA trouve le mat en 1 (Dxf7#)', st.over && st.reason === 'checkmate',
    { move: Chess.moveLabel(s, chosen), status: st });
}
{
  // L'IA (Noirs) doit parer un mat en 1 : après 1.e4 e5 2.Fc4 Cc6 3.Dh5,
  // tout coup noir laissant Dxf7# passer est un échec de l'IA.
  const s = Chess.fromFEN('r1bqkbnr/pppp1ppp/2n5/4p2Q/2B1P3/8/PPPP1PPP/RNB1K1NR b KQkq - 3 3');
  const res = Chess.rankRoot(Chess.exportState(s), 1500, 8);
  const moves = Chess.legalMoves(s);
  check('rankRoot (défense) index valide', res.idx >= 0 && res.idx < moves.length);
  const after = Chess.applyMove(s, moves[res.idx]);
  const reply = Chess.findMove(after, Chess.fromAlg('h5'), Chess.fromAlg('f7'));
  let mateAllowed = false;
  if (reply) {
    const st = Chess.gameStatus(Chess.applyMove(after, reply));
    mateAllowed = st.over && st.reason === 'checkmate';
  }
  check('l\'IA pare le mat du berger', !mateAllowed, Chess.moveLabel(s, moves[res.idx]));
}
{
  // 200 demi-coups aléatoires : jamais d'exception, jamais de coup illégal,
  // statut cohérent — le moteur doit rester stable sur n'importe quelle ligne.
  let s = Chess.initialState(), plies = 0;
  let rngState = 42;
  const rng = () => { rngState = (rngState * 1103515245 + 12345) & 0x7fffffff; return rngState / 0x7fffffff; };
  while (plies < 200) {
    const st = Chess.gameStatus(s);
    if (st.over) break;
    const moves = Chess.legalMoves(s);
    if (!moves.length) break;
    s = Chess.applyMove(s, moves[(rng() * moves.length) | 0]);
    plies++;
  }
  const kings = s.b.filter(p => p === 6 || p === -6).length;
  check('partie aléatoire stable (' + plies + ' demi-coups)', kings === 2);
}

console.log(failures === 0 ? '\n🎉 Tous les tests moteur échecs passent' : '\n💥 ' + failures + ' échec(s)');
process.exit(failures === 0 ? 0 : 1);
