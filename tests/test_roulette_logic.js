/**
 * Roulette Royale : les règles pures et le tirage scellé.
 *
 * Ce que ce test protège :
 *   • six couleurs, les mêmes pour les deux joueurs ;
 *   • le gagnant d'une manche (règles du 2026-11-05) : la couleur la plus
 *     proche de la couleur tirée ; à égale distance, manche nulle ; même
 *     couleur pour les deux, on rechoisit — et, pour toute paire de couleurs,
 *     chaque joueur a exactement la même chance (la roue est symétrique) ;
 *   • la fin du match : six manches (les rechoix ne comptent pas), fin
 *     anticipée quand l'écart ne peut plus être comblé, puis à égalité les
 *     manches 7 et 8, 9 et 10… DEUX PAR DEUX jusqu'à ce qu'un joueur gagne :
 *     rien ne se décide après la première d'une paire ; une paire à 1-0 (une
 *     manche nulle) décide, à 1-1 ou 0-0 elle en appelle une autre ;
 *   • la manche décisive garde la roue entière (six couleurs) et ses règles :
 *     la plus proche marque, égale distance nulle, même couleur on rechoisit ;
 *     son tirage est une couleur scellée, comme les autres ;
 *   • le tirage est uniforme, scellé avant les choix, vérifiable, et toute
 *     retouche de la valeur ou du sel se voit ;
 *   • la roue s'arrête sur la couleur tirée, au même endroit partout —
 *     parfois juste après la ligne ou juste avant la suivante (le suspens :
 *     sa part tirée du sel, son côté vers une couleur choisie voisine), au
 *     milieu à égale distance ;
 *   • le fichier des règles se charge tel quel dans un navigateur.
 */
const fs = require('fs');
const path = require('path');
const vm = require('vm');
const crypto = require('crypto');
const R = require('../lib/color-roulette');

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.log(`  FAIL ${label}${detail === undefined ? '' : ` -> ${JSON.stringify(detail)}`}`); }
}

console.log('Roulette Royale : couleurs');
check('six couleurs', R.COLORS.length === 6 && R.COLOR_COUNT === 6);
check('identifiants 0 à 5 dans l’ordre', R.COLORS.every((c, i) => c.id === i));
check('noms, teintes et formes tous différents', new Set(R.COLORS.map(c => c.name)).size === 6
  && new Set(R.COLORS.map(c => c.hex)).size === 6 && new Set(R.COLORS.map(c => c.shape)).size === 6);
check('six manches prévues', R.REGULAR_ROUNDS === 6);
check('toColor accepte 0..5 et « 3 », refuse le reste',
  R.toColor(0) === 0 && R.toColor('3') === 3 && R.toColor(6) === null && R.toColor(-1) === null
  && R.toColor(2.5) === null && R.toColor('rouge') === null && R.toColor(null) === null && R.toColor('12') === null);

console.log('Gagnant d’une manche : la couleur la plus proche');
check('distance sur la roue, par le plus court (0 à 3)', R.colorDistance(0, 0) === 0 && R.colorDistance(0, 1) === 1
  && R.colorDistance(0, 5) === 1 && R.colorDistance(1, 4) === 3 && R.colorDistance(5, 2) === 3 && R.colorDistance(4, 0) === 2
  && R.colorDistance(0, 9) === null);
check('pile sur la couleur du joueur 1', R.roundWinner(2, 4, 2) === 1);
check('pile sur la couleur du joueur 2', R.roundWinner(2, 4, 4) === 2);
check('Vert tiré : le Bleu (1 case) bat le Rouge (3 cases)', R.roundWinner(0, 4, 3) === 2);
check('Violet tiré : le Rouge (1 case) bat le Jaune (3 cases), en passant par le haut de la roue', R.roundWinner(0, 2, 5) === 1);
check('à égale distance : manche nulle (Rouge et Jaune, Orange tiré)', R.roundWinner(0, 2, 1) === 0);
check('à égale distance de l’autre côté : nulle (Rouge et Jaune, Bleu tiré)', R.roundWinner(0, 2, 4) === 0);
check('même couleur : personne (on rechoisit)', R.roundWinner(3, 3, 3) === 0 && R.roundWinner(3, 3, 1) === 0 && R.isRepick(3, 3) && !R.isRepick(3, 4));
check('tirage invalide : nulle', R.roundWinner(1, 2, null) === 0 && R.roundWinner(1, 2, 9) === 0);

// L'équité, pour TOUTE paire de couleurs différentes : autant de cases de la
// roue donnent la manche à l'un qu'à l'autre. Et la manche a un vainqueur bien
// plus souvent qu'avec « seul à avoir la couleur tirée » (1 fois sur 3).
let symmetric = true, winning = 0, cells = 0, minPair = 1;
for (let a = 0; a < 6; a++) for (let b = 0; b < 6; b++) {
  if (a === b) continue;
  let w1 = 0, w2 = 0;
  for (let d = 0; d < 6; d++) { const w = R.roundWinner(a, b, d); if (w === 1) w1++; else if (w === 2) w2++; }
  if (w1 !== w2) symmetric = false;
  winning += w1 + w2; cells += 6; minPair = Math.min(minPair, (w1 + w2) / 6);
}
check('chaque paire de couleurs : la même chance pour les deux joueurs', symmetric);
check(`une manche a un vainqueur ${(100 * winning / cells).toFixed(1)} fois sur 100 en moyenne (au moins 2 fois sur 3)`,
  Math.abs(winning / cells - 13 / 15) < 1e-9 && Math.abs(minPair - 2 / 3) < 1e-9, { winning, cells, minPair });

console.log('Suite du match');
const go = (scores, roundsPlayed, extra) => R.matchDecision({ scores, roundsPlayed, totalRounds: 6, ...extra });
check('0-0 après 1 manche : on continue', JSON.stringify(go([0, 0], 1)) === JSON.stringify({ over: false, decisive: false }));
check('4-0 après 4 manches : fin anticipée (2 restantes)', JSON.stringify(go([4, 0], 4)) === JSON.stringify({ over: true, winnerSlot: 1 }));
check('3-0 après 3 manches : encore rattrapable (3 restantes)', go([3, 0], 3).over === false);
check('0-3 après 4 manches : fin anticipée pour le 2', JSON.stringify(go([0, 3], 4)) === JSON.stringify({ over: true, winnerSlot: 2 }));
check('2-0 après 4 manches : rattrapable (2 restantes)', go([2, 0], 4).over === false);
check('1-0 après 5 manches : rattrapable (1 restante)', go([1, 0], 5).over === false);
check('3-2 après 6 manches : le 1 gagne', JSON.stringify(go([3, 2], 6)) === JSON.stringify({ over: true, winnerSlot: 1 }));
check('3-3 après 6 manches : on continue, manches décisives', JSON.stringify(go([3, 3], 6)) === JSON.stringify({ over: false, decisive: true }));
check('2-2 après 6 manches (deux nulles) : manches décisives', go([2, 2], 6).decisive === true);
check('0-0 après 6 manches : manches décisives', go([0, 0], 6).decisive === true);
const dec = (scores, decisivePlayed) => R.matchDecision({ scores, decisive: true, decisivePlayed });
check('7e manche gagnée par le 2 : l’autre joue quand même la 8e', JSON.stringify(dec([3, 4], 1)) === JSON.stringify({ over: false, decisive: true }));
check('7e manche nulle : la 8e se joue', JSON.stringify(dec([3, 3], 1)) === JSON.stringify({ over: false, decisive: true }));
check('paire 2-0 pour le 2 : fin', JSON.stringify(dec([3, 5], 2)) === JSON.stringify({ over: true, winnerSlot: 2 }));
check('paire 1-0 (une manche nulle) pour le 1 : fin', JSON.stringify(dec([4, 3], 2)) === JSON.stringify({ over: true, winnerSlot: 1 }));
check('paire 1-1 : une nouvelle paire (9e et 10e)', JSON.stringify(dec([4, 4], 2)) === JSON.stringify({ over: false, decisive: true }));
check('paire 0-0 (deux nulles) : une nouvelle paire', JSON.stringify(dec([3, 3], 2)) === JSON.stringify({ over: false, decisive: true }));
check('9e manche gagnée : on attend la réponse', dec([5, 4], 3).over === false);
check('2e paire 2-0 pour le 1 : fin', JSON.stringify(dec([6, 4], 4)) === JSON.stringify({ over: true, winnerSlot: 1 }));
check('rechoix (même couleur) : rien ne se décide', JSON.stringify(dec([3, 3], 0)) === JSON.stringify({ over: false, decisive: true }));
const hist = [
  { round: 1, decisive: false, repick: true }, { round: 2, decisive: false }, { round: 3, decisive: false },
  { round: 4, decisive: true }, { round: 5, decisive: true, repick: true }
];
check('manches comptées : sans les rechoix', R.regularPlayed(hist) === 2 && R.decisivePlayed(hist) === 1 && R.countedPlayed(hist) === 3);
check('place dans la paire : 2 (la réponse) après une décisive jouée', R.decisiveStep(hist) === 2 && R.decisiveStep([]) === 1
  && R.decisiveStep(hist.concat([{ round: 6, decisive: true }])) === 1);

console.log('Manche décisive : la roue garde ses six couleurs');
check('manche décisive : les six couleurs (« ne réduis pas »)', JSON.stringify(R.wheelFor(true, 4, 1)) === JSON.stringify([0, 1, 2, 3, 4, 5]));
check('manche normale : les six couleurs', JSON.stringify(R.wheelFor(false, 4, 1)) === JSON.stringify([0, 1, 2, 3, 4, 5]));
check('toute manche : la couleur scellée', R.drawnColor({ kind: 'color', value: 5 }, 0, 1) === 5);
check('même couleur : on rechoisit (null)', R.drawnColor({ kind: 'color', value: 5 }, 2, 2) === null);
check('un ancien sceau « bit » (roue à deux couleurs) n’a plus cours', R.drawnColor({ kind: 'bit', value: 1 }, 4, 1) === null);
check('manche décisive à égale distance : nulle, comme les autres (Rouge et Jaune, Orange tiré)', R.roundWinner(0, 2, 1) === 0);

console.log('Tirage scellé');
const seal = R.sealDraw('room-x', 3, false);
check('valeur 0..5, sel de 128 bits, empreinte SHA-256', R.isColor(seal.value) && /^[0-9a-f]{32}$/.test(seal.salt) && /^[0-9a-f]{64}$/.test(seal.hash));
check('l’empreinte se vérifie', R.verifySeal('room-x', 3, seal));
check('une autre couleur ne correspond plus', !R.verifySeal('room-x', 3, { ...seal, value: (seal.value + 1) % 6 }));
check('un autre sel ne correspond plus', !R.verifySeal('room-x', 3, { ...seal, salt: crypto.randomBytes(16).toString('hex') }));
check('une autre manche ne correspond plus', !R.verifySeal('room-x', 4, seal));
check('une autre partie ne correspond plus', !R.verifySeal('room-y', 3, seal));
check('l’empreinte = SHA-256 du texte publié', crypto.createHash('sha256').update(R.sealText('room-x', 3, 'color', seal.value, seal.salt)).digest('hex') === seal.hash);
const decisiveSeal = R.sealDraw('room-x', 7, true);
check('scellé décisif : une couleur, comme les autres', decisiveSeal.kind === 'color' && R.isColor(decisiveSeal.value) && R.verifySeal('room-x', 7, decisiveSeal));
const oldBitSalt = crypto.randomBytes(16).toString('hex');
const oldBit = { kind: 'bit', value: 1, salt: oldBitSalt, hash: R.hashSeal('room-x', 7, 'bit', 1, oldBitSalt) };
check('un ancien sceau « bit » relu après une mise à jour : la manche se rejoue (null)', R.sanitizeSeal('room-x', 7, oldBit) === null && !R.verifySeal('room-x', 7, oldBit));
check('sanitizeSeal garde un sceau intact', JSON.stringify(R.sanitizeSeal('room-x', 3, seal)) === JSON.stringify(seal));
check('sanitizeSeal refuse un sceau retouché', R.sanitizeSeal('room-x', 3, { ...seal, value: (seal.value + 2) % 6 }) === null);

// Uniformité : 60 000 tirages, khi-deux à 5 degrés de liberté (seuil 0,1 % : 20,52).
const N = 60000;
const counts = [0, 0, 0, 0, 0, 0];
for (let i = 0; i < N; i++) counts[R.sealDraw('u', i, false).value]++;
const expected = N / 6;
const chi2 = counts.reduce((sum, c) => sum + ((c - expected) ** 2) / expected, 0);
check(`tirage uniforme sur 60 000 (khi-deux ${chi2.toFixed(2)} < 20,52)`, chi2 < 20.52, counts);
const decisiveCounts = [0, 0, 0, 0, 0, 0];
for (let i = 0; i < N; i++) decisiveCounts[R.sealDraw('u', i, true).value]++;
const chi2d = decisiveCounts.reduce((sum, c) => sum + ((c - expected) ** 2) / expected, 0);
check(`tirage décisif uniforme lui aussi (khi-deux ${chi2d.toFixed(2)} < 20,52)`, chi2d < 20.52, decisiveCounts);

// Équité, avec le vrai tirage : quelles que soient les deux couleurs choisies
// (différentes, tous les écarts), chaque joueur gagne une manche normale avec
// la même probabilité, 13/30 (43 %) — la manche est nulle 2 fois sur 15.
const wins = [0, 0, 0];
for (let i = 0; i < 36000; i++) {
  const s = R.sealDraw('f', i, false);
  wins[R.roundWinner(i % 6, (i + 1 + (i % 5)) % 6, s.value)]++;
}
check('chaque joueur gagne ~43 % des manches normales', Math.abs(wins[1] / 36000 - 13 / 30) < 0.012 && Math.abs(wins[2] / 36000 - 13 / 30) < 0.012, wins);

console.log('Arrêt de la roue');
// Le suspens (2026-11-05) : parfois juste après la ligne (« dernière ligne »),
// parfois juste avant la suivante, sinon au milieu — toujours franchement dans
// la case tirée, le style tiré du sel (le côté vers une couleur choisie voisine,
// plus bas), au milieu à égale distance.
let landingsOk = true, anglesOk = true, insideOk = true;
let lineSideOk = true;
/* Le sel en hexadécimal : octet 0 = la case (parmi celles de la couleur), octet 1 =
   l'endroit dans la case, octet 2 = le suspens. Les 256 valeurs de l'octet 2, les
   deux autres variés : des parts exactes, sans hasard dans le test. */
const ROLL_SALTS = Array.from({ length: 256 }, (_, i) => {
  const b = crypto.randomBytes(16);
  b[0] = (i * 37) & 255; b[1] = (i * 101 + 7) & 255; b[2] = i;
  return b.toString('hex');
});
const styles = { 'last-line': 0, 'near-next': 0, middle: 0 };
for (let drawn = 0; drawn < 6; drawn++) {
  for (const salt of ROLL_SALTS) styles[R.landingFor(R.wheelFor(false), drawn, salt, drawn, (drawn + 3) % 6).style]++;
}
for (let drawn = 0; drawn < 6; drawn++) {
  for (let k = 0; k < 400; k++) {
    const salt = crypto.randomBytes(16).toString('hex');
    // Des couleurs qui ne donnent jamais une égalité : celle tirée contre une autre.
    for (const decisive of [false, true]) {
      const wheel = R.wheelFor(decisive, drawn, (drawn + 3) % 6);
      const landing = R.landingFor(wheel, drawn, salt, drawn, (drawn + 3) % 6, decisive);
      if (wheel[landing.segment] !== drawn) landingsOk = false;
      if (Math.abs(landing.offset) > 0.88 + 1e-9) insideOk = false;
      if (landing.style === 'last-line' && !(landing.offset >= 0.78 && landing.offset <= 0.881)) lineSideOk = false;
      if (landing.style === 'near-next' && !(landing.offset <= -0.78 && landing.offset >= -0.881)) lineSideOk = false;
      if (landing.style === 'middle' && Math.abs(landing.offset) > 0.45 + 1e-9) lineSideOk = false;
      const angle = R.landingAngle(wheel.length, landing);
      // La case sous le pointeur (en haut) une fois la roue tournée de `angle`.
      const seg = 360 / wheel.length;
      const under = Math.floor(((360 - angle) % 360) / seg);
      if (wheel[under] !== drawn || angle < 0 || angle >= 360) anglesOk = false;
    }
  }
}
const total = styles['last-line'] + styles['near-next'] + styles.middle;
check('la case d’arrêt est toujours de la couleur tirée', landingsOk);
check('toujours franchement dans la case (à 6 % au moins d’une ligne)', insideOk);
check('« dernière ligne » juste entrée, « juste avant la suivante » de l’autre côté, sinon au milieu', lineSideOk);
check(`le suspens selon le sel : 35 % dernière ligne, 20 % juste avant la suivante, 45 % au milieu (${styles['last-line']}/${styles['near-next']}/${styles.middle})`,
  Math.abs(styles['last-line'] / total - 0.35) < 0.01 && Math.abs(styles['near-next'] / total - 0.2) < 0.01 && Math.abs(styles.middle / total - 0.45) < 0.01, styles);
check('l’angle d’arrêt place cette case sous le pointeur', anglesOk);
check('même sel, même arrêt (identique sur tous les écrans)', JSON.stringify(R.landingFor(R.wheelFor(false), 3, 'a1b2c3', 3, 0)) === JSON.stringify(R.landingFor(R.wheelFor(false), 3, 'a1b2c3', 3, 0)));
// Rouge et Jaune, Orange tiré : à égale distance — jamais près d'une ligne (on croirait l'un plus près).
let tiesInMiddle = true;
for (let k = 0; k < 300; k++) {
  const landing = R.landingFor(R.wheelFor(false), 1, crypto.randomBytes(16).toString('hex'), 0, 2);
  if (landing.style !== 'middle' || Math.abs(landing.offset) > 0.45 + 1e-9) tiesInMiddle = false;
}
check('à égale distance, toujours au milieu de la case', tiesInMiddle);
// Le presque-arrêt va vers la couleur choisie voisine (owner : « ça va tomber sur une couleur que
// l'un a choisi mais ça n'arrive pas »). Sens de rotation : la case pick + 1 passe avant, puis pick − 1.
// Orange tiré (case 1) : Jaune (case 2) vient de passer, Rouge (case 0) arrive.
function sideStats(choice1, choice2, wheel = R.wheelFor(false), drawn = 1) {
  const out = { 'last-line': 0, 'near-next': 0, middle: 0 };
  for (const salt of ROLL_SALTS) out[R.landingFor(wheel, drawn, salt, choice1, choice2).style]++;
  return out;
}
const share = n => n / ROLL_SALTS.length;
const towardsPassed = sideStats(1, 2);   // Orange pile, Jaune voisin déjà passé
const towardsComing = sideStats(1, 0);   // Orange pile, Rouge voisin à venir
const awayBoth = sideStats(4, 2);        // Bleu (loin) et Jaune (voisin passé) : Jaune gagne
check(`une couleur choisie vient de passer : la roue traîne dessus puis franchit la ligne (${JSON.stringify(towardsPassed)})`,
  towardsPassed['near-next'] === 0 && Math.abs(share(towardsPassed['last-line']) - 0.55) < 0.01, towardsPassed);
check(`une couleur choisie arrive : la roue s’arrête juste avant elle (${JSON.stringify(towardsComing)})`,
  towardsComing['last-line'] === 0 && Math.abs(share(towardsComing['near-next']) - 0.55) < 0.01, towardsComing);
check('… même quand celle tirée n’est pas choisie (Bleu et Jaune, Orange tiré)', awayBoth['near-next'] === 0 && awayBoth['last-line'] > 0, awayBoth);
// Les choix ne décident que le côté : la part de suspens reste celle du sel.
check('les choix ne changent pas la part de suspens (55 %)', [towardsPassed, towardsComing, awayBoth].every(st => st.middle === styles.middle / 6));
// Manche décisive (« ça doit faire battre vite les cœurs ») : 80 % d'arrêts au ras d'une ligne —
// 50 % juste après, 30 % juste avant la suivante ; le côté va toujours vers une couleur choisie voisine.
const decisiveStats = (c1, c2, drawn = 1) => {
  const out = { 'last-line': 0, 'near-next': 0, middle: 0 };
  for (const salt of ROLL_SALTS) out[R.landingFor(R.wheelFor(true, c1, c2), drawn, salt, c1, c2, true).style]++;
  return out;
};
const decisiveFree = decisiveStats(1, 4);      // Orange pile, aucune voisine choisie
const decisivePassed = decisiveStats(1, 2);    // Jaune choisi, juste passé
check(`manche décisive : 80 % de suspens — 50 % dernière ligne, 30 % juste avant la suivante (${JSON.stringify(decisiveFree)})`,
  Math.abs(share(decisiveFree['last-line']) - 0.5) < 0.01 && Math.abs(share(decisiveFree['near-next']) - 0.3) < 0.01 && Math.abs(share(decisiveFree.middle) - 0.2) < 0.01, decisiveFree);
check(`manche décisive, une couleur choisie voisine : la roue traîne dessus (${JSON.stringify(decisivePassed)})`,
  decisivePassed['near-next'] === 0 && Math.abs(share(decisivePassed['last-line']) - 0.8) < 0.01, decisivePassed);
check('manche décisive à égale distance : toujours au milieu', decisiveStats(0, 2)['middle'] === ROLL_SALTS.length);
// La couleur tirée et la case d'arrêt ne dépendent jamais des choix.
let choicesNeverMove = true;
for (let k = 0; k < 500; k++) {
  const salt = crypto.randomBytes(16).toString('hex');
  const a = R.landingFor(R.wheelFor(false), 3, salt, 3, 0), b = R.landingFor(R.wheelFor(false), 3, salt, 2, 3);
  if (a.segment !== b.segment) choicesNeverMove = false;
}
check('les choix ne déplacent jamais la case d’arrêt (seulement l’endroit dans la case)', choicesNeverMove);
check('sans sel (un replay), au milieu', JSON.stringify(R.landingFor(R.wheelFor(false), 2, '')) === JSON.stringify({ segment: 2, offset: 0, style: 'middle' }));

console.log('Manche publique');
const pub = R.publicRound({ round: 2, choice1: 1, choice2: '4', drawn: 4, winnerSlot: 2, decisive: false, secret: 'x', salt: 'y' });
check('ne garde que les champs publics', JSON.stringify(pub) === JSON.stringify({ round: 2, choice1: 1, choice2: 4, drawn: 4, winnerSlot: 2, decisive: false, repick: false }));

console.log('Le même fichier dans un navigateur');
const source = fs.readFileSync(path.join(__dirname, '..', 'public', 'roulette-rules.js'), 'utf8');
const sandbox = { self: {} };
vm.runInNewContext(source, sandbox);
const browserRules = sandbox.self.RouletteRules;
check('window.RouletteRules exposé sans module', !!browserRules && browserRules.COLORS.length === 6);
check('mêmes réponses que le serveur', browserRules.roundWinner(2, 4, 4) === 2 && browserRules.roundWinner(0, 4, 3) === 2
  && browserRules.drawnColor({ kind: 'color', value: 1 }, 4, 1) === 1 && browserRules.REGULAR_ROUNDS === 6
  && JSON.stringify(browserRules.wheelFor(true, 4, 1)) === JSON.stringify([0, 1, 2, 3, 4, 5])
  && JSON.stringify(browserRules.matchDecision({ scores: [3, 4], decisive: true, decisivePlayed: 1 })) === JSON.stringify({ over: false, decisive: true }));

if (failures) {
  console.log(`\n${failures} échec(s)`);
  process.exit(1);
}
console.log('\nOK Roulette Royale : règles et tirage scellé');
