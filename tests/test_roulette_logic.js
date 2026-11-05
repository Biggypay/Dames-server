/**
 * Roulette Royale : les règles pures et le tirage scellé.
 *
 * Ce que ce test protège :
 *   • six couleurs, les mêmes pour les deux joueurs ;
 *   • le gagnant d'une manche : un seul joueur a la couleur tirée ;
 *     personne, ou les deux → manche nulle ;
 *   • la fin du match : cinq manches, fin anticipée quand l'écart ne peut
 *     plus être comblé, manche décisive à égalité ;
 *   • la manche décisive ne garde que les deux couleurs choisies (une chance
 *     sur deux), et se rejoue si les deux ont choisi la même ;
 *   • le tirage est uniforme, scellé avant les choix, vérifiable, et toute
 *     retouche de la valeur ou du sel se voit ;
 *   • la roue s'arrête sur la couleur tirée, au même endroit partout ;
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
check('cinq manches prévues', R.REGULAR_ROUNDS === 5);
check('toColor accepte 0..5 et « 3 », refuse le reste',
  R.toColor(0) === 0 && R.toColor('3') === 3 && R.toColor(6) === null && R.toColor(-1) === null
  && R.toColor(2.5) === null && R.toColor('rouge') === null && R.toColor(null) === null && R.toColor('12') === null);

console.log('Gagnant d’une manche');
check('seul le joueur 1 a la couleur', R.roundWinner(2, 4, 2) === 1);
check('seul le joueur 2 a la couleur', R.roundWinner(2, 4, 4) === 2);
check('personne ne l’a : manche nulle', R.roundWinner(2, 4, 0) === 0);
check('les deux l’ont : manche nulle', R.roundWinner(3, 3, 3) === 0);
check('même couleur non tirée : nulle', R.roundWinner(3, 3, 1) === 0);
check('tirage invalide : nulle', R.roundWinner(1, 2, null) === 0 && R.roundWinner(1, 2, 9) === 0);

console.log('Suite du match');
const go = (scores, roundsPlayed, extra) => R.matchDecision({ scores, roundsPlayed, totalRounds: 5, ...extra });
check('0-0 après 1 manche : on continue', JSON.stringify(go([0, 0], 1)) === JSON.stringify({ over: false, decisive: false }));
check('3-0 après 3 manches : fin anticipée (2 restantes)', JSON.stringify(go([3, 0], 3)) === JSON.stringify({ over: true, winnerSlot: 1 }));
check('2-0 après 3 manches : encore rattrapable', go([2, 0], 3).over === false);
check('0-2 après 4 manches : fin anticipée pour le 2', JSON.stringify(go([0, 2], 4)) === JSON.stringify({ over: true, winnerSlot: 2 }));
check('1-0 après 4 manches : rattrapable (1 restante)', go([1, 0], 4).over === false);
check('2-1 après 5 manches : le 1 gagne', JSON.stringify(go([2, 1], 5)) === JSON.stringify({ over: true, winnerSlot: 1 }));
check('1-1 après 5 manches : manche décisive', JSON.stringify(go([1, 1], 5)) === JSON.stringify({ over: false, decisive: true }));
check('0-0 après 5 manches : manche décisive', go([0, 0], 5).decisive === true);
check('décisive gagnée par le 2 : fin', JSON.stringify(R.matchDecision({ scores: [1, 2], decisive: true, lastWinner: 2 })) === JSON.stringify({ over: true, winnerSlot: 2 }));
check('décisive rejouée (même couleur) : on continue', JSON.stringify(R.matchDecision({ scores: [1, 1], decisive: true, lastWinner: 0 })) === JSON.stringify({ over: false, decisive: true }));

console.log('Manche décisive : deux couleurs');
check('la roue garde les deux couleurs, alternées', JSON.stringify(R.wheelFor(true, 4, 1)) === JSON.stringify([1, 4, 1, 4, 1, 4]));
check('manche normale : les six couleurs', JSON.stringify(R.wheelFor(false, 4, 1)) === JSON.stringify([0, 1, 2, 3, 4, 5]));
check('décisive, bit 0 : la plus petite couleur', R.drawnColor({ kind: 'bit', value: 0 }, 4, 1) === 1);
check('décisive, bit 1 : la plus grande couleur', R.drawnColor({ kind: 'bit', value: 1 }, 4, 1) === 4);
check('décisive, même couleur : on rechoisit (null)', R.drawnColor({ kind: 'bit', value: 1 }, 3, 3) === null);
check('manche normale : la couleur scellée', R.drawnColor({ kind: 'color', value: 5 }, 0, 1) === 5);
check('décisive : toujours un vainqueur quand les couleurs diffèrent', [0, 1].every(bit => {
  for (let a = 0; a < 6; a++) for (let b = 0; b < 6; b++) {
    if (a === b) continue;
    const d = R.drawnColor({ kind: 'bit', value: bit }, a, b);
    if (R.roundWinner(a, b, d) === 0) return false;
  }
  return true;
}));

console.log('Tirage scellé');
const seal = R.sealDraw('room-x', 3, false);
check('valeur 0..5, sel de 128 bits, empreinte SHA-256', R.isColor(seal.value) && /^[0-9a-f]{32}$/.test(seal.salt) && /^[0-9a-f]{64}$/.test(seal.hash));
check('l’empreinte se vérifie', R.verifySeal('room-x', 3, seal));
check('une autre couleur ne correspond plus', !R.verifySeal('room-x', 3, { ...seal, value: (seal.value + 1) % 6 }));
check('un autre sel ne correspond plus', !R.verifySeal('room-x', 3, { ...seal, salt: crypto.randomBytes(16).toString('hex') }));
check('une autre manche ne correspond plus', !R.verifySeal('room-x', 4, seal));
check('une autre partie ne correspond plus', !R.verifySeal('room-y', 3, seal));
check('l’empreinte = SHA-256 du texte publié', crypto.createHash('sha256').update(R.sealText('room-x', 3, 'color', seal.value, seal.salt)).digest('hex') === seal.hash);
const decisiveSeal = R.sealDraw('room-x', 6, true);
check('scellé décisif : un bit', decisiveSeal.kind === 'bit' && (decisiveSeal.value === 0 || decisiveSeal.value === 1) && R.verifySeal('room-x', 6, decisiveSeal));
check('sanitizeSeal garde un sceau intact', JSON.stringify(R.sanitizeSeal('room-x', 3, seal)) === JSON.stringify(seal));
check('sanitizeSeal refuse un sceau retouché', R.sanitizeSeal('room-x', 3, { ...seal, value: (seal.value + 2) % 6 }) === null);

// Uniformité : 60 000 tirages, khi-deux à 5 degrés de liberté (seuil 0,1 % : 20,52).
const N = 60000;
const counts = [0, 0, 0, 0, 0, 0];
for (let i = 0; i < N; i++) counts[R.sealDraw('u', i, false).value]++;
const expected = N / 6;
const chi2 = counts.reduce((sum, c) => sum + ((c - expected) ** 2) / expected, 0);
check(`tirage uniforme sur 60 000 (khi-deux ${chi2.toFixed(2)} < 20,52)`, chi2 < 20.52, counts);
const bits = [0, 0];
for (let i = 0; i < 20000; i++) bits[R.sealDraw('u', i, true).value]++;
check('bit décisif équilibré (49–51 %)', bits[0] / 20000 > 0.49 && bits[0] / 20000 < 0.51, bits);

// Équité : quelles que soient les deux couleurs choisies (différentes), chaque
// joueur gagne une manche normale avec la même probabilité, 1/6.
const wins = [0, 0, 0];
for (let i = 0; i < 36000; i++) {
  const s = R.sealDraw('f', i, false);
  wins[R.roundWinner(i % 6, (i + 1 + (i % 5)) % 6, s.value)]++;
}
check('chaque joueur gagne ~1/6 des manches normales', Math.abs(wins[1] / 36000 - 1 / 6) < 0.012 && Math.abs(wins[2] / 36000 - 1 / 6) < 0.012, wins);

console.log('Arrêt de la roue');
let landingsOk = true, anglesOk = true;
for (let drawn = 0; drawn < 6; drawn++) {
  for (let k = 0; k < 40; k++) {
    const salt = crypto.randomBytes(16).toString('hex');
    for (const wheel of [R.wheelFor(false), R.wheelFor(true, drawn, (drawn + 2) % 6)]) {
      const landing = R.landingFor(wheel, drawn, salt);
      if (wheel[landing.segment] !== drawn || Math.abs(landing.offset) > 0.3) landingsOk = false;
      const angle = R.landingAngle(wheel.length, landing);
      // La case sous le pointeur (en haut) une fois la roue tournée de `angle`.
      const seg = 360 / wheel.length;
      const under = Math.floor(((360 - angle) % 360) / seg);
      if (wheel[under] !== drawn || angle < 0 || angle >= 360) anglesOk = false;
    }
  }
}
check('la case d’arrêt est toujours de la couleur tirée, loin des bords', landingsOk);
check('l’angle d’arrêt place cette case sous le pointeur', anglesOk);
check('même sel, même arrêt (identique sur tous les écrans)', JSON.stringify(R.landingFor(R.wheelFor(false), 3, 'a1b2c3')) === JSON.stringify(R.landingFor(R.wheelFor(false), 3, 'a1b2c3')));

console.log('Manche publique');
const pub = R.publicRound({ round: 2, choice1: 1, choice2: '4', drawn: 4, winnerSlot: 2, decisive: false, secret: 'x', salt: 'y' });
check('ne garde que les champs publics', JSON.stringify(pub) === JSON.stringify({ round: 2, choice1: 1, choice2: 4, drawn: 4, winnerSlot: 2, decisive: false, repick: false }));

console.log('Le même fichier dans un navigateur');
const source = fs.readFileSync(path.join(__dirname, '..', 'public', 'roulette-rules.js'), 'utf8');
const sandbox = { self: {} };
vm.runInNewContext(source, sandbox);
const browserRules = sandbox.self.RouletteRules;
check('window.RouletteRules exposé sans module', !!browserRules && browserRules.COLORS.length === 6);
check('mêmes réponses que le serveur', browserRules.roundWinner(2, 4, 4) === 2 && browserRules.drawnColor({ kind: 'bit', value: 1 }, 4, 1) === 4);

if (failures) {
  console.log(`\n${failures} échec(s)`);
  process.exit(1);
}
console.log('\nOK Roulette Royale : règles et tirage scellé');
