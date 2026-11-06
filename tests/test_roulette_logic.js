/**
 * Roulette Royale : les règles pures et le tirage scellé.
 *
 * Ce que ce test protège :
 *   • six couleurs, les mêmes pour les deux joueurs ;
 *   • les points d'une manche (règles du 2026-11-05, 3e version) : seule la
 *     couleur EXACTE marque — l'aiguille sur la couleur d'un joueur, +1 pour
 *     lui ; sur une couleur que personne n'a choisie, personne ; même couleur
 *     pour les deux, la manche se joue : l'aiguille dessus, 1 point chacun
 *     (une manche nulle) ;
 *   • l'issue scellée avant les choix (0–99) : la couleur du joueur 1 (0–39),
 *     celle du joueur 2 (40–79) ou une couleur libre (80–99, chacune à parts
 *     égales, qu'il y en ait quatre ou cinq) — pour toute paire de couleurs, la
 *     même chance pour les deux (40 % chacun), un gagnant 8 manches sur 10, et
 *     l'aiguille toujours sur la couleur désignée ;
 *   • la fin du match : six manches (les rechoix ne comptent pas), fin
 *     anticipée quand l'écart ne peut plus être comblé, puis à égalité les
 *     manches 7 et 8, 9 et 10… DEUX PAR DEUX jusqu'à ce qu'un joueur gagne :
 *     rien ne se décide après la première d'une paire ; une paire à 1-0 (une
 *     manche nulle) décide, à 1-1 ou 0-0 elle en appelle une autre ;
 *   • la manche décisive garde la roue entière (six couleurs) et ses règles :
 *     la couleur exacte marque, la même couleur se joue ; son tirage est une
 *     issue scellée, comme les autres ;
 *   • le tirage est uniforme, scellé avant les choix, vérifiable, et toute
 *     retouche de la valeur ou du sel se voit ; un ancien sceau (« color »,
 *     « bit ») n'a plus cours ;
 *   • la roue s'arrête sur la couleur tirée, au même endroit partout —
 *     parfois juste après la ligne ou juste avant la suivante (le suspens :
 *     sa part tirée du sel, son côté vers une couleur choisie voisine), y
 *     compris dans une manche où personne ne marque ;
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

console.log('Gagnant d’une manche : la couleur exacte');
check('distance sur la roue (affichage), par le plus court (0 à 3)', R.colorDistance(0, 0) === 0 && R.colorDistance(0, 1) === 1
  && R.colorDistance(0, 5) === 1 && R.colorDistance(1, 4) === 3 && R.colorDistance(5, 2) === 3 && R.colorDistance(4, 0) === 2
  && R.colorDistance(0, 9) === null);
check('pile sur la couleur du joueur 1', R.roundWinner(2, 4, 2) === 1);
check('pile sur la couleur du joueur 2', R.roundWinner(2, 4, 4) === 2);
check('Vert tiré, Bleu et Rouge choisis : personne (« plus proche » ne compte plus)', R.roundWinner(0, 4, 3) === 0);
check('Violet tiré, Rouge et Jaune choisis : personne', R.roundWinner(0, 2, 5) === 0);
check('Orange tiré, Rouge et Jaune choisis : personne', R.roundWinner(0, 2, 1) === 0);
check('même couleur, l’aiguille dessus : 1 point chacun, une manche nulle', JSON.stringify(R.roundPoints(3, 3, 3)) === JSON.stringify([1, 1]) && R.roundWinner(3, 3, 3) === 0
  && R.sameColor(3, 3) && !R.sameColor(3, 4) && R.isRepick === undefined);
check('même couleur, l’aiguille ailleurs : personne', JSON.stringify(R.roundPoints(3, 3, 1)) === JSON.stringify([0, 0]) && R.roundWinner(3, 3, 1) === 0);
check('les points : 1 au seul joueur pile dessus', JSON.stringify(R.roundPoints(2, 4, 2)) === JSON.stringify([1, 0]) && JSON.stringify(R.roundPoints(2, 4, 4)) === JSON.stringify([0, 1])
  && JSON.stringify(R.roundPoints(2, 4, 0)) === JSON.stringify([0, 0]));
check('tirage invalide : nulle, aucun point', R.roundWinner(1, 2, null) === 0 && R.roundWinner(1, 2, 9) === 0 && JSON.stringify(R.roundPoints(1, 2, null)) === JSON.stringify([0, 0]));

console.log('L’issue scellée : la couleur désignée, où l’aiguille s’arrête');
check('issues : 0–39 la couleur du joueur 1, 40–79 celle du joueur 2, 80–99 une couleur libre', R.OUTCOME_SPACE === 100
  && [0, 39].every(v => R.outcomeWinner(v) === 1) && [40, 79].every(v => R.outcomeWinner(v) === 2) && [80, 99].every(v => R.outcomeWinner(v) === 0));
check('issue invalide : rien', [100, -1, 2.5, '3', null].every(v => R.outcomeWinner(v) === 0 && !R.isOutcome(v)) && R.isOutcome(0) && R.isOutcome(99));
check('les couleurs libres : les quatre autres, dans l’ordre de la roue ; cinq pour une même couleur', JSON.stringify(R.unchosenColors(4, 1)) === JSON.stringify([0, 2, 3, 5])
  && JSON.stringify(R.unchosenColors(2, 2)) === JSON.stringify([0, 1, 3, 4, 5]));
const out = v => ({ kind: 'outcome', value: v });
check('issue du joueur 1 : l’aiguille sur SA couleur', R.drawnColor(out(3), 4, 1) === 4 && R.drawnColor(out(39), 4, 1) === 4);
check('issue du joueur 2 : l’aiguille sur SA couleur', R.drawnColor(out(40), 4, 1) === 1 && R.drawnColor(out(79), 4, 1) === 1);
check('issue « couleur libre » : 80 → la 1re, 83 → la 4e, 84 → la 1re de nouveau', R.drawnColor(out(80), 4, 1) === 0 && R.drawnColor(out(81), 4, 1) === 2
  && R.drawnColor(out(82), 4, 1) === 3 && R.drawnColor(out(83), 4, 1) === 5 && R.drawnColor(out(84), 4, 1) === 0);
check('même couleur : l’issue d’un joueur désigne leur couleur commune', R.drawnColor(out(3), 2, 2) === 2 && R.drawnColor(out(55), 2, 2) === 2);
check('même couleur, issue « couleur libre » : une des cinq autres', R.drawnColor(out(80), 2, 2) === 0 && R.drawnColor(out(84), 2, 2) === 5 && R.drawnColor(out(85), 2, 2) === 0);
check('un choix manquant : rien', R.drawnColor(out(3), 2, null) === null && R.drawnColor(out(3), undefined, 1) === null);
check('un ancien sceau « color » (une couleur tirée sans regarder les choix) n’a plus cours', R.drawnColor({ kind: 'color', value: 5 }, 0, 1) === null);
check('un ancien sceau « bit » (roue à deux couleurs) n’a plus cours', R.drawnColor({ kind: 'bit', value: 1 }, 4, 1) === null);
check('une issue hors limites : rien', R.drawnColor(out(100), 4, 1) === null && R.drawnColor(out(-1), 4, 1) === null);

// L'équité, pour TOUTE paire de couleurs et TOUTE issue : l'aiguille tombe
// exactement sur la couleur désignée (jamais sur une couleur choisie quand
// personne ne marque) ; deux couleurs différentes : 40 issues sur 100 pour
// chacun, 20 pour personne, chacune des quatre couleurs libres 5 fois ; la
// même couleur : 80 issues sur 100 donnent 1 point à chacun, 20 aucune,
// chacune des cinq couleurs libres 4 fois.
let exactOk = true, fairOk = true, freeOk = true, sameOk = true;
for (let a = 0; a < 6; a++) for (let b = 0; b < 6; b++) {
  const won = [0, 0, 0], both = { yes: 0, no: 0 }, free = new Map();
  for (let v = 0; v < 100; v++) {
    const drawn = R.drawnColor(out(v), a, b);
    const points = R.roundPoints(a, b, drawn);
    if (!R.isColor(drawn)) { exactOk = false; continue; }
    if (R.outcomeWinner(v) === 1 && points[0] !== 1) exactOk = false;
    if (R.outcomeWinner(v) === 2 && points[1] !== 1) exactOk = false;
    if (R.outcomeWinner(v) === 0) {
      if (drawn === a || drawn === b) exactOk = false;
      free.set(drawn, (free.get(drawn) || 0) + 1);
    }
    if (a === b) (points[0] && points[1] ? both.yes++ : both.no++);
    else won[R.roundWinner(a, b, drawn)]++;
  }
  const shares = [...free.values()];
  if (a === b) {
    if (both.yes !== 80 || both.no !== 20) sameOk = false;
    if (free.size !== 5 || !shares.every(n => n === 4)) freeOk = false;
  } else {
    if (won[1] !== 40 || won[2] !== 40 || won[0] !== 20) fairOk = false;
    if (free.size !== 4 || !shares.every(n => n === 5)) freeOk = false;
  }
}
check('l’aiguille tombe exactement sur la couleur désignée', exactOk);
check('deux couleurs différentes : 40 issues sur 100 pour chacun, 20 pour personne', fairOk);
check('la même couleur : 80 issues sur 100 donnent 1 point à chacun, 20 aucune', sameOk);
check('une couleur libre : chacune à parts égales (5 issues sur 4 couleurs, 4 sur 5)', freeOk);

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
check('toute manche : l’issue scellée', R.drawnColor(out(52), 0, 1) === 1 && R.drawnColor(out(2), 0, 1) === 0);
check('même couleur en manche décisive : elle se joue (1 point chacun si elle sort)', R.drawnColor(out(5), 2, 2) === 2 && JSON.stringify(R.roundPoints(2, 2, 2)) === JSON.stringify([1, 1]));
check('manche décisive sur une couleur libre : nulle, comme les autres', R.roundWinner(0, 2, R.drawnColor(out(80), 0, 2)) === 0);

console.log('Tirage scellé');
const seal = R.sealDraw('room-x', 3, false);
check('issue 0..99, sel de 128 bits, empreinte SHA-256', seal.kind === 'outcome' && R.isOutcome(seal.value) && /^[0-9a-f]{32}$/.test(seal.salt) && /^[0-9a-f]{64}$/.test(seal.hash));
check('l’empreinte se vérifie', R.verifySeal('room-x', 3, seal));
check('une autre issue ne correspond plus', !R.verifySeal('room-x', 3, { ...seal, value: (seal.value + 1) % 100 }));
check('un autre sel ne correspond plus', !R.verifySeal('room-x', 3, { ...seal, salt: crypto.randomBytes(16).toString('hex') }));
check('une autre manche ne correspond plus', !R.verifySeal('room-x', 4, seal));
check('une autre partie ne correspond plus', !R.verifySeal('room-y', 3, seal));
check('l’empreinte = SHA-256 du texte publié', crypto.createHash('sha256').update(R.sealText('room-x', 3, 'outcome', seal.value, seal.salt)).digest('hex') === seal.hash);
const decisiveSeal = R.sealDraw('room-x', 7, true);
check('scellé décisif : une issue, comme les autres', decisiveSeal.kind === 'outcome' && R.isOutcome(decisiveSeal.value) && R.verifySeal('room-x', 7, decisiveSeal));
const oldSalt = crypto.randomBytes(16).toString('hex');
const oldBit = { kind: 'bit', value: 1, salt: oldSalt, hash: R.hashSeal('room-x', 7, 'bit', 1, oldSalt) };
check('un ancien sceau « bit » relu après une mise à jour : la manche se rejoue (null)', R.sanitizeSeal('room-x', 7, oldBit) === null && !R.verifySeal('room-x', 7, oldBit));
const oldColor = { kind: 'color', value: 4, salt: oldSalt, hash: R.hashSeal('room-x', 3, 'color', 4, oldSalt) };
check('un ancien sceau « color » relu après une mise à jour : la manche se rejoue (null)', R.sanitizeSeal('room-x', 3, oldColor) === null && !R.verifySeal('room-x', 3, oldColor));
check('sanitizeSeal garde un sceau intact', JSON.stringify(R.sanitizeSeal('room-x', 3, seal)) === JSON.stringify(seal));
check('sanitizeSeal refuse un sceau retouché', R.sanitizeSeal('room-x', 3, { ...seal, value: (seal.value + 2) % 100 }) === null);

// Uniformité : 60 000 tirages, khi-deux à 99 degrés de liberté (seuil 0,1 % : 148,23).
const N = 60000;
const chi2Of = list => list.reduce((sum, c) => sum + ((c - N / 100) ** 2) / (N / 100), 0);
const counts = new Array(100).fill(0);
for (let i = 0; i < N; i++) counts[R.sealDraw('u', i, false).value]++;
const chi2 = chi2Of(counts);
check(`tirage uniforme sur 60 000 (khi-deux ${chi2.toFixed(2)} < 148,23)`, chi2 < 148.23, counts);
const decisiveCounts = new Array(100).fill(0);
for (let i = 0; i < N; i++) decisiveCounts[R.sealDraw('u', i, true).value]++;
const chi2d = chi2Of(decisiveCounts);
check(`tirage décisif uniforme lui aussi (khi-deux ${chi2d.toFixed(2)} < 148,23)`, chi2d < 148.23, decisiveCounts);

// Équité, avec le vrai tirage : quelles que soient les deux couleurs choisies
// (différentes, tous les écarts), chaque joueur gagne 40 % des manches, et
// une manche a un gagnant 8 fois sur 10.
const wins = [0, 0, 0];
for (let i = 0; i < 36000; i++) {
  const s = R.sealDraw('f', i, false);
  const c1 = i % 6, c2 = (i + 1 + (i % 5)) % 6;
  wins[R.roundWinner(c1, c2, R.drawnColor(s, c1, c2))]++;
}
check(`chaque joueur gagne ~40 % des manches, personne ~20 % (${wins.join(' / ')})`,
  Math.abs(wins[1] / 36000 - 0.4) < 0.012 && Math.abs(wins[2] / 36000 - 0.4) < 0.012 && Math.abs(wins[0] / 36000 - 0.2) < 0.012, wins);
// La même couleur, avec le vrai tirage : 1 point chacun 8 fois sur 10.
let bothScored = 0;
for (let i = 0; i < 20000; i++) {
  const c = i % 6;
  const p = R.roundPoints(c, c, R.drawnColor(R.sealDraw('s', i, false), c, c));
  if (p[0] && p[1]) bothScored++;
}
check(`la même couleur sort ~80 % du temps : 1 point chacun (${(100 * bothScored / 20000).toFixed(1)} %)`, Math.abs(bothScored / 20000 - 0.8) < 0.015, bothScored);

console.log('Arrêt de la roue');
// Owner, 2026-11-06 : « l'aiguille arrive toujours dans cet espace-là… ça doit être de manière
// aléatoire, au milieu jusqu'à la fin, au début… parfois à des 1000 mm microscopiquement ». L'arrêt
// est tiré du sel n'importe où dans la case tirée : 'anywhere' (n'importe où), 'edge' (tout près
// d'une ligne), 'hair' (à un cheveu, moins d'un pixel) ; le côté va vers une couleur choisie
// voisine. La roue se recentre ensuite (roulette-board.js), et le résultat vient après.
/* Le sel en hexadécimal : caractères 2–5 = le genre d'arrêt, 6–11 = la distance, 12–13 = le côté,
   16 et suivants = le rythme du tour. Les 1 000 valeurs régulières du genre, le reste varié : des
   parts exactes, sans hasard dans le test. */
const STEPS = 1000;
const ROLL_SALTS = Array.from({ length: STEPS }, (_, i) => {
  const hex = crypto.randomBytes(16).toString('hex').split('');
  const roll = Math.floor((i + 0.5) / STEPS * 0xffff).toString(16).padStart(4, '0');
  const depth = Math.floor(((i * 7919) % STEPS + 0.5) / STEPS * 0xffffff).toString(16).padStart(6, '0');
  hex.splice(2, 4, ...roll);
  hex.splice(6, 6, ...depth);
  hex.splice(12, 2, ...((i * 37) % 256).toString(16).padStart(2, '0'));
  return hex.join('');
});
const HALF = 30;   // la demi-case, en degrés (six couleurs)
let landingsOk = true, anglesOk = true, neverOnLine = true, gapsOk = true, sameEverywhere = true;
const styles = { anywhere: 0, edge: 0, hair: 0 };
const dStyles = { anywhere: 0, edge: 0, hair: 0 };
const bins = new Array(10).fill(0);   // l'endroit dans la case, du début (la ligne qui vient de passer) à la fin
let closest = 1;
for (let drawn = 0; drawn < 6; drawn++) {
  for (const decisive of [false, true]) {
    const wheel = R.wheelFor(decisive, drawn, (drawn + 3) % 6);
    for (const salt of ROLL_SALTS) {
      // La couleur tirée contre celle d'en face : aucune voisine choisie, le côté vient du sel.
      const landing = R.landingFor(wheel, drawn, salt, drawn, (drawn + 3) % 6, decisive);
      (decisive ? dStyles : styles)[landing.style]++;
      if (wheel[landing.segment] !== drawn) landingsOk = false;
      const gap = 1 - Math.abs(landing.offset);
      if (!(gap > 0)) neverOnLine = false;
      closest = Math.min(closest, gap);
      if (landing.style === 'anywhere' && Math.abs(landing.offset) > 0.94 + 1e-9) gapsOk = false;
      if (landing.style === 'edge' && !(gap >= 0.01 - 1e-6 && gap <= 0.1 + 1e-6)) gapsOk = false;
      if (landing.style === 'hair' && !(gap >= 0.001 - 1e-6 && gap <= 0.01 + 1e-6)) gapsOk = false;
      if (!decisive) bins[Math.min(9, Math.floor((1 - landing.offset) / 2 * 10))]++;
      const angle = R.landingAngle(wheel.length, landing);
      // La case sous le pointeur (en haut) une fois la roue tournée de `angle`.
      const under = Math.floor(((360 - angle) % 360) / (360 / wheel.length));
      if (wheel[under] !== drawn || angle < 0 || angle >= 360) anglesOk = false;
      if (JSON.stringify(landing) !== JSON.stringify(R.landingFor(wheel, drawn, salt, drawn, (drawn + 3) % 6, decisive))) sameEverywhere = false;
    }
  }
}
const pct = (o, k) => Math.round(1000 * o[k] / (o.anywhere + o.edge + o.hair)) / 10;
check('la case d’arrêt est toujours de la couleur tirée', landingsOk);
check('l’angle d’arrêt place cette case sous le pointeur (au millième de degré près, même à un cheveu de la ligne)', anglesOk);
check(`jamais sur la ligne elle-même (au plus près : ${(closest * HALF).toFixed(3)}°)`, neverOnLine && closest >= 0.001 - 1e-6, closest);
check('n’importe où à 6 % au moins d’une ligne ; tout près : 1 à 10 % ; à un cheveu : 0,1 à 1 % de la demi-case', gapsOk);
check(`manche normale : 50 % n’importe où, 32 % tout près d’une ligne, 18 % à un cheveu (${pct(styles, 'anywhere')} / ${pct(styles, 'edge')} / ${pct(styles, 'hair')})`,
  Math.abs(pct(styles, 'anywhere') - 50) <= 0.2 && Math.abs(pct(styles, 'edge') - 32) <= 0.2 && Math.abs(pct(styles, 'hair') - 18) <= 0.2, styles);
check(`manche décisive : 30 % n’importe où, 40 % tout près, 30 % à un cheveu (${pct(dStyles, 'anywhere')} / ${pct(dStyles, 'edge')} / ${pct(dStyles, 'hair')})`,
  Math.abs(pct(dStyles, 'anywhere') - 30) <= 0.2 && Math.abs(pct(dStyles, 'edge') - 40) <= 0.2 && Math.abs(pct(dStyles, 'hair') - 30) <= 0.2, dStyles);
// Du début à la fin de la couleur : chaque dixième de la case reçoit des arrêts, les bords bien plus que le reste.
check(`du début à la fin de la couleur : chaque dixième de la case a ses arrêts (${bins.join(' ')})`, bins.every(n => n >= STEPS * 6 * 0.025), bins);
check('les bords de la case (les dixièmes contre les lignes) en ont plus que le milieu', bins[0] > bins[4] * 2 && bins[9] > bins[5] * 2, bins);
check('même sel, même arrêt (identique sur tous les écrans)', sameEverywhere);
// Un arrêt à un cheveu, c'est moins d'un pixel au bord d'une roue de 330 px de large.
const hairPx = (0.01 * HALF) * Math.PI / 180 * 165;
check(`« à un cheveu » : moins d’un pixel au bord d’une roue de 330 px (${hairPx.toFixed(2)} px au plus)`, hairPx < 1, hairPx);
// Le presque-arrêt va vers la couleur choisie voisine (owner : « ça peut tomber sur la couleur qu'un
// joueur a choisi, mais la roue glisse tellement que ça finit par dévier et aller dans une autre
// couleur »). Sens de rotation : la case pick + 1 passe avant, puis pick − 1. Orange tiré (case 1) :
// Jaune (case 2) vient de passer, Rouge (case 0) arrive.
function sideStats(choice1, choice2, drawn = 1, decisive = false) {
  const out = { plus: 0, minus: 0, anywhere: 0 };
  for (const salt of ROLL_SALTS) {
    const l = R.landingFor(R.wheelFor(decisive, choice1, choice2), drawn, salt, choice1, choice2, decisive);
    if (l.style === 'anywhere') out.anywhere++;
    else if (l.offset > 0) out.plus++;
    else out.minus++;
  }
  return out;
}
const towardsPassed = sideStats(1, 2);   // Orange pile, Jaune voisin déjà passé
const towardsComing = sideStats(1, 0);   // Orange pile, Rouge voisin à venir
const awayBoth = sideStats(4, 2);        // Bleu (loin) et Jaune (voisin passé) : personne ne marque
const freeComing = sideStats(2, 5, 3);   // Vert libre tiré : Jaune (case 2) arrive
const noNeighbour = sideStats(1, 4);     // Orange pile, aucune voisine choisie
check(`une couleur choisie vient de passer : la roue a glissé hors d’elle, juste après la ligne (${JSON.stringify(towardsPassed)})`,
  towardsPassed.minus === 0 && towardsPassed.plus === STEPS / 2, towardsPassed);
check(`une couleur choisie arrive : la roue s’arrête juste avant elle (${JSON.stringify(towardsComing)})`,
  towardsComing.plus === 0 && towardsComing.minus === STEPS / 2, towardsComing);
check('… même quand personne ne marque (Bleu et Jaune choisis, Orange libre) : la roue a frôlé le Jaune', awayBoth.minus === 0 && awayBoth.plus > 0, awayBoth);
check('… ou s’arrête juste avant une couleur choisie qui arrive (Vert libre, Jaune choisi)', freeComing.plus === 0 && freeComing.minus > 0, freeComing);
check(`sans voisine choisie, le côté vient du sel : les deux côtés (${JSON.stringify(noNeighbour)})`, noNeighbour.plus > STEPS * 0.2 && noNeighbour.minus > STEPS * 0.2, noNeighbour);
check('les choix ne changent pas la part d’arrêts près d’une ligne (la moitié)', [towardsPassed, towardsComing, awayBoth, freeComing, noNeighbour].every(st => st.anywhere === STEPS / 2));
const dPassed = sideStats(1, 2, 1, true);
check(`manche décisive, une couleur choisie voisine : 70 % d’arrêts contre elle (${JSON.stringify(dPassed)})`, dPassed.minus === 0 && dPassed.plus === STEPS * 0.7, dPassed);
// La couleur tirée, la case d'arrêt, le genre d'arrêt et sa distance ne dépendent jamais des choix.
let choicesNeverMove = true;
for (let k = 0; k < 500; k++) {
  const salt = crypto.randomBytes(16).toString('hex');
  const a = R.landingFor(R.wheelFor(false), 3, salt, 3, 0), b = R.landingFor(R.wheelFor(false), 3, salt, 2, 3);
  if (a.segment !== b.segment || a.style !== b.style || Math.abs(a.offset) !== Math.abs(b.offset) || a.turns !== b.turns) choicesNeverMove = false;
}
check('les choix ne déplacent jamais la case, ni la distance à la ligne (seulement le côté)', choicesNeverMove);
check('sans sel (un replay), au milieu, le tour de toujours', JSON.stringify(R.landingFor(R.wheelFor(false), 2, ''))
  === JSON.stringify({ segment: 2, offset: 0, style: 'middle', turns: 9, ease: 2.8, cruise: 0.35 }));

console.log('Le rythme du tour');
// « Tu dois modifier le roulement parce que ça arrive toujours au même moment sur une couleur. »
let planOk = true, peaksOk = true;
const scales = [], turnsSeen = new Set(), crawlAt = [];
let minPeak = Infinity, maxPeak = 0;
for (let k = 0; k < 4000; k++) {
  const salt = crypto.randomBytes(16).toString('hex');
  for (const decisive of [false, true]) {
    const plan = R.spinPlan(salt, decisive);
    if (!(plan.scale >= 0.9 && plan.scale <= 1.12 && plan.ease >= 2.4 && plan.ease <= 3.4 && plan.cruise >= 0.3 && plan.cruise <= 0.4 && plan.turns >= 7 && plan.turns <= 12)) planOk = false;
    const seconds = (decisive ? R.SPIN_DECISIVE_NOMINAL_MS : R.SPIN_NOMINAL_MS) * plan.scale / 1000;
    // La vitesse de pointe, pour le chemin le plus court et le plus long vers la case (0 à 360° de plus).
    const area = R.motionArea(plan.ease, plan.cruise);
    const low = plan.turns * 360 / seconds / area, high = (plan.turns * 360 + 360) / seconds / area;
    minPeak = Math.min(minPeak, low); maxPeak = Math.max(maxPeak, high);
    if (low < 1000 || high > 1900) peaksOk = false;
    if (!decisive) {
      scales.push(plan.scale);
      turnsSeen.add(plan.turns);
      // L'instant où la roue passe sous 10 % de sa pleine vitesse : le début de la fin au ralenti.
      const curve = R.motionCurve(plan.ease, plan.cruise);
      let u = plan.cruise;
      while (u < 1 && curve.speed(u) > 0.1) u += 0.002;
      crawlAt.push(u * seconds);
    }
  }
}
const spread = a => Math.max(...a) - Math.min(...a);
check('une durée de 0,90 à 1,12 fois la nominale, un freinage de 2,4 à 3,4, la pleine vitesse jusqu’à 0,30–0,40, 7 à 12 tours', planOk);
check(`la vitesse se voit toujours : pointe entre 1 000 et 1 900 °/s (${Math.round(minPeak)} à ${Math.round(maxPeak)})`, peaksOk);
check(`l’arrêt ne tombe jamais au même instant : de ${(Math.min(...scales) * 7.2).toFixed(1)} à ${(Math.max(...scales) * 7.2).toFixed(1)} s (écart ${(spread(scales) * 7.2).toFixed(2)} s)`, spread(scales) * 7.2 > 1.4, spread(scales));
check(`la fin au ralenti commence tantôt tôt, tantôt tard (de ${Math.min(...crawlAt).toFixed(1)} à ${Math.max(...crawlAt).toFixed(1)} s)`, spread(crawlAt) > 1.2, spread(crawlAt));
check(`le nombre de tours change (${[...turnsSeen].sort((a, b) => a - b).join(', ')})`, turnsSeen.size >= 4, [...turnsSeen]);
const salt0 = crypto.randomBytes(16).toString('hex');
check('même sel, même rythme (identique sur tous les écrans)', JSON.stringify(R.spinPlan(salt0, false)) === JSON.stringify(R.spinPlan(salt0, false)));
check('le rythme voyage avec l’arrêt', (() => { const l = R.landingFor(R.wheelFor(false), 2, salt0, 2, 5), p = R.spinPlan(salt0, false); return l.turns === p.turns && l.ease === p.ease && l.cruise === p.cruise; })());
const curve = R.motionCurve(2.8, 0.35);
let monotone = true;
for (let u = 0; u < 1; u += 0.001) if (curve.progress(u + 0.001) < curve.progress(u) - 1e-12) monotone = false;
check('le mouvement : de 0 à 1, toujours en avant, vitesse nulle au départ et à l’arrêt, pleine au milieu',
  curve.progress(0) === 0 && curve.progress(1) === 1 && monotone && curve.speed(0.01) === 0 && curve.speed(1) === 0 && curve.speed(0.3) === 1);
check('la surface sous la vitesse : la table et le calcul exact s’accordent', Math.abs(curve.area - R.motionArea(2.8, 0.35)) < 1e-4, [curve.area, R.motionArea(2.8, 0.35)]);
check('un rythme hors des bornes retombe sur le tour de toujours', R.motionCurve('x', 9).ease === 2.8 && R.motionCurve(NaN, 0.1).cruise === 0.35);
check('après l’arrêt : un instant immobile puis le recentrage, 1,8 s en tout, avant le résultat', R.SPIN_SETTLE_MS === 1800);

console.log('Manche publique');
const pub = R.publicRound({ round: 2, choice1: 1, choice2: '4', drawn: 4, winnerSlot: 2, decisive: false, secret: 'x', salt: 'y' });
check('ne garde que les champs publics', JSON.stringify(pub) === JSON.stringify({ round: 2, choice1: 1, choice2: 4, drawn: 4, winnerSlot: 2, decisive: false, repick: false }));

console.log('Le même fichier dans un navigateur');
const source = fs.readFileSync(path.join(__dirname, '..', 'public', 'roulette-rules.js'), 'utf8');
const sandbox = { self: {} };
vm.runInNewContext(source, sandbox);
const browserRules = sandbox.self.RouletteRules;
check('window.RouletteRules exposé sans module', !!browserRules && browserRules.COLORS.length === 6);
check('mêmes réponses que le serveur', browserRules.roundWinner(2, 4, 4) === 2 && browserRules.roundWinner(0, 4, 3) === 0
  && browserRules.drawnColor({ kind: 'outcome', value: 45 }, 4, 1) === 1 && browserRules.drawnColor({ kind: 'outcome', value: 83 }, 4, 1) === 5
  && browserRules.drawnColor({ kind: 'outcome', value: 10 }, 3, 3) === 3 && JSON.stringify(browserRules.roundPoints(3, 3, 3)) === JSON.stringify([1, 1])
  && browserRules.drawnColor({ kind: 'color', value: 1 }, 4, 1) === null && browserRules.REGULAR_ROUNDS === 6
  && JSON.stringify(browserRules.wheelFor(true, 4, 1)) === JSON.stringify([0, 1, 2, 3, 4, 5])
  && JSON.stringify(browserRules.matchDecision({ scores: [3, 4], decisive: true, decisivePlayed: 1 })) === JSON.stringify({ over: false, decisive: true }));

if (failures) {
  console.log(`\n${failures} échec(s)`);
  process.exit(1);
}
console.log('\nOK Roulette Royale : règles et tirage scellé');
