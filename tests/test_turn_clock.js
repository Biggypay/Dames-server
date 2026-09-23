'use strict';

// Chronomètre par coup (lib/turn-clock.js) : 30 s pour jouer, 60 s de grâce,
// puis la défaite — un seul budget par tour, que rien ne recharge.
//
// Ce que ces tests verrouillent, c'est ce qu'un joueur pourrait tenter pour
// gagner du temps : recharger la page (le tour reprend où il en était),
// s'absenter (le temps court), redémarrer le serveur (le temps consommé
// voyage avec la partie sauvegardée).

const Clock = require('../lib/turn-clock.js');

let failures = 0;
function check(label, cond, detail) {
  if (cond) console.log('  ✅ ' + label);
  else {
    failures++;
    console.log('  ❌ ' + label + (detail !== undefined ? ' → ' + JSON.stringify(detail) : ''));
  }
}

const T = 30000, G = 60000;
const at = seconds => 1_000_000 + seconds * 1000;

console.log('— Un tour : 30 s, puis 60 s de grâce, puis la défaite —');
{
  const c = Clock.create('v3', at(0), T, G);
  check('au départ : phase de jeu', Clock.phase(c, at(0)) === 'turn');
  check('à 29 s : toujours la phase de jeu', Clock.phase(c, at(29)) === 'turn');
  check('à 30 s : la grâce commence', Clock.phase(c, at(30)) === 'grace');
  check('à 89 s : encore la grâce', Clock.phase(c, at(89)) === 'grace');
  check('à 90 s : défaite', Clock.phase(c, at(90)) === 'expired');
  check('prochaine échéance depuis 10 s : fin des 30 s', Clock.msUntilNextPhase(c, at(10)) === 20000);
  check('prochaine échéance depuis 40 s : la défaite', Clock.msUntilNextPhase(c, at(40)) === 50000);
  check('temps restant à 40 s : 50 s', Clock.remainingMs(c, at(40)) === 50000);
  check('temps restant après l échéance : 0, jamais négatif', Clock.remainingMs(c, at(200)) === 0);
}

console.log('— Recharger la page ne rend pas le temps —');
{
  const c = Clock.create('v3', at(0), T, G);
  Clock.freeze(c, at(80));           // déconnexion à 80 s
  Clock.run(c, at(80));               // retour immédiat
  check('le tour repris garde ses 80 s consommées', Clock.usedMs(c, at(80)) === 80000);
  check('il ne lui reste que 10 s', Clock.remainingMs(c, at(80)) === 10000);
  check('et il perd à 90 s, pas à 170 s', Clock.phase(c, at(90)) === 'expired');
  const starts = Clock.phaseStarts(c, at(80));
  check('la page affiche la grâce entamée depuis 50 s', starts.graceStartTime === at(30), starts);
  check('et le tour commencé il y a 80 s', starts.turnStartTime === at(0), starts);
}

console.log('— Gelé seulement quand il ne peut pas jouer —');
{
  const c = Clock.create('v3', at(0), T, G);
  Clock.freeze(c, at(20));            // l'adversaire se déconnecte : pause
  check('gelé : 40 s de pause ne coûtent rien', Clock.usedMs(c, at(60)) === 20000);
  Clock.run(c, at(60));               // l'adversaire revient
  check('la reprise repart de 20 s consommées', Clock.usedMs(c, at(65)) === 25000);
  check('run() sur une horloge qui tourne ne rend rien', Clock.usedMs(Clock.run(c, at(70)), at(70)) === 30000);
  Clock.freeze(c, at(70));
  Clock.freeze(c, at(99));
  check('freeze() deux fois de suite ne facture rien de plus', Clock.usedMs(c, at(120)) === 30000);
}

console.log('— Redémarrage du serveur : le temps consommé voyage avec la partie —');
{
  const c = Clock.create('r12', at(0), T, G);
  const saved = JSON.parse(JSON.stringify(Clock.forSave(c, at(45))));
  check('la sauvegarde porte 45 s consommées, horloge à l arrêt', saved.usedMs === 45000 && saved.runningSince === null, saved);
  check('la sauvegarde ne modifie pas l horloge vivante', c.runningSince === at(0));
  const back = Clock.sanitize(saved);
  check('relue, elle reprend avec ses 45 s', back && Clock.usedMs(back, at(500)) === 45000, back);
  Clock.run(back, at(500));
  check('et tombe 45 s plus tard', Clock.phase(back, at(545)) === 'expired');
  check('la clé du tour est conservée', back.key === 'r12');
  check('forSave(null) : rien à sauvegarder', Clock.forSave(null, at(0)) === null);
}

console.log('— Une sauvegarde abîmée ne donne jamais de temps —');
{
  check('rien', Clock.sanitize(null) === null);
  check('pas de clé', Clock.sanitize({ turnMs: T, graceMs: G, usedMs: 0 }) === null);
  check('durées négatives', Clock.sanitize({ key: 'v1', turnMs: -5, graceMs: G, usedMs: 0 }) === null);
  check('temps consommé négatif', Clock.sanitize({ key: 'v1', turnMs: T, graceMs: G, usedMs: -9000 }) === null);
  check('temps consommé non numérique', Clock.sanitize({ key: 'v1', turnMs: T, graceMs: G, usedMs: 'beaucoup' }) === null);
  check('budget nul', Clock.sanitize({ key: 'v1', turnMs: 0, graceMs: 0, usedMs: 0 }) === null);
  const running = Clock.sanitize({ key: 'v1', turnMs: T, graceMs: G, usedMs: 1000, runningSince: 5 });
  check('une horloge relue repart toujours à l arrêt', running && running.runningSince === null, running);
}

if (failures) {
  console.log(`\n${failures} échec(s)`);
  process.exit(1);
}
console.log('\nOK chronomètre par coup');
