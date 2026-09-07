'use strict';

// Pendule Fischer des parties d'échecs de tournoi.
//
// Ce que ces tests vérifient est exactement ce que la cadence 10+5 promet :
// dix minutes chacun, cinq secondes rendues après chaque coup ACCEPTÉ, rien
// après un coup refusé, et un drapeau qui tombe sans transformer une position
// nulle en victoire.

const Clock = require('../lib/chess-clock.js');
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

const tc = (over) => Clock.readTimeControl({
  chess_time_control: Object.assign(
    { base_seconds: 600, white_seconds: 600, black_seconds: 600, increment_seconds: 5, label: '10+5', armageddon: false },
    over || {}
  )
});

console.log('— Cadence lue depuis la base —');
{
  const control = tc();
  check('10+5 : dix minutes par camp', control.whiteMs === 600000 && control.blackMs === 600000, control);
  check('incrément de cinq secondes', control.incrementMs === 5000, control);
  check('aucune cadence déclarée → aucune pendule', Clock.readTimeControl({}) === null);
  check('cadence illisible → aucune pendule', Clock.readTimeControl({ chess_time_control: { label: 'x' } }) === null);

  const armageddon = tc({ white_seconds: 300, black_seconds: 240, increment_seconds: 0, armageddon: true });
  check('Armageddon : temps asymétrique', armageddon.whiteMs === 300000 && armageddon.blackMs === 240000, armageddon);
  check('Armageddon signalé', armageddon.armageddon === true);

  const absurd = tc({ base_seconds: 0, white_seconds: 0, black_seconds: 999999, increment_seconds: 9999 });
  check('valeurs aberrantes bornées', absurd.whiteMs >= 1000 && absurd.blackMs <= 3 * 3600000 && absurd.incrementMs === 60000, absurd);
}

console.log('— 10+5 : le temps de réflexion se paie, l’incrément se rend —');
{
  const clock = Clock.createClock(tc());
  const t0 = 1_000_000;
  Clock.startSlot(clock, 1, t0);

  // 8:20 avant le coup → le joueur réfléchit 100 s : 10:00 - 1:40 = 8:20.
  check('temps qui défile pendant la réflexion',
    Clock.remainingFor(clock, 1, t0 + 100_000) === 500_000);
  check('la pendule de l’adversaire ne bouge pas',
    Clock.remainingFor(clock, 2, t0 + 100_000) === 600_000);

  Clock.chargeElapsed(clock, t0 + 100_000);
  Clock.addIncrement(clock, 1);
  check('8:20 → coup validé → 8:25', clock.remaining[1] === 505_000, clock.remaining);

  Clock.startSlot(clock, 2, t0 + 100_000);
  check('le trait passe à l’adversaire', clock.runningSlot === 2);
  check('le premier joueur garde son reste',
    Clock.remainingFor(clock, 1, t0 + 200_000) === 505_000);
}

console.log('— Un coup refusé ne donne aucun incrément —');
{
  const clock = Clock.createClock(tc());
  const t0 = 0;
  Clock.startSlot(clock, 1, t0);
  // Le serveur ne facture et n’incrémente QUE sur un coup accepté : ici, rien
  // n’est appelé, la pendule continue simplement de tourner.
  check('le temps continue de courir', Clock.remainingFor(clock, 1, t0 + 30_000) === 570_000);
  check('aucun incrément crédité', clock.remaining[1] === 600_000, clock.remaining);
}

console.log('— Pause, reconnexion, redémarrage : le reste est intact —');
{
  const clock = Clock.createClock(tc());
  Clock.startSlot(clock, 1, 0);
  Clock.chargeElapsed(clock, 60_000);           // pause à la 60e seconde
  check('la pause fige le temps restant', clock.remaining[1] === 540_000, clock.remaining);
  check('aucune pendule ne tourne pendant la pause', clock.runningSlot === null);

  // Redémarrage de Render : la pendule passe par du JSON.
  const restored = Clock.sanitizeClock(JSON.parse(JSON.stringify(clock)));
  check('le reste survit à la persistance', restored.remaining[1] === 540_000 && restored.remaining[2] === 600_000, restored.remaining);
  check('la pendule restaurée repart à l’arrêt', restored.runningSlot === null);
  check('l’incrément survit', restored.incrementMs === 5000);

  Clock.startSlot(restored, 1, 5_000_000);      // reprise bien plus tard
  check('le temps serveur éteint n’est facturé à personne',
    Clock.remainingFor(restored, 1, 5_000_000) === 540_000);

  check('une pendule illisible est rejetée', Clock.sanitizeClock({ remaining: {} }) === null);
}

console.log('— Drapeau tombé : article 6.9 —');
{
  const start = Chess.initialState();
  check('position initiale : l’adversaire peut mater → défaite au temps',
    Clock.flagFallOutcome(start, 1).winnerSlot === 2 && Clock.flagFallOutcome(start, 1).reason === 'timeout');

  // Roi et cavalier seuls contre roi : le mat est impossible, donc nulle.
  const lone = Chess.fromFEN('8/8/8/4k3/8/8/8/K6N w - - 0 1');
  check('FEN de test valide', !!lone);
  check('roi + cavalier ne peut pas mater : nulle au temps',
    Clock.flagFallOutcome(lone, 2).winnerSlot === 0 && Clock.flagFallOutcome(lone, 2).reason === 'draw',
    Clock.flagFallOutcome(lone, 2));

  const twoKnights = Chess.fromFEN('8/8/8/4k3/8/8/8/K5NN w - - 0 1');
  check('roi + deux cavaliers peut mater : victoire au temps',
    Clock.flagFallOutcome(twoKnights, 2).winnerSlot === 1);

  const pawn = Chess.fromFEN('8/8/8/4k3/8/8/4P3/K7 w - - 0 1');
  check('un simple pion suffit : victoire au temps',
    Clock.flagFallOutcome(pawn, 2).winnerSlot === 1);

  check('roi seul ne mate pas', Clock.hasMatingMaterial(Chess.fromFEN('8/8/8/4k3/8/8/8/K7 w - - 0 1').b, 0) === false);
}

console.log(failures === 0 ? '\n✅ Pendule d’échecs : tous les tests passent' : `\n❌ ${failures} test(s) en échec`);
process.exit(failures === 0 ? 0 : 1);
