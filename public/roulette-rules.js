/*
 * Roulette Royale — les règles, écrites une seule fois.
 *
 * Le même fichier sert au serveur (lib/color-roulette.js le charge avec
 * `require`) et aux trois pages du jeu (en ligne, contre l'IA, entre amis) :
 * aucune page ne peut compter un point autrement que le serveur.
 *
 * Le jeu
 * ------
 * - Une roue de six couleurs ; les deux joueurs disposent des mêmes six.
 * - À chaque manche, chacun choisit une couleur en secret.
 * - La roue tourne et désigne une couleur, tirée au hasard par le serveur.
 *   - Un seul joueur l'avait : il gagne la manche (+1).
 *   - Aucun des deux ne l'avait, ou les deux l'avaient : manche nulle.
 * - Cinq manches. Le match s'arrête plus tôt si l'écart ne peut plus être
 *   comblé. Égalité au bout des cinq : manche décisive.
 * - Manche décisive : la roue ne garde que les deux couleurs choisies, une
 *   chance sur deux chacun ; même couleur pour les deux, on rechoisit.
 *
 * Le tirage est scellé AVANT les choix : le serveur publie l'empreinte
 * (SHA-256) de la couleur tirée et d'un sel secret au début de la manche, et
 * les révèle après. N'importe qui peut vérifier que la couleur n'a pas été
 * changée une fois les choix connus (`sealText`).
 */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.RouletteRules = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  /* L'ordre de la roue, dans le sens des aiguilles d'une montre, depuis le
     haut. Chaque couleur a sa forme : un daltonien les distingue aussi. */
  var COLORS = [
    { id: 0, key: 'rouge', name: 'Rouge', hex: '#ef4444', deep: '#991b1b', shape: 'circle' },
    { id: 1, key: 'orange', name: 'Orange', hex: '#f97316', deep: '#9a3412', shape: 'triangle' },
    { id: 2, key: 'jaune', name: 'Jaune', hex: '#facc15', deep: '#a16207', shape: 'star' },
    { id: 3, key: 'vert', name: 'Vert', hex: '#22c55e', deep: '#166534', shape: 'square' },
    { id: 4, key: 'bleu', name: 'Bleu', hex: '#3b82f6', deep: '#1e40af', shape: 'diamond' },
    { id: 5, key: 'violet', name: 'Violet', hex: '#a855f7', deep: '#6b21a8', shape: 'hexagon' }
  ];
  var COLOR_COUNT = COLORS.length;
  /* Manches prévues d'un match, avant toute manche décisive. */
  var REGULAR_ROUNDS = 5;

  function isColor(value) {
    return typeof value === 'number' && value % 1 === 0 && value >= 0 && value < COLOR_COUNT;
  }

  /** Une couleur reçue du réseau (nombre ou chaîne « 0 » à « 5 »), ou null. */
  function toColor(value) {
    if (typeof value === 'string' && /^[0-5]$/.test(value)) value = Number(value);
    return isColor(value) ? value : null;
  }

  /**
   * Le texte scellé d'une manche. `kind` : 'color' (manche normale, la valeur
   * est la couleur tirée) ou 'bit' (manche décisive, la valeur choisit entre
   * les deux couleurs choisies, la plus petite d'abord).
   */
  function sealText(roomId, round, kind, value, salt) {
    return 'roulette:v1:' + roomId + ':' + round + ':' + kind + ':' + value + ':' + salt;
  }

  /** La roue d'une manche : les six couleurs, ou les deux choisies, alternées. */
  function wheelFor(decisive, choice1, choice2) {
    if (decisive && isColor(choice1) && isColor(choice2) && choice1 !== choice2) {
      var a = Math.min(choice1, choice2), b = Math.max(choice1, choice2);
      return [a, b, a, b, a, b];
    }
    return [0, 1, 2, 3, 4, 5];
  }

  /**
   * La couleur désignée. Manche normale : celle scellée. Manche décisive :
   * l'une des deux couleurs choisies selon le bit scellé — null si les deux
   * joueurs ont choisi la même (on rechoisit).
   */
  function drawnColor(seal, choice1, choice2) {
    if (!seal) return null;
    if (seal.kind === 'color') return isColor(seal.value) ? seal.value : null;
    if (seal.kind !== 'bit' || (seal.value !== 0 && seal.value !== 1)) return null;
    if (!isColor(choice1) || !isColor(choice2) || choice1 === choice2) return null;
    return seal.value === 0 ? Math.min(choice1, choice2) : Math.max(choice1, choice2);
  }

  /** Le gagnant de la manche : 1, 2, ou 0 (personne, ou les deux). */
  function roundWinner(choice1, choice2, drawn) {
    if (!isColor(drawn)) return 0;
    var hit1 = choice1 === drawn, hit2 = choice2 === drawn;
    if (hit1 && !hit2) return 1;
    if (hit2 && !hit1) return 2;
    return 0;
  }

  /**
   * Après une manche, la suite du match.
   *   { over: true, winnerSlot }      le match est joué ;
   *   { over: false, decisive }       une manche de plus (décisive ou non).
   * Fin anticipée : l'écart dépasse les manches restantes. Égalité au bout
   * des manches prévues : manches décisives jusqu'à un vainqueur.
   */
  function matchDecision(state) {
    var scores = state.scores || [0, 0];
    var s1 = Number(scores[0]) || 0, s2 = Number(scores[1]) || 0;
    var total = Number(state.totalRounds) || REGULAR_ROUNDS;
    if (state.decisive) {
      var w = Number(state.lastWinner) || 0;
      return w === 1 || w === 2 ? { over: true, winnerSlot: w } : { over: false, decisive: true };
    }
    var remaining = Math.max(0, total - (Number(state.roundsPlayed) || 0));
    if (Math.abs(s1 - s2) > remaining) return { over: true, winnerSlot: s1 > s2 ? 1 : 2 };
    if (remaining === 0) return { over: false, decisive: true };
    return { over: false, decisive: false };
  }

  /** Deux chiffres hexadécimaux du sel, en nombre de 0 à 1 (non cryptographique : l'affichage). */
  function saltFraction(salt, at) {
    var n = parseInt(String(salt || '').substr(at || 0, 2), 16);
    return isFinite(n) ? n / 255 : 0.5;
  }

  /**
   * Où la roue s'arrête : la case (parmi celles de la couleur tirée) et un
   * léger décalage dans la case, tirés du sel — le même arrêt sur tous les
   * écrans, joueurs et spectateurs.
   */
  function landingFor(wheel, drawn, salt) {
    var slots = [];
    for (var i = 0; i < wheel.length; i++) if (wheel[i] === drawn) slots.push(i);
    if (!slots.length) return { segment: 0, offset: 0 };
    var pick = slots[Math.min(slots.length - 1, Math.floor(saltFraction(salt, 0) * slots.length))];
    /* Jamais sur un bord : au plus 30 % d'une demi-case du centre. */
    var offset = (saltFraction(salt, 2) - 0.5) * 0.6;
    return { segment: pick, offset: Math.round(offset * 1000) / 1000 };
  }

  /** L'angle (degrés) qui amène la case `segment` sous le pointeur du haut. */
  function landingAngle(wheelLength, landing) {
    var seg = 360 / wheelLength;
    var center = landing.segment * seg + seg / 2 + (landing.offset || 0) * (seg / 2);
    return (360 - center) % 360;
  }

  /** Une manche passée, réduite à ce que tout le monde peut voir. */
  function publicRound(entry) {
    if (!entry || typeof entry !== 'object') return null;
    return {
      round: Number(entry.round) || 0,
      choice1: toColor(entry.choice1),
      choice2: toColor(entry.choice2),
      drawn: toColor(entry.drawn),
      winnerSlot: entry.winnerSlot === 1 || entry.winnerSlot === 2 ? entry.winnerSlot : 0,
      decisive: entry.decisive === true,
      repick: entry.repick === true
    };
  }

  function colorName(id) {
    return isColor(id) ? COLORS[id].name : '—';
  }

  return {
    COLORS: COLORS,
    COLOR_COUNT: COLOR_COUNT,
    REGULAR_ROUNDS: REGULAR_ROUNDS,
    isColor: isColor,
    toColor: toColor,
    sealText: sealText,
    wheelFor: wheelFor,
    drawnColor: drawnColor,
    roundWinner: roundWinner,
    matchDecision: matchDecision,
    landingFor: landingFor,
    landingAngle: landingAngle,
    publicRound: publicRound,
    colorName: colorName
  };
});
