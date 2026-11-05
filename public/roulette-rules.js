/*
 * Roulette Royale — les règles, écrites une seule fois.
 *
 * Le même fichier sert au serveur (lib/color-roulette.js le charge avec
 * `require`) et aux trois pages du jeu (en ligne, contre l'IA, entre amis) :
 * aucune page ne peut compter un point autrement que le serveur.
 *
 * Le jeu (règles du 2026-11-05, troisième version — owner : « l'aiguille doit
 * tomber sur la couleur exacte, pas sur une couleur qui est plus proche… le
 * système doit être strict, mais toujours donner la possibilité aux joueurs
 * d'avoir un gagnant… je ne dis pas de favoriser aucun joueur »)
 * ------
 * - Une roue de six couleurs ; les deux joueurs disposent des mêmes six.
 * - À chaque manche, chacun choisit une couleur en secret.
 * - Même couleur pour les deux : rien ne tourne, on rechoisit (la manche ne
 *   compte pas).
 * - Sinon la roue tourne et s'arrête sur UNE couleur. Seule la couleur
 *   EXACTE marque : l'aiguille sur votre couleur, +1 ; sur celle de
 *   l'adversaire, +1 pour lui ; sur une couleur que personne n'a choisie,
 *   personne ne marque (« plus proche » ne compte plus).
 * - L'issue de la manche est tirée au sort AVANT les choix, à parts égales
 *   pour les deux joueurs : le joueur 1 marque (4 chances sur 10), le joueur 2
 *   marque (4 sur 10), ou personne (2 sur 10 : la roue s'arrête alors sur une
 *   des quatre couleurs que personne n'a choisies, chacune 1 chance sur 20).
 *   L'aiguille tombe EXACTEMENT sur la couleur du gagnant. La couleur choisie
 *   ne change rien aux chances : nul ne peut être favorisé, et une manche a
 *   un gagnant 8 fois sur 10 (elle en avait un 1 fois sur 3 quand la roue
 *   tirait une couleur sur six sans regarder les choix).
 * - Six manches (owner : « ça devrait être 6 »). Le match s'arrête plus tôt
 *   si l'écart ne peut plus être comblé.
 * - Égalité au bout des six : on continue, 7e et 8e manches, puis 9e et
 *   10e… « jusqu'à ce qu'un joueur gagne ». Ces manches décisives vont DEUX
 *   PAR DEUX : même si l'un gagne la première de la paire, l'autre joue la
 *   seconde (« pour l'équité ») ; un point d'avance au bout de la paire, et
 *   c'est gagné ; sinon, une nouvelle paire.
 * - La roue garde ses six couleurs, manches décisives comprises (« ne réduis
 *   pas, pour ne pas baisser la tension »). Seule la mise en scène change :
 *   plus de suspens à l'arrêt, un tour de roue plus long.
 *
 * Le tirage est scellé AVANT les choix : le serveur publie l'empreinte
 * (SHA-256) de l'issue tirée (un nombre de 0 à 19) et d'un sel secret au
 * début de la manche, et les révèle après. N'importe qui peut vérifier que
 * l'issue n'a pas été changée une fois les choix connus (`sealText`) : 0 à 7,
 * le joueur 1 ; 8 à 15, le joueur 2 ; 16 à 19, la 1re, 2e, 3e ou 4e des
 * couleurs que personne n'a choisies, dans l'ordre de la roue.
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
  var REGULAR_ROUNDS = 6;
  /*
   * L'issue scellée d'une manche : un nombre tiré uniformément de 0 à 19.
   * 0–7 : le joueur 1 marque ; 8–15 : le joueur 2 ; 16–19 : personne (une des
   * quatre couleurs que personne n'a choisies). Parts égales pour les deux.
   */
  var OUTCOME_SPACE = 20;
  var OUTCOME_P1_END = 8;
  var OUTCOME_P2_END = 16;

  function isColor(value) {
    return typeof value === 'number' && value % 1 === 0 && value >= 0 && value < COLOR_COUNT;
  }

  /** Une couleur reçue du réseau (nombre ou chaîne « 0 » à « 5 »), ou null. */
  function toColor(value) {
    if (typeof value === 'string' && /^[0-5]$/.test(value)) value = Number(value);
    return isColor(value) ? value : null;
  }

  /** Une issue scellée valable : un entier de 0 à 19. */
  function isOutcome(value) {
    return typeof value === 'number' && value % 1 === 0 && value >= 0 && value < OUTCOME_SPACE;
  }

  /** Qui marque, d'après l'issue scellée : 1, 2, ou 0 (personne). */
  function outcomeWinner(value) {
    if (!isOutcome(value)) return 0;
    return value < OUTCOME_P1_END ? 1 : value < OUTCOME_P2_END ? 2 : 0;
  }

  /**
   * Le texte scellé d'une manche. `kind` : 'outcome', la valeur est l'issue
   * tirée (0 à 19, toute manche). Les genres 'color' (une couleur tirée sans
   * regarder les choix, jusqu'à la 3e version des règles) et 'bit' (les
   * manches décisives à deux couleurs) n'ont plus cours.
   */
  function sealText(roomId, round, kind, value, salt) {
    return 'roulette:v1:' + roomId + ':' + round + ':' + kind + ':' + value + ':' + salt;
  }

  /**
   * La roue d'une manche : toujours les six couleurs, manches décisives
   * comprises (owner : « ne réduis pas, pour ne pas baisser la tension »).
   * Les paramètres restent pour les appels existants.
   */
  function wheelFor(decisive, choice1, choice2) {
    return [0, 1, 2, 3, 4, 5];
  }

  /** La distance de deux couleurs sur la roue : 0 (la même) à 3 cases, par le plus court (affichage seulement). */
  function colorDistance(a, b) {
    if (!isColor(a) || !isColor(b)) return null;
    var d = Math.abs(a - b);
    return Math.min(d, COLOR_COUNT - d);
  }

  /** Même couleur pour les deux : rien ne tourne, on rechoisit (toute manche). */
  function isRepick(choice1, choice2) {
    return isColor(choice1) && choice1 === choice2;
  }

  /** Les couleurs que personne n'a choisies, dans l'ordre de la roue (quatre). */
  function unchosenColors(choice1, choice2) {
    var out = [];
    for (var c = 0; c < COLOR_COUNT; c++) if (c !== choice1 && c !== choice2) out.push(c);
    return out;
  }

  /**
   * La couleur où l'aiguille s'arrête, d'après l'issue scellée AVANT les
   * choix : celle du joueur 1 (issue 0–7), celle du joueur 2 (8–15), ou une
   * des couleurs que personne n'a choisies (16–19, dans l'ordre de la roue).
   * null si les deux joueurs ont choisi la même (on rechoisit), s'il manque un
   * choix, ou pour un sceau d'un autre genre.
   */
  function drawnColor(seal, choice1, choice2) {
    if (!seal || seal.kind !== 'outcome' || !isOutcome(seal.value)) return null;
    if (!isColor(choice1) || !isColor(choice2) || isRepick(choice1, choice2)) return null;
    var winner = outcomeWinner(seal.value);
    if (winner === 1) return choice1;
    if (winner === 2) return choice2;
    var free = unchosenColors(choice1, choice2);
    return free[seal.value - OUTCOME_P2_END] === undefined ? null : free[seal.value - OUTCOME_P2_END];
  }

  /**
   * Le gagnant de la manche : celui dont la couleur est EXACTEMENT celle où
   * l'aiguille s'est arrêtée (1 ou 2) ; 0 si c'est une couleur que personne
   * n'a choisie, ou si les deux ont la même couleur.
   */
  function roundWinner(choice1, choice2, drawn) {
    if (!isColor(drawn) || !isColor(choice1) || !isColor(choice2) || choice1 === choice2) return 0;
    if (drawn === choice1) return 1;
    if (drawn === choice2) return 2;
    return 0;
  }

  /** Les manches réglementaires jouées (les rechoix ne comptent pas). */
  function regularPlayed(history) {
    return (Array.isArray(history) ? history : []).filter(function (h) { return h && !h.decisive && !h.repick; }).length;
  }

  /** Les manches décisives jouées (les rechoix ne comptent pas). */
  function decisivePlayed(history) {
    return (Array.isArray(history) ? history : []).filter(function (h) { return h && h.decisive && !h.repick; }).length;
  }

  /** Dans la paire de manches décisives en cours : 1 (la première) ou 2 (la réponse). */
  function decisiveStep(history) {
    return (decisivePlayed(history) % 2) + 1;
  }

  /** Toutes les manches comptées, décisives comprises (les rechoix ne comptent pas). */
  function countedPlayed(history) {
    return regularPlayed(history) + decisivePlayed(history);
  }

  /**
   * Après une manche, la suite du match.
   *   { over: true, winnerSlot }      le match est joué ;
   *   { over: false, decisive }       une manche de plus (décisive ou non).
   * Fin anticipée : l'écart dépasse les manches restantes. Égalité au bout
   * des manches prévues : manches décisives (7e, 8e…), deux par deux. Le match
   * ne se décide qu'au bout d'une paire (`decisivePlayed` pair) : après la
   * première manche de la paire, l'autre joueur répond toujours. Les scores
   * étaient à égalité en entrant dans les manches décisives : un écart au bout
   * d'une paire, c'est 2-0 ou 1-0 (une manche nulle) dans cette paire ; 1-1 ou
   * 0-0, une nouvelle paire.
   */
  function matchDecision(state) {
    var scores = state.scores || [0, 0];
    var s1 = Number(scores[0]) || 0, s2 = Number(scores[1]) || 0;
    var total = Number(state.totalRounds) || REGULAR_ROUNDS;
    if (state.decisive) {
      var played = Number(state.decisivePlayed) || 0;
      if (played > 0 && played % 2 === 0 && s1 !== s2) return { over: true, winnerSlot: s1 > s2 ? 1 : 2 };
      return { over: false, decisive: true };
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
   * Où la roue s'arrête : la case (parmi celles de la couleur tirée) et
   * l'endroit dans la case, tirés du sel — le même arrêt sur tous les écrans,
   * joueurs et spectateurs. Pour le suspens (owner, 2026-11-05 : « parfois ça
   * s'arrête sur la couleur à la dernière ligne… créer plus de suspense »),
   * selon le sel :
   *   'last-line'  (40 % ; 50 % en manche décisive) la roue franchit la ligne
   *                au tout dernier moment : elle s'arrête juste entrée dans la
   *                case (offset +0,78 à +0,88, du côté de la case qui vient de
   *                passer sous l'aiguille) ;
   *   'near-next'  (25 % ; 35 % en manche décisive) elle s'arrête juste avant
   *                la ligne suivante (offset −0,78 à −0,88) ;
   *   'middle'     sinon, vers le milieu de la case.
   * Le presque-arrêt va vers une couleur choisie (owner : « des fois ça va
   * tomber sur une couleur que l'un a choisi mais ça n'arrive pas ») : quand
   * une seule des deux cases voisines est une couleur choisie, le côté passe
   * de ce côté-là — la roue traîne sur elle puis franchit la ligne
   * ('last-line'), ou s'arrête juste avant de l'atteindre ('near-next').
   * Le sel décide toujours SI la manche a du suspens (65 % ; 85 % en manche
   * décisive) ; les choix, publics au moment du tour, n'en décident que le
   * côté. Toujours franchement dans la case (au moins 6 % de sa largeur depuis
   * une ligne). Pure mise en scène : l'issue est scellée avant les choix,
   * l'arrêt ne change jamais la couleur ni le point — et quelques instants
   * après l'arrêt, la roue se recentre (roulette-board.js) : l'aiguille finit
   * au milieu de la couleur tirée. Sans sel (un replay), au milieu.
   */
  function landingFor(wheel, drawn, salt, choice1, choice2, decisive) {
    var slots = [];
    for (var i = 0; i < wheel.length; i++) if (wheel[i] === drawn) slots.push(i);
    if (!slots.length) return { segment: 0, offset: 0, style: 'middle' };
    var pick = slots[Math.min(slots.length - 1, Math.floor(saltFraction(salt, 0) * slots.length))];
    if (!salt) return { segment: pick, offset: 0, style: 'middle' };
    var roll = saltFraction(salt, 4), f = saltFraction(salt, 2);
    /* En manche décisive, le cœur doit battre : 85 % d'arrêts au ras d'une ligne. */
    var lastLine = decisive ? 0.5 : 0.4, nearNext = decisive ? 0.85 : 0.65;
    var style = roll < lastLine ? 'last-line' : roll < nearNext ? 'near-next' : 'middle';
    if (style !== 'middle') {
      // Le sens de rotation fait passer la case pick + 1 avant, puis pick − 1.
      var n = wheel.length;
      var passed = wheel[(pick + 1) % n], coming = wheel[(pick - 1 + n) % n];
      var chosen = function (c) { return c !== drawn && (c === choice1 || c === choice2); };
      if (chosen(passed) && !chosen(coming)) style = 'last-line';
      else if (chosen(coming) && !chosen(passed)) style = 'near-next';
    }
    var offset = style === 'last-line' ? 0.78 + 0.1 * f : style === 'near-next' ? -(0.78 + 0.1 * f) : (f - 0.5) * 0.9;
    return { segment: pick, offset: Math.round(offset * 1000) / 1000, style: style };
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
    OUTCOME_SPACE: OUTCOME_SPACE,
    OUTCOME_P1_END: OUTCOME_P1_END,
    OUTCOME_P2_END: OUTCOME_P2_END,
    isColor: isColor,
    isOutcome: isOutcome,
    outcomeWinner: outcomeWinner,
    unchosenColors: unchosenColors,
    toColor: toColor,
    sealText: sealText,
    wheelFor: wheelFor,
    drawnColor: drawnColor,
    colorDistance: colorDistance,
    isRepick: isRepick,
    roundWinner: roundWinner,
    regularPlayed: regularPlayed,
    decisivePlayed: decisivePlayed,
    decisiveStep: decisiveStep,
    countedPlayed: countedPlayed,
    matchDecision: matchDecision,
    landingFor: landingFor,
    landingAngle: landingAngle,
    publicRound: publicRound,
    colorName: colorName
  };
});
