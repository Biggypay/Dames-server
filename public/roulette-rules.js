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
 * - La roue tourne et s'arrête sur UNE couleur. Seule la couleur EXACTE
 *   marque : l'aiguille sur votre couleur, +1 ; sur celle de l'adversaire,
 *   +1 pour lui ; sur une couleur que personne n'a choisie, personne ne marque
 *   (« plus proche » ne compte plus).
 * - L'issue de la manche est tirée au sort AVANT les choix, à parts égales
 *   pour les deux joueurs : la couleur du joueur 1 (4 chances sur 10), celle
 *   du joueur 2 (4 sur 10), ou une couleur que personne n'a choisie (2 sur 10,
 *   chacune des couleurs libres à parts égales). L'aiguille tombe EXACTEMENT
 *   sur la couleur désignée. La couleur choisie ne change rien aux chances :
 *   nul ne peut être favorisé, et une manche a un gagnant 8 fois sur 10 (elle
 *   en avait un 1 fois sur 3 quand la roue tirait une couleur sur six sans
 *   regarder les choix).
 * - Même couleur pour les deux (owner, 2026-11-05 : « le système doit
 *   l'accepter et considérer ça comme une manche nulle… si les deux joueurs
 *   gagnent, cela donne 1 point à chaque joueur, tout simplement parce que
 *   c'est le hasard ») : on ne rechoisit plus, la manche se joue. L'aiguille
 *   sur leur couleur commune (8 fois sur 10), 1 point chacun ; ailleurs,
 *   personne. Dans les deux cas, une manche nulle : l'écart ne bouge pas.
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
 * (SHA-256) de l'issue tirée (un nombre de 0 à 99) et d'un sel secret au
 * début de la manche, et les révèle après. N'importe qui peut vérifier que
 * l'issue n'a pas été changée une fois les choix connus (`sealText`) : 0 à
 * 39, la couleur du joueur 1 ; 40 à 79, celle du joueur 2 ; 80 à 99, une des
 * couleurs que personne n'a choisies (la (n mod k)-ième, dans l'ordre de la
 * roue, k = 4 ou 5 : vingt issues se partagent toujours également).
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
   * L'issue scellée d'une manche : un nombre tiré uniformément de 0 à 99.
   * 0–39 : la couleur du joueur 1 ; 40–79 : celle du joueur 2 ; 80–99 : une
   * couleur que personne n'a choisie (quatre, ou cinq quand les deux ont la
   * même : vingt issues se partagent également entre elles). Parts égales
   * pour les deux joueurs.
   */
  var OUTCOME_SPACE = 100;
  var OUTCOME_P1_END = 40;
  var OUTCOME_P2_END = 80;

  function isColor(value) {
    return typeof value === 'number' && value % 1 === 0 && value >= 0 && value < COLOR_COUNT;
  }

  /** Une couleur reçue du réseau (nombre ou chaîne « 0 » à « 5 »), ou null. */
  function toColor(value) {
    if (typeof value === 'string' && /^[0-5]$/.test(value)) value = Number(value);
    return isColor(value) ? value : null;
  }

  /** Une issue scellée valable : un entier de 0 à 99. */
  function isOutcome(value) {
    return typeof value === 'number' && value % 1 === 0 && value >= 0 && value < OUTCOME_SPACE;
  }

  /** La couleur que l'issue désigne : celle du joueur 1, du joueur 2, ou 0 (une couleur libre). */
  function outcomeWinner(value) {
    if (!isOutcome(value)) return 0;
    return value < OUTCOME_P1_END ? 1 : value < OUTCOME_P2_END ? 2 : 0;
  }

  /**
   * Le texte scellé d'une manche. `kind` : 'outcome', la valeur est l'issue
   * tirée (0 à 99, toute manche). Les genres 'color' (une couleur tirée sans
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

  /**
   * Même couleur pour les deux : la manche se joue quand même (plus de
   * rechoix depuis le 2026-11-05) — 1 point chacun si l'aiguille s'arrête
   * dessus, personne sinon : une manche nulle.
   */
  function sameColor(choice1, choice2) {
    return isColor(choice1) && choice1 === choice2;
  }

  /** Les couleurs que personne n'a choisies, dans l'ordre de la roue (quatre, ou cinq pour une même couleur). */
  function unchosenColors(choice1, choice2) {
    var out = [];
    for (var c = 0; c < COLOR_COUNT; c++) if (c !== choice1 && c !== choice2) out.push(c);
    return out;
  }

  /**
   * La couleur où l'aiguille s'arrête, d'après l'issue scellée AVANT les
   * choix : celle du joueur 1 (issue 0–39), celle du joueur 2 (40–79), ou une
   * des couleurs que personne n'a choisies (80–99 : la ((issue − 80) mod k)-
   * ième, dans l'ordre de la roue — k = 4, ou 5 quand les deux ont la même
   * couleur). Même couleur : l'issue d'un joueur désigne leur couleur commune.
   * null s'il manque un choix, ou pour un sceau d'un autre genre.
   */
  function drawnColor(seal, choice1, choice2) {
    if (!seal || seal.kind !== 'outcome' || !isOutcome(seal.value)) return null;
    if (!isColor(choice1) || !isColor(choice2)) return null;
    var winner = outcomeWinner(seal.value);
    if (winner === 1) return choice1;
    if (winner === 2) return choice2;
    var free = unchosenColors(choice1, choice2);
    return free[(seal.value - OUTCOME_P2_END) % free.length];
  }

  /**
   * Les points de la manche, [joueur 1, joueur 2] : 1 à celui dont la couleur
   * est EXACTEMENT celle où l'aiguille s'est arrêtée. Même couleur pour les
   * deux, l'aiguille dessus : [1, 1] (« 1 point à chaque joueur ») ; une
   * couleur que personne n'a choisie : [0, 0].
   */
  function roundPoints(choice1, choice2, drawn) {
    if (!isColor(drawn) || !isColor(choice1) || !isColor(choice2)) return [0, 0];
    return [choice1 === drawn ? 1 : 0, choice2 === drawn ? 1 : 0];
  }

  /**
   * Le gagnant de la manche, s'il est seul : 1 ou 2 ; 0 pour une manche
   * nulle — une couleur que personne n'a choisie, ou la même couleur pour les
   * deux (1 point chacun si l'aiguille est dessus : l'écart ne bouge pas).
   */
  function roundWinner(choice1, choice2, drawn) {
    var points = roundPoints(choice1, choice2, drawn);
    return points[0] === points[1] ? 0 : points[0] ? 1 : 2;
  }

  /** Les manches réglementaires jouées (les anciens rechoix, d'avant le 2026-11-05, ne comptent pas). */
  function regularPlayed(history) {
    return (Array.isArray(history) ? history : []).filter(function (h) { return h && !h.decisive && !h.repick; }).length;
  }

  /** Les manches décisives jouées (les anciens rechoix ne comptent pas). */
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

  /**
   * Des chiffres hexadécimaux du sel (`len`, 2 par défaut, à partir de `at`),
   * en nombre de 0 à 1 — non cryptographique : la mise en scène seulement.
   */
  function saltFraction(salt, at, len) {
    var size = len || 2;
    var hex = String(salt || '').substr(at || 0, size);
    if (hex.length !== size || !/^[0-9a-f]+$/i.test(hex)) return 0.5;
    return parseInt(hex, 16) / (Math.pow(16, size) - 1);
  }

  function round3(x) { return Math.round(x * 1000) / 1000; }

  /*
   * Le mouvement d'un tour de roue, en temps normalisé u ∈ [0, 1] :
   *   0 → 0,06      l'élan : la roue recule un peu, puis repart (vitesse nulle
   *                 aux deux bouts) ;
   *   → 0,21        l'accélération, x^2,4 : lente au départ, puis la roue s'emballe ;
   *   → cruise      la pleine vitesse (0,30 à 0,40 du tour selon la manche) ;
   *   → 1           le freinage, (1 − s)^ease (ease de 2,4 à 3,4) : plus il est
   *                 grand, plus la roue ralentit tôt et plus la fin au ralenti
   *                 dure, où les dernières lignes passent une à une.
   * `area` : la surface sous la vitesse (la vitesse de pointe vaut le chemin
   * parcouru divisé par la durée et par elle).
   */
  var MOTION_WIND_END = 0.06, MOTION_ACC_END = 0.21, MOTION_ACC_POW = 2.4, MOTION_STEPS = 900;
  function motionArea(ease, cruise) {
    return (MOTION_ACC_END - MOTION_WIND_END) / (MOTION_ACC_POW + 1) + (cruise - MOTION_ACC_END) + (1 - cruise) / (ease + 1);
  }
  var motionCache = {}, motionCached = 0;
  function motionCurve(ease, cruise) {
    var K = Number(ease), C = Number(cruise);
    if (!(K >= 1.5 && K <= 5)) K = 2.8;
    if (!(C >= MOTION_ACC_END + 0.02 && C <= 0.6)) C = 0.35;
    var key = K.toFixed(3) + ':' + C.toFixed(3);
    if (motionCache[key]) return motionCache[key];
    function velocity(u) {
      if (u < MOTION_WIND_END) return 0;
      if (u < MOTION_ACC_END) return Math.pow((u - MOTION_WIND_END) / (MOTION_ACC_END - MOTION_WIND_END), MOTION_ACC_POW);
      if (u < C) return 1;
      return Math.pow(Math.max(0, 1 - (u - C) / (1 - C)), K);
    }
    var N = MOTION_STEPS, table = new Float64Array(N + 1), sum = 0;
    for (var i = 1; i <= N; i++) { sum += (velocity((i - 1) / N) + velocity(i / N)) / (2 * N); table[i] = sum; }
    for (var j = 0; j <= N; j++) table[j] /= sum;
    var curve = {
      ease: K,
      cruise: C,
      area: sum,
      /** La part du chemin vers l'avant parcourue à l'instant u. */
      progress: function (u) {
        if (u <= 0) return 0;
        if (u >= 1) return 1;
        var x = u * N, k = Math.floor(x);
        return table[k] + (table[Math.min(N, k + 1)] - table[k]) * (x - k);
      },
      /** La vitesse relative (1 à pleine vitesse). */
      speed: velocity,
      /** L'élan en arrière (degrés, ≤ 0) : 0 au départ et au bout de l'élan, sans à-coup. */
      windup: function (u, depth) {
        if (u <= 0 || u >= MOTION_WIND_END) return 0;
        return -depth * (1 - Math.cos(2 * Math.PI * u / MOTION_WIND_END)) / 2;
      }
    };
    if (motionCached >= 16) { motionCache = {}; motionCached = 0; }
    motionCache[key] = curve;
    motionCached++;
    return curve;
  }

  /*
   * Après l'arrêt de la roue : un instant immobile, puis le recentrage — et
   * seulement alors le résultat (owner, 2026-11-06 : « c'est le recadrage ou
   * le recentrage qui fera savoir au joueur si l'aiguille est tombée sur sa
   * couleur »). Le serveur annonce le point au bout de ce temps.
   */
  var SPIN_SETTLE_MS = 1800;
  /* La durée d'un tour (avant le recentrage), en manche normale et décisive. */
  var SPIN_NOMINAL_MS = 7200, SPIN_DECISIVE_NOMINAL_MS = 8400;

  /**
   * Le rythme du tour (owner, 2026-11-06 : « tu dois modifier le roulement
   * parce que ça arrive toujours au même moment sur une couleur… ça doit être
   * de manière aléatoire ») — tiré du sel, le même sur tous les écrans :
   *   scale   la durée du tour, 0,90 à 1,12 fois la durée nominale (6,5 à 8,1 s ;
   *           7,6 à 9,4 s en manche décisive) ;
   *   cruise  la fin de la pleine vitesse, 0,30 à 0,40 du tour ;
   *   ease    le freinage, 2,4 à 3,4 (voir motionCurve) ;
   *   turns   le nombre de tours, pour une vitesse de pointe de 1 250 à 1 550
   *           degrés par seconde (1 300 à 1 600 en manche décisive) — toujours
   *           franchement visible : 7 à 12 tours.
   * La roue ralentit ainsi tôt ou tard, rampe longtemps ou s'arrête plus net,
   * et l'arrêt tombe à un instant différent à chaque manche. Sans sel (un
   * replay), le tour de toujours.
   */
  function spinPlan(salt, decisive) {
    if (!salt) return { turns: decisive ? 10 : 9, ease: 2.8, cruise: 0.35, scale: 1 };
    var ease = round3(2.4 + saltFraction(salt, 16, 4));
    var cruise = round3(0.3 + 0.1 * saltFraction(salt, 20, 4));
    var scale = round3(0.9 + 0.22 * saltFraction(salt, 24, 4));
    var peak = (decisive ? 1300 : 1250) + 300 * saltFraction(salt, 28, 4);
    var seconds = (decisive ? SPIN_DECISIVE_NOMINAL_MS : SPIN_NOMINAL_MS) * scale / 1000;
    var turns = Math.round(peak * seconds * motionArea(ease, cruise) / 360 - 0.5);
    return { turns: Math.max(7, Math.min(12, turns)), ease: ease, cruise: cruise, scale: scale };
  }

  /* Les trois façons de s'arrêter dans la couleur, et leurs parts (normale ; décisive). */
  var LANDING_SHARES = { anywhere: [0.5, 0.3], edge: [0.32, 0.4], hair: [0.18, 0.3] };

  /**
   * Où l'aiguille s'arrête dans la couleur tirée (owner, 2026-11-06 :
   * « ça doit être de manière aléatoire, au milieu jusqu'à la fin, au
   * début… le plus proche que possible, à des 1000 mm microscopiquement…
   * même dans les infimes parties du côté de la couleur ») — tiré du sel, le
   * même arrêt sur tous les écrans, joueurs et spectateurs :
   *   'anywhere' (50 % ; 30 % en manche décisive) n'importe où dans la
   *              couleur, du début à la fin (à plus de 6 % d'une ligne) ;
   *   'edge'     (32 % ; 40 %) tout près d'une ligne : de 1 à 10 % de la
   *              demi-case ;
   *   'hair'     (18 % ; 30 %) à un cheveu de la ligne : de 0,1 à 1 % de la
   *              demi-case (0,03 à 0,3 degré) — moins d'un pixel à l'écran :
   *              on ne voit pas de quel côté elle est, c'est le recentrage qui
   *              le dit.
   * Le côté d'un arrêt près d'une ligne : vers une couleur choisie quand une
   * seule des deux cases voisines l'est (« ça peut tomber sur la couleur
   * qu'un joueur a choisi, mais la roue glisse tellement que ça finit par
   * dévier ») — juste sortie d'elle (offset +, la case qui vient de passer
   * sous l'aiguille) ou juste avant de l'atteindre (offset −, la suivante) ;
   * sinon le sel décide. Le sel décide du genre d'arrêt et de sa distance ;
   * les choix, publics au moment du tour, n'en décident que le côté. Pure
   * mise en scène : l'issue est scellée avant les choix, l'arrêt ne change
   * jamais la couleur ni le point, et la roue se recentre ensuite
   * (roulette-board.js) au milieu de la couleur tirée. L'arrêt porte aussi le
   * rythme du tour (`turns`, `ease`, `cruise` : spinPlan). Sans sel (un
   * replay), au milieu.
   */
  function landingFor(wheel, drawn, salt, choice1, choice2, decisive) {
    var plan = spinPlan(salt, decisive);
    function landing(segment, offset, style) {
      return { segment: segment, offset: offset, style: style, turns: plan.turns, ease: plan.ease, cruise: plan.cruise };
    }
    var slots = [];
    for (var i = 0; i < wheel.length; i++) if (wheel[i] === drawn) slots.push(i);
    if (!slots.length) return landing(0, 0, 'middle');
    var pick = slots[Math.min(slots.length - 1, Math.floor(saltFraction(salt, 0) * slots.length))];
    if (!salt) return landing(pick, 0, 'middle');
    var roll = saltFraction(salt, 2, 4), depth = saltFraction(salt, 6, 6), coin = saltFraction(salt, 12, 2);
    var k = decisive ? 1 : 0;
    var style = roll < LANDING_SHARES.anywhere[k] ? 'anywhere'
      : roll < LANDING_SHARES.anywhere[k] + LANDING_SHARES.edge[k] ? 'edge' : 'hair';
    var offset;
    if (style === 'anywhere') offset = (2 * depth - 1) * 0.94;
    else {
      var gap = style === 'edge' ? 0.01 + 0.09 * depth : 0.001 + 0.009 * depth;
      var side = coin < 0.5 ? 1 : -1;
      // Le sens de rotation fait passer la case pick + 1 sous l'aiguille avant, puis pick − 1.
      var n = wheel.length;
      var passed = wheel[(pick + 1) % n], coming = wheel[(pick - 1 + n) % n];
      var chosen = function (c) { return c !== drawn && (c === choice1 || c === choice2); };
      if (chosen(passed) && !chosen(coming)) side = 1;
      else if (chosen(coming) && !chosen(passed)) side = -1;
      offset = side * (1 - gap);
    }
    return landing(pick, Math.round(offset * 1e5) / 1e5, style);
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
    sameColor: sameColor,
    roundPoints: roundPoints,
    roundWinner: roundWinner,
    regularPlayed: regularPlayed,
    decisivePlayed: decisivePlayed,
    decisiveStep: decisiveStep,
    countedPlayed: countedPlayed,
    matchDecision: matchDecision,
    SPIN_SETTLE_MS: SPIN_SETTLE_MS,
    SPIN_NOMINAL_MS: SPIN_NOMINAL_MS,
    SPIN_DECISIVE_NOMINAL_MS: SPIN_DECISIVE_NOMINAL_MS,
    LANDING_SHARES: LANDING_SHARES,
    motionCurve: motionCurve,
    motionArea: motionArea,
    spinPlan: spinPlan,
    landingFor: landingFor,
    landingAngle: landingAngle,
    publicRound: publicRound,
    colorName: colorName
  };
});
