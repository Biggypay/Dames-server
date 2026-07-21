/* ============================================================
   MOTEUR D'ÉCHECS MINDSPILLE — règles internationales FIDE
   ------------------------------------------------------------
   Un seul moteur, trois usages :
     1. serveur autoritatif (require Node dans server.js)
     2. pages 3D (echecs_multi.html / echecs_ai.html)
     3. Web Worker IA (ChessEngineFactory.toString() → Blob)
   L'état est un objet 100% JSON (aucun tableau typé) pour que
   la persistance Supabase et la re-synchro socket round-trippent
   sans transformation.

   Plateau : indices 0..63, idx = row*8 + col.
     row 0 = 8e rangée (camp noir/rouge), row 7 = 1re rangée (Blancs).
     col 0 = colonne a. Les Blancs montent (row décroît).
   Pièces : 1=P 2=N 3=B 4=R 5=Q 6=K, positives = Blancs, négatives = Noirs.
   Règles couvertes : roque (2 côtés), prise en passant, promotion
   (Q/R/B/N), échec, mat, pat, règle des 50 coups, triple répétition,
   matériel insuffisant.
============================================================ */
function ChessEngineFactory() {
  'use strict';

  var WP = 1, WN = 2, WB = 3, WR = 4, WQ = 5, WK = 6;
  var PIECE_VALUES = [0, 100, 320, 330, 500, 900, 20000];
  var FILES = 'abcdefgh';

  // Droits de roque (bitmask) : 1 = Blanc O-O, 2 = Blanc O-O-O, 4 = Noir O-O, 8 = Noir O-O-O
  var CASTLE_WK = 1, CASTLE_WQ = 2, CASTLE_BK = 4, CASTLE_BQ = 8;

  var KNIGHT_DELTAS = [[-2, -1], [-2, 1], [-1, -2], [-1, 2], [1, -2], [1, 2], [2, -1], [2, 1]];
  var KING_DELTAS = [[-1, -1], [-1, 0], [-1, 1], [0, -1], [0, 1], [1, -1], [1, 0], [1, 1]];
  var BISHOP_DIRS = [[-1, -1], [-1, 1], [1, -1], [1, 1]];
  var ROOK_DIRS = [[-1, 0], [1, 0], [0, -1], [0, 1]];

  function idxOf(r, c) { return r * 8 + c; }
  function rowOf(i) { return i >> 3; }
  function colOf(i) { return i & 7; }
  function onBoard(r, c) { return r >= 0 && r < 8 && c >= 0 && c < 8; }
  function toAlg(i) { return FILES[colOf(i)] + (8 - rowOf(i)); }
  function fromAlg(a) {
    if (typeof a !== 'string' || a.length < 2) return -1;
    var c = FILES.indexOf(a[0]), r = 8 - parseInt(a[1], 10);
    return onBoard(r, c) ? idxOf(r, c) : -1;
  }

  function initialState() {
    var b = new Array(64);
    for (var i = 0; i < 64; i++) b[i] = 0;
    var back = [WR, WN, WB, WQ, WK, WB, WN, WR];
    for (var c = 0; c < 8; c++) {
      b[idxOf(0, c)] = -back[c];
      b[idxOf(1, c)] = -WP;
      b[idxOf(6, c)] = WP;
      b[idxOf(7, c)] = back[c];
    }
    var s = { b: b, t: 0, c: CASTLE_WK | CASTLE_WQ | CASTLE_BK | CASTLE_BQ, ep: -1, h: 0, f: 1, reps: {} };
    s.key = positionKey(s);
    s.reps[s.key] = 1;
    return s;
  }

  // Clé de position (répétitions + table de transposition) : plateau + trait +
  // droits de roque + case e.p. La règle FIDE ignore les compteurs de coups.
  function positionKey(s) {
    var chars = new Array(64);
    for (var i = 0; i < 64; i++) chars[i] = String.fromCharCode(s.b[i] + 71);
    return chars.join('') + '|' + s.t + s.c + ',' + s.ep;
  }

  function cloneState(s) {
    var reps = {};
    for (var k in s.reps) reps[k] = s.reps[k];
    return { b: s.b.slice(), t: s.t, c: s.c, ep: s.ep, h: s.h, f: s.f, reps: reps, key: s.key };
  }

  // Un état venu du réseau / de la persistance ne doit jamais être cru sur parole.
  function sanitizeState(o) {
    if (!o || typeof o !== 'object' || !Array.isArray(o.b) || o.b.length !== 64) return null;
    var b = new Array(64), wk = 0, bk = 0;
    for (var i = 0; i < 64; i++) {
      var p = Number(o.b[i]);
      if (!Number.isInteger(p) || p < -6 || p > 6) return null;
      if (p === WK) wk++;
      if (p === -WK) bk++;
      b[i] = p;
    }
    if (wk !== 1 || bk !== 1) return null;
    var t = o.t === 1 ? 1 : 0;
    var c = Number(o.c); if (!Number.isInteger(c) || c < 0 || c > 15) c = 0;
    var ep = Number(o.ep); if (!Number.isInteger(ep) || ep < 0 || ep > 63) ep = -1;
    var h = Number(o.h); if (!Number.isInteger(h) || h < 0 || h > 200) h = 0;
    var f = Number(o.f); if (!Number.isInteger(f) || f < 1 || f > 9999) f = 1;
    var reps = {};
    if (o.reps && typeof o.reps === 'object' && !Array.isArray(o.reps)) {
      var n = 0;
      for (var k in o.reps) {
        if (++n > 1000) break;
        var v = Number(o.reps[k]);
        if (Number.isInteger(v) && v > 0 && v < 10 && typeof k === 'string' && k.length < 80) reps[k] = v;
      }
    }
    var s = { b: b, t: t, c: c, ep: ep, h: h, f: f, reps: reps };
    s.key = positionKey(s);
    if (!s.reps[s.key]) s.reps[s.key] = 1;
    return s;
  }

  function exportState(s) {
    return { b: s.b.slice(), t: s.t, c: s.c, ep: s.ep, h: s.h, f: s.f, reps: s.reps, key: s.key };
  }

  function kingSquare(b, side) {
    var target = side === 0 ? WK : -WK;
    for (var i = 0; i < 64; i++) if (b[i] === target) return i;
    return -1;
  }

  // La case sq est-elle attaquée par le camp `side` ?
  function attacked(b, sq, side) {
    var r = rowOf(sq), c = colOf(sq), i, nr, nc, p;
    // Pions : un pion blanc attaque vers row-1 → il attaque sq depuis row+1.
    var pr = side === 0 ? r + 1 : r - 1;
    var pawn = side === 0 ? WP : -WP;
    if (pr >= 0 && pr < 8) {
      if (c > 0 && b[idxOf(pr, c - 1)] === pawn) return true;
      if (c < 7 && b[idxOf(pr, c + 1)] === pawn) return true;
    }
    var knight = side === 0 ? WN : -WN;
    for (i = 0; i < 8; i++) {
      nr = r + KNIGHT_DELTAS[i][0]; nc = c + KNIGHT_DELTAS[i][1];
      if (onBoard(nr, nc) && b[idxOf(nr, nc)] === knight) return true;
    }
    var king = side === 0 ? WK : -WK;
    for (i = 0; i < 8; i++) {
      nr = r + KING_DELTAS[i][0]; nc = c + KING_DELTAS[i][1];
      if (onBoard(nr, nc) && b[idxOf(nr, nc)] === king) return true;
    }
    var bishop = side === 0 ? WB : -WB, rook = side === 0 ? WR : -WR, queen = side === 0 ? WQ : -WQ;
    for (i = 0; i < 4; i++) {
      nr = r + BISHOP_DIRS[i][0]; nc = c + BISHOP_DIRS[i][1];
      while (onBoard(nr, nc)) {
        p = b[idxOf(nr, nc)];
        if (p !== 0) { if (p === bishop || p === queen) return true; break; }
        nr += BISHOP_DIRS[i][0]; nc += BISHOP_DIRS[i][1];
      }
    }
    for (i = 0; i < 4; i++) {
      nr = r + ROOK_DIRS[i][0]; nc = c + ROOK_DIRS[i][1];
      while (onBoard(nr, nc)) {
        p = b[idxOf(nr, nc)];
        if (p !== 0) { if (p === rook || p === queen) return true; break; }
        nr += ROOK_DIRS[i][0]; nc += ROOK_DIRS[i][1];
      }
    }
    return false;
  }

  function inCheck(s, side) {
    var who = side === undefined ? s.t : side;
    var k = kingSquare(s.b, who);
    return k >= 0 && attacked(s.b, k, 1 - who);
  }

  // Applique un coup SUR LE PLATEAU SEULEMENT (roque/e.p./promotion inclus).
  // Retourne le nouveau tableau. Utilisé par le filtre de légalité et applyMove.
  function applyToBoard(b, mv, side) {
    var nb = b.slice(), piece = nb[mv.f];
    nb[mv.f] = 0;
    if (mv.ep) nb[mv.t + (side === 0 ? 8 : -8)] = 0;
    nb[mv.t] = mv.p ? (side === 0 ? mv.p : -mv.p) : piece;
    if (mv.castle === 1) { nb[mv.t + 1] = 0; nb[mv.t - 1] = side === 0 ? WR : -WR; }
    else if (mv.castle === 2) { nb[mv.t - 2] = 0; nb[mv.t + 1] = side === 0 ? WR : -WR; }
    return nb;
  }

  // Coups pseudo-légaux (le roi peut rester en échec — filtré ensuite).
  // Chaque coup : { f, t, p (promotion 2..5 ou 0), cap (code pièce prise, e.p. inclus),
  //                ep (prise en passant), castle (0|1|2), dbl (double pas de pion) }
  function pseudoMoves(s) {
    var side = s.t, b = s.b, out = [], i, r, c, p, ap, nr, nc, d, target;
    var forward = side === 0 ? -1 : 1;
    var startRow = side === 0 ? 6 : 1;
    var lastRow = side === 0 ? 0 : 7;
    for (i = 0; i < 64; i++) {
      p = b[i];
      if (p === 0 || (side === 0 ? p < 0 : p > 0)) continue;
      ap = p < 0 ? -p : p;
      r = rowOf(i); c = colOf(i);
      if (ap === WP) {
        nr = r + forward;
        if (nr >= 0 && nr < 8 && b[idxOf(nr, c)] === 0) {
          pushPawnMove(out, i, idxOf(nr, c), 0, false, nr === lastRow);
          if (r === startRow && b[idxOf(r + 2 * forward, c)] === 0) {
            out.push({ f: i, t: idxOf(r + 2 * forward, c), p: 0, cap: 0, ep: false, castle: 0, dbl: true });
          }
        }
        for (d = -1; d <= 1; d += 2) {
          nc = c + d;
          if (nc < 0 || nc > 7 || nr < 0 || nr > 7) continue;
          target = idxOf(nr, nc);
          var victim = b[target];
          if (victim !== 0 && (side === 0 ? victim < 0 : victim > 0)) {
            pushPawnMove(out, i, target, victim < 0 ? -victim : victim, false, nr === lastRow);
          } else if (target === s.ep && victim === 0) {
            out.push({ f: i, t: target, p: 0, cap: WP, ep: true, castle: 0, dbl: false });
          }
        }
      } else if (ap === WN) {
        for (d = 0; d < 8; d++) {
          nr = r + KNIGHT_DELTAS[d][0]; nc = c + KNIGHT_DELTAS[d][1];
          if (!onBoard(nr, nc)) continue;
          addIfNotOwn(out, b, side, i, idxOf(nr, nc));
        }
      } else if (ap === WK) {
        for (d = 0; d < 8; d++) {
          nr = r + KING_DELTAS[d][0]; nc = c + KING_DELTAS[d][1];
          if (!onBoard(nr, nc)) continue;
          addIfNotOwn(out, b, side, i, idxOf(nr, nc));
        }
        addCastleMoves(out, s, side);
      } else {
        var dirs = ap === WB ? BISHOP_DIRS : ap === WR ? ROOK_DIRS : BISHOP_DIRS.concat(ROOK_DIRS);
        for (d = 0; d < dirs.length; d++) {
          nr = r + dirs[d][0]; nc = c + dirs[d][1];
          while (onBoard(nr, nc)) {
            target = idxOf(nr, nc);
            var q = b[target];
            if (q === 0) { out.push({ f: i, t: target, p: 0, cap: 0, ep: false, castle: 0, dbl: false }); }
            else {
              if (side === 0 ? q < 0 : q > 0) out.push({ f: i, t: target, p: 0, cap: q < 0 ? -q : q, ep: false, castle: 0, dbl: false });
              break;
            }
            nr += dirs[d][0]; nc += dirs[d][1];
          }
        }
      }
    }
    return out;
  }

  function pushPawnMove(out, f, t, cap, ep, promotes) {
    if (promotes) {
      out.push({ f: f, t: t, p: WQ, cap: cap, ep: ep, castle: 0, dbl: false });
      out.push({ f: f, t: t, p: WR, cap: cap, ep: ep, castle: 0, dbl: false });
      out.push({ f: f, t: t, p: WB, cap: cap, ep: ep, castle: 0, dbl: false });
      out.push({ f: f, t: t, p: WN, cap: cap, ep: ep, castle: 0, dbl: false });
    } else {
      out.push({ f: f, t: t, p: 0, cap: cap, ep: ep, castle: 0, dbl: false });
    }
  }

  function addIfNotOwn(out, b, side, f, t) {
    var q = b[t];
    if (q === 0) out.push({ f: f, t: t, p: 0, cap: 0, ep: false, castle: 0, dbl: false });
    else if (side === 0 ? q < 0 : q > 0) out.push({ f: f, t: t, p: 0, cap: q < 0 ? -q : q, ep: false, castle: 0, dbl: false });
  }

  function addCastleMoves(out, s, side) {
    var b = s.b;
    var home = side === 0 ? 60 : 4;          // e1 / e8
    if (b[home] !== (side === 0 ? WK : -WK)) return;
    var enemy = 1 - side;
    var kBit = side === 0 ? CASTLE_WK : CASTLE_BK;
    var qBit = side === 0 ? CASTLE_WQ : CASTLE_BQ;
    var rook = side === 0 ? WR : -WR;
    if ((s.c & kBit) && b[home + 3] === rook && b[home + 1] === 0 && b[home + 2] === 0 &&
        !attacked(b, home, enemy) && !attacked(b, home + 1, enemy) && !attacked(b, home + 2, enemy)) {
      out.push({ f: home, t: home + 2, p: 0, cap: 0, ep: false, castle: 1, dbl: false });
    }
    if ((s.c & qBit) && b[home - 4] === rook && b[home - 1] === 0 && b[home - 2] === 0 && b[home - 3] === 0 &&
        !attacked(b, home, enemy) && !attacked(b, home - 1, enemy) && !attacked(b, home - 2, enemy)) {
      out.push({ f: home, t: home - 2, p: 0, cap: 0, ep: false, castle: 2, dbl: false });
    }
  }

  function legalMoves(s) {
    var pseudo = pseudoMoves(s), out = [], side = s.t;
    for (var i = 0; i < pseudo.length; i++) {
      var nb = applyToBoard(s.b, pseudo[i], side);
      var k = kingSquare(nb, side);
      if (k >= 0 && !attacked(nb, k, 1 - side)) out.push(pseudo[i]);
    }
    return out;
  }

  // La case e.p. n'est mémorisée que si un pion adverse peut réellement capturer :
  // les clés de répétition suivent ainsi la définition FIDE de « même position ».
  function epSquareAfterDouble(b, mv, side) {
    var epSq = mv.t + (side === 0 ? 8 : -8);
    var enemyPawn = side === 0 ? -WP : WP;
    var r = rowOf(mv.t), c = colOf(mv.t);
    if (c > 0 && b[idxOf(r, c - 1)] === enemyPawn) return epSq;
    if (c < 7 && b[idxOf(r, c + 1)] === enemyPawn) return epSq;
    return -1;
  }

  // Applique un coup complet. `light` = version recherche IA (pas de table des
  // répétitions copiée, pour la vitesse) ; la partie réelle utilise light=false.
  function applyMove(s, mv, light) {
    var side = s.t;
    var piece = s.b[mv.f];
    var nb = applyToBoard(s.b, mv, side);
    var nc = s.c;
    if (piece === WK) nc &= ~(CASTLE_WK | CASTLE_WQ);
    else if (piece === -WK) nc &= ~(CASTLE_BK | CASTLE_BQ);
    if (mv.f === 63 || mv.t === 63) nc &= ~CASTLE_WK;
    if (mv.f === 56 || mv.t === 56) nc &= ~CASTLE_WQ;
    if (mv.f === 7 || mv.t === 7) nc &= ~CASTLE_BK;
    if (mv.f === 0 || mv.t === 0) nc &= ~CASTLE_BQ;
    var isPawn = piece === WP || piece === -WP;
    var ns = {
      b: nb,
      t: 1 - side,
      c: nc,
      ep: mv.dbl ? epSquareAfterDouble(nb, mv, side) : -1,
      h: (isPawn || mv.cap) ? 0 : s.h + 1,
      f: side === 1 ? s.f + 1 : s.f,
      reps: null,
      key: ''
    };
    ns.key = positionKey(ns);
    if (light) { ns.reps = s.reps; return ns; }
    var reps = {};
    for (var k in s.reps) reps[k] = s.reps[k];
    reps[ns.key] = (reps[ns.key] || 0) + 1;
    ns.reps = reps;
    return ns;
  }

  function insufficientMaterial(b) {
    var minors = [], colorSum = -1, sameColor = true;
    for (var i = 0; i < 64; i++) {
      var p = b[i]; if (p === 0) continue;
      var ap = p < 0 ? -p : p;
      if (ap === WK) continue;
      if (ap === WP || ap === WR || ap === WQ) return false;
      minors.push(i);
      var sqColor = (rowOf(i) + colOf(i)) & 1;
      if (ap === WB) { if (colorSum === -1) colorSum = sqColor; else if (colorSum !== sqColor) sameColor = false; }
    }
    if (minors.length === 0 || minors.length === 1) return true;
    // Plusieurs pièces : nul automatique seulement si tous des fous de même couleur de case.
    for (var j = 0; j < minors.length; j++) {
      var q = b[minors[j]]; if (q !== WB && q !== -WB) return false;
    }
    return sameColor;
  }

  // Statut FIDE de la position : mat, pat, 50 coups, triple répétition, matériel.
  function gameStatus(s, precomputedMoves) {
    var moves = precomputedMoves || legalMoves(s);
    if (moves.length === 0) {
      if (inCheck(s, s.t)) return { over: true, winner: 1 - s.t, reason: 'checkmate' };
      return { over: true, winner: null, reason: 'stalemate' };
    }
    if (s.h >= 100) return { over: true, winner: null, reason: 'fifty' };
    if (s.reps && s.reps[s.key] >= 3) return { over: true, winner: null, reason: 'repetition' };
    if (insufficientMaterial(s.b)) return { over: true, winner: null, reason: 'insufficient' };
    return { over: false, winner: null, reason: null };
  }

  // Retrouve le coup légal correspondant à (from, to, promo). promo : code 2..5,
  // lettre 'q/r/b/n', ou 0. Un pion qui promeut sans choix explicite → dame.
  function findMove(s, fromIdx, toIdx, promo) {
    var moves = legalMoves(s), want = 0;
    if (typeof promo === 'string') want = { q: WQ, r: WR, b: WB, n: WN }[promo.toLowerCase()] || 0;
    else if (typeof promo === 'number' && promo >= 2 && promo <= 5) want = promo;
    var fallback = null;
    for (var i = 0; i < moves.length; i++) {
      var m = moves[i];
      if (m.f !== fromIdx || m.t !== toIdx) continue;
      if (!m.p) return m;
      if (want && m.p === want) return m;
      if (m.p === WQ) fallback = m;
    }
    return fallback;
  }

  /* ══════════════════════════════════════════════════════
     ÉVALUATION — matériel + tables de position (CPW
     « simplified evaluation »), roi milieu/finale interpolé.
     Score positif = avantage Blancs.
  ══════════════════════════════════════════════════════ */
  var PST_P = [0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 10, 10, 20, 30, 30, 20, 10, 10, 5, 5, 10, 25, 25, 10, 5, 5, 0, 0, 0, 20, 20, 0, 0, 0, 5, -5, -10, 0, 0, -10, -5, 5, 5, 10, 10, -20, -20, 10, 10, 5, 0, 0, 0, 0, 0, 0, 0, 0];
  var PST_N = [-50, -40, -30, -30, -30, -30, -40, -50, -40, -20, 0, 0, 0, 0, -20, -40, -30, 0, 10, 15, 15, 10, 0, -30, -30, 5, 15, 20, 20, 15, 5, -30, -30, 0, 15, 20, 20, 15, 0, -30, -30, 5, 10, 15, 15, 10, 5, -30, -40, -20, 0, 5, 5, 0, -20, -40, -50, -40, -30, -30, -30, -30, -40, -50];
  var PST_B = [-20, -10, -10, -10, -10, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 10, 10, 5, 0, -10, -10, 5, 5, 10, 10, 5, 5, -10, -10, 0, 10, 10, 10, 10, 0, -10, -10, 10, 10, 10, 10, 10, 10, -10, -10, 5, 0, 0, 0, 0, 5, -10, -20, -10, -10, -10, -10, -10, -10, -20];
  var PST_R = [0, 0, 0, 0, 0, 0, 0, 0, 5, 10, 10, 10, 10, 10, 10, 5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, 0, 0, 0, 5, 5, 0, 0, 0];
  var PST_Q = [-20, -10, -10, -5, -5, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 5, 5, 5, 0, -10, -5, 0, 5, 5, 5, 5, 0, -5, 0, 0, 5, 5, 5, 5, 0, -5, -10, 5, 5, 5, 5, 5, 0, -10, -10, 0, 5, 0, 0, 0, 0, -10, -20, -10, -10, -5, -5, -10, -10, -20];
  var PST_K_MID = [-30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -20, -30, -30, -40, -40, -30, -30, -20, -10, -20, -20, -20, -20, -20, -20, -10, 20, 20, 0, 0, 0, 0, 20, 20, 20, 30, 10, 0, 0, 10, 30, 20];
  var PST_K_END = [-50, -40, -30, -20, -20, -30, -40, -50, -30, -20, -10, 0, 0, -10, -20, -30, -30, -10, 20, 30, 30, 20, -10, -30, -30, -10, 30, 40, 40, 30, -10, -30, -30, -10, 30, 40, 40, 30, -10, -30, -30, -10, 20, 30, 30, 20, -10, -30, -30, -30, 0, 0, 0, 0, -30, -30, -50, -30, -30, -30, -30, -30, -30, -50];
  var PSTS = [null, PST_P, PST_N, PST_B, PST_R, PST_Q, null];

  function evaluate(b) {
    var score = 0, i, p, ap, phase = 0, wkSq = -1, bkSq = -1;
    for (i = 0; i < 64; i++) {
      p = b[i]; if (p === 0) continue;
      ap = p < 0 ? -p : p;
      if (ap === WK) { if (p > 0) wkSq = i; else bkSq = i; continue; }
      if (ap === WN || ap === WB) phase += 1;
      else if (ap === WR) phase += 2;
      else if (ap === WQ) phase += 4;
      if (p > 0) score += PIECE_VALUES[ap] + PSTS[ap][i];
      else score -= PIECE_VALUES[ap] + PSTS[ap][i ^ 56];
    }
    // phase max ≈ 24 : interpolation roi actif en finale / roi abrité en milieu.
    var mid = phase > 24 ? 24 : phase;
    if (wkSq >= 0) score += ((PST_K_MID[wkSq] * mid) + (PST_K_END[wkSq] * (24 - mid))) / 24 | 0;
    if (bkSq >= 0) score -= ((PST_K_MID[bkSq ^ 56] * mid) + (PST_K_END[bkSq ^ 56] * (24 - mid))) / 24 | 0;
    return score;
  }

  /* ══════════════════════════════════════════════════════
     RECHERCHE — negamax alpha-bêta, approfondissement itératif,
     quiescence (prises/promotions), table de transposition,
     tri MVV-LVA + coup TT + historique. Répétitions détectées
     le long du chemin de recherche + historique réel de partie.
  ══════════════════════════════════════════════════════ */
  var TT = new Map(), HIST = null;
  var nodeCount = 0, abortAt = 0, aborted = false;
  var pathKeys = [], repBase = null;

  function moveOrderScore(m, ttMove) {
    if (ttMove && m.f === ttMove.f && m.t === ttMove.t && m.p === ttMove.p) return 1000000;
    var sc = 0;
    if (m.cap) sc = 100000 + PIECE_VALUES[m.cap] * 10 - (m.p ? 0 : PIECE_VALUES[1]);
    if (m.p) sc += 90000 + PIECE_VALUES[m.p];
    if (!m.cap && !m.p && HIST) sc += HIST[m.f * 64 + m.t] | 0;
    return sc;
  }

  function sortMoves(moves, ttMove) {
    for (var i = 0; i < moves.length; i++) moves[i]._o = moveOrderScore(moves[i], ttMove);
    moves.sort(function (a, b) { return b._o - a._o; });
  }

  function repetitionCount(key) {
    var n = repBase && repBase[key] ? repBase[key] : 0;
    for (var i = 0; i < pathKeys.length; i++) if (pathKeys[i] === key) n++;
    return n;
  }

  function quiescence(s, alpha, beta, ply) {
    nodeCount++;
    if ((nodeCount & 511) === 0 && Date.now() >= abortAt) { aborted = true; return 0; }
    var standRaw = evaluate(s.b);
    var stand = s.t === 0 ? standRaw : -standRaw;
    if (stand >= beta) return stand;
    if (stand > alpha) alpha = stand;
    if (ply > 24) return stand;
    var moves = legalMoves(s), noisy = [];
    for (var i = 0; i < moves.length; i++) if (moves[i].cap || moves[i].p) noisy.push(moves[i]);
    if (moves.length === 0) return inCheck(s, s.t) ? -(100000 - ply) : 0;
    sortMoves(noisy, null);
    for (i = 0; i < noisy.length; i++) {
      var child = applyMove(s, noisy[i], true);
      var sc = -quiescence(child, -beta, -alpha, ply + 1);
      if (aborted) return 0;
      if (sc >= beta) return sc;
      if (sc > alpha) alpha = sc;
    }
    return alpha;
  }

  function search(s, depth, alpha, beta, ply) {
    nodeCount++;
    if ((nodeCount & 511) === 0 && Date.now() >= abortAt) { aborted = true; return 0; }
    if (s.h >= 100) return 0;
    if (ply > 0 && repetitionCount(s.key) >= 2) return 0;   // 3e occurrence si on y va
    if (depth <= 0) return quiescence(s, alpha, beta, ply);
    var tk = s.key, te = TT.get(tk);
    if (te && te.d >= depth && ply > 0) {
      if (te.f === 0) return te.s;
      if (te.f === 1) { if (te.s >= beta) return te.s; if (te.s > alpha) alpha = te.s; }
      else { if (te.s <= alpha) return te.s; if (te.s < beta) beta = te.s; }
      if (alpha >= beta) return te.s;
    }
    var moves = legalMoves(s);
    if (moves.length === 0) return inCheck(s, s.t) ? -(100000 - ply) : 0;
    if (insufficientMaterial(s.b)) return 0;
    sortMoves(moves, te ? te.mv : null);
    var best = -Infinity, bestMv = null, a0 = alpha;
    pathKeys.push(s.key);
    for (var i = 0; i < moves.length; i++) {
      var child = applyMove(s, moves[i], true);
      var sc;
      // Réduction des coups calmes tardifs (LMR), re-recherche complète si surprise.
      if (depth >= 3 && i >= 4 && !moves[i].cap && !moves[i].p && isFinite(alpha)) {
        sc = -search(child, depth - 2, -alpha - 1, -alpha, ply + 1);
        if (!aborted && sc > alpha) sc = -search(child, depth - 1, -beta, -alpha, ply + 1);
      } else {
        sc = -search(child, depth - 1, -beta, -alpha, ply + 1);
      }
      if (aborted) { pathKeys.pop(); return 0; }
      if (sc > best) { best = sc; bestMv = moves[i]; }
      if (best > alpha) alpha = best;
      if (alpha >= beta) {
        if (!moves[i].cap && !moves[i].p && HIST) HIST[moves[i].f * 64 + moves[i].t] += depth * depth;
        break;
      }
    }
    pathKeys.pop();
    if (!aborted && TT.size < 600000) {
      TT.set(tk, { d: depth, s: best, f: best <= a0 ? 2 : (best >= beta ? 1 : 0), mv: bestMv ? { f: bestMv.f, t: bestMv.t, p: bestMv.p } : null });
    }
    return best;
  }

  /* Classe les coups légaux de la position `stateObj` (l'IA joue le trait).
     Approfondissement itératif jusqu'à épuisement du budget temps.
     Retourne { idx, depth, nodes, scores } — idx = index dans legalMoves(state),
     scores dans le même ordre (pour la variété contrôlée par niveau). */
  function rankRoot(stateObj, budget, maxDepth) {
    var s = sanitizeState(stateObj);
    if (!s) return { idx: -1, depth: 0, nodes: 0, scores: [] };
    var rootMoves = legalMoves(s);
    if (rootMoves.length === 0) return { idx: -1, depth: 0, nodes: 0, scores: [] };
    abortAt = Date.now() + Math.max(30, budget | 0); aborted = false; nodeCount = 0;
    HIST = new Int32Array(4096);
    if (TT.size > 400000) TT.clear();
    repBase = {};
    for (var k in s.reps) repBase[k] = s.reps[k];
    pathKeys = [s.key];
    var n = rootMoves.length, children = new Array(n), i;
    for (i = 0; i < n; i++) children[i] = applyMove(s, rootMoves[i], true);
    var order = new Array(n);
    for (i = 0; i < n; i++) order[i] = i;
    var bestIdx = 0, completedDepth = 0, lastScores = null;
    for (var d = 1; d <= maxDepth; d++) {
      var alpha = -Infinity, iterBest = -Infinity, iterIdx = -1, iterScores = new Array(n);
      for (var oi = 0; oi < n; oi++) {
        var ci = order[oi];
        var sc;
        if (repetitionCount(children[ci].key) >= 2) sc = 0;
        else sc = -search(children[ci], d - 1, -Infinity, -alpha, 1);
        if (aborted) break;
        iterScores[ci] = sc;
        if (sc > iterBest) { iterBest = sc; iterIdx = ci; }
        if (sc > alpha) alpha = sc;
      }
      if (!aborted) {
        completedDepth = d; bestIdx = iterIdx; lastScores = iterScores;
        order.sort(function (x, y) { return iterScores[y] - iterScores[x]; });
        if (iterBest >= 99000) break;   // mat forcé trouvé
      } else break;
      if (Date.now() >= abortAt) break;
    }
    var outScores = new Array(n);
    for (i = 0; i < n; i++) outScores[i] = (lastScores && typeof lastScores[i] === 'number') ? lastScores[i] : -Infinity;
    return { idx: bestIdx, depth: completedDepth, nodes: nodeCount, scores: outScores, moves: rootMoves };
  }

  /* ══════════════════════════════════════════════════════
     FEN + notation (tests, debug, affichage)
  ══════════════════════════════════════════════════════ */
  var FEN_PIECES = { p: WP, n: WN, b: WB, r: WR, q: WQ, k: WK };
  function fromFEN(fen) {
    var parts = String(fen).trim().split(/\s+/);
    if (parts.length < 2) return null;
    var b = new Array(64), i;
    for (i = 0; i < 64; i++) b[i] = 0;
    var rows = parts[0].split('/');
    if (rows.length !== 8) return null;
    for (var r = 0; r < 8; r++) {
      var c = 0;
      for (i = 0; i < rows[r].length; i++) {
        var ch = rows[r][i];
        if (ch >= '1' && ch <= '8') { c += parseInt(ch, 10); continue; }
        var lower = ch.toLowerCase(), code = FEN_PIECES[lower];
        if (!code || c > 7) return null;
        b[idxOf(r, c)] = ch === lower ? -code : code;
        c++;
      }
      if (c !== 8) return null;
    }
    var s = {
      b: b,
      t: parts[1] === 'b' ? 1 : 0,
      c: 0,
      ep: parts[3] && parts[3] !== '-' ? fromAlg(parts[3]) : -1,
      h: parts[4] ? parseInt(parts[4], 10) || 0 : 0,
      f: parts[5] ? parseInt(parts[5], 10) || 1 : 1,
      reps: {}
    };
    var castle = parts[2] || '-';
    if (castle.indexOf('K') >= 0) s.c |= CASTLE_WK;
    if (castle.indexOf('Q') >= 0) s.c |= CASTLE_WQ;
    if (castle.indexOf('k') >= 0) s.c |= CASTLE_BK;
    if (castle.indexOf('q') >= 0) s.c |= CASTLE_BQ;
    s.key = positionKey(s);
    s.reps[s.key] = 1;
    return s;
  }

  function toFEN(s) {
    var rows = [];
    for (var r = 0; r < 8; r++) {
      var row = '', empty = 0;
      for (var c = 0; c < 8; c++) {
        var p = s.b[idxOf(r, c)];
        if (p === 0) { empty++; continue; }
        if (empty) { row += empty; empty = 0; }
        var ch = ' pnbrqk'[p < 0 ? -p : p];
        row += p > 0 ? ch.toUpperCase() : ch;
      }
      if (empty) row += empty;
      rows.push(row);
    }
    var castle = '';
    if (s.c & CASTLE_WK) castle += 'K';
    if (s.c & CASTLE_WQ) castle += 'Q';
    if (s.c & CASTLE_BK) castle += 'k';
    if (s.c & CASTLE_BQ) castle += 'q';
    return rows.join('/') + ' ' + (s.t === 0 ? 'w' : 'b') + ' ' + (castle || '-') + ' ' +
      (s.ep >= 0 ? toAlg(s.ep) : '-') + ' ' + s.h + ' ' + s.f;
  }

  function moveLabel(s, mv) {
    var piece = s.b[mv.f], ap = piece < 0 ? -piece : piece;
    if (mv.castle === 1) return 'O-O';
    if (mv.castle === 2) return 'O-O-O';
    var letters = ['', '', 'C', 'F', 'T', 'D', 'R'];
    var label = letters[ap] + toAlg(mv.f) + (mv.cap ? 'x' : '-') + toAlg(mv.t);
    if (mv.p) label += '=' + letters[mv.p];
    return label;
  }

  function perft(s, depth) {
    if (depth === 0) return 1;
    var moves = legalMoves(s), total = 0;
    for (var i = 0; i < moves.length; i++) total += perft(applyMove(s, moves[i], true), depth - 1);
    return total;
  }

  return {
    initialState: initialState,
    cloneState: cloneState,
    exportState: exportState,
    sanitizeState: sanitizeState,
    positionKey: positionKey,
    legalMoves: legalMoves,
    applyMove: applyMove,
    findMove: findMove,
    inCheck: inCheck,
    attacked: attacked,
    kingSquare: kingSquare,
    gameStatus: gameStatus,
    insufficientMaterial: insufficientMaterial,
    evaluate: evaluate,
    rankRoot: rankRoot,
    fromFEN: fromFEN,
    toFEN: toFEN,
    toAlg: toAlg,
    fromAlg: fromAlg,
    moveLabel: moveLabel,
    perft: perft,
    idxOf: idxOf,
    rowOf: rowOf,
    colOf: colOf
  };
}

/* UMD léger : Node (serveur + tests), navigateur (pages 3D) et Web Worker. */
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { ChessEngineFactory: ChessEngineFactory };
} else if (typeof self !== 'undefined') {
  self.ChessEngineFactory = ChessEngineFactory;
}
