// ============================================================
//  SERVEUR NANO BANANA — Socket.io + Express
//  Dames 10x10 + Tic-Tac-Toe + Quoridor + Penalty Shootout + Chifoumi
//  Temps réel — Node 20
//  v5.5 — Correction Timing Fin Penalty & Smart Routing
// ============================================================
require('dotenv').config();
const express      = require('express');
const http         = require('http');
const fs           = require('fs');
const path         = require('path');
const { Server }   = require('socket.io');
const bcrypt       = require('bcryptjs');
const jwt          = require('jsonwebtoken');
const { v4: uuid } = require('uuid');

const app    = express();
const server = http.createServer(app);
const PUBLIC = path.join(__dirname, 'public');
const PORT       = process.env.PORT || 3000;
const JWT_SECRET = process.env.JWT_SECRET || 'checkers_secret_2025';
const ORIGIN     = process.env.ALLOWED_ORIGIN || '*';

const io = new Server(server, {
  cors: { origin: ORIGIN, methods: ['GET', 'POST'] }
});

app.use(express.json());
app.use((req, res, next) => {
  res.setHeader('Access-Control-Allow-Origin', ORIGIN);
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('X-Frame-Options', 'ALLOWALL');
  res.setHeader('Content-Security-Policy', 'frame-ancestors *');
  if (req.method === 'OPTIONS') return res.sendStatus(204);
  next();
});

// ── STOCKAGE EN MÉMOIRE ───────────────────────────────────
const users         = new Map();
const games         = new Map();
const queue         = new Map();
const socketUsers   = new Map();
const tttRooms      = new Map();
const damesRooms    = new Map();
const quoriRooms    = new Map();
const penaltyRooms  = new Map();
const chifoumiRooms = new Map();

// ── MOTEUR DAMES 10x10 (API REST legacy) ─────────────────
const EMPTY = 0, WHITE = 1, BLACK = 2, WKING = 3, BKING = 4;
const isKing  = p => p === WKING || p === BKING;
const isWhite = p => p === WHITE || p === WKING;
const isBlack = p => p === BLACK || p === BKING;
const isOwn   = (p, pl) => pl === 'white' ? isWhite(p) : isBlack(p);
const isEnemy = (p, pl) => pl === 'white' ? isBlack(p) : isWhite(p);
const inBounds = (r, c) => r >= 0 && r < 10 && c >= 0 && c < 10;
const copyB   = b => b.map(r => [...r]);

function initialBoard() {
  const b = Array.from({ length: 10 }, () => Array(10).fill(EMPTY));
  for (let r = 0; r < 4; r++)  for (let c = 0; c < 10; c++) if ((r + c) % 2 === 1) b[r][c] = BLACK;
  for (let r = 6; r < 10; r++) for (let c = 0; c < 10; c++) if ((r + c) % 2 === 1) b[r][c] = WHITE;
  return b;
}

function getSimpleMoves(r, c, b) {
  const piece = b[r][c], moves = [];
  if (!isKing(piece)) {
    const dirs = isWhite(piece) ? [[-1, -1], [-1, 1]] : [[1, -1], [1, 1]];
    for (const [dr, dc] of dirs) { const nr = r + dr, nc = c + dc; if (inBounds(nr, nc) && b[nr][nc] === EMPTY) moves.push({ to: [nr, nc], capturedPieces: [] }); }
  } else {
    for (const [dr, dc] of [[-1, -1], [-1, 1], [1, -1], [1, 1]]) { let nr = r + dr, nc = c + dc; while (inBounds(nr, nc) && b[nr][nc] === EMPTY) { moves.push({ to: [nr, nc], capturedPieces: [] }); nr += dr; nc += dc; } }
  }
  return moves;
}

function getCaptures(r, c, b, player, already = []) {
  const piece = b[r][c], results = [];
  if (!isKing(piece)) {
    for (const [dr, dc] of [[-1, -1], [-1, 1], [1, -1], [1, 1]]) {
      const mr = r + dr, mc = c + dc, lr = r + 2 * dr, lc = c + 2 * dc;
      if (!inBounds(lr, lc) || !isEnemy(b[mr][mc], player) || b[lr][lc] !== EMPTY) continue;
      const key = `${mr},${mc}`; if (already.includes(key)) continue;
      const nb = copyB(b), cp = b[mr][mc]; nb[lr][lc] = piece; nb[r][c] = EMPTY; nb[mr][mc] = EMPTY;
      const f = getCaptures(lr, lc, nb, player, [...already, key]);
      if (f.length) for (const x of f) results.push({ to: x.to, capturedPieces: [{ r: mr, c: mc, piece: cp }, ...x.capturedPieces] });
      else results.push({ to: [lr, lc], capturedPieces: [{ r: mr, c: mc, piece: cp }] });
    }
  } else {
    for (const [dr, dc] of [[-1, -1], [-1, 1], [1, -1], [1, 1]]) {
      let nr = r + dr, nc = c + dc;
      while (inBounds(nr, nc) && b[nr][nc] === EMPTY) { nr += dr; nc += dc; }
      if (!inBounds(nr, nc) || !isEnemy(b[nr][nc], player)) continue;
      const key = `${nr},${nc}`; if (already.includes(key)) continue;
      const ep = b[nr][nc]; let lr = nr + dr, lc = nc + dc;
      while (inBounds(lr, lc) && b[lr][lc] === EMPTY) {
        const nb = copyB(b); nb[lr][lc] = piece; nb[r][c] = EMPTY; nb[nr][nc] = EMPTY;
        const f = getCaptures(lr, lc, nb, player, [...already, key]);
        if (f.length) for (const x of f) results.push({ to: x.to, capturedPieces: [{ r: nr, c: nc, piece: ep }, ...x.capturedPieces] });
        else results.push({ to: [lr, lc], capturedPieces: [{ r: nr, c: nc, piece: ep }] });
        lr += dr; lc += dc;
      }
    }
  }
  return results;
}

function getAllCaptures(player, b) {
  const all = [];
  for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++)
    if (isOwn(b[r][c], player)) for (const m of getCaptures(r, c, b, player)) all.push({ from: [r, c], ...m });
  return all;
}

function hasAnyMove(player, b) {
  for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++)
    if (isOwn(b[r][c], player)) {
      if (getSimpleMoves(r, c, b).length) return true;
      if (getCaptures(r, c, b, player).length) return true;
    }
  return false;
}

function applyMove(board, player, fromR, fromC, toR, toC) {
  if (!inBounds(fromR, fromC) || !inBounds(toR, toC)) return { ok: false, reason: 'Hors limites' };
  if (!isOwn(board[fromR][fromC], player)) return { ok: false, reason: 'Pièce invalide' };
  const allCaps = getAllCaptures(player, board);
  const max = allCaps.length ? Math.max(...allCaps.map(m => m.capturedPieces.length)) : 0;
  const forced = allCaps.filter(m => m.capturedPieces.length === max && max > 0);
  let chosen = null;
  if (forced.length) {
    const mine = forced.filter(m => m.from[0] === fromR && m.from[1] === fromC);
    if (!mine.length) return { ok: false, reason: 'Capturez avec une autre pièce' };
    chosen = mine.find(m => m.to[0] === toR && m.to[1] === toC);
    if (!chosen) return { ok: false, reason: 'Capture maximale obligatoire' };
  } else {
    chosen = getSimpleMoves(fromR, fromC, board).find(m => m.to[0] === toR && m.to[1] === toC);
    if (!chosen) return { ok: false, reason: 'Mouvement illégal' };
  }
  const nb = copyB(board), piece = nb[fromR][fromC];
  nb[toR][toC] = piece; nb[fromR][fromC] = EMPTY;
  for (const cp of chosen.capturedPieces) nb[cp.r][cp.c] = EMPTY;
  let promoted = false;
  if (piece === WHITE && toR === 0) { nb[toR][toC] = WKING; promoted = true; }
  if (piece === BLACK && toR === 9) { nb[toR][toC] = BKING; promoted = true; }
  let w = 0, bl = 0;
  for (let r = 0; r < 10; r++) for (let c = 0; c < 10; c++) { if (isWhite(nb[r][c])) w++; if (isBlack(nb[r][c])) bl++; }
  let winner = null;
  if (w === 0) winner = 'black';
  else if (bl === 0) winner = 'white';
  const next = player === 'white' ? 'black' : 'white';
  if (!winner && !hasAnyMove(next, nb)) winner = player;
  return { ok: true, board: nb, captured: chosen.capturedPieces, promoted, winner, next: winner ? null : next };
}

// ── AUTH MIDDLEWARE ────────────────────────────────────────
function requireAuth(req, res, next) {
  const h = req.headers['authorization'] || '';
  if (!h.startsWith('Bearer ')) return res.status(401).json({ error: 'Token manquant' });
  try { req.userId = jwt.verify(h.slice(7), JWT_SECRET).userId; next(); }
  catch { res.status(401).json({ error: 'Token invalide' }); }
}

function emitToUser(userId, event, data) {
  for (const [sid, uid] of socketUsers.entries())
    if (uid === userId) io.to(sid).emit(event, data);
}

function calcFinancial(betAmount) {
  const bet      = betAmount || 0;
  const totalPot = bet * 2;
  const commission = Math.round(totalPot * 0.10);
  const netGain  = totalPot - commission;
  return { bet, totalPot, commission, netGain };
}

// ══════════════════════════════════════════════════════════
//  TIMERS GÉNÉRIQUES (30s de jeu + 60s de Grâce)
// ══════════════════════════════════════════════════════════
const TURN_DURATION  = 30 * 1000;
const GRACE_DURATION = 60 * 1000;

function clearDamesTurnTimers(droom) {
  if (droom.turnTimer)  { clearTimeout(droom.turnTimer);  droom.turnTimer  = null; }
  if (droom.graceTimer) { clearTimeout(droom.graceTimer); droom.graceTimer = null; }
  droom.turnStartTime = null; droom.graceStartTime = null; droom.turnPlayer = null;
}

function startDamesTurnTimer(droom, roomId, playerSlot) {
  clearDamesTurnTimers(droom);
  if (droom.status === 'finished') return;
  const now = Date.now();
  droom.turnPlayer = playerSlot; droom.turnStartTime = now; droom.graceStartTime = null;
  io.to(roomId).emit('dames_turn_start', { player: playerSlot, startTime: now, duration: TURN_DURATION });
  droom.turnTimer = setTimeout(() => {
    droom.turnTimer = null;
    if (droom.status === 'finished') return;
    const graceNow = Date.now();
    droom.graceStartTime = graceNow;
    io.to(roomId).emit('dames_turn_warning', { player: playerSlot, startTime: graceNow, duration: GRACE_DURATION });
    droom.graceTimer = setTimeout(() => {
      droom.graceTimer = null;
      if (droom.status === 'finished') return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      notifyDamesRoomOver(droom, roomId, winnerSlot, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

function clearTTTTurnTimers(troom) {
  if (troom.turnTimer)  { clearTimeout(troom.turnTimer);  troom.turnTimer  = null; }
  if (troom.graceTimer) { clearTimeout(troom.graceTimer); troom.graceTimer = null; }
  troom.turnStartTime = null; troom.graceStartTime = null; troom.turnPlayer = null;
}

function startTTTTurnTimer(troom, roomId, playerSlot) {
  clearTTTTurnTimers(troom);
  if (troom.status === 'finished') return;
  const now = Date.now();
  troom.turnPlayer = playerSlot; troom.turnStartTime = now; troom.graceStartTime = null;
  io.to(roomId).emit('ttt_turn_start', { player: playerSlot, startTime: now, duration: TURN_DURATION });
  troom.turnTimer = setTimeout(() => {
    troom.turnTimer = null;
    if (troom.status === 'finished') return;
    const graceNow = Date.now();
    troom.graceStartTime = graceNow;
    io.to(roomId).emit('ttt_turn_warning', { player: playerSlot, startTime: graceNow, duration: GRACE_DURATION });
    troom.graceTimer = setTimeout(() => {
      troom.graceTimer = null;
      if (troom.status === 'finished') return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      notifyTTTRoomOver(troom, roomId, winnerSlot, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

function clearQuoriTurnTimers(qroom) {
  if (qroom.turnTimer)  { clearTimeout(qroom.turnTimer);  qroom.turnTimer  = null; }
  if (qroom.graceTimer) { clearTimeout(qroom.graceTimer); qroom.graceTimer = null; }
  qroom.turnStartTime = null; qroom.graceStartTime = null; qroom.turnPlayer = null;
}

function startQuoriTurnTimer(qroom, roomId, playerSlot) {
  clearQuoriTurnTimers(qroom);
  if (qroom.status === 'finished') return;
  const now = Date.now();
  qroom.turnPlayer = playerSlot; qroom.turnStartTime = now; qroom.graceStartTime = null;
  io.to(roomId).emit('quoridor_turn_start', { player: playerSlot, startTime: now, duration: TURN_DURATION });
  qroom.turnTimer = setTimeout(() => {
    qroom.turnTimer = null;
    if (qroom.status === 'finished') return;
    const graceNow = Date.now();
    qroom.graceStartTime = graceNow;
    io.to(roomId).emit('quoridor_turn_warning', { player: playerSlot, startTime: graceNow, duration: GRACE_DURATION });
    qroom.graceTimer = setTimeout(() => {
      qroom.graceTimer = null;
      if (qroom.status === 'finished') return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      notifyQuoriRoomOver(qroom, roomId, winnerSlot, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// ── Penalty (15s + 60s Grace) ─────────────────────────────
const PENALTY_TURN_DURATION  = 15 * 1000;
const PENALTY_GRACE_DURATION = 60 * 1000;

function clearPenaltyTurnTimers(proom) {
  if (proom.turnTimer)  { clearTimeout(proom.turnTimer);  proom.turnTimer  = null; }
  if (proom.graceTimer) { clearTimeout(proom.graceTimer); proom.graceTimer = null; }
  proom.turnStartTime = null; proom.graceStartTime = null;
}

function startPenaltyTurnTimer(proom, roomId) {
  clearPenaltyTurnTimers(proom);
  if (proom.status === 'finished') return;
  const now = Date.now();
  proom.turnStartTime = now; proom.graceStartTime = null;
  io.to(roomId).emit('penalty_turn_start', { startTime: now, duration: PENALTY_TURN_DURATION });

  proom.turnTimer = setTimeout(() => {
    proom.turnTimer = null;
    if (proom.status === 'finished') return;

    const hp1 = proom.choices[1] !== undefined;
    const hp2 = proom.choices[2] !== undefined;

    if (hp1 && hp2) {
      resolvePenaltyRound(proom, roomId);
      return;
    }

    const graceNow = Date.now();
    proom.graceStartTime = graceNow;
    io.to(roomId).emit('penalty_turn_warning', { startTime: graceNow, duration: PENALTY_GRACE_DURATION });

    proom.graceTimer = setTimeout(() => {
      proom.graceTimer = null;
      if (proom.status === 'finished') return;

      const hp1Grace = proom.choices[1] !== undefined;
      const hp2Grace = proom.choices[2] !== undefined;

      if (!hp1Grace && !hp2Grace) {
        proom.status = 'finished';
        const { bet } = calcFinancial(proom.betAmount);
        const penalty = Math.round(bet * 0.05);
        const cp = {
          type: 'game_over', game: 'penalty', room: roomId, result: 'cancel', reason: 'both_disconnected',
          penalty, p1Id: proom.players[1]?.supabaseId, p2Id: proom.players[2]?.supabaseId,
          betAmount: bet, currency: proom.currency || 'HTG'
        };
        if (proom.players[1]?.socketId) { io.to(proom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
        if (proom.players[2]?.socketId) { io.to(proom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
        io.to(roomId).emit('game:result', { postMessage: cp });
      } else if (hp1Grace && hp2Grace) {
        resolvePenaltyRound(proom, roomId);
      } else {
        const winnerSlot = hp1Grace ? 1 : 2;
        notifyPenaltyRoomOver(proom, roomId, winnerSlot, 'timeout');
      }
    }, PENALTY_GRACE_DURATION);
  }, PENALTY_TURN_DURATION);
}

function resolvePenaltyRound(proom, roomId) {
  clearPenaltyTurnTimers(proom);
  if (proom.status === 'finished') return;

  const round = proom.currentRound;
  const shooterSlot = round % 2 === 1 ? 1 : 2;
  const keeperSlot  = shooterSlot === 1 ? 2 : 1;

  const shooterZone = proom.choices[shooterSlot]; 
  const keeperZone  = proom.choices[keeperSlot];  

  let isGoal = (shooterZone !== keeperZone);
  if (isGoal) proom.scores['p' + shooterSlot]++;

  const nextRound  = round + 1;
  const gameIsOver = nextRound > 10;

  io.to(roomId).emit('penalty_round_result', {
    p1Zone: proom.choices[1] !== undefined ? proom.choices[1] : null,
    p2Zone: proom.choices[2] !== undefined ? proom.choices[2] : null,
    isGoal, shooterSlot, keeperSlot, scores: { p1: proom.scores.p1, p2: proom.scores.p2 },
    nextRound, gameOver: gameIsOver
  });

  if (!gameIsOver) {
    proom.currentRound = nextRound;
    proom.choices      = {};
    setTimeout(() => { if (proom.status === 'playing') startPenaltyTurnTimer(proom, roomId); }, 3500);
  } else {
    // 🔥 DELAI DE 4 SECONDES POUR PERMETTRE A L'ANIMATION DU DERNIER TIR DE SE TERMINER SUR LE CLIENT
    setTimeout(() => {
        if (proom.status === 'finished') return;
        const p1Score = proom.scores.p1;
        const p2Score = proom.scores.p2;
        if (p1Score === p2Score) {
          notifyPenaltyRoomOver(proom, roomId, 0, 'draw');
        } else {
          const winnerSlot = p1Score > p2Score ? 1 : 2;
          notifyPenaltyRoomOver(proom, roomId, winnerSlot, 'normal');
        }
    }, 4000);
  }
}

// ── Chifoumi (15s + 60s Grace) ────────────────────────────
const CHIFOUMI_TURN_DURATION  = 15 * 1000;
const CHIFOUMI_GRACE_DURATION = 60 * 1000;

function clearChifoumiTurnTimers(croom) {
  if (croom.turnTimer)  { clearTimeout(croom.turnTimer);  croom.turnTimer  = null; }
  if (croom.graceTimer) { clearTimeout(croom.graceTimer); croom.graceTimer = null; }
  croom.turnStartTime = null; croom.graceStartTime = null;
}

function startChifoumiTurnTimer(croom, roomId) {
  clearChifoumiTurnTimers(croom);
  if (croom.status === 'finished') return;
  const now = Date.now();
  croom.turnStartTime = now; croom.graceStartTime = null;

  io.to(roomId).emit('chifoumi_turn_start', { startTime: now, duration: CHIFOUMI_TURN_DURATION });

  croom.turnTimer = setTimeout(() => {
    croom.turnTimer = null;
    if (croom.status === 'finished') return;

    const hp1 = croom.choices[1] !== undefined;
    const hp2 = croom.choices[2] !== undefined;

    if (hp1 && hp2) {
      return;
    }

    const graceNow = Date.now();
    croom.graceStartTime = graceNow;

    io.to(roomId).emit('chifoumi_turn_warning', { startTime: graceNow, duration: CHIFOUMI_GRACE_DURATION });

    croom.graceTimer = setTimeout(() => {
      croom.graceTimer = null;
      if (croom.status === 'finished') return;
      
      const hp1Grace = croom.choices[1] !== undefined;
      const hp2Grace = croom.choices[2] !== undefined;

      if (!hp1Grace && !hp2Grace) {
        croom.status = 'finished';
        const { bet } = calcFinancial(croom.betAmount);
        const penalty = Math.round(bet * 0.05);
        const cp = { type: 'game_over', game: 'chifoumi', room: roomId, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: croom.players[1]?.supabaseId, p2Id: croom.players[2]?.supabaseId, betAmount: bet, currency: croom.currency || 'HTG' };
        if (croom.players[1]?.socketId) { io.to(croom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(croom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
        if (croom.players[2]?.socketId) { io.to(croom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(croom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
        io.to(roomId).emit('game:result', { postMessage: cp });
      } else {
        const winnerSlot = hp1Grace ? 1 : 2;
        notifyChifoumiRoomOver(croom, roomId, winnerSlot, 'timeout');
      }
    }, CHIFOUMI_GRACE_DURATION);
  }, CHIFOUMI_TURN_DURATION);
}

// ══════════════════════════════════════════════════════════
//  PAUSE / REPRISE / ANNULATION (Sanction 5% si les deux abandonnent)
// ══════════════════════════════════════════════════════════
function pauseAndWatch({ room, roomId, gameName, getP1, getP2, winFn }) {
  if (room.disconnectTimer) return;
  room.status = 'paused';
  room.disconnectTimer = setTimeout(() => {
    if (room.status === 'finished') return;
    room.disconnectTimer = null;
    const p1 = getP1(), p2 = getP2();
    const p1back = p1?.connected === true, p2back = p2?.connected === true;
    if (p1back && p2back) { room.status = 'playing'; return; }
    if (!p1back && !p2back) {
      room.status = 'finished';
      const { bet } = calcFinancial(room.betAmount);
      const penalty = Math.round(bet * 0.05);
      const cp = {
        type: 'game_over', game: gameName, room: roomId, result: 'cancel', reason: 'both_disconnected',
        penalty, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, currency: room.currency || 'HTG',
        message: 'Les deux joueurs se sont déconnectés. Pénalité de 5% appliquée.'
      };
      if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(p1.socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
      if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(p2.socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
      io.to(roomId).emit('game:result', { postMessage: cp });
    } else {
      room.status = 'playing';
      winFn(p1back);
    }
  }, 60000);
}

// ── FIN DE PARTIES (Notifications avec gestion des Match Nuls) ──
function notifyGameOver(game, winner, reason = 'checkmate') {
  if (game.status === 'finished') return;
  game.status = 'finished'; game.winner = winner;
  if (game.disconnectTimer) { clearTimeout(game.disconnectTimer); game.disconnectTimer = null; }
  const winnerId = winner === 'white' ? game.playerWhite : game.playerBlack;
  const loserId  = winner === 'white' ? game.playerBlack : game.playerWhite;
  const wUser = users.get(winnerId), lUser = users.get(loserId);
  const { bet, totalPot, commission, netGain } = calcFinancial(game.betAmount);
  const base = { type: 'game_over', gameId: game.id, winner: winner === 'white' ? 'player1' : 'player2', winnerColor: winner, winnerName: wUser?.username, loserName: lUser?.username, winnerSupabaseId: wUser?.supabaseId, loserSupabaseId: lUser?.supabaseId, betAmount: bet, totalPot, commission, netGain, reason };
  emitToUser(winnerId, 'game:over',   { ...base, result: 'win',  myResult: +netGain });
  emitToUser(winnerId, 'game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } });
  emitToUser(loserId,  'game:over',   { ...base, result: 'loss', myResult: -bet });
  emitToUser(loserId,  'game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } });
  io.to(game.id).emit('game:over',   { ...base, result: 'win', myResult: +netGain });
  io.to(game.id).emit('game:result', { postMessage: { ...base, result: 'win', myResult: +netGain } });
}

function notifyDamesRoomOver(room, roomId, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return;
  room.status = 'finished'; clearDamesTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(room.betAmount);
  const p1 = room.players[1], p2 = room.players[2];
  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  const base = { type: 'game_over', game: 'dames', room: roomId, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId: losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: room.currency || 'HTG', reason };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win',  myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet });     io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  io.to(roomId).emit('game:over', { ...base, result: 'win', myResult: +netGain });
  io.to(roomId).emit('game:result', { postMessage: base });
}

function notifyTTTRoomOver(troom, roomId, winnerSlot, reason = 'normal') {
  if (troom.status === 'finished') return;
  troom.status = 'finished'; clearTTTTurnTimers(troom);
  if (troom.disconnectTimer) { clearTimeout(troom.disconnectTimer); troom.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(troom.betAmount);
  const p1 = troom.players[1], p2 = troom.players[2];
  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  const base = { type: 'game_over', game: 'tictactoe', room: roomId, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId: losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: troom.currency || 'HTG', reason };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win',  myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet });     io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  io.to(roomId).emit('game:over', { ...base, result: 'win', myResult: +netGain });
  io.to(roomId).emit('game:result', { postMessage: base });
}

function notifyQuoriRoomOver(qroom, roomId, winnerSlot, reason = 'normal') {
  if (qroom.status === 'finished') return;
  qroom.status = 'finished'; clearQuoriTurnTimers(qroom);
  if (qroom.disconnectTimer) { clearTimeout(qroom.disconnectTimer); qroom.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(qroom.betAmount);
  const p1 = qroom.players[1], p2 = qroom.players[2];
  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  const base = { type: 'game_over', game: 'quoridor', room: roomId, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId: losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: qroom.currency || 'HTG', reason };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win',  myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet });     io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  io.to(roomId).emit('game:over', { ...base, result: 'win', myResult: +netGain });
  io.to(roomId).emit('game:result', { postMessage: base });
}

function notifyPenaltyRoomOver(proom, roomId, winnerSlot, reason = 'normal') {
  if (proom.status === 'finished') return;
  proom.status = 'finished'; clearPenaltyTurnTimers(proom);
  if (proom.disconnectTimer) { clearTimeout(proom.disconnectTimer); proom.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(proom.betAmount);
  const p1 = proom.players[1], p2 = proom.players[2];

  if (winnerSlot === 0) {
    const base = { type: 'game_over', game: 'penalty', room: roomId, winner: 'draw', winnerSlot: 0, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission: 0, netGain: bet, currency: proom.currency || 'HTG', reason: 'draw', scores: proom.scores };
    if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p1.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p2.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    io.to(roomId).emit('game:result', { postMessage: base });
    return;
  }

  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  const base = { type: 'game_over', game: 'penalty', room: roomId, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId:  losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: proom.currency || 'HTG', reason, scores: proom.scores };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win',  myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet }); io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  io.to(roomId).emit('game:over', { ...base, result: 'win', myResult: +netGain });
  io.to(roomId).emit('game:result', { postMessage: base });
}

function notifyChifoumiRoomOver(room, roomId, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return;
  room.status = 'finished'; clearChifoumiTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(room.betAmount);
  const p1 = room.players[1], p2 = room.players[2];

  if (winnerSlot === 0) {
    const base = { type: 'game_over', game: 'chifoumi', room: roomId, winner: 'draw', winnerSlot: 0, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission: 0, netGain: bet, currency: room.currency || 'HTG', reason: 'draw', scores: room.scores };
    if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p1.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p2.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    io.to(roomId).emit('game:result', { postMessage: base });
    return;
  }

  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  const base = { type: 'game_over', game: 'chifoumi', room: roomId, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId: losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: room.currency || 'HTG', reason, scores: room.scores };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win', myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win', myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet }); io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  io.to(roomId).emit('game:over', { ...base, result: 'win', myResult: +netGain });
  io.to(roomId).emit('game:result', { postMessage: base });
}

// ══════════════════════════════════════════════════════════
//  ROUTES HTTP (Auto-Correction & Debug 404)
// ══════════════════════════════════════════════════════════
app.get('/health', (req, res) => res.json({
  status: 'ok', time: new Date().toISOString(),
  games: games.size, damesRooms: damesRooms.size,
  tttRooms: tttRooms.size, quoriRooms: quoriRooms.size,
  penaltyRooms: penaltyRooms.size, chifoumiRooms: chifoumiRooms.size,
  queue: [...queue.entries()].map(([amt, p]) => ({ betAmount: amt, waiting: p.length }))
}));

// Routeur intelligent qui liste les vrais fichiers si ça plante
const serveSmart = (possibleNames, injectRoom = false) => (req, res) => {
  let foundPath = null;
  let files = [];
  
  try {
    if (!fs.existsSync(PUBLIC)) {
      return res.status(404).send("Erreur critique : Le dossier 'public' n'existe pas sur ce serveur.");
    }

    files = fs.readdirSync(PUBLIC);

    // Cherche en ignorant la casse (majuscule/minuscule)
    for (let name of possibleNames) {
      const match = files.find(f => f.toLowerCase() === name.toLowerCase());
      if (match) {
        foundPath = path.join(PUBLIC, match);
        break;
      }
    }

    if (!foundPath) {
      return res.status(404).send(
        `<div style="font-family:sans-serif; padding: 20px; color: white; background: #1e1b4b; height: 100vh;">
          <h2 style="color:#f87171;">Fichier Introuvable (Erreur 404)</h2>
          <p>Le serveur cherche l'un de ces fichiers : <b>${possibleNames.join(', ')}</b></p>
          <hr style="border-color:#312e81;">
          <h3>Fichiers réellement vus par le serveur Render :</h3>
          <ul><li>${files.length > 0 ? files.join('</li><li>') : 'Aucun fichier (Dossier vide)'}</li></ul>
          <p style="color:#fbbf24; margin-top:20px;">💡 Si votre fichier n'est pas listé ici, c'est que Render.com n'a pas encore téléchargé la mise à jour depuis GitHub. Patientez 2 minutes.</p>
        </div>`
      );
    }
  } catch(e) {
    return res.status(500).send("Erreur de lecture du dossier public.");
  }

  let html = fs.readFileSync(foundPath, 'utf8');

  if (injectRoom) {
    const { room, p1Id, p2Id } = req.query;
    if (!room && p1Id && p2Id) {
      const ids = [p1Id, p2Id].sort();
      const generatedRoom = 'room-' + ids[0].slice(-8) + '-' + ids[1].slice(-8);
      const injection = `<script>(function(){ var u = new URL(window.location.href); if (!u.searchParams.get('room')) { u.searchParams.set('room', '${generatedRoom}'); window.history.replaceState({}, '', u.toString()); } })();</script>`;
      html = html.replace('</head>', injection + '\n</head>');
    }
  }

  res.setHeader('Content-Type', 'text/html;charset=utf-8');
  res.send(html);
};

// ── LIAISONS ROUTES ──
app.get(['/game', '/game-online.html', '/game.html'], serveSmart(['game.html', 'game-online.html']));
app.get(['/dames', '/dames.html', '/dames-online.html', '/dames_multi.html'], serveSmart(['dames_multi.html', 'dames.html', 'dames-online.html']));
app.get(['/ttt', '/ttt.html', '/ttt-online.html', '/ttt_game.html'], serveSmart(['ttt_game.html', 'ttt.html', 'ttt-online.html']));
app.get(['/quoridor', '/quoridor.html', '/quoridor-online.html', '/quoridor_multi.html'], serveSmart(['quoridor_multi.html', 'quoridor.html', 'quoridor-online.html']));
app.get(['/chifoumi', '/chifoumi.html', '/chifoumi-online.html'], serveSmart(['chifoumi-online.html', 'chifoumi.html']));
app.get(['/penalty', '/penalty.html', '/penalty_shootout.html', '/penalty-online.html', '/penalty_online.html'], serveSmart(['penalty_online.html', 'penalty_shootout.html', 'penalty-online.html', 'penalty.html'], true));

// -- REST API MATCHMAKING & AUTH --
app.post('/auth/register', (req, res) => {
  const { username, password, supabaseId } = req.body;
  if (!username || !password) return res.status(400).json({ error: 'Champs requis' });
  for (const u of users.values()) if (u.username === username) return res.status(409).json({ error: 'Nom déjà pris' });
  const id = uuid();
  users.set(id, { id, username, password: bcrypt.hashSync(password, 10), supabaseId: supabaseId || null });
  const token = jwt.sign({ userId: id }, JWT_SECRET, { expiresIn: '7d' });
  res.json({ token, userId: id, username });
});

app.post('/auth/login', (req, res) => {
  const { username, password, supabaseId } = req.body;
  const user = [...users.values()].find(u => u.username === username);
  if (!user || !bcrypt.compareSync(password, user.password)) return res.status(401).json({ error: 'Identifiants incorrects' });
  if (supabaseId) user.supabaseId = supabaseId;
  const token = jwt.sign({ userId: user.id }, JWT_SECRET, { expiresIn: '7d' });
  res.json({ token, userId: user.id, username: user.username });
});

app.post('/matchmaking/join', requireAuth, (req, res) => {
  const { betAmount, supabaseId, username } = req.body;
  if (!betAmount || betAmount <= 0) return res.status(400).json({ error: 'Montant invalide' });
  const userId = req.userId;
  let user = users.get(userId);
  if (!user) { user = { id: userId, username: username || 'Joueur', supabaseId: supabaseId || null }; users.set(userId, user); }
  else { if (username) user.username = username; if (supabaseId) user.supabaseId = supabaseId; }
  const existing = queue.get(betAmount) || [];
  if (existing.some(p => p.userId === userId)) return res.json({ status: 'waiting', message: 'En attente d\'un adversaire…' });
  const opponent = existing.find(p => p.userId !== userId);
  if (opponent) {
    queue.set(betAmount, existing.filter(p => p.userId !== opponent.userId));
    const whiteIsMe = Math.random() < 0.5;
    const whiteId = whiteIsMe ? userId : opponent.userId;
    const blackId = whiteIsMe ? opponent.userId : userId;
    const gameId  = uuid();
    games.set(gameId, { id: gameId, playerWhite: whiteId, playerBlack: blackId, board: initialBoard(), currentPlayer: 'white', status: 'playing', winner: null, betAmount, disconnectTimer: null });
    const wUser = users.get(whiteId), bUser = users.get(blackId);
    const host = `${req.protocol}://${req.get('host')}`;
    const base = { gameId, betAmount, white: { userId: whiteId, username: wUser?.username, supabaseId: wUser?.supabaseId }, black: { userId: blackId, username: bUser?.username, supabaseId: bUser?.supabaseId } };
    emitToUser(whiteId, 'match:found', { ...base, youAre: 'white', gameUrl: `${host}/game?gameId=${gameId}&player=${whiteId}` });
    emitToUser(blackId, 'match:found', { ...base, youAre: 'black', gameUrl: `${host}/game?gameId=${gameId}&player=${blackId}` });
    return res.json({ status: 'matched', gameId, youAre: whiteIsMe ? 'white' : 'black', opponent: opponent.username, betAmount, gameUrl: `${host}/game?gameId=${gameId}&player=${userId}` });
  } else {
    existing.push({ userId, username: user.username, supabaseId: user.supabaseId });
    queue.set(betAmount, existing);
    return res.json({ status: 'waiting', message: 'En attente d\'un adversaire…' });
  }
});

app.post('/matchmaking/leave', requireAuth, (req, res) => {
  const { betAmount } = req.body;
  if (betAmount) { const ex = queue.get(betAmount) || []; queue.set(betAmount, ex.filter(p => p.userId !== req.userId)); }
  else for (const [amt, pl] of queue.entries()) queue.set(amt, pl.filter(p => p.userId !== req.userId));
  res.json({ status: 'left' });
});

app.post('/game/join', requireAuth, (req, res) => {
  const { gameId, username, supabaseId, color, betAmount } = req.body;
  if (!gameId) return res.status(400).json({ error: 'gameId requis' });
  const userId = req.userId;
  let user = users.get(userId);
  if (!user) { user = { id: userId, username: username || 'Joueur', supabaseId: supabaseId || null }; users.set(userId, user); }
  else { if (username) user.username = username; if (supabaseId) user.supabaseId = supabaseId; }
  let game = games.get(gameId);
  if (!game) {
    game = { id: gameId, playerWhite: color === 'black' ? null : userId, playerBlack: color === 'black' ? userId : null, board: initialBoard(), currentPlayer: 'white', status: 'waiting', winner: null, betAmount: betAmount || 0, disconnectTimer: null };
    games.set(gameId, game);
    return res.json({ status: 'waiting', gameId, message: 'En attente du 2ème joueur…' });
  }
  if (game.status === 'playing') { const myColor = game.playerWhite === userId ? 'white' : game.playerBlack === userId ? 'black' : color || 'white'; return res.json({ status: 'ready', gameId, youAre: myColor }); }
  if (!game.playerWhite) game.playerWhite = userId; else if (!game.playerBlack) game.playerBlack = userId;
  game.status = 'playing';
  const myColor = game.playerWhite === userId ? 'white' : 'black';
  const wUser = users.get(game.playerWhite), bUser = users.get(game.playerBlack);
  const host = req.protocol + '://' + req.get('host');
  const base2 = { gameId, betAmount: game.betAmount, white: { userId: game.playerWhite, username: wUser?.username, supabaseId: wUser?.supabaseId }, black: { userId: game.playerBlack, username: bUser?.username, supabaseId: bUser?.supabaseId } };
  emitToUser(game.playerWhite, 'match:found', { ...base2, youAre: 'white', gameUrl: host + '/game?gameId=' + gameId + '&player=' + game.playerWhite });
  emitToUser(game.playerBlack, 'match:found', { ...base2, youAre: 'black', gameUrl: host + '/game?gameId=' + gameId + '&player=' + game.playerBlack });
  return res.json({ status: 'ready', gameId, youAre: myColor, opponent: myColor === 'white' ? bUser?.username : wUser?.username });
});

app.get('/games/:id', requireAuth, (req, res) => {
  const game = games.get(req.params.id);
  if (!game) return res.status(404).json({ error: 'Partie introuvable' });
  const color = game.playerWhite === req.userId ? 'white' : game.playerBlack === req.userId ? 'black' : null;
  if (!color) return res.status(403).json({ error: 'Accès refusé' });
  res.json({ gameId: game.id, board: game.board, currentPlayer: game.currentPlayer, status: game.status, winner: game.winner, betAmount: game.betAmount, youAre: color, opponentName: color === 'white' ? users.get(game.playerBlack)?.username : users.get(game.playerWhite)?.username });
});

app.post('/games/:id/move', requireAuth, (req, res) => {
  const game = games.get(req.params.id);
  if (!game || game.status !== 'playing') return res.status(400).json({ error: 'Partie non disponible' });
  const color = game.playerWhite === req.userId ? 'white' : game.playerBlack === req.userId ? 'black' : null;
  if (!color) return res.status(403).json({ error: 'Accès refusé' });
  if (game.currentPlayer !== color) return res.status(400).json({ error: 'Pas votre tour' });
  const { fromRow, fromCol, toRow, toCol } = req.body;
  const result = applyMove(game.board, color, +fromRow, +fromCol, +toRow, +toCol);
  if (!result.ok) return res.status(400).json({ error: result.reason });
  game.board = result.board; game.currentPlayer = result.winner ? null : result.next;
  const update = { gameId: game.id, board: game.board, currentPlayer: game.currentPlayer, status: game.status, winner: game.winner, lastMove: { fromRow, fromCol, toRow, toCol, captured: result.captured }, promoted: result.promoted };
  io.to(game.id).emit('game:move', update);
  if (result.winner) notifyGameOver(game, result.winner, 'checkmate');
  res.json(update);
});

app.post('/games/:id/resign', requireAuth, (req, res) => {
  const game = games.get(req.params.id);
  if (!game || game.status !== 'playing') return res.status(400).json({ error: 'Impossible' });
  const color = game.playerWhite === req.userId ? 'white' : 'black';
  notifyGameOver(game, color === 'white' ? 'black' : 'white', 'resign');
  res.json({ ok: true });
});

// ══════════════════════════════════════════════════════════
//  SOCKET.IO
// ══════════════════════════════════════════════════════════
io.on('connection', (socket) => {

  socket.on('auth', ({ token }) => {
    try { const { userId } = jwt.verify(token, JWT_SECRET); socketUsers.set(socket.id, userId); socket.userId = userId; socket.emit('auth:ok', { userId }); }
    catch { socket.emit('auth:error', { message: 'Token invalide' }); }
  });

  socket.on('auth:supabase', ({ supabaseId, username }) => {
    if (!supabaseId) return;
    let found = null;
    for (const u of users.values()) if (u.supabaseId === supabaseId) { found = u; break; }
    if (!found) { const id = uuid(); found = { id, username: username || 'Joueur', supabaseId }; users.set(id, found); }
    socketUsers.set(socket.id, found.id); socket.userId = found.id;
    const token = jwt.sign({ userId: found.id }, JWT_SECRET, { expiresIn: '7d' });
    socket.emit('auth:ok', { userId: found.id, token });
  });

  socket.on('game:join_room', ({ gameId }) => { socket.join(gameId); });

  // ══════════════════════════════════════════════════════
  //  DAMES MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('dames_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return;
    socket.join(room);
    let droom = damesRooms.get(room);
    if (!droom) {
      droom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, boardState: null, currentPlayer: 0, lastMove: null, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null };
      damesRooms.set(room, droom);
    }
    droom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !droom.betAmount) droom.betAmount = bet;

    if (droom.status === 'playing' || droom.status === 'paused') {
      const p1 = droom.players[1], p2 = droom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && droom.disconnectTimer) { clearTimeout(droom.disconnectTimer); droom.disconnectTimer = null; droom.status = 'playing'; io.to(room).emit('dames_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' }); }
      else if (droom.disconnectTimer) { droom.status = 'playing'; }
      else if (!bothBack) {
        droom.status = 'playing';
        const otherSlot = player === 1 ? 2 : 1;
        if (droom.players[otherSlot] && !droom.players[otherSlot].connected) {
          droom.disconnectTimer = setTimeout(() => {
            if (droom.status === 'finished') return;
            const p1b = droom.players[1]?.connected === true, p2b = droom.players[2]?.connected === true;
            droom.disconnectTimer = null;
            if (!p1b && !p2b) {
              droom.status = 'finished';
              const { bet: b } = calcFinancial(droom.betAmount); const penalty = Math.round(b * 0.05);
              const cp = { type: 'game_over', game: 'dames', room, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: droom.players[1]?.supabaseId, p2Id: droom.players[2]?.supabaseId, betAmount: b, currency: droom.currency || 'HTG' };
              if (droom.players[1]?.socketId) io.to(droom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty });
              if (droom.players[2]?.socketId) io.to(droom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty });
              io.to(room).emit('game:result', { postMessage: cp });
            } else { const ws = p1b ? 1 : 2; droom.status = 'playing'; notifyDamesRoomOver(droom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }
      socket.to(room).emit('dames_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (droom.players[2]?.name || 'Adversaire') : (droom.players[1]?.name || 'Adversaire');
      socket.emit('dames_start', { room, yourSlot: player, opponentName, bet: droom.betAmount, currency: droom.currency, reconnected: true, boardState: droom.boardState || null, currentPlayer: droom.currentPlayer !== undefined ? droom.currentPlayer : 0, lastMove: droom.lastMove || null });
      if (droom.turnPlayer !== null && droom.status === 'playing') {
        const now = Date.now();
        if (droom.graceStartTime) socket.emit('dames_turn_sync', { serverTime: now, turnPlayer: droom.turnPlayer, graceStartTime: droom.graceStartTime, duration: GRACE_DURATION });
        else if (droom.turnStartTime) socket.emit('dames_turn_sync', { serverTime: now, turnPlayer: droom.turnPlayer, turnStartTime: droom.turnStartTime, duration: TURN_DURATION });
      }
      return;
    }

    if (droom.players[1] && droom.players[2] && droom.status === 'waiting') {
      droom.status = 'playing';
      const p1 = droom.players[1], p2 = droom.players[2];
      io.to(p1.socketId).emit('dames_start', { room, yourSlot: 1, opponentName: p2.name, bet: droom.betAmount, currency: droom.currency, reconnected: false });
      io.to(p2.socketId).emit('dames_start', { room, yourSlot: 2, opponentName: p1.name, bet: droom.betAmount, currency: droom.currency, reconnected: false });
      setTimeout(() => { if (droom.status === 'playing') startDamesTurnTimer(droom, room, 1); }, 3000);
    }
  });

  socket.on('dames_move', ({ room, player, from, to, steps, boardState, nextPlayer, isComplete }) => {
    if (!room) return;
    const droom = damesRooms.get(room);
    if (droom) {
      if (boardState) droom.boardState = boardState;
      if (nextPlayer !== undefined) droom.currentPlayer = nextPlayer; else droom.currentPlayer = player === 1 ? 1 : 0;
      const nextSlot = nextPlayer !== undefined ? nextPlayer + 1 : (player === 1 ? 2 : 1);
      if (steps && steps.length > 0) droom.lastMove = { from: steps[0].from, to: steps[steps.length - 1].to, player };
      else if (from && to) droom.lastMove = { from, to, player };
      if (droom.status === 'playing') {
        if (isComplete === false) startDamesTurnTimer(droom, room, player);
        else startDamesTurnTimer(droom, room, nextSlot);
      }
    }
    socket.to(room).emit('dames_move', { room, player, steps: steps || [{ from, to }], boardState: boardState || null, nextPlayer: nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0), isComplete: isComplete !== false });
  });

  socket.on('dames_result', (data) => {
    const droom = damesRooms.get(data.room);
    if (!droom) return;
    const winnerSlot = data.winner === data.p1Id ? 1 : 2;
    notifyDamesRoomOver(droom, data.room, winnerSlot, data.reason || 'normal');
  });

  // ══════════════════════════════════════════════════════
  //  TTT MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('ttt_join', ({ room, player, supabaseId, name, bet, currency, manches }) => {
    if (!room) return;
    socket.join(room);
    let troom = tttRooms.get(room);
    if (!troom) {
      troom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: null, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null, totalManches: manches || 5 };
      tttRooms.set(room, troom);
    }
    troom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !troom.betAmount) troom.betAmount = bet;

    if (troom.status === 'playing' || troom.status === 'paused') {
      const p1 = troom.players[1], p2 = troom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && troom.disconnectTimer) { clearTimeout(troom.disconnectTimer); troom.disconnectTimer = null; troom.status = 'playing'; io.to(room).emit('ttt_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' }); }
      else if (troom.disconnectTimer) { troom.status = 'playing'; }
      else if (!bothBack) {
        troom.status = 'playing';
        const otherSlot = player === 1 ? 2 : 1;
        if (troom.players[otherSlot] && !troom.players[otherSlot].connected) {
          troom.disconnectTimer = setTimeout(() => {
            if (troom.status === 'finished') return;
            const p1b = troom.players[1]?.connected === true, p2b = troom.players[2]?.connected === true;
            troom.disconnectTimer = null;
            if (!p1b && !p2b) {
              troom.status = 'finished';
              const { bet: b } = calcFinancial(troom.betAmount); const penalty = Math.round(b * 0.05);
              const cp = { type: 'game_over', game: 'tictactoe', room, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: troom.players[1]?.supabaseId, p2Id: troom.players[2]?.supabaseId, betAmount: b, currency: troom.currency || 'HTG' };
              if (troom.players[1]?.socketId) { io.to(troom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(troom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              if (troom.players[2]?.socketId) { io.to(troom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(troom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              io.to(room).emit('game:result', { postMessage: cp });
            } else { const ws = p1b ? 1 : 2; troom.status = 'playing'; notifyTTTRoomOver(troom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }
      socket.to(room).emit('ttt_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (troom.players[2]?.name || 'Adversaire') : (troom.players[1]?.name || 'Adversaire');
      socket.emit('ttt_start', { room, yourSlot: player, opponentName, bet: troom.betAmount, currency: troom.currency, reconnected: true, gameState: troom.gameState || null, totalManches: troom.totalManches });
      if (troom.turnPlayer !== null && troom.status === 'playing') {
        const now = Date.now();
        if (troom.graceStartTime) socket.emit('ttt_turn_sync', { serverTime: now, turnPlayer: troom.turnPlayer, graceStartTime: troom.graceStartTime, duration: GRACE_DURATION });
        else if (troom.turnStartTime) socket.emit('ttt_turn_sync', { serverTime: now, turnPlayer: troom.turnPlayer, turnStartTime: troom.turnStartTime, duration: TURN_DURATION });
      }
      return;
    }

    if (troom.players[1] && troom.players[2] && troom.status === 'waiting') {
      troom.status = 'playing';
      const p1 = troom.players[1], p2 = troom.players[2];
      io.to(p1.socketId).emit('ttt_start', { room, yourSlot: 1, opponentName: p2.name, bet: troom.betAmount, currency: troom.currency, reconnected: false, totalManches: troom.totalManches });
      io.to(p2.socketId).emit('ttt_start', { room, yourSlot: 2, opponentName: p1.name, bet: troom.betAmount, currency: troom.currency, reconnected: false, totalManches: troom.totalManches });
      setTimeout(() => { if (troom.status === 'playing') startTTTTurnTimer(troom, room, 1); }, 3000);
    }
  });

  socket.on('ttt_move', ({ room, player, row, col, symbol, boardState, nextPlayer }) => {
    if (!room) return;
    const troom = tttRooms.get(room);
    if (troom) {
      if (boardState) { if (!troom.gameState) troom.gameState = {}; troom.gameState.board = JSON.parse(boardState); troom.gameState.currentPlayer = nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0); }
      const nextSlot = nextPlayer !== undefined ? nextPlayer + 1 : (player === 1 ? 2 : 1);
      if (troom.status === 'playing') startTTTTurnTimer(troom, room, nextSlot);
    }
    socket.to(room).emit('ttt_move', { room, player, row, col, symbol, boardState: boardState || null, nextPlayer: nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0) });
  });

  socket.on('ttt_manche_end', ({ room, player, winner, winLine, matchW, matchR, manchesDone, mancheResults, isTiebreaker, nextStarterPlayer }) => {
    if (!room) return;
    const troom = tttRooms.get(room);
    if (!troom) return;
    if (!troom.gameState) troom.gameState = {};
    troom.gameState.matchW = matchW || 0; troom.gameState.matchR = matchR || 0;
    troom.gameState.manchesDone = manchesDone || 0; troom.gameState.mancheResults = mancheResults || [];
    troom.gameState.isTiebreaker = isTiebreaker || false;
    troom.gameState.currentPlayer = nextStarterPlayer !== undefined ? nextStarterPlayer : 0;
    troom.gameState.board = [null,null,null,null,null,null,null,null,null];
    clearTTTTurnTimers(troom);
    io.to(room).emit('ttt_manche_result', { room, winner, winLine: winLine || null, matchW, matchR, manchesDone, mancheResults, isTiebreaker, nextStarterPlayer });
    setTimeout(() => {
      if (troom.status === 'playing') {
        const nextSlot = nextStarterPlayer !== undefined ? nextStarterPlayer + 1 : 1;
        startTTTTurnTimer(troom, room, nextSlot);
      }
    }, 4500);
  });

  socket.on('ttt_result', (data) => {
    const troom = tttRooms.get(data.room);
    if (!troom) return;
    const winnerSlot = data.winner === data.p1Id ? 1 : 2;
    notifyTTTRoomOver(troom, data.room, winnerSlot, data.reason || 'normal');
  });

  // ══════════════════════════════════════════════════════
  //  QUORIDOR MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('quoridor_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return;
    socket.join(room);
    let qroom = quoriRooms.get(room);
    if (!qroom) {
      qroom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: null, currentSlot: 1, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null };
      quoriRooms.set(room, qroom);
    }
    qroom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !qroom.betAmount) qroom.betAmount = bet;

    if (qroom.status === 'playing' || qroom.status === 'paused') {
      const p1 = qroom.players[1], p2 = qroom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && qroom.disconnectTimer) { clearTimeout(qroom.disconnectTimer); qroom.disconnectTimer = null; qroom.status = 'playing'; io.to(room).emit('quoridor_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' }); }
      else if (qroom.disconnectTimer) { qroom.status = 'playing'; }
      else if (!bothBack) {
        qroom.status = 'playing';
        const otherSlot = player === 1 ? 2 : 1;
        if (qroom.players[otherSlot] && !qroom.players[otherSlot].connected) {
          qroom.disconnectTimer = setTimeout(() => {
            if (qroom.status === 'finished') return;
            const p1b = qroom.players[1]?.connected === true, p2b = qroom.players[2]?.connected === true;
            qroom.disconnectTimer = null;
            if (!p1b && !p2b) {
              qroom.status = 'finished';
              const { bet: b } = calcFinancial(qroom.betAmount); const penalty = Math.round(b * 0.05);
              const cp = { type: 'game_over', game: 'quoridor', room, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: qroom.players[1]?.supabaseId, p2Id: qroom.players[2]?.supabaseId, betAmount: b, currency: qroom.currency || 'HTG' };
              if (qroom.players[1]?.socketId) { io.to(qroom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(qroom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              if (qroom.players[2]?.socketId) { io.to(qroom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(qroom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              io.to(room).emit('game:result', { postMessage: cp });
            } else { const ws = p1b ? 1 : 2; qroom.status = 'playing'; notifyQuoriRoomOver(qroom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }
      socket.to(room).emit('quoridor_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (qroom.players[2]?.name || 'Adversaire') : (qroom.players[1]?.name || 'Adversaire');
      socket.emit('quoridor_start', { room, yourSlot: player, opponentName, bet: qroom.betAmount, currency: qroom.currency, reconnected: true, gameState: qroom.gameState || null, currentSlot: qroom.currentSlot, turnPlayer: qroom.turnPlayer, turnStartTime: qroom.turnStartTime, graceStartTime: qroom.graceStartTime });
      if (qroom.turnPlayer !== null && qroom.status === 'playing') {
        const now = Date.now();
        if (qroom.graceStartTime) socket.emit('quoridor_turn_sync', { serverTime: now, turnPlayer: qroom.turnPlayer, graceStartTime: qroom.graceStartTime, duration: GRACE_DURATION });
        else if (qroom.turnStartTime) socket.emit('quoridor_turn_sync', { serverTime: now, turnPlayer: qroom.turnPlayer, turnStartTime: qroom.turnStartTime, duration: TURN_DURATION });
      }
      return;
    }

    if (qroom.players[1] && qroom.players[2] && qroom.status === 'waiting') {
      qroom.status = 'playing';
      const p1 = qroom.players[1], p2 = qroom.players[2];
      io.to(p1.socketId).emit('quoridor_start', { room, yourSlot: 1, opponentName: p2.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });
      io.to(p2.socketId).emit('quoridor_start', { room, yourSlot: 2, opponentName: p1.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });
      setTimeout(() => { if (qroom.status === 'playing') { qroom.currentSlot = 1; startQuoriTurnTimer(qroom, room, 1); } }, 3000);
    }
  });

  socket.on('quoridor_move', ({ room, player, moveType, data, gameState, nextPlayer }) => {
    if (!room) return;
    const qroom = quoriRooms.get(room);
    if (qroom) {
      if (gameState) qroom.gameState = gameState;
      const nextSlot = nextPlayer !== undefined ? nextPlayer + 1 : (player === 1 ? 2 : 1);
      qroom.currentSlot = nextSlot;
      if (qroom.status === 'playing') startQuoriTurnTimer(qroom, room, nextSlot);
    }
    socket.to(room).emit('quoridor_move', { room, player, moveType, data, gameState: gameState || null, nextPlayer: nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0) });
  });

  socket.on('quoridor_result', (data) => {
    const qroom = quoriRooms.get(data.room);
    if (!qroom) return;
    const winnerSlot = data.winner === data.p1Id ? 1 : 2;
    notifyQuoriRoomOver(qroom, data.room, winnerSlot, data.reason || 'normal');
  });

  // ══════════════════════════════════════════════════════
  //  PENALTY SHOOTOUT MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('penalty_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) { socket.emit('penalty_error', { message: 'room_id_missing', detail: 'Le paramètre room est absent.' }); return; }
    socket.join(room);
    let proom = penaltyRooms.get(room);

    if (!proom) {
      proom = {
        id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG',
        disconnectTimer: null, currentRound: 1, scores: { p1: 0, p2: 0 }, choices: {},
        turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null
      };
      penaltyRooms.set(room, proom);
    }

    proom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !proom.betAmount) proom.betAmount = bet;

    if (proom.status === 'playing' || proom.status === 'paused') {
      const p1 = proom.players[1], p2 = proom.players[2];
      const bothBack = p1?.connected && p2?.connected;

      if (bothBack && proom.disconnectTimer) {
        clearTimeout(proom.disconnectTimer); proom.disconnectTimer = null; proom.status = 'playing';
        io.to(room).emit('penalty_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
      } else if (proom.disconnectTimer) {
        proom.status = 'playing';
      } else if (!bothBack) {
        proom.status = 'playing';
        const otherSlot = player === 1 ? 2 : 1;
        if (proom.players[otherSlot] && !proom.players[otherSlot].connected) {
          proom.disconnectTimer = setTimeout(() => {
            if (proom.status === 'finished') return;
            const p1b = proom.players[1]?.connected === true;
            const p2b = proom.players[2]?.connected === true;
            proom.disconnectTimer = null;
            if (!p1b && !p2b) {
              proom.status = 'finished';
              const { bet: b } = calcFinancial(proom.betAmount); const penalty = Math.round(b * 0.05);
              const cp = { type: 'game_over', game: 'penalty', room, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: proom.players[1]?.supabaseId, p2Id: proom.players[2]?.supabaseId, betAmount: b, currency: proom.currency || 'HTG' };
              if (proom.players[1]?.socketId) { io.to(proom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              if (proom.players[2]?.socketId) { io.to(proom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              io.to(room).emit('game:result', { postMessage: cp });
            } else {
              const ws = p1b ? 1 : 2; proom.status = 'playing'; notifyPenaltyRoomOver(proom, room, ws, 'forfeit');
            }
          }, 60000);
        }
      }

      socket.to(room).emit('penalty_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (proom.players[2]?.name || 'Adversaire') : (proom.players[1]?.name || 'Adversaire');
      socket.emit('penalty_start', { room, yourSlot: player, opponentName, bet: proom.betAmount, currency: proom.currency, reconnected: true, gameState: { round: proom.currentRound, scores: proom.scores, phase: 'choosing' } });
      
      if (proom.status === 'playing') {
        const now = Date.now();
        if (proom.graceStartTime) { socket.emit('penalty_turn_sync', { serverTime: now, startTime: proom.graceStartTime, duration: PENALTY_GRACE_DURATION }); } 
        else if (proom.turnStartTime) { socket.emit('penalty_turn_sync', { serverTime: now, startTime: proom.turnStartTime, duration: PENALTY_TURN_DURATION }); }
      }
      return;
    }

    if (proom.players[1] && proom.players[2] && proom.status === 'waiting') {
      proom.status = 'playing';
      const p1 = proom.players[1], p2 = proom.players[2];
      io.to(p1.socketId).emit('penalty_start', { room, yourSlot: 1, opponentName: p2.name, bet: proom.betAmount, currency: proom.currency, reconnected: false });
      io.to(p2.socketId).emit('penalty_start', { room, yourSlot: 2, opponentName: p1.name, bet: proom.betAmount, currency: proom.currency, reconnected: false });
      setTimeout(() => { if (proom.status === 'playing') startPenaltyTurnTimer(proom, room); }, 2800);
    }
  });

  socket.on('penalty_choice', ({ room, player, round, zone }) => {
    if (!room) return;
    const proom = penaltyRooms.get(room);
    if (!proom || proom.status !== 'playing' || proom.currentRound !== round) return;
    proom.choices[player] = zone;
    socket.to(room).emit('penalty_choice_received', { player });

    if (proom.choices[1] !== undefined && proom.choices[2] !== undefined) {
      resolvePenaltyRound(proom, room);
    }
  });

  socket.on('penalty_result', (data) => {
    const proom = penaltyRooms.get(data.room);
    if (!proom) return;
    const winnerSlot = data.winner === data.p1Id ? 1 : 2;
    notifyPenaltyRoomOver(proom, data.room, winnerSlot, data.reason || 'normal');
  });

  // ══════════════════════════════════════════════════════
  //  CHIFOUMI MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('chifoumi_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return; socket.join(room);
    let croom = chifoumiRooms.get(room);
    if (!croom) {
      croom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, currentRound: 1, scores: [0, 0], choices: {}, history: [], turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null };
      chifoumiRooms.set(room, croom);
    }
    croom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !croom.betAmount) croom.betAmount = bet;

    if (croom.status === 'playing' || croom.status === 'paused') {
      const p1 = croom.players[1], p2 = croom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && croom.disconnectTimer) { clearTimeout(croom.disconnectTimer); croom.disconnectTimer = null; croom.status = 'playing'; io.to(room).emit('chifoumi_game_resumed', { message: 'Les deux joueurs sont de retour !' }); }
      else if (croom.disconnectTimer) { croom.status = 'playing'; }
      else if (!bothBack) {
        croom.status = 'playing';
        const otherSlot = player === 1 ? 2 : 1;
        if (croom.players[otherSlot] && !croom.players[otherSlot].connected) {
          croom.disconnectTimer = setTimeout(() => {
            if (croom.status === 'finished') return;
            const p1b = croom.players[1]?.connected === true, p2b = croom.players[2]?.connected === true;
            croom.disconnectTimer = null;
            if (!p1b && !p2b) {
              croom.status = 'finished';
              const { bet: b } = calcFinancial(croom.betAmount); const penalty = Math.round(b * 0.05);
              const cp = { type: 'game_over', game: 'chifoumi', room, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: croom.players[1]?.supabaseId, p2Id: croom.players[2]?.supabaseId, betAmount: b, currency: croom.currency || 'HTG' };
              if (croom.players[1]?.socketId) { io.to(croom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(croom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              if (croom.players[2]?.socketId) { io.to(croom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(croom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              io.to(room).emit('game:result', { postMessage: cp });
            } else { const ws = p1b ? 1 : 2; croom.status = 'playing'; notifyChifoumiRoomOver(croom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }
      socket.to(room).emit('chifoumi_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (croom.players[2]?.name || 'Adversaire') : (croom.players[1]?.name || 'Adversaire');
      socket.emit('chifoumi_start', { room, yourSlot: player, opponentName, bet: croom.betAmount, currency: croom.currency, reconnected: true, gameState: { scores: croom.scores, currentRound: croom.currentRound, history: croom.history } });
      
      if (croom.status === 'playing') {
        const now = Date.now();
        if (croom.graceStartTime) { socket.emit('chifoumi_turn_sync', { serverTime: now, startTime: croom.graceStartTime, duration: CHIFOUMI_GRACE_DURATION }); }
        else if (croom.turnStartTime) { socket.emit('chifoumi_turn_sync', { serverTime: now, startTime: croom.turnStartTime, duration: CHIFOUMI_TURN_DURATION }); }
      }
      return;
    }

    if (croom.players[1] && croom.players[2] && croom.status === 'waiting') {
      croom.status = 'playing'; const p1 = croom.players[1], p2 = croom.players[2];
      io.to(p1.socketId).emit('chifoumi_start', { room, yourSlot: 1, opponentName: p2.name, bet: croom.betAmount, currency: croom.currency, reconnected: false });
      io.to(p2.socketId).emit('chifoumi_start', { room, yourSlot: 2, opponentName: p1.name, bet: croom.betAmount, currency: croom.currency, reconnected: false });
      setTimeout(() => { if (croom.status === 'playing') startChifoumiTurnTimer(croom, room); }, 3000);
    }
  });

  socket.on('chifoumi_choice', ({ room, player, choice }) => {
    if (!room) return; const croom = chifoumiRooms.get(room);
    if (!croom || croom.status !== 'playing') return;
    croom.choices[player] = choice;
    socket.to(room).emit('chifoumi_opponent_choice', { choice });
    
    // Si les deux ont joué, on n'attend plus la période de grâce
    if (croom.choices[1] !== undefined && croom.choices[2] !== undefined) {
        clearChifoumiTurnTimers(croom);
    }
  });

  socket.on('chifoumi_round_start', ({ room, player, round }) => {
    const croom = chifoumiRooms.get(room);
    if (croom && croom.status === 'playing') {
      croom.currentRound = round; croom.choices = {}; startChifoumiTurnTimer(croom, room);
    }
  });

  socket.on('chifoumi_round_result', ({ room, player, round, result, playerChoice, opponentChoice }) => {
    const croom = chifoumiRooms.get(room);
    if (croom && croom.status === 'playing' && player === 1) {
       if (result === 'win') croom.scores[0]++;
       else if (result === 'lose') croom.scores[1]++;
       croom.history.push({ round, result, playerChoice, opponentChoice });
    }
  });

  socket.on('chifoumi_result', (data) => {
    const croom = chifoumiRooms.get(data.room); if (!croom) return;
    notifyChifoumiRoomOver(croom, data.room, data.winner === data.p1Id ? 1 : 2, data.reason || 'normal');
  });

  // ══════════════════════════════════════════════════════
  //  GAME:REJOIN (legacy)
  // ══════════════════════════════════════════════════════
  socket.on('game:rejoin', ({ gameId }) => {
    const game = games.get(gameId);
    if (!game) return;
    if (game.disconnectTimer) { clearTimeout(game.disconnectTimer); game.disconnectTimer = null; io.to(gameId).emit('player:reconnected', { message: 'Adversaire reconnecté !' }); }
    socket.join(gameId);
  });

  // ══════════════════════════════════════════════════════
  //  DÉCONNEXION
  // ══════════════════════════════════════════════════════
  socket.on('disconnect', () => {
    const userId = socketUsers.get(socket.id);
    socketUsers.delete(socket.id);

    // Dames API REST
    if (userId) {
      for (const [gameId, game] of games.entries()) {
        if (game.status !== 'playing') continue;
        const isWhite = game.playerWhite === userId, isBlack = game.playerBlack === userId;
        if (!isWhite && !isBlack) continue;
        if (game.disconnectTimer) continue;
        const winner = isWhite ? 'black' : 'white';
        io.to(gameId).emit('player:disconnected', { color: isWhite ? 'white' : 'black', countdown: 60, message: 'Adversaire déconnecté — victoire dans 60 secondes' });
        game.disconnectTimer = setTimeout(() => { if (game.status !== 'playing') return; notifyGameOver(game, winner, 'forfeit'); }, 60000);
        break;
      }
    }

    // Dames Multijoueur
    for (const [roomId, droom] of damesRooms.entries()) {
      if (droom.status !== 'playing' && droom.status !== 'paused') continue;
      let disconnectedSlot = null;
      for (const [slot, p] of Object.entries(droom.players)) { if (p.socketId === socket.id) { disconnectedSlot = parseInt(slot); break; } }
      if (disconnectedSlot === null) continue;
      droom.players[disconnectedSlot].connected = false;
      const dcName = droom.players[disconnectedSlot]?.name || `Joueur ${disconnectedSlot}`;
      socket.to(roomId).emit('dames_player_status', { slot: disconnectedSlot, connected: false, name: dcName });
      socket.to(roomId).emit('dames_opponent_disconnected', { slot: disconnectedSlot, message: `${dcName} s'est déconnecté.` });
      clearDamesTurnTimers(droom);
      pauseAndWatch({ room: droom, roomId, gameName: 'dames', getP1: () => droom.players[1], getP2: () => droom.players[2], winFn: (winnerIsP1) => notifyDamesRoomOver(droom, roomId, winnerIsP1 ? 1 : 2, 'forfeit') });
      break;
    }

    // TTT Multijoueur
    for (const [roomId, troom] of tttRooms.entries()) {
      if (troom.status !== 'playing' && troom.status !== 'paused') continue;
      let disconnectedSlot = null;
      for (const [slot, p] of Object.entries(troom.players)) { if (p.socketId === socket.id) { disconnectedSlot = parseInt(slot); break; } }
      if (disconnectedSlot === null) continue;
      troom.players[disconnectedSlot].connected = false;
      const dcName = troom.players[disconnectedSlot]?.name || `Joueur ${disconnectedSlot}`;
      socket.to(roomId).emit('ttt_player_status', { slot: disconnectedSlot, connected: false, name: dcName });
      socket.to(roomId).emit('ttt_opponent_disconnected', { slot: disconnectedSlot, message: `${dcName} s'est déconnecté.` });
      clearTTTTurnTimers(troom);
      pauseAndWatch({ room: troom, roomId, gameName: 'ttt', getP1: () => troom.players[1], getP2: () => troom.players[2], winFn: (winnerIsP1) => notifyTTTRoomOver(troom, roomId, winnerIsP1 ? 1 : 2, 'forfeit') });
      break;
    }

    // Quoridor Multijoueur
    for (const [roomId, qroom] of quoriRooms.entries()) {
      if (qroom.status !== 'playing' && qroom.status !== 'paused') continue;
      let disconnectedSlot = null;
      for (const [slot, p] of Object.entries(qroom.players)) { if (p.socketId === socket.id) { disconnectedSlot = parseInt(slot); break; } }
      if (disconnectedSlot === null) continue;
      qroom.players[disconnectedSlot].connected = false;
      const dcName = qroom.players[disconnectedSlot]?.name || `Joueur ${disconnectedSlot}`;
      socket.to(roomId).emit('quoridor_player_status', { slot: disconnectedSlot, connected: false, name: dcName });
      socket.to(roomId).emit('quoridor_opponent_disconnected', { slot: disconnectedSlot, message: `${dcName} s'est déconnecté.` });
      clearQuoriTurnTimers(qroom);
      pauseAndWatch({ room: qroom, roomId, gameName: 'quoridor', getP1: () => qroom.players[1], getP2: () => qroom.players[2], winFn: (winnerIsP1) => notifyQuoriRoomOver(qroom, roomId, winnerIsP1 ? 1 : 2, 'forfeit') });
      break;
    }

    // Penalty Multijoueur
    for (const [roomId, proom] of penaltyRooms.entries()) {
      if (proom.status !== 'playing' && proom.status !== 'paused') continue;
      let disconnectedSlot = null;
      for (const [slot, p] of Object.entries(proom.players)) { if (p.socketId === socket.id) { disconnectedSlot = parseInt(slot); break; } }
      if (disconnectedSlot === null) continue;
      proom.players[disconnectedSlot].connected = false;
      const dcName = proom.players[disconnectedSlot]?.name || `Joueur ${disconnectedSlot}`;
      socket.to(roomId).emit('penalty_player_status', { slot: disconnectedSlot, connected: false, name: dcName });
      socket.to(roomId).emit('penalty_opponent_disconnected', { slot: disconnectedSlot, message: `${dcName} s'est déconnecté.` });
      clearPenaltyTurnTimers(proom);
      pauseAndWatch({
        room: proom, roomId, gameName: 'penalty',
        getP1: () => proom.players[1], getP2: () => proom.players[2],
        winFn: (winnerIsP1) => notifyPenaltyRoomOver(proom, roomId, winnerIsP1 ? 1 : 2, 'forfeit')
      });
      break;
    }

    // Chifoumi Multijoueur
    for (const [roomId, croom] of chifoumiRooms.entries()) {
      if (croom.status !== 'playing' && croom.status !== 'paused') continue;
      let disconnectedSlot = null;
      for (const [slot, p] of Object.entries(croom.players)) { if (p.socketId === socket.id) { disconnectedSlot = parseInt(slot); break; } }
      if (disconnectedSlot === null) continue;
      croom.players[disconnectedSlot].connected = false;
      const dcName = croom.players[disconnectedSlot]?.name || `Joueur ${disconnectedSlot}`;
      socket.to(roomId).emit('chifoumi_player_status', { slot: disconnectedSlot, connected: false, name: dcName });
      socket.to(roomId).emit('chifoumi_opponent_disconnected', { slot: disconnectedSlot, message: `${dcName} s'est déconnecté.` });
      clearChifoumiTurnTimers(croom);
      pauseAndWatch({
        room: croom, roomId, gameName: 'chifoumi',
        getP1: () => croom.players[1], getP2: () => croom.players[2],
        winFn: (winnerIsP1) => notifyChifoumiRoomOver(croom, roomId, winnerIsP1 ? 1 : 2, 'forfeit')
      });
      break;
    }
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`✅ Serveur Nano Banana v5.5 démarré sur le port ${PORT}`);
});
