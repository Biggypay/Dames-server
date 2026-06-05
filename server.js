// ============================================================
//  SERVEUR NANO BANANA — Socket.io + Express
//  Dames 10x10 + Tic-Tac-Toe + Quoridor + Penalty Shootout + Chifoumi
//  Temps réel — Node 20
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
const games         = new Map(); // Dames API legacy
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

// ── AUTH & FINANCE ─────────────────────────────────────────
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
//  TIMERS GÉNÉRIQUES
// ══════════════════════════════════════════════════════════
const TURN_DURATION  = 30 * 1000;
const GRACE_DURATION = 60 * 1000;

function genericClearTurnTimers(room) {
  if (room.turnTimer)  { clearTimeout(room.turnTimer);  room.turnTimer  = null; }
  if (room.graceTimer) { clearTimeout(room.graceTimer); room.graceTimer = null; }
  room.turnStartTime = null; room.graceStartTime = null; room.turnPlayer = null;
}

// (Dames)
const clearDamesTurnTimers = genericClearTurnTimers;
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
      notifyDamesRoomOver(droom, roomId, playerSlot === 1 ? 2 : 1, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// (TTT)
const clearTTTTurnTimers = genericClearTurnTimers;
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
      notifyTTTRoomOver(troom, roomId, playerSlot === 1 ? 2 : 1, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// (Quoridor)
const clearQuoriTurnTimers = genericClearTurnTimers;
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
      notifyQuoriRoomOver(qroom, roomId, playerSlot === 1 ? 2 : 1, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// (Penalty)
const PENALTY_TURN_DURATION  = 15 * 1000;
const PENALTY_GRACE_DURATION = 30 * 1000;
const clearPenaltyTurnTimers = genericClearTurnTimers;

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
    if (hp1 || hp2) { resolvePenaltyRound(proom, roomId); return; }

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
        const cp = { type: 'game_over', game: 'penalty', room: roomId, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: proom.players[1]?.supabaseId, p2Id: proom.players[2]?.supabaseId, betAmount: bet, currency: proom.currency || 'HTG' };
        if (proom.players[1]?.socketId) { io.to(proom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
        if (proom.players[2]?.socketId) { io.to(proom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
        io.to(roomId).emit('game:result', { postMessage: cp });
      } else {
        resolvePenaltyRound(proom, roomId);
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

  let isGoal;
  if (shooterZone === undefined || shooterZone === null) isGoal = false;
  else if (keeperZone === undefined || keeperZone === null) isGoal = true;
  else isGoal = (shooterZone !== keeperZone);

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
    proom.currentRound = nextRound; proom.choices = {}; proom.choicesReady = 0;
    setTimeout(() => { if (proom.status === 'playing') startPenaltyTurnTimer(proom, roomId); }, 3500);
  } else {
    const p1Score = proom.scores.p1, p2Score = proom.scores.p2;
    if (p1Score === p2Score) notifyPenaltyRoomOver(proom, roomId, 0, 'draw');
    else notifyPenaltyRoomOver(proom, roomId, p1Score > p2Score ? 1 : 2, 'normal');
  }
}

// (Chifoumi)
const CHIFOUMI_TURN_DURATION  = 16 * 1000;
const CHIFOUMI_GRACE_DURATION = 30 * 1000;
const clearChifoumiTurnTimers = genericClearTurnTimers;

function startChifoumiTurnTimer(croom, roomId) {
  clearChifoumiTurnTimers(croom);
  if (croom.status === 'finished') return;
  const now = Date.now();
  croom.turnStartTime = now; croom.graceStartTime = null;

  croom.turnTimer = setTimeout(() => {
    croom.turnTimer = null;
    if (croom.status === 'finished') return;

    const hp1 = croom.choices[1] !== undefined;
    const hp2 = croom.choices[2] !== undefined;
    if (hp1 || hp2) {
      notifyChifoumiRoomOver(croom, roomId, hp1 ? 1 : 2, 'timeout');
      return;
    }

    const graceNow = Date.now();
    croom.graceStartTime = graceNow;

    croom.graceTimer = setTimeout(() => {
      croom.graceTimer = null;
      if (croom.status === 'finished') return;
      croom.status = 'finished';
      const { bet } = calcFinancial(croom.betAmount);
      const penalty = Math.round(bet * 0.05);
      const cp = { type: 'game_over', game: 'chifoumi', room: roomId, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: croom.players[1]?.supabaseId, p2Id: croom.players[2]?.supabaseId, betAmount: bet, currency: croom.currency || 'HTG' };
      if (croom.players[1]?.socketId) { io.to(croom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(croom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
      if (croom.players[2]?.socketId) { io.to(croom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(croom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
      io.to(roomId).emit('game:result', { postMessage: cp });
    }, CHIFOUMI_GRACE_DURATION);
  }, CHIFOUMI_TURN_DURATION);
}

// ══════════════════════════════════════════════════════════
//  PAUSE / REPRISE / ANNULATION (Générique)
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
      const cp = { type: 'game_over', game: gameName, room: roomId, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, currency: room.currency || 'HTG', message: 'Les deux joueurs se sont déconnectés. Pénalité de 5% appliquée.' };
      if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(p1.socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
      if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(p2.socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
      io.to(roomId).emit('game:result', { postMessage: cp });
    } else {
      room.status = 'playing';
      winFn(p1back);
    }
  }, 60000);
}

// ── FIN DE PARTIES (Notifications unifiées) ────────────────
function generateGameEndPayload(room, roomId, gameName, winnerSlot, reason) {
  const { bet, totalPot, commission, netGain } = calcFinancial(room.betAmount);
  const p1 = room.players[1], p2 = room.players[2];
  
  if (winnerSlot === 0) {
    return { type: 'game_over', game: gameName, room: roomId, winner: 'draw', winnerSlot: 0, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission: 0, netGain: bet, currency: room.currency || 'HTG', reason: 'draw', scores: room.scores, resultObj: 'draw' };
  }

  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  return { type: 'game_over', game: gameName, room: roomId, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId: losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: room.currency || 'HTG', reason, scores: room.scores, winP, losP };
}

function broadcastGameOver(room, roomId, payload) {
  if (payload.resultObj === 'draw') {
    const { winP: _, losP: __, resultObj, ...base } = payload;
    if (room.players[1]?.socketId) { io.to(room.players[1].socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(room.players[1].socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    if (room.players[2]?.socketId) { io.to(room.players[2].socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(room.players[2].socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    io.to(roomId).emit('game:result', { postMessage: base });
  } else {
    const { winP, losP, ...base } = payload;
    if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win', myResult: +base.netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win', myResult: +base.netGain } }); }
    if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -base.betAmount }); io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -base.betAmount } }); }
    io.to(roomId).emit('game:over', { ...base, result: 'win', myResult: +base.netGain });
    io.to(roomId).emit('game:result', { postMessage: base });
  }
}

function notifyDamesRoomOver(room, roomId, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return; room.status = 'finished'; clearDamesTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  broadcastGameOver(room, roomId, generateGameEndPayload(room, roomId, 'dames', winnerSlot, reason));
}

function notifyTTTRoomOver(room, roomId, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return; room.status = 'finished'; clearTTTTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  broadcastGameOver(room, roomId, generateGameEndPayload(room, roomId, 'tictactoe', winnerSlot, reason));
}

function notifyQuoriRoomOver(room, roomId, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return; room.status = 'finished'; clearQuoriTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  broadcastGameOver(room, roomId, generateGameEndPayload(room, roomId, 'quoridor', winnerSlot, reason));
}

function notifyPenaltyRoomOver(room, roomId, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return; room.status = 'finished'; clearPenaltyTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  broadcastGameOver(room, roomId, generateGameEndPayload(room, roomId, 'penalty', winnerSlot, reason));
}

function notifyChifoumiRoomOver(room, roomId, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return; room.status = 'finished'; clearChifoumiTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  broadcastGameOver(room, roomId, generateGameEndPayload(room, roomId, 'chifoumi', winnerSlot, reason));
}

function notifyGameOverAPI(game, winner, reason = 'checkmate') {
  if (game.status === 'finished') return; game.status = 'finished'; game.winner = winner;
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

// ══════════════════════════════════════════════════════════
//  ROUTES HTTP
// ══════════════════════════════════════════════════════════
app.get('/health', (req, res) => res.json({
  status: 'ok', time: new Date().toISOString(),
  games: games.size, damesRooms: damesRooms.size,
  tttRooms: tttRooms.size, quoriRooms: quoriRooms.size,
  penaltyRooms: penaltyRooms.size, chifoumiRooms: chifoumiRooms.size,
  queue: [...queue.entries()].map(([amt, p]) => ({ betAmount: amt, waiting: p.length }))
}));

const serveHTML = (filename) => (req, res) => {
  const f = path.join(PUBLIC, filename);
  if (fs.existsSync(f)) { res.setHeader('Content-Type','text/html;charset=utf-8'); res.send(fs.readFileSync(f,'utf8')); } 
  else res.status(404).send(`${filename} introuvable`);
};

app.get('/game', serveHTML('game.html'));
app.get('/dames', serveHTML('dames_multi.html'));
app.get('/ttt', serveHTML('ttt_game.html'));
app.get('/quoridor', serveHTML('quoridor_multi.html'));

// ── CHIFOUMI — routes corrigées pour pointer vers chifoumi-online.html ──
app.get('/chifoumi', serveHTML('chifoumi-online.html'));
app.get('/chifoumi.html', serveHTML('chifoumi-online.html'));
app.get('/chifoumi-online.html', serveHTML('chifoumi-online.html'));

app.get('/penalty', (req, res) => {
  const f = path.join(PUBLIC, 'penalty_shootout.html');
  if (!fs.existsSync(f)) return res.status(404).send('penalty_shootout.html introuvable dans /public');
  let html = fs.readFileSync(f, 'utf8');
  const { room, p1Id, p2Id } = req.query;
  if (!room && p1Id && p2Id) {
    const ids = [p1Id, p2Id].sort();
    const generatedRoom = 'penalty-' + ids[0].slice(-8) + '-' + ids[1].slice(-8);
    const injection = `<script>(function(){ var u = new URL(window.location.href); if (!u.searchParams.get('room')) { u.searchParams.set('room', '${generatedRoom}'); window.history.replaceState({}, '', u.toString()); } })();</script>`;
    html = html.replace('</head>', injection + '\n</head>');
  }
  res.setHeader('Content-Type', 'text/html;charset=utf-8');
  res.send(html);
});

app.get('/penalty_shootout.html', serveHTML('penalty_shootout.html'));

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
  if (result.winner) notifyGameOverAPI(game, result.winner, 'checkmate');
  res.json(update);
});

app.post('/games/:id/resign', requireAuth, (req, res) => {
  const game = games.get(req.params.id);
  if (!game || game.status !== 'playing') return res.status(400).json({ error: 'Impossible' });
  const color = game.playerWhite === req.userId ? 'white' : 'black';
  notifyGameOverAPI(game, color === 'white' ? 'black' : 'white', 'resign');
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

  // ── HELPER DE RECONNEXION GÉNÉRIQUE ──
  function handleReconnection(roomState, room, player, name, gameName, notifyOverFn, customStartPayloadFn) {
    const p1 = roomState.players[1], p2 = roomState.players[2];
    const bothBack = p1?.connected && p2?.connected;
    if (bothBack && roomState.disconnectTimer) {
      clearTimeout(roomState.disconnectTimer); roomState.disconnectTimer = null; roomState.status = 'playing';
      io.to(room).emit(`${gameName}_game_resumed`, { message: 'Les deux joueurs sont de retour. La partie reprend !' });
    } else if (roomState.disconnectTimer) {
      roomState.status = 'playing';
    } else if (!bothBack) {
      roomState.status = 'playing';
      const otherSlot = player === 1 ? 2 : 1;
      if (roomState.players[otherSlot] && !roomState.players[otherSlot].connected) {
        roomState.disconnectTimer = setTimeout(() => {
          if (roomState.status === 'finished') return;
          const p1b = roomState.players[1]?.connected === true, p2b = roomState.players[2]?.connected === true;
          roomState.disconnectTimer = null;
          if (!p1b && !p2b) {
            roomState.status = 'finished';
            const { bet: b } = calcFinancial(roomState.betAmount); const penalty = Math.round(b * 0.05);
            const cp = { type: 'game_over', game: gameName, room, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: roomState.players[1]?.supabaseId, p2Id: roomState.players[2]?.supabaseId, betAmount: b, currency: roomState.currency || 'HTG' };
            if (roomState.players[1]?.socketId) { io.to(roomState.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(roomState.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
            if (roomState.players[2]?.socketId) { io.to(roomState.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(roomState.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
            io.to(room).emit('game:result', { postMessage: cp });
          } else { 
            const ws = p1b ? 1 : 2; roomState.status = 'playing'; notifyOverFn(roomState, room, ws, 'forfeit'); 
          }
        }, 60000);
      }
    }
    socket.to(room).emit(`${gameName}_player_status`, { slot: player, connected: true, name });
    socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
    
    const opponentName = player === 1 ? (roomState.players[2]?.name || 'Adversaire') : (roomState.players[1]?.name || 'Adversaire');
    socket.emit(`${gameName}_start`, customStartPayloadFn(opponentName));
    
    if (roomState.turnPlayer !== null && roomState.status === 'playing') {
      const now = Date.now();
      if (roomState.graceStartTime) socket.emit(`${gameName}_turn_sync`, { serverTime: now, turnPlayer: roomState.turnPlayer, startTime: roomState.graceStartTime, duration: GRACE_DURATION });
      else if (roomState.turnStartTime) socket.emit(`${gameName}_turn_sync`, { serverTime: now, turnPlayer: roomState.turnPlayer, startTime: roomState.turnStartTime, duration: TURN_DURATION });
    }
  }

  // ══════════════════════════════════════════════════════
  //  DAMES MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('dames_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return; socket.join(room);
    let droom = damesRooms.get(room);
    if (!droom) { droom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, boardState: null, currentPlayer: 0, lastMove: null, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null }; damesRooms.set(room, droom); }
    droom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !droom.betAmount) droom.betAmount = bet;

    if (droom.status === 'playing' || droom.status === 'paused') {
      handleReconnection(droom, room, player, name, 'dames', notifyDamesRoomOver, (oppName) => ({ room, yourSlot: player, opponentName: oppName, bet: droom.betAmount, currency: droom.currency, reconnected: true, boardState: droom.boardState || null, currentPlayer: droom.currentPlayer !== undefined ? droom.currentPlayer : 0, lastMove: droom.lastMove || null }));
      return;
    }

    if (droom.players[1] && droom.players[2] && droom.status === 'waiting') {
      droom.status = 'playing'; const p1 = droom.players[1], p2 = droom.players[2];
      io.to(p1.socketId).emit('dames_start', { room, yourSlot: 1, opponentName: p2.name, bet: droom.betAmount, currency: droom.currency, reconnected: false });
      io.to(p2.socketId).emit('dames_start', { room, yourSlot: 2, opponentName: p1.name, bet: droom.betAmount, currency: droom.currency, reconnected: false });
      setTimeout(() => { if (droom.status === 'playing') startDamesTurnTimer(droom, room, 1); }, 3000);
    }
  });

  socket.on('dames_move', ({ room, player, from, to, steps, boardState, nextPlayer, isComplete }) => {
    if (!room) return; const droom = damesRooms.get(room);
    if (droom) {
      if (boardState) droom.boardState = boardState;
      if (nextPlayer !== undefined) droom.currentPlayer = nextPlayer; else droom.currentPlayer = player === 1 ? 1 : 0;
      const nextSlot = nextPlayer !== undefined ? nextPlayer + 1 : (player === 1 ? 2 : 1);
      if (steps && steps.length > 0) droom.lastMove = { from: steps[0].from, to: steps[steps.length - 1].to, player };
      else if (from && to) droom.lastMove = { from, to, player };
      if (droom.status === 'playing') { if (isComplete === false) startDamesTurnTimer(droom, room, player); else startDamesTurnTimer(droom, room, nextSlot); }
    }
    socket.to(room).emit('dames_move', { room, player, steps: steps || [{ from, to }], boardState: boardState || null, nextPlayer: nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0), isComplete: isComplete !== false });
  });

  socket.on('dames_result', (data) => {
    const droom = damesRooms.get(data.room); if (!droom) return;
    notifyDamesRoomOver(droom, data.room, data.winner === data.p1Id ? 1 : 2, data.reason || 'normal');
  });

  // ══════════════════════════════════════════════════════
  //  TTT MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('ttt_join', ({ room, player, supabaseId, name, bet, currency, manches }) => {
    if (!room) return; socket.join(room);
    let troom = tttRooms.get(room);
    if (!troom) { troom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: null, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null, totalManches: manches || 5 }; tttRooms.set(room, troom); }
    troom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !troom.betAmount) troom.betAmount = bet;

    if (troom.status === 'playing' || troom.status === 'paused') {
      handleReconnection(troom, room, player, name, 'ttt', notifyTTTRoomOver, (oppName) => ({ room, yourSlot: player, opponentName: oppName, bet: troom.betAmount, currency: troom.currency, reconnected: true, gameState: troom.gameState || null, totalManches: troom.totalManches }));
      return;
    }

    if (troom.players[1] && troom.players[2] && troom.status === 'waiting') {
      troom.status = 'playing'; const p1 = troom.players[1], p2 = troom.players[2];
      io.to(p1.socketId).emit('ttt_start', { room, yourSlot: 1, opponentName: p2.name, bet: troom.betAmount, currency: troom.currency, reconnected: false, totalManches: troom.totalManches });
      io.to(p2.socketId).emit('ttt_start', { room, yourSlot: 2, opponentName: p1.name, bet: troom.betAmount, currency: troom.currency, reconnected: false, totalManches: troom.totalManches });
      setTimeout(() => { if (troom.status === 'playing') startTTTTurnTimer(troom, room, 1); }, 3000);
    }
  });

  socket.on('ttt_move', ({ room, player, row, col, symbol, boardState, nextPlayer }) => {
    if (!room) return; const troom = tttRooms.get(room);
    if (troom) {
      if (boardState) { if (!troom.gameState) troom.gameState = {}; troom.gameState.board = JSON.parse(boardState); troom.gameState.currentPlayer = nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0); }
      const nextSlot = nextPlayer !== undefined ? nextPlayer + 1 : (player === 1 ? 2 : 1);
      if (troom.status === 'playing') startTTTTurnTimer(troom, room, nextSlot);
    }
    socket.to(room).emit('ttt_move', { room, player, row, col, symbol, boardState: boardState || null, nextPlayer: nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0) });
  });

  socket.on('ttt_manche_end', ({ room, player, winner, winLine, matchW, matchR, manchesDone, mancheResults, isTiebreaker, nextStarterPlayer }) => {
    if (!room) return; const troom = tttRooms.get(room); if (!troom) return;
    if (!troom.gameState) troom.gameState = {};
    troom.gameState.matchW = matchW || 0; troom.gameState.matchR = matchR || 0;
    troom.gameState.manchesDone = manchesDone || 0; troom.gameState.mancheResults = mancheResults || [];
    troom.gameState.isTiebreaker = isTiebreaker || false; troom.gameState.currentPlayer = nextStarterPlayer !== undefined ? nextStarterPlayer : 0;
    troom.gameState.board = [null,null,null,null,null,null,null,null,null];
    clearTTTTurnTimers(troom);
    io.to(room).emit('ttt_manche_result', { room, winner, winLine: winLine || null, matchW, matchR, manchesDone, mancheResults, isTiebreaker, nextStarterPlayer });
    setTimeout(() => { if (troom.status === 'playing') { const nextSlot = nextStarterPlayer !== undefined ? nextStarterPlayer + 1 : 1; startTTTTurnTimer(troom, room, nextSlot); } }, 4500);
  });

  socket.on('ttt_result', (data) => {
    const troom = tttRooms.get(data.room); if (!troom) return;
    notifyTTTRoomOver(troom, data.room, data.winner === data.p1Id ? 1 : 2, data.reason || 'normal');
  });

  // ══════════════════════════════════════════════════════
  //  QUORIDOR MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('quoridor_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return; socket.join(room);
    let qroom = quoriRooms.get(room);
    if (!qroom) { qroom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: null, currentSlot: 1, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null }; quoriRooms.set(room, qroom); }
    qroom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !qroom.betAmount) qroom.betAmount = bet;

    if (qroom.status === 'playing' || qroom.status === 'paused') {
      handleReconnection(qroom, room, player, name, 'quoridor', notifyQuoriRoomOver, (oppName) => ({ room, yourSlot: player, opponentName: oppName, bet: qroom.betAmount, currency: qroom.currency, reconnected: true, gameState: qroom.gameState || null, currentSlot: qroom.currentSlot, turnPlayer: qroom.turnPlayer, turnStartTime: qroom.turnStartTime, graceStartTime: qroom.graceStartTime }));
      return;
    }

    if (qroom.players[1] && qroom.players[2] && qroom.status === 'waiting') {
      qroom.status = 'playing'; const p1 = qroom.players[1], p2 = qroom.players[2];
      io.to(p1.socketId).emit('quoridor_start', { room, yourSlot: 1, opponentName: p2.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });
      io.to(p2.socketId).emit('quoridor_start', { room, yourSlot: 2, opponentName: p1.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });
      setTimeout(() => { if (qroom.status === 'playing') { qroom.currentSlot = 1; startQuoriTurnTimer(qroom, room, 1); } }, 3000);
    }
  });

  socket.on('quoridor_move', ({ room, player, moveType, data, gameState, nextPlayer }) => {
    if (!room) return; const qroom = quoriRooms.get(room);
    if (qroom) {
      if (gameState) qroom.gameState = gameState;
      const nextSlot = nextPlayer !== undefined ? nextPlayer + 1 : (player === 1 ? 2 : 1);
      qroom.currentSlot = nextSlot;
      if (qroom.status === 'playing') startQuoriTurnTimer(qroom, room, nextSlot);
    }
    socket.to(room).emit('quoridor_move', { room, player, moveType, data, gameState: gameState || null, nextPlayer: nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0) });
  });

  socket.on('quoridor_result', (data) => {
    const qroom = quoriRooms.get(data.room); if (!qroom) return;
    notifyQuoriRoomOver(qroom, data.room, data.winner === data.p1Id ? 1 : 2, data.reason || 'normal');
  });

  // ══════════════════════════════════════════════════════
  //  PENALTY SHOOTOUT MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('penalty_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return; socket.join(room);
    let proom = penaltyRooms.get(room);
    if (!proom) { proom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, currentRound: 1, scores: { p1: 0, p2: 0 }, choices: {}, choicesReady: 0, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null }; penaltyRooms.set(room, proom); }
    proom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !proom.betAmount) proom.betAmount = bet;

    if (proom.status === 'playing' || proom.status === 'paused') {
      handleReconnection(proom, room, player, name, 'penalty', notifyPenaltyRoomOver, (oppName) => ({ room, yourSlot: player, opponentName: oppName, bet: proom.betAmount, currency: proom.currency, reconnected: true, gameState: { round: proom.currentRound, scores: proom.scores, phase: 'choosing' } }));
      return;
    }

    if (proom.players[1] && proom.players[2] && proom.status === 'waiting') {
      proom.status = 'playing'; const p1 = proom.players[1], p2 = proom.players[2];
      io.to(p1.socketId).emit('penalty_start', { room, yourSlot: 1, opponentName: p2.name, bet: proom.betAmount, currency: proom.currency, reconnected: false });
      io.to(p2.socketId).emit('penalty_start', { room, yourSlot: 2, opponentName: p1.name, bet: proom.betAmount, currency: proom.currency, reconnected: false });
      setTimeout(() => { if (proom.status === 'playing') startPenaltyTurnTimer(proom, room); }, 2800);
    }
  });

  socket.on('penalty_choice', ({ room, player, round, zone }) => {
    if (!room) return; const proom = penaltyRooms.get(room);
    if (!proom || proom.status !== 'playing' || proom.currentRound !== round) return;
    proom.choices[player] = zone;
    socket.to(room).emit('penalty_choice_received', { player });
    if (proom.choices[1] !== undefined && proom.choices[2] !== undefined) resolvePenaltyRound(proom, room);
  });

  socket.on('penalty_result', (data) => {
    const proom = penaltyRooms.get(data.room); if (!proom) return;
    notifyPenaltyRoomOver(proom, data.room, data.winner === data.p1Id ? 1 : 2, data.reason || 'normal');
  });

  // ══════════════════════════════════════════════════════
  //  CHIFOUMI MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('chifoumi_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return; socket.join(room);
    let croom = chifoumiRooms.get(room);
    
    if (!croom) {
      croom = { 
        id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', 
        disconnectTimer: null, currentRound: 1, scores: [0, 0], choices: {}, history: [],
        turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null 
      };
      chifoumiRooms.set(room, croom);
    }
    
    croom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !croom.betAmount) croom.betAmount = bet;

    if (croom.status === 'playing' || croom.status === 'paused') {
      handleReconnection(croom, room, player, name, 'chifoumi', notifyChifoumiRoomOver, (oppName) => ({
        room, yourSlot: player, opponentName: oppName, bet: croom.betAmount, currency: croom.currency,
        reconnected: true, gameState: { scores: croom.scores, currentRound: croom.currentRound, history: croom.history }
      }));
      return;
    }

    if (croom.players[1] && croom.players[2] && croom.status === 'waiting') {
      croom.status = 'playing'; const p1 = croom.players[1], p2 = croom.players[2];
      io.to(p1.socketId).emit('chifoumi_start', { room, yourSlot: 1, opponentName: p2.name, bet: croom.betAmount, currency: croom.currency, reconnected: false });
      io.to(p2.socketId).emit('chifoumi_start', { room, yourSlot: 2, opponentName: p1.name, bet: croom.betAmount, currency: croom.currency, reconnected: false });
      setTimeout(() => { if (croom.status === 'playing') startChifoumiTurnTimer(croom, room); }, 3000);
    }
  });

  socket.on('chifoumi_choice', ({ room, player, choice, isTimeout }) => {
    if (!room) return; const croom = chifoumiRooms.get(room);
    if (!croom || croom.status !== 'playing') return;
    
    croom.choices[player] = choice;
    socket.to(room).emit('chifoumi_opponent_choice', { choice });

    if (croom.choices[1] && croom.choices[2]) {
      clearChifoumiTurnTimers(croom);
    }
  });

  socket.on('chifoumi_round_start', ({ room, player, round }) => {
    const croom = chifoumiRooms.get(room);
    if (croom && croom.status === 'playing') {
      croom.currentRound = round;
      croom.choices = {};
      startChifoumiTurnTimer(croom, room);
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

    if (userId) {
      for (const [gameId, game] of games.entries()) {
        if (game.status !== 'playing') continue;
        const isWhite = game.playerWhite === userId, isBlack = game.playerBlack === userId;
        if (!isWhite && !isBlack) continue;
        if (game.disconnectTimer) continue;
        const winner = isWhite ? 'black' : 'white';
        io.to(gameId).emit('player:disconnected', { color: isWhite ? 'white' : 'black', countdown: 60, message: 'Adversaire déconnecté — victoire dans 60 secondes' });
        game.disconnectTimer = setTimeout(() => { if (game.status !== 'playing') return; notifyGameOverAPI(game, winner, 'forfeit'); }, 60000);
        break;
      }
    }

    const processDisconnect = (roomsMap, gameName, clearTimersFn, notifyOverFn) => {
      for (const [roomId, roomState] of roomsMap.entries()) {
        if (roomState.status !== 'playing' && roomState.status !== 'paused') continue;
        let disconnectedSlot = null;
        for (const [slot, p] of Object.entries(roomState.players)) { if (p.socketId === socket.id) { disconnectedSlot = parseInt(slot); break; } }
        if (disconnectedSlot === null) continue;
        
        roomState.players[disconnectedSlot].connected = false;
        const dcName = roomState.players[disconnectedSlot]?.name || `Joueur ${disconnectedSlot}`;
        socket.to(roomId).emit(`${gameName}_player_status`, { slot: disconnectedSlot, connected: false, name: dcName });
        socket.to(roomId).emit(`${gameName}_opponent_disconnected`, { slot: disconnectedSlot, message: `${dcName} s'est déconnecté.` });
        
        clearTimersFn(roomState);
        pauseAndWatch({ 
          room: roomState, roomId, gameName, 
          getP1: () => roomState.players[1], getP2: () => roomState.players[2], 
          winFn: (winnerIsP1) => notifyOverFn(roomState, roomId, winnerIsP1 ? 1 : 2, 'forfeit') 
        });
        return true;
      }
      return false;
    };

    if (processDisconnect(damesRooms, 'dames', clearDamesTurnTimers, notifyDamesRoomOver)) return;
    if (processDisconnect(tttRooms, 'ttt', clearTTTTurnTimers, notifyTTTRoomOver)) return;
    if (processDisconnect(quoriRooms, 'quoridor', clearQuoriTurnTimers, notifyQuoriRoomOver)) return;
    if (processDisconnect(penaltyRooms, 'penalty', clearPenaltyTurnTimers, notifyPenaltyRoomOver)) return;
    if (processDisconnect(chifoumiRooms, 'chifoumi', clearChifoumiTurnTimers, notifyChifoumiRoomOver)) return;
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`✅ Serveur Nano Banana v5.2 démarré sur le port ${PORT}`);
  console.log(`   /game                  → Dames HTML (API REST legacy)`);
  console.log(`   /dames                 → Dames 3D Multijoueur HTML`);
  console.log(`   /ttt                   → Tic Tac Toe HTML`);
  console.log(`   /quoridor              → Quoridor Multijoueur HTML`);
  console.log(`   /penalty               → Penalty Shootout Multijoueur HTML`);
  console.log(`   /chifoumi              → Chifoumi Multijoueur HTML`);
  console.log(`   /chifoumi-online.html  → Chifoumi (alias direct)`);
  console.log(`   /matchmaking/join      → matchmaking`);
  console.log(`   /health                → status`);
});
