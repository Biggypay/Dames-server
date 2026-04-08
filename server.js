// ============================================================
//  SERVEUR MINDSPILLE — Socket.io + Express
//  Dames 10x10 + Tic-Tac-Toe + Quoridor — Temps réel
//  Render.com — Node 20
//  v3.5 — Quoridor multijoueur (events quoridor_*)
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
const users       = new Map();
const games       = new Map();
const queue       = new Map();
const socketUsers = new Map();
const tttRooms    = new Map();
const damesRooms  = new Map();
const quoriRooms  = new Map(); // ← NOUVEAU : Quoridor

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
//  TIMERS GÉNÉRIQUES — réutilisés par Dames, TTT et Quoridor
// ══════════════════════════════════════════════════════════
const TURN_DURATION  = 30 * 1000;
const GRACE_DURATION = 60 * 1000;

// ── Dames ─────────────────────────────────────────────────
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
    console.log(`⚠️  [dames] Tour expiré slot${playerSlot}, grâce 60s | room:${roomId}`);
    droom.graceTimer = setTimeout(() => {
      droom.graceTimer = null;
      if (droom.status === 'finished') return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      console.log(`🏳️  [dames] Grâce expirée slot${playerSlot} → forfait | room:${roomId}`);
      notifyDamesRoomOver(droom, winnerSlot, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// ── TTT ───────────────────────────────────────────────────
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
    console.log(`⚠️  [ttt] Tour expiré slot${playerSlot}, grâce 60s | room:${roomId}`);
    troom.graceTimer = setTimeout(() => {
      troom.graceTimer = null;
      if (troom.status === 'finished') return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      console.log(`🏳️  [ttt] Grâce expirée slot${playerSlot} → forfait | room:${roomId}`);
      notifyTTTRoomOver(troom, roomId, winnerSlot, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// ── Quoridor ──────────────────────────────────────────────
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
    console.log(`⚠️  [quori] Tour expiré slot${playerSlot}, grâce 60s | room:${roomId}`);
    qroom.graceTimer = setTimeout(() => {
      qroom.graceTimer = null;
      if (qroom.status === 'finished') return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      console.log(`🏳️  [quori] Grâce expirée slot${playerSlot} → forfait | room:${roomId}`);
      notifyQuoriRoomOver(qroom, roomId, winnerSlot, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// ══════════════════════════════════════════════════════════
//  PAUSE / REPRISE / ANNULATION
// ══════════════════════════════════════════════════════════
function pauseAndWatch({ room, roomId, gameName, getP1, getP2, winFn }) {
  if (room.disconnectTimer) return;
  room.status = 'paused';
  console.log(`⏸️  [${gameName}] Partie en pause | room:${roomId}`);
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
      console.log(`❌ [${gameName}] Deux absents → pénalité ${penalty} HTG | room:${roomId}`);
    } else {
      room.status = 'playing';
      winFn(p1back);
      console.log(`🏆 [${gameName}] Victoire forfait (p1:${p1back}) | room:${roomId}`);
    }
  }, 60000);
}

// ── FIN DE PARTIE DAMES API ────────────────────────────────
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
  console.log(`🏆 Dames API | ${wUser?.username} bat ${lUser?.username} | mise:${bet} pot:${totalPot} commission:${commission} gain:${netGain} HTG (${reason})`);
}

// ── FIN DE PARTIE DAMES MULTI ─────────────────────────────
function notifyDamesRoomOver(room, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return;
  room.status = 'finished';
  clearDamesTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(room.betAmount);
  const p1 = room.players[1], p2 = room.players[2];
  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  const base = { type: 'game_over', game: 'dames', room: room.id, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId: losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: room.currency || 'HTG', reason };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win',  myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet });     io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  io.to(room.id).emit('game:over', { ...base, result: 'win', myResult: +netGain });
  io.to(room.id).emit('game:result', { postMessage: base });
  console.log(`🏆 Dames Multi | Slot${winnerSlot} gagne | room:${room.id} | mise:${bet} pot:${totalPot} commission:${commission} gain:${netGain} HTG (${reason})`);
}

// ── FIN DE PARTIE TTT ─────────────────────────────────────
function notifyTTTRoomOver(troom, roomId, winnerSlot, reason = 'normal') {
  if (troom.status === 'finished') return;
  troom.status = 'finished';
  clearTTTTurnTimers(troom);
  if (troom.disconnectTimer) { clearTimeout(troom.disconnectTimer); troom.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(troom.betAmount);
  const p1 = troom.players[1], p2 = troom.players[2];
  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  const base = { type: 'game_over', game: 'tictactoe', room: roomId, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId: losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: troom.currency || 'HTG', reason };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win',  myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet });     io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  io.to(roomId).emit('game:over', { ...base, result: 'win', myResult: +netGain });
  io.to(roomId).emit('game:result', { postMessage: base });
  console.log(`🏆 TTT | Slot${winnerSlot} gagne | room:${roomId} | mise:${bet} pot:${totalPot} commission:${commission} gain:${netGain} HTG (${reason})`);
}

// ── FIN DE PARTIE QUORIDOR ────────────────────────────────
function notifyQuoriRoomOver(qroom, roomId, winnerSlot, reason = 'normal') {
  if (qroom.status === 'finished') return;
  qroom.status = 'finished';
  clearQuoriTurnTimers(qroom);
  if (qroom.disconnectTimer) { clearTimeout(qroom.disconnectTimer); qroom.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(qroom.betAmount);
  const p1 = qroom.players[1], p2 = qroom.players[2];
  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  const base = { type: 'game_over', game: 'quoridor', room: roomId, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId: losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: qroom.currency || 'HTG', reason };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win',  myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet });     io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  io.to(roomId).emit('game:over', { ...base, result: 'win', myResult: +netGain });
  io.to(roomId).emit('game:result', { postMessage: base });
  console.log(`🏆 Quoridor | Slot${winnerSlot} gagne | room:${roomId} | mise:${bet} pot:${totalPot} commission:${commission} gain:${netGain} HTG (${reason})`);
}

// ══════════════════════════════════════════════════════════
//  ROUTES
// ══════════════════════════════════════════════════════════
app.get('/health', (req, res) => res.json({
  status: 'ok', time: new Date().toISOString(),
  games: games.size, damesRooms: damesRooms.size,
  tttRooms: tttRooms.size, quoriRooms: quoriRooms.size,
  queue: [...queue.entries()].map(([amt, p]) => ({ betAmount: amt, waiting: p.length }))
}));

app.get('/game',     (req, res) => { const f = path.join(PUBLIC, 'game.html');           if (fs.existsSync(f)) { res.setHeader('Content-Type','text/html;charset=utf-8'); res.send(fs.readFileSync(f,'utf8')); } else res.status(404).send('game.html introuvable'); });
app.get('/dames',    (req, res) => { const f = path.join(PUBLIC, 'dames_multi.html');    if (fs.existsSync(f)) { res.setHeader('Content-Type','text/html;charset=utf-8'); res.send(fs.readFileSync(f,'utf8')); } else res.status(404).send('dames_multi.html introuvable'); });
app.get('/ttt',      (req, res) => { const f = path.join(PUBLIC, 'ttt_game.html');       if (fs.existsSync(f)) { res.setHeader('Content-Type','text/html;charset=utf-8'); res.send(fs.readFileSync(f,'utf8')); } else res.status(404).send('ttt_game.html introuvable'); });
app.get('/quoridor', (req, res) => { const f = path.join(PUBLIC, 'quoridor_multi.html'); if (fs.existsSync(f)) { res.setHeader('Content-Type','text/html;charset=utf-8'); res.send(fs.readFileSync(f,'utf8')); } else res.status(404).send('quoridor_multi.html introuvable'); });

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
    console.log(`✅ Match: ${wUser?.username}(⬜) vs ${bUser?.username}(⬛) — ${betAmount} HTG`);
    return res.json({ status: 'matched', gameId, youAre: whiteIsMe ? 'white' : 'black', opponent: opponent.username, betAmount, gameUrl: `${host}/game?gameId=${gameId}&player=${userId}` });
  } else {
    existing.push({ userId, username: user.username, supabaseId: user.supabaseId });
    queue.set(betAmount, existing);
    console.log(`⏳ File: ${user.username} — ${betAmount} HTG (${existing.length} en attente)`);
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
  console.log('🔌', socket.id);

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

  // ════════════════════════════════════════════════════════
  //  DAMES MULTIJOUEUR
  // ════════════════════════════════════════════════════════
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
    console.log(`♟️  Dames | Joueur ${player} (${name}) | room:${room} | statut:${droom.status}`);

    if (droom.status === 'playing' || droom.status === 'paused') {
      const p1 = droom.players[1], p2 = droom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && droom.disconnectTimer) { clearTimeout(droom.disconnectTimer); droom.disconnectTimer = null; droom.status = 'playing'; io.to(room).emit('dames_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' }); console.log(`▶️  Dames | Reprise | room:${room}`); }
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
            } else { const ws = p1b ? 1 : 2; droom.status = 'playing'; notifyDamesRoomOver(droom, ws, 'forfeit'); }
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
      console.log(`✅ Dames Multi | ${p1.name} (⬜) vs ${p2.name} (⬛) | room:${room} | mise:${droom.betAmount} ${droom.currency}`);
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
      if (droom.status === 'playing' && isComplete !== false) startDamesTurnTimer(droom, room, nextSlot);
    }
    socket.to(room).emit('dames_move', { room, player, steps: steps || [{ from, to }], boardState: boardState || null, nextPlayer: nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0), isComplete: isComplete !== false });
  });

  socket.on('dames_result', (data) => {
    const droom = damesRooms.get(data.room);
    if (!droom) return;
    const winnerSlot = data.winner === data.p1Id ? 1 : 2;
    notifyDamesRoomOver(droom, winnerSlot, data.reason || 'normal');
  });

  // ════════════════════════════════════════════════════════
  //  TTT MULTIJOUEUR
  // ════════════════════════════════════════════════════════
  socket.on('ttt_join', ({ room, player, supabaseId, name, bet, currency, manches }) => {
    if (!room) return;
    socket.join(room);

    let troom = tttRooms.get(room);
    if (!troom) {
      troom = {
        id: room, players: {}, status: 'waiting',
        betAmount: bet || 0, currency: currency || 'HTG',
        disconnectTimer: null, gameState: null,
        turnTimer: null, graceTimer: null,
        turnStartTime: null, graceStartTime: null, turnPlayer: null,
        totalManches: manches || 5,
      };
      tttRooms.set(room, troom);
    }

    troom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !troom.betAmount) troom.betAmount = bet;
    console.log(`🎮 TTT | Joueur ${player} (${name}) | room:${room} | statut:${troom.status}`);

    if (troom.status === 'playing' || troom.status === 'paused') {
      const p1 = troom.players[1], p2 = troom.players[2];
      const bothBack = p1?.connected && p2?.connected;

      if (bothBack && troom.disconnectTimer) {
        clearTimeout(troom.disconnectTimer); troom.disconnectTimer = null;
        troom.status = 'playing';
        io.to(room).emit('ttt_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
        console.log(`▶️  TTT | Reprise | room:${room}`);
      } else if (troom.disconnectTimer) {
        troom.status = 'playing';
      } else if (!bothBack) {
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
            } else {
              const ws = p1b ? 1 : 2; troom.status = 'playing'; notifyTTTRoomOver(troom, room, ws, 'forfeit');
            }
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
      console.log(`✅ TTT | ${p1.name} (X) vs ${p2.name} (O) | room:${room} | mise:${troom.betAmount} ${troom.currency}`);
      setTimeout(() => { if (troom.status === 'playing') startTTTTurnTimer(troom, room, 1); }, 3000);
    }
  });

  socket.on('ttt_move', ({ room, player, row, col, symbol, boardState, nextPlayer }) => {
    if (!room) return;
    const troom = tttRooms.get(room);
    if (troom) {
      if (boardState) {
        if (!troom.gameState) troom.gameState = {};
        troom.gameState.board = JSON.parse(boardState);
        troom.gameState.currentPlayer = nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0);
      }
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

  // ════════════════════════════════════════════════════════
  //  QUORIDOR MULTIJOUEUR
  // ════════════════════════════════════════════════════════
  socket.on('quoridor_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return;
    socket.join(room);

    let qroom = quoriRooms.get(room);
    if (!qroom) {
      qroom = {
        id: room, players: {}, status: 'waiting',
        betAmount: bet || 0, currency: currency || 'HTG',
        disconnectTimer: null,
        gameState: null,    // JSON string — état complet pour reconnexion
        currentSlot: 1,     // 1 ou 2 — qui joue
        turnTimer: null, graceTimer: null,
        turnStartTime: null, graceStartTime: null, turnPlayer: null,
      };
      quoriRooms.set(room, qroom);
    }

    qroom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    if (bet && !qroom.betAmount) qroom.betAmount = bet;
    console.log(`🔲 Quoridor | Joueur ${player} (${name}) | room:${room} | statut:${qroom.status}`);

    // ── CAS 1 : RECONNEXION ──────────────────────────────
    if (qroom.status === 'playing' || qroom.status === 'paused') {
      const p1 = qroom.players[1], p2 = qroom.players[2];
      const bothBack = p1?.connected && p2?.connected;

      if (bothBack && qroom.disconnectTimer) {
        clearTimeout(qroom.disconnectTimer); qroom.disconnectTimer = null;
        qroom.status = 'playing';
        io.to(room).emit('quoridor_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
        console.log(`▶️  Quoridor | Reprise | room:${room}`);
      } else if (qroom.disconnectTimer) {
        qroom.status = 'playing';
      } else if (!bothBack) {
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
            } else {
              const ws = p1b ? 1 : 2;
              qroom.status = 'playing';
              notifyQuoriRoomOver(qroom, room, ws, 'forfeit');
            }
          }, 60000);
        }
      }

      socket.to(room).emit('quoridor_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });

      const opponentName = player === 1 ? (qroom.players[2]?.name || 'Adversaire') : (qroom.players[1]?.name || 'Adversaire');

      // Envoyer état complet pour restauration
      const reconnectPayload = {
        room, yourSlot: player, opponentName,
        bet: qroom.betAmount, currency: qroom.currency,
        reconnected: true,
        gameState: qroom.gameState || null,
        currentSlot: qroom.currentSlot,
        turnPlayer: qroom.turnPlayer,
        turnStartTime: qroom.turnStartTime,
        graceStartTime: qroom.graceStartTime,
      };
      socket.emit('quoridor_start', reconnectPayload);

      // Resync timer
      if (qroom.turnPlayer !== null && qroom.status === 'playing') {
        const now = Date.now();
        if (qroom.graceStartTime) socket.emit('quoridor_turn_sync', { serverTime: now, turnPlayer: qroom.turnPlayer, graceStartTime: qroom.graceStartTime, duration: GRACE_DURATION });
        else if (qroom.turnStartTime) socket.emit('quoridor_turn_sync', { serverTime: now, turnPlayer: qroom.turnPlayer, turnStartTime: qroom.turnStartTime, duration: TURN_DURATION });
      }
      return;
    }

    // ── CAS 2 : PREMIÈRE CONNEXION DES DEUX JOUEURS ──────
    if (qroom.players[1] && qroom.players[2] && qroom.status === 'waiting') {
      qroom.status = 'playing';
      const p1 = qroom.players[1], p2 = qroom.players[2];

      io.to(p1.socketId).emit('quoridor_start', {
        room, yourSlot: 1, opponentName: p2.name,
        bet: qroom.betAmount, currency: qroom.currency,
        reconnected: false,
      });
      io.to(p2.socketId).emit('quoridor_start', {
        room, yourSlot: 2, opponentName: p1.name,
        bet: qroom.betAmount, currency: qroom.currency,
        reconnected: false,
      });

      console.log(`✅ Quoridor | ${p1.name} (⬜) vs ${p2.name} (🔴) | room:${room} | mise:${qroom.betAmount} ${qroom.currency}`);

      // Slot 1 (blanc) commence toujours
      setTimeout(() => {
        if (qroom.status === 'playing') {
          qroom.currentSlot = 1;
          startQuoriTurnTimer(qroom, room, 1);
        }
      }, 3000);
    }
  });

  // ── Quoridor : coup joué ───────────────────────────────
  socket.on('quoridor_move', ({ room, player, moveType, data, gameState, nextPlayer }) => {
    if (!room) return;
    const qroom = quoriRooms.get(room);

    if (qroom) {
      // Sauvegarder l'état pour reconnexion
      if (gameState) qroom.gameState = gameState;
      const nextSlot = nextPlayer !== undefined ? nextPlayer + 1 : (player === 1 ? 2 : 1);
      qroom.currentSlot = nextSlot;
      if (qroom.status === 'playing') startQuoriTurnTimer(qroom, room, nextSlot);
    }

    // Relayer à l'adversaire
    socket.to(room).emit('quoridor_move', {
      room, player, moveType, data,
      gameState: gameState || null,
      nextPlayer: nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0),
    });
  });

  // ── Quoridor : résultat final ──────────────────────────
  socket.on('quoridor_result', (data) => {
    const qroom = quoriRooms.get(data.room);
    if (!qroom) return;
    const winnerSlot = data.winner === data.p1Id ? 1 : 2;
    notifyQuoriRoomOver(qroom, data.room, winnerSlot, data.reason || 'normal');
  });

  // ════════════════════════════════════════════════════════
  //  GAME:REJOIN (legacy)
  // ════════════════════════════════════════════════════════
  socket.on('game:rejoin', ({ gameId }) => {
    const game = games.get(gameId);
    if (!game) return;
    if (game.disconnectTimer) { clearTimeout(game.disconnectTimer); game.disconnectTimer = null; io.to(gameId).emit('player:reconnected', { message: 'Adversaire reconnecté !' }); }
    socket.join(gameId);
  });

  // ════════════════════════════════════════════════════════
  //  DÉCONNEXION
  // ════════════════════════════════════════════════════════
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
      console.log(`⚠️  [dames] Joueur ${disconnectedSlot} déconnecté | room:${roomId}`);
      pauseAndWatch({ room: droom, roomId, gameName: 'dames', getP1: () => droom.players[1], getP2: () => droom.players[2], winFn: (winnerIsP1) => notifyDamesRoomOver(droom, winnerIsP1 ? 1 : 2, 'forfeit') });
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
      console.log(`⚠️  [ttt] Joueur ${disconnectedSlot} déconnecté | room:${roomId}`);
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
      console.log(`⚠️  [quori] Joueur ${disconnectedSlot} déconnecté | room:${roomId}`);
      pauseAndWatch({ room: qroom, roomId, gameName: 'quoridor', getP1: () => qroom.players[1], getP2: () => qroom.players[2], winFn: (winnerIsP1) => notifyQuoriRoomOver(qroom, roomId, winnerIsP1 ? 1 : 2, 'forfeit') });
      break;
    }

    console.log('🔌 Déconnexion:', socket.id, userId || '(non auth)');
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`✅ Serveur démarré sur le port ${PORT}`);
  console.log(`   /game             → Dames HTML (API REST legacy)`);
  console.log(`   /dames            → Dames 3D Multijoueur HTML`);
  console.log(`   /ttt              → Tic Tac Toe HTML`);
  console.log(`   /quoridor         → Quoridor Multijoueur HTML`);
  console.log(`   /matchmaking/join → matchmaking`);
  console.log(`   /health           → status`);
});
