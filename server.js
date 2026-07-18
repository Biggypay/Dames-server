// ============================================================
//  SERVEUR NANO BANANA — Socket.io + Express
//  Dames 10x10 + Tic-Tac-Toe + Quoridor + Penalty Shootout + Chifoumi
//  Temps réel — Node 20
//  v5.6 — Résolution du bug critique d'égalité (Match Nul)
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
const crypto     = require('crypto');
const PORT       = process.env.PORT || 3000;

// ── SÉCURITÉ : secret JWT ──────────────────────────────────
// Ne JAMAIS utiliser un secret par défaut connu (il permettrait de forger des jetons
// pour n'importe quel joueur). À défaut de JWT_SECRET, on génère un secret aléatoire.
const JWT_SECRET = process.env.JWT_SECRET || crypto.randomBytes(48).toString('hex');
if (!process.env.JWT_SECRET) {
  console.warn('⚠️  JWT_SECRET absent : un secret aléatoire a été généré (les jetons ne survivront pas à un redémarrage). Définissez JWT_SECRET dans Render pour la production.');
}
const ORIGIN          = process.env.ALLOWED_ORIGIN || '*';
const ALLOWED_ORIGINS = ORIGIN === '*' ? '*' : ORIGIN.split(',').map(origin => origin.trim()).filter(Boolean);

// Autorise les origines configurées + tout sous-domaine *.lovable.app
// (site publié, aperçu id-preview--..., remix, PWA installée) : l'appli
// MindSpille tourne sur lovable.app et doit pouvoir interroger /health,
// ouvrir les sockets et intégrer les jeux en iframe.
const LOVABLE_ORIGIN_RE = /^https:\/\/[a-z0-9-]+\.lovable\.app$/i;
function isAllowedOrigin(origin) {
  if (!origin) return false;
  if (ALLOWED_ORIGINS === '*') return true;
  if (Array.isArray(ALLOWED_ORIGINS) && ALLOWED_ORIGINS.includes(origin)) return true;
  return LOVABLE_ORIGIN_RE.test(origin);
}
const SUPABASE_URL = String(process.env.SUPABASE_URL || '').replace(/\/$/, '');
const SUPABASE_PUBLISHABLE_KEY = process.env.SUPABASE_PUBLISHABLE_KEY || process.env.SUPABASE_ANON_KEY || '';
// Never expose this key to a browser. It is used only to settle a game that
// has already been validated by this process.
const SUPABASE_SERVICE_ROLE_KEY = process.env.SUPABASE_SERVICE_ROLE_KEY || '';
const LEGACY_LOCAL_AUTH = process.env.ALLOW_LEGACY_LOCAL_AUTH === 'true' || process.env.NODE_ENV !== 'production';
if (process.env.NODE_ENV === 'production' && (!process.env.JWT_SECRET || !SUPABASE_URL || !SUPABASE_PUBLISHABLE_KEY || !SUPABASE_SERVICE_ROLE_KEY || ORIGIN === '*' || (process.env.FRAME_ANCESTORS || '*') === '*')) {
  throw new Error('Production requires JWT_SECRET, SUPABASE_URL, SUPABASE_PUBLISHABLE_KEY, SUPABASE_SERVICE_ROLE_KEY, ALLOWED_ORIGIN and FRAME_ANCESTORS. See .env.example.');
}
// Origines autorisées à embarquer le jeu en iframe (Lovable / domaine live). '*' = permissif.
const FRAME_ANCESTORS = process.env.FRAME_ANCESTORS || '*';

const io = new Server(server, {
  cors: { origin: (origin, cb) => cb(null, ALLOWED_ORIGINS === '*' || !origin || isAllowedOrigin(origin)), methods: ['GET', 'POST'] },
  maxHttpBufferSize: 1e5   // 100 KB max par message socket (anti-flood mémoire)
});

app.disable('x-powered-by');
app.use(express.json({ limit: '64kb' }));   // limite la taille des corps de requête
app.use((req, res, next) => {
  const requestOrigin = req.headers.origin;
  if (ALLOWED_ORIGINS === '*') {
    res.setHeader('Access-Control-Allow-Origin', '*');
  } else if (requestOrigin && isAllowedOrigin(requestOrigin)) {
    res.setHeader('Access-Control-Allow-Origin', requestOrigin);
    res.setHeader('Vary', 'Origin');
  }
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  // On garde frame-ancestors permissif pour l'iframe Lovable, mais on ajoute les autres protections.
  res.setHeader('X-Frame-Options', 'ALLOWALL');
  res.setHeader('Content-Security-Policy', 'frame-ancestors ' + FRAME_ANCESTORS + ' https://*.lovable.app');
  res.setHeader('X-Content-Type-Options', 'nosniff');
  res.setHeader('Referrer-Policy', 'no-referrer');
  res.setHeader('Permissions-Policy', 'geolocation=(), microphone=(), camera=()');
  res.setHeader('Strict-Transport-Security', 'max-age=31536000; includeSubDomains');
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

// ══════════════════════════════════════════════════════════
//  SÉCURITÉ — limiteur de débit, validation, anti-fraude
// ══════════════════════════════════════════════════════════
const rlStore = new Map(); // clé -> { count, resetAt }
function rateLimit(key, max, windowMs) {
  const now = Date.now();
  let e = rlStore.get(key);
  if (!e || now > e.resetAt) { e = { count: 0, resetAt: now + windowMs }; rlStore.set(key, e); }
  e.count++;
  return e.count <= max;
}
const _rlSweep = setInterval(() => {
  const now = Date.now();
  for (const [k, e] of rlStore) if (now > e.resetAt) rlStore.delete(k);
}, 60000);
if (_rlSweep.unref) _rlSweep.unref();

function clientIp(req) {
  const xf = String(req.headers['x-forwarded-for'] || '').split(',')[0].trim();
  return xf || (req.socket && req.socket.remoteAddress) || 'unknown';
}
// Un identifiant de room valide (anti-injection de room / abus)
function validRoom(r) { return typeof r === 'string' && r.length > 0 && r.length <= 100 && /^[\w:.\-]+$/.test(r); }
function isUuid(value) { return typeof value === 'string' && /^[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$/i.test(value); }
// Raison de fin normalisée (on n'accepte pas une chaîne arbitraire du client)
function safeReason(r) { return ['normal','forfeit','timeout','draw','resign','checkmate','both_disconnected'].includes(r) ? r : 'normal'; }

// ANTI-SPOOF DE RÉSULTAT : le socket qui émet doit être un joueur RÉEL de la room.
function socketIsPlayer(room, socketId) {
  return !!(room && room.players && (
    (room.players[1] && room.players[1].socketId === socketId) ||
    (room.players[2] && room.players[2].socketId === socketId)
  ));
}
// Le gagnant déclaré doit correspondre à un joueur RÉEL de la room (selon le serveur),
// sinon 0 (nul) : impossible de créditer un compte qui ne joue pas dans cette room.
function resolveWinnerSlot(room, data) {
  if (!data || data.result === 'draw' || data.winner === 'draw' || !data.winner) return 0;
  const s1 = room.players[1] && room.players[1].supabaseId;
  const s2 = room.players[2] && room.players[2].supabaseId;
  if (s1 && data.winner === s1) return 1;
  if (s2 && data.winner === s2) return 2;
  return 0;
}

// Dames, Tic-Tac-Toe and Quoridor still render their move engines in the
// browser. Until their engines are fully moved server-side, a normal result
// must be corroborated by both players; one browser can never settle alone.
function consensusResult(room, socket, data) {
  const reason = safeReason(data.reason);
  if (reason !== 'normal' && reason !== 'draw') return null;
  const slot = room.players[1]?.socketId === socket.id ? 1 : room.players[2]?.socketId === socket.id ? 2 : 0;
  if (!slot) return null;
  const proposal = { winnerSlot: resolveWinnerSlot(room, data), reason };
  room.pendingResults = room.pendingResults || {};
  room.pendingResults[slot] = proposal;
  const other = room.pendingResults[slot === 1 ? 2 : 1];
  if (!other) return null;
  if (other.winnerSlot !== proposal.winnerSlot || other.reason !== proposal.reason) {
    io.to(room.players[1]?.socketId).emit('game:error', { message: 'Resultats des joueurs incoherents. La partie reste active.' });
    io.to(room.players[2]?.socketId).emit('game:error', { message: 'Resultats des joueurs incoherents. La partie reste active.' });
    return null;
  }
  return proposal;
}
// Limiteur d'événements socket sensibles (anti-flood ciblé)
function socketAllow(socketId, tag, max, windowMs) { return rateLimit('sock:' + tag + ':' + socketId, max, windowMs); }

function validPlayerSlot(slot) { return slot === 1 || slot === 2; }
function safeName(value, fallback = 'Joueur') {
  const name = typeof value === 'string' ? value.trim().slice(0, 40) : '';
  return name || fallback;
}
function authenticatedSocketUser(socket) {
  return socket && socket.userId ? users.get(socket.userId) || null : null;
}
function rejectSocket(socket, message) {
  socket.emit('game:error', { message });
  return null;
}
function bindDatabaseGame(room, gameId) {
  if (!isUuid(gameId)) return true; // Legacy rooms may not have a database game yet.
  if (room.databaseGameId && room.databaseGameId !== gameId) return false;
  room.databaseGameId = gameId;
  return true;
}

const DB_GAME_TYPES = { dames: 'checkers', tictactoe: 'tictactoe', quoridor: 'quoridor', penalty: 'penalty_shootout', chifoumi: 'rock_paper_scissors' };
function databaseResult(winnerSlot, reason) {
  if (winnerSlot === 0) return reason === 'both_disconnected' || reason === 'mutual_quit' ? 'mutual_quit' : 'draw';
  return reason === 'timeout' ? 'timeout' : 'win';
}
async function settleRoomInSupabase(room, game, winnerSlot, reason) {
  if (room.settlementPromise) return room.settlementPromise;
  if (!room.databaseGameId) {
    console.error('[settlement] Missing games.id for room', room.id);
    return null;
  }
  if (!SUPABASE_URL || !SUPABASE_SERVICE_ROLE_KEY) {
    console.error('[settlement] SUPABASE_SERVICE_ROLE_KEY is not configured; refusing browser settlement.');
    return null;
  }
  const p1 = room.players[1]?.supabaseId, p2 = room.players[2]?.supabaseId;
  if (!isUuid(p1) || !isUuid(p2)) {
    console.error('[settlement] Invalid room participants for', room.id);
    return null;
  }
  room.settlementPromise = (async () => {
    const headers = { apikey: SUPABASE_SERVICE_ROLE_KEY, Authorization: 'Bearer ' + SUPABASE_SERVICE_ROLE_KEY, 'Content-Type': 'application/json' };
    const gameId = encodeURIComponent(room.databaseGameId);
    const lookup = await fetch(SUPABASE_URL + '/rest/v1/games?id=eq.' + gameId + '&select=id,game_type,player1_id,player2_id,bet_amount,status', { headers });
    if (!lookup.ok) throw new Error('Cannot verify database game: ' + lookup.status);
    const rows = await lookup.json();
    const dbGame = Array.isArray(rows) ? rows[0] : null;
    const samePlayers = dbGame && dbGame.player1_id === p1 && dbGame.player2_id === p2;
    const expectedType = DB_GAME_TYPES[game];
    const sameBet = dbGame && Math.abs(Number(dbGame.bet_amount || 0) - Number(room.betAmount || 0)) < 0.0001;
    if (!samePlayers || dbGame.game_type !== expectedType || !sameBet) throw new Error('Database game does not match authenticated room');
    const startedAt = Number(room.startedAt || Date.now());
    const payload = {
      p_game_id: room.databaseGameId,
      p_status: 'completed',
      p_result: databaseResult(winnerSlot, reason),
      p_winner_id: winnerSlot ? room.players[winnerSlot].supabaseId : null,
      p_platform_fee: winnerSlot ? Number(room.betAmount || 0) * 0.2 : 0,
      p_duration_seconds: Math.max(0, Math.floor((Date.now() - startedAt) / 1000))
    };
    const settled = await fetch(SUPABASE_URL + '/rest/v1/rpc/submit_game_result', { method: 'POST', headers, body: JSON.stringify(payload) });
    if (!settled.ok) throw new Error('Settlement RPC failed: ' + settled.status + ' ' + (await settled.text()).slice(0, 400));
    room.settledAt = Date.now();
    console.info('[settlement] completed', room.databaseGameId, game, payload.p_result);
  })().catch(error => {
    room.settlementPromise = null; // An operator may retry only after investigating server logs.
    console.error('[settlement] failed', room.databaseGameId, error.message);
    io.to(room.id).emit('game:error', { message: 'Résultat validé, mais synchronisation portefeuille en attente. Ne relancez pas la partie.' });
  });
  return room.settlementPromise;
}
// A room slot belongs to the authenticated player only. Reconnecting with the
// same account is allowed; replacing another player is not.
function joinRoomAsAuthenticatedPlayer(socket, roomState, roomId, player, claimedSupabaseId, claimedName) {
  if (!validRoom(roomId) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
  const user = authenticatedSocketUser(socket);
  if (!user || !user.supabaseId) return rejectSocket(socket, 'Authentification requise.');
  if (claimedSupabaseId && claimedSupabaseId !== user.supabaseId) return rejectSocket(socket, 'Identité de joueur invalide.');
  const other = roomState.players[player === 1 ? 2 : 1];
  if (other && other.userId === user.id) return rejectSocket(socket, 'Un joueur ne peut pas occuper les deux places.');
  const existing = roomState.players[player];
  if (existing && existing.userId !== user.id) return rejectSocket(socket, 'Cette place est déjà occupée.');
  roomState.players[player] = {
    socketId: socket.id,
    userId: user.id,
    supabaseId: user.supabaseId,
    name: safeName(claimedName, safeName(user.username)),
    slot: player,
    connected: true
  };
  socket.join(roomId);
  return roomState.players[player];
}

// Limiteur HTTP anti brute-force / credential stuffing sur l'authentification
function authRateLimit(req, res, next) {
  if (!rateLimit('auth:' + clientIp(req), 12, 5 * 60 * 1000)) {
    return res.status(429).json({ error: 'Trop de tentatives. Réessayez dans quelques minutes.' });
  }
  next();
}

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

function checkersClientBoard(board) {
  return board.map(row => row.map(piece => {
    if (!piece) return null;
    return { player: isWhite(piece) ? 0 : 1, king: isKing(piece), dying: false };
  }));
}

const TTT_LINES = [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]];
function tttWinningLine(board, symbol) { return TTT_LINES.find(line => line.every(index => board[index] === symbol)) || null; }
function tttState() { return { board: Array(9).fill(null), currentPlayer: 0, matchW: 0, matchR: 0, manchesDone: 0, mancheResults: [], isTiebreaker: false, mancheStarterPlayer: 0, resolvingRound: false }; }
function tttMatchWinner(state, total) {
  if (state.isTiebreaker) return null;
  const remaining = total - state.manchesDone;
  if (state.matchW > state.matchR + remaining) return 1;
  if (state.matchR > state.matchW + remaining) return 2;
  if (state.manchesDone < total) return null;
  if (state.matchW === state.matchR) { state.isTiebreaker = true; return null; }
  return state.matchW > state.matchR ? 1 : 2;
}
function finishTTTRound(room, roomId, winnerSlot, winLine) {
  const state = room.gameState;
  if (room.status !== 'playing' || state.resolvingRound) return;
  state.resolvingRound = true;
  clearTTTTurnTimers(room);
  state.manchesDone++;
  if (winnerSlot === 1) { state.matchW++; state.mancheResults.push('w'); }
  else if (winnerSlot === 2) { state.matchR++; state.mancheResults.push('r'); }
  else state.mancheResults.push('d');
  state.mancheStarterPlayer = 1 - state.mancheStarterPlayer;
  state.currentPlayer = state.mancheStarterPlayer;
  const winner = winnerSlot || 'draw';
  io.to(roomId).emit('ttt_manche_result', { room: roomId, winner, winLine: winLine ? winLine.map(index => ({ row: Math.floor(index / 3), col: index % 3 })) : null, matchW: state.matchW, matchR: state.matchR, manchesDone: state.manchesDone, mancheResults: state.mancheResults, isTiebreaker: state.isTiebreaker, nextStarterPlayer: state.mancheStarterPlayer });
  const matchWinner = state.isTiebreaker ? winnerSlot : tttMatchWinner(state, room.totalManches);
  setTimeout(() => {
    if (room.status !== 'playing') return;
    if (matchWinner) return notifyTTTRoomOver(room, roomId, matchWinner, 'normal');
    state.board = Array(9).fill(null);
    state.resolvingRound = false;
    startTTTTurnTimer(room, roomId, state.currentPlayer + 1);
  }, 2800);
}

function quoriInitialState() {
  return { s1Pos: { r: 8, c: 4 }, s2Pos: { r: 0, c: 4 }, s1Walls: 10, s2Walls: 10, hW: Array.from({ length: 8 }, () => Array(8).fill(false)), vW: Array.from({ length: 8 }, () => Array(8).fill(false)), currentSlot: 1 };
}
function quoriInBounds(r, c) { return Number.isInteger(r) && Number.isInteger(c) && r >= 0 && r <= 8 && c >= 0 && c <= 8; }
function quoriBlocked(state, r1, c1, r2, c2) {
  const dr = r2 - r1, dc = c2 - c1, h = state.hW, v = state.vW;
  if (dr === -1) return (c1 <= 7 && r1 >= 1 && h[r1 - 1][c1]) || (c1 >= 1 && r1 >= 1 && h[r1 - 1][c1 - 1]);
  if (dr === 1) return (c1 <= 7 && r1 <= 7 && h[r1][c1]) || (c1 >= 1 && r1 <= 7 && h[r1][c1 - 1]);
  if (dc === -1) return (c1 >= 1 && r1 <= 7 && v[r1][c1 - 1]) || (c1 >= 1 && r1 >= 1 && v[r1 - 1][c1 - 1]);
  if (dc === 1) return (c1 <= 7 && r1 <= 7 && v[r1][c1]) || (c1 <= 7 && r1 >= 1 && v[r1 - 1][c1]);
  return true;
}
function quoriMoves(state, pos, opponent) {
  const moves = [], dirs = [[-1, 0], [1, 0], [0, -1], [0, 1]];
  for (const [dr, dc] of dirs) {
    const nr = pos.r + dr, nc = pos.c + dc;
    if (!quoriInBounds(nr, nc) || quoriBlocked(state, pos.r, pos.c, nr, nc)) continue;
    if (nr !== opponent.r || nc !== opponent.c) { moves.push({ r: nr, c: nc }); continue; }
    const jr = nr + dr, jc = nc + dc;
    if (quoriInBounds(jr, jc) && !quoriBlocked(state, nr, nc, jr, jc)) { moves.push({ r: jr, c: jc }); continue; }
    for (const [pdr, pdc] of [[dc, dr], [-dc, -dr]]) {
      const pr = nr + pdr, pc = nc + pdc;
      if (quoriInBounds(pr, pc) && !quoriBlocked(state, nr, nc, pr, pc)) moves.push({ r: pr, c: pc });
    }
  }
  return moves;
}
function quoriHasPath(state, pos, goalRow) {
  const seen = new Set([pos.r + ',' + pos.c]), queue = [pos];
  for (let i = 0; i < queue.length; i++) {
    const at = queue[i]; if (at.r === goalRow) return true;
    for (const [dr, dc] of [[-1, 0], [1, 0], [0, -1], [0, 1]]) {
      const nr = at.r + dr, nc = at.c + dc, key = nr + ',' + nc;
      if (quoriInBounds(nr, nc) && !seen.has(key) && !quoriBlocked(state, at.r, at.c, nr, nc)) { seen.add(key); queue.push({ r: nr, c: nc }); }
    }
  }
  return false;
}
function quoriCanPlaceWall(state, type, r, c) {
  if (!Number.isInteger(r) || !Number.isInteger(c) || r < 0 || r > 7 || c < 0 || c > 7) return false;
  const own = type === 'wallH' ? state.hW : state.vW, adjacent = type === 'wallH' ? state.hW : state.vW, crossing = type === 'wallH' ? state.vW : state.hW;
  if (own[r][c] || crossing[r][c]) return false;
  if (type === 'wallH' && ((c > 0 && adjacent[r][c - 1]) || (c < 7 && adjacent[r][c + 1]))) return false;
  if (type === 'wallV' && ((r > 0 && adjacent[r - 1][c]) || (r < 7 && adjacent[r + 1][c]))) return false;
  own[r][c] = true;
  const ok = quoriHasPath(state, state.s1Pos, 0) && quoriHasPath(state, state.s2Pos, 8);
  own[r][c] = false;
  return ok;
}

// ── AUTH MIDDLEWARE ────────────────────────────────────────
function requireAuth(req, res, next) {
  const h = req.headers['authorization'] || '';
  if (!h.startsWith('Bearer ')) return res.status(401).json({ error: 'Token manquant' });
  try {
    const userId = jwt.verify(h.slice(7), JWT_SECRET).userId;
    if (!users.has(userId)) return res.status(401).json({ error: 'Session expirée. Reconnectez-vous.' });
    req.userId = userId;
    next();
  }
  catch { res.status(401).json({ error: 'Token invalide' }); }
}

function findUserBySupabaseId(supabaseId) {
  for (const user of users.values()) if (user.supabaseId === supabaseId) return user;
  return null;
}

// The browser must prove its Supabase identity. A raw UUID received from a
// client is never an authentication credential.
async function verifySupabaseAccessToken(accessToken) {
  if (!SUPABASE_URL || !SUPABASE_PUBLISHABLE_KEY || typeof accessToken !== 'string' || accessToken.length < 20 || accessToken.length > 4096) return null;
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 5000);
  try {
    const response = await fetch(SUPABASE_URL + '/auth/v1/user', {
      headers: { apikey: SUPABASE_PUBLISHABLE_KEY, Authorization: 'Bearer ' + accessToken },
      signal: controller.signal
    });
    if (!response.ok) return null;
    const profile = await response.json();
    return profile && typeof profile.id === 'string' ? profile : null;
  } catch {
    return null;
  } finally {
    clearTimeout(timeout);
  }
}

function issueServerToken(res, user) {
  const token = jwt.sign({ userId: user.id }, JWT_SECRET, { expiresIn: '7d' });
  res.json({ token, userId: user.id, username: user.username });
}

function authenticateSocketToken(socket, token) {
  if (typeof token !== 'string' || token.length > 4096) return false;
  try {
    const { userId } = jwt.verify(token, JWT_SECRET);
    if (!users.has(userId)) return false;
    socketUsers.set(socket.id, userId);
    socket.userId = userId;
    return true;
  } catch {
    return false;
  }
}

io.use((socket, next) => {
  const token = socket.handshake.auth && socket.handshake.auth.token;
  if (!token) return next();
  if (!authenticateSocketToken(socket, token)) return next(new Error('unauthorized'));
  next();
});

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

function chifoumiWinnerSlot(choice1, choice2) {
  if (choice1 === choice2) return 0;
  return (choice1 === 'pierre' && choice2 === 'ciseaux') ||
    (choice1 === 'feuille' && choice2 === 'pierre') ||
    (choice1 === 'ciseaux' && choice2 === 'feuille') ? 1 : 2;
}

function resolveChifoumiRound(croom, roomId) {
  if (croom.status !== 'playing' || croom.choices[1] === undefined || croom.choices[2] === undefined) return;
  clearChifoumiTurnTimers(croom);
  const choice1 = croom.choices[1], choice2 = croom.choices[2];
  const winnerSlot = chifoumiWinnerSlot(choice1, choice2);
  if (winnerSlot === 1) croom.scores[0]++;
  if (winnerSlot === 2) croom.scores[1]++;
  croom.history.push({ round: croom.currentRound, choice1, choice2, winnerSlot });

  for (const slot of [1, 2]) {
    const player = croom.players[slot];
    if (!player?.socketId) continue;
    io.to(player.socketId).emit('chifoumi_reveal', {
      myChoice: slot === 1 ? choice1 : choice2,
      opChoice: slot === 1 ? choice2 : choice1,
      scores: croom.scores,
      round: croom.currentRound
    });
  }

  if (croom.currentRound >= 5) {
    return setTimeout(() => {
      if (croom.status !== 'playing') return;
      const winner = croom.scores[0] === croom.scores[1] ? 0 : (croom.scores[0] > croom.scores[1] ? 1 : 2);
      notifyChifoumiRoomOver(croom, roomId, winner, winner === 0 ? 'draw' : 'normal');
    }, 3000);
  }
  croom.awaitingNextRound = true;
}

// ══════════════════════════════════════════════════════════
//  PAUSE / REPRISE / ANNULATION (Sanction 5% si les deux abandonnent)
// ══════════════════════════════════════════════════════════
function pauseAndWatch({ room, roomId, gameName, getP1, getP2, winFn, onResume }) {
  if (room.disconnectTimer) return;
  room.status = 'paused';
  const serverTime = Date.now();
  room.reconnectDeadline = serverTime + 60000;
  io.to(roomId).emit('game:reconnect_deadline', { game: gameName, serverTime, reconnectDeadline: room.reconnectDeadline });
  room.disconnectTimer = setTimeout(() => {
    if (room.status === 'finished') return;
    room.disconnectTimer = null;
    const p1 = getP1(), p2 = getP2();
    const p1back = p1?.connected === true, p2back = p2?.connected === true;
    if (p1back && p2back) {
      room.status = 'playing';
      room.reconnectDeadline = null;
      if (onResume) onResume();
      return;
    }
    if (!p1back && !p2back) {
      room.status = 'finished';
      void settleRoomInSupabase(room, gameName, 0, 'both_disconnected');
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
      room.reconnectDeadline = null;
      winFn(p1back);
    }
  }, 60000);
}

// ── FIN DE PARTIES (Notifications avec gestion des Match Nuls sécurisée) ──
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
  void settleRoomInSupabase(room, 'dames', winnerSlot, reason);

  if (winnerSlot === 0) {
    const base = { type: 'game_over', game: 'dames', room: roomId, winner: 'draw', winnerSlot: 0, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission: 0, netGain: bet, currency: room.currency || 'HTG', reason: 'draw' };
    if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p1.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p2.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    io.to(roomId).emit('game:result', { postMessage: base });
    return;
  }

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
  void settleRoomInSupabase(troom, 'tictactoe', winnerSlot, reason);

  if (winnerSlot === 0) {
    const base = { type: 'game_over', game: 'tictactoe', room: roomId, winner: 'draw', winnerSlot: 0, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission: 0, netGain: bet, currency: troom.currency || 'HTG', reason: 'draw' };
    if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p1.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p2.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    io.to(roomId).emit('game:result', { postMessage: base });
    return;
  }

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
  void settleRoomInSupabase(qroom, 'quoridor', winnerSlot, reason);

  if (winnerSlot === 0) {
    const base = { type: 'game_over', game: 'quoridor', room: roomId, winner: 'draw', winnerSlot: 0, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission: 0, netGain: bet, currency: qroom.currency || 'HTG', reason: 'draw' };
    if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p1.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p2.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    io.to(roomId).emit('game:result', { postMessage: base });
    return;
  }

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
  void settleRoomInSupabase(proom, 'penalty', winnerSlot, reason);

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
  void settleRoomInSupabase(room, 'chifoumi', winnerSlot, reason);

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
app.get('/health', (req, res) => {
  // Le contrôle de disponibilité de l'appli doit réussir depuis n'importe
  // quelle origine (PWA, aperçu, app installée). /health ne renvoie que
  // l'état du serveur, aucune donnée sensible.
  res.setHeader('Access-Control-Allow-Origin', '*');
  res.json({
    status: 'ok', time: new Date().toISOString(),
    games: games.size, damesRooms: damesRooms.size,
    tttRooms: tttRooms.size, quoriRooms: quoriRooms.size,
    penaltyRooms: penaltyRooms.size, chifoumiRooms: chifoumiRooms.size,
    queue: [...queue.entries()].map(([amt, p]) => ({ betAmount: amt, waiting: p.length }))
  });
});

// Routeur intelligent qui liste les vrais fichiers si ça plante
const serveSmart = (possibleNames, injectRoom = false) => (req, res) => {
  let foundPath = null;
  let files = [];
  
  try {
    if (!fs.existsSync(PUBLIC)) {
      return res.status(404).send("Erreur critique : Le dossier 'public' n'existe pas sur ce serveur.");
    }
    files = fs.readdirSync(PUBLIC);
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
app.get(['/dames-ai', '/dames_ai.html', '/dames-solo', '/dames-entrainement', '/dames-practice', '/dames-ia'], serveSmart(['dames_ai.html', 'dames-ai.html']));
app.get(['/ttt', '/ttt.html', '/ttt-online.html', '/ttt_game.html'], serveSmart(['ttt_game.html', 'ttt.html', 'ttt-online.html']));
app.get(['/quoridor', '/quoridor.html', '/quoridor-online.html', '/quoridor_multi.html'], serveSmart(['quoridor_multi.html', 'quoridor.html', 'quoridor-online.html']));
app.get(['/quoridor-ai', '/quoridor_ai.html', '/quoridor-solo', '/quoridor-entrainement', '/quoridor-ia'], serveSmart(['quoridor_ai.html', 'quoridor-ai.html']));
app.get(['/chifoumi', '/chifoumi.html', '/chifoumi-online.html'], serveSmart(['chifoumi-online.html', 'chifoumi.html']));
app.get(['/chifoumi-ai', '/chifoumi_ai.html', '/chifoumi-solo', '/chifoumi-entrainement', '/chifoumi-ia'], serveSmart(['chifoumi_ai.html', 'chifoumi-ai.html']));
app.get(['/penalty', '/penalty.html', '/penalty_shootout.html', '/penalty-online.html', '/penalty_online.html'], serveSmart(['penalty_online.html', 'penalty_shootout.html', 'penalty-online.html', 'penalty.html'], true));
app.get(['/penalty-ai', '/penalty_ai.html', '/penalty-solo', '/penalty-entrainement', '/penalty-ia'], serveSmart(['penalty_ai.html', 'penalty-ai.html'], true));

// -- REST API MATCHMAKING & AUTH --
app.post('/auth/register', authRateLimit, async (req, res) => {
  const { username, password, supabaseId } = req.body;
  const supabaseProfile = await verifySupabaseAccessToken(req.body.supabaseAccessToken);
  if (supabaseProfile) {
    let user = findUserBySupabaseId(supabaseProfile.id);
    if (!user) {
      const safeUsername = safeName(username, 'Joueur');
      if ([...users.values()].some(u => u.username === safeUsername)) return res.status(409).json({ error: 'Nom deja pris' });
      user = { id: uuid(), username: safeUsername, supabaseId: supabaseProfile.id };
      users.set(user.id, user);
    }
    return issueServerToken(res, user);
  }
  if (!LEGACY_LOCAL_AUTH) return res.status(401).json({ error: 'Session Supabase valide requise.' });
  if (!username || !password) return res.status(400).json({ error: 'Champs requis' });
  for (const u of users.values()) if (u.username === username) return res.status(409).json({ error: 'Nom déjà pris' });
  const id = uuid();
  users.set(id, { id, username, password: bcrypt.hashSync(password, 10), supabaseId: supabaseId || null });
  const token = jwt.sign({ userId: id }, JWT_SECRET, { expiresIn: '7d' });
  res.json({ token, userId: id, username });
});

app.post('/auth/login', authRateLimit, async (req, res) => {
  const { username, password, supabaseId } = req.body;
  const supabaseProfile = await verifySupabaseAccessToken(req.body.supabaseAccessToken);
  if (supabaseProfile) {
    let user = findUserBySupabaseId(supabaseProfile.id);
    if (!user) {
      user = { id: uuid(), username: safeName(username || supabaseProfile.email, 'Joueur'), supabaseId: supabaseProfile.id };
      users.set(user.id, user);
    }
    return issueServerToken(res, user);
  }
  if (!LEGACY_LOCAL_AUTH) return res.status(401).json({ error: 'Session Supabase valide requise.' });
  const user = [...users.values()].find(u => u.username === username);
  if (!user || !bcrypt.compareSync(password, user.password)) return res.status(401).json({ error: 'Identifiants incorrects' });
  if (supabaseId) user.supabaseId = supabaseId;
  const token = jwt.sign({ userId: user.id }, JWT_SECRET, { expiresIn: '7d' });
  res.json({ token, userId: user.id, username: user.username });
});

app.post('/matchmaking/join', requireAuth, (req, res) => {
  const { betAmount, username } = req.body;
  if (!betAmount || betAmount <= 0) return res.status(400).json({ error: 'Montant invalide' });
  const userId = req.userId;
  let user = users.get(userId);
  if (!user) return res.status(401).json({ error: 'Session expirÃ©e. Reconnectez-vous.' });
  if (username) user.username = safeName(username, user.username);
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
  const { gameId, username, color, betAmount } = req.body;
  if (!gameId) return res.status(400).json({ error: 'gameId requis' });
  const userId = req.userId;
  const user = users.get(userId);
  if (!user) return res.status(401).json({ error: 'Session expirÃ©e. Reconnectez-vous.' });
  if (username) user.username = safeName(username, user.username);
  let game = games.get(gameId);
  if (!game) {
    game = { id: gameId, playerWhite: color === 'black' ? null : userId, playerBlack: color === 'black' ? userId : null, board: initialBoard(), currentPlayer: 'white', status: 'waiting', winner: null, betAmount: betAmount || 0, disconnectTimer: null };
    games.set(gameId, game);
    return res.json({ status: 'waiting', gameId, message: 'En attente du 2ème joueur…' });
  }
  if (game.status === 'playing') {
    const myColor = game.playerWhite === userId ? 'white' : game.playerBlack === userId ? 'black' : null;
    if (!myColor) return res.status(403).json({ error: 'AccÃ¨s refusÃ©' });
    return res.json({ status: 'ready', gameId, youAre: myColor });
  }
  if (game.playerWhite === userId || game.playerBlack === userId) return res.json({ status: 'waiting', gameId, message: 'En attente du 2Ã¨me joueurâ€¦' });
  if (!game.playerWhite) game.playerWhite = userId;
  else if (!game.playerBlack) game.playerBlack = userId;
  else return res.status(409).json({ error: 'Partie complÃ¨te' });
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
  const color = game.playerWhite === req.userId ? 'white' : game.playerBlack === req.userId ? 'black' : null;
  if (!color) return res.status(403).json({ error: 'AccÃ¨s refusÃ©' });
  notifyGameOver(game, color === 'white' ? 'black' : 'white', 'resign');
  res.json({ ok: true });
});

// ══════════════════════════════════════════════════════════
//  SOCKET.IO
// ══════════════════════════════════════════════════════════
io.on('connection', (socket) => {

  // Anti-flood : un socket qui envoie un volume anormal d'événements est déconnecté.
  // Seuil très large (500 / 10 s) : les vrais joueurs ne l'atteignent jamais, seuls les bots.
  socket.onAny(() => {
    if (!socketAllow(socket.id, 'any', 500, 10000)) {
      try { socket.disconnect(true); } catch (e) {}
    }
  });

  socket.on('auth', ({ token }) => {
    if (authenticateSocketToken(socket, token)) socket.emit('auth:ok', { userId: socket.userId });
    else socket.emit('auth:error', { message: 'Token invalide ou session expirée' });
  });

  socket.on('auth:supabase', async ({ supabaseId, username, accessToken }) => {
    const supabaseProfile = await verifySupabaseAccessToken(accessToken);
    if (supabaseProfile) {
      let found = findUserBySupabaseId(supabaseProfile.id);
      if (!found) {
        found = { id: uuid(), username: safeName(username || supabaseProfile.email, 'Joueur'), supabaseId: supabaseProfile.id };
        users.set(found.id, found);
      }
      socketUsers.set(socket.id, found.id); socket.userId = found.id;
      const token = jwt.sign({ userId: found.id }, JWT_SECRET, { expiresIn: '7d' });
      return socket.emit('auth:ok', { userId: found.id, token });
    }
    if (!LEGACY_LOCAL_AUTH) {
      return socket.emit('auth:error', { message: 'Authentification Supabase vérifiée requise.' });
    }
    if (!supabaseId) return;
    let found = null;
    for (const u of users.values()) if (u.supabaseId === supabaseId) { found = u; break; }
    if (!found) { const id = uuid(); found = { id, username: username || 'Joueur', supabaseId }; users.set(id, found); }
    socketUsers.set(socket.id, found.id); socket.userId = found.id;
    const token = jwt.sign({ userId: found.id }, JWT_SECRET, { expiresIn: '7d' });
    socket.emit('auth:ok', { userId: found.id, token });
  });

  socket.on('game:join_room', ({ gameId }) => {
    const game = games.get(gameId);
    if (!validRoom(gameId) || !authenticatedSocketUser(socket) || !game || (game.playerWhite !== socket.userId && game.playerBlack !== socket.userId)) {
      return rejectSocket(socket, 'Accès à cette partie refusé.');
    }
    socket.join(gameId);
  });

  // ══════════════════════════════════════════════════════
  //  DAMES MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('dames_join', ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
    let droom = damesRooms.get(room);
    if (!droom) {
      droom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, engineBoard: initialBoard(), boardState: JSON.stringify(checkersClientBoard(initialBoard())), currentPlayer: 0, lastMove: null, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null };
      damesRooms.set(room, droom);
    }
    if (!bindDatabaseGame(droom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, droom, room, player, supabaseId, name)) return;
    if (bet && !droom.betAmount) droom.betAmount = bet;

    if (droom.status === 'playing' || droom.status === 'paused') {
      const p1 = droom.players[1], p2 = droom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && droom.disconnectTimer) {
        clearTimeout(droom.disconnectTimer); droom.disconnectTimer = null; droom.reconnectDeadline = null; droom.status = 'playing';
        startDamesTurnTimer(droom, room, droom.pausedTurnPlayer || 1);
        io.to(room).emit('dames_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
      } else if (droom.disconnectTimer) {
        setTimeout(() => socket.emit('game:reconnect_deadline', { game: 'dames', serverTime: Date.now(), reconnectDeadline: droom.reconnectDeadline }), 0);
      }
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
      socket.emit('dames_start', { room, yourSlot: player, opponentName, bet: droom.betAmount, currency: droom.currency, reconnected: true, paused: droom.status === 'paused', boardState: droom.boardState || null, currentPlayer: droom.currentPlayer !== undefined ? droom.currentPlayer : 0, lastMove: droom.lastMove || null });
      if (droom.turnPlayer !== null && droom.status === 'playing') {
        const now = Date.now();
        if (droom.graceStartTime) socket.emit('dames_turn_sync', { serverTime: now, turnPlayer: droom.turnPlayer, graceStartTime: droom.graceStartTime, duration: GRACE_DURATION });
        else if (droom.turnStartTime) socket.emit('dames_turn_sync', { serverTime: now, turnPlayer: droom.turnPlayer, turnStartTime: droom.turnStartTime, duration: TURN_DURATION });
      }
      return;
    }

    if (droom.players[1] && droom.players[2] && droom.status === 'waiting') {
      droom.status = 'playing';
      droom.startedAt = Date.now();
      const p1 = droom.players[1], p2 = droom.players[2];
      io.to(p1.socketId).emit('dames_start', { room, yourSlot: 1, opponentName: p2.name, bet: droom.betAmount, currency: droom.currency, reconnected: false });
      io.to(p2.socketId).emit('dames_start', { room, yourSlot: 2, opponentName: p1.name, bet: droom.betAmount, currency: droom.currency, reconnected: false });
      setTimeout(() => { if (droom.status === 'playing') startDamesTurnTimer(droom, room, 1); }, 3000);
    }
  });

  socket.on('dames_move', ({ room, player, from, to, steps }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const droom = damesRooms.get(room);
    if (!droom || droom.status !== 'playing' || droom.players[player]?.socketId !== socket.id) return;
    if (droom.currentPlayer !== player - 1) return rejectSocket(socket, 'Ce n’est pas votre tour.');
    const sequence = Array.isArray(steps) && steps.length ? steps : [{ from, to }];
    const first = sequence[0]?.from, last = sequence[sequence.length - 1]?.to;
    if (!first || !last || !Number.isInteger(first.row) || !Number.isInteger(first.col) || !Number.isInteger(last.row) || !Number.isInteger(last.col)) return rejectSocket(socket, 'Coup de dames invalide.');
    const result = applyMove(droom.engineBoard, player === 1 ? 'white' : 'black', first.row, first.col, last.row, last.col);
    if (!result.ok) return rejectSocket(socket, result.reason);
    droom.engineBoard = result.board;
    droom.boardState = JSON.stringify(checkersClientBoard(result.board));
    droom.currentPlayer = result.next === 'white' ? 0 : 1;
    droom.lastMove = { from: first, to: last, player };
    socket.to(room).emit('dames_move', { room, player, steps: sequence, boardState: droom.boardState, nextPlayer: droom.currentPlayer, isComplete: true });
    if (result.winner) return notifyDamesRoomOver(droom, room, result.winner === 'white' ? 1 : 2, 'checkmate');
    startDamesTurnTimer(droom, room, droom.currentPlayer + 1);
  });

  socket.on('dames_result', (data) => {
    if (!data || !validRoom(data.room)) return;
    // Legacy clients still emit this after their animation. It is intentionally
    // ignored: only the authoritative move engine can finish a match.
  });

  // ══════════════════════════════════════════════════════
  //  TTT MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('ttt_join', ({ room, player, supabaseId, name, bet, currency, manches, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
    let troom = tttRooms.get(room);
    if (!troom) {
      troom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: tttState(), turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null, totalManches: Math.max(1, Math.min(15, Number(manches) || 5)) };
      tttRooms.set(room, troom);
    }
    if (!bindDatabaseGame(troom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, troom, room, player, supabaseId, name)) return;
    if (bet && !troom.betAmount) troom.betAmount = bet;

    if (troom.status === 'playing' || troom.status === 'paused') {
      const p1 = troom.players[1], p2 = troom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && troom.disconnectTimer) {
        clearTimeout(troom.disconnectTimer); troom.disconnectTimer = null; troom.reconnectDeadline = null; troom.status = 'playing';
        startTTTTurnTimer(troom, room, troom.pausedTurnPlayer || 1);
        io.to(room).emit('ttt_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
      } else if (troom.disconnectTimer) {
        setTimeout(() => socket.emit('game:reconnect_deadline', { game: 'tictactoe', serverTime: Date.now(), reconnectDeadline: troom.reconnectDeadline }), 0);
      }
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
      socket.emit('ttt_start', { room, yourSlot: player, opponentName, bet: troom.betAmount, currency: troom.currency, reconnected: true, paused: troom.status === 'paused', gameState: troom.gameState || null, totalManches: troom.totalManches });
      if (troom.turnPlayer !== null && troom.status === 'playing') {
        const now = Date.now();
        if (troom.graceStartTime) socket.emit('ttt_turn_sync', { serverTime: now, turnPlayer: troom.turnPlayer, graceStartTime: troom.graceStartTime, duration: GRACE_DURATION });
        else if (troom.turnStartTime) socket.emit('ttt_turn_sync', { serverTime: now, turnPlayer: troom.turnPlayer, turnStartTime: troom.turnStartTime, duration: TURN_DURATION });
      }
      return;
    }

    if (troom.players[1] && troom.players[2] && troom.status === 'waiting') {
      troom.status = 'playing';
      troom.startedAt = Date.now();
      const p1 = troom.players[1], p2 = troom.players[2];
      io.to(p1.socketId).emit('ttt_start', { room, yourSlot: 1, opponentName: p2.name, bet: troom.betAmount, currency: troom.currency, reconnected: false, totalManches: troom.totalManches });
      io.to(p2.socketId).emit('ttt_start', { room, yourSlot: 2, opponentName: p1.name, bet: troom.betAmount, currency: troom.currency, reconnected: false, totalManches: troom.totalManches });
      setTimeout(() => { if (troom.status === 'playing') startTTTTurnTimer(troom, room, 1); }, 3000);
    }
  });

  socket.on('ttt_move', ({ room, player, row, col, symbol }) => {
    if (!validRoom(room) || !validPlayerSlot(player) || !Number.isInteger(row) || !Number.isInteger(col) || row < 0 || row > 2 || col < 0 || col > 2) return;
    const troom = tttRooms.get(room), state = troom?.gameState;
    if (!troom || !state || troom.status !== 'playing' || state.resolvingRound || troom.players[player]?.socketId !== socket.id) return;
    const expectedSymbol = player === 1 ? 'X' : 'O', index = row * 3 + col;
    if (state.currentPlayer !== player - 1 || symbol !== expectedSymbol || state.board[index] !== null) return rejectSocket(socket, 'Coup Tic-Tac-Toe invalide.');
    state.board[index] = expectedSymbol;
    const line = tttWinningLine(state.board, expectedSymbol);
    const draw = !line && state.board.every(Boolean);
    state.currentPlayer = player === 1 ? 1 : 0;
    socket.to(room).emit('ttt_move', { room, player, row, col, symbol: expectedSymbol, boardState: JSON.stringify(state.board), nextPlayer: state.currentPlayer });
    if (line || draw) return finishTTTRound(troom, room, line ? player : 0, line);
    startTTTTurnTimer(troom, room, state.currentPlayer + 1);
  });

  socket.on('ttt_manche_end', () => {}); // Kept for old clients; scores are server-owned.

  socket.on('ttt_result', (data) => {
    if (!data || !validRoom(data.room)) return;
    const troom = tttRooms.get(data.room);
    if (!troom || !socketIsPlayer(troom, socket.id)) return;
  });

  // ══════════════════════════════════════════════════════
  //  QUORIDOR MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('quoridor_join', ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
    let qroom = quoriRooms.get(room);
    if (!qroom) {
      qroom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: quoriInitialState(), currentSlot: 1, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null };
      quoriRooms.set(room, qroom);
    }
    if (!bindDatabaseGame(qroom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, qroom, room, player, supabaseId, name)) return;
    if (bet && !qroom.betAmount) qroom.betAmount = bet;

    if (qroom.status === 'playing' || qroom.status === 'paused') {
      const p1 = qroom.players[1], p2 = qroom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && qroom.disconnectTimer) {
        clearTimeout(qroom.disconnectTimer); qroom.disconnectTimer = null; qroom.reconnectDeadline = null; qroom.status = 'playing';
        startQuoriTurnTimer(qroom, room, qroom.pausedTurnPlayer || qroom.currentSlot || 1);
        io.to(room).emit('quoridor_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
      } else if (qroom.disconnectTimer) {
        setTimeout(() => socket.emit('game:reconnect_deadline', { game: 'quoridor', serverTime: Date.now(), reconnectDeadline: qroom.reconnectDeadline }), 0);
      }
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
      socket.emit('quoridor_start', { room, yourSlot: player, opponentName, bet: qroom.betAmount, currency: qroom.currency, reconnected: true, paused: qroom.status === 'paused', gameState: qroom.gameState || null, currentSlot: qroom.currentSlot, turnPlayer: qroom.turnPlayer, turnStartTime: qroom.turnStartTime, graceStartTime: qroom.graceStartTime });
      if (qroom.turnPlayer !== null && qroom.status === 'playing') {
        const now = Date.now();
        if (qroom.graceStartTime) socket.emit('quoridor_turn_sync', { serverTime: now, turnPlayer: qroom.turnPlayer, graceStartTime: qroom.graceStartTime, duration: GRACE_DURATION });
        else if (qroom.turnStartTime) socket.emit('quoridor_turn_sync', { serverTime: now, turnPlayer: qroom.turnPlayer, turnStartTime: qroom.turnStartTime, duration: TURN_DURATION });
      }
      return;
    }

    if (qroom.players[1] && qroom.players[2] && qroom.status === 'waiting') {
      qroom.status = 'playing';
      qroom.startedAt = Date.now();
      const p1 = qroom.players[1], p2 = qroom.players[2];
      io.to(p1.socketId).emit('quoridor_start', { room, yourSlot: 1, opponentName: p2.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });
      io.to(p2.socketId).emit('quoridor_start', { room, yourSlot: 2, opponentName: p1.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });
      setTimeout(() => { if (qroom.status === 'playing') { qroom.currentSlot = 1; startQuoriTurnTimer(qroom, room, 1); } }, 3000);
    }
  });

  socket.on('quoridor_move', ({ room, player, moveType, data }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const qroom = quoriRooms.get(room), state = qroom?.gameState;
    if (!qroom || !state || qroom.status !== 'playing' || qroom.players[player]?.socketId !== socket.id) return;
    if (qroom.currentSlot !== player) return rejectSocket(socket, 'Ce n’est pas votre tour.');
    const ownPos = player === 1 ? state.s1Pos : state.s2Pos, otherPos = player === 1 ? state.s2Pos : state.s1Pos;
    if (!data || !Number.isInteger(data.r) || !Number.isInteger(data.c)) return rejectSocket(socket, 'Coup Quoridor invalide.');
    if (moveType === 'move') {
      const legal = quoriMoves(state, ownPos, otherPos).some(move => move.r === data.r && move.c === data.c);
      if (!legal) return rejectSocket(socket, 'Déplacement Quoridor invalide.');
      if (player === 1) state.s1Pos = { r: data.r, c: data.c }; else state.s2Pos = { r: data.r, c: data.c };
    } else if (moveType === 'wallH' || moveType === 'wallV') {
      const walls = player === 1 ? state.s1Walls : state.s2Walls;
      if (walls <= 0 || !quoriCanPlaceWall(state, moveType, data.r, data.c)) return rejectSocket(socket, 'Mur Quoridor invalide.');
      (moveType === 'wallH' ? state.hW : state.vW)[data.r][data.c] = true;
      if (player === 1) state.s1Walls--; else state.s2Walls--;
    } else return rejectSocket(socket, 'Action Quoridor invalide.');
    const winnerSlot = (player === 1 && state.s1Pos.r === 0) || (player === 2 && state.s2Pos.r === 8) ? player : 0;
    qroom.currentSlot = player === 1 ? 2 : 1;
    state.currentSlot = qroom.currentSlot;
    socket.to(room).emit('quoridor_move', { room, player, moveType, data: { r: data.r, c: data.c }, gameState: JSON.stringify(state), nextPlayer: qroom.currentSlot - 1 });
    if (winnerSlot) return notifyQuoriRoomOver(qroom, room, winnerSlot, 'normal');
    startQuoriTurnTimer(qroom, room, qroom.currentSlot);
  });

  socket.on('quoridor_result', (data) => {
    if (!data || !validRoom(data.room)) return;
    const qroom = quoriRooms.get(data.room);
    if (!qroom || !socketIsPlayer(qroom, socket.id)) return;
  });

  // ══════════════════════════════════════════════════════
  //  PENALTY SHOOTOUT MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('penalty_join', ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) { socket.emit('penalty_error', { message: 'room_or_player_invalid', detail: 'Room ou joueur invalide.' }); return; }
    let proom = penaltyRooms.get(room);

    if (!proom) {
      proom = {
        id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG',
        disconnectTimer: null, currentRound: 1, scores: { p1: 0, p2: 0 }, choices: {},
        turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null
      };
      penaltyRooms.set(room, proom);
    }
    if (!bindDatabaseGame(proom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');

    if (!joinRoomAsAuthenticatedPlayer(socket, proom, room, player, supabaseId, name)) return;
    if (bet && !proom.betAmount) proom.betAmount = bet;

    if (proom.status === 'playing' || proom.status === 'paused') {
      const p1 = proom.players[1], p2 = proom.players[2];
      const bothBack = p1?.connected && p2?.connected;

      if (bothBack && proom.disconnectTimer) {
        clearTimeout(proom.disconnectTimer); proom.disconnectTimer = null; proom.reconnectDeadline = null; proom.status = 'playing';
        startPenaltyTurnTimer(proom, room);
        io.to(room).emit('penalty_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
      } else if (proom.disconnectTimer) {
        setTimeout(() => socket.emit('game:reconnect_deadline', { game: 'penalty', serverTime: Date.now(), reconnectDeadline: proom.reconnectDeadline }), 0);
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
      socket.emit('penalty_start', { room, yourSlot: player, opponentName, bet: proom.betAmount, currency: proom.currency, reconnected: true, paused: proom.status === 'paused', gameState: { round: proom.currentRound, scores: proom.scores, phase: 'choosing' } });
      
      if (proom.status === 'playing') {
        const now = Date.now();
        if (proom.graceStartTime) { socket.emit('penalty_turn_sync', { serverTime: now, startTime: proom.graceStartTime, duration: PENALTY_GRACE_DURATION }); } 
        else if (proom.turnStartTime) { socket.emit('penalty_turn_sync', { serverTime: now, startTime: proom.turnStartTime, duration: PENALTY_TURN_DURATION }); }
      }
      return;
    }

    if (proom.players[1] && proom.players[2] && proom.status === 'waiting') {
      proom.status = 'playing';
      proom.startedAt = Date.now();
      const p1 = proom.players[1], p2 = proom.players[2];
      io.to(p1.socketId).emit('penalty_start', { room, yourSlot: 1, opponentName: p2.name, bet: proom.betAmount, currency: proom.currency, reconnected: false });
      io.to(p2.socketId).emit('penalty_start', { room, yourSlot: 2, opponentName: p1.name, bet: proom.betAmount, currency: proom.currency, reconnected: false });
      setTimeout(() => { if (proom.status === 'playing') startPenaltyTurnTimer(proom, room); }, 2800);
    }
  });

  socket.on('penalty_choice', ({ room, player, round, zone }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const proom = penaltyRooms.get(room);
    if (!proom || proom.status !== 'playing' || proom.currentRound !== round || proom.players[player]?.socketId !== socket.id) return;
    if (!Number.isInteger(zone) || zone < 0 || zone > 8 || proom.choices[player] !== undefined) return;
    proom.choices[player] = zone;
    socket.to(room).emit('penalty_choice_received', { player });

    if (proom.choices[1] !== undefined && proom.choices[2] !== undefined) {
      resolvePenaltyRound(proom, room);
    }
  });

  socket.on('penalty_result', (data) => {
    if (!data || !validRoom(data.room)) return;
    if (!socketAllow(socket.id, 'result', 15, 10000)) return;
    const proom = penaltyRooms.get(data.room);
    if (!proom) return;
    if (!socketIsPlayer(proom, socket.id)) return;
    // The score and the final result are calculated by resolvePenaltyRound.
    // Client result messages are display-only and cannot settle a match.
  });

  // ══════════════════════════════════════════════════════
  //  CHIFOUMI MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('chifoumi_join', ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
    let croom = chifoumiRooms.get(room);
    if (!croom) {
      croom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, currentRound: 1, scores: [0, 0], choices: {}, history: [], turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null };
      chifoumiRooms.set(room, croom);
    }
    if (!bindDatabaseGame(croom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, croom, room, player, supabaseId, name)) return;
    if (bet && !croom.betAmount) croom.betAmount = bet;

    if (croom.status === 'playing' || croom.status === 'paused') {
      const p1 = croom.players[1], p2 = croom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && croom.disconnectTimer) {
        clearTimeout(croom.disconnectTimer); croom.disconnectTimer = null; croom.reconnectDeadline = null; croom.status = 'playing';
        startChifoumiTurnTimer(croom, room);
        io.to(room).emit('chifoumi_game_resumed', { message: 'Les deux joueurs sont de retour !' });
      } else if (croom.disconnectTimer) {
        setTimeout(() => socket.emit('game:reconnect_deadline', { game: 'chifoumi', serverTime: Date.now(), reconnectDeadline: croom.reconnectDeadline }), 0);
      }
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
      socket.emit('chifoumi_start', { room, yourSlot: player, opponentName, bet: croom.betAmount, currency: croom.currency, reconnected: true, paused: croom.status === 'paused', gameState: { scores: croom.scores, currentRound: croom.currentRound, history: croom.history } });
      
      if (croom.status === 'playing') {
        const now = Date.now();
        if (croom.graceStartTime) { socket.emit('chifoumi_turn_sync', { serverTime: now, startTime: croom.graceStartTime, duration: CHIFOUMI_GRACE_DURATION }); }
        else if (croom.turnStartTime) { socket.emit('chifoumi_turn_sync', { serverTime: now, startTime: croom.turnStartTime, duration: CHIFOUMI_TURN_DURATION }); }
      }
      return;
    }

    if (croom.players[1] && croom.players[2] && croom.status === 'waiting') {
      croom.status = 'playing'; const p1 = croom.players[1], p2 = croom.players[2];
      croom.startedAt = Date.now();
      io.to(p1.socketId).emit('chifoumi_start', { room, yourSlot: 1, opponentName: p2.name, bet: croom.betAmount, currency: croom.currency, reconnected: false });
      io.to(p2.socketId).emit('chifoumi_start', { room, yourSlot: 2, opponentName: p1.name, bet: croom.betAmount, currency: croom.currency, reconnected: false });
      setTimeout(() => { if (croom.status === 'playing') startChifoumiTurnTimer(croom, room); }, 3000);
    }
  });

  socket.on('chifoumi_choice', ({ room, player, choice }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const croom = chifoumiRooms.get(room);
    if (!croom || croom.status !== 'playing' || croom.players[player]?.socketId !== socket.id) return;
    if (!['pierre', 'feuille', 'ciseaux'].includes(choice) || croom.choices[player] !== undefined) return;
    croom.choices[player] = choice;
    socket.to(room).emit('chifoumi_opponent_choice', { player });
    
    // Si les deux ont joué, on n'attend plus la période de grâce
    if (croom.choices[1] !== undefined && croom.choices[2] !== undefined) {
        resolveChifoumiRound(croom, room);
    }
  });

  socket.on('chifoumi_round_start', ({ room, player, round }) => {
    const croom = chifoumiRooms.get(room);
    if (croom && croom.status === 'playing' && validPlayerSlot(player) && croom.players[player]?.socketId === socket.id && croom.awaitingNextRound === true && Number.isInteger(round) && round === croom.currentRound + 1 && croom.history.length === croom.currentRound) {
      croom.currentRound = round;
      croom.choices = {};
      croom.awaitingNextRound = false;
      startChifoumiTurnTimer(croom, room);
    }
  });

  socket.on('chifoumi_round_result', () => {});

  socket.on('chifoumi_result', (data) => {
    if (!data || !validRoom(data.room)) return;
    if (!socketAllow(socket.id, 'result', 15, 10000)) return;
    const croom = chifoumiRooms.get(data.room); if (!croom) return;
    if (!socketIsPlayer(croom, socket.id)) return;
    // Normal outcomes are calculated above from the server's own choices and scores.
    // Never let a browser select the winner of a paid match.
    if (safeReason(data.reason) !== 'normal' && safeReason(data.reason) !== 'draw') return;
  });

  // A mutual quit requires confirmation from BOTH authenticated sockets. A
  // single browser can request it, but cannot turn its own request into a
  // refund or a wallet operation.
  socket.on('game_mutual_quit', ({ room, game, player }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const entries = {
      dames: [damesRooms, notifyDamesRoomOver],
      tictactoe: [tttRooms, notifyTTTRoomOver],
      quoridor: [quoriRooms, notifyQuoriRoomOver],
      penalty: [penaltyRooms, notifyPenaltyRoomOver],
      chifoumi: [chifoumiRooms, notifyChifoumiRoomOver]
    };
    const entry = entries[game];
    if (!entry) return;
    const [rooms, finish] = entry, gameRoom = rooms.get(room);
    if (!gameRoom || gameRoom.status !== 'playing' || gameRoom.players[player]?.socketId !== socket.id) return;
    gameRoom.mutualQuitRequests = gameRoom.mutualQuitRequests || new Set();
    gameRoom.mutualQuitRequests.add(player);
    const other = player === 1 ? 2 : 1;
    io.to(room).emit('game:mutual_quit_requested', { game, requestedBy: player, awaiting: gameRoom.mutualQuitRequests.size < 2 });
    if (gameRoom.mutualQuitRequests.has(other)) finish(gameRoom, room, 0, 'mutual_quit');
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
      droom.pausedTurnPlayer = droom.turnPlayer || (droom.currentPlayer + 1) || 1;
      clearDamesTurnTimers(droom);
      pauseAndWatch({ room: droom, roomId, gameName: 'dames', getP1: () => droom.players[1], getP2: () => droom.players[2], winFn: (winnerIsP1) => notifyDamesRoomOver(droom, roomId, winnerIsP1 ? 1 : 2, 'forfeit'), onResume: () => startDamesTurnTimer(droom, roomId, droom.pausedTurnPlayer || 1) });
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
      troom.pausedTurnPlayer = troom.turnPlayer || ((troom.gameState?.currentPlayer || 0) + 1);
      clearTTTTurnTimers(troom);
      pauseAndWatch({ room: troom, roomId, gameName: 'tictactoe', getP1: () => troom.players[1], getP2: () => troom.players[2], winFn: (winnerIsP1) => notifyTTTRoomOver(troom, roomId, winnerIsP1 ? 1 : 2, 'forfeit'), onResume: () => startTTTTurnTimer(troom, roomId, troom.pausedTurnPlayer || 1) });
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
      qroom.pausedTurnPlayer = qroom.turnPlayer || qroom.currentSlot || 1;
      clearQuoriTurnTimers(qroom);
      pauseAndWatch({ room: qroom, roomId, gameName: 'quoridor', getP1: () => qroom.players[1], getP2: () => qroom.players[2], winFn: (winnerIsP1) => notifyQuoriRoomOver(qroom, roomId, winnerIsP1 ? 1 : 2, 'forfeit'), onResume: () => startQuoriTurnTimer(qroom, roomId, qroom.pausedTurnPlayer || 1) });
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
      proom.choices = {};
      clearPenaltyTurnTimers(proom);
      pauseAndWatch({
        room: proom, roomId, gameName: 'penalty',
        getP1: () => proom.players[1], getP2: () => proom.players[2],
        winFn: (winnerIsP1) => notifyPenaltyRoomOver(proom, roomId, winnerIsP1 ? 1 : 2, 'forfeit'),
        onResume: () => startPenaltyTurnTimer(proom, roomId)
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
      croom.choices = {};
      clearChifoumiTurnTimers(croom);
      pauseAndWatch({
        room: croom, roomId, gameName: 'chifoumi',
        getP1: () => croom.players[1], getP2: () => croom.players[2],
        winFn: (winnerIsP1) => notifyChifoumiRoomOver(croom, roomId, winnerIsP1 ? 1 : 2, 'forfeit'),
        onResume: () => startChifoumiTurnTimer(croom, roomId)
      });
      break;
    }
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`✅ Serveur Nano Banana v5.6 démarré sur le port ${PORT}`);
});
