// ============================================================
//  SERVEUR MINDSPILLE — Socket.io + Express
//  Dames 10x10 + Tic-Tac-Toe — Matchmaking + Temps réel
//  Render.com — Node 20
//  v3.4 — Intégration Dames Multi + Sync Financière
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
const tttGames    = new Map();
const damesRooms  = new Map();

// ── MOTEUR DAMES 10x10 (Logique de base) ─────────────────
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

// Fonctions de calcul de coups (utilisées pour la validation si nécessaire)
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

function applyMove(board, player, fromR, fromC, toR, toC) {
  const nb = copyB(board), piece = nb[fromR][fromC];
  nb[toR][toC] = piece; nb[fromR][fromC] = EMPTY;
  // Promotion simplifiée
  if (piece === WHITE && toR === 0) nb[toR][toC] = WKING;
  if (piece === BLACK && toR === 9) nb[toR][toC] = BKING;
  return { ok: true, board: nb };
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

// ── CALCUL FINANCIER ──────────────────────────────────────
function calcFinancial(betAmount) {
  const bet      = betAmount || 0;
  const totalPot = bet * 2;
  const commission = Math.round(totalPot * 0.10);
  const netGain  = totalPot - commission;
  return { bet, totalPot, commission, netGain };
}

// ══════════════════════════════════════════════════════════
//  TIMERS DE TOUR — DAMES MULTIJOUEUR
// ══════════════════════════════════════════════════════════
const TURN_DURATION  = 30 * 1000;
const GRACE_DURATION = 60 * 1000;

function clearDamesTurnTimers(droom) {
  if (droom.turnTimer)  { clearTimeout(droom.turnTimer);  droom.turnTimer  = null; }
  if (droom.graceTimer) { clearTimeout(droom.graceTimer); droom.graceTimer = null; }
  droom.turnStartTime  = null;
  droom.graceStartTime = null;
  droom.turnPlayer     = null;
}

function startDamesTurnTimer(droom, roomId, playerSlot) {
  clearDamesTurnTimers(droom);
  if (droom.status === 'finished') return;

  const now = Date.now();
  droom.turnPlayer    = playerSlot;
  droom.turnStartTime = now;
  droom.graceStartTime = null;

  io.to(roomId).emit('dames_turn_start', {
    player:    playerSlot,
    startTime: now,
    duration:  TURN_DURATION,
  });

  droom.turnTimer = setTimeout(() => {
    droom.turnTimer = null;
    if (droom.status === 'finished') return;

    const graceNow = Date.now();
    droom.graceStartTime = graceNow;

    io.to(roomId).emit('dames_turn_warning', {
      player:    playerSlot,
      startTime: graceNow,
      duration:  GRACE_DURATION,
    });

    droom.graceTimer = setTimeout(() => {
      droom.graceTimer = null;
      if (droom.status === 'finished') return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      notifyDamesRoomOver(droom, winnerSlot, 'timeout');
    }, GRACE_DURATION);

  }, TURN_DURATION);
}

// ══════════════════════════════════════════════════════════
//  SYSTÈME UNIVERSEL PAUSE / REPRISE / ANNULATION
// ══════════════════════════════════════════════════════════
function pauseAndWatch({ room, roomId, gameName, getP1, getP2, winFn }) {
  if (room.disconnectTimer) return;
  room.status = 'paused';
  console.log(`⏸️  [${gameName}] Partie en pause | room:${roomId}`);

  room.disconnectTimer = setTimeout(() => {
    if (room.status === 'finished') return;
    room.disconnectTimer = null;

    const p1 = getP1();
    const p2 = getP2();
    const p1back = p1?.connected === true;
    const p2back = p2?.connected === true;

    if (p1back && p2back) {
      room.status = 'playing';
      return;
    }

    if (!p1back && !p2back) {
      room.status = 'finished';
      const { bet } = calcFinancial(room.betAmount);
      const penalty = Math.round(bet * 0.05);
      const cancelPayload = {
        type:     'game_over',
        game:     gameName,
        room:     roomId,
        result:   'cancel',
        reason:   'both_disconnected',
        penalty,
        p1Id:     p1?.supabaseId,
        p2Id:     p2?.supabaseId,
        betAmount: bet,
        currency: room.currency || 'HTG',
        message:  'Les deux joueurs se sont déconnectés. Pénalité de 5% appliquée.',
      };
      if (p1?.socketId) io.to(p1.socketId).emit('game:over',   { ...cancelPayload, myResult: -penalty });
      if (p1?.socketId) io.to(p1.socketId).emit('game:result', { postMessage: { ...cancelPayload, myResult: -penalty } });
      if (p2?.socketId) io.to(p2.socketId).emit('game:over',   { ...cancelPayload, myResult: -penalty });
      if (p2?.socketId) io.to(p2.socketId).emit('game:result', { postMessage: { ...cancelPayload, myResult: -penalty } });
      io.to(roomId).emit('game:result', { postMessage: cancelPayload });
    } else {
      const winnerIsP1 = p1back;
      room.status = 'playing';
      winFn(winnerIsP1);
    }
  }, 60000);
}

// ── NOTIFICATION FIN DE PARTIE DAMES (API REST) ───────────
function notifyGameOver(game, winner, reason = 'checkmate') {
  if (game.status === 'finished') return;
  game.status = 'finished'; game.winner = winner;
  if (game.disconnectTimer) { clearTimeout(game.disconnectTimer); game.disconnectTimer = null; }
  const winnerId = winner === 'white' ? game.playerWhite : game.playerBlack;
  const loserId  = winner === 'white' ? game.playerBlack : game.playerWhite;
  const wUser    = users.get(winnerId);
  const lUser    = users.get(loserId);
  const { bet, totalPot, commission, netGain } = calcFinancial(game.betAmount);
  const base = {
    type:             'game_over',
    gameId:           game.id,
    winner:           winner === 'white' ? 'player1' : 'player2',
    winnerColor:      winner,
    winnerName:       wUser?.username,
    loserName:        lUser?.username,
    winnerSupabaseId: wUser?.supabaseId,
    loserSupabaseId:  lUser?.supabaseId,
    betAmount:        bet,
    totalPot,
    commission,
    netGain,
    reason,
  };
  emitToUser(winnerId, 'game:over',   { ...base, result: 'win',  myResult: +netGain });
  emitToUser(winnerId, 'game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } });
  emitToUser(loserId,  'game:over',   { ...base, result: 'loss', myResult: -bet });
  emitToUser(loserId,  'game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } });
  io.to(game.id).emit('game:over',   { ...base, result: 'win', myResult: +netGain });
  io.to(game.id).emit('game:result', { postMessage: { ...base, result: 'win', myResult: +netGain } });
}

// ── NOTIFICATION FIN DE PARTIE DAMES MULTIJOUEUR ─────────
function notifyDamesRoomOver(room, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return;
  room.status = 'finished';
  clearDamesTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }

  const { bet, totalPot, commission, netGain } = calcFinancial(room.betAmount);
  const p1 = room.players[1];
  const p2 = room.players[2];
  const winnerPlayer = winnerSlot === 1 ? p1 : p2;
  const loserPlayer  = winnerSlot === 1 ? p2 : p1;

  const base = {
    type:             'game_over',
    game:             'dames',
    room:             room.id,
    winner:           winnerSlot === 1 ? 'player1' : 'player2',
    winnerSlot,
    winnerSupabaseId: winnerPlayer?.supabaseId,
    loserSupabaseId:  loserPlayer?.supabaseId,
    p1Id:             p1?.supabaseId,
    p2Id:             p2?.supabaseId,
    betAmount:        bet,
    totalPot,
    commission,
    netGain,
    currency:         room.currency || 'HTG',
    reason,
  };

  if (winnerPlayer?.socketId) {
    io.to(winnerPlayer.socketId).emit('game:over',   { ...base, result: 'win',  myResult: +netGain });
    io.to(winnerPlayer.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } });
  }
  if (loserPlayer?.socketId) {
    io.to(loserPlayer.socketId).emit('game:over',   { ...base, result: 'loss', myResult: -bet });
    io.to(loserPlayer.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } });
  }
  io.to(room.id).emit('game:over',   { ...base, result: 'win', myResult: +netGain });
  io.to(room.id).emit('game:result', { postMessage: base });
  console.log(`🏆 Dames Multi | Slot${winnerSlot} gagne | mise:${bet} HTG | room:${room.id}`);
}

// ══════════════════════════════════════════════════════════
//  ROUTES (Inchangées)
// ══════════════════════════════════════════════════════════
app.get('/health', (req, res) => res.json({
  status: 'ok', time: new Date().toISOString(),
  games: games.size,
  damesRooms: damesRooms.size,
  tttGames: tttGames.size,
  queue: [...queue.entries()].map(([amt, p]) => ({ betAmount: amt, waiting: p.length }))
}));

app.get('/game', (req, res) => {
  const f = path.join(PUBLIC, 'game.html');
  if (fs.existsSync(f)) { res.setHeader('Content-Type', 'text/html; charset=utf-8'); res.send(fs.readFileSync(f, 'utf8')); }
  else res.status(404).send('game.html introuvable');
});

app.get('/dames', (req, res) => {
  const f = path.join(PUBLIC, 'dames_multi.html');
  if (fs.existsSync(f)) { res.setHeader('Content-Type', 'text/html; charset=utf-8'); res.send(fs.readFileSync(f, 'utf8')); }
  else res.status(404).send('dames_multi.html introuvable');
});

app.get('/ttt', (req, res) => {
  const f = path.join(PUBLIC, 'ttt_game.html');
  if (fs.existsSync(f)) { res.setHeader('Content-Type', 'text/html; charset=utf-8'); res.send(fs.readFileSync(f, 'utf8')); }
  else res.status(404).send('ttt_game.html introuvable');
});

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
  const userId = req.userId;
  let user = users.get(userId);
  if (!user) { user = { id: userId, username: username || 'Joueur', supabaseId: supabaseId || null }; users.set(userId, user); }
  const existing = queue.get(betAmount) || [];
  const opponent = existing.find(p => p.userId !== userId);
  if (opponent) {
    queue.set(betAmount, existing.filter(p => p.userId !== opponent.userId));
    const whiteId = userId, blackId = opponent.userId, gameId = uuid();
    games.set(gameId, { id: gameId, playerWhite: whiteId, playerBlack: blackId, board: initialBoard(), currentPlayer: 'white', status: 'playing', betAmount });
    emitToUser(whiteId, 'match:found', { gameId, youAre: 'white', betAmount });
    emitToUser(blackId, 'match:found', { gameId, youAre: 'black', betAmount });
    return res.json({ status: 'matched', gameId });
  } else {
    existing.push({ userId, username: user.username, supabaseId: user.supabaseId });
    queue.set(betAmount, existing);
    return res.json({ status: 'waiting' });
  }
});

// ══════════════════════════════════════════════════════════
//  SOCKET.IO LOGIQUE CENTRALE
// ══════════════════════════════════════════════════════════
io.on('connection', (socket) => {
  console.log('🔌 Nouveau socket:', socket.id);

  socket.on('auth:supabase', ({ supabaseId, username }) => {
    if (!supabaseId) return;
    let found = null;
    for (const u of users.values()) if (u.supabaseId === supabaseId) { found = u; break; }
    if (!found) { const id = uuid(); found = { id, username: username || 'Joueur', supabaseId }; users.set(id, found); }
    socketUsers.set(socket.id, found.id); socket.userId = found.id;
    const token = jwt.sign({ userId: found.id }, JWT_SECRET, { expiresIn: '7d' });
    socket.emit('auth:ok', { userId: found.id, token });
  });

  // ── DAMES MULTIJOUEUR ──
  socket.on('dames_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return;
    socket.join(room);

    let droom = damesRooms.get(room);
    if (!droom) {
      droom = {
        id: room, players: {}, status: 'waiting',
        betAmount: bet || 0, currency: currency || 'HTG',
        disconnectTimer: null, boardState: null,
        currentPlayer: 0, lastMove: null,
      };
      damesRooms.set(room, droom);
    }

    droom.players[player] = { socketId: socket.id, supabaseId, name, slot: player, connected: true };
    
    if (droom.players[1] && droom.players[2] && droom.status === 'waiting') {
      droom.status = 'playing';
      io.to(droom.players[1].socketId).emit('dames_start', { room, yourSlot: 1, opponentName: droom.players[2].name, bet: droom.betAmount });
      io.to(droom.players[2].socketId).emit('dames_start', { room, yourSlot: 2, opponentName: droom.players[1].name, bet: droom.betAmount });
      setTimeout(() => startDamesTurnTimer(droom, room, 1), 2000);
    } else if (droom.status === 'playing') {
      // Reconnexion
      socket.emit('dames_start', { room, yourSlot: player, reconnected: true, boardState: droom.boardState, currentPlayer: droom.currentPlayer });
    }
  });

  socket.on('dames_move', ({ room, player, from, to, steps, boardState, nextPlayer, isComplete }) => {
    const droom = damesRooms.get(room);
    if (droom) {
      droom.boardState = boardState;
      droom.currentPlayer = nextPlayer;
      if (isComplete !== false) {
        const nextSlot = nextPlayer + 1;
        startDamesTurnTimer(droom, room, nextSlot);
      }
      socket.to(room).emit('dames_move', { player, steps, boardState, nextPlayer, isComplete });
    }
  });

  socket.on('dames_result', (data) => {
    const droom = damesRooms.get(data.room);
    if (!droom) return;
    const winnerSlot = data.winner === data.p1Id ? 1 : 2;
    notifyDamesRoomOver(droom, winnerSlot, data.reason || 'normal');
  });

  // ── TIC-TAC-TOE ──
  socket.on('ttt:join', ({ gameId, playerId, betAmount }) => {
    socket.join(gameId);
    let game = tttGames.get(gameId);
    if (!game) {
      game = { id: gameId, players: [{ socketId: socket.id, userId: playerId, symbol: 'X' }], board: Array(9).fill(null), curTurn: 'X', status: 'waiting', betAmount };
      tttGames.set(gameId, game);
    } else if (game.players.length === 1) {
      game.players.push({ socketId: socket.id, userId: playerId, symbol: 'O' });
      game.status = 'playing';
      io.to(gameId).emit('ttt:ready', { gameId, betAmount: game.betAmount });
    }
  });

  socket.on('ttt:move', ({ gameId, cell, symbol }) => {
    const game = tttGames.get(gameId);
    if (game && game.curTurn === symbol) {
      game.board[cell] = symbol;
      game.curTurn = symbol === 'X' ? 'O' : 'X';
      socket.to(gameId).emit('ttt:move', { cell, symbol });
    }
  });

  socket.on('ttt:match_over', ({ gameId, winner, scores }) => {
    const game = tttGames.get(gameId);
    if (game && game.status !== 'finished') {
      game.status = 'finished';
      const { bet, netGain } = calcFinancial(game.betAmount);
      io.to(gameId).emit('game:over', { winner, betAmount: bet, netGain });
    }
  });

  // ── DÉCONNEXION ──
  socket.on('disconnect', () => {
    const userId = socketUsers.get(socket.id);
    // Logique Dames Multi
    for (const [roomId, droom] of damesRooms.entries()) {
      for (const slot in droom.players) {
        if (droom.players[slot].socketId === socket.id) {
          droom.players[slot].connected = false;
          socket.to(roomId).emit('dames_player_status', { slot, connected: false });
          pauseAndWatch({
            room: droom, roomId, gameName: 'dames',
            getP1: () => droom.players[1], getP2: () => droom.players[2],
            winFn: (p1Win) => notifyDamesRoomOver(droom, p1Win ? 1 : 2, 'forfeit')
          });
        }
      }
    }
    socketUsers.delete(socket.id);
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`✅ Serveur MINDSPILLE v3.4 actif sur le port ${PORT}`);
});
