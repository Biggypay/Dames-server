// ============================================================
//  SERVEUR MINDSPILLE — Socket.io + Express
//  Dames 10x10 + Tic-Tac-Toe — Matchmaking + Temps réel
//  Render.com — Node 20
//  v3.3 — Fix synchronisation prises multiples + robustesse
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
const PORT   = process.env.PORT || 3000;

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
const users        = new Map();
const games        = new Map();
const queue        = new Map();
const socketUsers  = new Map();
const tttGames     = new Map();
const damesRooms   = new Map();

// ── MOTEUR DAMES 10x10 ─────────────────────────────────────
const EMPTY=0, WHITE=1, BLACK=2, WKING=3, BKING=4;

const isKing  = p => p === WKING || p === BKING;
const isWhite = p => p === WHITE || p === WKING;
const isBlack = p => p === BLACK || p === BKING;
const isOwn   = (p, pl) => pl === 'white' ? isWhite(p) : isBlack(p);
const isEnemy = (p, pl) => pl === 'white' ? isBlack(p) : isWhite(p);
const inBounds = (r, c) => r >= 0 && r < 10 && c >= 0 && c < 10;
const copyB   = b => b.map(r => [...r]);

function initialBoard() {
  const b = Array.from({length: 10}, () => Array(10).fill(EMPTY));
  for (let r = 0; r < 4; r++) for (let c = 0; c < 10; c++) if ((r + c) % 2 === 1) b[r][c] = BLACK;
  for (let r = 6; r < 10; r++) for (let c = 0; c < 10; c++) if ((r + c) % 2 === 1) b[r][c] = WHITE;
  return b;
}

// ... (toutes tes fonctions getSimpleMoves, getCaptures, getAllCaptures, hasAnyMove, applyMove restent identiques)
// Je les garde pour ne pas alourdir, mais elles sont inchangées par rapport à ta v3.2

const getSimpleMoves = /* ... ta fonction originale ... */;
const getCaptures = /* ... ta fonction originale ... */;
const getAllCaptures = /* ... ta fonction originale ... */;
const hasAnyMove = /* ... ta fonction originale ... */;
const applyMove = /* ... ta fonction originale ... */;

// ── AUTH & UTILS ───────────────────────────────────────────
function requireAuth(req, res, next) {
  const h = req.headers['authorization'] || '';
  if (!h.startsWith('Bearer ')) return res.status(401).json({ error: 'Token manquant' });
  try {
    req.userId = jwt.verify(h.slice(7), JWT_SECRET).userId;
    next();
  } catch { res.status(401).json({ error: 'Token invalide' }); }
}

function emitToUser(userId, event, data) {
  for (const [sid, uid] of socketUsers.entries()) {
    if (uid === userId) io.to(sid).emit(event, data);
  }
}

function calcFinancial(betAmount) {
  const bet = betAmount || 0;
  const totalPot = bet * 2;
  const commission = Math.round(totalPot * 0.10);
  const netGain = totalPot - commission;
  return { bet, totalPot, commission, netGain };
}

// ── TIMERS DAMES ───────────────────────────────────────────
const TURN_DURATION  = 30 * 1000;
const GRACE_DURATION = 60 * 1000;

function clearDamesTurnTimers(droom) {
  if (droom.turnTimer)  { clearTimeout(droom.turnTimer);  droom.turnTimer = null; }
  if (droom.graceTimer) { clearTimeout(droom.graceTimer); droom.graceTimer = null; }
  droom.turnStartTime = null;
  droom.graceStartTime = null;
  droom.turnPlayer = null;
}

function startDamesTurnTimer(droom, roomId, playerSlot) {
  clearDamesTurnTimers(droom);
  if (droom.status === 'finished') return;

  const now = Date.now();
  droom.turnPlayer = playerSlot;
  droom.turnStartTime = now;

  io.to(roomId).emit('dames_turn_start', {
    player: playerSlot,
    startTime: now,
    duration: TURN_DURATION,
  });

  droom.turnTimer = setTimeout(() => {
    if (droom.status === 'finished') return;

    const graceNow = Date.now();
    droom.graceStartTime = graceNow;

    io.to(roomId).emit('dames_turn_warning', {
      player: playerSlot,
      startTime: graceNow,
      duration: GRACE_DURATION,
    });

    droom.graceTimer = setTimeout(() => {
      if (droom.status === 'finished') return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      notifyDamesRoomOver(droom, winnerSlot, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// ── PAUSE / RECONNEXION ─────────────────────────────────────
function pauseAndWatch({ room, roomId, gameName, getP1, getP2, winFn }) {
  if (room.disconnectTimer) return;
  room.status = 'paused';

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
        type: 'game_over',
        game: gameName,
        room: roomId,
        result: 'cancel',
        reason: 'both_disconnected',
        penalty,
        p1Id: p1?.supabaseId,
        p2Id: p2?.supabaseId,
        betAmount: bet,
        currency: room.currency || 'HTG',
        message: 'Les deux joueurs se sont déconnectés. Pénalité de 5% appliquée.'
      };
      io.to(roomId).emit('game:over', cancelPayload);
      io.to(roomId).emit('game:result', { postMessage: cancelPayload });
    } else {
      const winnerIsP1 = p1back;
      room.status = 'playing';
      winFn(winnerIsP1);
    }
  }, 60000);
}

function resumeGame({ room, roomId, gameName }) {
  if (!room.disconnectTimer) return false;
  clearTimeout(room.disconnectTimer);
  room.disconnectTimer = null;
  room.status = 'playing';
  io.to(roomId).emit('dames_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
  return true;
}

// ── NOTIFICATION FIN DE PARTIE ─────────────────────────────
function notifyDamesRoomOver(room, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return;
  room.status = 'finished';
  clearDamesTurnTimers(room);
  if (room.disconnectTimer) {
    clearTimeout(room.disconnectTimer);
    room.disconnectTimer = null;
  }

  const { bet, totalPot, commission, netGain } = calcFinancial(room.betAmount);
  const p1 = room.players[1];
  const p2 = room.players[2];
  const winnerPlayer = winnerSlot === 1 ? p1 : p2;
  const loserPlayer  = winnerSlot === 1 ? p2 : p1;

  const base = {
    type: 'game_over',
    game: 'dames',
    room: room.id,
    winner: winnerSlot === 1 ? 'player1' : 'player2',
    winnerSlot,
    winnerSupabaseId: winnerPlayer?.supabaseId,
    loserSupabaseId: loserPlayer?.supabaseId,
    p1Id: p1?.supabaseId,
    p2Id: p2?.supabaseId,
    betAmount: bet,
    totalPot,
    commission,
    netGain,
    currency: room.currency || 'HTG',
    reason,
  };

  const winPayload  = { ...base, result: 'win',  myResult: +netGain };
  const losePayload = { ...base, result: 'loss', myResult: -bet };

  if (winnerPlayer?.socketId) {
    io.to(winnerPlayer.socketId).emit('game:over', winPayload);
    io.to(winnerPlayer.socketId).emit('game:result', { postMessage: winPayload });
  }
  if (loserPlayer?.socketId) {
    io.to(loserPlayer.socketId).emit('game:over', losePayload);
    io.to(loserPlayer.socketId).emit('game:result', { postMessage: losePayload });
  }
  io.to(room.id).emit('game:over', winPayload);
  io.to(room.id).emit('game:result', { postMessage: winPayload });

  console.log(`🏆 Dames Multi | Slot${winnerSlot} gagne | room:${room.id} | mise:${bet} | raison:${reason}`);
}

// ══════════════════════════════════════════════════════════
//  ROUTES (inchangées)
// ══════════════════════════════════════════════════════════
// ... toutes tes routes (/health, /game, /dames, /ttt, auth, matchmaking, etc.) restent identiques à ta version originale

// (Pour ne pas surcharger le message, je les ai omises ici, mais tu peux les garder exactement comme avant)

// ══════════════════════════════════════════════════════════
//  SOCKET.IO
// ══════════════════════════════════════════════════════════
io.on('connection', (socket) => {
  console.log('🔌 Connexion:', socket.id);

  socket.on('auth', ({ token }) => {
    try {
      const { userId } = jwt.verify(token, JWT_SECRET);
      socketUsers.set(socket.id, userId);
      socket.userId = userId;
      socket.emit('auth:ok', { userId });
    } catch {
      socket.emit('auth:error', { message: 'Token invalide' });
    }
  });

  socket.on('auth:supabase', ({ supabaseId, username }) => {
    if (!supabaseId) return;
    let found = [...users.values()].find(u => u.supabaseId === supabaseId);
    if (!found) {
      const id = uuid();
      found = { id, username: username || 'Joueur', supabaseId };
      users.set(id, found);
    }
    socketUsers.set(socket.id, found.id);
    socket.userId = found.id;
    const token = jwt.sign({ userId: found.id }, JWT_SECRET, { expiresIn: '7d' });
    socket.emit('auth:ok', { userId: found.id, token });
  });

  socket.on('game:join_room', ({ gameId }) => socket.join(gameId));

  // ====================== DAMES MULTIJOUEUR ======================
  socket.on('dames_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) return;
    socket.join(room);

    let droom = damesRooms.get(room);
    if (!droom) {
      droom = {
        id: room,
        players: {},
        status: 'waiting',
        betAmount: bet || 0,
        currency: currency || 'HTG',
        disconnectTimer: null,
        boardState: null,
        currentPlayer: 0,
        lastMove: null,
        turnTimer: null,
        graceTimer: null,
        turnStartTime: null,
        graceStartTime: null,
        turnPlayer: null,
      };
      damesRooms.set(room, droom);
    }

    droom.players[player] = {
      socketId: socket.id,
      supabaseId,
      name: name || `Joueur ${player}`,
      slot: player,
      connected: true
    };

    if (bet && !droom.betAmount) droom.betAmount = bet;

    console.log(`♟️ Dames Join | Slot ${player} (${name}) | room:${room} | status:${droom.status}`);

    // Reconnexion
    if (droom.status === 'playing' || droom.status === 'paused') {
      const p1 = droom.players[1];
      const p2 = droom.players[2];
      const bothBack = p1?.connected && p2?.connected;

      if (bothBack && droom.disconnectTimer) resumeGame({ room: droom, roomId: room, gameName: 'dames' });

      socket.to(room).emit('dames_player_status', { slot: player, connected: true, name: droom.players[player].name });

      socket.emit('dames_start', {
        room,
        yourSlot: player,
        opponentName: player === 1 ? (p2?.name || 'Adversaire') : (p1?.name || 'Adversaire'),
        bet: droom.betAmount,
        currency: droom.currency,
        reconnected: true,
        boardState: droom.boardState,
        currentPlayer: droom.currentPlayer,
        lastMove: droom.lastMove
      });

      // Resync timer
      if (droom.turnPlayer !== null) {
        const now = Date.now();
        if (droom.graceStartTime) {
          socket.emit('dames_turn_sync', { serverTime: now, turnPlayer: droom.turnPlayer, graceStartTime: droom.graceStartTime, duration: GRACE_DURATION });
        } else if (droom.turnStartTime) {
          socket.emit('dames_turn_sync', { serverTime: now, turnPlayer: droom.turnPlayer, turnStartTime: droom.turnStartTime, duration: TURN_DURATION });
        }
      }
      return;
    }

    // Démarrage de partie quand les deux sont là
    if (droom.players[1] && droom.players[2] && droom.status === 'waiting') {
      droom.status = 'playing';

      io.to(droom.players[1].socketId).emit('dames_start', {
        room, yourSlot: 1, opponentName: droom.players[2].name,
        bet: droom.betAmount, currency: droom.currency, reconnected: false
      });
      io.to(droom.players[2].socketId).emit('dames_start', {
        room, yourSlot: 2, opponentName: droom.players[1].name,
        bet: droom.betAmount, currency: droom.currency, reconnected: false
      });

      console.log(`✅ Dames Démarrée | ${droom.players[1].name} vs ${droom.players[2].name} | room:${room}`);

      setTimeout(() => {
        if (droom.status === 'playing') startDamesTurnTimer(droom, room, 1);
      }, 3000);
    }
  });

  // ====================== DAMES MOVE — VERSION CORRIGÉE ======================
  socket.on('dames_move', ({ room, player, from, to, steps, boardState, nextPlayer, isComplete }) => {
    const droom = damesRooms.get(room);
    if (!droom || droom.status !== 'playing') return;

    // Sauvegarde état pour reconnexion
    droom.boardState = boardState || null;
    droom.currentPlayer = nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0);

    if (steps && steps.length > 0) {
      droom.lastMove = { from: steps[0].from, to: steps[steps.length - 1].to, player };
    } else if (from && to) {
      droom.lastMove = { from, to, player };
    }

    // ÉMISSION FIABLE À L'ADVERSAIRE
    socket.to(room).emit('dames_move', {
      room,
      player,
      steps: steps || [{ from, to }],
      boardState: boardState || null,
      nextPlayer: nextPlayer !== undefined ? nextPlayer : (player === 1 ? 1 : 0),
      isComplete: isComplete !== false
    });

    // Redémarrer le timer adverse UNIQUEMENT à la fin de la séquence
    if (isComplete !== false) {
      const nextSlot = (nextPlayer !== undefined) ? nextPlayer + 1 : (player === 1 ? 2 : 1);
      startDamesTurnTimer(droom, room, nextSlot);
    }
  });

  socket.on('dames_result', (data) => {
    const droom = damesRooms.get(data.room);
    if (!droom) return;
    const winnerSlot = data.winner === data.p1Id ? 1 : 2;
    notifyDamesRoomOver(droom, winnerSlot, data.reason || 'normal');
  });

  // ====================== TTT (inchangé) ======================
  // ... tout ton code TTT reste identique ...

  // ====================== DISCONNECT ======================
  socket.on('disconnect', () => {
    const userId = socketUsers.get(socket.id);
    socketUsers.delete(socket.id);

    // Gestion déconnexion Dames Multijoueur
    for (const [roomId, droom] of damesRooms.entries()) {
      if (droom.status !== 'playing' && droom.status !== 'paused') continue;

      let disconnectedSlot = null;
      for (const [slot, p] of Object.entries(droom.players)) {
        if (p.socketId === socket.id) {
          disconnectedSlot = parseInt(slot);
          break;
        }
      }
      if (disconnectedSlot === null) continue;

      droom.players[disconnectedSlot].connected = false;
      socket.to(roomId).emit('dames_player_status', { slot: disconnectedSlot, connected: false });
      socket.to(roomId).emit('dames_opponent_disconnected', { slot: disconnectedSlot, message: 'Adversaire déconnecté.' });

      pauseAndWatch({
        room: droom,
        roomId,
        gameName: 'dames',
        getP1: () => droom.players[1],
        getP2: () => droom.players[2],
        winFn: (winnerIsP1) => notifyDamesRoomOver(droom, winnerIsP1 ? 1 : 2, 'forfeit')
      });
      break;
    }

    console.log('🔌 Déconnexion:', socket.id);
  });
});

// Routes (à remettre ici si tu veux le fichier complet)
// Pour l'instant je les ai laissées de côté pour la lisibilité, mais tu peux copier tes routes originales juste avant le io.on('connection'

server.listen(PORT, '0.0.0.0', () => {
  console.log(`✅ Serveur Mindspille v3.3 démarré sur le port ${PORT}`);
  console.log(`   /dames  → Dames 3D Multijoueur`);
  console.log(`   /health → Status`);
});
