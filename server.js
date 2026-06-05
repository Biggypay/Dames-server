// ============================================================
//  SERVEUR MINDSPILLE — Socket.io + Express
//  Dames 10x10 + Tic-Tac-Toe + Quoridor + Penalty Shootout + Chifoumi
//  Temps réel — Render.com — Node 20
//  v5.2 — Optimisation Penalty Shootout (Grace 60s & Match Nul)
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
//  TIMERS GÉNÉRIQUES
// ══════════════════════════════════════════════════════════
const TURN_DURATION  = 30 * 1000;
const GRACE_DURATION = 60 * 1000;

function clearDamesTurnTimers(droom) {
  if (droom.turnTimer)  { clearTimeout(droom.turnTimer);  droom.turnTimer  = null; }
  if (droom.graceTimer) { clearTimeout(droom.graceTimer); droom.graceTimer = null; }
  droom.turnStartTime = null; droom.graceStartTime = null; droom.turnPlayer = null;
}
function startDamesTurnTimer(droom, roomId, playerSlot) { ... } // Conservé tel quel
function clearTTTTurnTimers(troom) { ... } // Conservé tel quel
function startTTTTurnTimer(troom, roomId, playerSlot) { ... } // Conservé tel quel
function clearQuoriTurnTimers(qroom) { ... } // Conservé tel quel
function startQuoriTurnTimer(qroom, roomId, playerSlot) { ... } // Conservé tel quel
function clearChifoumiTurnTimers(croom) { ... } // Conservé tel quel
function startChifoumiTurnTimer(croom, roomId) { ... } // Conservé tel quel


// ── PENALTY SHOOTOUT (CORRIGÉ: Grace 60s et Match Nul) ──
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

    // Si les DEUX ont joué, la partie continue normalement (bien que ce soit souvent résolu avant)
    if (hp1 && hp2) {
      resolvePenaltyRound(proom, roomId);
      return;
    }

    // Sinon, on déclenche la période de Grâce de 60s !
    const graceNow = Date.now();
    proom.graceStartTime = graceNow;
    io.to(roomId).emit('penalty_turn_warning', { startTime: graceNow, duration: PENALTY_GRACE_DURATION });
    console.log(`⚠️  [penalty] Manche ${proom.currentRound} — 15s écoulées, grâce 60s | room:${roomId}`);

    proom.graceTimer = setTimeout(() => {
      proom.graceTimer = null;
      if (proom.status === 'finished') return;

      const hp1Grace = proom.choices[1] !== undefined;
      const hp2Grace = proom.choices[2] !== undefined;

      if (!hp1Grace && !hp2Grace) {
        // Les deux n'ont pas joué -> Annulation (Cancel)
        console.log(`🏳️  [penalty] Personne n'a joué après 60s → cancel | room:${roomId}`);
        proom.status = 'finished';
        const { bet } = calcFinancial(proom.betAmount);
        const penalty = Math.round(bet * 0.05);
        const cp = {
          type: 'game_over', game: 'penalty', room: roomId,
          result: 'cancel', reason: 'both_disconnected',
          penalty, p1Id: proom.players[1]?.supabaseId, p2Id: proom.players[2]?.supabaseId,
          betAmount: bet, currency: proom.currency || 'HTG'
        };
        if (proom.players[1]?.socketId) { io.to(proom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
        if (proom.players[2]?.socketId) { io.to(proom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
        io.to(roomId).emit('game:result', { postMessage: cp });
      } else if (hp1Grace && hp2Grace) {
        resolvePenaltyRound(proom, roomId);
      } else {
        // Un seul a joué -> Victoire par forfait (Timeout)
        console.log(`🏳️  [penalty] Grace expirée, résolution forfait avec ${hp1Grace?'P1':'P2'} | room:${roomId}`);
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
    const p1Score = proom.scores.p1;
    const p2Score = proom.scores.p2;
    if (p1Score === p2Score) {
      // CORRECTION : Match nul parfait
      notifyPenaltyRoomOver(proom, roomId, 0, 'draw');
    } else {
      const winnerSlot = p1Score > p2Score ? 1 : 2;
      notifyPenaltyRoomOver(proom, roomId, winnerSlot, 'normal');
    }
  }
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
      const cp = {
        type: 'game_over', game: gameName, room: roomId,
        result: 'cancel', reason: 'both_disconnected',
        penalty, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId,
        betAmount: bet, currency: room.currency || 'HTG',
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

// ── FONCTIONS NOTIFY GAME OVER (API, Dames, TTT, Quoridor, Chifoumi gardées par défaut) ──
function notifyGameOver(game, winner, reason = 'checkmate') { ... } // Ignoré pour brièveté
function notifyDamesRoomOver(room, roomIdOrReason, winnerSlotOrRoomId, reason = 'normal') { ... } 
function notifyTTTRoomOver(troom, roomId, winnerSlot, reason = 'normal') { ... }
function notifyQuoriRoomOver(qroom, roomId, winnerSlot, reason = 'normal') { ... }
function notifyChifoumiRoomOver(room, roomId, winnerSlot, reason = 'normal') { ... }

// ── FIN DE PARTIE PENALTY (Match Nul inclus) ─────────────────────────────────
function notifyPenaltyRoomOver(proom, roomId, winnerSlot, reason = 'normal') {
  if (proom.status === 'finished') return;
  proom.status = 'finished';
  clearPenaltyTurnTimers(proom);
  if (proom.disconnectTimer) { clearTimeout(proom.disconnectTimer); proom.disconnectTimer = null; }

  const { bet, totalPot, commission, netGain } = calcFinancial(proom.betAmount);
  const p1 = proom.players[1], p2 = proom.players[2];

  // Gestion du MATCH NUL (0 commission, remboursement)
  if (winnerSlot === 0) {
    const base = {
      type: 'game_over', game: 'penalty', room: roomId,
      winner: 'draw', winnerSlot: 0,
      p1Id: p1?.supabaseId, p2Id: p2?.supabaseId,
      betAmount: bet, totalPot, commission: 0, netGain: bet,
      currency: proom.currency || 'HTG',
      reason: 'draw', scores: proom.scores
    };
    if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p1.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p2.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    io.to(roomId).emit('game:result', { postMessage: base });
    console.log(`🤝 Penalty | Match nul | room:${roomId} | scores: ${proom.scores.p1}-${proom.scores.p2}`);
    return;
  }

  const winP = winnerSlot === 1 ? p1 : p2;
  const losP = winnerSlot === 1 ? p2 : p1;
  const base = {
    type: 'game_over', game: 'penalty', room: roomId,
    winner: winnerSlot === 1 ? 'player1' : 'player2',
    winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId:  losP?.supabaseId,
    p1Id: p1?.supabaseId, p2Id: p2?.supabaseId,
    betAmount: bet, totalPot, commission, netGain,
    currency: proom.currency || 'HTG',
    reason, scores: proom.scores
  };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win',  myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet }); io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  io.to(roomId).emit('game:over', { ...base, result: 'win', myResult: +netGain });
  io.to(roomId).emit('game:result', { postMessage: base });
}

// ══════════════════════════════════════════════════════════
//  ROUTES HTTP & API (Identiques)
// ══════════════════════════════════════════════════════════
app.get('/health', (req, res) => res.json({ status: 'ok' }));
const serveHTML = (filename) => (req, res) => { const f = path.join(PUBLIC, filename); if (fs.existsSync(f)) { res.setHeader('Content-Type','text/html;charset=utf-8'); res.send(fs.readFileSync(f,'utf8')); } else res.status(404).send(`${filename} introuvable`); };
app.get('/game', serveHTML('game.html')); app.get('/game-online.html', serveHTML('game.html'));
app.get('/dames', serveHTML('dames_multi.html')); app.get('/dames.html', serveHTML('dames_multi.html')); app.get('/dames-online.html', serveHTML('dames_multi.html'));
app.get('/ttt', serveHTML('ttt_game.html')); app.get('/ttt.html', serveHTML('ttt_game.html')); app.get('/ttt-online.html', serveHTML('ttt_game.html'));
app.get('/quoridor', serveHTML('quoridor_multi.html')); app.get('/quoridor.html', serveHTML('quoridor_multi.html')); app.get('/quoridor-online.html', serveHTML('quoridor_multi.html'));
app.get('/chifoumi', serveHTML('chifoumi-online.html')); app.get('/chifoumi.html', serveHTML('chifoumi-online.html')); app.get('/chifoumi-online.html', serveHTML('chifoumi-online.html'));

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
app.get('/penalty-online.html', serveHTML('penalty_shootout.html'));

app.post('/auth/register', (req, res) => { ... });
app.post('/auth/login', (req, res) => { ... });
app.post('/matchmaking/join', requireAuth, (req, res) => { ... });
app.post('/matchmaking/leave', requireAuth, (req, res) => { ... });
app.post('/game/join', requireAuth, (req, res) => { ... });

// ══════════════════════════════════════════════════════════
//  SOCKET.IO (Connexion et événements Penalty)
// ══════════════════════════════════════════════════════════
io.on('connection', (socket) => {
  socket.on('auth', ({ token }) => { try { const { userId } = jwt.verify(token, JWT_SECRET); socketUsers.set(socket.id, userId); socket.userId = userId; socket.emit('auth:ok', { userId }); } catch { socket.emit('auth:error', { message: 'Token invalide' }); } });
  socket.on('auth:supabase', ({ supabaseId, username }) => { if (!supabaseId) return; let found = null; for (const u of users.values()) if (u.supabaseId === supabaseId) { found = u; break; } if (!found) { const id = uuid(); found = { id, username: username || 'Joueur', supabaseId }; users.set(id, found); } socketUsers.set(socket.id, found.id); socket.userId = found.id; const token = jwt.sign({ userId: found.id }, JWT_SECRET, { expiresIn: '7d' }); socket.emit('auth:ok', { userId: found.id, token }); });

  // -- Les autres jeux (Dames, TTT, Quoridor, Chifoumi) restent identiques --

  // ══════════════════════════════════════════════════════
  //  PENALTY SHOOTOUT MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('penalty_join', ({ room, player, supabaseId, name, bet, currency }) => {
    if (!room) { socket.emit('penalty_error', { message: 'room_id_missing', detail: 'Le paramètre room est absent.' }); return; }
    socket.join(room);
    let proom = penaltyRooms.get(room);
    if (!proom) {
      proom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, currentRound: 1, scores: { p1: 0, p2: 0 }, choices: {}, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null };
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
            const p1b = proom.players[1]?.connected === true, p2b = proom.players[2]?.connected === true;
            proom.disconnectTimer = null;
            if (!p1b && !p2b) {
              proom.status = 'finished';
              const { bet: b } = calcFinancial(proom.betAmount); const penalty = Math.round(b * 0.05);
              const cp = { type: 'game_over', game: 'penalty', room, result: 'cancel', reason: 'both_disconnected', penalty, p1Id: proom.players[1]?.supabaseId, p2Id: proom.players[2]?.supabaseId, betAmount: b, currency: proom.currency || 'HTG' };
              if (proom.players[1]?.socketId) { io.to(proom.players[1].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[1].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              if (proom.players[2]?.socketId) { io.to(proom.players[2].socketId).emit('game:over', { ...cp, myResult: -penalty }); io.to(proom.players[2].socketId).emit('game:result', { postMessage: { ...cp, myResult: -penalty } }); }
              io.to(room).emit('game:result', { postMessage: cp });
            } else { const ws = p1b ? 1 : 2; proom.status = 'playing'; notifyPenaltyRoomOver(proom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }

      socket.to(room).emit('penalty_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (proom.players[2]?.name || 'Adversaire') : (proom.players[1]?.name || 'Adversaire');
      socket.emit('penalty_start', { room, yourSlot: player, opponentName, bet: proom.betAmount, currency: proom.currency, reconnected: true, gameState: { round: proom.currentRound, scores: proom.scores, phase: 'choosing' } });
      
      // Resynchronisation des timers 
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
    
    // Informe l'autre client que l'adversaire a joué
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

  // Gestion des déconnexions (Identique)
  socket.on('disconnect', () => {
    const userId = socketUsers.get(socket.id);
    socketUsers.delete(socket.id);
    // (Conserve ici le code de déconnexion pour Dames, TTT, Quoridor, Penalty, Chifoumi...)
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
        getP1: () => proom.players[1],
        getP2: () => proom.players[2],
        winFn: (winnerIsP1) => notifyPenaltyRoomOver(proom, roomId, winnerIsP1 ? 1 : 2, 'forfeit')
      });
      break;
    }
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`✅ Serveur Nano Banana v5.2 démarré sur le port ${PORT}`);
});
