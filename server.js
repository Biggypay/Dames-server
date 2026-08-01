// ============================================================
//  SERVEUR NANO BANANA — Socket.io + Express
//  Dames 10x10 + Tic-Tac-Toe + Quoridor + Penalty Shootout + Chifoumi + Échecs
//  Temps réel — Node 20
//  v5.7 — Ajout des Échecs (règles FIDE, moteur autoritatif serveur)
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
// Moteur d'échecs FIDE partagé (même code que les pages 3D et le Worker IA).
const { ChessEngineFactory } = require('./public/echecs-engine.js');
const ChessEngine = ChessEngineFactory();
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
// Production, Lovable preview and installed-app origins. These first-party
// origins must remain accepted even when Render still has an older, narrower
// ALLOWED_ORIGIN value (for example only mindspille.lovable.app).
const FIRST_PARTY_ORIGINS = new Set([
  'https://mindspille.com',
  'https://www.mindspille.com',
  'https://mindspille.lovable.app',
  // Online game pages are served in an iframe by this Render service. Their
  // Socket.io handshake therefore carries the game-server origin, not the
  // parent Lovable origin. Omitting it loads the HTML but rejects the socket
  // with Engine.IO code 4 (Forbidden), leaving ROOM/SLOT on screen forever.
  'https://games-server-top9.onrender.com',
  'https://dames-server.onrender.com',
  ...[process.env.RENDER_EXTERNAL_URL, process.env.GAME_SERVER_PUBLIC_URL]
    .filter(Boolean)
    .map(value => String(value).replace(/\/$/, '')),
  'capacitor://localhost',
  'ionic://localhost',
  'http://localhost',
  'https://localhost'
]);

// Autorise les origines configurées + tout sous-domaine *.lovable.app
// (site publié, aperçu id-preview--..., remix, PWA installée) : l'appli
// MindSpille tourne sur lovable.app et doit pouvoir interroger /health,
// ouvrir les sockets et intégrer les jeux en iframe.
function originMatches(pattern, origin) {
  if (pattern === origin) return true;
  if (pattern === 'https://*.lovable.app') return /^https:\/\/[a-z0-9-]+\.lovable\.app$/i.test(origin);
  return false;
}
function isAllowedOrigin(origin) {
  if (!origin) return false;
  if (FIRST_PARTY_ORIGINS.has(origin)) return true;
  if (/^https:\/\/[a-z0-9-]+\.lovable\.app$/i.test(origin)) return true;
  if (ALLOWED_ORIGINS === '*') return true;
  return Array.isArray(ALLOWED_ORIGINS) && ALLOWED_ORIGINS.some(pattern => originMatches(pattern, origin));
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
const FRAME_ANCESTORS = Array.from(new Set([
  "'self'",
  'https://mindspille.com',
  'https://www.mindspille.com',
  'https://mindspille.lovable.app',
  'https://*.lovable.app',
  ...String(process.env.FRAME_ANCESTORS || '').split(/\s+/).filter(value => value && value !== "'self'")
])).join(' ');

const io = new Server(server, {
  cors: {
    origin: (origin, callback) => callback(null, !origin || isAllowedOrigin(origin)),
    methods: ['GET', 'POST']
  },
  allowRequest: (req, callback) => {
    const origin = req.headers.origin;
    callback(null, !origin || isAllowedOrigin(origin));
  },
  maxHttpBufferSize: 1e5   // 100 KB max par message socket (anti-flood mémoire)
});

app.disable('x-powered-by');
app.use(express.json({ limit: '64kb' }));   // limite la taille des corps de requête
app.use((req, res, next) => {
  const requestOrigin = req.headers.origin;
  if (requestOrigin && isAllowedOrigin(requestOrigin)) {
    // On reflète l'origine appelante : l'appli MindSpille peut tourner sur
    // lovable.app, un aperçu ou une app installée (origine variable). La
    // sécurité réelle vient de la validation du jeton Supabase et des Bearer
    // JWT côté serveur — aucun cookie n'est utilisé, donc refléter l'origine
    // est sans danger (impossible de détourner une session cross-origine).
    res.setHeader('Access-Control-Allow-Origin', requestOrigin);
    res.setHeader('Vary', 'Origin');
  } else if (ALLOWED_ORIGINS === '*') {
    res.setHeader('Access-Control-Allow-Origin', '*');
  }
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type, Authorization');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('Content-Security-Policy', 'frame-ancestors ' + FRAME_ANCESTORS);
  // On garde frame-ancestors permissif pour l'iframe Lovable, mais on ajoute les autres protections.
  // Pas de restriction d'affichage en iframe : l'appli MindSpille est aussi
  // une app native (WebView) dont l'origine (capacitor://…, https://localhost…)
  // n'est pas https://*.lovable.app et serait bloquée par frame-ancestors,
  // laissant l'iframe du jeu blanche. Le jeu n'expose aucune donnée sensible
  // (le jeton est propre au joueur), donc autoriser l'embed partout est sûr.
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
const echecsRooms   = new Map();
const ludoRooms      = new Map();

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
  // A database match has exactly one authoritative socket room. Allowing a
  // client to choose another room id for the same games.id could create two
  // independent boards racing to settle one escrow.
  if (!room || room.id !== gameId) return false;
  if (room.databaseGameId && room.databaseGameId !== gameId) return false;
  room.databaseGameId = gameId;
  return true;
}

const DB_GAME_TYPES = { dames: 'checkers', tictactoe: 'tictactoe', quoridor: 'quoridor', penalty: 'penalty_shootout', chifoumi: 'rock_paper_scissors', echecs: 'chess', ludo: 'ludo' };
const ROOM_MAPS = { dames: damesRooms, tictactoe: tttRooms, quoridor: quoriRooms, penalty: penaltyRooms, chifoumi: chifoumiRooms, echecs: echecsRooms, ludo: ludoRooms };
// Room snapshots are persisted after actual state changes. The periodic loop is
// only a crash-safety fallback and the fingerprint below makes unchanged rooms
// a no-op. Persisting every room every three seconds generated unnecessary WAL
// and could let two concurrent HTTP requests save snapshots out of order.
const ROOM_PERSIST_INTERVAL = Math.max(5000, Number(process.env.ROOM_PERSIST_INTERVAL_MS) || 15000);
const ROOM_PERSIST_DEBOUNCE_MS = Math.max(100, Number(process.env.ROOM_PERSIST_DEBOUNCE_MS) || 500);
const ROOM_RETENTION_MS = 10 * 60 * 1000;
const SETTLEMENT_RETRY_MAX_DELAY_MS = 60 * 1000;
let roomPersistenceInFlight = false;

function serverSupabaseHeaders() {
  return {
    apikey: SUPABASE_SERVICE_ROLE_KEY,
    Authorization: 'Bearer ' + SUPABASE_SERVICE_ROLE_KEY,
    'Content-Type': 'application/json'
  };
}

async function callServerStateRpc(name, payload) {
  if (!SUPABASE_URL || !SUPABASE_SERVICE_ROLE_KEY) return null;
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 5000);
  try {
    const response = await fetch(SUPABASE_URL + '/rest/v1/rpc/' + name, {
      method: 'POST', headers: serverSupabaseHeaders(), body: JSON.stringify(payload || {}), signal: controller.signal
    });
    if (!response.ok) throw new Error(name + ' failed: ' + response.status + ' ' + (await response.text()).slice(0, 300));
    const text = await response.text();
    return text ? JSON.parse(text) : null;
  } finally {
    clearTimeout(timeout);
  }
}

function serializableRoomState(room) {
  const ignored = new Set([
    'turnTimer', 'graceTimer', 'revealTimer', 'nextRoundTimer', 'disconnectTimer',
    'settlementPromise', 'settlementRetryTimer', 'persistTimer', 'cleanupTimer',
    '_persistPromise', '_batchPersistPromise', '_lastPersistedFingerprint'
  ]);
  const state = JSON.parse(JSON.stringify(room, (key, value) => {
    if (ignored.has(key)) return undefined;
    if (value instanceof Set) return [...value];
    return value;
  }));
  state.players = {};
  for (const slot of [1, 2]) {
    const player = room.players?.[slot];
    if (!player) continue;
    state.players[slot] = {
      slot,
      supabaseId: player.supabaseId,
      name: safeName(player.name),
      connected: false,
      socketId: null,
      userId: null
    };
  }
  return state;
}

function persistedRoomPayload(gameName, room) {
  if (!room || !validRoom(room.id) || !isUuid(room.databaseGameId)) return null;
  if (!['waiting', 'playing', 'paused', 'finished'].includes(room.status)) return null;
  return {
    game_type: gameName,
    room_id: room.id,
    game_id: room.databaseGameId,
    status: room.status,
    state: serializableRoomState(room)
  };
}

async function persistRoomState(gameName, room) {
  if (!room) return false;

  // Serialize writes per room. Besides reducing calls, this prevents a slower
  // old request from overwriting a newer board snapshot in Supabase.
  const blockers = [room._persistPromise, room._batchPersistPromise].filter(Boolean);
  const previous = blockers.length ? Promise.allSettled(blockers) : Promise.resolve();
  let operation;
  operation = previous.catch(() => undefined).then(async () => {
    const payload = persistedRoomPayload(gameName, room);
    if (!payload) return false;
    const fingerprint = JSON.stringify(payload);
    if (room._lastPersistedFingerprint === fingerprint) return false;
    await callServerStateRpc('save_game_server_room_states', { p_rooms: [payload] });
    room._lastPersistedFingerprint = fingerprint;
    return true;
  }).finally(() => {
    if (room._persistPromise === operation) room._persistPromise = null;
  });
  room._persistPromise = operation;
  return operation;
}

function persistRoomSoon(gameName, room) {
  if (!room || room.persistTimer) return;
  room.persistTimer = setTimeout(() => {
    room.persistTimer = null;
    void persistRoomState(gameName, room).catch(error => {
      console.error('[persistence] debounced save failed', gameName, room?.id, error.message);
    });
  }, ROOM_PERSIST_DEBOUNCE_MS);
  if (room.persistTimer.unref) room.persistTimer.unref();
}

async function persistAllRoomStates() {
  if (roomPersistenceInFlight || !SUPABASE_URL || !SUPABASE_SERVICE_ROLE_KEY) return;
  roomPersistenceInFlight = true;
  const candidates = [];
  for (const [gameName, roomMap] of Object.entries(ROOM_MAPS)) {
    for (const room of roomMap.values()) {
      if (room.status !== 'finished' || room.pendingSettlement) {
        candidates.push({ gameName, room });
      }
    }
  }
  if (!candidates.length) {
    roomPersistenceInFlight = false;
    return;
  }
  const previousWrites = candidates.map(({ room }) => room._persistPromise).filter(Boolean);
  let releaseBatchGate;
  const batchGate = new Promise(resolve => { releaseBatchGate = resolve; });
  for (const { room } of candidates) room._batchPersistPromise = batchGate;
  try {
    // Let any earlier per-room state transition finish first, then take one
    // consistent batch snapshot. `save_game_server_room_states` performs a SQL
    // no-op for identical JSON but still refreshes server_live_at every 15 s.
    // That liveness pulse is required for tournament/live spectator listings.
    await Promise.allSettled(previousWrites);
    const snapshots = candidates.map(({ gameName, room }) => {
      const payload = persistedRoomPayload(gameName, room);
      return payload ? { room, payload, fingerprint: JSON.stringify(payload) } : null;
    }).filter(Boolean);
    if (!snapshots.length) return;

    await callServerStateRpc('save_game_server_room_states', {
      p_rooms: snapshots.map(snapshot => snapshot.payload)
    });
    for (const snapshot of snapshots) snapshot.room._lastPersistedFingerprint = snapshot.fingerprint;
  } catch (error) {
    console.error('[persistence] periodic save failed', error.message);
  } finally {
    releaseBatchGate();
    for (const { room } of candidates) {
      if (room._batchPersistPromise === batchGate) room._batchPersistPromise = null;
    }
    roomPersistenceInFlight = false;
  }
}

async function deletePersistedRoom(gameName, roomId) {
  try {
    await callServerStateRpc('delete_game_server_room_state', { p_game_type: gameName, p_room_id: roomId });
  } catch (error) {
    console.error('[persistence] delete failed', roomId, error.message);
  }
}

function scheduleRoomCleanup(gameName, roomId, room) {
  const roomMap = ROOM_MAPS[gameName];
  if (!roomMap || room.cleanupTimer) return;
  room.cleanupTimer = setTimeout(() => {
    if (roomMap.get(roomId) === room && room.status === 'finished') roomMap.delete(roomId);
  }, ROOM_RETENTION_MS);
  if (room.cleanupTimer.unref) room.cleanupTimer.unref();
}

function hydratePersistedRoom(record) {
  if (!record || !DB_GAME_TYPES[record.game_type] || !validRoom(record.room_id) || !isUuid(record.game_id)) return null;
  const room = record.state && typeof record.state === 'object' ? record.state : null;
  if (!room) return null;
  room.id = record.room_id;
  room.databaseGameId = record.game_id;
  room.players = room.players || {};
  for (const slot of [1, 2]) {
    const player = room.players[slot];
    if (!player) continue;
    player.slot = slot;
    player.connected = false;
    player.socketId = null;
    player.userId = null;
  }
  room.turnTimer = null; room.graceTimer = null; room.revealTimer = null; room.nextRoundTimer = null; room.disconnectTimer = null;
  if (record.game_type === 'chifoumi') room.revealPending = false;
  if (record.game_type === 'quoridor') {
    room.gameState = room.gameState && typeof room.gameState === 'object' ? room.gameState : quoriInitialState();
    room.stateVersion = Math.max(0, Number(room.stateVersion ?? room.gameState.stateVersion) || 0);
    room.gameState.currentSlot = validPlayerSlot(room.currentSlot) ? room.currentSlot : (validPlayerSlot(room.gameState.currentSlot) ? room.gameState.currentSlot : 1);
    room.currentSlot = room.gameState.currentSlot;
  }
  if (record.game_type === 'tictactoe') {
    room.totalManches = TTT_TOTAL_ROUNDS;
    room.gameState = room.gameState && typeof room.gameState === 'object' ? room.gameState : tttState();
    room.gameState.revision = Math.max(0, Number(room.gameState.revision) || 0);
    // A round result is persisted before the animation delay. If Render restarts
    // during that delay, resume from the next clean round instead of leaving the
    // room permanently locked in resolvingRound=true.
    if (room.gameState.resolvingRound) {
      const lastResult = room.gameState.mancheResults?.[room.gameState.mancheResults.length - 1];
      const recoveredWinner = room.gameState.isTiebreaker
        ? (lastResult === 'w' ? 1 : (lastResult === 'r' ? 2 : 0))
        : tttMatchWinner(room.gameState, room.totalManches);
      if (recoveredWinner) room.recoveredTTTWinnerSlot = recoveredWinner;
      else {
        room.gameState.board = Array(9).fill(null);
        room.gameState.resolvingRound = false;
        room.gameState.currentPlayer = Number(room.gameState.mancheStarterPlayer) === 1 ? 1 : 0;
        room.gameState.revision++;
      }
    }
  }
  room.settlementPromise = null; room.settlementRetryTimer = null; room.cleanupTimer = null; room.reconnectDeadline = null;
  room._persistPromise = null; room._batchPersistPromise = null; room._lastPersistedFingerprint = null;
  room.mutualQuitRequests = new Set(Array.isArray(room.mutualQuitRequests) ? room.mutualQuitRequests : []);
  if (room.status !== 'finished') {
    const playerCount = [room.players[1], room.players[2]].filter(Boolean).length;
    room.status = record.db_status === 'in_progress' || playerCount === 2 ? 'paused' : 'waiting';
  }
  return room;
}

async function restorePersistedRooms() {
  if (!SUPABASE_URL || !SUPABASE_SERVICE_ROLE_KEY) return;
  try {
    const records = await callServerStateRpc('load_game_server_room_states', {});
    if (!Array.isArray(records)) return;
    let restored = 0;
    for (const record of records) {
      const room = hydratePersistedRoom(record);
      const roomMap = ROOM_MAPS[record?.game_type];
      if (!room || !roomMap) continue;
      roomMap.set(room.id, room);
      restored++;
      if (record.game_type === 'tictactoe' && room.recoveredTTTWinnerSlot) {
        const winnerSlot = room.recoveredTTTWinnerSlot;
        delete room.recoveredTTTWinnerSlot;
        room.status = 'playing';
        notifyTTTRoomOver(room, room.id, winnerSlot, 'normal');
      } else if (room.status === 'finished' && room.pendingSettlement) {
        const pending = room.pendingSettlement;
        void settleRoomInSupabase(room, record.game_type, pending.winnerSlot, pending.reason);
      } else if (room.status === 'paused') {
        // A Render restart disconnects both sockets. Keep the exact board, but
        // apply the same 60-second reconnect rule as a normal disconnection.
        room.reconnectDeadline = Date.now() + 60000;
        room.disconnectTimer = setTimeout(() => {
          room.disconnectTimer = null;
          if (room.status !== 'finished' && !room.players[1]?.connected && !room.players[2]?.connected) {
            finishBothDisconnected(room, record.game_type, room.id);
          }
        }, 60000);
        if (room.disconnectTimer.unref) room.disconnectTimer.unref();
      }
    }
    if (restored) console.info('[persistence] restored rooms', restored);
  } catch (error) {
    console.error('[persistence] restore failed', error.message);
  }
}

const _roomPersistenceLoop = setInterval(() => { void persistAllRoomStates(); }, ROOM_PERSIST_INTERVAL);
if (_roomPersistenceLoop.unref) _roomPersistenceLoop.unref();

function databaseResult(winnerSlot, reason) {
  if (winnerSlot === 0) return reason === 'both_disconnected' || reason === 'mutual_quit' ? 'mutual_quit' : 'draw';
  return reason === 'timeout' ? 'timeout' : 'win';
}

function scheduleSettlementRetry(room, game) {
  if (!room?.pendingSettlement || room.settlementRetryTimer) return;
  const attempt = Math.max(0, Number(room.settlementRetryCount || 0));
  const delay = Math.min(SETTLEMENT_RETRY_MAX_DELAY_MS, 2000 * (2 ** Math.min(attempt, 5)));
  room.settlementRetryCount = attempt + 1;
  room.settlementRetryTimer = setTimeout(() => {
    room.settlementRetryTimer = null;
    const pending = room.pendingSettlement;
    if (pending) void settleRoomInSupabase(room, game, pending.winnerSlot, pending.reason);
  }, delay);
  if (room.settlementRetryTimer.unref) room.settlementRetryTimer.unref();
  console.warn('[settlement] retry scheduled', room.databaseGameId, 'attempt', attempt + 1, 'in', delay, 'ms');
}

async function settleRoomInSupabase(room, game, winnerSlot, reason) {
  if (room.settlementPromise) return room.settlementPromise;
  room.pendingSettlement = { winnerSlot, reason };
  if (!room.databaseGameId) {
    console.error('[settlement] Missing games.id for room', room.id);
    return null;
  }
  if (!SUPABASE_URL || !SUPABASE_SERVICE_ROLE_KEY) {
    console.error('[settlement] SUPABASE_SERVICE_ROLE_KEY is not configured; refusing browser settlement.');
    return null;
  }
  room.settlementPromise = (async () => {
    // A Render restart can restore a paid database game whose second iframe
    // never finished joining the in-memory room. Recover that immutable player
    // identity from the database game before settling; never invent it from a
    // browser payload.
    if (!room.players?.[1]?.supabaseId || !room.players?.[2]?.supabaseId) {
      await hydrateRoomParticipantsFromDatabase({ gameName: game, roomId: room.id, room });
    }
    const p1 = room.players?.[1]?.supabaseId, p2 = room.players?.[2]?.supabaseId;
    if (!isUuid(p1) || !isUuid(p2)) throw new Error('Invalid room participants');

    // Store the terminal outcome before touching wallets. If Render restarts
    // during settlement, startup can safely retry the same idempotent result.
    await persistRoomState(game, room);
    const headers = serverSupabaseHeaders();
    const gameId = encodeURIComponent(room.databaseGameId);
    const lookup = await fetch(SUPABASE_URL + '/rest/v1/games?id=eq.' + gameId + '&select=id,game_type,player1_id,player2_id,bet_amount,status,result,winner_id', { headers });
    if (!lookup.ok) throw new Error('Cannot verify database game: ' + lookup.status);
    const rows = await lookup.json();
    const dbGame = Array.isArray(rows) ? rows[0] : null;
    const samePlayers = dbGame && dbGame.player1_id === p1 && dbGame.player2_id === p2;
    const expectedType = DB_GAME_TYPES[game];
    const sameBet = dbGame && Math.abs(Number(dbGame.bet_amount || 0) - Number(room.betAmount || 0)) < 0.0001;
    if (!samePlayers || dbGame.game_type !== expectedType || !sameBet) throw new Error('Database game does not match authenticated room');
    // A completed row is accepted only when it contains this exact server
    // outcome. This is the idempotent retry path when an HTTP response was lost.
    const expectedResult = databaseResult(winnerSlot, reason);
    const expectedWinner = winnerSlot ? room.players[winnerSlot].supabaseId : null;
    const alreadyCompleted = dbGame.status === 'completed';
    if (alreadyCompleted) {
      if (dbGame.result !== expectedResult || dbGame.winner_id !== expectedWinner) {
        throw new Error('Completed database game conflicts with the authoritative room outcome');
      }
    } else if (dbGame.status !== 'in_progress') {
      throw new Error('Database game was never started; settlement refused');
    }
    const startedAt = Number(room.startedAt || Date.now());
    const payload = {
      p_game_id: room.databaseGameId,
      p_status: 'completed',
      p_result: expectedResult,
      p_winner_id: expectedWinner,
      p_platform_fee: winnerSlot ? Number(room.betAmount || 0) * 0.2 : 0,
      p_duration_seconds: Math.max(0, Math.floor((Date.now() - startedAt) / 1000))
    };
    if (!alreadyCompleted) {
      const settled = await fetch(SUPABASE_URL + '/rest/v1/rpc/submit_game_result', { method: 'POST', headers, body: JSON.stringify(payload) });
      if (!settled.ok) throw new Error('Settlement RPC failed: ' + settled.status + ' ' + (await settled.text()).slice(0, 400));
    }
    room.settledAt = Date.now();
    room.pendingSettlement = null;
    room.settlementRetryCount = 0;
    if (room.settlementRetryTimer) clearTimeout(room.settlementRetryTimer);
    room.settlementRetryTimer = null;
    await deletePersistedRoom(game, room.id);
    // Once the database confirms the terminal result there is nothing left to
    // reconnect to. Keeping the room for ten minutes made /health advertise a
    // phantom live game and allowed the persistence loop to retain stale state.
    const roomMap = ROOM_MAPS[game];
    if (roomMap?.get(room.id) === room) roomMap.delete(room.id);
    // A persistence batch that started just before pendingSettlement was
    // cleared can finish after the deletion and reinsert a stale terminal
    // snapshot. Delete once more after two persistence intervals.
    const finalPersistedCleanup = setTimeout(() => {
      void deletePersistedRoom(game, room.id);
    }, ROOM_PERSIST_INTERVAL * 2);
    if (finalPersistedCleanup.unref) finalPersistedCleanup.unref();
    console.info('[settlement] completed', room.databaseGameId, game, payload.p_result);
  })().catch(error => {
    room.settlementPromise = null;
    console.error('[settlement] failed', room.databaseGameId, error.message);
    io.to(room.id).emit('game:error', { message: 'Résultat validé, mais synchronisation portefeuille en attente. Ne relancez pas la partie.' });
    persistRoomSoon(game, room);
    scheduleSettlementRetry(room, game);
  });
  return room.settlementPromise;
}
// A room slot belongs to the authenticated player only. Reconnecting with the
// same account is allowed; replacing another player is not.
function joinRoomAsAuthenticatedPlayer(socket, roomState, roomId, player, claimedSupabaseId, claimedName) {
  if (!validRoom(roomId) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
  if (!roomState || roomState.status === 'finished') return rejectSocket(socket, 'Cette partie est déjà terminée.');
  const user = authenticatedSocketUser(socket);
  if (!user || !user.supabaseId) return rejectSocket(socket, 'Authentification requise.');
  if (claimedSupabaseId && claimedSupabaseId !== user.supabaseId) return rejectSocket(socket, 'Identité de joueur invalide.');
  const other = roomState.players[player === 1 ? 2 : 1];
  if (other && other.supabaseId === user.supabaseId) return rejectSocket(socket, 'Un joueur ne peut pas occuper les deux places.');
  const existing = roomState.players[player];
  if (existing && existing.supabaseId !== user.supabaseId) return rejectSocket(socket, 'Cette place est déjà occupée.');
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

// The HTTP compatibility gate and the Socket.io join happen immediately one
// after the other and used to perform the same PostgREST query twice per
// player. Share the in-flight request and keep its immutable join fields for a
// very short period. Socket room ownership is still checked independently.
const databaseGameJoinCache = new Map();
const databaseGameJoinInFlight = new Map();
const DATABASE_GAME_JOIN_CACHE_TTL_MS = 2500;

async function loadDatabaseGameForJoin(gameId) {
  const cached = databaseGameJoinCache.get(gameId);
  if (cached && cached.expiresAt > Date.now()) return cached.game;
  if (cached) databaseGameJoinCache.delete(gameId);
  if (databaseGameJoinInFlight.has(gameId)) return databaseGameJoinInFlight.get(gameId);

  const lookup = (async () => {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 5000);
    try {
      const response = await fetch(
        SUPABASE_URL + '/rest/v1/games?id=eq.' + encodeURIComponent(gameId) + '&select=id,game_type,player1_id,player2_id,bet_amount,status,is_ai_opponent',
        { headers: serverSupabaseHeaders(), signal: controller.signal }
      );
      if (!response.ok) throw new Error('database_game_lookup_' + response.status);
      const rows = await response.json();
      const game = Array.isArray(rows) ? rows[0] || null : null;
      databaseGameJoinCache.set(gameId, {
        game,
        expiresAt: Date.now() + DATABASE_GAME_JOIN_CACHE_TTL_MS
      });
      return game;
    } finally {
      clearTimeout(timeout);
    }
  })();

  databaseGameJoinInFlight.set(gameId, lookup);
  try {
    return await lookup;
  } finally {
    databaseGameJoinInFlight.delete(gameId);
  }
}

async function verifyDatabaseGameForJoin(socket, gameId, gameName, player, bet, roomId) {
  const user = authenticatedSocketUser(socket);
  if (!user?.supabaseId) return { ok: false, message: 'Authentification requise.' };
  if (isUuid(gameId) && roomId !== gameId) {
    return { ok: false, message: 'La room ne correspond pas à cette partie.' };
  }
  if (!isUuid(gameId)) {
    if (process.env.NODE_ENV !== 'production' && !SUPABASE_SERVICE_ROLE_KEY) return { ok: true };
    return { ok: false, message: 'Identifiant de partie manquant ou invalide.' };
  }
  if (!SUPABASE_URL || !SUPABASE_SERVICE_ROLE_KEY) return { ok: false, message: 'Validation serveur temporairement indisponible.' };
  try {
    const game = await loadDatabaseGameForJoin(gameId);
    const expectedPlayer = player === 1 ? game?.player1_id : game?.player2_id;
    const sameBet = game && Math.abs(Number(game.bet_amount || 0) - Number(bet || 0)) < 0.0001;
    if (!game || game.game_type !== DB_GAME_TYPES[gameName] || expectedPlayer !== user.supabaseId || !sameBet) {
      return { ok: false, message: 'Cette partie ne correspond pas au joueur, au jeu ou à la mise.' };
    }
    if (!['waiting', 'in_progress'].includes(game.status)) return { ok: false, message: 'Cette partie est déjà terminée.' };
    return { ok: true };
  } catch {
    return { ok: false, message: 'Validation serveur temporairement indisponible.' };
  }
}

function findLiveRoomByDatabaseGameId(gameId) {
  if (!isUuid(gameId)) return null;
  for (const [gameName, rooms] of Object.entries(ROOM_MAPS)) {
    for (const [roomId, room] of rooms.entries()) {
      if (room?.databaseGameId !== gameId) continue;
      if (room.status !== 'playing') return null;
      if (!room.players?.[1]?.supabaseId || !room.players?.[2]?.supabaseId) return null;
      if (room.players[1].supabaseId === room.players[2].supabaseId) return null;
      return { gameName, roomId, room };
    }
  }
  return null;
}

function spectatorRoomSnapshot(gameName, room) {
  const common = {
    gameId: room.databaseGameId,
    gameType: DB_GAME_TYPES[gameName],
    serverGame: gameName,
    room: room.id,
    status: room.status,
    betAmount: Number(room.betAmount || 0),
    currency: room.currency || 'HTG',
    serverTime: Date.now(),
    players: {
      1: { name: safeName(room.players?.[1]?.name), connected: room.players?.[1]?.connected === true },
      2: { name: safeName(room.players?.[2]?.name), connected: room.players?.[2]?.connected === true }
    }
  };

  if (gameName === 'dames') return { ...common, state: damesSnapshot(room) };
  if (gameName === 'echecs') return { ...common, state: echecsSnapshot(room) };
  if (gameName === 'tictactoe') {
    return {
      ...common,
      state: {
        gameState: room.gameState || null,
        totalManches: room.totalManches || 5,
        turnPlayer: room.turnPlayer,
        turnStartTime: room.turnStartTime,
        graceStartTime: room.graceStartTime,
        turnDuration: TURN_DURATION,
        graceDuration: GRACE_DURATION
      }
    };
  }
  if (gameName === 'quoridor') {
    return {
      ...common,
      state: {
        gameState: room.gameState || null,
        currentSlot: room.currentSlot,
        turnPlayer: room.turnPlayer,
        turnStartTime: room.turnStartTime,
        graceStartTime: room.graceStartTime,
        turnDuration: TURN_DURATION,
        graceDuration: GRACE_DURATION
      }
    };
  }
  if (gameName === 'penalty') {
    return {
      ...common,
      state: {
        round: room.currentRound,
        scores: { p1: Number(room.scores?.p1 || 0), p2: Number(room.scores?.p2 || 0) },
        phase: 'choosing',
        turnStartTime: room.turnStartTime,
        graceStartTime: room.graceStartTime,
        turnDuration: PENALTY_TURN_DURATION,
        graceDuration: PENALTY_GRACE_DURATION
      }
    };
  }
  if (gameName === 'chifoumi') {
    return {
      ...common,
      state: {
        scores: Array.isArray(room.scores) ? [...room.scores] : [0, 0],
        currentRound: room.currentRound,
        history: Array.isArray(room.history) ? room.history.map(item => ({ ...item })) : [],
        awaitingNextRound: room.awaitingNextRound === true,
        revealPending: room.revealPending === true,
        revealStartTime: room.revealStartTime || null,
        revealDuration: CHIFOUMI_REVEAL_DURATION,
        turnStartTime: room.turnStartTime,
        graceStartTime: room.graceStartTime,
        turnDuration: CHIFOUMI_TURN_DURATION,
        graceDuration: CHIFOUMI_GRACE_DURATION
      }
    };
  }
  if (gameName === 'ludo') return { ...common, state: ludoPublicState(room) };
  return null;
}

function authoritativeRoomById(roomId) {
  for (const rooms of Object.values(ROOM_MAPS)) {
    const room = rooms.get(roomId);
    if (room) return room;
  }
  return null;
}

function spectatorCountForRoom(roomId) {
  const members = io.sockets.adapter.rooms.get(roomId);
  if (!members) return 0;
  const room = authoritativeRoomById(roomId);
  const playerSockets = new Set(
    [room?.players?.[1]?.socketId, room?.players?.[2]?.socketId].filter(Boolean)
  );
  let count = 0;
  for (const socketId of members) {
    if (!playerSockets.has(socketId)) count++;
  }
  return count;
}

function emitSpectatorCount(roomId, count = spectatorCountForRoom(roomId)) {
  io.to(roomId).emit('spectator_count', {
    room: roomId,
    count: Math.max(0, Number(count) || 0)
  });
}

// Limiteur HTTP anti brute-force / credential stuffing sur l'authentification
function authRateLimit(req, res, next) {
  const accessToken = req.body && req.body.supabaseAccessToken;
  // Mobile carriers commonly place many customers behind the same public IP.
  // Limiting every authenticated player only by IP made a second player fail
  // to open a game after a few retries (login -> register -> login can already
  // consume three requests). A valid Supabase session is rate-limited by its
  // token digest, while the IP ceiling remains as a coarse abuse guard.
  if (typeof accessToken === 'string' && accessToken.length >= 20 && accessToken.length <= 4096) {
    const tokenKey = supabaseTokenDigest(accessToken);
    if (!rateLimit('auth-token:' + tokenKey, 30, 5 * 60 * 1000) ||
        !rateLimit('auth-ip:' + clientIp(req), 180, 5 * 60 * 1000)) {
      return res.status(429).json({ error: 'Trop de tentatives. Réessayez dans quelques minutes.' });
    }
    return next();
  }
  // Legacy/local authentication has no independently verified Supabase
  // identity, so it keeps the stricter IP limit.
  if (!rateLimit('auth-legacy:' + clientIp(req), 12, 5 * 60 * 1000)) {
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

const TTT_TOTAL_ROUNDS = Math.max(1, Math.min(15, Number(process.env.TTT_TOTAL_ROUNDS) || 5));
const TTT_LINES = [[0, 1, 2], [3, 4, 5], [6, 7, 8], [0, 3, 6], [1, 4, 7], [2, 5, 8], [0, 4, 8], [2, 4, 6]];
function tttWinningLine(board, symbol) { return TTT_LINES.find(line => line.every(index => board[index] === symbol)) || null; }
function tttState() { return { board: Array(9).fill(null), currentPlayer: 0, matchW: 0, matchR: 0, manchesDone: 0, mancheResults: [], isTiebreaker: false, mancheStarterPlayer: 0, resolvingRound: false, revision: 0 }; }
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
  state.revision = Math.max(0, Number(state.revision) || 0) + 1;
  const matchWinner = state.isTiebreaker ? winnerSlot : tttMatchWinner(state, room.totalManches);
  const winner = winnerSlot || 'draw';
  io.to(roomId).emit('ttt_manche_result', { room: roomId, winner, winLine: winLine ? winLine.map(index => ({ row: Math.floor(index / 3), col: index % 3 })) : null, matchW: state.matchW, matchR: state.matchR, manchesDone: state.manchesDone, mancheResults: [...state.mancheResults], isTiebreaker: state.isTiebreaker, nextStarterPlayer: state.mancheStarterPlayer, matchWinner, revision: state.revision, totalManches: room.totalManches });
  persistRoomSoon('tictactoe', room);
  setTimeout(() => {
    if (room.status === 'finished') return;
    if (matchWinner) return notifyTTTRoomOver(room, roomId, matchWinner, 'normal');
    state.board = Array(9).fill(null);
    state.resolvingRound = false;
    state.revision++;
    persistRoomSoon('tictactoe', room);
    if (room.status !== 'playing') {
      room.pausedTurnPlayer = state.currentPlayer + 1;
      return;
    }
    io.to(roomId).emit('ttt_state_sync', tttSnapshot(room));
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
    const payload = jwt.verify(h.slice(7), JWT_SECRET);
    const userId = payload && payload.userId;
    if (!isUuid(userId)) return res.status(401).json({ error: 'Token invalide' });
    // Render can restart between /auth/login and /game/join. Restore the user
    // only from fields signed by this server, exactly as Socket.io already
    // does, so a healthy game is not rejected because an in-memory Map reset.
    if (!users.has(userId) && isUuid(payload.supabaseId)) {
      users.set(userId, {
        id: userId,
        username: safeName(payload.username, 'Joueur'),
        supabaseId: payload.supabaseId
      });
      console.info('[auth] restored signed Supabase user for HTTP request');
    }
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

// A game page used to verify the same Supabase token again on every mount.
// Cache only successful verifications, keyed by a SHA-256 digest (never by the
// raw token), for at most one minute and never beyond the JWT expiry.
const verifiedSupabaseTokens = new Map();
const supabaseVerificationInFlight = new Map();
const SUPABASE_AUTH_CACHE_TTL_MS = 60 * 1000;
const SUPABASE_AUTH_CACHE_MAX = 2000;

function supabaseTokenDigest(accessToken) {
  return crypto.createHash('sha256').update(accessToken).digest('hex');
}

function cacheVerifiedSupabaseProfile(key, accessToken, profile) {
  let expiresAt = Date.now() + SUPABASE_AUTH_CACHE_TTL_MS;
  try {
    const decoded = jwt.decode(accessToken);
    if (decoded && Number.isFinite(Number(decoded.exp))) {
      expiresAt = Math.min(expiresAt, Number(decoded.exp) * 1000 - 5000);
    }
  } catch {}
  if (expiresAt <= Date.now()) return;
  if (verifiedSupabaseTokens.size >= SUPABASE_AUTH_CACHE_MAX) {
    verifiedSupabaseTokens.delete(verifiedSupabaseTokens.keys().next().value);
  }
  verifiedSupabaseTokens.set(key, { profile, expiresAt });
}

// The browser must prove its Supabase identity. A raw UUID received from a
// client is never an authentication credential.
async function verifySupabaseAccessToken(accessToken) {
  if (!SUPABASE_URL || !SUPABASE_PUBLISHABLE_KEY || typeof accessToken !== 'string' || accessToken.length < 20 || accessToken.length > 4096) return null;
  const key = supabaseTokenDigest(accessToken);
  const cached = verifiedSupabaseTokens.get(key);
  if (cached && cached.expiresAt > Date.now()) return cached.profile;
  if (cached) verifiedSupabaseTokens.delete(key);
  if (supabaseVerificationInFlight.has(key)) return supabaseVerificationInFlight.get(key);

  const verification = (async () => {
    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), 5000);
    try {
      const response = await fetch(SUPABASE_URL + '/auth/v1/user', {
        headers: { apikey: SUPABASE_PUBLISHABLE_KEY, Authorization: 'Bearer ' + accessToken },
        signal: controller.signal
      });
      if (!response.ok) return null;
      const profile = await response.json();
      if (!profile || typeof profile.id !== 'string') return null;
      cacheVerifiedSupabaseProfile(key, accessToken, profile);
      return profile;
    } catch {
      return null;
    } finally {
      clearTimeout(timeout);
    }
  })();
  supabaseVerificationInFlight.set(key, verification);
  try {
    return await verification;
  } finally {
    supabaseVerificationInFlight.delete(key);
  }
}

function createServerToken(user) {
  const payload = {
    userId: user.id,
    username: safeName(user.username, 'Joueur')
  };
  // supabaseId is signed by this server. Including it lets a valid session
  // restore its in-memory user after a Render restart without trusting any
  // browser-provided identity.
  if (isUuid(user.supabaseId)) payload.supabaseId = user.supabaseId;
  return jwt.sign(payload, JWT_SECRET, { expiresIn: '2h' });
}

function issueServerToken(res, user) {
  const token = createServerToken(user);
  res.json({ token, userId: user.id, username: user.username });
}

function authenticateSocketToken(socket, token) {
  if (typeof token !== 'string' || token.length > 4096) return false;
  try {
    const payload = jwt.verify(token, JWT_SECRET);
    if (!payload || typeof payload !== 'object' || !isUuid(payload.userId)) return false;
    const { userId } = payload;
    let user = users.get(userId);
    if (!user && isUuid(payload.supabaseId)) {
      user = {
        id: userId,
        username: safeName(payload.username, 'Joueur'),
        supabaseId: payload.supabaseId
      };
      users.set(userId, user);
      console.info('[auth] restored signed Supabase user after restart');
    }
    if (!user) return false;
    socketUsers.set(socket.id, userId);
    socket.userId = userId;
    return true;
  } catch {
    return false;
  }
}

io.use((socket, next) => {
  const forwarded = String(socket.handshake.headers['x-forwarded-for'] || '').split(',')[0].trim();
  const ip = forwarded || socket.handshake.address || 'unknown';
  const token = socket.handshake.auth && socket.handshake.auth.token;
  if (!token) {
    if (!rateLimit('socket-anonymous:' + ip, 30, 60000)) return next(new Error('rate_limited'));
    return next();
  }
  if (!authenticateSocketToken(socket, token)) {
    if (!rateLimit('socket-invalid:' + ip, 20, 60000)) return next(new Error('rate_limited'));
    return next(new Error('unauthorized'));
  }
  // A shared carrier IP must not prevent two legitimate authenticated players
  // from joining the same room. Limit the signed server account instead.
  if (!rateLimit('socket-user:' + socket.userId, 30, 60000)) return next(new Error('rate_limited'));
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
  if (droom.status !== 'playing' || droom.currentPlayer + 1 !== playerSlot) return;
  const now = Date.now();
  droom.turnPlayer = playerSlot; droom.turnStartTime = now; droom.graceStartTime = null;
  io.to(roomId).emit('dames_turn_start', { player: playerSlot, startTime: now, duration: TURN_DURATION });
  droom.turnTimer = setTimeout(() => {
    droom.turnTimer = null;
    if (droom.status !== 'playing' || droom.currentPlayer + 1 !== playerSlot || droom.turnPlayer !== playerSlot) return;
    const graceNow = Date.now();
    droom.graceStartTime = graceNow;
    io.to(roomId).emit('dames_turn_warning', { player: playerSlot, startTime: graceNow, duration: GRACE_DURATION });
    droom.graceTimer = setTimeout(() => {
      droom.graceTimer = null;
      if (droom.status !== 'playing' || droom.currentPlayer + 1 !== playerSlot || droom.turnPlayer !== playerSlot) return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      notifyDamesRoomOver(droom, roomId, winnerSlot, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// ── RE-SYNCHRO AUTORITATIVE DAMES ──────────────────────────
// Le serveur est la seule source de vérité du plateau. Un événement socket
// peut se perdre (réseau mobile, socket à moitié morte) : sans rattrapage, le
// plateau du joueur reste figé et la partie meurt en timeout/abandon. Ce bloc
// renvoie donc l'état exact à intervalle régulier et sur demande, pour qu'un
// coup perdu se corrige tout seul au lieu de geler la partie.
const DAMES_SYNC_INTERVAL = 5000;

function damesSnapshot(droom) {
  const snap = {
    room: droom.id,
    version: droom.stateVersion || 0,
    boardState: droom.boardState,
    currentPlayer: droom.currentPlayer,
    lastMove: droom.lastMove || null,
    status: droom.status,
    serverTime: Date.now()
  };
  if (droom.turnPlayer !== null && droom.status === 'playing') {
    snap.turnPlayer = droom.turnPlayer;
    if (droom.graceStartTime) { snap.graceStartTime = droom.graceStartTime; snap.graceDuration = GRACE_DURATION; }
    else if (droom.turnStartTime) { snap.turnStartTime = droom.turnStartTime; snap.turnDuration = TURN_DURATION; }
  }
  return snap;
}

const _damesSyncLoop = setInterval(() => {
  for (const [roomId, droom] of damesRooms) {
    if (droom.status !== 'playing') continue;
    io.to(roomId).emit('dames_state_sync', damesSnapshot(droom));
  }
}, DAMES_SYNC_INTERVAL);
if (_damesSyncLoop.unref) _damesSyncLoop.unref();

// ── ÉCHECS : timers de tour + re-synchro autoritative (même modèle que Dames) ──
function clearEchecsTurnTimers(eroom) {
  if (eroom.turnTimer)  { clearTimeout(eroom.turnTimer);  eroom.turnTimer  = null; }
  if (eroom.graceTimer) { clearTimeout(eroom.graceTimer); eroom.graceTimer = null; }
  eroom.turnStartTime = null; eroom.graceStartTime = null; eroom.turnPlayer = null;
}

function startEchecsTurnTimer(eroom, roomId, playerSlot) {
  clearEchecsTurnTimers(eroom);
  if (eroom.status !== 'playing' || eroom.currentPlayer + 1 !== playerSlot) return;
  const now = Date.now();
  eroom.turnPlayer = playerSlot; eroom.turnStartTime = now; eroom.graceStartTime = null;
  io.to(roomId).emit('echecs_turn_start', { player: playerSlot, startTime: now, duration: TURN_DURATION });
  eroom.turnTimer = setTimeout(() => {
    eroom.turnTimer = null;
    if (eroom.status !== 'playing' || eroom.currentPlayer + 1 !== playerSlot || eroom.turnPlayer !== playerSlot) return;
    const graceNow = Date.now();
    eroom.graceStartTime = graceNow;
    io.to(roomId).emit('echecs_turn_warning', { player: playerSlot, startTime: graceNow, duration: GRACE_DURATION });
    eroom.graceTimer = setTimeout(() => {
      eroom.graceTimer = null;
      if (eroom.status !== 'playing' || eroom.currentPlayer + 1 !== playerSlot || eroom.turnPlayer !== playerSlot) return;
      const winnerSlot = playerSlot === 1 ? 2 : 1;
      notifyEchecsRoomOver(eroom, roomId, winnerSlot, 'timeout');
    }, GRACE_DURATION);
  }, TURN_DURATION);
}

// L'état vient de la persistance ou du réseau : on le revalide toujours avant usage.
function ensureEchecsEngineState(eroom) {
  const cleaned = ChessEngine.sanitizeState(eroom.engineState);
  eroom.engineState = cleaned || ChessEngine.initialState();
  return eroom.engineState;
}

function echecsSnapshot(eroom) {
  const snap = {
    room: eroom.id,
    version: eroom.stateVersion || 0,
    gameState: JSON.stringify(ChessEngine.exportState(ensureEchecsEngineState(eroom))),
    currentPlayer: eroom.currentPlayer,
    lastMove: eroom.lastMove || null,
    status: eroom.status,
    serverTime: Date.now()
  };
  if (eroom.turnPlayer !== null && eroom.status === 'playing') {
    snap.turnPlayer = eroom.turnPlayer;
    if (eroom.graceStartTime) { snap.graceStartTime = eroom.graceStartTime; snap.graceDuration = GRACE_DURATION; }
    else if (eroom.turnStartTime) { snap.turnStartTime = eroom.turnStartTime; snap.turnDuration = TURN_DURATION; }
  }
  return snap;
}

const _echecsSyncLoop = setInterval(() => {
  for (const [roomId, eroom] of echecsRooms) {
    if (eroom.status !== 'playing') continue;
    io.to(roomId).emit('echecs_state_sync', echecsSnapshot(eroom));
  }
}, DAMES_SYNC_INTERVAL);
if (_echecsSyncLoop.unref) _echecsSyncLoop.unref();

function clearTTTTurnTimers(troom) {
  if (troom.turnTimer)  { clearTimeout(troom.turnTimer);  troom.turnTimer  = null; }
  if (troom.graceTimer) { clearTimeout(troom.graceTimer); troom.graceTimer = null; }
  troom.turnStartTime = null; troom.graceStartTime = null; troom.turnPlayer = null;
}

function tttSnapshot(troom) {
  const state = troom.gameState || tttState();
  const snap = {
    room: troom.id,
    revision: Math.max(0, Number(state.revision) || 0),
    gameState: {
      board: Array.isArray(state.board) ? [...state.board] : Array(9).fill(null),
      currentPlayer: Number(state.currentPlayer) === 1 ? 1 : 0,
      matchW: Number(state.matchW) || 0,
      matchR: Number(state.matchR) || 0,
      manchesDone: Number(state.manchesDone) || 0,
      mancheResults: Array.isArray(state.mancheResults) ? [...state.mancheResults] : [],
      isTiebreaker: state.isTiebreaker === true,
      mancheStarterPlayer: Number(state.mancheStarterPlayer) === 1 ? 1 : 0,
      resolvingRound: state.resolvingRound === true,
      revision: Math.max(0, Number(state.revision) || 0)
    },
    totalManches: troom.totalManches || TTT_TOTAL_ROUNDS,
    status: troom.status,
    serverTime: Date.now(),
    turnPlayer: troom.turnPlayer
  };
  if (troom.status === 'playing' && troom.turnPlayer !== null) {
    if (troom.graceStartTime) { snap.graceStartTime = troom.graceStartTime; snap.graceDuration = GRACE_DURATION; }
    else if (troom.turnStartTime) { snap.turnStartTime = troom.turnStartTime; snap.turnDuration = TURN_DURATION; }
  }
  return snap;
}

const _tttSyncLoop = setInterval(() => {
  for (const [roomId, troom] of tttRooms) {
    if (troom.status !== 'playing') continue;
    io.to(roomId).emit('ttt_state_sync', tttSnapshot(troom));
  }
}, DAMES_SYNC_INTERVAL);
if (_tttSyncLoop.unref) _tttSyncLoop.unref();

function startTTTTurnTimer(troom, roomId, playerSlot) {
  clearTTTTurnTimers(troom);
  const state = troom.gameState;
  if (troom.status !== 'playing' || !state || state.resolvingRound || state.currentPlayer + 1 !== playerSlot) return;
  const now = Date.now();
  troom.turnPlayer = playerSlot; troom.turnStartTime = now; troom.graceStartTime = null;
  io.to(roomId).emit('ttt_turn_start', { player: playerSlot, startTime: now, duration: TURN_DURATION });
  troom.turnTimer = setTimeout(() => {
    troom.turnTimer = null;
    if (troom.status !== 'playing' || state.resolvingRound || state.currentPlayer + 1 !== playerSlot) return;
    const graceNow = Date.now();
    troom.graceStartTime = graceNow;
    io.to(roomId).emit('ttt_turn_warning', { player: playerSlot, startTime: graceNow, duration: GRACE_DURATION });
    troom.graceTimer = setTimeout(() => {
      troom.graceTimer = null;
      if (troom.status !== 'playing' || state.resolvingRound || state.currentPlayer + 1 !== playerSlot) return;
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

function quoriSnapshot(qroom) {
  const state = qroom.gameState || quoriInitialState();
  const gameState = {
    s1Pos: { r: Number(state.s1Pos?.r), c: Number(state.s1Pos?.c) },
    s2Pos: { r: Number(state.s2Pos?.r), c: Number(state.s2Pos?.c) },
    s1Walls: Number(state.s1Walls),
    s2Walls: Number(state.s2Walls),
    hW: Array.isArray(state.hW) ? state.hW.map(row => Array.isArray(row) ? [...row] : []) : [],
    vW: Array.isArray(state.vW) ? state.vW.map(row => Array.isArray(row) ? [...row] : []) : [],
    currentSlot: validPlayerSlot(qroom.currentSlot) ? qroom.currentSlot : 1
  };
  const snap = {
    room: qroom.id,
    version: Math.max(0, Number(qroom.stateVersion) || 0),
    gameState,
    currentSlot: gameState.currentSlot,
    status: qroom.status,
    serverTime: Date.now(),
    turnPlayer: qroom.turnPlayer
  };
  if (qroom.status === 'playing' && qroom.turnPlayer !== null) {
    if (qroom.graceStartTime) { snap.graceStartTime = qroom.graceStartTime; snap.graceDuration = GRACE_DURATION; }
    else if (qroom.turnStartTime) { snap.turnStartTime = qroom.turnStartTime; snap.turnDuration = TURN_DURATION; }
  }
  return snap;
}

const _quoriSyncLoop = setInterval(() => {
  for (const [roomId, qroom] of quoriRooms) {
    if (qroom.status !== 'playing') continue;
    io.to(roomId).emit('quoridor_state_sync', quoriSnapshot(qroom));
  }
}, DAMES_SYNC_INTERVAL);
if (_quoriSyncLoop.unref) _quoriSyncLoop.unref();

function startQuoriTurnTimer(qroom, roomId, playerSlot) {
  clearQuoriTurnTimers(qroom);
  if (qroom.status !== 'playing' || qroom.currentSlot !== playerSlot) return;
  const now = Date.now();
  qroom.turnPlayer = playerSlot; qroom.turnStartTime = now; qroom.graceStartTime = null;
  io.to(roomId).emit('quoridor_turn_start', { player: playerSlot, startTime: now, duration: TURN_DURATION });
  qroom.turnTimer = setTimeout(() => {
    qroom.turnTimer = null;
    if (qroom.status !== 'playing' || qroom.currentSlot !== playerSlot || qroom.turnPlayer !== playerSlot) return;
    const graceNow = Date.now();
    qroom.graceStartTime = graceNow;
    io.to(roomId).emit('quoridor_turn_warning', { player: playerSlot, startTime: graceNow, duration: GRACE_DURATION });
    qroom.graceTimer = setTimeout(() => {
      qroom.graceTimer = null;
      if (qroom.status !== 'playing' || qroom.currentSlot !== playerSlot || qroom.turnPlayer !== playerSlot) return;
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
  if (proom.status !== 'playing') return;
  const round = proom.currentRound;
  const now = Date.now();
  proom.turnStartTime = now; proom.graceStartTime = null;
  io.to(roomId).emit('penalty_turn_start', { startTime: now, duration: PENALTY_TURN_DURATION });

  proom.turnTimer = setTimeout(() => {
    proom.turnTimer = null;
    if (proom.status !== 'playing' || proom.currentRound !== round) return;

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
      if (proom.status !== 'playing' || proom.currentRound !== round) return;

      const hp1Grace = proom.choices[1] !== undefined;
      const hp2Grace = proom.choices[2] !== undefined;

      if (!hp1Grace && !hp2Grace) {
        finishBothDisconnected(proom, 'penalty', roomId);
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

  persistRoomSoon('penalty', proom);
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
const CHIFOUMI_REVEAL_DURATION = 5 * 1000;

function clearChifoumiTurnTimers(croom) {
  if (croom.turnTimer)  { clearTimeout(croom.turnTimer);  croom.turnTimer  = null; }
  if (croom.graceTimer) { clearTimeout(croom.graceTimer); croom.graceTimer = null; }
  if (croom.revealTimer) { clearTimeout(croom.revealTimer); croom.revealTimer = null; }
  if (croom.nextRoundTimer) { clearTimeout(croom.nextRoundTimer); croom.nextRoundTimer = null; }
  croom.revealPending = false;
  croom.revealStartTime = null; croom.turnStartTime = null; croom.graceStartTime = null;
}

function startChifoumiTurnTimer(croom, roomId) {
  if (croom.status !== 'playing' || croom.revealPending || croom.awaitingNextRound) return;
  clearChifoumiTurnTimers(croom);
  const round = croom.currentRound;
  const now = Date.now();
  croom.turnStartTime = now; croom.graceStartTime = null;

  io.to(roomId).emit('chifoumi_turn_start', { startTime: now, duration: CHIFOUMI_TURN_DURATION });

  croom.turnTimer = setTimeout(() => {
    croom.turnTimer = null;
    if (croom.status !== 'playing' || croom.currentRound !== round || croom.revealPending || croom.awaitingNextRound) return;

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
      if (croom.status !== 'playing' || croom.currentRound !== round || croom.revealPending || croom.awaitingNextRound) return;
      
      const hp1Grace = croom.choices[1] !== undefined;
      const hp2Grace = croom.choices[2] !== undefined;

      if (!hp1Grace && !hp2Grace) {
        finishBothDisconnected(croom, 'chifoumi', roomId);
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

function advanceChifoumiRound(croom, roomId, expectedRound) {
  if (!croom || croom.status !== 'playing' || croom.awaitingNextRound !== true) return false;
  const nextRound = croom.currentRound + 1;
  if (Number.isInteger(expectedRound) && expectedRound !== nextRound) return false;
  if (croom.history.length !== croom.currentRound || nextRound > 5) return false;
  clearChifoumiTurnTimers(croom);
  croom.currentRound = nextRound;
  croom.choices = {};
  croom.awaitingNextRound = false;
  persistRoomSoon('chifoumi', croom);
  io.to(roomId).emit('chifoumi_round_ready', { round: nextRound, scores: [...croom.scores] });
  startChifoumiTurnTimer(croom, roomId);
  return true;
}

function scheduleNextChifoumiRound(croom, roomId) {
  if (!croom || croom.status !== 'playing' || croom.awaitingNextRound !== true || croom.nextRoundTimer) return;
  croom.nextRoundTimer = setTimeout(() => {
    croom.nextRoundTimer = null;
    advanceChifoumiRound(croom, roomId);
  }, 4500);
  if (croom.nextRoundTimer.unref) croom.nextRoundTimer.unref();
}

function resolveChifoumiRound(croom, roomId) {
  if (croom.status !== 'playing' || croom.choices[1] === undefined || croom.choices[2] === undefined) return;
  clearChifoumiTurnTimers(croom);
  const choice1 = croom.choices[1], choice2 = croom.choices[2];
  const winnerSlot = chifoumiWinnerSlot(choice1, choice2);
  if (winnerSlot === 1) croom.scores[0]++;
  if (winnerSlot === 2) croom.scores[1]++;
  croom.history.push({ round: croom.currentRound, choice1, choice2, winnerSlot });
  persistRoomSoon('chifoumi', croom);

  // Public only after both hidden choices have been locked and resolved.
  // Spectators never receive the private choice events sent to each player.
  io.to(roomId).emit('chifoumi_round_result', {
    round: croom.currentRound,
    choice1,
    choice2,
    winnerSlot,
    scores: [...croom.scores],
    nextRound: croom.currentRound + 1
  });

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
  persistRoomSoon('chifoumi', croom);
  // A backgrounded browser can miss its legacy round_start callback. The
  // authoritative server advances the round after a short compatibility delay.
  scheduleNextChifoumiRound(croom, roomId);
}

function scheduleChifoumiReveal(croom, roomId) {
  if (croom.status !== 'playing' || croom.revealPending) return;
  if (croom.choices[1] === undefined || croom.choices[2] === undefined) return;
  if (croom.turnTimer) { clearTimeout(croom.turnTimer); croom.turnTimer = null; }
  if (croom.graceTimer) { clearTimeout(croom.graceTimer); croom.graceTimer = null; }
  croom.turnStartTime = null;
  croom.graceStartTime = null;
  croom.revealPending = true;
  const startTime = Date.now();
  croom.revealStartTime = startTime;
  persistRoomSoon('chifoumi', croom);
  io.to(roomId).emit('chifoumi_reveal_countdown', {
    serverTime: startTime,
    startTime,
    duration: CHIFOUMI_REVEAL_DURATION
  });
  croom.revealTimer = setTimeout(() => {
    croom.revealTimer = null;
    croom.revealPending = false;
    croom.revealStartTime = null;
    resolveChifoumiRound(croom, roomId);
  }, CHIFOUMI_REVEAL_DURATION);
  if (croom.revealTimer.unref) croom.revealTimer.unref();
}

// Ludo 2 joueurs : le dé, les coups légaux et la victoire sont décidés
// uniquement par le serveur. Le navigateur ne peut jamais choisir un résultat.
const LUDO_TURN_DURATION = 30 * 1000;
const LUDO_GRACE_DURATION = 60 * 1000;
const LUDO_FINISH = 57;
// Absolute cells match the 15x15 board artwork: slot 1 uses the yellow
// start (cell 39), while slot 2 uses the blue start (cell 26).
const LUDO_START_OFFSET = { 1: 39, 2: 26 };
const LUDO_SAFE_CELLS = new Set([0, 8, 13, 21, 26, 34, 39, 47]);

function createLudoState() {
  return {
    tokens: { 1: [-1, -1, -1, -1], 2: [-1, -1, -1, -1] },
    currentPlayer: 1,
    dice: null,
    phase: 'roll',
    legalMoves: [],
    consecutiveSixes: { 1: 0, 2: 0 },
    revision: 0
  };
}

function ensureLudoState(room) {
  if (!room.gameState || !room.gameState.tokens) room.gameState = createLudoState();
  for (const slot of [1, 2]) {
    if (!Array.isArray(room.gameState.tokens[slot]) || room.gameState.tokens[slot].length !== 4) {
      room.gameState.tokens[slot] = [-1, -1, -1, -1];
    }
  }
  room.gameState.consecutiveSixes = room.gameState.consecutiveSixes || { 1: 0, 2: 0 };
  room.gameState.legalMoves = Array.isArray(room.gameState.legalMoves) ? room.gameState.legalMoves : [];
  return room.gameState;
}

function ludoAbsoluteCell(slot, progress) {
  return progress >= 0 && progress <= 51 ? (LUDO_START_OFFSET[slot] + progress) % 52 : null;
}

function ludoOpponentBlockade(room, slot, targetProgress) {
  const target = ludoAbsoluteCell(slot, targetProgress);
  if (target === null || LUDO_SAFE_CELLS.has(target)) return false;
  const other = slot === 1 ? 2 : 1;
  return ensureLudoState(room).tokens[other]
    .filter(progress => ludoAbsoluteCell(other, progress) === target).length >= 2;
}

function legalLudoMoves(room, slot, dice) {
  if (!validPlayerSlot(slot) || !Number.isInteger(dice) || dice < 1 || dice > 6) return [];
  const tokens = ensureLudoState(room).tokens[slot];
  const legal = [];
  for (let index = 0; index < tokens.length; index++) {
    const progress = tokens[index];
    let target = null;
    if (progress === -1) {
      if (dice === 6) target = 0;
    } else if (Number.isInteger(progress) && progress >= 0 && progress < LUDO_FINISH && progress + dice <= LUDO_FINISH) {
      target = progress + dice;
    }
    if (target === null || ludoOpponentBlockade(room, slot, target)) continue;
    legal.push(index);
  }
  return legal;
}

function ludoPublicState(room) {
  const state = ensureLudoState(room);
  return {
    tokens: { 1: [...state.tokens[1]], 2: [...state.tokens[2]] },
    currentPlayer: state.currentPlayer,
    dice: state.dice,
    phase: state.phase,
    legalMoves: [...state.legalMoves],
    consecutiveSixes: Number(state.consecutiveSixes[state.currentPlayer] || 0),
    revision: Number(state.revision || 0),
    serverTime: Date.now(),
    turnStartedAt: room.turnStartTime || null,
    graceStartedAt: room.graceStartTime || null,
    turnDuration: LUDO_TURN_DURATION,
    graceDuration: LUDO_GRACE_DURATION
  };
}

function emitLudoState(room, roomId, action = null) {
  io.to(roomId).emit('ludo_state', { room: roomId, state: ludoPublicState(room), action });
}

function clearLudoTurnTimers(room) {
  if (room.turnTimer) { clearTimeout(room.turnTimer); room.turnTimer = null; }
  if (room.graceTimer) { clearTimeout(room.graceTimer); room.graceTimer = null; }
  room.turnStartTime = null;
  room.graceStartTime = null;
}

function startLudoTurnTimer(room, roomId) {
  clearLudoTurnTimers(room);
  if (room.status !== 'playing') return;
  const state = ensureLudoState(room);
  const player = state.currentPlayer;
  room.turnStartTime = Date.now();
  io.to(roomId).emit('ludo_turn_start', {
    player: state.currentPlayer,
    serverTime: room.turnStartTime,
    startTime: room.turnStartTime,
    duration: LUDO_TURN_DURATION
  });
  persistRoomSoon('ludo', room);
  room.turnTimer = setTimeout(() => {
    room.turnTimer = null;
    if (room.status !== 'playing' || state.currentPlayer !== player) return;
    room.graceStartTime = Date.now();
    io.to(roomId).emit('ludo_turn_warning', {
      player: state.currentPlayer,
      serverTime: room.graceStartTime,
      startTime: room.graceStartTime,
      duration: LUDO_GRACE_DURATION
    });
    room.graceTimer = setTimeout(() => {
      room.graceTimer = null;
      if (room.status !== 'playing' || state.currentPlayer !== player) return;
      notifyLudoRoomOver(room, roomId, player === 1 ? 2 : 1, 'timeout');
    }, LUDO_GRACE_DURATION);
    if (room.graceTimer.unref) room.graceTimer.unref();
  }, LUDO_TURN_DURATION);
  if (room.turnTimer.unref) room.turnTimer.unref();
}

function beginNextLudoTurn(room, roomId, samePlayer = false, action = null) {
  if (room.status !== 'playing') return;
  const state = ensureLudoState(room);
  if (!samePlayer) state.currentPlayer = state.currentPlayer === 1 ? 2 : 1;
  state.dice = null;
  state.phase = 'roll';
  state.legalMoves = [];
  state.revision = Number(state.revision || 0) + 1;
  persistRoomSoon('ludo', room);
  emitLudoState(room, roomId, action);
  startLudoTurnTimer(room, roomId);
}

function applyLudoMove(room, slot, tokenIndex) {
  const state = ensureLudoState(room);
  if (!state.legalMoves.includes(tokenIndex)) return null;
  const dice = state.dice;
  const from = state.tokens[slot][tokenIndex];
  const to = from === -1 ? 0 : from + dice;
  state.tokens[slot][tokenIndex] = to;
  const captured = [];
  const absolute = ludoAbsoluteCell(slot, to);
  if (absolute !== null && !LUDO_SAFE_CELLS.has(absolute)) {
    const other = slot === 1 ? 2 : 1;
    state.tokens[other].forEach((progress, index) => {
      if (ludoAbsoluteCell(other, progress) === absolute) {
        state.tokens[other][index] = -1;
        captured.push(index);
      }
    });
  }
  return { player: slot, tokenIndex, from, to, dice, captured, finished: to === LUDO_FINISH };
}

function requireNonProductionLegacyGame(req, res, next) {
  if (process.env.NODE_ENV === 'production') {
    return res.status(410).json({ error: 'Cette ancienne API de jeu est désactivée. Utilisez le lobby sécurisé.' });
  }
  next();
}

function clearTimersForGame(gameName, room) {
  if (gameName === 'dames') clearDamesTurnTimers(room);
  else if (gameName === 'tictactoe') clearTTTTurnTimers(room);
  else if (gameName === 'quoridor') clearQuoriTurnTimers(room);
  else if (gameName === 'penalty') clearPenaltyTurnTimers(room);
  else if (gameName === 'chifoumi') clearChifoumiTurnTimers(room);
  else if (gameName === 'echecs') clearEchecsTurnTimers(room);
  else if (gameName === 'ludo') clearLudoTurnTimers(room);
}

function finishBothDisconnected(room, gameName, roomId) {
  if (!room || room.status === 'finished') return;
  room.status = 'finished';
  room.reconnectDeadline = null;
  clearTimersForGame(gameName, room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  room.pendingSettlement = { winnerSlot: 0, reason: 'both_disconnected' };
  void settleRoomInSupabase(room, gameName, 0, 'both_disconnected');
  const p1 = room.players[1], p2 = room.players[2];
  const { bet } = calcFinancial(room.betAmount);
  const penalty = Math.round(bet * 0.05);
  const payload = {
    type: 'game_over', game: gameName, room: roomId, result: 'cancel', reason: 'both_disconnected',
    penalty, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet,
    currency: room.currency || 'HTG', message: 'Les deux joueurs sont absents. Pénalité de 5% appliquée.'
  };
  if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...payload, myResult: -penalty }); io.to(p1.socketId).emit('game:result', { postMessage: { ...payload, myResult: -penalty } }); }
  if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...payload, myResult: -penalty }); io.to(p2.socketId).emit('game:result', { postMessage: { ...payload, myResult: -penalty } }); }
  io.to(roomId).emit('game:result', { postMessage: payload });
}

// ══════════════════════════════════════════════════════════
//  PAUSE / REPRISE / ANNULATION (Sanction 5% si les deux abandonnent)
// ══════════════════════════════════════════════════════════
function pauseAndWatch({ room, roomId, gameName, getP1, getP2, winFn, onResume }) {
  if (room.disconnectTimer) return;
  room.status = 'paused';
  const serverTime = Date.now();
  room.reconnectDeadline = serverTime + 60000;
  persistRoomSoon(gameName, room);
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
      finishBothDisconnected(room, gameName, roomId);
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
  // Player-specific results must not be broadcast to the whole room: both
  // sockets belong to it, so a shared win packet made the loser look like a winner.
  const cleanup = setTimeout(() => { if (games.get(game.id) === game) games.delete(game.id); }, ROOM_RETENTION_MS);
  if (cleanup.unref) cleanup.unref();
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
  io.to(roomId).emit('game:result', { postMessage: base });
}

function notifyEchecsRoomOver(eroom, roomId, winnerSlot, reason = 'normal') {
  if (eroom.status === 'finished') return;
  eroom.status = 'finished'; clearEchecsTurnTimers(eroom);
  if (eroom.disconnectTimer) { clearTimeout(eroom.disconnectTimer); eroom.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(eroom.betAmount);
  const p1 = eroom.players[1], p2 = eroom.players[2];
  void settleRoomInSupabase(eroom, 'echecs', winnerSlot, reason);

  if (winnerSlot === 0) {
    const base = { type: 'game_over', game: 'echecs', room: roomId, winner: 'draw', winnerSlot: 0, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission: 0, netGain: bet, currency: eroom.currency || 'HTG', reason: 'draw', detail: eroom.endDetail || reason };
    if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p1.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p2.socketId).emit('game:result', { postMessage: { ...base, result: 'draw' } }); }
    io.to(roomId).emit('game:result', { postMessage: base });
    return;
  }

  const winP = winnerSlot === 1 ? p1 : p2, losP = winnerSlot === 1 ? p2 : p1;
  const base = { type: 'game_over', game: 'echecs', room: roomId, winner: winnerSlot === 1 ? 'player1' : 'player2', winnerSlot, winnerSupabaseId: winP?.supabaseId, loserSupabaseId: losP?.supabaseId, p1Id: p1?.supabaseId, p2Id: p2?.supabaseId, betAmount: bet, totalPot, commission, netGain, currency: eroom.currency || 'HTG', reason };
  if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win',  myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win',  myResult: +netGain } }); }
  if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet });     io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
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
  io.to(roomId).emit('game:result', { postMessage: base });
}

function notifyLudoRoomOver(room, roomId, winnerSlot, reason = 'normal') {
  if (room.status === 'finished') return;
  room.status = 'finished';
  clearLudoTurnTimers(room);
  if (room.disconnectTimer) { clearTimeout(room.disconnectTimer); room.disconnectTimer = null; }
  const { bet, totalPot, commission, netGain } = calcFinancial(room.betAmount);
  const p1 = room.players[1], p2 = room.players[2];
  void settleRoomInSupabase(room, 'ludo', winnerSlot, reason);
  const base = {
    type: 'game_over', game: 'ludo', room: roomId,
    winner: winnerSlot === 1 ? 'player1' : winnerSlot === 2 ? 'player2' : 'draw',
    winnerSlot,
    winnerSupabaseId: winnerSlot ? room.players[winnerSlot]?.supabaseId : null,
    loserSupabaseId: winnerSlot ? room.players[winnerSlot === 1 ? 2 : 1]?.supabaseId : null,
    p1Id: p1?.supabaseId, p2Id: p2?.supabaseId,
    betAmount: bet, totalPot,
    commission: winnerSlot ? commission : 0,
    netGain: winnerSlot ? netGain : bet,
    currency: room.currency || 'HTG',
    reason: winnerSlot ? reason : 'draw',
    finalState: ludoPublicState(room)
  };
  io.to(roomId).emit('ludo_game_over', base);
  if (winnerSlot === 0) {
    if (p1?.socketId) { io.to(p1.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p1.socketId).emit('game:result', { postMessage: { ...base, result: 'draw', myResult: 0 } }); }
    if (p2?.socketId) { io.to(p2.socketId).emit('game:over', { ...base, result: 'draw', myResult: 0 }); io.to(p2.socketId).emit('game:result', { postMessage: { ...base, result: 'draw', myResult: 0 } }); }
  } else {
    const winP = winnerSlot === 1 ? p1 : p2;
    const losP = winnerSlot === 1 ? p2 : p1;
    if (winP?.socketId) { io.to(winP.socketId).emit('game:over', { ...base, result: 'win', myResult: +netGain }); io.to(winP.socketId).emit('game:result', { postMessage: { ...base, result: 'win', myResult: +netGain } }); }
    if (losP?.socketId) { io.to(losP.socketId).emit('game:over', { ...base, result: 'loss', myResult: -bet }); io.to(losP.socketId).emit('game:result', { postMessage: { ...base, result: 'loss', myResult: -bet } }); }
  }
  io.to(roomId).emit('game:result', { postMessage: base });
}

// A voluntary resignation is different from a mutual quit: one authenticated
// participant gives up and the other participant wins. Keep this operation on
// the authoritative game server so the room outcome and escrow are settled by
// the same idempotent path as a normal server-detected victory.
function getRoomFinisher(gameName) {
  return {
    dames: notifyDamesRoomOver,
    tictactoe: notifyTTTRoomOver,
    quoridor: notifyQuoriRoomOver,
    penalty: notifyPenaltyRoomOver,
    chifoumi: notifyChifoumiRoomOver,
    echecs: notifyEchecsRoomOver,
    ludo: notifyLudoRoomOver
  }[gameName] || null;
}

function findAuthoritativeRoom(gameId) {
  for (const [gameName, roomMap] of Object.entries(ROOM_MAPS)) {
    const direct = roomMap.get(gameId);
    if (direct) return { gameName, roomId: gameId, room: direct };
    for (const [roomId, room] of roomMap.entries()) {
      if (room?.databaseGameId === gameId) return { gameName, roomId, room };
    }
  }
  return null;
}

async function hydrateRoomParticipantsFromDatabase(entry) {
  const { gameName, room } = entry || {};
  if (!room || !isUuid(room.databaseGameId)) return false;
  if (room.players?.[1]?.supabaseId && room.players?.[2]?.supabaseId) return true;

  const dbGame = await loadDatabaseGameForJoin(room.databaseGameId);
  const sameType = dbGame?.game_type === DB_GAME_TYPES[gameName];
  const sameBet = dbGame && Math.abs(Number(dbGame.bet_amount || 0) - Number(room.betAmount || 0)) < 0.0001;
  const existingP1 = room.players?.[1]?.supabaseId;
  const existingP2 = room.players?.[2]?.supabaseId;
  if (!sameType || !sameBet || (existingP1 && existingP1 !== dbGame.player1_id) || (existingP2 && existingP2 !== dbGame.player2_id)) {
    return false;
  }

  room.players = room.players || {};
  if (!existingP1 && isUuid(dbGame.player1_id)) {
    room.players[1] = { slot: 1, supabaseId: dbGame.player1_id, name: 'Joueur 1', connected: false, socketId: null, userId: null };
  }
  if (!existingP2 && isUuid(dbGame.player2_id)) {
    room.players[2] = { slot: 2, supabaseId: dbGame.player2_id, name: 'Joueur 2', connected: false, socketId: null, userId: null };
  }
  persistRoomSoon(gameName, room);
  return !!(room.players[1]?.supabaseId && room.players[2]?.supabaseId);
}

function resignAuthoritativeRoom(entry, supabaseId) {
  const { gameName, roomId, room } = entry || {};
  const finisher = getRoomFinisher(gameName);
  if (!room || !finisher || (!isUuid(supabaseId) && process.env.NODE_ENV === 'production')) {
    return { ok: false, status: 404, error: 'Partie autoritative introuvable.' };
  }
  const loserSlot = room.players?.[1]?.supabaseId === supabaseId
    ? 1
    : room.players?.[2]?.supabaseId === supabaseId
      ? 2
      : 0;
  if (!loserSlot) return { ok: false, status: 403, error: 'Vous ne participez pas à cette partie.' };

  // Once a terminal outcome has been chosen, never replace it. This is the
  // idempotent retry path for a dialog that remained open while the 60-second
  // server deadline elapsed.
  if (room.status === 'finished') {
    return {
      ok: true,
      alreadyFinished: true,
      settlementPending: !!room.pendingSettlement,
      gameName,
      roomId
    };
  }
  if (room.status !== 'playing' && room.status !== 'paused') {
    return { ok: false, status: 409, error: 'La partie n’a pas encore commencé ou n’est plus abandonnable.' };
  }

  const winnerSlot = loserSlot === 1 ? 2 : 1;
  if (!room.players?.[winnerSlot]?.supabaseId) {
    return { ok: false, status: 409, error: 'L’adversaire de cette partie est introuvable.' };
  }
  finisher(room, roomId, winnerSlot, 'resign');
  return {
    ok: true,
    alreadyFinished: false,
    settlementPending: !!room.pendingSettlement,
    gameName,
    roomId,
    loserSlot,
    winnerSlot
  };
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
    echecsRooms: echecsRooms.size, ludoRooms: ludoRooms.size,
    ludoConfig: { finish: LUDO_FINISH, starts: { yellow: LUDO_START_OFFSET[1], blue: LUDO_START_OFFSET[2] } },
    spectatorProtocol: { version: 1, event: 'spectator_join', readOnly: true },
    queuedPlayers: [...queue.values()].reduce((total, players) => total + players.length, 0)
  });
});

// Serve the 3D runtime from the same origin as the game. Some mobile networks
// take several seconds (or fail entirely) when the iframe has to open a second
// TLS connection to a public CDN before it can draw the board. Render fetches
// the pinned runtime once, keeps it in memory, and browsers cache the versioned
// URL. The two fixed upstreams are fallbacks only; no user-controlled URL is
// ever fetched.
let threeRuntimeSource = null;
let threeRuntimeInFlight = null;
async function loadThreeRuntime() {
  if (threeRuntimeSource) return threeRuntimeSource;
  if (threeRuntimeInFlight) return threeRuntimeInFlight;
  threeRuntimeInFlight = (async () => {
    const sources = [
      'https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js',
      'https://cdn.jsdelivr.net/npm/three@0.128.0/build/three.min.js'
    ];
    let lastError = null;
    for (const source of sources) {
      const controller = new AbortController();
      const timeout = setTimeout(() => controller.abort(), 8000);
      try {
        const response = await fetch(source, { signal: controller.signal });
        if (!response.ok) throw new Error('three_runtime_' + response.status);
        const body = await response.text();
        if (body.length < 100000 || !body.includes('THREE')) throw new Error('three_runtime_invalid');
        threeRuntimeSource = body;
        return body;
      } catch (error) {
        lastError = error;
      } finally {
        clearTimeout(timeout);
      }
    }
    throw lastError || new Error('three_runtime_unavailable');
  })();
  try {
    return await threeRuntimeInFlight;
  } finally {
    threeRuntimeInFlight = null;
  }
}

app.get('/vendor/three-r128.min.js', async (req, res) => {
  try {
    const source = await loadThreeRuntime();
    res.setHeader('Content-Type', 'application/javascript; charset=utf-8');
    res.setHeader('Cache-Control', 'public, max-age=86400, immutable');
    res.send(source);
  } catch (error) {
    console.error('[assets] Three.js runtime unavailable', error?.message || error);
    res.status(503).type('text/plain').send('3D runtime temporarily unavailable');
  }
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
      if (!isUuid(p1Id) || !isUuid(p2Id)) return res.status(400).send('Identifiants de joueurs invalides.');
      const ids = [p1Id, p2Id].sort();
      const generatedRoom = 'room-' + ids[0].slice(-8) + '-' + ids[1].slice(-8);
      const safeRoomLiteral = JSON.stringify(generatedRoom).replace(/</g, '\\u003c');
      const injection = `<script>(function(){ var u = new URL(window.location.href); if (!u.searchParams.get('room')) { u.searchParams.set('room', ${safeRoomLiteral}); window.history.replaceState({}, '', u.toString()); } })();</script>`;
      html = html.replace('</head>', injection + '\n</head>');
    }
  }

  res.setHeader('Content-Type', 'text/html;charset=utf-8');
  res.setHeader('Cache-Control', 'no-store, max-age=0');
  res.send(html);
};

// ── LIAISONS ROUTES ──
app.get(['/game', '/game-online.html', '/game.html'], serveSmart(['game.html', 'game-online.html']));
app.get(['/dames', '/dames.html', '/dames-online.html', '/dames_multi.html'], serveSmart(['dames_multi.html', 'dames.html', 'dames-online.html']));
app.get(['/dames-ai', '/dames_ai.html', '/dames-solo', '/dames-entrainement', '/dames-practice', '/dames-ia'], serveSmart(['dames_ai.html', 'dames-ai.html']));
app.get(['/ttt', '/ttt.html', '/ttt-online.html', '/ttt_game.html'], serveSmart(['ttt_game.html', 'ttt.html', 'ttt-online.html']));
app.get(['/tictactoe-ai', '/ttt-ai', '/ttt_ai.html', '/tictactoe_ai.html', '/ttt-solo', '/tictactoe-solo', '/ttt-entrainement', '/tictactoe-entrainement', '/ttt-ia', '/tictactoe-ia'], serveSmart(['ttt_ai.html', 'tictactoe_ai.html', 'ttt-ai.html']));
app.get(['/quoridor', '/quoridor.html', '/quoridor-online.html', '/quoridor_multi.html'], serveSmart(['quoridor_multi.html', 'quoridor.html', 'quoridor-online.html']));
app.get(['/quoridor-ai', '/quoridor_ai.html', '/quoridor-solo', '/quoridor-entrainement', '/quoridor-ia'], serveSmart(['quoridor_ai.html', 'quoridor-ai.html']));
app.get(['/chifoumi', '/chifoumi.html', '/chifoumi-online.html'], serveSmart(['chifoumi-online.html', 'chifoumi.html']));
app.get(['/chifoumi-ai', '/chifoumi_ai.html', '/chifoumi-solo', '/chifoumi-entrainement', '/chifoumi-ia'], serveSmart(['chifoumi_ai.html', 'chifoumi-ai.html']));
app.get(['/penalty', '/penalty.html', '/penalty_shootout.html', '/penalty-online.html', '/penalty_online.html'], serveSmart(['penalty_online.html', 'penalty_shootout.html', 'penalty-online.html', 'penalty.html'], true));
app.get(['/penalty-ai', '/penalty_ai.html', '/penalty-solo', '/penalty-entrainement', '/penalty-ia'], serveSmart(['penalty_ai.html', 'penalty-ai.html'], true));
app.get(['/echecs', '/echecs.html', '/echecs-online.html', '/echecs_multi.html', '/chess', '/chess.html', '/chess-online.html'], serveSmart(['echecs_multi.html', 'echecs.html', 'echecs-online.html']));
app.get(['/echecs-ai', '/echecs_ai.html', '/echecs-solo', '/echecs-entrainement', '/echecs-ia', '/chess-ai', '/chess_ai.html', '/chess-solo', '/chess-ia'], serveSmart(['echecs_ai.html', 'echecs-ai.html']));

// Moteur d'échecs partagé : servi depuis la même origine (pages 3D + Worker IA).
app.get(['/echecs-engine.js', '/chess-engine.js'], (req, res) => {
  res.setHeader('Content-Type', 'application/javascript; charset=utf-8');
  res.setHeader('Cache-Control', 'public, max-age=300');
  res.sendFile(path.join(PUBLIC, 'echecs-engine.js'));
});

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
  const token = createServerToken(users.get(id));
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
  const token = createServerToken(user);
  res.json({ token, userId: user.id, username: user.username });
});

app.post('/matchmaking/join', requireNonProductionLegacyGame, requireAuth, (req, res) => {
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

app.post('/matchmaking/leave', requireNonProductionLegacyGame, requireAuth, (req, res) => {
  const { betAmount } = req.body;
  if (betAmount) { const ex = queue.get(betAmount) || []; queue.set(betAmount, ex.filter(p => p.userId !== req.userId)); }
  else for (const [amt, pl] of queue.entries()) queue.set(amt, pl.filter(p => p.userId !== req.userId));
  res.json({ status: 'left' });
});

// Compatibility gate used by the current web client before it opens the game
// iframe. It never creates or mutates a legacy in-memory game. It only proves
// that the authenticated Supabase account belongs to an active database game.
// Socket.io validates these facts again before creating/restoring the room.
app.post('/game/join', requireAuth, async (req, res) => {
  const { gameId, username, supabaseId, betAmount } = req.body || {};
  if (!isUuid(gameId)) return res.status(400).json({ error: 'Identifiant de partie invalide.' });

  const user = users.get(req.userId);
  if (!user?.supabaseId) return res.status(401).json({ error: 'Session Supabase requise.' });
  if (supabaseId && supabaseId !== user.supabaseId) {
    return res.status(403).json({ error: 'Identité de joueur invalide.' });
  }
  if (!SUPABASE_URL || !SUPABASE_SERVICE_ROLE_KEY) {
    return res.status(503).json({ error: 'Validation serveur temporairement indisponible.' });
  }
  if (betAmount !== undefined && (!Number.isFinite(Number(betAmount)) || Number(betAmount) < 0)) {
    return res.status(400).json({ error: 'Montant de mise invalide.' });
  }

  try {
    const game = await loadDatabaseGameForJoin(gameId);
    const playerSlot = game?.player1_id === user.supabaseId ? 1 : game?.player2_id === user.supabaseId ? 2 : 0;
    const knownGameType = game && Object.values(DB_GAME_TYPES).includes(game.game_type);
    const sameBet = betAmount === undefined || Math.abs(Number(game?.bet_amount || 0) - Number(betAmount)) < 0.0001;

    if (!game || !playerSlot || !knownGameType || !sameBet) {
      return res.status(403).json({ error: 'Cette partie ne correspond pas au joueur, au jeu ou à la mise.' });
    }
    if (!['waiting', 'in_progress'].includes(game.status)) {
      return res.status(409).json({ error: 'Cette partie est déjà terminée.' });
    }

    if (username) user.username = safeName(username, user.username);
    return res.json({
      status: 'ready',
      gameId: game.id,
      gameType: game.game_type,
      playerSlot,
      youAre: playerSlot === 1 ? 'player1' : 'player2',
      betAmount: Number(game.bet_amount || 0)
    });
  } catch (error) {
    console.error('[game/join] validation failed', error?.message || error);
    return res.status(503).json({ error: 'Validation serveur temporairement indisponible.' });
  }
});

// Used by the global reconnect dialog, where no game iframe/socket is open.
// The signed server JWT identifies the Supabase participant; the browser can
// neither choose the winner nor write games/wallets directly.
app.post('/game/resign', requireAuth, async (req, res) => {
  if (!rateLimit('game-resign:' + req.userId, 10, 60000)) {
    return res.status(429).json({ error: 'Trop de tentatives. Réessayez dans un instant.' });
  }
  const gameId = req.body?.gameId;
  if (!isUuid(gameId) && !(process.env.NODE_ENV !== 'production' && validRoom(gameId))) {
    return res.status(400).json({ error: 'Identifiant de partie invalide.' });
  }
  const user = users.get(req.userId);
  if (!user?.supabaseId) return res.status(401).json({ error: 'Session Supabase requise.' });

  const entry = findAuthoritativeRoom(gameId);
  try {
    if (entry) await hydrateRoomParticipantsFromDatabase(entry);
  } catch (error) {
    console.error('[game/resign] participant recovery failed', error?.message || error);
  }
  const result = resignAuthoritativeRoom(entry, user.supabaseId);
  if (!result.ok) return res.status(result.status || 400).json({ error: result.error });
  return res.status(result.settlementPending ? 202 : 200).json({
    ok: true,
    status: result.alreadyFinished ? 'already_finished' : 'resigned',
    settlementPending: result.settlementPending,
    game: result.gameName,
    room: result.roomId
  });
});

app.post('/game/join-legacy', requireNonProductionLegacyGame, requireAuth, (req, res) => {
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

app.get('/games/:id', requireNonProductionLegacyGame, requireAuth, (req, res) => {
  const game = games.get(req.params.id);
  if (!game) return res.status(404).json({ error: 'Partie introuvable' });
  const color = game.playerWhite === req.userId ? 'white' : game.playerBlack === req.userId ? 'black' : null;
  if (!color) return res.status(403).json({ error: 'Accès refusé' });
  res.json({ gameId: game.id, board: game.board, currentPlayer: game.currentPlayer, status: game.status, winner: game.winner, betAmount: game.betAmount, youAre: color, opponentName: color === 'white' ? users.get(game.playerBlack)?.username : users.get(game.playerWhite)?.username });
});

app.post('/games/:id/move', requireNonProductionLegacyGame, requireAuth, (req, res) => {
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

app.post('/games/:id/resign', requireNonProductionLegacyGame, requireAuth, (req, res) => {
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
  socket.authDeadline = setTimeout(() => {
    if (!socket.userId) socket.disconnect(true);
  }, 15000);
  if (socket.authDeadline.unref) socket.authDeadline.unref();

  const authenticated = () => {
    if (socket.authDeadline) { clearTimeout(socket.authDeadline); socket.authDeadline = null; }
  };
  if (socket.userId) authenticated();

  // Anti-flood : un socket qui envoie un volume anormal d'événements est déconnecté.
  // Seuil très large (500 / 10 s) : les vrais joueurs ne l'atteignent jamais, seuls les bots.
  socket.onAny(() => {
    if (!socketAllow(socket.id, 'any', 500, 10000)) {
      try { socket.disconnect(true); } catch (e) {}
    }
  });

  socket.on('auth', ({ token }) => {
    if (authenticateSocketToken(socket, token)) { authenticated(); socket.emit('auth:ok', { userId: socket.userId }); }
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
      authenticated();
      const token = createServerToken(found);
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
    authenticated();
    const token = createServerToken(found);
    socket.emit('auth:ok', { userId: found.id, token });
  });

  socket.on('game:join_room', ({ gameId }) => {
    const game = games.get(gameId);
    if (!validRoom(gameId) || !authenticatedSocketUser(socket) || !game || (game.playerWhite !== socket.userId && game.playerBlack !== socket.userId)) {
      return rejectSocket(socket, 'Accès à cette partie refusé.');
    }
    socket.join(gameId);
  });

  // Spectators join a real server-owned room in read-only mode. They never
  // occupy a player slot, so every move/result handler keeps rejecting them.
  // The initial snapshot is sanitised: hidden Penalty/RPS choices are omitted.
  socket.on('spectator_join', async ({ gameId } = {}) => {
    if (!authenticatedSocketUser(socket)) {
      return socket.emit('spectator:error', { code: 'not_authenticated', message: 'Connexion requise pour regarder ce direct.' });
    }
    if (!isUuid(gameId) || !socketAllow(socket.id, 'spectator-join', 20, 60000)) {
      return socket.emit('spectator:error', { code: 'invalid_request', message: 'Direct indisponible.' });
    }

    let databaseGame;
    try {
      databaseGame = await loadDatabaseGameForJoin(gameId);
    } catch {
      return socket.emit('spectator:error', { code: 'verification_failed', message: 'Vérification du direct indisponible.' });
    }
    if (!databaseGame ||
        databaseGame.status !== 'in_progress' ||
        databaseGame.is_ai_opponent === true ||
        !databaseGame.player1_id ||
        !databaseGame.player2_id ||
        databaseGame.player1_id === databaseGame.player2_id) {
      return socket.emit('spectator:error', { code: 'not_live', message: 'Ce match n’est plus en direct.' });
    }

    const live = findLiveRoomByDatabaseGameId(gameId);
    if (!live || DB_GAME_TYPES[live.gameName] !== databaseGame.game_type) {
      return socket.emit('spectator:error', { code: 'room_not_live', message: 'Le plateau n’est plus disponible en direct.' });
    }
    const snapshot = spectatorRoomSnapshot(live.gameName, live.room);
    if (!snapshot) {
      return socket.emit('spectator:error', { code: 'unsupported_game', message: 'Ce plateau ne peut pas encore être diffusé.' });
    }

    if (socket.spectatorRoomId && socket.spectatorRoomId !== live.roomId) {
      socket.leave(socket.spectatorRoomId);
    }
    socket.spectatorRoomId = live.roomId;
    socket.spectatorGameId = gameId;
    socket.join(live.roomId);
    socket.emit('spectator:joined', {
      gameId,
      room: live.roomId,
      gameType: databaseGame.game_type,
      readOnly: true
    });
    socket.emit('spectator_state', snapshot);
    emitSpectatorCount(live.roomId);
  });

  socket.on('spectator_leave', () => {
    const roomId = socket.spectatorRoomId;
    if (roomId) {
      socket.leave(roomId);
      emitSpectatorCount(roomId);
    }
    socket.spectatorRoomId = null;
    socket.spectatorGameId = null;
  });

  // Un spectateur peut redemander un snapshot complet après une coupure ou un
  // événement manqué. Cette voie reste strictement en lecture seule et ne
  // permet jamais de rejoindre une place joueur ni d'envoyer un coup.
  socket.on('spectator_request_state', ({ gameId } = {}) => {
    if (!socketAllow(socket.id, 'spectator-state', 12, 10000)) return;
    if (!isUuid(gameId) || socket.spectatorGameId !== gameId || !socket.spectatorRoomId) return;
    const live = findLiveRoomByDatabaseGameId(gameId);
    if (!live || live.roomId !== socket.spectatorRoomId) {
      return socket.emit('spectator:error', { code: 'not_live', message: 'Ce match n’est plus en direct.' });
    }
    const snapshot = spectatorRoomSnapshot(live.gameName, live.room);
    if (snapshot) socket.emit('spectator_state', snapshot);
  });

  socket.on('disconnecting', () => {
    const roomId = socket.spectatorRoomId;
    if (!roomId) return;
    socket.to(roomId).emit('spectator_count', {
      room: roomId,
      count: Math.max(0, spectatorCountForRoom(roomId) - 1)
    });
  });

  // ══════════════════════════════════════════════════════
  //  DAMES MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('dames_join', async ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
    const databaseCheck = await verifyDatabaseGameForJoin(socket, gameId, 'dames', player, bet, room);
    if (!databaseCheck.ok) return rejectSocket(socket, databaseCheck.message);
    let droom = damesRooms.get(room);
    if (!droom) {
      droom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, engineBoard: initialBoard(), boardState: JSON.stringify(checkersClientBoard(initialBoard())), currentPlayer: 0, lastMove: null, stateVersion: 0, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null };
      damesRooms.set(room, droom);
    }
    if (!bindDatabaseGame(droom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, droom, room, player, supabaseId, name)) return;
    if (bet && !droom.betAmount) droom.betAmount = bet;
    persistRoomSoon('dames', droom);
    socket.emit('dames_joined', {
      room,
      player,
      waitingForOpponent: !(droom.players[1] && droom.players[2])
    });

    if (droom.status === 'playing' || droom.status === 'paused') {
      const p1 = droom.players[1], p2 = droom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && droom.disconnectTimer) {
        clearTimeout(droom.disconnectTimer); droom.disconnectTimer = null; droom.reconnectDeadline = null; droom.status = 'playing';
        startDamesTurnTimer(droom, room, droom.pausedTurnPlayer || 1);
        io.to(room).emit('dames_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
        io.to(room).emit('dames_state_sync', damesSnapshot(droom));
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
              finishBothDisconnected(droom, 'dames', room);
            } else { const ws = p1b ? 1 : 2; droom.status = 'playing'; notifyDamesRoomOver(droom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }
      socket.to(room).emit('dames_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (droom.players[2]?.name || 'Adversaire') : (droom.players[1]?.name || 'Adversaire');
      socket.emit('dames_start', { room, yourSlot: player, opponentName, bet: droom.betAmount, currency: droom.currency, reconnected: true, paused: droom.status === 'paused', boardState: droom.boardState || null, currentPlayer: droom.currentPlayer !== undefined ? droom.currentPlayer : 0, lastMove: droom.lastMove || null, stateVersion: droom.stateVersion || 0 });
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
      persistRoomSoon('dames', droom);
      const p1 = droom.players[1], p2 = droom.players[2];
      io.to(p1.socketId).emit('dames_start', { room, yourSlot: 1, opponentName: p2.name, bet: droom.betAmount, currency: droom.currency, reconnected: false });
      io.to(p2.socketId).emit('dames_start', { room, yourSlot: 2, opponentName: p1.name, bet: droom.betAmount, currency: droom.currency, reconnected: false });
      const initialVersion = droom.stateVersion;
      setTimeout(() => {
        if (droom.status === 'playing' && droom.stateVersion === initialVersion && !droom.turnStartTime) {
          startDamesTurnTimer(droom, room, 1);
        }
      }, 3000);
    }
  });

  socket.on('dames_move', ({ room, player, from, to, steps }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const droom = damesRooms.get(room);
    if (!droom || droom.status !== 'playing' || droom.players[player]?.socketId !== socket.id) return;
    // Sur rejet, on renvoie l'état autoritatif après l'erreur : un client dont
    // le plateau a divergé (coup local appliqué mais refusé ici) se recale au
    // lieu de rester figé sur une position que le serveur ne connaît pas.
    if (droom.currentPlayer !== player - 1) { rejectSocket(socket, 'Ce n’est pas votre tour.'); return void socket.emit('dames_state_sync', damesSnapshot(droom)); }
    const sequence = Array.isArray(steps) && steps.length ? steps : [{ from, to }];
    const first = sequence[0]?.from, last = sequence[sequence.length - 1]?.to;
    if (!first || !last || !Number.isInteger(first.row) || !Number.isInteger(first.col) || !Number.isInteger(last.row) || !Number.isInteger(last.col)) return rejectSocket(socket, 'Coup de dames invalide.');
    const result = applyMove(droom.engineBoard, player === 1 ? 'white' : 'black', first.row, first.col, last.row, last.col);
    if (!result.ok) { rejectSocket(socket, result.reason); return void socket.emit('dames_state_sync', damesSnapshot(droom)); }
    droom.engineBoard = result.board;
    droom.boardState = JSON.stringify(checkersClientBoard(result.board));
    droom.currentPlayer = result.next === 'white' ? 0 : 1;
    droom.stateVersion = (droom.stateVersion || 0) + 1;
    droom.lastMove = { from: first, to: last, player };
    socket.to(room).emit('dames_move', { room, player, steps: sequence, boardState: droom.boardState, nextPlayer: droom.currentPlayer, isComplete: true, version: droom.stateVersion });
    // Accusé de réception : le joueur sait que son coup est enregistré. Sans
    // ack sous quelques secondes, son client redemande l'état complet.
    socket.emit('dames_move_ack', { room, version: droom.stateVersion, currentPlayer: droom.currentPlayer });
    persistRoomSoon('dames', droom);
    if (result.winner) return notifyDamesRoomOver(droom, room, result.winner === 'white' ? 1 : 2, 'checkmate');
    startDamesTurnTimer(droom, room, droom.currentPlayer + 1);
  });

  // Un joueur de la room peut redemander l'état exact à tout moment (plateau
  // figé, événement raté, doute après reconnexion). Lecture seule, limitée.
  socket.on('dames_request_state', ({ room } = {}) => {
    if (!validRoom(room)) return;
    if (!socketAllow(socket.id, 'dsync', 20, 10000)) return;
    const droom = damesRooms.get(room);
    if (!droom || !socketIsPlayer(droom, socket.id)) return;
    socket.emit('dames_state_sync', damesSnapshot(droom));
  });

  socket.on('dames_result', (data) => {
    if (!data || !validRoom(data.room)) return;
    // Legacy clients still emit this after their animation. It is intentionally
    // ignored: only the authoritative move engine can finish a match.
  });

  // ══════════════════════════════════════════════════════
  //  ÉCHECS MULTIJOUEUR (moteur FIDE autoritatif serveur)
  // ══════════════════════════════════════════════════════
  socket.on('echecs_join', async ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
    const databaseCheck = await verifyDatabaseGameForJoin(socket, gameId, 'echecs', player, bet, room);
    if (!databaseCheck.ok) return rejectSocket(socket, databaseCheck.message);
    let eroom = echecsRooms.get(room);
    if (!eroom) {
      eroom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, engineState: ChessEngine.initialState(), currentPlayer: 0, lastMove: null, stateVersion: 0, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null };
      echecsRooms.set(room, eroom);
    }
    ensureEchecsEngineState(eroom);
    if (!bindDatabaseGame(eroom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, eroom, room, player, supabaseId, name)) return;
    if (bet && !eroom.betAmount) eroom.betAmount = bet;
    persistRoomSoon('echecs', eroom);
    socket.emit('echecs_joined', {
      room,
      player,
      waitingForOpponent: !(eroom.players[1] && eroom.players[2])
    });

    if (eroom.status === 'playing' || eroom.status === 'paused') {
      const p1 = eroom.players[1], p2 = eroom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && eroom.disconnectTimer) {
        clearTimeout(eroom.disconnectTimer); eroom.disconnectTimer = null; eroom.reconnectDeadline = null; eroom.status = 'playing';
        startEchecsTurnTimer(eroom, room, eroom.pausedTurnPlayer || eroom.currentPlayer + 1 || 1);
        io.to(room).emit('echecs_game_resumed', { message: 'Les deux joueurs sont de retour. La partie reprend !' });
        io.to(room).emit('echecs_state_sync', echecsSnapshot(eroom));
      } else if (eroom.disconnectTimer) {
        setTimeout(() => socket.emit('game:reconnect_deadline', { game: 'echecs', serverTime: Date.now(), reconnectDeadline: eroom.reconnectDeadline }), 0);
      }
      else if (!bothBack) {
        eroom.status = 'playing';
        const otherSlot = player === 1 ? 2 : 1;
        if (eroom.players[otherSlot] && !eroom.players[otherSlot].connected) {
          eroom.disconnectTimer = setTimeout(() => {
            if (eroom.status === 'finished') return;
            const p1b = eroom.players[1]?.connected === true, p2b = eroom.players[2]?.connected === true;
            eroom.disconnectTimer = null;
            if (!p1b && !p2b) {
              finishBothDisconnected(eroom, 'echecs', room);
            } else { const ws = p1b ? 1 : 2; eroom.status = 'playing'; notifyEchecsRoomOver(eroom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }
      socket.to(room).emit('echecs_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (eroom.players[2]?.name || 'Adversaire') : (eroom.players[1]?.name || 'Adversaire');
      socket.emit('echecs_start', { room, yourSlot: player, opponentName, bet: eroom.betAmount, currency: eroom.currency, reconnected: true, paused: eroom.status === 'paused', gameState: JSON.stringify(ChessEngine.exportState(ensureEchecsEngineState(eroom))), currentPlayer: eroom.currentPlayer !== undefined ? eroom.currentPlayer : 0, lastMove: eroom.lastMove || null, stateVersion: eroom.stateVersion || 0 });
      if (eroom.turnPlayer !== null && eroom.status === 'playing') {
        const now = Date.now();
        if (eroom.graceStartTime) socket.emit('echecs_turn_sync', { serverTime: now, turnPlayer: eroom.turnPlayer, graceStartTime: eroom.graceStartTime, duration: GRACE_DURATION });
        else if (eroom.turnStartTime) socket.emit('echecs_turn_sync', { serverTime: now, turnPlayer: eroom.turnPlayer, turnStartTime: eroom.turnStartTime, duration: TURN_DURATION });
      }
      return;
    }

    if (eroom.players[1] && eroom.players[2] && eroom.status === 'waiting') {
      eroom.status = 'playing';
      eroom.startedAt = Date.now();
      persistRoomSoon('echecs', eroom);
      const p1 = eroom.players[1], p2 = eroom.players[2];
      io.to(p1.socketId).emit('echecs_start', { room, yourSlot: 1, opponentName: p2.name, bet: eroom.betAmount, currency: eroom.currency, reconnected: false });
      io.to(p2.socketId).emit('echecs_start', { room, yourSlot: 2, opponentName: p1.name, bet: eroom.betAmount, currency: eroom.currency, reconnected: false });
      const initialVersion = eroom.stateVersion;
      setTimeout(() => {
        if (eroom.status === 'playing' && eroom.stateVersion === initialVersion && !eroom.turnStartTime) {
          startEchecsTurnTimer(eroom, room, 1);
        }
      }, 3000);
    }
  });

  socket.on('echecs_move', ({ room, player, from, to, promo }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const eroom = echecsRooms.get(room);
    if (!eroom || eroom.status !== 'playing' || eroom.players[player]?.socketId !== socket.id) return;
    // Sur rejet, on renvoie l'état autoritatif : un client dont le plateau a
    // divergé se recale au lieu de rester figé.
    if (eroom.currentPlayer !== player - 1) { rejectSocket(socket, 'Ce n’est pas votre tour.'); return void socket.emit('echecs_state_sync', echecsSnapshot(eroom)); }
    if (!from || !to || !Number.isInteger(from.row) || !Number.isInteger(from.col) || !Number.isInteger(to.row) || !Number.isInteger(to.col) ||
        from.row < 0 || from.row > 7 || from.col < 0 || from.col > 7 || to.row < 0 || to.row > 7 || to.col < 0 || to.col > 7) {
      return rejectSocket(socket, 'Coup d’échecs invalide.');
    }
    const state = ensureEchecsEngineState(eroom);
    const expectedSide = player === 1 ? 0 : 1;
    if (state.t !== expectedSide) { rejectSocket(socket, 'Ce n’est pas votre tour.'); return void socket.emit('echecs_state_sync', echecsSnapshot(eroom)); }
    const mv = ChessEngine.findMove(state, from.row * 8 + from.col, to.row * 8 + to.col, promo);
    if (!mv) { rejectSocket(socket, 'Coup d’échecs illégal.'); return void socket.emit('echecs_state_sync', echecsSnapshot(eroom)); }
    eroom.engineState = ChessEngine.applyMove(state, mv);
    eroom.currentPlayer = eroom.engineState.t;
    eroom.stateVersion = (eroom.stateVersion || 0) + 1;
    eroom.lastMove = { from: { row: from.row, col: from.col }, to: { row: to.row, col: to.col }, player };
    const status = ChessEngine.gameStatus(eroom.engineState);
    socket.to(room).emit('echecs_move', {
      room, player,
      from: { row: from.row, col: from.col },
      to: { row: to.row, col: to.col },
      promo: mv.p || 0,
      gameState: JSON.stringify(ChessEngine.exportState(eroom.engineState)),
      nextPlayer: eroom.currentPlayer,
      version: eroom.stateVersion
    });
    // Accusé de réception : le joueur sait que son coup est enregistré. Sans
    // ack sous quelques secondes, son client redemande l'état complet.
    socket.emit('echecs_move_ack', { room, version: eroom.stateVersion, currentPlayer: eroom.currentPlayer });
    persistRoomSoon('echecs', eroom);
    if (status.over) {
      if (status.reason === 'checkmate') return notifyEchecsRoomOver(eroom, room, status.winner === 0 ? 1 : 2, 'checkmate');
      eroom.endDetail = status.reason;
      return notifyEchecsRoomOver(eroom, room, 0, 'draw');
    }
    startEchecsTurnTimer(eroom, room, eroom.currentPlayer + 1);
  });

  // Un joueur de la room peut redemander l'état exact à tout moment.
  socket.on('echecs_request_state', ({ room } = {}) => {
    if (!validRoom(room)) return;
    if (!socketAllow(socket.id, 'esync', 20, 10000)) return;
    const eroom = echecsRooms.get(room);
    if (!eroom || !socketIsPlayer(eroom, socket.id)) return;
    socket.emit('echecs_state_sync', echecsSnapshot(eroom));
  });

  socket.on('echecs_result', (data) => {
    if (!data || !validRoom(data.room)) return;
    // Résultat d'affichage uniquement : seul le moteur autoritatif du serveur
    // peut terminer un match d'échecs (mat, pat, nulle, temps, abandon).
  });

  // ══════════════════════════════════════════════════════
  //  TTT MULTIJOUEUR
  // ══════════════════════════════════════════════════════
  socket.on('ttt_join', async ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
    const databaseCheck = await verifyDatabaseGameForJoin(socket, gameId, 'tictactoe', player, bet, room);
    if (!databaseCheck.ok) return rejectSocket(socket, databaseCheck.message);
    let troom = tttRooms.get(room);
    if (!troom) {
      troom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: tttState(), turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null, totalManches: TTT_TOTAL_ROUNDS };
      tttRooms.set(room, troom);
    }
    troom.totalManches = TTT_TOTAL_ROUNDS;
    if (!bindDatabaseGame(troom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, troom, room, player, supabaseId, name)) return;
    if (bet && !troom.betAmount) troom.betAmount = bet;
    persistRoomSoon('tictactoe', troom);

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
              finishBothDisconnected(troom, 'tictactoe', room);
            } else { const ws = p1b ? 1 : 2; troom.status = 'playing'; notifyTTTRoomOver(troom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }
      socket.to(room).emit('ttt_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (troom.players[2]?.name || 'Adversaire') : (troom.players[1]?.name || 'Adversaire');
      socket.emit('ttt_start', { room, yourSlot: player, opponentName, bet: troom.betAmount, currency: troom.currency, reconnected: true, paused: troom.status === 'paused', gameState: troom.gameState || null, totalManches: troom.totalManches, revision: troom.gameState?.revision || 0 });
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
      persistRoomSoon('tictactoe', troom);
      const p1 = troom.players[1], p2 = troom.players[2];
      io.to(p1.socketId).emit('ttt_start', { room, yourSlot: 1, opponentName: p2.name, bet: troom.betAmount, currency: troom.currency, reconnected: false, totalManches: troom.totalManches, gameState: troom.gameState, revision: troom.gameState.revision });
      io.to(p2.socketId).emit('ttt_start', { room, yourSlot: 2, opponentName: p1.name, bet: troom.betAmount, currency: troom.currency, reconnected: false, totalManches: troom.totalManches, gameState: troom.gameState, revision: troom.gameState.revision });
      // Start exactly once. The old delayed timeout could fire after player 1's
      // first move and incorrectly put the clock back on player 1.
      startTTTTurnTimer(troom, room, 1);
    }
  });

  socket.on('ttt_move', ({ room, player, row, col, symbol, clientMoveId } = {}) => {
    if (!validRoom(room) || !validPlayerSlot(player) || !Number.isInteger(row) || !Number.isInteger(col) || row < 0 || row > 2 || col < 0 || col > 2) return rejectSocket(socket, 'Coup Tic-Tac-Toe invalide.');
    const troom = tttRooms.get(room), state = troom?.gameState;
    const rejectMove = (message) => {
      socket.emit('game:error', { message, game: 'tictactoe', recoverable: true });
      if (troom && state) socket.emit('ttt_state_sync', tttSnapshot(troom));
    };
    if (!troom || !state) return rejectMove('Partie Tic-Tac-Toe introuvable.');
    if (troom.status !== 'playing' || state.resolvingRound || troom.players[player]?.socketId !== socket.id) return rejectMove('Ce coup ne peut pas être joué maintenant.');
    const expectedSymbol = player === 1 ? 'X' : 'O', index = row * 3 + col;
    if (state.currentPlayer !== player - 1 || symbol !== expectedSymbol || state.board[index] !== null) return rejectMove('Coup Tic-Tac-Toe invalide.');
    clearTTTTurnTimers(troom);
    state.board[index] = expectedSymbol;
    const line = tttWinningLine(state.board, expectedSymbol);
    const draw = !line && state.board.every(Boolean);
    state.currentPlayer = player === 1 ? 1 : 0;
    state.revision = Math.max(0, Number(state.revision) || 0) + 1;
    io.to(room).emit('ttt_move', { room, player, row, col, symbol: expectedSymbol, boardState: JSON.stringify(state.board), nextPlayer: state.currentPlayer, revision: state.revision, clientMoveId: typeof clientMoveId === 'string' ? clientMoveId.slice(0, 80) : null });
    persistRoomSoon('tictactoe', troom);
    if (line || draw) return finishTTTRound(troom, room, line ? player : 0, line);
    startTTTTurnTimer(troom, room, state.currentPlayer + 1);
  });

  socket.on('ttt_request_state', ({ room } = {}) => {
    if (!validRoom(room) || !socketAllow(socket.id, 'tttsync', 20, 10000)) return;
    const troom = tttRooms.get(room);
    if (!troom || !socketIsPlayer(troom, socket.id)) return;
    socket.emit('ttt_state_sync', tttSnapshot(troom));
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
  socket.on('quoridor_join', async ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
    const databaseCheck = await verifyDatabaseGameForJoin(socket, gameId, 'quoridor', player, bet, room);
    if (!databaseCheck.ok) return rejectSocket(socket, databaseCheck.message);
    let qroom = quoriRooms.get(room);
    if (!qroom) {
      qroom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: quoriInitialState(), currentSlot: 1, stateVersion: 0, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null };
      quoriRooms.set(room, qroom);
    }
    if (!bindDatabaseGame(qroom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, qroom, room, player, supabaseId, name)) return;
    if (bet && !qroom.betAmount) qroom.betAmount = bet;
    persistRoomSoon('quoridor', qroom);

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
              finishBothDisconnected(qroom, 'quoridor', room);
            } else { const ws = p1b ? 1 : 2; qroom.status = 'playing'; notifyQuoriRoomOver(qroom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }
      socket.to(room).emit('quoridor_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (qroom.players[2]?.name || 'Adversaire') : (qroom.players[1]?.name || 'Adversaire');
      socket.emit('quoridor_start', { room, yourSlot: player, opponentName, bet: qroom.betAmount, currency: qroom.currency, reconnected: true, paused: qroom.status === 'paused', gameState: qroom.gameState || null, stateVersion: qroom.stateVersion || 0, currentSlot: qroom.currentSlot, turnPlayer: qroom.turnPlayer, turnStartTime: qroom.turnStartTime, graceStartTime: qroom.graceStartTime });
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
      persistRoomSoon('quoridor', qroom);
      const p1 = qroom.players[1], p2 = qroom.players[2];
      io.to(p1.socketId).emit('quoridor_start', { room, yourSlot: 1, opponentName: p2.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });
      io.to(p2.socketId).emit('quoridor_start', { room, yourSlot: 2, opponentName: p1.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });
      const initialVersion = qroom.stateVersion;
      setTimeout(() => {
        if (qroom.status === 'playing' && qroom.stateVersion === initialVersion && !qroom.turnStartTime) {
          startQuoriTurnTimer(qroom, room, 1);
        }
      }, 3000);
    }
  });

  socket.on('quoridor_move', ({ room, player, moveType, data }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const qroom = quoriRooms.get(room), state = qroom?.gameState;
    if (!qroom || !state || qroom.status !== 'playing' || qroom.players[player]?.socketId !== socket.id) return;
    const rejectMove = message => {
      rejectSocket(socket, message);
      socket.emit('quoridor_state_sync', quoriSnapshot(qroom));
    };
    if (qroom.currentSlot !== player) return rejectMove('Ce n’est pas votre tour.');
    const ownPos = player === 1 ? state.s1Pos : state.s2Pos, otherPos = player === 1 ? state.s2Pos : state.s1Pos;
    if (!data || !Number.isInteger(data.r) || !Number.isInteger(data.c)) return rejectMove('Coup Quoridor invalide.');
    if (moveType === 'move') {
      const legal = quoriMoves(state, ownPos, otherPos).some(move => move.r === data.r && move.c === data.c);
      if (!legal) return rejectMove('Déplacement Quoridor invalide.');
      if (player === 1) state.s1Pos = { r: data.r, c: data.c }; else state.s2Pos = { r: data.r, c: data.c };
    } else if (moveType === 'wallH' || moveType === 'wallV') {
      const walls = player === 1 ? state.s1Walls : state.s2Walls;
      if (walls <= 0 || !quoriCanPlaceWall(state, moveType, data.r, data.c)) return rejectMove('Mur Quoridor invalide.');
      (moveType === 'wallH' ? state.hW : state.vW)[data.r][data.c] = true;
      if (player === 1) state.s1Walls--; else state.s2Walls--;
    } else return rejectMove('Action Quoridor invalide.');
    const winnerSlot = (player === 1 && state.s1Pos.r === 0) || (player === 2 && state.s2Pos.r === 8) ? player : 0;
    qroom.currentSlot = player === 1 ? 2 : 1;
    state.currentSlot = qroom.currentSlot;
    qroom.stateVersion = Math.max(0, Number(qroom.stateVersion) || 0) + 1;
    io.to(room).emit('quoridor_move', { room, player, moveType, data: { r: data.r, c: data.c }, gameState: JSON.stringify(state), version: qroom.stateVersion, nextPlayer: qroom.currentSlot - 1 });
    persistRoomSoon('quoridor', qroom);
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
  socket.on('penalty_join', async ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) { socket.emit('penalty_error', { message: 'room_or_player_invalid', detail: 'Room ou joueur invalide.' }); return; }
    const databaseCheck = await verifyDatabaseGameForJoin(socket, gameId, 'penalty', player, bet, room);
    if (!databaseCheck.ok) return rejectSocket(socket, databaseCheck.message);
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
    persistRoomSoon('penalty', proom);

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
              finishBothDisconnected(proom, 'penalty', room);
            } else {
              const ws = p1b ? 1 : 2; proom.status = 'playing'; notifyPenaltyRoomOver(proom, room, ws, 'forfeit');
            }
          }, 60000);
        }
      }

      socket.to(room).emit('penalty_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (proom.players[2]?.name || 'Adversaire') : (proom.players[1]?.name || 'Adversaire');
      socket.emit('penalty_start', { room, yourSlot: player, opponentName, bet: proom.betAmount, currency: proom.currency, reconnected: true, paused: proom.status === 'paused', gameState: { round: proom.currentRound, scores: proom.scores, phase: 'choosing', yourChoice: proom.choices[player] ?? null, opponentHasChosen: proom.choices[player === 1 ? 2 : 1] !== undefined } });
      
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
      persistRoomSoon('penalty', proom);
      const p1 = proom.players[1], p2 = proom.players[2];
      io.to(p1.socketId).emit('penalty_start', { room, yourSlot: 1, opponentName: p2.name, bet: proom.betAmount, currency: proom.currency, reconnected: false });
      io.to(p2.socketId).emit('penalty_start', { room, yourSlot: 2, opponentName: p1.name, bet: proom.betAmount, currency: proom.currency, reconnected: false });
      const initialRound = proom.currentRound;
      setTimeout(() => {
        if (proom.status === 'playing' && proom.currentRound === initialRound && !proom.turnStartTime) {
          startPenaltyTurnTimer(proom, room);
        }
      }, 2800);
    }
  });

  socket.on('penalty_choice', ({ room, player, round, zone }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const proom = penaltyRooms.get(room);
    if (!proom || proom.status !== 'playing' || proom.currentRound !== round || proom.players[player]?.socketId !== socket.id) return;
    if (!Number.isInteger(zone) || zone < 0 || zone > 8 || proom.choices[player] !== undefined) return;
    proom.choices[player] = zone;
    persistRoomSoon('penalty', proom);
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
  socket.on('chifoumi_join', async ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur invalide.');
    const databaseCheck = await verifyDatabaseGameForJoin(socket, gameId, 'chifoumi', player, bet, room);
    if (!databaseCheck.ok) return rejectSocket(socket, databaseCheck.message);
    let croom = chifoumiRooms.get(room);
    if (!croom) {
      croom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, currentRound: 1, scores: [0, 0], choices: {}, history: [], turnTimer: null, graceTimer: null, revealTimer: null, nextRoundTimer: null, awaitingNextRound: false, revealPending: false, revealStartTime: null, turnStartTime: null, graceStartTime: null };
      chifoumiRooms.set(room, croom);
    }
    if (!bindDatabaseGame(croom, gameId)) return rejectSocket(socket, 'Cette room est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, croom, room, player, supabaseId, name)) return;
    if (bet && !croom.betAmount) croom.betAmount = bet;
    persistRoomSoon('chifoumi', croom);

    if (croom.status === 'playing' || croom.status === 'paused') {
      const p1 = croom.players[1], p2 = croom.players[2];
      const bothBack = p1?.connected && p2?.connected;
      if (bothBack && croom.disconnectTimer) {
        clearTimeout(croom.disconnectTimer); croom.disconnectTimer = null; croom.reconnectDeadline = null; croom.status = 'playing';
        if (croom.awaitingNextRound === true) scheduleNextChifoumiRound(croom, room);
        else if (croom.choices[1] !== undefined && croom.choices[2] !== undefined) scheduleChifoumiReveal(croom, room);
        else startChifoumiTurnTimer(croom, room);
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
              finishBothDisconnected(croom, 'chifoumi', room);
            } else { const ws = p1b ? 1 : 2; croom.status = 'playing'; notifyChifoumiRoomOver(croom, room, ws, 'forfeit'); }
          }, 60000);
        }
      }
      socket.to(room).emit('chifoumi_player_status', { slot: player, connected: true, name });
      socket.to(room).emit('player:reconnected', { message: `${name} est de retour !` });
      const opponentName = player === 1 ? (croom.players[2]?.name || 'Adversaire') : (croom.players[1]?.name || 'Adversaire');
      socket.emit('chifoumi_start', {
        room, yourSlot: player, opponentName, bet: croom.betAmount,
        currency: croom.currency, reconnected: true, paused: croom.status === 'paused',
        gameState: {
          scores: croom.scores,
          currentRound: croom.currentRound,
          history: croom.history,
          currentChoice: croom.choices[player] ?? null,
          opponentHasChosen: croom.choices[player === 1 ? 2 : 1] !== undefined,
          revealPending: croom.revealPending === true,
          awaitingNextRound: croom.awaitingNextRound === true
        }
      });
      
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
      persistRoomSoon('chifoumi', croom);
      io.to(p1.socketId).emit('chifoumi_start', { room, yourSlot: 1, opponentName: p2.name, bet: croom.betAmount, currency: croom.currency, reconnected: false });
      io.to(p2.socketId).emit('chifoumi_start', { room, yourSlot: 2, opponentName: p1.name, bet: croom.betAmount, currency: croom.currency, reconnected: false });
      const initialRound = croom.currentRound;
      setTimeout(() => {
        if (croom.status === 'playing' && croom.currentRound === initialRound &&
            !croom.revealPending && !croom.awaitingNextRound && !croom.turnStartTime) {
          startChifoumiTurnTimer(croom, room);
        }
      }, 3000);
    }
  });

  socket.on('chifoumi_choice', ({ room, player, choice }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return;
    const croom = chifoumiRooms.get(room);
    if (!croom || croom.status !== 'playing' || croom.revealPending || croom.players[player]?.socketId !== socket.id) return;
    if (!['pierre', 'feuille', 'ciseaux'].includes(choice) || croom.choices[player] !== undefined) return;
    croom.choices[player] = choice;
    persistRoomSoon('chifoumi', croom);
    socket.to(room).emit('chifoumi_opponent_choice', { player });
    
    // Si les deux ont joué, on n'attend plus la période de grâce
    if (croom.choices[1] !== undefined && croom.choices[2] !== undefined) {
        scheduleChifoumiReveal(croom, room);
    }
  });

  socket.on('chifoumi_round_start', ({ room, player, round }) => {
    const croom = chifoumiRooms.get(room);
    if (!croom || !validPlayerSlot(player) || croom.players[player]?.socketId !== socket.id) return;
    advanceChifoumiRound(croom, room, round);
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

  socket.on('quoridor_request_state', ({ room }) => {
    if (!validRoom(room)) return;
    const qroom = quoriRooms.get(room);
    if (!qroom || !socketIsPlayer(qroom, socket.id)) return;
    socket.emit('quoridor_state_sync', quoriSnapshot(qroom));
  });

  // LUDO MULTIJOUEUR - état et règles autoritatifs côté serveur.
  socket.on('ludo_join', async ({ room, player, supabaseId, name, bet, currency, gameId }) => {
    if (!validRoom(room) || !validPlayerSlot(player)) return rejectSocket(socket, 'Room ou joueur Ludo invalide.');
    if (isUuid(gameId) && room !== gameId) return rejectSocket(socket, 'La room Ludo ne correspond pas à cette partie.');
    const databaseCheck = await verifyDatabaseGameForJoin(socket, gameId, 'ludo', player, bet, room);
    if (!databaseCheck.ok) return rejectSocket(socket, databaseCheck.message);
    let lroom = ludoRooms.get(room);
    if (!lroom) {
      lroom = {
        id: room, players: {}, status: 'waiting',
        betAmount: Number(bet) || 0, currency: currency || 'HTG',
        gameState: createLudoState(), disconnectTimer: null,
        turnTimer: null, graceTimer: null,
        turnStartTime: null, graceStartTime: null
      };
      ludoRooms.set(room, lroom);
    }
    ensureLudoState(lroom);
    if (!bindDatabaseGame(lroom, gameId)) return rejectSocket(socket, 'Cette room Ludo est déjà liée à une autre partie.');
    if (!joinRoomAsAuthenticatedPlayer(socket, lroom, room, player, supabaseId, name)) return;
    if (bet && !lroom.betAmount) lroom.betAmount = Number(bet) || 0;
    persistRoomSoon('ludo', lroom);
    socket.emit('ludo_joined', { room, player, waitingForOpponent: !(lroom.players[1] && lroom.players[2]) });

    if (lroom.status === 'playing' || lroom.status === 'paused') {
      const bothBack = lroom.players[1]?.connected && lroom.players[2]?.connected;
      if (bothBack && lroom.disconnectTimer) {
        clearTimeout(lroom.disconnectTimer);
        lroom.disconnectTimer = null;
        lroom.reconnectDeadline = null;
        lroom.status = 'playing';
        io.to(room).emit('ludo_game_resumed', { message: 'Les deux joueurs sont de retour.' });
        emitLudoState(lroom, room, { type: 'resume' });
        startLudoTurnTimer(lroom, room);
      } else if (lroom.disconnectTimer) {
        setTimeout(() => socket.emit('game:reconnect_deadline', {
          game: 'ludo', serverTime: Date.now(), reconnectDeadline: lroom.reconnectDeadline
        }), 0);
      }
      const opponentName = player === 1 ? (lroom.players[2]?.name || 'Adversaire') : (lroom.players[1]?.name || 'Adversaire');
      socket.to(room).emit('ludo_player_status', { slot: player, connected: true, name: safeName(name) });
      socket.emit('ludo_start', {
        room, yourSlot: player, opponentName,
        bet: lroom.betAmount, currency: lroom.currency,
        reconnected: true, paused: lroom.status === 'paused',
        state: ludoPublicState(lroom),
        rules: { exitOnSix: true, extraTurnOnSix: true, extraTurnOnCapture: true, tripleSixLosesTurn: true, exactFinish: true }
      });
      return;
    }

    if (lroom.players[1] && lroom.players[2] && lroom.status === 'waiting') {
      lroom.status = 'playing';
      lroom.startedAt = Date.now();
      persistRoomSoon('ludo', lroom);
      const p1 = lroom.players[1], p2 = lroom.players[2];
      const common = {
        room, bet: lroom.betAmount, currency: lroom.currency, reconnected: false,
        state: ludoPublicState(lroom),
        rules: { exitOnSix: true, extraTurnOnSix: true, extraTurnOnCapture: true, tripleSixLosesTurn: true, exactFinish: true }
      };
      io.to(p1.socketId).emit('ludo_start', { ...common, yourSlot: 1, opponentName: p2.name });
      io.to(p2.socketId).emit('ludo_start', { ...common, yourSlot: 2, opponentName: p1.name });
      emitLudoState(lroom, room, { type: 'start' });
      const timer = setTimeout(() => {
        if (lroom.status === 'playing' && !lroom.turnStartTime && !lroom.graceStartTime) {
          startLudoTurnTimer(lroom, room);
        }
      }, 1200);
      if (timer.unref) timer.unref();
    }
  });

  socket.on('ludo_get_state', ({ room } = {}) => {
    if (!validRoom(room) || !socketAllow(socket.id, 'ludo-sync', 20, 10000)) return;
    const lroom = ludoRooms.get(room);
    if (!lroom || !socketIsPlayer(lroom, socket.id)) return;
    socket.emit('ludo_state', { room, state: ludoPublicState(lroom), action: { type: 'sync' } });
  });

  socket.on('ludo_roll', ({ room, player } = {}) => {
    if (!validRoom(room) || !validPlayerSlot(player) || !socketAllow(socket.id, 'ludo-roll', 8, 5000)) return;
    const lroom = ludoRooms.get(room);
    if (!lroom || lroom.status !== 'playing' || lroom.players[player]?.socketId !== socket.id) return;
    const state = ensureLudoState(lroom);
    if (state.currentPlayer !== player || state.phase !== 'roll' || state.dice !== null) {
      return rejectSocket(socket, 'Ce lancer de dé Ludo est invalide.');
    }
    const dice = crypto.randomInt(1, 7);
    state.dice = dice;
    state.consecutiveSixes[player] = dice === 6 ? Number(state.consecutiveSixes[player] || 0) + 1 : 0;
    state.revision = Number(state.revision || 0) + 1;

    if (state.consecutiveSixes[player] >= 3) {
      clearLudoTurnTimers(lroom);
      state.consecutiveSixes[player] = 0;
      state.phase = 'locked';
      state.legalMoves = [];
      persistRoomSoon('ludo', lroom);
      emitLudoState(lroom, room, { type: 'triple_six', player, dice });
      const timer = setTimeout(() => {
        if (lroom.status === 'playing' && state.currentPlayer === player && state.phase === 'locked') {
          beginNextLudoTurn(lroom, room, false, { type: 'turn_passed', reason: 'triple_six' });
        }
      }, 900);
      if (timer.unref) timer.unref();
      return;
    }

    state.legalMoves = legalLudoMoves(lroom, player, dice);
    state.phase = state.legalMoves.length ? 'move' : 'locked';
    persistRoomSoon('ludo', lroom);
    emitLudoState(lroom, room, { type: 'roll', player, dice });
    if (!state.legalMoves.length) {
      clearLudoTurnTimers(lroom);
      const timer = setTimeout(() => {
        if (lroom.status === 'playing' && state.currentPlayer === player && state.phase === 'locked') {
          beginNextLudoTurn(lroom, room, dice === 6, { type: 'no_legal_move', player, dice });
        }
      }, 900);
      if (timer.unref) timer.unref();
    }
  });

  socket.on('ludo_move', ({ room, player, tokenIndex } = {}) => {
    if (!validRoom(room) || !validPlayerSlot(player) || !Number.isInteger(tokenIndex) || tokenIndex < 0 || tokenIndex > 3) return;
    if (!socketAllow(socket.id, 'ludo-move', 12, 5000)) return;
    const lroom = ludoRooms.get(room);
    if (!lroom || lroom.status !== 'playing' || lroom.players[player]?.socketId !== socket.id) return;
    const state = ensureLudoState(lroom);
    if (state.currentPlayer !== player || state.phase !== 'move') return rejectSocket(socket, 'Ce mouvement Ludo est invalide.');
    const move = applyLudoMove(lroom, player, tokenIndex);
    if (!move) return rejectSocket(socket, 'Ce pion ne peut pas avancer avec ce dé.');
    clearLudoTurnTimers(lroom);
    state.phase = 'locked';
    state.legalMoves = [];
    state.revision = Number(state.revision || 0) + 1;
    persistRoomSoon('ludo', lroom);
    emitLudoState(lroom, room, { type: 'move', ...move });
    if (state.tokens[player].every(progress => progress === LUDO_FINISH)) {
      const timer = setTimeout(() => {
        if (lroom.status === 'playing') notifyLudoRoomOver(lroom, room, player, 'normal');
      }, 650);
      if (timer.unref) timer.unref();
      return;
    }
    const extraTurn = move.dice === 6 || move.captured.length > 0 || move.finished;
    if (move.dice !== 6) state.consecutiveSixes[player] = 0;
    const timer = setTimeout(() => {
      if (lroom.status === 'playing' && state.currentPlayer === player && state.phase === 'locked') {
        beginNextLudoTurn(lroom, room, extraTurn, { type: extraTurn ? 'extra_turn' : 'next_turn', player });
      }
    }, 650);
    if (timer.unref) timer.unref();
  });

  socket.on('ludo_result', () => {
    // Intentionnellement ignoré : seul le moteur serveur termine la partie.
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
      chifoumi: [chifoumiRooms, notifyChifoumiRoomOver],
      echecs: [echecsRooms, notifyEchecsRoomOver],
      ludo: [ludoRooms, notifyLudoRoomOver]
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
  // In-game voluntary resignation. The authenticated socket identity decides
  // the loser; client-supplied slot/winner fields are deliberately ignored.
  socket.on('game_resign', async ({ room } = {}, acknowledge) => {
    const reply = typeof acknowledge === 'function' ? acknowledge : () => {};
    if (!validRoom(room) || !socketAllow(socket.id, 'resign', 5, 60000)) {
      return reply({ ok: false, error: 'Demande de forfait invalide.' });
    }
    const user = authenticatedSocketUser(socket);
    if (!user?.supabaseId) return reply({ ok: false, error: 'Authentification requise.' });
    const entry = findAuthoritativeRoom(room);
    try {
      if (entry) await hydrateRoomParticipantsFromDatabase(entry);
    } catch (error) {
      console.error('[game_resign] participant recovery failed', error?.message || error);
    }
    const result = resignAuthoritativeRoom(entry, user.supabaseId);
    if (!result.ok) return reply({ ok: false, error: result.error });
    reply({
      ok: true,
      status: result.alreadyFinished ? 'already_finished' : 'resigned',
      settlementPending: result.settlementPending
    });
  });

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
    if (socket.authDeadline) { clearTimeout(socket.authDeadline); socket.authDeadline = null; }
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
      clearChifoumiTurnTimers(croom);
      pauseAndWatch({
        room: croom, roomId, gameName: 'chifoumi',
        getP1: () => croom.players[1], getP2: () => croom.players[2],
        winFn: (winnerIsP1) => notifyChifoumiRoomOver(croom, roomId, winnerIsP1 ? 1 : 2, 'forfeit'),
        onResume: () => {
          if (croom.awaitingNextRound === true) scheduleNextChifoumiRound(croom, roomId);
          else if (croom.choices[1] !== undefined && croom.choices[2] !== undefined) scheduleChifoumiReveal(croom, roomId);
          else startChifoumiTurnTimer(croom, roomId);
        }
      });
      break;
    }

    // Échecs Multijoueur
    for (const [roomId, eroom] of echecsRooms.entries()) {
      if (eroom.status !== 'playing' && eroom.status !== 'paused') continue;
      let disconnectedSlot = null;
      for (const [slot, p] of Object.entries(eroom.players)) { if (p.socketId === socket.id) { disconnectedSlot = parseInt(slot); break; } }
      if (disconnectedSlot === null) continue;
      eroom.players[disconnectedSlot].connected = false;
      const dcName = eroom.players[disconnectedSlot]?.name || `Joueur ${disconnectedSlot}`;
      socket.to(roomId).emit('echecs_player_status', { slot: disconnectedSlot, connected: false, name: dcName });
      socket.to(roomId).emit('echecs_opponent_disconnected', { slot: disconnectedSlot, message: `${dcName} s'est déconnecté.` });
      eroom.pausedTurnPlayer = eroom.turnPlayer || (eroom.currentPlayer + 1) || 1;
      clearEchecsTurnTimers(eroom);
      pauseAndWatch({ room: eroom, roomId, gameName: 'echecs', getP1: () => eroom.players[1], getP2: () => eroom.players[2], winFn: (winnerIsP1) => notifyEchecsRoomOver(eroom, roomId, winnerIsP1 ? 1 : 2, 'forfeit'), onResume: () => startEchecsTurnTimer(eroom, roomId, eroom.pausedTurnPlayer || 1) });
      break;
    }

    // Ludo Multijoueur
    for (const [roomId, lroom] of ludoRooms.entries()) {
      if (lroom.status !== 'playing' && lroom.status !== 'paused') continue;
      let disconnectedSlot = null;
      for (const [slot, player] of Object.entries(lroom.players)) {
        if (player.socketId === socket.id) { disconnectedSlot = Number(slot); break; }
      }
      if (!disconnectedSlot) continue;
      lroom.players[disconnectedSlot].connected = false;
      clearLudoTurnTimers(lroom);
      const disconnectedName = lroom.players[disconnectedSlot]?.name || `Joueur ${disconnectedSlot}`;
      socket.to(roomId).emit('ludo_player_status', { slot: disconnectedSlot, connected: false, name: disconnectedName });
      socket.to(roomId).emit('ludo_opponent_disconnected', { slot: disconnectedSlot, message: `${disconnectedName} s'est déconnecté.` });
      pauseAndWatch({
        room: lroom,
        roomId,
        gameName: 'ludo',
        getP1: () => lroom.players[1],
        getP2: () => lroom.players[2],
        winFn: winnerIsP1 => notifyLudoRoomOver(lroom, roomId, winnerIsP1 ? 1 : 2, 'forfeit'),
        onResume: () => startLudoTurnTimer(lroom, roomId)
      });
      break;
    }
  });
});

async function startServer() {
  await restorePersistedRooms();
  server.listen(PORT, '0.0.0.0', () => {
    console.log(`✅ Serveur Nano Banana v5.6 démarré sur le port ${PORT}`);
  });
}

startServer().catch(error => {
  console.error('[startup] fatal error', error.message);
  process.exit(1);
});

