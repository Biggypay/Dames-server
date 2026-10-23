'use strict';

// La nulle aux dames, sur le VRAI serveur : 25 coups de dames de chaque côté
// (50 en tout) sans prise ni pion qui bouge. Le plateau l'annonçait seul,
// chacun avec son propre compte, pendant que le serveur continuait la partie
// — qui finissait plus tard au temps, contre l'un des deux. C'est maintenant le
// serveur qui la prononce, pour les deux joueurs à la fois.
//
// La position est injectée par la reprise après redémarrage : une dame
// blanche et une dame noire qui vont et viennent sans jamais pouvoir se prendre.

const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const crypto = require('crypto');
const { io } = require('socket.io-client');

const ROOT = path.join(__dirname, '..');
const GAME_PORT = 3242;
const DB_PORT = 3243;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const RECONNECT_MS = 1200;

const GAMES = {
  dames:     { dbType: 'checkers',            join: 'dames_join' },
  echecs:    { dbType: 'chess',               join: 'echecs_join' },
  tictactoe: { dbType: 'tictactoe',           join: 'ttt_join' },
  quoridor:  { dbType: 'quoridor',            join: 'quoridor_join' },
  gomoku:    { dbType: 'gomoku',              join: 'gomoku_join' },
  penalty:   { dbType: 'penalty_shootout',    join: 'penalty_join' },
  chifoumi:  { dbType: 'rock_paper_scissors', join: 'chifoumi_join' },
  ludo:      { dbType: 'ludo',                join: 'ludo_join' }
};

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : JSON.stringify(detail)); }
}
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));

// ── Base de données simulée : parties, sauvegardes des rooms, pause de tournoi ──
const games = new Map();
const savedRooms = new Map();
const tournamentPause = { gameIds: new Set(), paused: false, revision: 0 };
function mockDatabase() {
  return http.createServer((request, response) => {
    let body = '';
    request.on('data', chunk => { body += chunk; });
    request.on('end', () => {
      const url = new URL(request.url, `http://127.0.0.1:${DB_PORT}`);
      response.setHeader('Content-Type', 'application/json');
      if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
        const row = games.get(String(url.searchParams.get('id') || '').replace(/^eq\./, ''));
        return response.end(JSON.stringify(row ? [row] : []));
      }
      if (url.pathname.endsWith('/save_game_server_room_states')) {
        for (const room of JSON.parse(body || '{}').p_rooms || []) savedRooms.set(room.room_id, { ...room, db_status: 'in_progress' });
        return response.end('null');
      }
      if (url.pathname.endsWith('/load_game_server_room_states')) {
        return response.end(JSON.stringify([...savedRooms.values()].filter(room => room.status !== 'finished')));
      }
      if (url.pathname.endsWith('/server_tournament_game_controls')) {
        const ids = JSON.parse(body || '{}').p_game_ids || [];
        return response.end(JSON.stringify(ids.filter(id => tournamentPause.gameIds.has(id)).map(game_id => ({
          game_id, is_paused: tournamentPause.paused, pause_revision: tournamentPause.revision
        }))));
      }
      if (url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
      response.statusCode = 404;
      response.end('{}');
    });
  });
}

// ── Serveur de jeu ──
let serverLog = '';
function startServer() {
  const server = spawn(process.execPath, ['server.js'], {
    cwd: ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT), NODE_ENV: 'test',
      JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      SUPABASE_URL: `http://127.0.0.1:${DB_PORT}`,
      SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app',
      TURN_DURATION_MS: '20000',
      GRACE_DURATION_MS: '20000',
      RECONNECT_DURATION_MS: String(RECONNECT_MS),
      TOURNAMENT_CONTROL_INTERVAL_MS: '2000'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stdout.on('data', chunk => { serverLog += chunk; });
  server.stderr.on('data', chunk => { serverLog += chunk; });
  return server;
}
async function health() {
  for (let i = 0; i < 50; i++) {
    const ok = await new Promise(resolve => {
      http.get(`${GAME_URL}/health`, response => { response.resume(); resolve(response.statusCode === 200); })
        .on('error', () => resolve(false));
    });
    if (ok) return;
    await sleep(200);
  }
  throw new Error('server unavailable');
}
function stopServer(server, signal = 'SIGTERM') {
  return new Promise(resolve => {
    if (server.exitCode !== null) return resolve();
    server.once('exit', resolve);
    server.kill(signal);
  });
}

// ── Joueurs ──
let addressCounter = 0;
const opened = new Set();
async function connectAs(userId, name) {
  addressCounter++;
  const socket = io(GAME_URL, {
    transports: ['websocket'], reconnection: false, forceNew: true,
    extraHeaders: { 'x-forwarded-for': `10.79.${Math.floor(addressCounter / 250)}.${(addressCounter % 250) + 1}` }
  });
  opened.add(socket);
  socket.events = [];
  socket.onAny((event, data) => socket.events.push({ event, data, at: Date.now() }));
  await new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error('timeout connect')), 5000);
    socket.once('connect', () => { clearTimeout(timer); resolve(); });
  });
  socket.emit('auth:supabase', { supabaseId: userId, username: name });
  await waitFor(socket, 'auth:ok', { timeout: 5000 });
  return socket;
}
function waitFor(socket, event, { after = 0, timeout = 6000, where = () => true } = {}) {
  return new Promise((resolve, reject) => {
    const seen = socket.events.find(entry => entry.at >= after && entry.event === event && where(entry.data));
    if (seen) return resolve(seen);
    const listener = (name, data) => {
      if (name !== event || !where(data)) return;
      clearTimeout(timer); socket.offAny(listener);
      resolve({ event, data, at: Date.now() });
    };
    const timer = setTimeout(() => { socket.offAny(listener); reject(new Error(`timeout ${event}`)); }, timeout);
    socket.onAny(listener);
  });
}
const gotEvent = (socket, event, after) => socket.events.some(entry => entry.at >= after && entry.event === event);

function newMatch(gameName) {
  const id = crypto.randomUUID();
  const users = { 1: crypto.randomUUID(), 2: crypto.randomUUID() };
  games.set(id, {
    id, game_type: GAMES[gameName].dbType, player1_id: users[1], player2_id: users[2],
    bet_amount: 0, status: 'in_progress', is_ai_opponent: false, is_tournament: false, game_settings: {}
  });
  return { gameName, id, users, sockets: {} };
}
async function join(match, slot) {
  const socket = await connectAs(match.users[slot], `Joueur ${slot}`);
  socket.emit(GAMES[match.gameName].join, {
    room: match.id, player: slot, supabaseId: match.users[slot], name: `Joueur ${slot}`, bet: 0, currency: 'HTG', gameId: match.id
  });
  match.sockets[slot] = socket;
  return socket;
}

function closeMatch(match) {
  for (const socket of Object.values(match.sockets)) socket.disconnect();
}

const WKING = 3, BKING = 4;
function kingsOnlyRoom(match) {
  const board = Array.from({ length: 10 }, () => Array(10).fill(0));
  board[9][0] = WKING;
  board[0][1] = BKING;
  const players = {};
  for (const slot of [1, 2]) players[slot] = { slot, supabaseId: match.users[slot], name: `Joueur ${slot}`, connected: false, socketId: null, userId: null };
  savedRooms.set(match.id, {
    game_type: 'dames', room_id: match.id, game_id: match.id, status: 'paused', db_status: 'in_progress',
    state: { id: match.id, databaseGameId: match.id, players, status: 'paused', betAmount: 0, currency: 'HTG',
      engineBoard: board, currentPlayer: 0, stateVersion: 0, lastMove: null, startedAt: Date.now() }
  });
}

// Blancs : (9,0) <-> (8,1). Noirs : (0,1) <-> (1,0). Jamais sur une même diagonale.
const WHITE_SQUARES = [{ row: 9, col: 0 }, { row: 8, col: 1 }];
const BLACK_SQUARES = [{ row: 0, col: 1 }, { row: 1, col: 0 }];
async function playQuietMove(match, ply) {
  const slot = ply % 2 === 0 ? 1 : 2;
  const squares = slot === 1 ? WHITE_SQUARES : BLACK_SQUARES;
  const turn = Math.floor(ply / 2);
  const from = squares[turn % 2], to = squares[(turn + 1) % 2];
  const socket = match.sockets[slot];
  const acked = waitFor(socket, 'dames_move_ack', { timeout: 3000, where: data => data.version === ply + 1 });
  socket.emit('dames_move', { room: match.id, player: slot, from, to, steps: [{ from, to }] });
  return acked;
}

async function main() {
  const db = mockDatabase();
  await new Promise(resolve => db.listen(DB_PORT, '127.0.0.1', resolve));
  const match = newMatch('dames');
  kingsOnlyRoom(match);
  const server = startServer();
  try {
    await health();
    await join(match, 1);
    await join(match, 2);
    await waitFor(match.sockets[1], 'dames_game_resumed', { timeout: 5000 });
    for (let ply = 0; ply < 49; ply++) await playQuietMove(match, ply);
    check('49 coups de dames sans prise : la partie continue',
      !gotEvent(match.sockets[1], 'game:over', 0) && !gotEvent(match.sockets[2], 'game:over', 0));
    const startedAt = Date.now();
    await playQuietMove(match, 49);
    const overs = await Promise.all([1, 2].map(slot => waitFor(match.sockets[slot], 'game:over', { after: startedAt, timeout: 3000 }).catch(() => null)));
    for (const slot of [1, 2]) {
      const over = overs[slot - 1];
      check(`au 50e, le serveur prononce la nulle pour le joueur ${slot}`,
        over && over.data.result === 'draw' && over.data.winnerSlot === 0, over ? over.data : 'aucune fin de partie');
    }
  } catch (error) {
    failures++; console.error('  FAIL scénario interrompu :', error.message);
  } finally {
    closeMatch(match);
    for (const socket of opened) socket.disconnect();
    await stopServer(server);
    await new Promise(resolve => db.close(resolve));
  }
  if (/TypeError|ReferenceError|SyntaxError/.test(serverLog)) {
    failures++;
    console.error('  FAIL erreur JavaScript côté serveur :\n' + serverLog.split('\n').filter(line => /Error/.test(line)).slice(0, 10).join('\n'));
  }
  if (failures) {
    console.error(`\n${failures} échec(s)`);
    process.exit(1);
  }
  console.log('\nOK nulle aux dames prononcée par le serveur');
}

main().catch(error => { console.error(error); process.exit(1); });
