'use strict';

// Le délai de reconnexion, sur le VRAI serveur, pour les huit jeux en ligne.
// Le délai est raccourci (1,2 s au lieu de 60 s) et le chronomètre par coup
// allongé (20 s) : seule l'échéance de reconnexion peut finir la partie ici.
//
//  1. après un redémarrage du serveur, si un seul joueur revient, il gagne par
//     forfait à l'échéance. Avant, la room restait en pause pour toujours : le
//     minuteur de reprise ne traitait que le cas « aucun des deux n'est là » ;
//  2. après un redémarrage, si les deux reviennent, la partie continue ;
//  3. un joueur qui part pendant une pause de tournoi a, à la reprise, le
//     délai ordinaire. Avant, aucun délai n'était armé : la partie restait en
//     pause et le tableau du tournoi ne pouvait plus avancer.

const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const crypto = require('crypto');
const { io } = require('socket.io-client');

const ROOT = path.join(__dirname, '..');
const GAME_PORT = 3232;
const DB_PORT = 3233;
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
    extraHeaders: { 'x-forwarded-for': `10.78.${Math.floor(addressCounter / 250)}.${(addressCounter % 250) + 1}` }
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
async function startMatches() {
  const matches = Object.keys(GAMES).map(newMatch);
  for (const match of matches) { await join(match, 1); await join(match, 2); }
  await sleep(3500);                                  // démarrage + sauvegarde des rooms
  return matches;
}

// ── 1 et 2 : redémarrage du serveur ──
async function restartScenarios(server) {
  const alone = await startMatches();
  const together = await startMatches();
  for (const match of [...alone, ...together]) closeMatch(match);
  await stopServer(server, 'SIGKILL');                // arrêt brutal, comme un crash
  for (const match of [...alone, ...together]) {
    check(`${match.gameName} : la partie en cours a été sauvegardée`, savedRooms.has(match.id));
  }

  server = startServer();
  await health();
  await sleep(300);
  const backAt = Date.now();
  for (const match of alone) await join(match, 1);
  for (const match of together) { await join(match, 1); await join(match, 2); }

  await Promise.all(alone.map(async match => {
    const over = await waitFor(match.sockets[1], 'game:over', { after: backAt, timeout: RECONNECT_MS + 4000 }).catch(() => null);
    check(`${match.gameName} : après un redémarrage, celui qui revient seul gagne par forfait`,
      over && over.data.result === 'win' && over.data.reason === 'forfeit' && over.data.winnerSlot === 1,
      over ? over.data : 'aucune fin de partie : la room restait en pause pour toujours');
    check(`${match.gameName} : à l échéance du délai de reconnexion`,
      over && over.at - backAt <= RECONNECT_MS + 1500, over && { afterReturn: over.at - backAt });
  }));
  for (const match of together) {
    check(`${match.gameName} : après un redémarrage, les deux revenus continuent la partie`,
      !gotEvent(match.sockets[1], 'game:over', backAt) && !gotEvent(match.sockets[2], 'game:over', backAt),
      match.sockets[1].events.filter(entry => entry.event === 'game:over'));
  }
  for (const match of [...alone, ...together]) closeMatch(match);
  return server;
}

// ── 3 : départ pendant une pause de tournoi ──
async function tournamentPauseScenario() {
  const matches = await startMatches();
  for (const match of matches) tournamentPause.gameIds.add(match.id);
  tournamentPause.paused = true; tournamentPause.revision++;
  await Promise.all(matches.map(match => waitFor(match.sockets[1], 'tournament:paused', { timeout: 6000 })));
  for (const match of matches) match.sockets[2].disconnect();
  await sleep(RECONNECT_MS + 500);                    // la pause ne fait courir aucun délai
  for (const match of matches) {
    check(`${match.gameName} : pas de forfait pendant la pause du tournoi`, !gotEvent(match.sockets[1], 'game:over', 0));
  }
  tournamentPause.paused = false; tournamentPause.revision++;
  const resumed = await Promise.all(matches.map(match => waitFor(match.sockets[1], 'tournament:resumed', { timeout: 6000 })));
  await Promise.all(matches.map(async (match, index) => {
    const over = await waitFor(match.sockets[1], 'game:over', { after: resumed[index].at, timeout: RECONNECT_MS + 4000 }).catch(() => null);
    check(`${match.gameName} : à la reprise du tournoi, l absent a le délai ordinaire puis perd par forfait`,
      over && over.data.result === 'win' && over.data.reason === 'forfeit',
      over ? over.data : 'aucune fin de partie : la room restait en pause pour toujours');
  }));
  for (const match of matches) closeMatch(match);
}

async function main() {
  const db = mockDatabase();
  await new Promise(resolve => db.listen(DB_PORT, '127.0.0.1', resolve));
  let server = startServer();
  try {
    await health();
    try { await tournamentPauseScenario(); }
    catch (error) { failures++; console.error('  FAIL pause de tournoi :', error.message); }
    try { server = await restartScenarios(server); }
    catch (error) { failures++; console.error('  FAIL redémarrage :', error.message); }
  } finally {
    for (const socket of opened) socket.disconnect();
    if (server) await stopServer(server);
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
  console.log('\nOK délai de reconnexion sur le vrai serveur (8 jeux)');
}

main().catch(error => { console.error(error); process.exit(1); });
