'use strict';

// Le chronomètre par coup, joué sur le VRAI serveur, pour les sept jeux en
// ligne. Les durées sont raccourcies (0,5 s de jeu + 1 s de grâce au lieu de
// 30 s + 60 s) : c'est la règle qui est vérifiée, pas l'horloge murale.
//
// Pour chaque jeu :
//  1. celui qui ne joue pas perd par « timeout » à l'échéance, avec l'annonce
//     de la grâce entre les deux ;
//  2. recharger la page pendant la grâce ne rend pas le temps : la défaite
//     tombe à la même échéance, et la page reprise affiche le bon reste ;
//  3. celui qui doit jouer et se déconnecte perd à l'échéance, sans attendre
//     les 60 s du délai de reconnexion ;
//  4. si c'est l'autre qui se déconnecte, le tour est gelé : celui qui doit
//     jouer ne perd pas pendant l'absence, et retrouve le temps qui lui restait.
// Puis, pour le Tic-Tac-Toe et le Morpion à cinq : après un redémarrage du
// serveur, le tour du joueur 2 est bien chronométré (il ne l'était plus du
// tout : le serveur relançait le chronomètre du joueur 1, qui ne jouait pas).

const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const crypto = require('crypto');
const { io } = require('socket.io-client');

const ROOT = path.join(__dirname, '..');
const GAME_PORT = 3212;
const DB_PORT = 3213;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const TURN_MS = 500;
const GRACE_MS = 1000;
const BUDGET_MS = TURN_MS + GRACE_MS;

const GAMES = {
  dames:     { dbType: 'checkers',            join: 'dames_join',    event: 'dames' },
  echecs:    { dbType: 'chess',               join: 'echecs_join',   event: 'echecs' },
  tictactoe: { dbType: 'tictactoe',           join: 'ttt_join',      event: 'ttt' },
  quoridor:  { dbType: 'quoridor',            join: 'quoridor_join', event: 'quoridor' },
  gomoku:    { dbType: 'gomoku',              join: 'gomoku_join',   event: 'gomoku' },
  penalty:   { dbType: 'penalty_shootout',    join: 'penalty_join',  event: 'penalty',  simultaneous: true },
  chifoumi:  { dbType: 'rock_paper_scissors', join: 'chifoumi_join', event: 'chifoumi', simultaneous: true }
};

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : JSON.stringify(detail)); }
}
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));

// ── Base de données simulée : parties, sauvegardes des rooms, résultats ──
const games = new Map();
const savedRooms = new Map();
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
      TURN_DURATION_MS: String(TURN_MS),
      GRACE_DURATION_MS: String(GRACE_MS)
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
// Chaque socket se présente avec sa propre adresse : la limite de connexions
// anonymes par adresse ne doit pas fausser un test qui en ouvre beaucoup.
let addressCounter = 0;
const opened = new Set();
async function connectAs(userId, name) {
  addressCounter++;
  const socket = io(GAME_URL, {
    transports: ['websocket'], reconnection: false, forceNew: true,
    extraHeaders: { 'x-forwarded-for': `10.77.${Math.floor(addressCounter / 250)}.${(addressCounter % 250) + 1}` }
  });
  opened.add(socket);
  socket.events = [];
  socket.onAny((event, data) => socket.events.push({ event, data, at: Date.now() }));
  await waitFor(socket, 'connect', { timeout: 5000 });
  socket.emit('auth:supabase', { supabaseId: userId, username: name });
  await waitFor(socket, 'auth:ok', { timeout: 5000 });
  return socket;
}
function waitFor(socket, event, { after = 0, timeout = 6000, where = () => true } = {}) {
  return new Promise((resolve, reject) => {
    const seen = (socket.events || []).find(entry => entry.at >= after && entry.event === event && where(entry.data));
    if (seen) return resolve(seen);
    const listener = (name, data) => {
      if (name !== event || !where(data)) return;
      clearTimeout(timer); socket.offAny(listener); socket.off(event, direct);
      resolve({ event, data, at: Date.now() });
    };
    // `connect` n'est pas un événement « onAny » : on l'écoute aussi en direct.
    const direct = data => listener(event, data);
    const timer = setTimeout(() => { socket.offAny(listener); socket.off(event, direct); reject(new Error(`timeout ${event}`)); }, timeout);
    socket.onAny(listener);
    if (event === 'connect') socket.once('connect', direct);
  });
}
const gotEvent = (socket, event, after, where = () => true) =>
  socket.events.some(entry => entry.at >= after && entry.event === event && where(entry.data));

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
function choose(match, slot) {
  const socket = match.sockets[slot];
  if (match.gameName === 'penalty') socket.emit('penalty_choice', { room: match.id, player: slot, round: 1, zone: 4 });
  if (match.gameName === 'chifoumi') socket.emit('chifoumi_choice', { room: match.id, player: slot, choice: 'pierre' });
}

/**
 * Lance une partie et attend le premier tour chronométré. Rend le joueur qui
 * doit jouer (`late`) : dans les jeux simultanés, le joueur 1 choisit tout de
 * suite et c'est le joueur 2 qui traîne.
 */
async function startMatch(gameName) {
  const match = newMatch(gameName);
  const event = GAMES[gameName].event;
  await join(match, 1);
  await join(match, 2);
  const start = await waitFor(match.sockets[1], `${event}_turn_start`, { timeout: 8000 });
  let late = start.data.player;
  if (GAMES[gameName].simultaneous) {
    choose(match, 1);
    late = 2;
  }
  return { match, event, start, late, other: late === 1 ? 2 : 1 };
}
function closeMatch(match) {
  for (const socket of Object.values(match.sockets)) socket.disconnect();
}

// ── Les quatre règles ──
async function ruleTimeout(gameName) {
  const { match, event, start, late, other } = await startMatch(gameName);
  try {
    check(`${gameName} : le tour annonce 30 s (ici ${TURN_MS} ms)`, start.data.duration === TURN_MS, start.data);
    const warning = await waitFor(match.sockets[other], `${event}_turn_warning`, { after: start.at });
    const toGrace = warning.at - start.at;
    check(`${gameName} : la grâce est annoncée à la fin des 30 s`, toGrace >= TURN_MS - 100 && toGrace <= TURN_MS + 400, { toGrace });
    check(`${gameName} : la grâce dure 60 s (ici ${GRACE_MS} ms)`, warning.data.duration === GRACE_MS, warning.data);
    const over = await waitFor(match.sockets[late], 'game:over', { after: start.at });
    const elapsed = over.at - start.at;
    check(`${gameName} : sans coup, défaite par timeout à l échéance`, over.data.reason === 'timeout' && over.data.result === 'loss', over.data);
    check(`${gameName} : ni avant, ni longtemps après les 90 s`, elapsed >= BUDGET_MS - 100 && elapsed <= BUDGET_MS + 600, { elapsed });
    const winner = await waitFor(match.sockets[other], 'game:over', { after: start.at });
    check(`${gameName} : l adversaire gagne`, winner.data.result === 'win', winner.data);
  } finally { closeMatch(match); }
}

async function ruleReloadKeepsTime(gameName) {
  const { match, event, start, late, other } = await startMatch(gameName);
  try {
    await sleep(TURN_MS + 400);                       // en pleine grâce
    match.sockets[late].disconnect();
    await sleep(60);
    const back = await join(match, late);             // la page rechargée
    const resumed = await waitFor(back, `${event}_turn_warning`, { after: start.at, timeout: 3000 }).catch(() => null);
    const graceStart = start.data.startTime + TURN_MS;
    check(`${gameName} : après rechargement, la page reprend la grâce entamée`,
      resumed && Math.abs(resumed.data.startTime - graceStart) <= 150, resumed && { startTime: resumed.data.startTime, graceStart });
    const over = await waitFor(match.sockets[other], 'game:over', { after: start.at });
    const elapsed = over.at - start.at;
    check(`${gameName} : recharger ne rend pas le temps — défaite à la même échéance`,
      over.data.reason === 'timeout' && over.data.result === 'win' && elapsed <= BUDGET_MS + 600,
      { elapsed, reason: over.data.reason, before: 'aurait été ' + (TURN_MS + 400 + BUDGET_MS) + ' ms' });
  } finally { closeMatch(match); }
}

async function ruleAbsentPlayerKeepsLosingTime(gameName) {
  const { match, start, late, other } = await startMatch(gameName);
  try {
    await sleep(200);
    match.sockets[late].disconnect();
    const over = await waitFor(match.sockets[other], 'game:over', { after: start.at, timeout: 5000 });
    const elapsed = over.at - start.at;
    check(`${gameName} : absent pendant son tour, il perd par timeout à l échéance`,
      over.data.reason === 'timeout' && over.data.result === 'win', over.data);
    check(`${gameName} : sans attendre les 60 s de reconnexion`, elapsed <= BUDGET_MS + 600, { elapsed });
  } finally { closeMatch(match); }
}

async function ruleOpponentAwayFreezesTurn(gameName) {
  const { match, start, late, other } = await startMatch(gameName);
  try {
    await sleep(200);
    match.sockets[other].disconnect();
    await sleep(BUDGET_MS + 300);                     // bien au-delà de son budget
    check(`${gameName} : l adversaire absent gèle le tour — pas de défaite pendant l absence`,
      !gotEvent(match.sockets[late], 'game:over', start.at), match.sockets[late].events.filter(e => e.event === 'game:over'));
    const back = await join(match, other);
    const backAt = Date.now();
    const over = await waitFor(back, 'game:over', { after: backAt, timeout: 5000 });
    const afterReturn = over.at - backAt;
    check(`${gameName} : au retour, il retrouve le temps qui lui restait`,
      over.data.reason === 'timeout' && over.data.result === 'win'
        && afterReturn >= BUDGET_MS - 200 - 250 && afterReturn <= BUDGET_MS - 200 + 600,
      { afterReturn, reason: over.data.reason });
  } finally { closeMatch(match); }
}

// ── Redémarrage du serveur au milieu du tour du joueur 2 ──
async function playUntilPlayerTwoMoves(match) {
  const socket1 = match.sockets[1], socket2 = match.sockets[2];
  if (match.gameName === 'tictactoe') {
    const started = await waitFor(socket1, 'ttt_start');
    const symbols = started.data.gameState.slotSymbols;
    const opener = Number(started.data.gameState.currentPlayer) + 1;
    const cells = [[0, 0], [1, 1]];
    const order = opener === 1 ? [1] : [2, 1];
    for (const [i, slot] of order.entries()) {
      const moved = waitFor(match.sockets[slot === 1 ? 2 : 1], 'ttt_move', { after: Date.now() });
      match.sockets[slot].emit('ttt_move', { room: match.id, player: slot, row: cells[i][0], col: cells[i][1], symbol: symbols[slot] });
      await moved;
    }
  } else {
    const started = await waitFor(socket1, 'gomoku_start');
    const opener = Number(started.data.currentSlot);
    const cells = [[7, 7], [7, 8]];
    const order = opener === 1 ? [1] : [2, 1];
    for (const [i, slot] of order.entries()) {
      const moved = waitFor(match.sockets[slot === 1 ? 2 : 1], 'gomoku_move', { after: Date.now() });
      match.sockets[slot].emit('gomoku_move', { room: match.id, player: slot, data: { r: cells[i][0], c: cells[i][1] } });
      await moved;
    }
  }
  return waitFor(socket2, `${GAMES[match.gameName].event}_turn_start`, { where: data => data.player === 2 });
}

async function ruleRestartStillTimesPlayerTwo(gameName) {
  let server = startServer();
  await health();
  const match = newMatch(gameName);
  await join(match, 1);
  await join(match, 2);
  await playUntilPlayerTwoMoves(match);
  await sleep(800);                                   // la room est sauvegardée
  closeMatch(match);
  await stopServer(server, 'SIGKILL');                // arrêt brutal, comme un crash
  for (const roomId of [...savedRooms.keys()]) if (roomId !== match.id) savedRooms.delete(roomId);
  check(`${gameName} : la partie en cours a bien été sauvegardée`, savedRooms.has(match.id));

  server = startServer();
  try {
    await health();
    await sleep(300);
    const socket1 = await join(match, 1);
    await sleep(100);
    await join(match, 2);
    const rejoinedAt = Date.now();
    const over = await waitFor(socket1, 'game:over', { after: rejoinedAt, timeout: 5000 }).catch(() => null);
    check(`${gameName} : après un redémarrage, le tour du joueur 2 est chronométré`,
      over && over.data.reason === 'timeout' && over.data.result === 'win' && over.data.winnerSlot === 1,
      over ? over.data : 'aucune fin de partie : le tour n était plus limité');
    check(`${gameName} : et il tombe dans le budget du tour`, over && over.at - rejoinedAt <= BUDGET_MS + 600, over && { afterRejoin: over.at - rejoinedAt });
  } finally {
    closeMatch(match);
    await stopServer(server);
  }
}

async function main() {
  const db = mockDatabase();
  await new Promise(resolve => db.listen(DB_PORT, '127.0.0.1', resolve));
  let server = startServer();
  try {
    await health();
    const names = Object.keys(GAMES);
    const results = await Promise.allSettled(names.flatMap(name => [
      ruleTimeout(name), ruleReloadKeepsTime(name), ruleAbsentPlayerKeepsLosingTime(name), ruleOpponentAwayFreezesTurn(name)
    ]));
    for (const result of results) {
      if (result.status === 'rejected') { failures++; console.error('  FAIL scénario interrompu :', result.reason && result.reason.message); }
    }
    await stopServer(server);
    server = null;

    for (const name of ['tictactoe', 'gomoku']) {
      try { await ruleRestartStillTimesPlayerTwo(name); }
      catch (error) { failures++; console.error(`  FAIL ${name} redémarrage :`, error.message); }
    }
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
  console.log('\nOK chronomètre par coup sur le vrai serveur (7 jeux)');
}

main().catch(error => { console.error(error); process.exit(1); });
