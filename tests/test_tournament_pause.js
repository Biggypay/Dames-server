const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const ROOT = path.join(__dirname, '..');
const GAME_PORT = 3152;
const DB_PORT = 3153;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const GAME_ID = '30000000-0000-4000-8000-000000000001';
const TOURNAMENT_ID = '30000000-0000-4000-8000-000000000002';
const P1 = '30000000-0000-4000-8000-000000000011';
const P2 = '30000000-0000-4000-8000-000000000012';
let paused = false;
let revision = 0;
let failures = 0;

const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail || ''); }
}
function once(socket, event, timeoutMs = 6000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error(`timeout ${event}`)), timeoutMs);
    socket.once(event, data => { clearTimeout(timer); resolve(data); });
  });
}
async function health() {
  for (let i = 0; i < 40; i++) {
    const ok = await new Promise(resolve => {
      http.get(`${GAME_URL}/health`, response => { response.resume(); resolve(response.statusCode === 200); })
        .on('error', () => resolve(false));
    });
    if (ok) return;
    await sleep(200);
  }
  throw new Error('server unavailable');
}
async function connect(id, username) {
  const socket = io(GAME_URL, { transports: ['websocket'], reconnection: false });
  await once(socket, 'connect');
  socket.emit('auth:supabase', { supabaseId: id, username });
  await once(socket, 'auth:ok');
  return socket;
}
function mockDatabase() {
  return http.createServer((request, response) => {
    const requestUrl = new URL(request.url, `http://127.0.0.1:${DB_PORT}`);
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && requestUrl.pathname === '/rest/v1/games') {
      return response.end(JSON.stringify([{
        id: GAME_ID, game_type: 'tictactoe', player1_id: P1, player2_id: P2,
        bet_amount: 0, status: 'in_progress', is_ai_opponent: false,
        is_tournament: true, game_settings: { tournament_paused: paused }
      }]));
    }
    if (request.method === 'POST' && requestUrl.pathname.endsWith('/load_game_server_room_states')) {
      return response.end('[]');
    }
    if (request.method === 'POST' && requestUrl.pathname.endsWith('/server_tournament_game_controls')) {
      return response.end(JSON.stringify([{
        game_id: GAME_ID, tournament_id: TOURNAMENT_ID,
        is_paused: paused, pause_revision: revision
      }]));
    }
    if (request.method === 'POST' && requestUrl.pathname.startsWith('/rest/v1/rpc/')) {
      return response.end('null');
    }
    response.statusCode = 404;
    response.end('{}');
  });
}

async function main() {
  const db = mockDatabase();
  await new Promise(resolve => db.listen(DB_PORT, '127.0.0.1', resolve));
  const server = spawn('node', ['server.js'], {
    cwd: ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT), NODE_ENV: 'test',
      JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      SUPABASE_URL: `http://127.0.0.1:${DB_PORT}`,
      SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app',
      TOURNAMENT_CONTROL_INTERVAL_MS: '2000'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  const sockets = [];
  try {
    await health();
    const p1 = await connect(P1, 'Alice');
    const p2 = await connect(P2, 'Bob');
    sockets.push(p1, p2);
    const start1 = once(p1, 'ttt_start');
    const start2 = once(p2, 'ttt_start');
    p1.emit('ttt_join', { room: GAME_ID, player: 1, supabaseId: P1, name: 'Alice', bet: 0, currency: 'HTG', gameId: GAME_ID });
    p2.emit('ttt_join', { room: GAME_ID, player: 2, supabaseId: P2, name: 'Bob', bet: 0, currency: 'HTG', gameId: GAME_ID });
    await Promise.all([start1, start2]);

    const firstMove = once(p2, 'ttt_move');
    p1.emit('ttt_move', { room: GAME_ID, player: 1, row: 0, col: 0, symbol: 'X' });
    await firstMove;

    paused = true; revision++;
    const pauseNotice = await once(p1, 'tournament:paused');
    check('administrator pause reaches active players', pauseNotice.room === GAME_ID, pauseNotice);

    let movedWhilePaused = false;
    const forbiddenMove = () => { movedWhilePaused = true; };
    p1.once('ttt_move', forbiddenMove);
    p2.emit('ttt_move', { room: GAME_ID, player: 2, row: 1, col: 1, symbol: 'O' });
    await sleep(500);
    p1.off('ttt_move', forbiddenMove);
    check('moves are rejected while the tournament is paused', movedWhilePaused === false);

    paused = false; revision++;
    const resumeNotice = await once(p1, 'tournament:resumed');
    check('resume reaches active players', resumeNotice.waitingForPlayers === false, resumeNotice);
    const resumedMove = once(p1, 'ttt_move');
    p2.emit('ttt_move', { room: GAME_ID, player: 2, row: 1, col: 1, symbol: 'O' });
    const move = await resumedMove;
    check('the same board continues after resume', move.row === 1 && move.col === 1, move);
  } finally {
    for (const socket of sockets) socket.disconnect();
    server.kill('SIGTERM');
    await new Promise(resolve => db.close(resolve));
  }
  if (failures) process.exitCode = 1;
}

main().catch(error => { console.error(error); process.exitCode = 1; });
