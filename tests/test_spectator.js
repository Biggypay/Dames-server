const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

/** Les pages qui implémentent le protocole spectateur. */
const SPECTATOR_PAGES = [
  'dames_multi.html',
  'echecs_multi.html',
  'quoridor-online.html',
  'ttt_game.html',
];

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3132;
const MOCK_DB_PORT = 3133;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const GAME_ID = '10000000-0000-4000-8000-000000000001';
const PLAYER_1 = '10000000-0000-4000-8000-000000000011';
const PLAYER_2 = '10000000-0000-4000-8000-000000000012';
const SPECTATOR = '10000000-0000-4000-8000-000000000013';
const ROOM = 'spectator-ttt-room';
let failures = 0;

function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else {
    failures++;
    console.error(`  FAIL ${label}`, detail || '');
  }
}

function once(socket, event, timeoutMs = 4000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error(`timeout ${event}`)), timeoutMs);
    socket.once(event, data => {
      clearTimeout(timer);
      resolve(data);
    });
  });
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

async function waitForHealth(retries = 40) {
  for (let attempt = 0; attempt < retries; attempt++) {
    try {
      const ok = await new Promise(resolve => {
        http.get(`${GAME_URL}/health`, response => {
          response.resume();
          resolve(response.statusCode === 200);
        }).on('error', () => resolve(false));
      });
      if (ok) return;
    } catch {}
    await sleep(200);
  }
  throw new Error('game server unavailable');
}

async function connectUser(supabaseId, username) {
  const socket = io(GAME_URL, { transports: ['websocket'], reconnection: false });
  await once(socket, 'connect');
  socket.emit('auth:supabase', { supabaseId, username });
  await once(socket, 'auth:ok');
  return socket;
}

function startMockDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, `http://127.0.0.1:${MOCK_DB_PORT}`);
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
      return response.end(JSON.stringify([{
        id: GAME_ID,
        game_type: 'tictactoe',
        player1_id: PLAYER_1,
        player2_id: PLAYER_2,
        bet_amount: 0,
        status: 'in_progress',
        is_ai_opponent: false
      }]));
    }
    if (request.method === 'POST' && url.pathname.endsWith('/load_game_server_room_states')) {
      return response.end('[]');
    }
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) {
      return response.end('null');
    }
    response.statusCode = 404;
    response.end('{}');
  });
}

async function main() {
  const mockDb = startMockDatabase();
  await new Promise(resolve => mockDb.listen(MOCK_DB_PORT, '127.0.0.1', resolve));
  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT),
      NODE_ENV: 'test',
      JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      SUPABASE_URL: `http://127.0.0.1:${MOCK_DB_PORT}`,
      SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', data => process.stderr.write(String(data)));

  const sockets = [];
  try {
    await waitForHealth();
    const p1 = await connectUser(PLAYER_1, 'Alice');
    const p2 = await connectUser(PLAYER_2, 'Bob');
    const spectator = await connectUser(SPECTATOR, 'Claire');
    sockets.push(p1, p2, spectator);

    // ── Le spectateur arrive AVANT les joueurs ──────────────────────────────
    //
    // C'est le cas normal d'un match de tournoi : la partie est créée par la
    // base de données, alors que la salle de ce serveur n'existe qu'à partir du
    // moment où les deux joueurs ont ouvert leur plateau. Entre les deux, le
    // direct n'est pas mort — il n'a pas commencé.
    //
    // Le serveur doit donc répondre « room_not_live », un refus explicitement
    // temporaire, et non un code que le plateau prendrait pour un adieu. C'est
    // sur cette distinction que repose la relance côté client ; sans elle, le
    // plateau restait noir pour tout le reste du match.
    const tooEarly = once(spectator, 'spectator:error');
    spectator.emit('spectator_join', { gameId: GAME_ID });
    const early = await tooEarly;
    check('spectateur arrivé avant la salle : refus temporaire, pas définitif',
      early.code === 'room_not_live', early);

    const start1 = once(p1, 'ttt_start');
    const start2 = once(p2, 'ttt_start');
    p1.emit('ttt_join', {
      room: ROOM, player: 1, supabaseId: PLAYER_1, name: 'Alice',
      bet: 0, currency: 'HTG', manches: 1, gameId: GAME_ID
    });
    p2.emit('ttt_join', {
      room: ROOM, player: 2, supabaseId: PLAYER_2, name: 'Bob',
      bet: 0, currency: 'HTG', manches: 1, gameId: GAME_ID
    });
    await Promise.all([start1, start2]);

    const joinedPromise = once(spectator, 'spectator:joined');
    const statePromise = once(spectator, 'spectator_state');
    const countPromise = once(spectator, 'spectator_count');
    spectator.emit('spectator_join', { gameId: GAME_ID });
    const [joined, initial, count] = await Promise.all([joinedPromise, statePromise, countPromise]);

    check('spectator joins in read-only mode', joined.readOnly === true && joined.gameType === 'tictactoe', joined);
    check('spectator count is real and excludes players', count.count === 1, count);
    check('initial authoritative state is returned', initial.gameId === GAME_ID && initial.state?.gameState?.board?.length === 9, initial);
    check('snapshot does not expose player identifiers', !JSON.stringify(initial.players).includes(PLAYER_1) && !JSON.stringify(initial.players).includes(PLAYER_2));

    const resyncPromise = once(spectator, 'spectator_state');
    spectator.emit('spectator_request_state', { gameId: GAME_ID });
    const resynced = await resyncPromise;
    check('spectator can safely resync the read-only board', resynced.gameId === GAME_ID && resynced.state?.gameState?.board?.length === 9, resynced);

    spectator.emit('ttt_move', { room: ROOM, player: 1, row: 0, col: 0, symbol: 'X' });
    await sleep(100);
    const unchangedPromise = once(spectator, 'spectator_state');
    spectator.emit('spectator_join', { gameId: GAME_ID });
    const unchanged = await unchangedPromise;
    check('spectator cannot inject a move', unchanged.state.gameState.board[0] === null, unchanged.state.gameState.board);

    const relayedMove = once(spectator, 'ttt_move');
    p1.emit('ttt_move', { room: ROOM, player: 1, row: 0, col: 0, symbol: 'X' });
    const move = await relayedMove;
    check('real player move is streamed to spectator', move.row === 0 && move.col === 0 && move.symbol === 'X', move);

    const anonymous = io(GAME_URL, { transports: ['websocket'], reconnection: false });
    sockets.push(anonymous);
    await once(anonymous, 'connect');
    const denied = once(anonymous, 'spectator:error');
    anonymous.emit('spectator_join', { gameId: GAME_ID });
    const denial = await denied;
    check('anonymous spectator is rejected', denial.code === 'not_authenticated', denial);

    // ── La table de décision embarquée dans les plateaux ─────────────────────
    //
    // Le serveur classe ses refus ; encore faut-il que chaque plateau les lise
    // de la même façon. On extrait la fonction réellement livrée dans chaque
    // page et on vérifie son verdict, code par code.
    //
    // Deux règles à ne pas perdre :
    //   — « room_not_live » se réessaie SANS limite. C'est l'attente d'un match
    //     de tournoi, qui peut durer plusieurs minutes.
    //   — un refus d'identité ne se réessaie JAMAIS : marteler le serveur avec
    //     une session invalide ne fait que remplir son compteur anti-abus.
    for (const page of SPECTATOR_PAGES) {
      const source = fs.readFileSync(path.join(REPO_ROOT, 'public', page), 'utf8');
      const extracted = /function spectatorRetryable\(code\)\{[\s\S]*?\r?\n {2}\}/.exec(source);
      if (!extracted) {
        check(`${page} : table de décision présente`, false, 'fonction introuvable');
        continue;
      }
      const build = new Function(
        'SPECT_RETRY_MAX_TRIES',
        'spectRetryTries',
        `${extracted[0]}; return spectatorRetryable;`,
      );
      const fresh = build(10, 0);
      const exhausted = build(10, 10);

      check(`${page} : attend les joueurs sans limite de temps`,
        fresh('room_not_live') === true && exhausted('room_not_live') === true);
      check(`${page} : accident passager réessayé, puis abandonné`,
        fresh('not_live') === true && exhausted('not_live') === false &&
        fresh('verification_failed') === true && exhausted('verification_failed') === false);
      check(`${page} : un refus d'identité n'est jamais réessayé`,
        fresh('not_authenticated') === false &&
        fresh('invalid_request') === false &&
        fresh('unsupported_game') === false &&
        fresh('') === false);
    }
  } finally {
    for (const socket of sockets) socket.disconnect();
    server.kill('SIGKILL');
    await new Promise(resolve => mockDb.close(resolve));
  }
  process.exit(failures === 0 ? 0 : 1);
}

main().catch(error => {
  console.error(error);
  process.exit(1);
});
