const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3132;
const MOCK_DB_PORT = 3133;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const GAME_ID = '10000000-0000-4000-8000-000000000001';
const CHIFOUMI_GAME_ID = '10000000-0000-4000-8000-000000000002';
const PENALTY_GAME_ID = '10000000-0000-4000-8000-000000000003';
const QUORIDOR_GAME_ID = '10000000-0000-4000-8000-000000000004';
const PLAYER_1 = '10000000-0000-4000-8000-000000000011';
const PLAYER_2 = '10000000-0000-4000-8000-000000000012';
const SPECTATOR = '10000000-0000-4000-8000-000000000013';
// Production clients use games.id as the unique authoritative socket room.
// Keeping this invariant in tests also protects against duplicate boards
// racing to settle the same escrow row.
const ROOM = GAME_ID;
const SPECTATOR_PAGES = [
  'dames_multi.html',
  'ttt_game.html',
  'quoridor-online.html',
  'penalty-online.html',
  'chifoumi-online.html',
  'echecs_multi.html',
];
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
      const requestedId = (url.searchParams.get('id') || '').replace(/^eq\./, '');
      const gameType = requestedId === CHIFOUMI_GAME_ID
        ? 'rock_paper_scissors'
        : requestedId === PENALTY_GAME_ID ? 'penalty_shootout'
        : requestedId === QUORIDOR_GAME_ID ? 'quoridor' : 'tictactoe';
      return response.end(JSON.stringify([{
        id: requestedId || GAME_ID,
        game_type: gameType,
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

    const chifoumiRoom = CHIFOUMI_GAME_ID;
    const chifStart1 = once(p1, 'chifoumi_start');
    const chifStart2 = once(p2, 'chifoumi_start');
    p1.emit('chifoumi_join', { room:chifoumiRoom, player:1, supabaseId:PLAYER_1, name:'Alice', bet:0, currency:'HTG', gameId:CHIFOUMI_GAME_ID });
    p2.emit('chifoumi_join', { room:chifoumiRoom, player:2, supabaseId:PLAYER_2, name:'Bob', bet:0, currency:'HTG', gameId:CHIFOUMI_GAME_ID });
    await Promise.all([chifStart1, chifStart2]);
    const chifJoined = once(spectator, 'spectator:joined');
    const chifState = once(spectator, 'spectator_state');
    spectator.emit('spectator_join', { gameId:CHIFOUMI_GAME_ID });
    await chifJoined;
    const chifInitial = await chifState;
    check('RPS spectator snapshot hides current choices', !('choices' in chifInitial.state) && !JSON.stringify(chifInitial.state).includes('pierre'), chifInitial.state);
    p1.emit('chifoumi_choice', { room:chifoumiRoom, player:1, choice:'pierre' });
    await sleep(50);
    const hiddenAfterChoice = once(spectator, 'spectator_state');
    spectator.emit('spectator_request_state', { gameId:CHIFOUMI_GAME_ID });
    const hiddenSnapshot = await hiddenAfterChoice;
    check('RPS first secret stays private before reveal', !JSON.stringify(hiddenSnapshot.state).includes('pierre'), hiddenSnapshot.state);
    const publicReveal = once(spectator, 'chifoumi_round_result', 7000);
    const automaticNextRound = once(spectator, 'chifoumi_round_ready', 12000);
    p2.emit('chifoumi_choice', { room:chifoumiRoom, player:2, choice:'ciseaux' });
    const revealed = await publicReveal;
    check('RPS reveals both choices only after server resolution', revealed.choice1 === 'pierre' && revealed.choice2 === 'ciseaux' && revealed.winnerSlot === 1, revealed);
    const nextRound = await automaticNextRound;
    check('RPS server advances a round even when clients miss their callback', nextRound.round === 2, nextRound);

    // ── Quoridor : le plateau doit être diffusable comme les autres ──
    // Ce jeu était le seul des six pages du serveur à n'avoir aucun test de
    // diffusion. Un spectateur qui ouvrait un direct de Quoridor restait
    // devant un plateau muet, sans que rien ne le signale.
    const quoriRoom = QUORIDOR_GAME_ID;
    const quoriStart1 = once(p1, 'quoridor_start');
    const quoriStart2 = once(p2, 'quoridor_start');
    p1.emit('quoridor_join', { room:quoriRoom, player:1, supabaseId:PLAYER_1, name:'Alice', bet:0, currency:'HTG', gameId:QUORIDOR_GAME_ID });
    p2.emit('quoridor_join', { room:quoriRoom, player:2, supabaseId:PLAYER_2, name:'Bob', bet:0, currency:'HTG', gameId:QUORIDOR_GAME_ID });
    await Promise.all([quoriStart1, quoriStart2]);

    const quoriJoined = once(spectator, 'spectator:joined');
    const quoriState = once(spectator, 'spectator_state');
    spectator.emit('spectator_join', { gameId:QUORIDOR_GAME_ID });
    const quoriJoinAck = await quoriJoined;
    check('Quoridor spectator is accepted', quoriJoinAck.gameType === 'quoridor' && quoriJoinAck.readOnly === true, quoriJoinAck);
    const quoriInitial = await quoriState;
    const quoriBoard = quoriInitial.state && (typeof quoriInitial.state.gameState === 'string'
      ? JSON.parse(quoriInitial.state.gameState)
      : quoriInitial.state.gameState);
    check('Quoridor spectator receives the real board',
      !!quoriBoard && quoriBoard.s1Pos.r === 8 && quoriBoard.s2Pos.r === 0 && quoriBoard.s1Walls === 10,
      quoriBoard);
    check('Quoridor spectator sees both player names',
      quoriInitial.players && quoriInitial.players[1].name === 'Alice' && quoriInitial.players[2].name === 'Bob',
      quoriInitial.players);

    // Un coup réel doit parvenir au spectateur, sinon le direct est figé.
    const quoriRelay = once(spectator, 'quoridor_move', 5000);
    p1.emit('quoridor_move', { room:quoriRoom, player:1, moveType:'move', data:{ r:7, c:4 } });
    const quoriMove = await quoriRelay;
    check('Quoridor spectator receives live moves', quoriMove.player === 1 && JSON.parse(quoriMove.gameState).s1Pos.r === 7, quoriMove);

    const penaltyRoom = PENALTY_GAME_ID;
    const penaltyStart1 = once(p1, 'penalty_start');
    const penaltyStart2 = once(p2, 'penalty_start');
    p1.emit('penalty_join', { room:penaltyRoom, player:1, supabaseId:PLAYER_1, name:'Alice', bet:0, currency:'HTG', gameId:PENALTY_GAME_ID });
    p2.emit('penalty_join', { room:penaltyRoom, player:2, supabaseId:PLAYER_2, name:'Bob', bet:0, currency:'HTG', gameId:PENALTY_GAME_ID });
    await Promise.all([penaltyStart1, penaltyStart2]);
    const penaltyJoined = once(spectator, 'spectator:joined');
    const penaltyState = once(spectator, 'spectator_state');
    spectator.emit('spectator_join', { gameId:PENALTY_GAME_ID });
    await penaltyJoined;
    const penaltyInitial = await penaltyState;
    check('Penalty spectator snapshot hides shot zones', !('choices' in penaltyInitial.state) && !('p1Zone' in penaltyInitial.state), penaltyInitial.state);
    p1.emit('penalty_choice', { room:penaltyRoom, player:1, round:1, zone:0 });
    await sleep(50);
    const penaltyHiddenState = once(spectator, 'spectator_state');
    spectator.emit('spectator_request_state', { gameId:PENALTY_GAME_ID });
    const penaltyHidden = await penaltyHiddenState;
    check('Penalty first zone stays private before resolution', !('p1Zone' in penaltyHidden.state) && !('choices' in penaltyHidden.state), penaltyHidden.state);
    p1.disconnect();
    await sleep(100);
    const p1PenaltyReconnect = await connectUser(PLAYER_1, 'Alice');
    sockets.push(p1PenaltyReconnect);
    const penaltyReconnectState = once(p1PenaltyReconnect, 'penalty_start');
    p1PenaltyReconnect.emit('penalty_join', { room:penaltyRoom, player:1, supabaseId:PLAYER_1, name:'Alice', bet:0, currency:'HTG', gameId:PENALTY_GAME_ID });
    const restoredPenalty = await penaltyReconnectState;
    check('Penalty reconnect restores the player locked zone', restoredPenalty.reconnected === true && restoredPenalty.gameState?.yourChoice === 0 && restoredPenalty.gameState?.opponentHasChosen === false, restoredPenalty);
    const penaltyReveal = once(spectator, 'penalty_round_result');
    p2.emit('penalty_choice', { room:penaltyRoom, player:2, round:1, zone:1 });
    const penaltyResult = await penaltyReveal;
    check('Penalty round is publicly streamed after both choices', penaltyResult.p1Zone === 0 && penaltyResult.p2Zone === 1 && penaltyResult.isGoal === true, penaltyResult);

    // Every spectator page must keep waiting while a valid tournament room is
    // being created, but must stop retrying authentication or malformed data.
    for (const page of SPECTATOR_PAGES) {
      const source = fs.readFileSync(path.join(REPO_ROOT, 'public', page), 'utf8');
      const extracted = /function spectatorRetryable\(code\)\{[\s\S]*?\r?\n {2}\}/.exec(source);
      if (!extracted) {
        check(`${page}: spectator retry policy exists`, false, 'function not found');
        continue;
      }
      const build = new Function(
        'SPECT_RETRY_MAX_TRIES',
        'spectRetryTries',
        `${extracted[0]}; return spectatorRetryable;`,
      );
      const fresh = build(10, 0);
      const exhausted = build(10, 10);

      check(`${page}: waits for players without a fixed deadline`,
        fresh('room_not_live') === true && exhausted('room_not_live') === true);
      check(`${page}: retries transient failures only up to the configured limit`,
        fresh('not_live') === true && exhausted('not_live') === false &&
        fresh('verification_failed') === true && exhausted('verification_failed') === false);
      check(`${page}: never retries identity or malformed-request failures`,
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
