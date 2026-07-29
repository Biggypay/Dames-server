const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const ROOT = path.join(__dirname, '..');
const PORT = 3131;
const URL = `http://127.0.0.1:${PORT}`;
const ROOM = 'test-ttt-full-match';
let failures = 0;

function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else {
    failures++;
    console.error(`  FAIL ${label}`, detail ?? '');
  }
}

function once(socket, event, timeoutMs = 7000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error(`timeout ${event}`)), timeoutMs);
    socket.once(event, data => {
      clearTimeout(timer);
      resolve(data);
    });
  });
}

function waitFor(socket, event, predicate, timeoutMs = 7000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      socket.off(event, handler);
      reject(new Error(`timeout ${event} predicate`));
    }, timeoutMs);
    const handler = data => {
      if (!predicate(data)) return;
      clearTimeout(timer);
      socket.off(event, handler);
      resolve(data);
    };
    socket.on(event, handler);
  });
}

function waitHealth() {
  return new Promise((resolve, reject) => {
    let remaining = 50;
    const attempt = () => {
      http.get(`${URL}/health`, response => {
        response.resume();
        if (response.statusCode === 200) resolve();
        else retry();
      }).on('error', retry);
    };
    const retry = () => {
      if (--remaining <= 0) reject(new Error('server unavailable'));
      else setTimeout(attempt, 200);
    };
    attempt();
  });
}

async function connectPlayer(id, name) {
  const socket = io(URL, { transports: ['websocket'], reconnection: false });
  await once(socket, 'connect');
  socket.emit('auth:supabase', { supabaseId: id, username: name });
  await once(socket, 'auth:ok');
  return socket;
}

async function playMove(socket, player, row, col) {
  const clientMoveId = `${player}-${row}-${col}-${Date.now()}`;
  const accepted = new Promise((resolve, reject) => {
    const timer = setTimeout(() => done(new Error(`move timeout p${player} ${row},${col}`)), 4000);
    const onMove = data => {
      if (data.clientMoveId !== clientMoveId) return;
      done(null, data);
    };
    const onError = data => done(new Error(`move rejected p${player} ${row},${col}: ${data?.message}`));
    const done = (error, data) => {
      clearTimeout(timer);
      socket.off('ttt_move', onMove);
      socket.off('game:error', onError);
      if (error) reject(error);
      else resolve(data);
    };
    socket.on('ttt_move', onMove);
    socket.on('game:error', onError);
  });
  socket.emit('ttt_move', {
    room: ROOM,
    player,
    row,
    col,
    symbol: player === 1 ? 'X' : 'O',
    clientMoveId
  });
  return accepted;
}

async function playRound(p1, p2, moves, expected) {
  const roundResult = once(p1, 'ttt_manche_result');
  for (const [player, row, col] of moves) {
    await playMove(player === 1 ? p1 : p2, player, row, col);
  }
  const result = await roundResult;
  check(`round ${result.manchesDone} winner is authoritative`, result.winner === expected.winner, result);
  check(`round ${result.manchesDone} absolute score is correct`, result.matchW === expected.matchW && result.matchR === expected.matchR, result);
  return result;
}

async function main() {
  const server = spawn('node', ['server.js'], {
    cwd: ROOT,
    env: { ...process.env, PORT: String(PORT), NODE_ENV: 'test', TTT_TOTAL_ROUNDS: '3' },
    stdio: ['ignore', 'ignore', 'pipe']
  });
  server.stderr.on('data', data => {
    const line = String(data);
    if (!line.includes('JWT_SECRET') && !line.includes('Missing games.id')) process.stderr.write(line);
  });

  let p1;
  let p2;
  try {
    await waitHealth();
    p1 = await connectPlayer('ttt-player-1', 'Alice');
    p2 = await connectPlayer('ttt-player-2', 'Bob');

    const start1 = once(p1, 'ttt_start');
    const start2 = once(p2, 'ttt_start');
    p1.emit('ttt_join', { room: ROOM, player: 1, supabaseId: 'ttt-player-1', name: 'Alice', bet: 500, currency: 'HTG' });
    p2.emit('ttt_join', { room: ROOM, player: 2, supabaseId: 'ttt-player-2', name: 'Bob', bet: 500, currency: 'HTG' });
    const [joined1, joined2] = await Promise.all([start1, start2]);
    check('both clients receive three server-owned regulation rounds', joined1.totalManches === 3 && joined2.totalManches === 3);

    await playMove(p1, 1, 0, 0);
    p2.disconnect();
    await new Promise(resolve => setTimeout(resolve, 250));
    p2 = await connectPlayer('ttt-player-2', 'Bob');
    const restoredStart = once(p2, 'ttt_start');
    p2.emit('ttt_join', { room: ROOM, player: 2, supabaseId: 'ttt-player-2', name: 'Bob', bet: 500, currency: 'HTG' });
    const restored = await restoredStart;
    check('reconnection restores the exact accepted move', restored.reconnected === true && restored.gameState.board[0] === 'X', restored.gameState);
    check('reconnection restores player 2 turn', restored.gameState.currentPlayer === 1, restored.gameState);

    let round = await playRound(p1, p2, [[2,1,0],[1,0,1],[2,1,1],[1,0,2]], { winner: 1, matchW: 1, matchR: 0 });
    check('round 2 starter alternates to player 2', round.nextStarterPlayer === 1, round);
    await waitFor(p1, 'ttt_state_sync', data => data.gameState?.resolvingRound === false && data.gameState?.board?.every(cell => cell === null));

    round = await playRound(p1, p2, [[2,0,0],[1,1,0],[2,0,1],[1,1,1],[2,0,2]], { winner: 2, matchW: 1, matchR: 1 });
    check('round 3 starter alternates back to player 1', round.nextStarterPlayer === 0, round);
    await waitFor(p1, 'ttt_state_sync', data => data.gameState?.resolvingRound === false && data.gameState?.board?.every(cell => cell === null));

    round = await playRound(p1, p2, [[1,0,0],[2,0,1],[1,0,2],[2,1,1],[1,1,0],[2,2,0],[1,2,1],[2,1,2],[1,2,2]], { winner: 'draw', matchW: 1, matchR: 1 });
    check('regulation tie activates sudden death', round.isTiebreaker === true && !round.matchWinner, round);
    await waitFor(p1, 'ttt_state_sync', data => data.gameState?.resolvingRound === false && data.gameState?.board?.every(cell => cell === null));

    const over1 = once(p1, 'game:over');
    const over2 = once(p2, 'game:over');
    round = await playRound(p1, p2, [[2,0,0],[1,1,0],[2,0,1],[1,1,1],[2,0,2]], { winner: 2, matchW: 1, matchR: 2 });
    check('sudden-death winner is declared by the server', round.matchWinner === 2, round);
    const [result1, result2] = await Promise.all([over1, over2]);
    check('player 1 receives one loss', result1.result === 'loss' && result1.winnerSlot === 2, result1);
    check('player 2 receives one win', result2.result === 'win' && result2.winnerSlot === 2, result2);

    console.log(failures === 0 ? 'OK full Tic-Tac-Toe match tests passed' : `FAIL ${failures} Tic-Tac-Toe checks`);
  } finally {
    p1?.disconnect();
    p2?.disconnect();
    server.kill('SIGKILL');
  }
  process.exit(failures === 0 ? 0 : 1);
}

main().catch(error => {
  console.error(error);
  process.exit(1);
});

