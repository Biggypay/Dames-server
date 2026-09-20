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

/* Symboles attribues par le serveur au tirage de l'ouverture : le slot 1 n'a
   pas toujours les X. Renseigne des la reception de ttt_start. */
let SLOT_SYMBOLS = { 1: 'X', 2: 'O' };

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
    symbol: SLOT_SYMBOLS[player],
    clientMoveId
  });
  return accepted;
}

/* Qui ouvre est tire au sort (randomOpeningSlot). Le scenario est donc ecrit
   avec des roles — 'A' ouvre la premiere manche, 'B' suit — et les slots reels
   sont lus dans ttt_start. Ecrit en dur sur le slot 1, il echouait une fois
   sur deux des le premier coup : « move rejected p1 0,0 ». */
let ROLE = { A: 1, B: 2 };
const slotOf = role => ROLE[role];

async function playRound(p1, p2, moves, expected) {
  const roundResult = once(p1, 'ttt_manche_result');
  for (const [role, row, col] of moves) {
    const player = slotOf(role);
    await playMove(player === 1 ? p1 : p2, player, row, col);
  }
  const result = await roundResult;
  const expectedWinner = expected.winner === 'draw' ? 'draw' : slotOf(expected.winner);
  check(`round ${result.manchesDone} winner is authoritative`, result.winner === expectedWinner, result);
  /* matchW/matchR comptent les slots 1 et 2, pas les roles : on convertit. */
  const winsForSlot = { 1: 0, 2: 0 };
  winsForSlot[slotOf('A')] = expected.winsA;
  winsForSlot[slotOf('B')] = expected.winsB;
  check(`round ${result.manchesDone} absolute score is correct`, result.matchW === winsForSlot[1] && result.matchR === winsForSlot[2], { result, winsForSlot });
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

    /* Le serveur vient d'annoncer qui ouvre et avec quel symbole. */
    const openerSlot = Number(joined1.gameState.currentPlayer) === 1 ? 2 : 1;
    ROLE = { A: openerSlot, B: openerSlot === 1 ? 2 : 1 };
    SLOT_SYMBOLS = { 1: joined1.gameState.slotSymbols[1], 2: joined1.gameState.slotSymbols[2] };
    const socketOf = role => (slotOf(role) === 1 ? p1 : p2);

    await playMove(socketOf('A'), slotOf('A'), 0, 0);
    p2.disconnect();
    await new Promise(resolve => setTimeout(resolve, 250));
    p2 = await connectPlayer('ttt-player-2', 'Bob');
    const restoredStart = once(p2, 'ttt_start');
    p2.emit('ttt_join', { room: ROOM, player: 2, supabaseId: 'ttt-player-2', name: 'Bob', bet: 500, currency: 'HTG' });
    const restored = await restoredStart;
    check('reconnection restores the exact accepted move', restored.reconnected === true && restored.gameState.board[0] === SLOT_SYMBOLS[slotOf('A')], restored.gameState);
    check('reconnection restores the second player turn', restored.gameState.currentPlayer === slotOf('B') - 1, restored.gameState);

    let round = await playRound(p1, p2, [['B',1,0],['A',0,1],['B',1,1],['A',0,2]], { winner: 'A', winsA: 1, winsB: 0 });
    check('round 2 starter alternates to the other player', round.nextStarterPlayer === slotOf('B') - 1, round);
    await waitFor(p1, 'ttt_state_sync', data => data.gameState?.resolvingRound === false && data.gameState?.board?.every(cell => cell === null));

    round = await playRound(p1, p2, [['B',0,0],['A',1,0],['B',0,1],['A',1,1],['B',0,2]], { winner: 'B', winsA: 1, winsB: 1 });
    check('round 3 starter alternates back to the opening player', round.nextStarterPlayer === slotOf('A') - 1, round);
    await waitFor(p1, 'ttt_state_sync', data => data.gameState?.resolvingRound === false && data.gameState?.board?.every(cell => cell === null));

    round = await playRound(p1, p2, [['A',0,0],['B',0,1],['A',0,2],['B',1,1],['A',1,0],['B',2,0],['A',2,1],['B',1,2],['A',2,2]], { winner: 'draw', winsA: 1, winsB: 1 });
    check('regulation tie activates sudden death', round.isTiebreaker === true && !round.matchWinner, round);
    await waitFor(p1, 'ttt_state_sync', data => data.gameState?.resolvingRound === false && data.gameState?.board?.every(cell => cell === null));

    const over1 = once(p1, 'game:over');
    const over2 = once(p2, 'game:over');
    round = await playRound(p1, p2, [['B',0,0],['A',1,0],['B',0,1],['A',1,1],['B',0,2]], { winner: 'B', winsA: 1, winsB: 2 });
    check('sudden-death winner is declared by the server', round.matchWinner === slotOf('B'), round);
    const [result1, result2] = await Promise.all([over1, over2]);
    const loser = slotOf('A') === 1 ? result1 : result2, winner = slotOf('B') === 1 ? result1 : result2;
    check('the beaten player receives one loss', loser.result === 'loss' && loser.winnerSlot === slotOf('B'), loser);
    check('the sudden-death winner receives one win', winner.result === 'win' && winner.winnerSlot === slotOf('B'), winner);

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

