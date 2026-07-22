const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const REPO_ROOT = path.join(__dirname, '..');
const PORT = 3131;
const URL = `http://127.0.0.1:${PORT}`;
let failures = 0;

function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.log(`  FAIL ${label}${detail === undefined ? '' : ` -> ${JSON.stringify(detail)}`}`); }
}

function onceWhere(socket, event, predicate = () => true, timeoutMs = 8000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      socket.off(event, handler);
      reject(new Error(`timeout waiting for ${event}`));
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

function sleep(ms) { return new Promise(resolve => setTimeout(resolve, ms)); }

function waitHealth(retries = 40) {
  return new Promise((resolve, reject) => {
    const attempt = left => {
      http.get(`${URL}/health`, response => {
        response.resume();
        if (response.statusCode === 200) resolve();
        else retry(left);
      }).on('error', () => retry(left));
    };
    const retry = left => left <= 0
      ? reject(new Error('server unavailable'))
      : setTimeout(() => attempt(left - 1), 250);
    attempt(retries);
  });
}

async function connectPlayer(id, name) {
  const socket = io(URL, { transports: ['websocket'], reconnection: false });
  await onceWhere(socket, 'connect');
  socket.emit('auth:supabase', { supabaseId: id, username: name });
  await onceWhere(socket, 'auth:ok');
  return socket;
}

async function main() {
  const server = spawn(process.execPath, ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(PORT),
      NODE_ENV: 'test',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app',
      FRAME_ANCESTORS: 'https://mindspille.lovable.app'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', data => {
    const line = String(data);
    if (!line.includes('JWT_SECRET') && !line.includes('Missing games.id')) process.stderr.write(line);
  });

  const sockets = [];
  try {
    await waitHealth();
    const p1 = await connectPlayer('11111111-1111-4111-8111-111111111111', 'Alice');
    const p2 = await connectPlayer('22222222-2222-4222-8222-222222222222', 'Bob');
    sockets.push(p1, p2);

    console.log('Chifoumi server countdown');
    const rpsRoom = 'test-rps-countdown';
    const rpsStart1 = onceWhere(p1, 'chifoumi_start');
    const rpsStart2 = onceWhere(p2, 'chifoumi_start');
    p1.emit('chifoumi_join', { room: rpsRoom, player: 1, name: 'Alice', bet: 0 });
    p2.emit('chifoumi_join', { room: rpsRoom, player: 2, name: 'Bob', bet: 0 });
    await Promise.all([rpsStart1, rpsStart2]);
    const countdown1 = onceWhere(p1, 'chifoumi_reveal_countdown');
    const countdown2 = onceWhere(p2, 'chifoumi_reveal_countdown');
    let revealedEarly = false;
    const earlyHandler = () => { revealedEarly = true; };
    p1.once('chifoumi_reveal', earlyHandler);
    p1.emit('chifoumi_choice', { room: rpsRoom, player: 1, choice: 'pierre' });
    p2.emit('chifoumi_choice', { room: rpsRoom, player: 2, choice: 'ciseaux' });
    const [cd1, cd2] = await Promise.all([countdown1, countdown2]);
    check('both players receive the same 5-second deadline', cd1.duration === 5000 && cd2.startTime === cd1.startTime, { cd1, cd2 });
    await sleep(4300);
    check('choices are not revealed before five seconds', !revealedEarly);
    p1.off('chifoumi_reveal', earlyHandler);
    const reveal1 = onceWhere(p1, 'chifoumi_reveal', () => true, 2500);
    const reveal2 = onceWhere(p2, 'chifoumi_reveal', () => true, 2500);
    const [rv1, rv2] = await Promise.all([reveal1, reveal2]);
    check('server computes rock over scissors for player 1', rv1.myChoice === 'pierre' && rv1.opChoice === 'ciseaux' && rv1.scores[0] === 1, rv1);
    check('player 2 receives the mirrored authoritative choices', rv2.myChoice === 'ciseaux' && rv2.opChoice === 'pierre' && rv2.scores[0] === 1, rv2);

    console.log('Ludo authoritative state and reconnect');
    const ludoRoom = 'test-ludo-authoritative';
    const ludoStart1 = onceWhere(p1, 'ludo_start');
    const ludoStart2 = onceWhere(p2, 'ludo_start');
    p1.emit('ludo_join', { room: ludoRoom, player: 1, name: 'Alice', bet: 0 });
    p2.emit('ludo_join', { room: ludoRoom, player: 2, name: 'Bob', bet: 0 });
    const [ls1, ls2] = await Promise.all([ludoStart1, ludoStart2]);
    check('Ludo starts with four home tokens per player', ls1.yourSlot === 1 && ls2.yourSlot === 2 && ls1.state.tokens[1].every(value => value === -1), ls1.state);

    let current = 1;
    let movedSlot = 0;
    for (let attempt = 0; attempt < 60 && !movedSlot; attempt++) {
      const actor = current === 1 ? p1 : p2;
      const rolled = onceWhere(actor, 'ludo_state', data => data?.action?.type === 'roll');
      actor.emit('ludo_roll', { room: ludoRoom, player: current });
      const rollState = await rolled;
      check('server-generated die is between 1 and 6', Number.isInteger(rollState.action.dice) && rollState.action.dice >= 1 && rollState.action.dice <= 6, rollState.action);
      if (rollState.action.dice === 6) {
        check('a six authorizes a home token to leave', rollState.state.phase === 'move' && rollState.state.legalMoves.length === 4, rollState.state);
        const moved = onceWhere(actor, 'ludo_state', data => data?.action?.type === 'move');
        actor.emit('ludo_move', { room: ludoRoom, player: current, tokenIndex: 0 });
        const moveState = await moved;
        check('server moves the selected token to its start square', moveState.state.tokens[current][0] === 0, moveState.state.tokens);
        movedSlot = current;
      } else {
        const next = await onceWhere(actor, 'ludo_turn_start', data => data?.player !== current, 3000);
        current = next.player;
      }
    }
    check('a playable six was reached without client-controlled dice', movedSlot === 1 || movedSlot === 2, movedSlot);

    if (movedSlot) {
      const oldSocket = movedSlot === 1 ? p1 : p2;
      oldSocket.disconnect();
      await sleep(150);
      const replacement = await connectPlayer(
        movedSlot === 1 ? '11111111-1111-4111-8111-111111111111' : '22222222-2222-4222-8222-222222222222',
        movedSlot === 1 ? 'Alice' : 'Bob'
      );
      sockets.push(replacement);
      const resumed = onceWhere(replacement, 'ludo_start');
      replacement.emit('ludo_join', { room: ludoRoom, player: movedSlot, name: movedSlot === 1 ? 'Alice' : 'Bob', bet: 0 });
      const resumeState = await resumed;
      check('reconnection restores the exact Ludo token position', resumeState.reconnected === true && resumeState.state.tokens[movedSlot][0] === 0, resumeState.state);
    }
  } catch (error) {
    failures++;
    console.error(`  FAIL exception: ${error.message}`);
  } finally {
    for (const socket of sockets) {
      try { socket.close(); } catch {}
    }
    server.kill();
  }

  console.log(failures === 0 ? 'OK Ludo/Chifoumi tests passed' : `FAIL ${failures} test(s)`);
  process.exit(failures === 0 ? 0 : 1);
}

main();
