'use strict';

const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const ROOT = path.join(__dirname, '..');
const PORT = 3137;
const URL = 'http://127.0.0.1:' + PORT;
const ROOM = 'competition-draw-claim-room';
let failures = 0;

function check(label, cond, detail) {
  if (cond) console.log('  ✅ ' + label);
  else {
    failures++;
    console.log('  ❌ ' + label + (detail !== undefined ? ' → ' + JSON.stringify(detail) : ''));
  }
}
function once(socket, event, timeoutMs = 6000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error('timeout: ' + event)), timeoutMs);
    socket.once(event, (data) => { clearTimeout(timer); resolve(data); });
  });
}
function waitHealth(retries = 50) {
  return new Promise((resolve, reject) => {
    const attempt = (left) => {
      http.get(URL + '/health', (res) => {
        res.resume();
        if (res.statusCode === 200) resolve();
        else retry(left);
      }).on('error', () => retry(left));
    };
    const retry = (left) => left <= 0 ? reject(new Error('serveur runtime injoignable')) : setTimeout(() => attempt(left - 1), 250);
    attempt(retries);
  });
}
function sq(alg) {
  return { row: 8 - Number(alg[1]), col: 'abcdefgh'.indexOf(alg[0]) };
}
async function connectPlayer(id, name) {
  const socket = io(URL, { transports: ['websocket'], reconnection: false });
  await once(socket, 'connect');
  socket.emit('auth:supabase', { supabaseId: id, username: name });
  await once(socket, 'auth:ok');
  return socket;
}
async function move(sender, receiver, player, from, to) {
  const relayed = once(receiver, 'echecs_move');
  const ack = once(sender, 'echecs_move_ack');
  sender.emit('echecs_move', { room: ROOM, player, from: sq(from), to: sq(to), promo: 0 });
  await relayed;
  await ack;
}

async function main() {
  const server = spawn('node', ['scripts/start-server.js'], {
    cwd: ROOT,
    env: {
      ...process.env,
      PORT: String(PORT),
      NODE_ENV: 'test',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app',
      FRAME_ANCESTORS: 'https://mindspille.lovable.app'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stdout.on('data', () => {});
  server.stderr.on('data', (d) => {
    const text = String(d).trim();
    if (text) console.log('[runtime] ' + text);
  });

  let p1, p2;
  try {
    await waitHealth();
    console.log('— runtime production patch —');
    check('start-server.js démarre avec les patches', true);

    p1 = await connectPlayer('33333333-3333-4333-8333-333333333333', 'Blanc');
    p2 = await connectPlayer('44444444-4444-4444-8444-444444444444', 'Noir');

    const s1 = once(p1, 'echecs_start');
    const s2 = once(p2, 'echecs_start');
    p1.emit('echecs_join', { room: ROOM, player: 1, name: 'Blanc', bet: 0, currency: 'HTG' });
    await once(p1, 'echecs_joined');
    p2.emit('echecs_join', { room: ROOM, player: 2, name: 'Noir', bet: 0, currency: 'HTG' });
    await s1; await s2;

    const cycle = [
      [p1, p2, 1, 'g1', 'f3'],
      [p2, p1, 2, 'g8', 'f6'],
      [p1, p2, 1, 'f3', 'g1'],
      [p2, p1, 2, 'f6', 'g8'],
    ];
    for (let round = 0; round < 2; round++) {
      for (const step of cycle) await move(...step);
    }

    const sync = once(p1, 'echecs_state_sync');
    p1.emit('echecs_request_state', { room: ROOM });
    const snapshot = await sync;
    const state = JSON.parse(snapshot.gameState);
    check('3e répétition atteinte sans fin automatique', snapshot.status === 'playing' && state.reps[state.key] >= 3, { status: snapshot.status, repetitions: state.reps[state.key] });

    const claimEvent1 = once(p1, 'echecs_draw_claimed');
    const claimEvent2 = once(p2, 'echecs_draw_claimed');
    const over1 = once(p1, 'game:over');
    const over2 = once(p2, 'game:over');
    p1.emit('echecs_claim_draw', { room: ROOM, player: 1 });
    const [claim1, claim2, end1, end2] = await Promise.all([claimEvent1, claimEvent2, over1, over2]);
    check('réclamation acceptée pour triple répétition', claim1.reason === 'repetition' && claim2.reason === 'repetition', claim1);
    check('les deux joueurs reçoivent une nulle', end1.winnerSlot === 0 && end2.winnerSlot === 0, { end1, end2 });
  } catch (error) {
    failures++;
    console.log('  ❌ exception: ' + error.message);
  } finally {
    if (p1) p1.close();
    if (p2) p2.close();
    server.kill();
  }

  console.log('');
  console.log(failures === 0 ? '✅ RUNTIME ÉCHECS COMPÉTITION VALIDÉ' : '💥 ' + failures + ' échec(s)');
  process.exit(failures === 0 ? 0 : 1);
}

main();
