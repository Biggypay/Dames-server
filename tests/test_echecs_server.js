// Test d'intégration des Échecs multijoueur (serveur autoritatif).
// Lance le vrai serveur, connecte deux joueurs socket.io et vérifie :
//  1. join → echecs_start pour les deux joueurs (Blancs = slot 1)
//  2. coup légal → version incrémentée, relai à l'adversaire, ack à l'émetteur
//  3. coup hors tour → game:error PUIS echecs_state_sync correctif
//  4. coup illégal (cavalier en diagonale) → game:error
//  5. echecs_request_state → instantané complet (état FIDE JSON)
//  6. mat de l'imbécile (1.f3 e5 2.g4 Dh4#) → game:over checkmate,
//     gagnant = slot 2, perdant = slot 1, chacun son propre résultat
//  7. routes HTTP /echecs, /echecs-ai et /echecs-engine.js servies
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');
const REPO_ROOT = path.join(__dirname, '..');

const PORT = 3129;
const URL = 'http://127.0.0.1:' + PORT;
const ROOM = 'test-echecs-room';
let failures = 0;

function check(label, cond, detail) {
  if (cond) console.log('  ✅ ' + label);
  else { failures++; console.log('  ❌ ' + label + (detail !== undefined ? ' → ' + JSON.stringify(detail) : '')); }
}
function once(socket, event, timeoutMs = 5000) {
  return new Promise((resolve, reject) => {
    const t = setTimeout(() => reject(new Error('timeout en attendant ' + event)), timeoutMs);
    socket.once(event, (data) => { clearTimeout(t); resolve(data); });
  });
}
function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }
function waitHealth(retries = 40) {
  return new Promise((resolve, reject) => {
    const tryOnce = (n) => {
      http.get(URL + '/health', res => { res.resume(); res.statusCode === 200 ? resolve() : retry(n); })
        .on('error', () => retry(n));
    };
    const retry = (n) => n <= 0 ? reject(new Error('serveur injoignable')) : setTimeout(() => tryOnce(n - 1), 250);
    tryOnce(retries);
  });
}
function httpGet(pathname) {
  return new Promise((resolve, reject) => {
    http.get(URL + pathname, res => {
      let body = '';
      res.setEncoding('utf8');
      res.on('data', chunk => { body += chunk; });
      res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, body }));
    }).on('error', reject);
  });
}

async function connectPlayer(supabaseId, name) {
  const s = io(URL, { transports: ['websocket'], reconnection: false });
  await once(s, 'connect');
  s.emit('auth:supabase', { supabaseId, username: name });
  const ok = await once(s, 'auth:ok');
  return { socket: s, token: ok.token, userId: ok.userId };
}

// Coordonnées : row = 8 - rang, col = colonne (a=0). e2 → {row:6, col:4}.
function sq(alg) { return { row: 8 - parseInt(alg[1], 10), col: 'abcdefgh'.indexOf(alg[0]) }; }

async function playMove(sender, receiver, player, fromAlg, toAlg, promo) {
  const relay = once(receiver.socket, 'echecs_move');
  const ack = once(sender.socket, 'echecs_move_ack');
  sender.socket.emit('echecs_move', { room: ROOM, player, from: sq(fromAlg), to: sq(toAlg), promo: promo || 0 });
  return { relay: await relay, ack: await ack };
}

async function main() {
  const server = spawn('node', ['server.js'], {
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
  server.stdout.on('data', () => {});
  server.stderr.on('data', d => { const line = String(d).trim(); if (line) console.log('[server] ' + line); });

  try {
    await waitHealth();

    console.log('— Routes HTTP échecs —');
    const pageMulti = await httpGet('/echecs');
    check('/echecs sert la page multijoueur', pageMulti.status === 200 && pageMulti.body.includes('Échecs 3D Pro'));
    const pageAI = await httpGet('/echecs-ai');
    check('/echecs-ai sert la page entraînement', pageAI.status === 200 && pageAI.body.includes('Entraînement IA'));
    const engineJs = await httpGet('/echecs-engine.js');
    check('/echecs-engine.js servi avec type JS', engineJs.status === 200 && /javascript/.test(engineJs.headers['content-type'] || '') && engineJs.body.includes('ChessEngineFactory'));
    const health = await httpGet('/health');
    check('/health expose echecsRooms', JSON.parse(health.body).echecsRooms === 0, health.body);

    console.log('— Connexion des deux joueurs —');
    const p1 = await connectPlayer('11111111-1111-4111-8111-111111111111', 'Blanc');
    const p2 = await connectPlayer('22222222-2222-4222-8222-222222222222', 'Rouge');

    const start1 = once(p1.socket, 'echecs_start');
    const start2 = once(p2.socket, 'echecs_start');
    p1.socket.emit('echecs_join', { room: ROOM, player: 1, name: 'Blanc', bet: 0, currency: 'HTG' });
    await once(p1.socket, 'echecs_joined');
    p2.socket.emit('echecs_join', { room: ROOM, player: 2, name: 'Rouge', bet: 0, currency: 'HTG' });
    const [s1, s2] = [await start1, await start2];
    check('P1 reçoit echecs_start slot 1', s1.yourSlot === 1 && s1.opponentName === 'Rouge', s1);
    check('P2 reçoit echecs_start slot 2', s2.yourSlot === 2 && s2.opponentName === 'Blanc', s2);
    const turn1 = await once(p1.socket, 'echecs_turn_start', 6000);
    check('Timer de tour démarré pour les Blancs (slot 1)', turn1.player === 1, turn1);

    console.log('— Coup légal (1. f3) —');
    const mv1 = await playMove(p1, p2, 1, 'f2', 'f3');
    check('P2 reçoit le coup avec version 1', mv1.relay.version === 1 && mv1.relay.from.row === 6 && mv1.relay.from.col === 5, mv1.relay);
    check('P2 reçoit l’état FIDE JSON du serveur', typeof mv1.relay.gameState === 'string' && JSON.parse(mv1.relay.gameState).t === 1);
    check('P1 reçoit un ack version 1', mv1.ack.version === 1 && mv1.ack.currentPlayer === 1, mv1.ack);

    console.log('— Coup hors tour (P1 rejoue) —');
    const err1 = once(p1.socket, 'game:error');
    const sync1 = once(p1.socket, 'echecs_state_sync');
    p1.socket.emit('echecs_move', { room: ROOM, player: 1, from: sq('e2'), to: sq('e4') });
    check('game:error reçu', !!(await err1));
    const snap1 = await sync1;
    check('État correctif version 1 (coup refusé non compté)', snap1.version === 1, snap1.version);

    console.log('— Coup illégal (cavalier b8 en diagonale) —');
    const err2 = once(p2.socket, 'game:error');
    p2.socket.emit('echecs_move', { room: ROOM, player: 2, from: sq('b8'), to: sq('b6') });
    check('game:error reçu pour coup illégal', !!(await err2));

    console.log('— echecs_request_state —');
    const reqSync = once(p2.socket, 'echecs_state_sync');
    p2.socket.emit('echecs_request_state', { room: ROOM });
    const snap2 = await reqSync;
    check('Instantané version 1', snap2.version === 1, snap2.version);
    check('Instantané currentPlayer 1 (Rouges)', snap2.currentPlayer === 1, snap2.currentPlayer);
    check('Instantané horodaté serveur', typeof snap2.serverTime === 'number');
    const snapState = JSON.parse(snap2.gameState);
    check('Le pion f3 est bien sur le plateau serveur', snapState.b[5 * 8 + 5] === 1);

    console.log('— Mat de l’imbécile (1...e5 2.g4 Dh4#) —');
    await playMove(p2, p1, 2, 'e7', 'e5');
    await playMove(p1, p2, 1, 'g2', 'g4');
    const over1 = once(p1.socket, 'game:over', 6000);
    const over2 = once(p2.socket, 'game:over', 6000);
    p2.socket.emit('echecs_move', { room: ROOM, player: 2, from: sq('d8'), to: sq('h4') });
    const [o1, o2] = [await over1, await over2];
    check('P1 (maté) reçoit une défaite', o1.result === 'loss' && o1.reason === 'checkmate', o1);
    check('P2 (mateur) reçoit une victoire', o2.result === 'win' && o2.reason === 'checkmate', o2);
    check('Gagnant = slot 2', o2.winnerSlot === 2, o2.winnerSlot);

    p1.socket.close(); p2.socket.close();
  } catch (error) {
    failures++;
    console.log('  ❌ exception: ' + error.message);
  } finally {
    server.kill();
  }

  console.log('');
  console.log(failures === 0 ? '✅ TOUS LES TESTS ÉCHECS SERVEUR PASSENT' : '💥 ' + failures + ' échec(s)');
  process.exit(failures === 0 ? 0 : 1);
}

main();
