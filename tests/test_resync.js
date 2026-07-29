// Test d'intégration du correctif « serveur autoritatif + re-synchro dames ».
// Lance le vrai serveur, connecte deux joueurs socket.io et vérifie :
//  1. coup légal → version incrémentée, relai avec version, ack à l'émetteur
//  2. dames_request_state → instantané complet de l'état
//  3. coup hors tour → game:error PUIS dames_state_sync correctif
//  4. coup illégal → game:error PUIS dames_state_sync correctif
//  5. diffusion périodique dames_state_sync (~5 s) aux deux joueurs
//  6. reconnexion → dames_start avec stateVersion + sync de reprise
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');
const REPO_ROOT = path.join(__dirname, '..');

const PORT = 3123;
const URL = 'http://127.0.0.1:' + PORT;
const ROOM = 'test-resync-room';
let failures = 0;

function check(label, cond, detail) {
  if (cond) console.log('  ✅ ' + label);
  else { failures++; console.log('  ❌ ' + label + (detail !== undefined ? ' → ' + JSON.stringify(detail) : '')); }
}
function once(socket, event, timeoutMs = 4000) {
  return new Promise((resolve, reject) => {
    const t = setTimeout(() => reject(new Error('timeout en attendant ' + event)), timeoutMs);
    socket.once(event, (data) => { clearTimeout(t); resolve(data); });
  });
}
function sleep(ms) { return new Promise(r => setTimeout(r, ms)); }
async function emitAndWait(sender, receiver, emitEvent, payload, receiveEvent) {
  const received = once(receiver, receiveEvent);
  sender.emit(emitEvent, payload);
  return received;
}
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

function httpRequest(pathname, { method = 'GET', headers = {}, body = null } = {}) {
  return new Promise((resolve, reject) => {
    const req = http.request(URL + pathname, { method, headers }, res => {
      let body = '';
      res.setEncoding('utf8');
      res.on('data', chunk => { body += chunk; });
      res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, body }));
    });
    req.on('error', reject);
    req.end(body);
  });
}

async function connectPlayer(supabaseId, name) {
  const s = io(URL, { transports: ['websocket'], reconnection: false });
  await once(s, 'connect');
  s.emit('auth:supabase', { supabaseId, username: name });
  const ok = await once(s, 'auth:ok');
  return { socket: s, token: ok.token, userId: ok.userId };
}

async function main() {
  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(PORT),
      NODE_ENV: 'test',
      TTT_TOTAL_ROUNDS: '1',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app',
      FRAME_ANCESTORS: 'https://mindspille.lovable.app'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stdout.on('data', () => {});
  server.stderr.on('data', d => { const s = String(d); if (!s.includes('JWT_SECRET')) process.stderr.write('[server] ' + s); });
  try {
    await waitHealth();
    console.log('Serveur démarré.');

    const health = await httpRequest('/health');
    const healthBody = JSON.parse(health.body);
    check('/health does not expose queued bet amounts', health.status === 200 && !('queues' in healthBody) && Number.isInteger(healthBody.queuedPlayers));
    const deniedCors = await httpRequest('/dames', { method: 'OPTIONS', headers: { Origin: 'https://evil.example' } });
    check('Disallowed origins do not receive CORS', deniedCors.headers['access-control-allow-origin'] === undefined);
    const allowedCors = await httpRequest('/dames', { method: 'OPTIONS', headers: { Origin: 'https://mindspille.lovable.app' } });
    check('Configured origin receives CORS', allowedCors.headers['access-control-allow-origin'] === 'https://mindspille.lovable.app');
    const invalidInjection = await httpRequest('/penalty?p1Id=%3Cscript%3Ealert(1)%3C%2Fscript%3E&p2Id=550e8400-e29b-41d4-a716-446655440000');
    check('Injectable player identifiers are rejected', invalidInjection.status === 400 && !invalidInjection.body.includes('<script>'));

    const p1 = await connectPlayer('test-user-aaa', 'Alice');
    const p2 = await connectPlayer('test-user-bbb', 'Bob');

    // ── Join des deux joueurs ─────────────────────────────
    const start1 = once(p1.socket, 'dames_start');
    const start2 = once(p2.socket, 'dames_start');
    p1.socket.emit('dames_join', { room: ROOM, player: 1, supabaseId: 'test-user-aaa', name: 'Alice', bet: 5000, currency: 'HTG' });
    await sleep(150);
    p2.socket.emit('dames_join', { room: ROOM, player: 2, supabaseId: 'test-user-bbb', name: 'Bob', bet: 5000, currency: 'HTG' });
    const [s1, s2] = await Promise.all([start1, start2]);
    console.log('\n— Démarrage —');
    check('P1 reçoit dames_start slot 1', s1.yourSlot === 1);
    check('P2 reçoit dames_start slot 2', s2.yourSlot === 2);

    // ── 1. Coup légal : version + relai + ack ─────────────
    console.log('\n— Coup légal (P1 blanc 6,1 → 5,2) —');
    const moveToP2 = once(p2.socket, 'dames_move');
    const ackToP1 = once(p1.socket, 'dames_move_ack');
    p1.socket.emit('dames_move', { room: ROOM, player: 1, steps: [{ from: { row: 6, col: 1 }, to: { row: 5, col: 2 } }] });
    const [mv, ack] = await Promise.all([moveToP2, ackToP1]);
    check('P2 reçoit le coup avec version 1', mv.version === 1, mv.version);
    check('P2 reçoit nextPlayer = 1 (tour des noirs)', mv.nextPlayer === 1, mv.nextPlayer);
    check('P1 reçoit un ack version 1', ack.version === 1 && ack.room === ROOM, ack);

    // ── 2. Demande d'état à la volée ──────────────────────
    console.log('\n— dames_request_state —');
    const syncReq = once(p2.socket, 'dames_state_sync');
    p2.socket.emit('dames_request_state', { room: ROOM });
    const snap = await syncReq;
    check('Instantané version 1', snap.version === 1, snap.version);
    check('Instantané currentPlayer 1', snap.currentPlayer === 1, snap.currentPlayer);
    const parsedBoard = JSON.parse(snap.boardState);
    check('Plateau 10x10 avec le coup appliqué', parsedBoard.length === 10 && parsedBoard[5][2] !== null && parsedBoard[6][1] === null);
    check('Instantané horodaté serveur', typeof snap.serverTime === 'number');

    // ── 3. Coup hors tour → erreur + état correctif ───────
    console.log('\n— Coup hors tour (P1 rejoue) —');
    const err1 = once(p1.socket, 'game:error');
    const fix1 = once(p1.socket, 'dames_state_sync');
    p1.socket.emit('dames_move', { room: ROOM, player: 1, steps: [{ from: { row: 6, col: 3 }, to: { row: 5, col: 4 } }] });
    const [e1, f1] = await Promise.all([err1, fix1]);
    check('game:error reçu', typeof e1.message === 'string');
    check('État correctif version 1 (coup refusé non compté)', f1.version === 1, f1.version);

    // ── 4. Coup illégal → erreur + état correctif ─────────
    console.log('\n— Coup illégal (P2 depuis case vide) —');
    const err2 = once(p2.socket, 'game:error');
    const fix2 = once(p2.socket, 'dames_state_sync');
    p2.socket.emit('dames_move', { room: ROOM, player: 2, steps: [{ from: { row: 4, col: 4 }, to: { row: 5, col: 5 } }] });
    const [e2, f2] = await Promise.all([err2, fix2]);
    check('game:error reçu', typeof e2.message === 'string');
    check('État correctif version 1', f2.version === 1, f2.version);

    // ── 5. Diffusion périodique ───────────────────────────
    console.log('\n— Diffusion périodique (attente ≤ 6,5 s) —');
    let periodic1 = 0, periodic2 = 0;
    const h1 = () => periodic1++, h2 = () => periodic2++;
    p1.socket.on('dames_state_sync', h1);
    p2.socket.on('dames_state_sync', h2);
    await sleep(6500);
    p1.socket.off('dames_state_sync', h1);
    p2.socket.off('dames_state_sync', h2);
    check('P1 a reçu au moins une sync périodique', periodic1 >= 1, periodic1);
    check('P2 a reçu au moins une sync périodique', periodic2 >= 1, periodic2);

    // ── Coup légal P2 pour passer en version 2 ────────────
    console.log('\n— Coup légal (P2 noir 3,0 → 4,1) —');
    const moveToP1 = once(p1.socket, 'dames_move');
    const ackToP2 = once(p2.socket, 'dames_move_ack');
    p2.socket.emit('dames_move', { room: ROOM, player: 2, steps: [{ from: { row: 3, col: 0 }, to: { row: 4, col: 1 } }] });
    const [mv2, ack2] = await Promise.all([moveToP1, ackToP2]);
    check('P1 reçoit le coup avec version 2', mv2.version === 2, mv2.version);
    check('P2 reçoit un ack version 2', ack2.version === 2, ack2);

    // ── 6. Reconnexion : dames_start versionné + sync de reprise ──
    console.log('\n— Reconnexion de P2 —');
    p2.socket.disconnect();
    await sleep(400);
    const p2b = await connectPlayer('test-user-bbb', 'Bob');
    const restart = once(p2b.socket, 'dames_start');
    const resumeSync = once(p2b.socket, 'dames_state_sync');
    p2b.socket.emit('dames_join', { room: ROOM, player: 2, supabaseId: 'test-user-bbb', name: 'Bob', bet: 5000, currency: 'HTG' });
    const rs = await restart;
    check('dames_start reconnected', rs.reconnected === true);
    check('dames_start porte stateVersion 2', rs.stateVersion === 2, rs.stateVersion);
    check('dames_start porte le plateau', typeof rs.boardState === 'string' && rs.boardState.length > 10);
    const rsync = await resumeSync;

    console.log('\n--- Tic-Tac-Toe server-authoritative outcome ---');
    const tttRoom = 'test-ttt-authoritative';
    const tttTurnEvents = [];
    p1.socket.on('ttt_turn_start', data => tttTurnEvents.push({ ...data, receivedAt: Date.now() }));
    const tttStart1 = once(p1.socket, 'ttt_start');
    const tttStart2 = once(p2b.socket, 'ttt_start');
    p1.socket.emit('ttt_join', { room: tttRoom, player: 1, supabaseId: 'test-user-aaa', name: 'Alice', bet: 5000, currency: 'HTG', manches: 1 });
    p2b.socket.emit('ttt_join', { room: tttRoom, player: 2, supabaseId: 'test-user-bbb', name: 'Bob', bet: 5000, currency: 'HTG', manches: 1 });
    const [tttStarted1, tttStarted2] = await Promise.all([tttStart1, tttStart2]);
    check('TTT uses the server-owned round count', tttStarted1.totalManches === 1 && tttStarted2.totalManches === 1);
    check('TTT start contains the authoritative empty board', Array.isArray(tttStarted1.gameState?.board) && tttStarted1.gameState.board.every(cell => cell === null));
    const invalidTurnError = once(p2b.socket, 'game:error');
    const invalidTurnSync = once(p2b.socket, 'ttt_state_sync');
    p2b.socket.emit('ttt_move', { room: tttRoom, player: 2, row: 2, col: 2, symbol: 'O' });
    const [tttInvalidError, tttInvalidSync] = await Promise.all([invalidTurnError, invalidTurnSync]);
    check('TTT rejects an out-of-turn move', tttInvalidError.recoverable === true, tttInvalidError);
    check('TTT repairs the rejected client with an unchanged board', tttInvalidSync.revision === 0 && tttInvalidSync.gameState.board.every(cell => cell === null), tttInvalidSync);
    const firstMoveAt = Date.now();
    await emitAndWait(p1.socket, p2b.socket, 'ttt_move', { room: tttRoom, player: 1, row: 0, col: 0, symbol: 'X' }, 'ttt_move');
    await sleep(3200);
    // Compare the authoritative startTime, not the local receive time: on a
    // fast runner the legitimate initial timer and the move can be received in
    // the same millisecond.
    const lateWrongTimer = tttTurnEvents.find(event => event.startTime >= firstMoveAt && event.player === 1);
    check('TTT never restores the clock to player 1 after the first move', !lateWrongTimer, tttTurnEvents);
    check('TTT starts player 2 clock after player 1 move', tttTurnEvents.some(event => event.startTime >= firstMoveAt && event.player === 2), tttTurnEvents);
    await emitAndWait(p2b.socket, p1.socket, 'ttt_move', { room: tttRoom, player: 2, row: 1, col: 0, symbol: 'O' }, 'ttt_move');
    await emitAndWait(p1.socket, p2b.socket, 'ttt_move', { room: tttRoom, player: 1, row: 0, col: 1, symbol: 'X' }, 'ttt_move');
    await emitAndWait(p2b.socket, p1.socket, 'ttt_move', { room: tttRoom, player: 2, row: 1, col: 1, symbol: 'O' }, 'ttt_move');
    const tttOver1 = once(p1.socket, 'game:over', 6000);
    const tttOver2 = once(p2b.socket, 'game:over', 6000);
    p1.socket.emit('ttt_move', { room: tttRoom, player: 1, row: 0, col: 2, symbol: 'X' });
    const [tttResult1, tttResult2] = await Promise.all([tttOver1, tttOver2]);
    check('TTT winner receives only a win', tttResult1.game === 'tictactoe' && tttResult1.result === 'win' && tttResult1.myResult > 0, tttResult1);
    check('TTT loser receives only a loss', tttResult2.game === 'tictactoe' && tttResult2.result === 'loss' && tttResult2.myResult < 0, tttResult2);

    console.log('\n--- Quoridor server-authoritative outcome ---');
    const quoriRoom = 'test-quoridor-authoritative';
    const quoriStart1 = once(p1.socket, 'quoridor_start');
    const quoriStart2 = once(p2b.socket, 'quoridor_start');
    p1.socket.emit('quoridor_join', { room: quoriRoom, player: 1, supabaseId: 'test-user-aaa', name: 'Alice', bet: 5000, currency: 'HTG' });
    p2b.socket.emit('quoridor_join', { room: quoriRoom, player: 2, supabaseId: 'test-user-bbb', name: 'Bob', bet: 5000, currency: 'HTG' });
    await Promise.all([quoriStart1, quoriStart2]);
    const p1Path = [{r:7,c:4},{r:6,c:4},{r:5,c:4},{r:4,c:4},{r:3,c:4},{r:2,c:4},{r:1,c:4}];
    const p2Path = [{r:0,c:3},{r:0,c:2},{r:0,c:1},{r:0,c:0},{r:1,c:0},{r:1,c:1},{r:1,c:2}];
    for (let i = 0; i < p1Path.length; i++) {
      await emitAndWait(p1.socket, p2b.socket, 'quoridor_move', { room: quoriRoom, player: 1, moveType: 'move', data: p1Path[i] }, 'quoridor_move');
      await emitAndWait(p2b.socket, p1.socket, 'quoridor_move', { room: quoriRoom, player: 2, moveType: 'move', data: p2Path[i] }, 'quoridor_move');
    }
    const quoriOver1 = once(p1.socket, 'game:over');
    const quoriOver2 = once(p2b.socket, 'game:over');
    p1.socket.emit('quoridor_move', { room: quoriRoom, player: 1, moveType: 'move', data: { r: 0, c: 4 } });
    const [quoriResult1, quoriResult2] = await Promise.all([quoriOver1, quoriOver2]);
    check('Quoridor winner receives only a win', quoriResult1.game === 'quoridor' && quoriResult1.result === 'win' && quoriResult1.myResult > 0, quoriResult1);
    check('Quoridor loser receives only a loss', quoriResult2.game === 'quoridor' && quoriResult2.result === 'loss' && quoriResult2.myResult < 0, quoriResult2);
    check('Sync de reprise diffusée à la reconnexion (version 2)', rsync.version === 2, rsync.version);

    console.log('\n══════════════════════════════');
    console.log(failures === 0 ? '✅ TOUS LES TESTS PASSENT' : '❌ ' + failures + ' ÉCHEC(S)');
    console.log('\n--- Forfait volontaire serveur-autoritatif ---');
    const resignRoom = 'test-voluntary-resign';
    const resignStart1 = once(p1.socket, 'ttt_start');
    const resignStart2 = once(p2b.socket, 'ttt_start');
    p1.socket.emit('ttt_join', { room: resignRoom, player: 1, supabaseId: 'test-user-aaa', name: 'Alice', bet: 5000, currency: 'HTG', manches: 1 });
    p2b.socket.emit('ttt_join', { room: resignRoom, player: 2, supabaseId: 'test-user-bbb', name: 'Bob', bet: 5000, currency: 'HTG', manches: 1 });
    await Promise.all([resignStart1, resignStart2]);
    const resignLoss = once(p1.socket, 'game:over');
    const resignWin = once(p2b.socket, 'game:over');
    const resignResponse = await httpRequest('/game/resign', {
      method: 'POST',
      headers: { Authorization: 'Bearer ' + p1.token, 'Content-Type': 'application/json' },
      body: JSON.stringify({ gameId: resignRoom })
    });
    const [resignLoserResult, resignWinnerResult] = await Promise.all([resignLoss, resignWin]);
    check('Le forfait HTTP authentifié est accepté', [200, 202].includes(resignResponse.status), resignResponse);
    check('Le joueur qui abandonne perd', resignLoserResult.result === 'loss' && resignLoserResult.reason === 'resign', resignLoserResult);
    check('Son adversaire gagne', resignWinnerResult.result === 'win' && resignWinnerResult.reason === 'resign', resignWinnerResult);

    p1.socket.disconnect(); p2b.socket.disconnect();
  } finally {
    server.kill('SIGKILL');
  }
  process.exit(failures === 0 ? 0 : 1);
}

main().catch(e => { console.error('ERREUR FATALE:', e.message); process.exit(1); });

