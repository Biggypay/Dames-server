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
/* `once` prend le PROCHAIN evenement, quel qu'il soit. Or le serveur diffuse
   chaque coup aux DEUX sockets : la copie non consommee du coup precedent
   satisfait aussitot l'attente suivante, et le test enchaine alors qu'un coup
   est encore en vol. Le suivant part hors tour et se fait refuser. D'ou cette
   variante, qui attend l'evenement correspondant au coup reellement envoye. */
function onceMatching(socket, event, predicate, timeoutMs = 4000) {
  return new Promise((resolve, reject) => {
    const handler = (data) => {
      if (!predicate(data)) return;
      clearTimeout(timer); socket.off(event, handler); resolve(data);
    };
    const timer = setTimeout(() => { socket.off(event, handler); reject(new Error('timeout en attendant ' + event)); }, timeoutMs);
    socket.on(event, handler);
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
    let periodic1 = 0, periodic2 = 0, lastPeriodic1 = null, lastPeriodic2 = null;
    const h1 = data => { periodic1++; lastPeriodic1 = data; };
    const h2 = data => { periodic2++; lastPeriodic2 = data; };
    p1.socket.on('dames_state_sync', h1);
    p2.socket.on('dames_state_sync', h2);
    await sleep(6500);
    p1.socket.off('dames_state_sync', h1);
    p2.socket.off('dames_state_sync', h2);
    check('P1 a reçu au moins une sync périodique', periodic1 >= 1, periodic1);
    check('P2 a reçu au moins une sync périodique', periodic2 >= 1, periodic2);
    check('Le démarrage différé ne remet jamais l’horloge à P1 après son coup', lastPeriodic1?.turnPlayer === 2 && lastPeriodic2?.turnPlayer === 2, { lastPeriodic1, lastPeriodic2 });

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

    /* Qui ouvre la partie est TIRE AU SORT par le serveur (randomOpeningSlot),
       et les symboles suivent ce tirage. Ce scenario supposait que le slot 1
       commence avec X : une fois sur deux le "coup hors tour" ci-dessous etait
       en realite un coup legal, toute la choregraphie se desynchronisait et le
       test mourait plus loin sur un timeout dont le message changeait d'une
       execution a l'autre. On lit donc l'ouverture annoncee par ttt_start. */
    const tttSockets = { 1: p1.socket, 2: p2b.socket };

    const tttOpener = Number(tttStarted1.gameState.currentPlayer) === 1 ? 2 : 1;
    const tttFollower = tttOpener === 1 ? 2 : 1;
    const tttSymbol = slot => tttStarted1.gameState.slotSymbols[slot];
    const tttStartRevision = Number(tttStarted1.revision);
    /* Chaque coup accepte est diffuse aux deux joueurs : on attend les deux
       copies, et on les identifie par la case jouee. Rien ne reste en file
       pour parasiter l'attente suivante. */
    const tttPlay = (slot, row, col) => {
      const matches = m => m.player === slot && m.row === row && m.col === col;
      const mine = onceMatching(tttSockets[slot], 'ttt_move', matches);
      const theirs = onceMatching(tttSockets[slot === 1 ? 2 : 1], 'ttt_move', matches);
      tttSockets[slot].emit('ttt_move', { room: tttRoom, player: slot, row, col, symbol: tttSymbol(slot) });
      return Promise.all([mine, theirs]);
    };

    const invalidTurnError = once(tttSockets[tttFollower], 'game:error');
    const invalidTurnSync = once(tttSockets[tttFollower], 'ttt_state_sync');
    tttSockets[tttFollower].emit('ttt_move', { room: tttRoom, player: tttFollower, row: 2, col: 2, symbol: tttSymbol(tttFollower) });
    const [tttInvalidError, tttInvalidSync] = await Promise.all([invalidTurnError, invalidTurnSync]);
    check('TTT rejects an out-of-turn move', tttInvalidError.recoverable === true, tttInvalidError);
    /* "Inchange" se mesure par rapport a ce que le client connait deja, pas
       par rapport a zero : le serveur incremente la revision en faisant passer
       la partie en "playing", si bien que ttt_start annonce deja 1. */
    check('TTT repairs the rejected client with an unchanged board',
      tttInvalidSync.revision === tttStartRevision && tttInvalidSync.gameState.board.every(cell => cell === null),
      { syncRevision: tttInvalidSync.revision, startRevision: tttStartRevision, board: tttInvalidSync.gameState.board });
    const firstMoveAt = Date.now();
    await tttPlay(tttOpener, 0, 0);
    await sleep(3200);
    // Compare the authoritative startTime, not the local receive time: on a
    // fast runner the legitimate initial timer and the move can be received in
    // the same millisecond.
    const lateWrongTimer = tttTurnEvents.find(event => event.startTime > firstMoveAt && event.player === tttOpener);
    check("TTT never restores the clock to the opening player after the first move", !lateWrongTimer, tttTurnEvents);
    check('TTT starts the other player clock after the opening move', tttTurnEvents.some(event => event.startTime >= firstMoveAt && event.player === tttFollower), tttTurnEvents);
    await tttPlay(tttFollower, 1, 0);
    await tttPlay(tttOpener, 0, 1);
    await tttPlay(tttFollower, 1, 1);
    const tttOver1 = once(tttSockets[tttOpener], 'game:over', 6000);
    const tttOver2 = once(tttSockets[tttFollower], 'game:over', 6000);
    tttSockets[tttOpener].emit('ttt_move', { room: tttRoom, player: tttOpener, row: 0, col: 2, symbol: tttSymbol(tttOpener) });
    const [tttResult1, tttResult2] = await Promise.all([tttOver1, tttOver2]);
    check('TTT winner receives only a win', tttResult1.game === 'tictactoe' && tttResult1.result === 'win' && tttResult1.myResult > 0, tttResult1);
    check('TTT loser receives only a loss', tttResult2.game === 'tictactoe' && tttResult2.result === 'loss' && tttResult2.myResult < 0, tttResult2);

    console.log('\n--- Quoridor server-authoritative outcome ---');
    const quoriRoom = 'test-quoridor-authoritative';
    const quoriStart1 = once(p1.socket, 'quoridor_start');
    const quoriStart2 = once(p2b.socket, 'quoridor_start');
    p1.socket.emit('quoridor_join', { room: quoriRoom, player: 1, supabaseId: 'test-user-aaa', name: 'Alice', bet: 5000, currency: 'HTG' });
    p2b.socket.emit('quoridor_join', { room: quoriRoom, player: 2, supabaseId: 'test-user-bbb', name: 'Bob', bet: 5000, currency: 'HTG' });
    const [quoriStarted1] = await Promise.all([quoriStart1, quoriStart2]);

    /* Meme tirage au sort que pour le Tic-Tac-Toe : quoridor_start annonce
       currentSlot. Le camp qui ouvre court jusqu'a son but par la colonne 4,
       l'autre pietine dans son coin, hors du couloir. Les deux itineraires
       sont le miroir exact l'un de l'autre — slot 1 part de (8,4) et gagne en
       r=0, slot 2 part de (0,4) et gagne en r=8 — si bien que le scenario est
       identique quel que soit le tirage. */
    const quoriSockets = { 1: p1.socket, 2: p2b.socket };
    const QUORI_ROUTES = {
      1: {
        run:  [{r:7,c:4},{r:6,c:4},{r:5,c:4},{r:4,c:4},{r:3,c:4},{r:2,c:4},{r:1,c:4}],
        goal: {r:0,c:4},
        idle: [{r:8,c:3},{r:8,c:2},{r:8,c:1},{r:8,c:0},{r:7,c:0},{r:7,c:1},{r:7,c:2},{r:7,c:3}]
      },
      2: {
        run:  [{r:1,c:4},{r:2,c:4},{r:3,c:4},{r:4,c:4},{r:5,c:4},{r:6,c:4},{r:7,c:4}],
        goal: {r:8,c:4},
        idle: [{r:0,c:3},{r:0,c:2},{r:0,c:1},{r:0,c:0},{r:1,c:0},{r:1,c:1},{r:1,c:2},{r:1,c:3}]
      }
    };
    const quoriOpener = Number(quoriStarted1.currentSlot) === 2 ? 2 : 1;
    const quoriFollower = quoriOpener === 1 ? 2 : 1;
    const runnerPath = QUORI_ROUTES[quoriOpener].run;
    const idlePath = QUORI_ROUTES[quoriFollower].idle;

    const quoriWrongTurnError = once(quoriSockets[quoriFollower], 'game:error');
    const quoriWrongTurnRepair = once(quoriSockets[quoriFollower], 'quoridor_state_sync');
    quoriSockets[quoriFollower].emit('quoridor_move', { room: quoriRoom, player: quoriFollower, moveType: 'move', data: QUORI_ROUTES[quoriFollower].run[0] });
    const [quoriError, quoriRepair] = await Promise.all([quoriWrongTurnError, quoriWrongTurnRepair]);
    check('Quoridor rejects an out-of-turn move', typeof quoriError.message === 'string', quoriError);
    check('Quoridor repairs a rejected optimistic client',
      quoriRepair.version === 0 && quoriRepair.gameState.s1Pos.r === 8 && quoriRepair.gameState.s2Pos.r === 0, quoriRepair);

    const quoriAck1 = once(quoriSockets[quoriOpener], 'quoridor_move');
    const quoriMove1 = once(quoriSockets[quoriFollower], 'quoridor_move');
    quoriSockets[quoriOpener].emit('quoridor_move', { room: quoriRoom, player: quoriOpener, moveType: 'move', data: runnerPath[0] });
    const [quoriOwnAck, quoriOpponentMove] = await Promise.all([quoriAck1, quoriMove1]);
    const quoriAckState = JSON.parse(quoriOwnAck.gameState);
    const quoriOpenerPos = quoriOpener === 1 ? quoriAckState.s1Pos : quoriAckState.s2Pos;
    check('Quoridor acknowledges the accepted move to its sender', quoriOwnAck.version === 1 && quoriOpenerPos.r === runnerPath[0].r, quoriOwnAck);
    check('Quoridor streams the same authoritative version to the opponent', quoriOpponentMove.version === 1, quoriOpponentMove);
    // The introductory 3-second delay must not restore the opening player after
    // a fast first move. That race made Quoridor appear frozen or reject the
    // second player.
    await sleep(3200);
    const quoriAfterIntro = once(quoriSockets[quoriFollower], 'quoridor_state_sync');
    quoriSockets[quoriFollower].emit('quoridor_request_state', { room: quoriRoom });
    const quoriAfterIntroSnapshot = await quoriAfterIntro;
    check('Quoridor keeps the second player active after the delayed intro timer',
      quoriAfterIntroSnapshot.currentSlot === quoriFollower && quoriAfterIntroSnapshot.turnPlayer === quoriFollower, quoriAfterIntroSnapshot);
    const idleFirstAck = once(quoriSockets[quoriFollower], 'quoridor_move');
    const idleFirstRelay = once(quoriSockets[quoriOpener], 'quoridor_move');
    quoriSockets[quoriFollower].emit('quoridor_move', { room: quoriRoom, player: quoriFollower, moveType: 'move', data: idlePath[0] });
    await Promise.all([idleFirstAck, idleFirstRelay]);
    const requestedQuoriState = once(quoriSockets[quoriOpener], 'quoridor_state_sync');
    quoriSockets[quoriOpener].emit('quoridor_request_state', { room: quoriRoom });
    const quoriSnapshot = await requestedQuoriState;
    check('Quoridor state can be resynchronised on demand', quoriSnapshot.version === 2 && quoriSnapshot.currentSlot === quoriOpener, quoriSnapshot);

    /* Quoridor se joue en SERIE : lib/gomoku-series.js compte six manches
       reglementaires et ne tranche le match que lorsque l'ecart ne peut plus
       etre rattrape — soit quatre manches gagnees. Ce scenario n'en jouait
       qu'une seule et attendait game:over : il ne pouvait qu'expirer, quel
       que soit le tirage. On joue donc la serie pour de vrai, ce qui couvre
       au passage l'enchainement des manches et l'alternance du starter. */
    const quoriRunner = quoriOpener, quoriIdler = quoriFollower;
    const quoriStep = async (slot, data) => {
      const ack = once(quoriSockets[slot], 'quoridor_move');
      const relay = once(quoriSockets[slot === 1 ? 2 : 1], 'quoridor_move');
      quoriSockets[slot].emit('quoridor_move', { room: quoriRoom, player: slot, moveType: 'move', data });
      await Promise.all([ack, relay]);
    };
    /* Deroule une manche jusqu'au coup gagnant du coureur. `ri`/`ii` permettent
       de reprendre la premiere manche la ou les verifications ci-dessus l'ont
       laissee. Renvoie la fin de manche, et la fin de match sur la derniere. */
    const quoriPlayRound = async ({ starter, ri = 0, ii = 0, expectMatchOver = false }) => {
      const run = QUORI_ROUTES[quoriRunner].run, idle = QUORI_ROUTES[quoriIdler].idle;
      let turn = starter;
      while (ri < run.length) {
        if (turn === quoriRunner) await quoriStep(quoriRunner, run[ri++]);
        else await quoriStep(quoriIdler, idle[ii++]);
        turn = turn === 1 ? 2 : 1;
      }
      if (turn !== quoriRunner) { await quoriStep(quoriIdler, idle[ii++]); turn = quoriRunner; }
      const roundEnd = once(quoriSockets[quoriRunner], 'quoridor_round_end', 8000);
      const overWinner = expectMatchOver ? once(quoriSockets[quoriRunner], 'game:over', 8000) : null;
      const overLoser = expectMatchOver ? once(quoriSockets[quoriIdler], 'game:over', 8000) : null;
      quoriSockets[quoriRunner].emit('quoridor_move', { room: quoriRoom, player: quoriRunner, moveType: 'move', data: QUORI_ROUTES[quoriRunner].goal });
      const ended = await roundEnd;
      if (!expectMatchOver) return { ended };
      return { ended, winner: await overWinner, loser: await overLoser };
    };

    const quoriRound1 = await quoriPlayRound({ starter: quoriRunner, ri: 1, ii: 1 });
    check('Quoridor attributes the round to the pawn that reached its goal', quoriRound1.ended.roundWinner === quoriRunner, quoriRound1.ended);
    check('Quoridor does not end the match on the first round of a six-round series',
      quoriRound1.ended.series.roundsPlayed === 1 && quoriRound1.ended.series.wins[quoriRunner] === 1, quoriRound1.ended.series);

    /* Quatre manches suffisent : 4 - 0 avec deux manches restantes, l'ecart
       n'est plus rattrapable. Le starter alterne a chaque manche, et
       quoridor_round_start l'annonce — on le lit plutot que de le deduire. */
    let quoriResult1, quoriResult2;
    for (let round = 2; round <= 4; round++) {
      const nextRound = await once(quoriSockets[quoriRunner], 'quoridor_round_start', 8000);
      const outcome = await quoriPlayRound({ starter: Number(nextRound.currentSlot), expectMatchOver: round === 4 });
      if (round === 4) { quoriResult1 = outcome.winner; quoriResult2 = outcome.loser; }
    }
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

