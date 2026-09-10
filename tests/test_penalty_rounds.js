/**
 * Tirs au but : six manches réglementaires, puis mort subite par paires.
 *
 * Ce que ce test protège :
 *   • une séance compte SIX manches, pas dix ;
 *   • une égalité au bout des six ne rend plus « match nul » : la séance
 *     continue ;
 *   • la mort subite se joue par PAIRES de manches. Le tireur alterne d'une
 *     manche à l'autre : conclure sur une manche isolée ferait gagner celui
 *     qui a tiré en dernier sans que l'autre ait pu répliquer. Le test le
 *     vérifie en marquant en manche 7 et en s'assurant que la séance n'est
 *     PAS close avant que la manche 8 ait été jouée ;
 *   • un score déjà départagé au bout des six conclut sans mort subite.
 *
 * Le serveur fait autorité : le test ne fait que choisir des zones.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const REPO_ROOT = path.join(__dirname, '..');
const PORT = 3138;
const URL = `http://127.0.0.1:${PORT}`;
let failures = 0;

function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.log(`  FAIL ${label}${detail === undefined ? '' : ` -> ${JSON.stringify(detail)}`}`); }
}

function onceWhere(socket, event, predicate = () => true, timeoutMs = 15000) {
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

/**
 * Joue une manche. `goal` dit si le tireur doit marquer : le gardien plonge
 * ailleurs quand oui, au même endroit quand non.
 */
async function playRound(p1, p2, room, round, goal) {
  const result = onceWhere(p1, 'penalty_round_result', () => true, 20000);
  const shooterZone = 4;
  const keeperZone = goal ? 0 : 4;
  const shooterSlot = round % 2 === 1 ? 1 : 2;
  const zoneFor = slot => (slot === shooterSlot ? shooterZone : keeperZone);
  p1.emit('penalty_choice', { room, player: 1, round, zone: zoneFor(1) });
  p2.emit('penalty_choice', { room, player: 2, round, zone: zoneFor(2) });
  return result;
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

    // ── A. Six manches à égalité, puis mort subite par paires ──────────────
    console.log('Tirs au but : six manches puis mort subite');
    const p1 = await connectPlayer('eeeeeeee-1111-4111-8111-111111111111', 'Alice');
    const p2 = await connectPlayer('ffffffff-2222-4222-8222-222222222222', 'Bob');
    sockets.push(p1, p2);

    const room = 'test-penalty-six-manches';
    const start1 = onceWhere(p1, 'penalty_start');
    p1.emit('penalty_join', { room, player: 1, name: 'Alice', bet: 0 });
    p2.emit('penalty_join', { room, player: 2, name: 'Bob', bet: 0 });
    const started = await start1;
    check('le serveur annonce six manches réglementaires', Number(started.totalRounds) === 6, started.totalRounds);

    // Tout le monde marque : 3-3 au bout des six.
    let last = null;
    for (let round = 1; round <= 6; round++) {
      last = await playRound(p1, p2, room, round, true);
      check(`manche ${round} jouée`, last.isGoal === true, last);
    }
    check('score 3-3 au bout des six manches', last.scores.p1 === 3 && last.scores.p2 === 3, last.scores);
    check('la séance n’est pas close sur une égalité', last.gameOver === false, last);
    check('le serveur annonce la mort subite', last.isTiebreaker === true, last);
    check('une septième manche est annoncée', Number(last.nextRound) === 7, last);

    // Manche 7 : Alice marque. La séance ne DOIT PAS se terminer — Bob n'a pas
    // encore tiré sa manche de mort subite.
    const seventh = await playRound(p1, p2, room, 7, true);
    check('manche 7 : Alice marque et mène', seventh.scores.p1 === 4 && seventh.scores.p2 === 3, seventh.scores);
    check('la séance reste ouverte : le tireur suivant doit répliquer',
      seventh.gameOver === false, seventh);
    check('la manche 8 est annoncée', Number(seventh.nextRound) === 8, seventh);

    // Manche 8 : Bob rate. La paire est complète, Alice l'emporte.
    const overP1 = onceWhere(p1, 'game:over', () => true, 20000);
    const eighth = await playRound(p1, p2, room, 8, false);
    check('manche 8 : Bob rate', eighth.isGoal === false && eighth.scores.p2 === 3, eighth.scores);
    check('la paire complétée clôt la séance', eighth.gameOver === true, eighth);
    const o1 = await overP1;
    check('la mort subite désigne le meilleur buteur', Number(o1.winnerSlot) === 1, o1);
    check('la séance n’est jamais déclarée nulle', o1.reason !== 'draw' && o1.winner !== 'draw', o1);

    // ── B. Score départagé au bout des six : pas de mort subite ────────────
    console.log('Tirs au but : score déjà départagé au bout des six manches');
    const p3 = await connectPlayer('11112222-3333-4333-8333-333333333333', 'Carla');
    const p4 = await connectPlayer('22223333-4444-4444-8444-444444444444', 'Dan');
    sockets.push(p3, p4);

    const room2 = 'test-penalty-decide';
    const start3 = onceWhere(p3, 'penalty_start');
    p3.emit('penalty_join', { room: room2, player: 1, name: 'Carla', bet: 0 });
    p4.emit('penalty_join', { room: room2, player: 2, name: 'Dan', bet: 0 });
    await start3;

    const over3 = onceWhere(p3, 'game:over', () => true, 60000);
    let sixth = null;
    for (let round = 1; round <= 6; round++) {
      // Carla marque ses trois tirs, Dan rate les siens : 3-0.
      sixth = await playRound(p3, p4, room2, round, round % 2 === 1);
    }
    check('score 3-0 au bout des six manches', sixth.scores.p1 === 3 && sixth.scores.p2 === 0, sixth.scores);
    check('un score départagé clôt la séance sans mort subite',
      sixth.gameOver === true && sixth.isTiebreaker === false, sixth);
    const o3 = await over3;
    check('le meilleur buteur des six manches remporte la séance', Number(o3.winnerSlot) === 1, o3);
  } finally {
    for (const socket of sockets) socket.close();
    server.kill('SIGKILL');
  }

  if (failures) { console.log(`\n${failures} test(s) en échec`); process.exit(1); }
  console.log('\nOK Tirs au but : six manches et mort subite par paires');
}

main().catch(error => { console.error('ERREUR FATALE:', error.message); process.exit(1); });
