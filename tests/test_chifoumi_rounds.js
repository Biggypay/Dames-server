/**
 * Chifoumi : six manches réglementaires, puis mort subite.
 *
 * Ce que ce test protège :
 *   • un match compte SIX manches, pas cinq ;
 *   • à l'issue des six, une égalité ne rend plus un « match nul » : le
 *     serveur ouvre une mort subite et enchaîne des manches jusqu'à ce que
 *     l'une d'elles désigne un vainqueur ;
 *   • une manche de mort subite nulle (les deux mêmes signes) ne tranche
 *     rien et laisse le match ouvert ;
 *   • un score déjà départagé au bout des six manches conclut sans mort
 *     subite.
 *
 * Le serveur fait autorité : le test ne joue que des coups et lit ce que le
 * serveur en déduit.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const REPO_ROOT = path.join(__dirname, '..');
const PORT = 3137;
const URL = `http://127.0.0.1:${PORT}`;
let failures = 0;

function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.log(`  FAIL ${label}${detail === undefined ? '' : ` -> ${JSON.stringify(detail)}`}`); }
}

function onceWhere(socket, event, predicate = () => true, timeoutMs = 12000) {
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

/** Joue une manche et rend son résultat officiel, tel que le serveur l'écrit. */
async function playRound(p1, p2, room, round, choice1, choice2) {
  const result = onceWhere(p1, 'chifoumi_round_result', d => Number(d.round) === round, 15000);
  p1.emit('chifoumi_choice', { room, player: 1, choice: choice1 });
  p2.emit('chifoumi_choice', { room, player: 2, choice: choice2 });
  return result;
}

/** Attend l'ouverture de la manche suivante. */
function nextRoundReady(socket, round) {
  return onceWhere(socket, 'chifoumi_round_ready', d => Number(d.round) === round, 15000);
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

    // ── A. Six manches, égalité 3-3, puis mort subite ───────────────────────
    console.log('Chifoumi : six manches puis mort subite');
    const p1 = await connectPlayer('aaaaaaaa-1111-4111-8111-111111111111', 'Alice');
    const p2 = await connectPlayer('bbbbbbbb-2222-4222-8222-222222222222', 'Bob');
    sockets.push(p1, p2);

    const room = 'test-chifoumi-six-manches';
    const start1 = onceWhere(p1, 'chifoumi_start');
    p1.emit('chifoumi_join', { room, player: 1, name: 'Alice', bet: 0 });
    p2.emit('chifoumi_join', { room, player: 2, name: 'Bob', bet: 0 });
    const started = await start1;
    check('le serveur annonce six manches réglementaires', Number(started.totalRounds) === 6, started.totalRounds);

    // Trois manches pour Alice, trois pour Bob : 3-3 après les six.
    const WIN_P1 = ['pierre', 'ciseaux'];   // pierre bat ciseaux
    const WIN_P2 = ['ciseaux', 'pierre'];
    const plan = [WIN_P1, WIN_P2, WIN_P1, WIN_P2, WIN_P1, WIN_P2];

    for (let round = 1; round <= 6; round++) {
      const [c1, c2] = plan[round - 1];
      const result = await playRound(p1, p2, room, round, c1, c2);
      check(`manche ${round} tranchée par le serveur`, result.winnerSlot === (round % 2 === 1 ? 1 : 2), result);
      if (round === 6) {
        check('score 3-3 au bout des six manches', result.scores[0] === 3 && result.scores[1] === 3, result.scores);
      } else {
        await nextRoundReady(p1, round + 1);
      }
    }

    // Le serveur doit ouvrir une septième manche, en mort subite.
    const suddenDeath = await nextRoundReady(p1, 7);
    check('une septième manche est ouverte au lieu d’un match nul', Number(suddenDeath.round) === 7, suddenDeath);
    check('le serveur annonce la mort subite', suddenDeath.isTiebreaker === true, suddenDeath);

    // Une manche de mort subite nulle ne tranche rien : on rejoue.
    const drawn = await playRound(p1, p2, room, 7, 'pierre', 'pierre');
    check('une manche décisive nulle ne désigne personne', drawn.winnerSlot === 0, drawn);
    const eighth = await nextRoundReady(p1, 8);
    check('la mort subite continue après une manche nulle', eighth.isTiebreaker === true, eighth);

    // Une manche décisive tranche enfin le match.
    const overP1 = onceWhere(p1, 'game:over', () => true, 15000);
    const overP2 = onceWhere(p2, 'game:over', () => true, 15000);
    await playRound(p1, p2, room, 8, 'pierre', 'ciseaux');
    const [o1, o2] = await Promise.all([overP1, overP2]);
    check('la mort subite désigne le vainqueur de la manche décisive', Number(o1.winnerSlot) === 1, o1);
    check('les deux joueurs reçoivent le même verdict', Number(o2.winnerSlot) === 1, o2);
    check('le match n’est jamais déclaré nul', o1.reason !== 'draw' && o1.winner !== 'draw', o1);

    // ── B. Score départagé au bout des six : pas de mort subite ─────────────
    console.log('Chifoumi : score déjà départagé au bout des six manches');
    const p3 = await connectPlayer('cccccccc-3333-4333-8333-333333333333', 'Carla');
    const p4 = await connectPlayer('dddddddd-4444-4444-8444-444444444444', 'Dan');
    sockets.push(p3, p4);

    const room2 = 'test-chifoumi-decide';
    const start3 = onceWhere(p3, 'chifoumi_start');
    p3.emit('chifoumi_join', { room: room2, player: 1, name: 'Carla', bet: 0 });
    p4.emit('chifoumi_join', { room: room2, player: 2, name: 'Dan', bet: 0 });
    await start3;

    const over3 = onceWhere(p3, 'game:over', () => true, 90000);
    let sawSeventh = false;
    p3.on('chifoumi_round_ready', d => { if (Number(d.round) === 7) sawSeventh = true; });

    for (let round = 1; round <= 6; round++) {
      // Carla gagne les quatre premières, Dan les deux dernières : 4-2.
      const [c1, c2] = round <= 4 ? WIN_P1 : WIN_P2;
      await playRound(p3, p4, room2, round, c1, c2);
      if (round < 6) await nextRoundReady(p3, round + 1);
    }
    const o3 = await over3;
    check('un score départagé conclut sans mort subite', !sawSeventh, { sawSeventh });
    check('le vainqueur des six manches remporte le match', Number(o3.winnerSlot) === 1, o3);
    check('le score final est bien de six manches', o3.scores[0] + o3.scores[1] === 6, o3.scores);
  } finally {
    for (const socket of sockets) socket.close();
    server.kill('SIGKILL');
  }

  if (failures) { console.log(`\n${failures} test(s) en échec`); process.exit(1); }
  console.log('\nOK Chifoumi : six manches et mort subite');
}

main().catch(error => { console.error('ERREUR FATALE:', error.message); process.exit(1); });
