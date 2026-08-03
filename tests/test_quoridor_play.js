// Peut-on encore JOUER au Quoridor ?
//
// Depuis que le serveur valide lui-même les coups, plus aucune partie de
// Quoridor n'est allée au bout : les dernières se sont éteintes en « timeout »
// après quatre-vingt-treize secondes — soit trois secondes d'attente, trente
// secondes de tour et soixante de sursis, sans qu'un seul coup soit joué.
//
// Ce fichier rejoue une partie complète contre le vrai serveur : deux joueurs
// se connectent, avancent leur pion, posent un mur, et tentent les coups qui
// doivent être refusés. Si le serveur refuse un coup légal, le test le dit avec
// le message exact — celui-là même que le joueur voit à l'écran.
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const REPO_ROOT = path.join(__dirname, '..');
const PORT = 3126;
const URL = 'http://127.0.0.1:' + PORT;
const ROOM = 'test-quoridor-room';
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
// Un coup peut être accepté (quoridor_move) ou refusé (game:error). On écoute
// les deux pour pouvoir rapporter le refus au lieu d'expirer bêtement.
//
// Le serveur diffuse chaque coup aux DEUX joueurs : sans filtrer sur le coup
// qu'on vient d'envoyer, on récolterait celui de l'adversaire, encore en file.
function moveOutcome(socket, expected, timeoutMs = 4000) {
  return new Promise((resolve) => {
    const matches = (data) => data
      && data.player === expected.player
      && data.moveType === expected.moveType
      && data.data && data.data.r === expected.r && data.data.c === expected.c;
    const done = (value) => {
      clearTimeout(timer);
      socket.off('quoridor_move', onMove);
      socket.off('game:error', onError);
      resolve(value);
    };
    const timer = setTimeout(() => done({ outcome: 'silence' }), timeoutMs);
    const onMove = (data) => { if (matches(data)) done({ outcome: 'accepte', data }); };
    const onError = (data) => done({ outcome: 'refuse', message: data && data.message });
    socket.on('quoridor_move', onMove);
    socket.on('game:error', onError);
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
async function connectPlayer(supabaseId, name) {
  const s = io(URL, { transports: ['websocket'], reconnection: false });
  await once(s, 'connect');
  s.emit('auth:supabase', { supabaseId, username: name });
  await once(s, 'auth:ok');
  return s;
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
  server.stderr.on('data', d => { const s = String(d); if (!s.includes('JWT_SECRET')) process.stderr.write('[server] ' + s); });

  try {
    await waitHealth();
    console.log('Serveur démarré.');

    const p1 = await connectPlayer('test-quoridor-aaa', 'Alice');
    const p2 = await connectPlayer('test-quoridor-bbb', 'Bob');

    console.log('\n— Démarrage —');
    const start1 = once(p1, 'quoridor_start');
    const start2 = once(p2, 'quoridor_start');
    p1.emit('quoridor_join', { room: ROOM, player: 1, supabaseId: 'test-quoridor-aaa', name: 'Alice', bet: 0, currency: 'HTG' });
    await sleep(150);
    p2.emit('quoridor_join', { room: ROOM, player: 2, supabaseId: 'test-quoridor-bbb', name: 'Bob', bet: 0, currency: 'HTG' });
    const [s1, s2] = await Promise.all([start1, start2]);
    check('P1 reçoit quoridor_start slot 1', s1.yourSlot === 1, s1);
    check('P2 reçoit quoridor_start slot 2', s2.yourSlot === 2, s2);

    // Le pion 1 part de (8,4) et vise la rangée 0 ; le pion 2 part de (0,4).
    console.log('\n— Premier coup : P1 avance de (8,4) vers (7,4) —');
    const first = moveOutcome(p1, { player: 1, moveType: 'move', r: 7, c: 4 });
    p1.emit('quoridor_move', { room: ROOM, player: 1, moveType: 'move', data: { r: 7, c: 4 } });
    const firstResult = await first;
    check('Le serveur accepte le premier coup légal', firstResult.outcome === 'accepte', firstResult);
    if (firstResult.outcome === 'accepte') {
      const state = JSON.parse(firstResult.data.gameState);
      check('Le pion 1 a bien avancé', state.s1Pos.r === 7 && state.s1Pos.c === 4, state.s1Pos);
      check('La main passe au joueur 2', firstResult.data.nextPlayer === 1, firstResult.data.nextPlayer);
      check('La version d\'état est incrémentée', firstResult.data.version === 1, firstResult.data.version);
    }

    console.log('\n— P2 répond : (0,4) vers (1,4) —');
    const second = moveOutcome(p2, { player: 2, moveType: 'move', r: 1, c: 4 });
    p2.emit('quoridor_move', { room: ROOM, player: 2, moveType: 'move', data: { r: 1, c: 4 } });
    const secondResult = await second;
    check('Le serveur accepte la réponse de P2', secondResult.outcome === 'accepte', secondResult);

    console.log('\n— P1 pose un mur horizontal en (4,4) —');
    const wall = moveOutcome(p1, { player: 1, moveType: 'wallH', r: 4, c: 4 });
    p1.emit('quoridor_move', { room: ROOM, player: 1, moveType: 'wallH', data: { r: 4, c: 4 } });
    const wallResult = await wall;
    check('Le serveur accepte un mur légal', wallResult.outcome === 'accepte', wallResult);
    if (wallResult.outcome === 'accepte') {
      const state = JSON.parse(wallResult.data.gameState);
      check('Le mur est posé', state.hW[4][4] === true);
      check('Le stock de murs de P1 diminue', state.s1Walls === 9, state.s1Walls);
    }

    console.log('\n— Ce qui doit être refusé —');
    const outOfTurn = moveOutcome(p1, { player: 1, moveType: 'move', r: 6, c: 4 });
    p1.emit('quoridor_move', { room: ROOM, player: 1, moveType: 'move', data: { r: 6, c: 4 } });
    const outOfTurnResult = await outOfTurn;
    check('Un coup hors tour est refusé', outOfTurnResult.outcome === 'refuse', outOfTurnResult);

    const teleport = moveOutcome(p2, { player: 2, moveType: 'move', r: 7, c: 0 });
    p2.emit('quoridor_move', { room: ROOM, player: 2, moveType: 'move', data: { r: 7, c: 0 } });
    const teleportResult = await teleport;
    check('Un déplacement impossible est refusé', teleportResult.outcome === 'refuse', teleportResult);

    [p1, p2].forEach(s => s.disconnect());
  } catch (error) {
    failures++;
    console.log('  ❌ Exception : ' + error.message);
  } finally {
    server.kill('SIGTERM');
  }

  console.log(failures === 0 ? '\nOK Quoridor : une partie se joue de bout en bout' : `\n${failures} échec(s)`);
  process.exit(failures === 0 ? 0 : 1);
}

main();
