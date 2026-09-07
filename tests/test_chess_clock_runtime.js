'use strict';

// La pendule 10+5 vue du vrai serveur, avec une base de données simulée.
//
// La cadence n'arrive JAMAIS du navigateur : le serveur la lit dans
// `games.game_settings.chess_time_control` avec sa clé de service. Ce test
// monte donc un faux PostgREST qui sert exactement cette ligne, puis vérifie
// sur de vrais sockets ce que les joueurs verront :
//   • 10:00 à l'ouverture du plateau, pour les deux camps ;
//   • le temps de réflexion facturé et l'incrément rendu après un coup validé ;
//   • une reconnexion qui ne remet rien à zéro ;
//   • un drapeau qui tombe et donne la victoire à l'adversaire.

const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const ROOT = path.join(__dirname, '..');
const PORT = 3141;
const DB_PORT = 3142;
const URL = 'http://127.0.0.1:' + PORT;

const P1 = '11111111-1111-4111-8111-111111111111';
const P2 = '22222222-2222-4222-8222-222222222222';

let failures = 0;
function check(label, cond, detail) {
  if (cond) console.log('  ✅ ' + label);
  else {
    failures++;
    console.log('  ❌ ' + label + (detail !== undefined ? ' → ' + JSON.stringify(detail) : ''));
  }
}
function once(socket, event, timeoutMs = 8000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error('timeout: ' + event)), timeoutMs);
    socket.once(event, (data) => { clearTimeout(timer); resolve(data); });
  });
}
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const sq = (alg) => ({ row: 8 - parseInt(alg[1], 10), col: 'abcdefgh'.indexOf(alg[0]) });

function waitHealth(retries = 60) {
  return new Promise((resolve, reject) => {
    const attempt = (left) => {
      http.get(URL + '/health', (res) => { res.resume(); res.statusCode === 200 ? resolve() : retry(left); })
        .on('error', () => retry(left));
    };
    const retry = (left) => (left <= 0 ? reject(new Error('serveur injoignable')) : setTimeout(() => attempt(left - 1), 250));
    attempt(retries);
  });
}

/** Faux PostgREST : une seule partie d'échecs, avec sa cadence officielle. */
function startFakeDatabase(games) {
  const server = http.createServer((req, res) => {
    let body = '';
    req.on('data', (chunk) => { body += chunk; });
    req.on('end', () => {
      res.setHeader('Content-Type', 'application/json');
      if (req.url.startsWith('/rest/v1/games')) {
        const id = decodeURIComponent((req.url.match(/id=eq\.([^&]+)/) || [])[1] || '');
        return res.end(JSON.stringify(games.has(id) ? [games.get(id)] : []));
      }
      if (req.url.startsWith('/rest/v1/rpc/load_game_server_room_states')) return res.end('[]');
      if (req.url.startsWith('/rest/v1/rpc/')) return res.end('null');
      res.statusCode = 404;
      res.end('[]');
    });
  });
  return new Promise((resolve) => server.listen(DB_PORT, '127.0.0.1', () => resolve(server)));
}

function makeGame(id, timeControl) {
  return {
    id,
    game_type: 'chess',
    player1_id: P1,
    player2_id: P2,
    bet_amount: 0,
    status: 'in_progress',
    is_ai_opponent: false,
    is_tournament: true,
    game_settings: { chess_time_control: timeControl }
  };
}

async function connectPlayer(supabaseId, name) {
  const socket = io(URL, { transports: ['websocket'], reconnection: false });
  await once(socket, 'connect');
  socket.emit('auth:supabase', { supabaseId, username: name });
  await once(socket, 'auth:ok');
  return socket;
}

async function seat(room, timeControlGames) {
  const white = await connectPlayer(P1, 'Blanc');
  const black = await connectPlayer(P2, 'Noir');
  const start1 = once(white, 'echecs_start');
  const start2 = once(black, 'echecs_start');
  white.emit('echecs_join', { room, player: 1, supabaseId: P1, name: 'Blanc', bet: 0, currency: 'HTG', gameId: room });
  await once(white, 'echecs_joined');
  black.emit('echecs_join', { room, player: 2, supabaseId: P2, name: 'Noir', bet: 0, currency: 'HTG', gameId: room });
  await once(black, 'echecs_joined');
  return { white, black, starts: await Promise.all([start1, start2]) };
}

async function main() {
  const NORMAL = '33333333-3333-4333-8333-333333333333';
  const FAST = '44444444-4444-4444-8444-444444444444';
  const games = new Map([
    [NORMAL, makeGame(NORMAL, { base_seconds: 600, white_seconds: 600, black_seconds: 600, increment_seconds: 5, label: '10+5', armageddon: false })],
    [FAST, makeGame(FAST, { base_seconds: 2, white_seconds: 2, black_seconds: 2, increment_seconds: 0, label: '0+0', armageddon: false })]
  ]);
  const database = await startFakeDatabase(games);

  const server = spawn('node', ['server.js'], {
    cwd: ROOT,
    env: {
      ...process.env,
      PORT: String(PORT),
      NODE_ENV: 'test',
      SUPABASE_URL: 'http://127.0.0.1:' + DB_PORT,
      SUPABASE_SERVICE_ROLE_KEY: 'test-service-role-key',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app',
      FRAME_ANCESTORS: 'https://mindspille.lovable.app'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stdout.on('data', () => {});
  server.stderr.on('data', (d) => { const line = String(d).trim(); if (line) console.log('[server] ' + line); });

  const sockets = [];
  try {
    await waitHealth();

    console.log('— 10+5 : la cadence vient de la base, pas du navigateur —');
    const room = await seat(NORMAL, games);
    sockets.push(room.white, room.black);
    const [startWhite, startBlack] = room.starts;
    check('les deux plateaux ouvrent à 10:00',
      startWhite.clock?.white === 600000 && startWhite.clock?.black === 600000
      && startBlack.clock?.white === 600000, startWhite.clock);
    check('la cadence officielle est annoncée', startWhite.clock?.label === '10+5', startWhite.clock);
    check('aucune pendule ne tourne avant le coup d’envoi', startWhite.clock?.runningSlot === null, startWhite.clock);

    const firstTurn = await once(room.white, 'echecs_turn_start', 9000);
    check('le trait revient aux Blancs', firstTurn.player === 1, firstTurn);
    check('le tour dure tout le temps restant, pas 30 s',
      firstTurn.clock === true && firstTurn.duration > 590000, firstTurn);

    console.log('— Un coup validé : le temps se paie, l’incrément se rend —');
    await sleep(1200);
    const clockAfterMove = once(room.white, 'echecs_clock');
    room.white.emit('echecs_move', { room: NORMAL, player: 1, from: sq('e2'), to: sq('e4'), promo: 0 });
    const clock = await clockAfterMove;
    check('les Blancs ont payé leur réflexion et reçu +5 s',
      clock.white > 600000 - 3000 + 5000 && clock.white <= 605000, clock);
    check('la pendule des Noirs est intacte', clock.black === 600000, clock);
    check('c’est aux Noirs de jouer', clock.runningSlot === 2, clock);

    console.log('— Reconnexion : rien n’est remis à zéro —');
    const whiteBefore = clock.white;
    room.white.disconnect();
    await sleep(400);
    const back = await connectPlayer(P1, 'Blanc');
    sockets.push(back);
    const resumed = once(back, 'echecs_start');
    back.emit('echecs_join', { room: NORMAL, player: 1, supabaseId: P1, name: 'Blanc', bet: 0, currency: 'HTG', gameId: NORMAL });
    const restored = await resumed;
    check('le temps des Blancs est retrouvé à l’identique',
      restored.clock?.white === whiteBefore, { attendu: whiteBefore, obtenu: restored.clock?.white });
    check('les Noirs n’ont pas perdu leur temps non plus',
      restored.clock?.black <= 600000 && restored.clock?.black > 590000, restored.clock);
    check('les couleurs n’ont pas bougé', restored.yourSlot === 1, restored);

    console.log('— Drapeau tombé : l’adversaire l’emporte —');
    const fast = await seat(FAST, games);
    sockets.push(fast.white, fast.black);
    check('pendule courte chargée depuis la base', fast.starts[0].clock?.white === 2000, fast.starts[0].clock);
    const over = await once(fast.black, 'game:over', 12000);
    check('la partie se termine au temps', over.reason === 'timeout', over);
    check('les Noirs gagnent quand les Blancs tombent', over.winnerSlot === 2, over);
  } catch (error) {
    failures++;
    console.log('  ❌ exception : ' + error.message);
  } finally {
    for (const socket of sockets) { try { socket.disconnect(); } catch { /* déjà fermé */ } }
    server.kill('SIGKILL');
    database.close();
  }

  console.log(failures === 0 ? '\n✅ Pendule d’échecs (serveur) : tous les tests passent' : `\n❌ ${failures} test(s) en échec`);
  process.exit(failures === 0 ? 0 : 1);
}

main();
