/**
 * Morpion à cinq (Gomoku) — le serveur est seul juge.
 *
 * Ce jeu se joue pour de l'argent réel : un plateau incohérent entre les deux
 * écrans, ou un coup accepté hors tour, se traduirait directement par un
 * escrow réglé au mauvais joueur. Les tests ci-dessous vérifient donc que le
 * serveur, et lui seul, décide de ce qui est jouable et de qui gagne.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3142;
const MOCK_DB_PORT = 3143;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const GAME_ID = '20000000-0000-4000-8000-000000000001';
const PLAYER_1 = '20000000-0000-4000-8000-000000000011';
const PLAYER_2 = '20000000-0000-4000-8000-000000000012';
const ROOM = GAME_ID;

let failures = 0;

function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else {
    failures++;
    console.error(`  FAIL ${label}`, detail || '');
  }
}

function once(socket, event, timeoutMs = 5000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error(`timeout ${event}`)), timeoutMs);
    socket.once(event, data => { clearTimeout(timer); resolve(data); });
  });
}

const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));

async function waitForHealth(retries = 40) {
  for (let attempt = 0; attempt < retries; attempt++) {
    const ok = await new Promise(resolve => {
      http.get(`${GAME_URL}/health`, response => {
        response.resume();
        resolve(response.statusCode === 200);
      }).on('error', () => resolve(false));
    });
    if (ok) return;
    await sleep(200);
  }
  throw new Error('game server unavailable');
}

async function connectUser(supabaseId, username) {
  const socket = io(GAME_URL, { transports: ['websocket'], reconnection: false });
  await once(socket, 'connect');
  socket.emit('auth:supabase', { supabaseId, username });
  await once(socket, 'auth:ok');
  return socket;
}

function startMockDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, `http://127.0.0.1:${MOCK_DB_PORT}`);
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
      const requestedId = (url.searchParams.get('id') || '').replace(/^eq\./, '');
      return response.end(JSON.stringify([{
        id: requestedId || GAME_ID,
        game_type: 'gomoku',
        player1_id: PLAYER_1,
        player2_id: PLAYER_2,
        bet_amount: 0,
        status: 'in_progress',
        is_ai_opponent: false
      }]));
    }
    if (request.method === 'POST' && url.pathname.endsWith('/load_game_server_room_states')) {
      return response.end('[]');
    }
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) {
      return response.end('null');
    }
    response.statusCode = 404;
    response.end('{}');
  });
}

/**
 * Le serveur diffuse chaque coup à TOUTE la room : les deux sockets reçoivent
 * donc le même événement. Attendre « le prochain gomoku_move » est alors une
 * course perdue d'avance — on attend le coup précis qu'on vient de jouer.
 */
function onceMatching(socket, event, predicate, timeoutMs = 5000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      socket.off(event, handler);
      reject(new Error(`timeout ${event}`));
    }, timeoutMs);
    function handler(data) {
      if (!predicate(data)) return;
      clearTimeout(timer);
      socket.off(event, handler);
      resolve(data);
    }
    socket.on(event, handler);
  });
}

/** Joue un coup et attend la diffusion serveur de CE coup. */
async function play(socket, listenOn, player, r, c) {
  const broadcast = onceMatching(listenOn, 'gomoku_move',
    d => d && d.player === player && d.data && d.data.r === r && d.data.c === c);
  socket.emit('gomoku_move', { room: ROOM, player, data: { r, c } });
  return broadcast;
}

async function main() {
  const mockDb = startMockDatabase();
  await new Promise(resolve => mockDb.listen(MOCK_DB_PORT, '127.0.0.1', resolve));
  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT),
      NODE_ENV: 'test',
      JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      SUPABASE_URL: `http://127.0.0.1:${MOCK_DB_PORT}`,
      SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', data => process.stderr.write(String(data)));

  const sockets = [];
  try {
    await waitForHealth();
    const p1 = await connectUser(PLAYER_1, 'Alice');
    const p2 = await connectUser(PLAYER_2, 'Bob');
    sockets.push(p1, p2);

    const start1 = once(p1, 'gomoku_start');
    const start2 = once(p2, 'gomoku_start');
    p1.emit('gomoku_join', { room: ROOM, player: 1, supabaseId: PLAYER_1, name: 'Alice', bet: 0, currency: 'HTG', gameId: GAME_ID });
    p2.emit('gomoku_join', { room: ROOM, player: 2, supabaseId: PLAYER_2, name: 'Bob', bet: 0, currency: 'HTG', gameId: GAME_ID });
    const [s1, s2] = await Promise.all([start1, start2]);
    check('les deux joueurs reçoivent gomoku_start', s1.yourSlot === 1 && s2.yourSlot === 2, { s1, s2 });

    // Le slot 1 ouvre : jouer hors tour ne doit rien produire.
    const outOfTurn = once(p2, 'game:error', 2500).catch(() => null);
    p2.emit('gomoku_move', { room: ROOM, player: 2, data: { r: 0, c: 0 } });
    const refusal = await outOfTurn;
    check('un coup hors tour est refusé', !!refusal, refusal);

    // Alignement horizontal du slot 1 en ligne 7, colonnes 3..7.
    // Le slot 2 répond loin de là pour ne pas bloquer.
    let last = null;
    for (let step = 0; step < 4; step++) {
      last = await play(p1, p1, 1, 7, 3 + step);
      check(`coup ${step + 1} du slot 1 diffusé`, last && last.player === 1, last);
      const reply = await play(p2, p2, 2, 0, step);
      check(`réponse ${step + 1} du slot 2 diffusée`, reply && reply.player === 2, reply);
    }

    // Case déjà occupée : refus, sans altérer le plateau.
    const occupied = once(p1, 'game:error', 2500).catch(() => null);
    p1.emit('gomoku_move', { room: ROOM, player: 1, data: { r: 7, c: 3 } });
    check('une case occupée est refusée', !!(await occupied));

    // Cinquième pion : victoire du slot 1.
    const over1 = once(p1, 'game:over');
    const over2 = once(p2, 'game:over');
    const winningBroadcast = onceMatching(p1, 'gomoku_move',
      d => d && d.player === 1 && d.data && d.data.r === 7 && d.data.c === 7);
    p1.emit('gomoku_move', { room: ROOM, player: 1, data: { r: 7, c: 7 } });
    const winMove = await winningBroadcast;
    check('le serveur renvoie la ligne gagnante', Array.isArray(winMove.winLine) && winMove.winLine.length === 5, winMove.winLine);

    const [end1, end2] = await Promise.all([over1, over2]);
    check('le slot 1 est déclaré vainqueur', end1.winnerSlot === 1 && end1.result === 'win', end1);
    check('le slot 2 est déclaré perdant', end2.winnerSlot === 1 && end2.result === 'loss', end2);
    check('la partie se règle en une seule manche', end1.reason === 'normal', end1.reason);

    // Une fois la partie finie, plus aucun coup n'est accepté.
    const afterEnd = once(p2, 'gomoku_move', 1500).catch(() => null);
    p2.emit('gomoku_move', { room: ROOM, player: 2, data: { r: 5, c: 5 } });
    check('aucun coup n’est accepté après la fin', !(await afterEnd));
  } finally {
    for (const socket of sockets) socket.disconnect();
    server.kill('SIGKILL');
    await new Promise(resolve => mockDb.close(resolve));
  }

  if (failures) {
    console.error(`FAIL ${failures} vérification(s) Gomoku`);
    process.exit(1);
  }
  console.log('OK tests Gomoku passés');
}

main().catch(error => {
  console.error(error);
  process.exit(1);
});
