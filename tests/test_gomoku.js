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

    // Le serveur tire le premier joueur. Le protocole doit fonctionner quel
    // que soit le slot gagnant du tirage, pas seulement quand le slot 1 ouvre.
    const openingSlot = s1.currentSlot;
    check('le premier joueur est tiré par le serveur et synchronisé',
      (openingSlot === 1 || openingSlot === 2) && s2.currentSlot === openingSlot,
      { s1, s2 });
    const opener = openingSlot === 1 ? p1 : p2;
    const responder = openingSlot === 1 ? p2 : p1;
    const responderSlot = openingSlot === 1 ? 2 : 1;

    // Jouer hors tour ne doit rien produire.
    const outOfTurn = once(responder, 'game:error', 2500).catch(() => null);
    responder.emit('gomoku_move', { room: ROOM, player: responderSlot, data: { r: 0, c: 0 } });
    const refusal = await outOfTurn;
    check('un coup hors tour est refusé', !!refusal, refusal);

    // L'ouvreur aligne cinq pions en ligne 7. L'autre répond loin de là pour
    // ne pas bloquer, ce qui valide aussi le cas où le slot 2 commence.
    let last = null;
    for (let step = 0; step < 4; step++) {
      last = await play(opener, opener, openingSlot, 7, 3 + step);
      check(`coup ${step + 1} de l'ouvreur diffusé`, last && last.player === openingSlot, last);
      const reply = await play(responder, responder, responderSlot, 0, step);
      check(`réponse ${step + 1} de l'adversaire diffusée`, reply && reply.player === responderSlot, reply);
    }

    // Case déjà occupée : refus, sans altérer le plateau.
    const occupied = once(opener, 'game:error', 2500).catch(() => null);
    opener.emit('gomoku_move', { room: ROOM, player: openingSlot, data: { r: 7, c: 3 } });
    check('une case occupée est refusée', !!(await occupied));

    // ── Le match se joue en 6 manches : gagner une manche ne doit JAMAIS
    // déclencher game:over/le règlement du portefeuille. On vérifie ça en
    // gardant un espion actif sur toute la durée du test.
    let prematureGameOver = false;
    p1.on('game:over', () => { prematureGameOver = true; });
    p2.on('game:over', () => { prematureGameOver = true; });

    const winnerSlot = openingSlot, loserSlot = openingSlot === 1 ? 2 : 1;
    const winnerSocket = opener, loserSocket = responder;

    async function playRoundToWin(starterIsWinner) {
      const wCols = [3, 4, 5, 6, 7];
      const lCols = [0, 2, 4, 6, 8];
      let wi = 0, li = 0;
      const totalMoves = starterIsWinner ? 9 : 10;
      let turn = starterIsWinner ? 'W' : 'L';
      let winMove = null;
      for (let i = 0; i < totalMoves; i++) {
        if (turn === 'W') {
          const c = wCols[wi++];
          const isLast = wi === wCols.length;
          const bcast = onceMatching(winnerSocket, 'gomoku_move',
            d => d && d.player === winnerSlot && d.data && d.data.r === 7 && d.data.c === c);
          winnerSocket.emit('gomoku_move', { room: ROOM, player: winnerSlot, data: { r: 7, c } });
          const move = await bcast;
          if (isLast) winMove = move;
          turn = 'L';
        } else {
          const c = lCols[li++];
          const bcast = onceMatching(loserSocket, 'gomoku_move',
            d => d && d.player === loserSlot && d.data && d.data.r === 0 && d.data.c === c);
          loserSocket.emit('gomoku_move', { room: ROOM, player: loserSlot, data: { r: 0, c } });
          await bcast;
          turn = 'W';
        }
      }
      return winMove;
    }

    const roundEnd1a = once(p1, 'gomoku_round_end');
    const roundEnd1b = once(p2, 'gomoku_round_end');
    const winningBroadcast = onceMatching(opener, 'gomoku_move',
      d => d && d.player === openingSlot && d.data && d.data.r === 7 && d.data.c === 7);
    opener.emit('gomoku_move', { room: ROOM, player: openingSlot, data: { r: 7, c: 7 } });
    const winMove = await winningBroadcast;
    check('le serveur renvoie la ligne gagnante', Array.isArray(winMove.winLine) && winMove.winLine.length === 5, winMove.winLine);

    const [re1a, re1b] = await Promise.all([roundEnd1a, roundEnd1b]);
    check('manche 1 : le vainqueur de la manche est annoncé', re1a.roundWinner === winnerSlot, re1a);
    check('manche 1 : la série indique 1 manche jouée sur 6', re1a.series.roundsPlayed === 1 && re1a.series.regularRounds === 6, re1a.series);
    check('manche 1 : le score reflète la victoire', re1a.series.wins[winnerSlot] === 1 && re1a.series.wins[loserSlot] === 0, re1a.series);
    check('manche 1 : le match continue (pas de fin de série)', re1a.series.roundsPlayed < re1a.series.regularRounds);

    const roundStart2a = once(p1, 'gomoku_round_start');
    const roundStart2b = once(p2, 'gomoku_round_start');
    const [rs2a, rs2b] = await Promise.all([roundStart2a, roundStart2b]);
    check('manche 2 : le plateau est réinitialisé et les deux joueurs sont resynchronisés',
      rs2a.currentSlot === rs2b.currentSlot && (rs2a.currentSlot === 1 || rs2a.currentSlot === 2), { rs2a, rs2b });
    check('manche 2 : le joueur qui commence alterne', rs2a.currentSlot === loserSlot, rs2a.currentSlot);

    for (let round = 2; round <= 4; round++) {
      const starterIsWinner = (round % 2 === 1);
      const roundEndA = once(p1, 'gomoku_round_end');
      const roundEndB = once(p2, 'gomoku_round_end');
      await playRoundToWin(starterIsWinner);
      const [reA] = await Promise.all([roundEndA, roundEndB]);
      check(`manche ${round} : le vainqueur est annoncé`, reA.roundWinner === winnerSlot, reA);
      check(`manche ${round} : le score de la série est correct`, reA.series.wins[winnerSlot] === round && reA.series.wins[loserSlot] === 0, reA.series);
      if (round < 4) {
        const rsA = once(p1, 'gomoku_round_start');
        const rsB = once(p2, 'gomoku_round_start');
        await Promise.all([rsA, rsB]);
      }
    }

    check('aucun game:over prématuré pendant les manches 1 à 4', !prematureGameOver);
    const over1 = once(p1, 'game:over');
    const over2 = once(p2, 'game:over');
    const [end1, end2] = await Promise.all([over1, over2]);
    check('la série est gagnée par le joueur qui a mené 4 manches à 0',
      end1.winnerSlot === winnerSlot && end1.result === (winnerSlot === 1 ? 'win' : 'loss'), end1);
    check('l’adversaire est déclaré perdant de la série', end2.winnerSlot === winnerSlot && end2.result === (winnerSlot === 2 ? 'win' : 'loss'), end2);

    const afterEnd = once(responder, 'gomoku_move', 1500).catch(() => null);
    responder.emit('gomoku_move', { room: ROOM, player: responderSlot, data: { r: 5, c: 5 } });
    check('aucun coup n’est accepté après la fin de la série', !(await afterEnd));
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
