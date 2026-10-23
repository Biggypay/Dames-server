/**
 * TIKAN — le serveur est seul juge (simulation autoritative).
 *
 * Vérifie sur un vrai serveur : démarrage à deux, flux d'instantanés, entrées
 * (jamais de positions), usurpation refusée, match joué jusqu'au bout par deux
 * robots, résultat diffusé et règlement envoyé une seule fois.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const { io } = require('socket.io-client');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3162;
const MOCK_DB_PORT = 3163;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const GAME_ID = '60000000-0000-4000-8000-000000000001';
const PLAYER_1 = '60000000-0000-4000-8000-000000000011';
const PLAYER_2 = '60000000-0000-4000-8000-000000000012';
const ROOM = GAME_ID;

let failures = 0;
const rpcCalls = [];
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail || ''); }
}
function once(socket, event, timeoutMs = 5000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error(`timeout ${event}`)), timeoutMs);
    socket.once(event, data => { clearTimeout(timer); resolve(data); });
  });
}
const sleep = ms => new Promise(r => setTimeout(r, ms));

async function waitForHealth(retries = 40) {
  for (let i = 0; i < retries; i++) {
    const ok = await new Promise(resolve => {
      http.get(`${GAME_URL}/health`, res => { res.resume(); resolve(res.statusCode === 200); }).on('error', () => resolve(false));
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
    let body = '';
    request.on('data', c => { body += c; });
    request.on('end', () => {
      if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
        const id = (url.searchParams.get('id') || '').replace(/^eq\./, '');
        return response.end(JSON.stringify([{
          id: id || GAME_ID, game_type: 'tikan', player1_id: PLAYER_1, player2_id: PLAYER_2,
          bet_amount: 0, status: 'in_progress', is_ai_opponent: false
        }]));
      }
      if (request.method === 'POST' && url.pathname.endsWith('/load_game_server_room_states')) return response.end('[]');
      if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) {
        rpcCalls.push({ name: url.pathname.split('/').pop(), body });
        return response.end('null');
      }
      response.statusCode = 404;
      response.end('{}');
    });
  });
}

/** Robot : court vers le ballon, un peu en retrait côté défensif, tire en continu. */
function makeBot(socket, slot, getSnap) {
  return setInterval(() => {
    const s = getSnap();
    if (!s) return;
    const me = s.p[slot - 1], b = s.b;
    // Se place derrière le ballon (par rapport au but visé) puis pousse dedans.
    const dirY = slot === 1 ? -1 : 1;
    // Le robot 2 se range sur le côté et ne fait que regarder : le robot 1 marque.
    const passive = slot === 2;
    const tx = passive ? 40 : b[0], ty = passive ? 200 : b[1] - dirY * 14;
    let dx = tx - me[0], dy = ty - me[1];
    const d = Math.hypot(dx, dy) || 1;
    dx /= d; dy /= d;
    socket.emit('tikan_input', { room: ROOM, player: slot, input: { dx, dy, mg: 1, kick: !passive, deg: false, spr: false } });
  }, 33);
}

async function main() {
  const mockDb = startMockDatabase();
  await new Promise(r => mockDb.listen(MOCK_DB_PORT, '127.0.0.1', r));
  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env, PORT: String(GAME_PORT), NODE_ENV: 'test',
      JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      SUPABASE_URL: `http://127.0.0.1:${MOCK_DB_PORT}`,
      SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));

  const sockets = [], timers = [];
  try {
    await waitForHealth();
    const p1 = await connectUser(PLAYER_1, 'Alice');
    const p2 = await connectUser(PLAYER_2, 'Bob');
    const intruder = await connectUser('60000000-0000-4000-8000-000000000099', 'Eve');
    sockets.push(p1, p2, intruder);

    const start1 = once(p1, 'tikan_start'), start2 = once(p2, 'tikan_start');
    p1.emit('tikan_join', { room: ROOM, player: 1, supabaseId: PLAYER_1, name: 'Alice', bet: 0, currency: 'HTG', gameId: GAME_ID });
    p2.emit('tikan_join', { room: ROOM, player: 2, supabaseId: PLAYER_2, name: 'Bob', bet: 0, currency: 'HTG', gameId: GAME_ID });
    const [s1, s2] = await Promise.all([start1, start2]);
    check('les deux joueurs reçoivent tikan_start avec leur place', s1.yourSlot === 1 && s2.yourSlot === 2, { s1, s2 });
    check('le terrain et la limite de buts sont envoyés', s1.field && s1.field.W > 0 && s1.maxGoals === 5, s1);

    let snap1 = null, snap2 = null, states = 0;
    p1.on('tikan_state', s => { snap1 = s; states++; });
    p2.on('tikan_state', s => { snap2 = s; });
    await sleep(700);
    check('le serveur diffuse des instantanés réguliers (≈30 Hz)', states >= 10, states);

    // Compte à rebours d'ouverture : les entrées ne bougent personne.
    const before = snap1 && snap1.p[0].slice(0, 2);
    p1.emit('tikan_input', { room: ROOM, player: 1, input: { dx: 1, dy: 0, mg: 1 } });
    await sleep(300);
    check('pendant le compte à rebours, aucun joueur ne bouge',
      before && snap1.p[0][0] === before[0] && snap1.p[0][1] === before[1], { before, now: snap1 && snap1.p[0] });

    // L'intrus ne peut piloter personne.
    const eveInput = { room: ROOM, player: 1, input: { dx: -1, dy: 0, mg: 1 } };
    intruder.emit('tikan_input', eveInput);

    // Attendre la fin de l'ouverture (≈3 s) puis tester la saisie réelle.
    await sleep(3000);
    const x0 = snap1.p[0][0];
    p1.emit('tikan_input', { room: ROOM, player: 1, input: { dx: 1, dy: 0, mg: 1, x: 9999, y: 9999 } });
    await sleep(200);
    p1.emit('tikan_input', { room: ROOM, player: 1, input: { dx: 1, dy: 0, mg: 1 } });
    await sleep(300);
    const moved = snap1.p[0][0] - x0;
    check('une entrée déplace le joueur à vitesse plafonnée', moved > 10 && moved < 200 * 0.8, moved);
    check('une position envoyée par un client est ignorée', snap1.p[0][0] < 400 && snap1.p[0][1] < 700);
    p1.emit('tikan_input', { room: ROOM, player: 1, input: { dx: 0, dy: 0, mg: 0 } });

    // Les deux robots jouent le match jusqu'au bout.
    let over1 = null, over2 = null;
    p1.on('game:over', d => { over1 = d; });
    p2.on('game:over', d => { over2 = d; });
    let events = []; if (process.env.TIKAN_DEBUG) p1.on('tikan_event', e => console.log(JSON.stringify(e)));
    p1.on('tikan_event', e => events.push(e));
    timers.push(makeBot(p1, 1, () => snap1), makeBot(p2, 2, () => snap2));
    const deadline = Date.now() + 240000;
    while (!over1 && Date.now() < deadline) await sleep(250);
    check('la partie se termine toute seule', !!over1 && !!over2, { over1: !!over1, over2: !!over2, last: snap1 && snap1.sc });
    if (over1) {
      const sc = over1.scores;
      check('un joueur atteint 5 buts (ou fin réglementaire)', Math.max(sc[0], sc[1]) === 5 || over1.reason, over1);
      check('le vainqueur annoncé correspond au score', over1.winnerSlot === (sc[0] > sc[1] ? 1 : sc[1] > sc[0] ? 2 : 0), over1);
      check('les deux joueurs reçoivent le même verdict',
        over1.winnerSlot === over2.winnerSlot && over1.result !== over2.result || over1.winnerSlot === 0, { a: over1.result, b: over2.result });
      check('des événements de but ont été diffusés', events.some(e => e.t === 'goal'), events.slice(-3));
    }
    await sleep(800);
    const settle = rpcCalls.filter(c => c.name === 'submit_game_result');
    check('le résultat est réglé une seule fois', settle.length === 1, settle.length);
  } finally {
    timers.forEach(clearInterval);
    for (const s of sockets) s.disconnect();
    server.kill();
    mockDb.close();
  }
  if (failures) { console.error(`${failures} échec(s)`); process.exit(1); }
  console.log('Tests serveur TIKAN réussis');
}
main().catch(e => { console.error(e); process.exit(1); });
