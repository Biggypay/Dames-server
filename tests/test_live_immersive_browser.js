/**
 * Le direct « immersif » de l'application — la vraie page spectateur, dans un vrai
 * navigateur, encadrée par une page d'une AUTRE origine (comme sur mindspille.com).
 *
 * L'écran « Live » de l'application pose le plateau en plein écran et dessine
 * lui-même, par-dessus, les deux joueurs, le VS, les commentaires et les boutons.
 * Il demande donc à la page spectateur (`mindspille:layout`, `split` + `hud`) de
 * retirer son propre en-tête, de lui dire ce qu'il contenait (qui joue, le score),
 * et de poser le message de manche et la fiche de fin SOUS ce que l'application
 * couvre (`insetTop`).
 *
 *  1. Sans demande : la page spectateur garde sa vue (une ancienne application).
 *  2. À la demande : l'en-tête s'efface, le plateau gagne la place, ni barre ni aide.
 *  3. Le HUD part vers l'application : joueur 1 à gauche, joueur 2 à droite, celui
 *     qui a la main, le score — et il suit un coup joué.
 *  4. Les marges : `--ms-inset-top` posée, bornée ; le message de manche sous elle.
 *  5. Le spectateur ne peut rien jouer ; aucune exception JavaScript.
 *
 * Les deux joueurs sont deux connexions au serveur (comme `test_dames_draw.js`) :
 * les variables de la page Dames ne sont pas lisibles de l'extérieur, et c'est la
 * page SPECTATEUR que ce test regarde.
 *  6. Retour à la vue normale sur demande.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { io } = require('socket.io-client');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3176;
const PARENT_PORT = 3177;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const PARENT_URL = `http://127.0.0.1:${PARENT_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';

const GAME_ID = '30000000-0000-4000-8000-000000000171';
const P1 = { user: '30000000-0000-4000-8000-000000000181', supabase: '30000000-0000-4000-8000-000000000191', name: 'Alice' };
const P2 = { user: '30000000-0000-4000-8000-000000000182', supabase: '30000000-0000-4000-8000-000000000192', name: 'Bob' };
const VIEWER = { user: '30000000-0000-4000-8000-000000000183', supabase: '30000000-0000-4000-8000-000000000193', name: 'Cara' };

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : detail); }
}
const sleep = ms => new Promise(r => setTimeout(r, ms));

async function waitForHealth(retries = 50) {
  for (let i = 0; i < retries; i++) {
    const ok = await new Promise(resolve => {
      http.get(`${GAME_URL}/health`, res => { res.resume(); resolve(res.statusCode === 200); })
        .on('error', () => resolve(false));
    });
    if (ok) return;
    await sleep(200);
  }
  throw new Error('game server unavailable');
}

const tokenFor = p => jwt.sign({ userId: p.user, supabaseId: p.supabase, username: p.name }, JWT_SECRET);

/* Un joueur : une connexion authentifiée, comme le fait sa page. */
async function joinAs(player, slot) {
  const socket = io(GAME_URL, { transports: ['websocket'], reconnection: false, forceNew: true,
    extraHeaders: { 'x-forwarded-for': `10.81.0.${slot}` } });
  socket.events = [];
  socket.onAny((event, data) => socket.events.push({ event, data }));
  await new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error('timeout connect')), 5000);
    socket.once('connect', () => { clearTimeout(timer); resolve(); });
  });
  socket.emit('auth:supabase', { supabaseId: player.supabase, username: player.name });
  for (let i = 0; i < 50 && !socket.events.some(e => e.event === 'auth:ok'); i++) await sleep(100);
  socket.emit('dames_join', { room: GAME_ID, player: slot, supabaseId: player.supabase, name: player.name, bet: 1000, currency: 'HTG', gameId: GAME_ID });
  return socket;
}
const spectatorUrl = () => `${GAME_URL}/dames?${new URLSearchParams({
  room: GAME_ID, gameId: GAME_ID, spectate: '1', controls: '0', chrome: '0', p1Name: P1.name, p2Name: P2.name
}).toString()}`;

/* La page « application » : elle remet le jeton au plateau, puis demande la mise en page. */
function parentPage(src) {
  return `<!doctype html><html><body style="margin:0;background:#000">
<iframe id="board" src="${src}" style="position:fixed;inset:0;width:100vw;height:100vh;border:0"></iframe>
<script>
window.__messages = [];
var board = document.getElementById('board');
var GAME = ${JSON.stringify(GAME_URL)};
function init() {
  board.contentWindow.postMessage({ type: 'spectator:init', gameId: ${JSON.stringify(GAME_ID)}, token: ${JSON.stringify(tokenFor(VIEWER))},
    player1Name: 'Alice', player2Name: 'Bob', showControls: false }, GAME);
}
window.addEventListener('message', function (e) {
  if (e.origin !== GAME) return;
  window.__messages.push(e.data);
  if (e.data && e.data.type === 'spectator:ready') init();
});
board.addEventListener('load', init);
window.__layout = function (options) {
  board.contentWindow.postMessage(Object.assign({ type: 'mindspille:layout', gameId: ${JSON.stringify(GAME_ID)} }, options), GAME);
};
</script></body></html>`;
}

function startParentAndDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, PARENT_URL);
    if (url.pathname === '/app') {
      response.setHeader('Content-Type', 'text/html; charset=utf-8');
      return response.end(parentPage(url.searchParams.get('src') || ''));
    }
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
      return response.end(JSON.stringify([{
        id: GAME_ID, game_type: 'checkers', player1_id: P1.supabase, player2_id: P2.supabase,
        bet_amount: 1000, status: 'in_progress', is_ai_opponent: false
      }]));
    }
    if (request.method === 'POST' && url.pathname.endsWith('/load_game_server_room_states')) return response.end('[]');
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
    response.statusCode = 404;
    response.end('{}');
  });
}

const view = frame => frame.evaluate(() => {
  const shown = id => { const el = document.getElementById(id); return !!el && getComputedStyle(el).display !== 'none'; };
  const root = document.documentElement;
  return {
    split: root.classList.contains('ms-split'),
    inset: root.classList.contains('ms-inset'),
    insetTop: getComputedStyle(root).getPropertyValue('--ms-inset-top').trim(),
    top: shown('top'), bot: shown('bot'), hint: shown('hint'), forfeit: shown('forfeit-bar'),
    wrapHeight: Math.round(document.getElementById('wrap').getBoundingClientRect().height),
    ready: getComputedStyle(document.getElementById('loading')).display === 'none'
  };
});

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK direct immersif ignoré');
    return;
  }

  const parent = startParentAndDatabase();
  await new Promise(r => parent.listen(PARENT_PORT, '127.0.0.1', r));
  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT), NODE_ENV: 'test', JWT_SECRET,
      SUPABASE_URL: PARENT_URL, SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: `${GAME_URL},${PARENT_URL}`,
      FRAME_ANCESTORS: PARENT_URL
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));

  let browser;
  const sockets = [];
  try {
    await waitForHealth();
    browser = await chromium.launch({ executablePath });
    const newContext = async viewport => {
      const context = await browser.newContext({ viewport });
      if (process.env.THREE_RUNTIME_FILE) {
        await context.route('**/vendor/three-r128.min.js', route =>
          route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
      }
      return context;
    };
    const errors = [];
    const s1 = await joinAs(P1, 1);
    const s2 = await joinAs(P2, 2);
    sockets.push(s1, s2);
    const started = socket => socket.events.some(e => /^dames_(start|game_start|state|game_resumed|turn_start)/.test(e.event));
    for (let i = 0; i < 60 && !(started(s1) && started(s2)); i++) await sleep(150);
    check('le match est lancé entre les deux joueurs', started(s1) && started(s2), s1.events.map(e => e.event));

    // Le spectateur, dans l'application (un téléphone tenu droit).
    const app = await (await newContext({ width: 390, height: 844 })).newPage();
    app.on('pageerror', e => errors.push(`application : ${e.message}`));
    await app.goto(`${PARENT_URL}/app?src=${encodeURIComponent(spectatorUrl())}`);
    const frame = () => app.frames().find(f => f.url().startsWith(`${GAME_URL}/dames`));
    const messages = () => app.evaluate(() => window.__messages.slice());
    for (let i = 0; i < 80; i++) {
      if ((await messages()).some(m => m && m.type === 'spectator:connected')) break;
      await sleep(250);
    }
    check('le spectateur est branché sur le direct', (await messages()).some(m => m && m.type === 'spectator:connected'));
    for (let i = 0; i < 40 && !(frame() && (await view(frame())).ready); i++) await sleep(250);
    await sleep(600);
    const ready = (await messages()).find(m => m && m.type === 'mindspille:layout-ready');
    check('la page spectateur annonce qu elle écoute la mise en page', !!ready && ready.gameId === GAME_ID && ready.spectator === true, ready);

    console.log('1. Sans demande de l application');
    const before = await view(frame());
    check('la page garde son en-tête', before.top && !before.split && !before.inset, before);
    check('aucun HUD n est envoyé', !(await messages()).some(m => m && m.type === 'mindspille:board-hud'));

    console.log('2. L application demande le direct immersif');
    const shots = process.env.LIVE_TEST_SHOTS;
    if (shots) await app.screenshot({ path: path.join(shots, 'spectateur-avant.png') });
    await app.evaluate(() => window.__layout({ split: true, hud: true, insetTop: 164, insetBottom: 72 }));
    await sleep(800);
    const immersive = await view(frame());
    if (shots) await app.screenshot({ path: path.join(shots, 'spectateur-immersif.png') });
    check('l en-tête de la page s efface', immersive.split && !immersive.top, immersive);
    check('ni barre de commandes ni aide au geste', !immersive.bot && !immersive.hint, immersive);
    check('le plateau gagne la place libérée', immersive.wrapHeight > before.wrapHeight + 40, { before: before.wrapHeight, after: immersive.wrapHeight });
    check('le bandeau de forfait reste caché pour un spectateur', !immersive.forfeit, immersive);

    console.log('3. Le HUD part vers l application');
    const hudOf = async () => (await messages()).filter(m => m && m.type === 'mindspille:board-hud').pop();
    let hud = await hudOf();
    check('les deux joueurs, joueur 1 à gauche', !!hud && hud.gameId === GAME_ID && hud.hud && hud.hud.left.name === 'Alice' && hud.hud.right.name === 'Bob', hud && hud.hud);
    check('celui qui a la main est désigné (les Blancs commencent)', !!hud && hud.hud.left.active === true && hud.hud.right.active === false, hud && hud.hud);
    check('le score du centre est lu', !!hud && Array.isArray(hud.hud.score) && hud.hud.score[0] === 20 && hud.hud.score[1] === 20, hud && hud.hud.score);
    // Un coup du joueur 1 : la main passe, le HUD suit.
    // Un coup d'ouverture des Blancs (joueur 1) : 32-28 vu du plateau du serveur.
    const from = { row: 6, col: 1 }, to = { row: 5, col: 2 };
    s1.emit('dames_move', { room: GAME_ID, player: 1, from, to, steps: [{ from, to }] });
    for (let i = 0; i < 30 && !s1.events.some(e => e.event === 'dames_move_ack'); i++) await sleep(100);
    const moved = s1.events.filter(e => /ack|error|reject/.test(e.event)).map(e => e.event);
    let turned = false;
    for (let i = 0; i < 40 && !turned; i++) {
      await sleep(250);
      hud = await hudOf();
      turned = !!hud && hud.hud.right.active === true && hud.hud.left.active === false;
    }
    check('après un coup du joueur 1, la main passe au joueur 2 dans le HUD', turned, { moved, hud: hud && hud.hud });

    console.log('4. Les marges de l application');
    check('la marge du haut est posée', immersive.inset && immersive.insetTop === '164px', immersive);
    const toastTop = await frame().evaluate(() => {
      const toast = document.getElementById('toast');
      if (!toast) return null;
      toast.style.display = 'block';
      toast.style.opacity = '1';
      const top = Math.round(toast.getBoundingClientRect().top);
      toast.style.display = '';
      toast.style.opacity = '';
      return top;
    });
    check('le message de manche se pose sous ce que l application couvre', toastTop === null || toastTop >= 164, toastTop);
    await app.evaluate(() => window.__layout({ split: true, hud: true, insetTop: 99999, insetBottom: -50 }));
    await sleep(300);
    const bounded = await view(frame());
    check('une marge démesurée est bornée (elle vient d une autre origine)', bounded.insetTop === '600px', bounded);
    await app.evaluate(() => window.__layout({ split: true, hud: true, insetTop: 164, insetBottom: 72 }));

    console.log('5. Le spectateur ne joue pas');
    // Une connexion de spectateur qui tente le coup du joueur 2 (au trait) : refusé.
    const intruder = io(GAME_URL, { transports: ['websocket'], reconnection: false, forceNew: true,
      extraHeaders: { 'x-forwarded-for': '10.81.0.9' } });
    sockets.push(intruder);
    await new Promise(resolve => intruder.once('connect', resolve));
    intruder.emit('auth:supabase', { supabaseId: VIEWER.supabase, username: VIEWER.name });
    await sleep(400);
    intruder.emit('spectator_join', { gameId: GAME_ID });
    await sleep(400);
    const movesBefore = s1.events.filter(e => e.event === 'dames_move').length;
    const black = { from: { row: 3, col: 0 }, to: { row: 4, col: 1 } };
    intruder.emit('dames_move', { room: GAME_ID, player: 2, from: black.from, to: black.to, steps: [black] });
    await sleep(900);
    const movesAfter = s1.events.filter(e => e.event === 'dames_move').length;
    check('un coup envoyé par un spectateur ne change pas le plateau', movesBefore === movesAfter, { movesBefore, movesAfter });
    // Le même coup, par le joueur 2 lui-même, passe : le refus tenait bien au spectateur.
    s2.emit('dames_move', { room: GAME_ID, player: 2, from: black.from, to: black.to, steps: [black] });
    for (let i = 0; i < 30 && s1.events.filter(e => e.event === 'dames_move').length === movesAfter; i++) await sleep(100);
    check('le même coup, joué par le joueur 2, est accepté', s1.events.filter(e => e.event === 'dames_move').length === movesAfter + 1);

    console.log('6. Retour à la vue normale');
    await app.evaluate(() => window.__layout({ split: false }));
    await sleep(600);
    const back = await view(frame());
    check('l en-tête revient, les marges sont levées', !back.split && back.top && !back.inset, back);

    check('aucune exception JavaScript', errors.length === 0, errors);
  } finally {
    sockets.forEach(socket => socket.disconnect());
    if (browser) await browser.close();
    server.kill('SIGTERM');
    await new Promise(r => parent.close(r));
  }
  if (failures) process.exitCode = 1;
  else console.log('OK direct immersif');
}

main().catch(error => { console.error(error); process.exitCode = 1; });
