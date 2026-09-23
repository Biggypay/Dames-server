/**
 * Ce que le plateau échange avec l'application, dans un vrai navigateur.
 *
 * 1. Messagerie de partie (sept pages en ligne). Le bouton du plateau doit
 *    rester invisible tant que l'application ne l'a pas demandé, puis
 *    apparaître à sa place — deuxième de la barre du bas, juste après la vue
 *    (après « Déplacer » au Quoridor, en tête de barre au Morpion à cinq,
 *    flottant au Penalty et au Chifoumi qui n'ont pas de barre) — sans
 *    chevaucher ses voisins ni sortir de l'écran. Il affiche le nombre de
 *    messages non lus, signale le clic à l'application, et passe à l'état
 *    « ouvert » quand elle le dit.
 *
 * 2. Entraînement contre l'IA et partie entre amis (quatorze pages). En écran
 *    partagé, l'en-tête quitte le plateau comme en ligne, et son contenu —
 *    joueurs, main, score — part vers le panneau de l'application.
 *
 * Chaque page est chargée dans une iframe d'une AUTRE origine, comme sur
 * mindspille.com, et aucune ne doit lever d'exception.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3202;
const PARENT_PORT = 3203;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const PARENT_URL = `http://127.0.0.1:${PARENT_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';
const P1 = { user: '30000000-0000-4000-8000-000000000381', supabase: '30000000-0000-4000-8000-000000000391', name: 'Alice' };
const P2 = { user: '30000000-0000-4000-8000-000000000382', supabase: '30000000-0000-4000-8000-000000000392', name: 'Bob' };

const ONLINE = [
  { key: 'dames', route: '/dames', type: 'checkers', slot: 'after-view', id: '30000000-0000-4000-8000-000000000301' },
  { key: 'echecs', route: '/echecs', type: 'chess', slot: 'after-view', id: '30000000-0000-4000-8000-000000000302' },
  { key: 'tictactoe', route: '/ttt', type: 'tictactoe', slot: 'after-view', id: '30000000-0000-4000-8000-000000000303' },
  { key: 'gomoku', route: '/gomoku', type: 'gomoku', slot: 'bar-start', id: '30000000-0000-4000-8000-000000000304' },
  { key: 'quoridor', route: '/quoridor', type: 'quoridor', slot: 'after-move', id: '30000000-0000-4000-8000-000000000305' },
  { key: 'penalty', route: '/penalty', type: 'penalty_shootout', slot: 'floating', id: '30000000-0000-4000-8000-000000000306' },
  { key: 'chifoumi', route: '/chifoumi', type: 'rock_paper_scissors', slot: 'floating', id: '30000000-0000-4000-8000-000000000307' }
];
const OFFLINE = ['dames', 'echecs', 'ttt', 'gomoku', 'quoridor', 'penalty', 'chifoumi'].flatMap(game => [
  { key: `${game} IA`, route: `/${game}-ai?difficulty=medium&name=Alice` },
  { key: `${game} ami`, route: `/${game}-local?name=Joueur%201&p2Name=Joueur%202` }
]);

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : detail); }
}
const sleep = ms => new Promise(r => setTimeout(r, ms));
async function waitFor(fn, timeoutMs = 8000, stepMs = 150) {
  const end = Date.now() + timeoutMs;
  let value;
  while (Date.now() < end) {
    try { value = await fn(); } catch (_) { value = undefined; }
    if (value) return value;
    await sleep(stepMs);
  }
  return value;
}

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

const token = p => jwt.sign({ userId: p.user, supabaseId: p.supabase, username: p.name }, JWT_SECRET);
function onlineUrl(game, slot = 1) {
  const params = new URLSearchParams({
    room: game.id, gameId: game.id, player: String(slot),
    p1Id: P1.supabase, p2Id: P2.supabase, p1Name: P1.name, p2Name: P2.name, bet: '500', currency: 'HTG'
  });
  return `${GAME_URL}${game.route}?${params}#${new URLSearchParams({ token: token(slot === 1 ? P1 : P2) })}`;
}

/* L'« application » : une autre origine, qui encadre le plateau et note tout
   ce qu'il lui envoie. */
function parentPage(src) {
  return `<!doctype html><html><body style="margin:0;background:#111">
<iframe id="board" src="${src}" style="width:100vw;height:100vh;border:0"></iframe>
<script>
window.__messages = [];
window.addEventListener('message', function (e) {
  if (e.origin !== ${JSON.stringify(GAME_URL)}) return;
  window.__messages.push(e.data);
});
window.__send = function (message) {
  document.getElementById('board').contentWindow.postMessage(message, ${JSON.stringify(GAME_URL)});
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
      const id = String(url.searchParams.get('id') || '').replace(/^eq\./, '');
      const game = ONLINE.find(g => g.id === id);
      return response.end(JSON.stringify(game ? [{
        id: game.id, game_type: game.type, player1_id: P1.supabase, player2_id: P2.supabase,
        bet_amount: 500, status: 'in_progress', is_ai_opponent: false
      }] : []));
    }
    if (request.method === 'POST' && url.pathname.endsWith('/load_game_server_room_states')) return response.end('[]');
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
    response.statusCode = 404;
    response.end('{}');
  });
}

async function openFramed(browser, src, viewport) {
  const context = await browser.newContext({ viewport });
  if (process.env.THREE_RUNTIME_FILE) {
    await context.route('**/vendor/three-r128.min.js', route =>
      route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
  }
  const page = await context.newPage();
  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  page.on('response', r => {
    if (r.url().startsWith(GAME_URL) && r.status() >= 400) errors.push(`HTTP ${r.status()} ${r.url().slice(GAME_URL.length).split('?')[0]}`);
  });
  await page.goto(`${PARENT_URL}/app?src=${encodeURIComponent(src)}`);
  const frame = await waitFor(() => page.frames().find(f => f.url().startsWith(GAME_URL)), 8000);
  const messages = () => page.evaluate(() => window.__messages.slice());
  const send = message => page.evaluate(m => window.__send(m), message);
  return { page, frame, errors, messages, send, close: () => context.close() };
}

const chatButton = frame => frame.evaluate(() => {
  const button = document.querySelector('.ms-chat-btn');
  if (!button) return null;
  const rect = button.getBoundingClientRect();
  const style = getComputedStyle(button);
  const badge = button.querySelector('.ms-chat-badge');
  const bar = document.getElementById('bot');
  const prev = button.previousElementSibling;
  const inBar = button.closest('#bot');
  const neighbours = [...(inBar ? inBar.querySelectorAll('button') : [])]
    .filter(b => b !== button && getComputedStyle(b).display !== 'none')
    .map(b => b.getBoundingClientRect())
    .filter(r => r.width > 0);
  /* Un libellé coupé (« DÉPLACEF ») compte comme un chevauchement. */
  const clipped = [...(inBar ? inBar.querySelectorAll('button') : [])]
    .filter(b => getComputedStyle(b).display !== 'none')
    .filter(b => b.scrollWidth > b.clientWidth + 1).map(b => b.id || b.className);
  const outside = [...(inBar ? inBar.querySelectorAll('button') : [])]
    .filter(b => getComputedStyle(b).display !== 'none')
    .filter(b => { const r = b.getBoundingClientRect(); return r.left < 0 || r.right > innerWidth; }).map(b => b.id || b.className);
  const overlaps = neighbours.some(r => !(r.right <= rect.left + 1 || r.left >= rect.right - 1 || r.bottom <= rect.top + 1 || r.top >= rect.bottom - 1));
  return {
    visible: style.display !== 'none' && rect.width > 0,
    inViewport: rect.left >= 0 && rect.top >= 0 && rect.right <= innerWidth && rect.bottom <= innerHeight,
    previousId: prev ? prev.id : null,
    firstInBar: !!bar && bar.firstElementChild === button,
    floating: style.position === 'fixed',
    open: button.classList.contains('ms-open'),
    badgeShown: getComputedStyle(badge).display !== 'none',
    badgeText: badge.textContent,
    label: button.getAttribute('aria-label'),
    overlaps,
    clipped,
    outside
  };
});

async function online(browser, game, viewport, shots) {
  /* L'adversaire ouvre sa page : la partie démarre et l'écran d'attente, qui
     couvre tout le plateau, s'efface — le bouton est testé en pleine partie. */
  const opponent = await (await browser.newContext({ viewport: { width: 400, height: 800 } })).newPage();
  if (process.env.THREE_RUNTIME_FILE) {
    await opponent.context().route('**/vendor/three-r128.min.js', route =>
      route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
  }
  const board = await openFramed(browser, onlineUrl(game), viewport);
  await opponent.goto(onlineUrl(game, 2));
  const where = `${game.key} (${viewport.width}×${viewport.height})`;
  const ready = await waitFor(async () => (await board.messages()).some(m => m && m.type === 'mindspille:chat-ready' && m.gameId === game.id));
  check(`${where} : la page annonce sa messagerie`, !!ready);

  const hidden = await chatButton(board.frame);
  check(`${where} : sans l application, aucun bouton`, !!hidden && !hidden.visible, hidden);

  await board.send({ type: 'mindspille:chat', gameId: game.id, enabled: true, unread: 0, open: false });
  await waitFor(async () => { const b = await chatButton(board.frame); return b && b.visible; });
  /* Les boutons du Quoridor animent tout changement de style (transition de
     0,2 s) : on mesure la barre une fois posée. */
  await sleep(600);
  const shown = await chatButton(board.frame);
  const placed = shown && (
    game.slot === 'after-view' ? shown.previousId === 'btn-topview'
      : game.slot === 'after-move' ? shown.previousId === 'btnMove'
        : game.slot === 'bar-start' ? shown.firstInBar
          : shown.floating);
  check(`${where} : le bouton apparaît à sa place (${game.slot})`, !!placed, shown);
  check(`${where} : il reste dans l écran, sans chevaucher ses voisins ni couper leur libellé`, !!shown && shown.inViewport && !shown.overlaps && shown.clipped.length === 0 && shown.outside.length === 0, shown);
  check(`${where} : pas de pastille sans message`, !!shown && !shown.badgeShown, shown);

  await board.send({ type: 'mindspille:chat', gameId: game.id, enabled: true, unread: 3, open: false });
  const unread = await waitFor(async () => { const b = await chatButton(board.frame); return b && b.badgeShown ? b : null; });
  check(`${where} : la pastille compte les messages non lus`, !!unread && unread.badgeText === '3' && /3 nouveaux messages/.test(unread.label), unread);
  if (shots) await board.page.screenshot({ path: path.join(shots, `chat-${game.key}-${viewport.width}.png`) });

  await waitFor(() => board.frame.evaluate(() => {
    const overlay = document.getElementById('waiting-overlay') || document.getElementById('loading');
    return !overlay || getComputedStyle(overlay).display === 'none' || getComputedStyle(overlay).opacity === '0'
      || !overlay.classList.contains('show') && getComputedStyle(overlay).pointerEvents === 'none';
  }), 10000);
  await board.frame.click('.ms-chat-btn', { timeout: 8000 });
  const toggled = await waitFor(async () => (await board.messages()).some(m => m && m.type === 'mindspille:chat-toggle' && m.gameId === game.id));
  check(`${where} : un clic est signalé à l application`, !!toggled);

  await board.send({ type: 'mindspille:chat', gameId: game.id, enabled: true, unread: 0, open: true });
  const open = await waitFor(async () => { const b = await chatButton(board.frame); return b && b.open ? b : null; });
  check(`${where} : état « ouvert », pastille effacée`, !!open && !open.badgeShown, open);

  await board.send({ type: 'mindspille:chat', gameId: 'autre-partie', enabled: false, unread: 0, open: false });
  await sleep(200);
  const foreign = await chatButton(board.frame);
  check(`${where} : un message d une autre partie est ignoré`, !!foreign && foreign.visible && foreign.open, foreign);

  /* Sur un téléphone de 360 px, l'en-tête tenait mal : six repères de manche
     poussaient le profil de droite hors de l'écran. */
  const header = await board.frame.evaluate(() => [...document.querySelectorAll('#top > .profile')].map(p => {
    const r = p.getBoundingClientRect();
    return { left: Math.round(r.left), right: Math.round(r.right), width: innerWidth };
  }));
  check(`${where} : les deux profils de l en-tête restent dans l écran`, header.every(p => p.left >= 0 && p.right <= p.width + 1), header);

  check(`${where} : aucune exception, aucune ressource manquante`, board.errors.length === 0, [...new Set(board.errors)]);
  await board.close();
  await opponent.context().close();
}

const boardState = frame => frame.evaluate(() => {
  const shown = id => { const el = document.getElementById(id); return !!el && getComputedStyle(el).display !== 'none'; };
  const canvases = [...document.querySelectorAll('canvas')].map(c => c.getBoundingClientRect()).filter(r => r.width > 40);
  return {
    top: shown('top'), bot: document.getElementById('bot') ? shown('bot') : null,
    split: document.documentElement.classList.contains('ms-split'),
    board: canvases.reduce((max, r) => Math.max(max, Math.round(Math.min(r.width, r.height))), 0)
  };
});

async function offline(browser, game, shots) {
  const board = await openFramed(browser, `${GAME_URL}${game.route}`, { width: 700, height: 390 });
  const ready = await waitFor(async () => (await board.messages()).some(m => m && m.type === 'mindspille:layout-ready'), 10000);
  check(`${game.key} : la page écoute l application`, !!ready);
  await sleep(1500);
  const before = await boardState(board.frame);

  await board.send({ type: 'mindspille:layout', split: true, hud: true });
  const hud = await waitFor(async () => {
    const list = (await board.messages()).filter(m => m && m.type === 'mindspille:board-hud');
    const last = list[list.length - 1];
    return last && last.hud && last.hud.left && last.hud.right ? last.hud : null;
  });
  await sleep(700);
  const after = await boardState(board.frame);
  if (shots) await board.page.screenshot({ path: path.join(shots, `split-${game.key.replace(' ', '-')}.png`) });

  check(`${game.key} : en écran partagé, l en-tête quitte le plateau`, before.top && !after.top && after.split, { before, after });
  check(`${game.key} : la barre du bas reste`, after.bot !== false, after);
  check(`${game.key} : le plateau ne rétrécit pas`, after.board >= before.board, { before: before.board, after: after.board });
  check(`${game.key} : l en-tête part vers le panneau (joueurs, main)`, !!hud && !!hud.left.name && !!hud.right.name
    && typeof hud.left.active === 'boolean' && typeof hud.right.active === 'boolean', hud);

  await board.send({ type: 'mindspille:layout', split: false });
  await board.page.setViewportSize({ width: 360, height: 740 });
  await sleep(700);
  const back = await boardState(board.frame);
  check(`${game.key} : retour en portrait, l en-tête revient`, back.top && !back.split, back);
  const header = await board.frame.evaluate(() => [...document.querySelectorAll('#top > .profile')].map(p => {
    const r = p.getBoundingClientRect();
    return { left: Math.round(r.left), right: Math.round(r.right), width: innerWidth };
  }));
  check(`${game.key} : à 360 px, les deux profils de l en-tête restent dans l écran`, header.every(p => p.left >= 0 && p.right <= p.width + 1), header);
  check(`${game.key} : aucune exception, aucune ressource manquante`, board.errors.length === 0, [...new Set(board.errors)]);
  await board.close();
}

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK pont plateau ↔ application ignoré');
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
  const shots = process.env.BRIDGE_TEST_SHOTS;
  try {
    await waitForHealth();
    const script = await new Promise((resolve, reject) => {
      http.get(`${GAME_URL}/mindspille-chat.js`, res => {
        res.resume();
        resolve({ status: res.statusCode, type: res.headers['content-type'] });
      }).on('error', reject);
    });
    check('/mindspille-chat.js est servi en JavaScript', script.status === 200 && /javascript/.test(script.type || ''), script);

    browser = await chromium.launch({ executablePath });
    console.log('  — messagerie de partie');
    for (const game of ONLINE) {
      // Téléphone couché (écran partagé) puis téléphone droit.
      await online(browser, game, { width: 700, height: 390 }, shots);
      await online(browser, game, { width: 360, height: 740 }, shots);
      // La barre la plus chargée, sur le plus petit téléphone courant.
      if (game.key === 'quoridor') await online(browser, game, { width: 320, height: 640 }, shots);
    }
    console.log('  — entraînement contre l IA et partie entre amis');
    for (const game of OFFLINE) await offline(browser, game, shots);
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
    await new Promise(r => parent.close(r));
  }
  if (failures) process.exitCode = 1;
  else console.log('OK pont plateau ↔ application');
}

main().catch(error => { console.error(error); process.exitCode = 1; });
