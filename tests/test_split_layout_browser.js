/**
 * Écran partagé de l'application — la vraie page, dans un vrai navigateur.
 *
 * Sur grand écran, l'application pose le plateau à gauche et son panneau de
 * partie à droite, puis demande à la page (`mindspille:layout`) de retirer ce
 * que le panneau affiche déjà : profils, score, mise, bandeaux. La barre du bas
 * (vue, figer, rotation) doit rester, le plateau doit gagner la place libérée,
 * et le texte des bandeaux doit repartir vers l'application.
 *
 * Le test reproduit le montage réel : la page de jeu dans une iframe d'une
 * AUTRE origine que la sienne, comme sur mindspille.com. Le second joueur ouvre
 * sa page normalement, ce qui démarre la partie ; il la quitte ensuite, et le
 * bandeau « Adversaire absent » du premier doit arriver dans l'application au
 * lieu de couvrir le plateau.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3172;
const PARENT_PORT = 3173;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const PARENT_URL = `http://127.0.0.1:${PARENT_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';

const GAME_ID = '30000000-0000-4000-8000-000000000071';
const P1 = { user: '30000000-0000-4000-8000-000000000081', supabase: '30000000-0000-4000-8000-000000000091', name: 'Alice' };
const P2 = { user: '30000000-0000-4000-8000-000000000082', supabase: '30000000-0000-4000-8000-000000000092', name: 'Bob' };

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

function boardUrl(slot, extra = {}) {
  const params = new URLSearchParams({
    room: GAME_ID, gameId: GAME_ID, player: String(slot),
    p1Id: P1.supabase, p2Id: P2.supabase, p1Name: P1.name, p2Name: P2.name,
    bet: '1000', currency: 'HTG', ...extra
  });
  return `${GAME_URL}/dames?${params.toString()}#${new URLSearchParams({ token: tokenFor(slot === 1 ? P1 : P2) }).toString()}`;
}

/* Une page « application » d'une autre origine : la base simulée la sert aussi. */
function parentPage(src) {
  return `<!doctype html><html><body style="margin:0;background:#111">
<iframe id="board" src="${src}" style="width:100vw;height:100vh;border:0"></iframe>
<script>
window.__messages = [];
window.addEventListener('message', function (e) {
  if (e.origin !== ${JSON.stringify(GAME_URL)}) return;
  window.__messages.push(e.data);
});
window.__layout = function (split) {
  document.getElementById('board').contentWindow.postMessage(
    { type: 'mindspille:layout', split: split, gameId: ${JSON.stringify(GAME_ID)} }, ${JSON.stringify(GAME_URL)});
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

const boardState = frame => frame.evaluate(() => {
  const shown = id => { const el = document.getElementById(id); return !!el && getComputedStyle(el).display !== 'none'; };
  const wrap = document.getElementById('wrap').getBoundingClientRect();
  return {
    split: document.documentElement.classList.contains('ms-split'),
    top: shown('top'), bot: shown('bot'), forfeit: shown('forfeit-bar'),
    wrapHeight: Math.round(wrap.height),
    ready: getComputedStyle(document.getElementById('loading')).display === 'none'
  };
});

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK écran partagé ignoré');
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
      // La page « application » doit avoir le droit d'embarquer le plateau.
      FRAME_ANCESTORS: PARENT_URL
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));

  let browser;
  try {
    await waitForHealth();

    const script = await new Promise((resolve, reject) => {
      http.get(`${GAME_URL}/mindspille-split.js`, res => {
        let body = ''; res.on('data', c => { body += c; });
        res.on('end', () => resolve({ status: res.statusCode, type: res.headers['content-type'], body }));
      }).on('error', reject);
    });
    check('le script d écran partagé est servi', script.status === 200 && /javascript/.test(script.type || ''), script.status);

    browser = await chromium.launch({ executablePath });
    /* Le serveur télécharge Three.js depuis un CDN. Une machine sans accès à
       Internet peut fournir sa propre copie r128 par THREE_RUNTIME_FILE ; sinon
       le plateau 3D ne démarre pas et le test n'a pas de sens. */
    const newContext = async viewport => {
      const context = await browser.newContext({ viewport });
      if (process.env.THREE_RUNTIME_FILE) {
        await context.route('**/vendor/three-r128.min.js', route =>
          route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
      }
      return context;
    };
    // Un téléphone couché : la place en hauteur est rare, c'est là que ça compte.
    const app = await (await newContext({ width: 700, height: 390 })).newPage();
    const opponent = await (await newContext({ width: 420, height: 900 })).newPage();
    const errors = [];
    app.on('pageerror', e => errors.push(`app: ${e.message}`));
    opponent.on('pageerror', e => errors.push(`adversaire: ${e.message}`));

    await Promise.all([
      app.goto(`${PARENT_URL}/app?src=${encodeURIComponent(boardUrl(1))}`),
      opponent.goto(boardUrl(2))
    ]);
    const frame = () => app.frames().find(f => f.url().startsWith(`${GAME_URL}/dames`));
    for (let i = 0; i < 60 && !(frame() && (await boardState(frame())).ready); i++) await sleep(250);
    await sleep(1200);

    const messages = () => app.evaluate(() => window.__messages.slice());
    check('la page annonce qu elle écoute (layout-ready)',
      (await messages()).some(m => m && m.type === 'mindspille:layout-ready' && m.gameId === GAME_ID));

    const before = await boardState(frame());
    check('sans écran partagé, rien ne change', before.top && before.bot && !before.split, before);

    const shots = process.env.SPLIT_TEST_SHOTS;
    if (shots) await app.screenshot({ path: path.join(shots, 'avant.png') });
    await app.evaluate(() => window.__layout(true));
    await sleep(700);
    const split = await boardState(frame());
    if (shots) await app.screenshot({ path: path.join(shots, 'apres.png') });
    check('écran partagé : profils, score et mise quittent le plateau', split.split && !split.top, split);
    check('écran partagé : la barre du bas (vue, figer, rotation) reste', split.bot, split);
    check('écran partagé : le plateau gagne la place libérée', split.wrapHeight > before.wrapHeight + 40, { before: before.wrapHeight, after: split.wrapHeight });

    // Le second joueur s'en va : le bandeau d'absence doit partir vers l'application.
    await opponent.close();
    let absence = null;
    for (let i = 0; i < 40 && !absence; i++) {
      await sleep(250);
      const notices = (await messages()).filter(m => m && m.type === 'mindspille:board-notices');
      const last = notices[notices.length - 1];
      absence = last && last.notices.find(n => n.id === 'forfeit-bar');
    }
    check('le bandeau « Adversaire absent » est relayé à l application', !!absence && /absent/i.test(absence.text), absence);
    check('… et ne couvre plus le plateau', !(await boardState(frame())).forfeit);

    await app.evaluate(() => window.__layout(false));
    await sleep(700);
    const back = await boardState(frame());
    check('retour en portrait : l en-tête revient', !back.split && back.top && back.bot, back);
    const lastNotices = (await messages()).filter(m => m && m.type === 'mindspille:board-notices').pop();
    check('retour en portrait : le panneau ne garde aucun bandeau', lastNotices && lastNotices.notices.length === 0, lastNotices);

    // Un spectateur garde sa propre vue : le message ne le concerne pas.
    const spectator = await (await newContext({ width: 700, height: 390 })).newPage();
    spectator.on('pageerror', e => errors.push(`spectateur: ${e.message}`));
    await spectator.goto(`${PARENT_URL}/app?src=${encodeURIComponent(boardUrl(1, { spectate: '1' }))}`);
    await sleep(1500);
    await spectator.evaluate(() => window.__layout(true));
    await sleep(400);
    const spectatorFrame = spectator.frames().find(f => f.url().startsWith(`${GAME_URL}/dames`));
    const spectatorSplit = await spectatorFrame.evaluate(() => document.documentElement.classList.contains('ms-split'));
    check('la page spectateur ignore l écran partagé', spectatorSplit === false);

    check('aucune exception JavaScript', errors.length === 0, errors);
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
    await new Promise(r => parent.close(r));
  }
  if (failures) process.exitCode = 1;
  else console.log('OK écran partagé');
}

main().catch(error => { console.error(error); process.exitCode = 1; });
