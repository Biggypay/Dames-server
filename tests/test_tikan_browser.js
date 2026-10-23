/**
 * TIKAN — parcours réel, dans deux vrais navigateurs : la page se charge sans
 * exception, le terrain est dessiné, les deux écrans voient la même partie et
 * une touche déplace réellement le joueur (via le serveur).
 */
const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3172;
const MOCK_DB_PORT = 3173;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';

const GAME_ID = '70000000-0000-4000-8000-000000000001';
const P1 = { user: '70000000-0000-4000-8000-000000000011', supabase: '70000000-0000-4000-8000-000000000021', name: 'Alice' };
const P2 = { user: '70000000-0000-4000-8000-000000000012', supabase: '70000000-0000-4000-8000-000000000022', name: 'Bob' };

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

function startMockDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, `http://127.0.0.1:${MOCK_DB_PORT}`);
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
      const id = (url.searchParams.get('id') || '').replace(/^eq\./, '');
      return response.end(JSON.stringify([{
        id: id || GAME_ID, game_type: 'tikan',
        player1_id: P1.supabase, player2_id: P2.supabase,
        bet_amount: 0, status: 'in_progress', is_ai_opponent: false
      }]));
    }
    if (request.method === 'POST' && url.pathname.endsWith('/load_game_server_room_states')) return response.end('[]');
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
    response.statusCode = 404;
    response.end('{}');
  });
}

/**
 * Chromium est pre-installe dans l'image, mais son dossier porte le numero de
 * build (chromium-1194). Le chercher evite que le test casse a la prochaine
 * mise a jour de l'image.
 */

const tokenFor = p => jwt.sign({ userId: p.user, supabaseId: p.supabase, username: p.name }, JWT_SECRET);

function boardUrl(slot) {
  const params = new URLSearchParams({
    room: GAME_ID, gameId: GAME_ID, player: String(slot),
    p1Id: P1.supabase, p2Id: P2.supabase,
    p1Name: P1.name, p2Name: P2.name,
    bet: '0', currency: 'HTG'
  });
  const token = tokenFor(slot === 1 ? P1 : P2);
  return `${GAME_URL}/tikan?${params.toString()}#${new URLSearchParams({ token }).toString()}`;
}


const SHOT_DIR = process.env.TIKAN_SHOTS || '';

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK parcours navigateur TIKAN ignoré');
    return;
  }
  const mockDb = startMockDatabase();
  await new Promise(r => mockDb.listen(MOCK_DB_PORT, '127.0.0.1', r));
  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: { ...process.env, PORT: String(GAME_PORT), NODE_ENV: 'test', JWT_SECRET,
      SUPABASE_URL: `http://127.0.0.1:${MOCK_DB_PORT}`, SUPABASE_SERVICE_ROLE_KEY: 'test-service-role', ALLOWED_ORIGIN: GAME_URL },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));
  let browser;
  try {
    await waitForHealth();
    browser = await chromium.launch({ executablePath });
    const ctxs = [await browser.newContext({ viewport: { width: 400, height: 780 }, hasTouch: true }),
                  await browser.newContext({ viewport: { width: 400, height: 780 }, hasTouch: true })];
    const pages = [await ctxs[0].newPage(), await ctxs[1].newPage()];
    const errors = [];
    pages.forEach((pg, k) => {
      pg.on('pageerror', e => errors.push(`J${k + 1}: ${e.message}`));
      pg.on('response', r => { if (r.status() >= 400 && !/favicon/.test(r.url())) errors.push(`J${k + 1} HTTP ${r.status()} ${r.url()}`); });
    });
    await Promise.all([pages[0].goto(boardUrl(1)), pages[1].goto(boardUrl(2))]);
    await sleep(1800);
    if (SHOT_DIR) await pages[0].screenshot({ path: path.join(SHOT_DIR, 'opening.png') });
    await sleep(2500);

    const paint = pg => pg.evaluate(() => {
      const c = document.getElementById('gc');
      const d = c.getContext('2d').getImageData(0, 0, c.width, c.height).data;
      let lit = 0;
      for (let i = 0; i < d.length; i += 4 * 37) if (d[i] + d[i + 1] + d[i + 2] > 60) lit++;
      return { w: c.width, h: c.height, lit, wait: getComputedStyle(document.getElementById('wait')).display };
    });
    const a = await paint(pages[0]), b = await paint(pages[1]);
    check('aucune exception JavaScript sur les deux écrans', errors.length === 0, errors);
    check('le voile de connexion se retire des deux côtés', a.wait === 'none' && b.wait === 'none', { a, b });
    check('le terrain est dessiné des deux côtés', a.lit > 300 && b.lit > 300 && a.w > 100, { a, b });

    // Une touche (flèche gauche) déplace le joueur 1 : on lit sa position dans l'instantané reçu.
    for (const pg of pages) await pg.evaluate(() => { window.mindspilleSocket.on('tikan_state', st => { window.__lastTikan = st; }); });
    await sleep(300);
    const me = pg => pg.evaluate(() => window.__lastTikan || null);
    const hasDebug = await me(pages[0]);
    check('les deux écrans reçoivent les instantanés du serveur', !!hasDebug && !!(await me(pages[1])));
    if (hasDebug) {
      const x0 = hasDebug.p[0][0];
      await pages[0].keyboard.down('ArrowLeft');
      await sleep(900);
      await pages[0].keyboard.up('ArrowLeft');
      const s = await me(pages[1]);
      check('la touche déplace le joueur 1, et l’autre écran le voit', s && s.p[0][0] < x0 - 20, { x0, now: s && s.p[0] });
    } else {
      console.log('  (info) aucun instantané lu : test de déplacement ignoré');
    }
    if (SHOT_DIR) { await pages[0].screenshot({ path: path.join(SHOT_DIR, 'play1.png') }); await pages[1].screenshot({ path: path.join(SHOT_DIR, 'play2.png') }); }
    check('toujours aucune exception après quelques secondes de jeu', errors.length === 0, errors);
  } finally {
    if (browser) await browser.close();
    server.kill();
    mockDb.close();
  }
  if (failures) { console.error(`${failures} échec(s)`); process.exit(1); }
  console.log('OK parcours navigateur TIKAN');
}
main().catch(e => { console.error(e); process.exit(1); });
