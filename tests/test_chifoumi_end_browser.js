/**
 * Chifoumi : égalité au bout des manches réglementaires, deux vrais navigateurs.
 *
 * Le serveur ouvre alors une manche décisive (mort subite). La page, elle,
 * concluait seule après la dernière manche : « Égalité », écran de fin, plus
 * rien ne se jouait. Personne ne jouait la manche décisive et les deux joueurs
 * finissaient par perdre au temps — partie annulée, pénalité pour chacun.
 *
 * Ici, une seule manche réglementaire (CHIFOUMI_TOTAL_ROUNDS=1) : pierre contre
 * pierre, puis la manche décisive se joue et désigne le vrai vainqueur.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3262;
const DB_PORT = 3263;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const DB_URL = `http://127.0.0.1:${DB_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';
const GAME_ID = '30000000-0000-4000-8000-000000000406';
const P1 = { user: '30000000-0000-4000-8000-000000000481', supabase: '30000000-0000-4000-8000-000000000491', name: 'Alice' };
const P2 = { user: '30000000-0000-4000-8000-000000000482', supabase: '30000000-0000-4000-8000-000000000492', name: 'Bob' };

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : detail); }
}
const sleep = ms => new Promise(r => setTimeout(r, ms));
async function waitFor(fn, timeoutMs = 10000, stepMs = 200) {
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

const tokenFor = p => jwt.sign({ userId: p.user, supabaseId: p.supabase, username: p.name }, JWT_SECRET);
function pageUrl(slot) {
  const params = new URLSearchParams({
    room: GAME_ID, gameId: GAME_ID, player: String(slot),
    p1Id: P1.supabase, p2Id: P2.supabase, p1Name: P1.name, p2Name: P2.name,
    bet: '0', currency: 'HTG'
  });
  return `${GAME_URL}/chifoumi?${params}#${new URLSearchParams({ token: tokenFor(slot === 1 ? P1 : P2) })}`;
}

function mockDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, DB_URL);
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
      return response.end(JSON.stringify([{
        id: GAME_ID, game_type: 'rock_paper_scissors', player1_id: P1.supabase, player2_id: P2.supabase,
        bet_amount: 0, status: 'in_progress', is_ai_opponent: false, is_tournament: false, game_settings: {}
      }]));
    }
    if (request.method === 'POST' && url.pathname.endsWith('/load_game_server_room_states')) return response.end('[]');
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
    response.statusCode = 404;
    response.end('{}');
  });
}

const playable = page => page.evaluate(() => {
  const buttons = [...document.querySelectorAll('.choice-btn')];
  return document.getElementById('profile-human').classList.contains('human-active')
    && buttons.length === 3 && buttons.every(b => !b.classList.contains('disabled') && !b.classList.contains('locked'));
});
const view = page => page.evaluate(() => ({
  label: document.getElementById('roundLabel').textContent.trim(),
  over: document.getElementById('gameOverModal').classList.contains('show'),
  title: document.getElementById('modalTitle').textContent.trim()
}));
const choose = (page, choice) => page.evaluate(c => document.querySelector(`.choice-btn[data-choice="${c}"]`).click(), choice);

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK mort subite du Chifoumi ignorée');
    return;
  }
  const db = mockDatabase();
  await new Promise(r => db.listen(DB_PORT, '127.0.0.1', r));
  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT), NODE_ENV: 'test', JWT_SECRET,
      SUPABASE_URL: DB_URL, SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: GAME_URL, CHIFOUMI_TOTAL_ROUNDS: '1'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));

  let browser;
  const errors = [];
  try {
    await waitForHealth();
    browser = await chromium.launch({ executablePath });
    const pages = [];
    for (const slot of [1, 2]) {
      const context = await browser.newContext({ viewport: { width: 420, height: 860 } });
      const page = await context.newPage();
      page.on('pageerror', e => errors.push(`joueur ${slot} : ${e.message}`));
      pages.push(page);
    }
    const [p1, p2] = pages;
    await Promise.all(pages.map((page, i) => page.goto(pageUrl(i + 1))));

    const first = await waitFor(async () => (await Promise.all(pages.map(playable))).every(Boolean), 15000);
    check('la manche réglementaire est jouable', first === true);
    await choose(p1, 'pierre');
    await choose(p2, 'pierre');

    const decisive = await waitFor(async () => {
      const ok = await Promise.all(pages.map(async p => (await playable(p)) && /d[ée]cisive/i.test((await view(p)).label)));
      return ok.every(Boolean);
    }, 20000);
    const states = await Promise.all(pages.map(view));
    check('égalité : la manche décisive s ouvre chez les deux joueurs', decisive === true, JSON.stringify(states));
    check('… sans écran de fin « Égalité »', states.every(s => !s.over), JSON.stringify(states));

    await choose(p1, 'pierre');
    await choose(p2, 'ciseaux');
    const finals = await waitFor(async () => {
      const v = await Promise.all(pages.map(view));
      return v.every(s => s.over) ? v : null;
    }, 20000);
    check('la manche décisive désigne le vainqueur : victoire du joueur 1', finals && /VICTOIRE/.test(finals[0].title), JSON.stringify(finals));
    check('… et défaite du joueur 2', finals && /DÉFAITE/.test(finals[1].title), JSON.stringify(finals));
    check('aucune exception JavaScript', errors.length === 0, [...new Set(errors)]);
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
    await new Promise(r => db.close(r));
  }
  if (failures) process.exitCode = 1;
  else console.log('OK mort subite du Chifoumi jouée jusqu au bout');
}

main().catch(error => { console.error(error); process.exitCode = 1; });
