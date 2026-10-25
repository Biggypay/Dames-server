/**
 * Chifoumi : les dessins du propriétaire (pierre, feuille, ciseaux) à la place
 * des émojis ✊ ✋ ✌️, sur les trois pages du jeu — en ligne, contre l'IA,
 * entre amis sur le même appareil.
 *
 * - Les trois dessins sont servis en WebP (une liste fermée : rien d'autre ne
 *   sort de public/chifoumi/).
 * - Les boutons portent chacun son dessin, chargé.
 * - À la révélation, chaque carte montre le dessin du choix, côté joueur et
 *   côté adversaire, et le message dit le coup en toutes lettres
 *   (« Victoire ! Pierre bat Ciseaux ») sur une seule ligne, même à 320 px.
 * - L'historique de fin de partie montre les miniatures (une partie entière
 *   entre amis).
 * - Plus aucun émoji de main nulle part, aucune exception, aucune ressource
 *   manquante.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3272;
const DB_PORT = 3273;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const DB_URL = `http://127.0.0.1:${DB_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';
const GAME_ID = '30000000-0000-4000-8000-000000000506';
const P1 = { user: '30000000-0000-4000-8000-000000000581', supabase: '30000000-0000-4000-8000-000000000591', name: 'Alice' };
const P2 = { user: '30000000-0000-4000-8000-000000000582', supabase: '30000000-0000-4000-8000-000000000592', name: 'Bob' };
const HANDS = /[✊✋✌]/u;

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
const head = url => new Promise((resolve, reject) => {
  http.get(url, res => { res.resume(); res.on('end', () => resolve({ status: res.statusCode, type: res.headers['content-type'] || '' })); })
    .on('error', reject);
});

const tokenFor = p => jwt.sign({ userId: p.user, supabaseId: p.supabase, username: p.name }, JWT_SECRET);
function onlineUrl(slot) {
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

async function openPage(browser, url, viewport, errors, label) {
  const context = await browser.newContext({ viewport });
  const page = await context.newPage();
  page.on('pageerror', e => errors.push(`${label} : ${e.message}`));
  page.on('response', r => {
    if (r.url().startsWith(GAME_URL) && r.status() >= 400) errors.push(`${label} : HTTP ${r.status()} ${r.url().slice(GAME_URL.length).split('?')[0]}`);
  });
  await page.goto(url);
  return page;
}

/* La manche est ouverte quand startRound() a allumé le profil du joueur ; avant, un clic est ignoré. */
const playable = page => page.evaluate(() => {
  const buttons = [...document.querySelectorAll('.choice-btn')];
  return document.getElementById('profile-human').classList.contains('human-active')
    && buttons.length === 3 && buttons.every(b => !b.classList.contains('disabled') && !b.classList.contains('locked'));
});
const choose = (page, choice) => page.evaluate(c => document.querySelector(`.choice-btn[data-choice="${c}"]`).click(), choice);

/* Ce que la page montre : le dessin de chaque bouton, des deux cartes, le message. */
const look = page => page.evaluate(() => {
  const artOf = img => (img && img.complete && img.naturalWidth > 0 && (/\/chifoumi\/(\w+)\.webp/.exec(img.getAttribute('src')) || [])[1]) || null;
  const status = document.getElementById('status');
  const rect = status.getBoundingClientRect();
  return {
    buttons: [...document.querySelectorAll('.choice-btn')].map(b => artOf(b.querySelector('img.rps-art'))),
    me: artOf(document.querySelector('#playerEmoji img.rps-art')),
    op: artOf(document.querySelector('#aiEmoji img.rps-art')),
    status: status.textContent.trim(),
    result: status.classList.contains('result'),
    oneLine: getComputedStyle(status).whiteSpace === 'nowrap' && status.scrollWidth <= status.clientWidth + 1 && rect.height < 34,
    text: document.body.innerText
  };
});

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK dessins du Chifoumi ignorés');
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

    const served = await Promise.all(['pierre', 'feuille', 'ciseaux'].map(n => head(`${GAME_URL}/chifoumi/${n}.webp?v=1`)));
    check('les trois dessins sont servis en WebP', served.every(r => r.status === 200 && r.type.startsWith('image/webp')), served);
    const others = await Promise.all(['autre.webp', 'pierre.png', '..%2Fserver.js'].map(n => head(`${GAME_URL}/chifoumi/${n}`)));
    check('… et rien d autre sous /chifoumi/', others.every(r => r.status === 404), others);

    browser = await chromium.launch({ executablePath });

    /* En ligne : deux vrais navigateurs, une manche (CHIFOUMI_TOTAL_ROUNDS=1). */
    const p1 = await openPage(browser, onlineUrl(1), { width: 420, height: 860 }, errors, 'en ligne, joueur 1');
    const p2 = await openPage(browser, onlineUrl(2), { width: 420, height: 860 }, errors, 'en ligne, joueur 2');
    const ready = await waitFor(async () => (await playable(p1)) && (await playable(p2)), 15000);
    check('en ligne : la manche est jouable', ready === true);
    const atStart = await Promise.all([p1, p2].map(look));
    check('en ligne : chaque bouton porte son dessin, chargé',
      atStart.every(v => v.buttons.join() === 'pierre,feuille,ciseaux'), atStart.map(v => v.buttons));
    await choose(p1, 'pierre');
    await choose(p2, 'ciseaux');
    const shown = await waitFor(async () => {
      const v = await Promise.all([p1, p2].map(look));
      return v.every(s => s.result && s.me && s.op) ? v : null;
    }, 15000);
    check('en ligne : chez le joueur 1, sa pierre face aux ciseaux', shown && shown[0].me === 'pierre' && shown[0].op === 'ciseaux', shown && shown[0]);
    check('en ligne : chez le joueur 2, ses ciseaux face à la pierre', shown && shown[1].me === 'ciseaux' && shown[1].op === 'pierre', shown && shown[1]);
    check('en ligne : « Victoire ! Pierre bat Ciseaux » / « Défaite... Pierre bat Ciseaux », sur une ligne',
      shown && /Victoire ! Pierre bat Ciseaux/.test(shown[0].status) && /Défaite\.\.\. Pierre bat Ciseaux/.test(shown[1].status)
        && shown.every(s => s.oneLine), shown && shown.map(s => [s.status, s.oneLine]));

    const ends = await Promise.all([p1, p2].map(look));
    check('en ligne : aucun émoji de main sur la page', ends.every(v => !HANDS.test(v.text)));
    await p1.context().close();
    await p2.context().close();

    /* Contre l'IA, et sur le plus petit téléphone. */
    for (const viewport of [{ width: 390, height: 844 }, { width: 320, height: 568 }]) {
      const label = `IA ${viewport.width} px`;
      const ai = await openPage(browser, `${GAME_URL}/chifoumi-ai?difficulty=easy`, viewport, errors, label);
      check(`${label} : la manche est jouable`, (await waitFor(() => playable(ai), 15000)) === true);
      check(`${label} : chaque bouton porte son dessin, chargé`, (await look(ai)).buttons.join() === 'pierre,feuille,ciseaux');
      await choose(ai, 'feuille');
      const v = await waitFor(async () => { const s = await look(ai); return s.result && s.me && s.op ? s : null; }, 25000);
      check(`${label} : la feuille et le dessin choisi par l IA sont révélés`, v && v.me === 'feuille' && ['pierre', 'feuille', 'ciseaux'].includes(v.op), v && [v.me, v.op]);
      check(`${label} : le message tient sur une ligne`, v && v.oneLine, v && v.status);
      check(`${label} : aucun émoji de main`, v && !HANDS.test(v.text));
      await ai.context().close();
    }

    /* Entre amis, sur le même appareil : chacun choisit à son tour. */
    for (const viewport of [{ width: 390, height: 844 }, { width: 320, height: 568 }]) {
      const label = `entre amis ${viewport.width} px`;
      const local = await openPage(browser, `${GAME_URL}/chifoumi-local`, viewport, errors, label);
      check(`${label} : la manche est jouable`, (await waitFor(() => playable(local), 15000)) === true);
      check(`${label} : chaque bouton porte son dessin, chargé`, (await look(local)).buttons.join() === 'pierre,feuille,ciseaux');
      /* Le joueur 1 choisit, la main passe aussitôt au joueur 2. */
      await choose(local, 'pierre');
      await choose(local, 'feuille');
      const v = await waitFor(async () => { const s = await look(local); return s.result && s.me && s.op ? s : null; }, 25000);
      check(`${label} : la pierre du joueur 1 face à la feuille du joueur 2`, v && v.me === 'pierre' && v.op === 'feuille', v && [v.me, v.op]);
      check(`${label} : « … gagne ! Feuille bat Pierre » sur une ligne`, v && /gagne ! Feuille bat Pierre/.test(v.status) && v.oneLine, v && v.status);
      check(`${label} : aucun émoji de main`, v && !HANDS.test(v.text));
      if (viewport.width === 390) {
        /* La partie jusqu'au bout : l'historique de fin montre les miniatures. */
        const over = () => local.evaluate(() => document.getElementById('gameOverModal').classList.contains('show'));
        for (let round = 0; round < 10 && !(await over()); round++) {
          if (!(await waitFor(async () => (await over()) || (await playable(local)), 20000))) break;
          if (await over()) break;
          await choose(local, 'pierre');
          await choose(local, 'feuille');
        }
        const rows = await waitFor(async () => (await over()) && local.evaluate(() =>
          [...document.querySelectorAll('.modal-history-item')].map(row => [...row.querySelectorAll('img.rps-mini')]
            .map(img => (img.complete && img.naturalWidth > 0 && (/\/chifoumi\/(\w+)\.webp/.exec(img.getAttribute('src')) || [])[1]) || '?').join(' VS '))), 20000);
        check('fin de partie : l historique montre les miniatures de chaque manche',
          Array.isArray(rows) && rows.length > 1 && rows.every(r => r === 'pierre VS feuille'), rows);
      }
      await local.context().close();
    }

    check('aucune exception JavaScript, aucune ressource manquante', errors.length === 0, [...new Set(errors)]);
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
    await new Promise(r => db.close(r));
  }
  if (failures) process.exitCode = 1;
  else console.log('OK dessins du Chifoumi sur les trois pages');
}

main().catch(error => { console.error(error); process.exitCode = 1; });
