/**
 * L'en-tête des sept plateaux en ligne (owner, 2026-10-25) — mindspille-hud.js.
 *
 * Deux vrais navigateurs par jeu, une vraie partie :
 * 1. chaque profil montre le joueur — sa photo, sinon l'initiale de son
 *    pseudo — jamais un pion, un symbole ou un émoji, même quand c'est son
 *    tour ; le joueur qui attend est pâle ;
 * 2. Morpion et Morpion à 5 : sous chaque nom, le symbole du joueur
 *    (« Croix » / « Ronds »), le même des deux côtés de l'écran ;
 * 3. Dames et Échecs : les pièces restantes de chacun au centre, de SON côté
 *    (à gauche celles du profil de gauche), quelle que soit sa couleur ;
 * 4. les manches décisives ont leur propre rangée, sous les manches prévues.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3196;
const DB_PORT = 3197;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const DB_URL = `http://127.0.0.1:${DB_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';
const P1 = { user: '31000000-0000-4000-8000-000000000281', supabase: '31000000-0000-4000-8000-000000000291', name: 'Alice' };
const P2 = { user: '31000000-0000-4000-8000-000000000282', supabase: '31000000-0000-4000-8000-000000000292', name: 'Bob' };
const GAMES = [
  { key: 'tictactoe', route: '/ttt', type: 'tictactoe', id: '31000000-0000-4000-8000-000000000204', turns: true, symbols: true },
  { key: 'gomoku', route: '/gomoku', type: 'gomoku', id: '31000000-0000-4000-8000-000000000205', turns: true, symbols: true },
  { key: 'dames', route: '/dames', type: 'checkers', id: '31000000-0000-4000-8000-000000000206', turns: true, pieces: 20 },
  { key: 'echecs', route: '/echecs', type: 'chess', id: '31000000-0000-4000-8000-000000000207', turns: true, pieces: 16 },
  { key: 'quoridor', route: '/quoridor', type: 'quoridor', id: '31000000-0000-4000-8000-000000000201', turns: true },
  { key: 'penalty', route: '/penalty', type: 'penalty_shootout', id: '31000000-0000-4000-8000-000000000202' },
  { key: 'chifoumi', route: '/chifoumi', type: 'rock_paper_scissors', id: '31000000-0000-4000-8000-000000000203' }
];

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : JSON.stringify(detail)); }
}
const sleep = ms => new Promise(r => setTimeout(r, ms));
async function waitFor(fn, timeoutMs = 10000, stepMs = 200) {
  const end = Date.now() + timeoutMs;
  let last = null;
  while (Date.now() < end) {
    try { last = await fn(); if (last) return last; } catch (_) {}
    await sleep(stepMs);
  }
  return last;
}
async function waitForHealth(retries = 50) {
  for (let i = 0; i < retries; i++) {
    const ok = await new Promise(resolve => http.get(`${GAME_URL}/health`, r => { r.resume(); resolve(r.statusCode === 200); }).on('error', () => resolve(false)));
    if (ok) return;
    await sleep(200);
  }
  throw new Error('game server unavailable');
}
const tokenFor = p => jwt.sign({ userId: p.user, supabaseId: p.supabase, username: p.name }, JWT_SECRET);
function pageUrl(game, slot) {
  const params = new URLSearchParams({
    room: game.id, gameId: game.id, player: String(slot),
    p1Id: P1.supabase, p2Id: P2.supabase, p1Name: P1.name, p2Name: P2.name,
    bet: '1000', currency: 'HTG'
  });
  return `${GAME_URL}${game.route}?${params}#${new URLSearchParams({ token: tokenFor(slot === 1 ? P1 : P2) })}`;
}
function mockDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, DB_URL);
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
      const id = String(url.searchParams.get('id') || '').replace(/^eq\./, '');
      const game = GAMES.find(g => g.id === id);
      return response.end(JSON.stringify(game ? [{
        id: game.id, game_type: game.type, player1_id: P1.supabase, player2_id: P2.supabase,
        bet_amount: 1000, status: 'in_progress', is_ai_opponent: false, is_tournament: false, game_settings: {}
      }] : []));
    }
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
    response.statusCode = 404;
    response.end('{}');
  });
}

async function openMatch(browser, game) {
  const errors = [];
  const pages = [];
  for (const slot of [1, 2]) {
    const context = await browser.newContext({ viewport: { width: 390, height: 844 } });
    if (process.env.THREE_RUNTIME_FILE) {
      await context.route('**/vendor/three-r128.min.js', route =>
        route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
    }
    const page = await context.newPage();
    page.on('pageerror', e => errors.push(`joueur ${slot} : ${e.message}`));
    pages.push(page);
  }
  await Promise.all(pages.map((page, i) => page.goto(pageUrl(game, i + 1))));
  return { pages, errors, close: () => Promise.all(pages.map(p => p.context().close())) };
}

/** Ce que montre l'en-tête : les portraits, les camps, le profil allumé, les pièces au centre. */
const readHeader = page => page.evaluate(() => {
  const profiles = [...document.querySelectorAll('#top > .profile')];
  return profiles.map(profile => {
    const avatar = profile.querySelector('.profile-avatar');
    const first = avatar && avatar.firstElementChild;
    return {
      portrait: first ? (first.classList.contains('ms-initial') ? 'initial' : first.classList.contains('profile-photo') ? 'photo' : first.className || first.tagName) : 'empty',
      letter: first && first.classList.contains('ms-initial') ? first.textContent : null,
      piece: !!(avatar && avatar.querySelector('.av-w, .av-r, .av-x, .av-o, .av-white, .av-red, .turn-stone')),
      emoji: /[\u{1F300}-\u{1FAFF}⚽]/u.test(avatar ? [...avatar.childNodes].filter(n => !n.classList || !n.classList.contains('role-badge')).map(n => n.textContent).join('') : ''),
      side: (profile.querySelector('.profile-side .ms-side-lbl') || {}).textContent || null,
      active: profile.classList.contains('active'),
      opacity: Number(getComputedStyle(profile).opacity)
    };
  });
});

async function hud(browser, game) {
  const match = await openMatch(browser, game);
  const [a, b] = match.pages;
  // La partie démarre chez les deux joueurs : un profil allumé (jeux au tour par tour), ou six secondes.
  if (game.turns) await waitFor(async () => (await Promise.all(match.pages.map(readHeader))).every(h => h.filter(p => p.active).length === 1), 15000);
  else await sleep(6000);
  await sleep(700); // la pâleur suit le tour par une transition de 0,3 s
  const [ha, hb] = await Promise.all([readHeader(a), readHeader(b)]);

  check(`${game.key} : deux profils de chaque côté`, ha.length === 2 && hb.length === 2, { ha, hb });
  const all = [...ha, ...hb];
  check(`${game.key} : chaque profil montre le joueur (photo ou initiale), jamais un pion ni un émoji`,
    all.every(p => (p.portrait === 'initial' || p.portrait === 'photo') && !p.piece && !p.emoji), all);
  check(`${game.key} : l’initiale est celle du pseudo, chacun à sa place (vous à gauche)`,
    ha[0].letter === 'A' && ha[1].letter === 'B' && hb[0].letter === 'B' && hb[1].letter === 'A', all.map(p => p.letter));

  if (game.turns) {
    const pale = h => { const on = h.find(p => p.active), off = h.find(p => !p.active); return !!on && !!off && off.opacity < 0.7 && on.opacity > 0.9; };
    check(`${game.key} : le joueur au trait est allumé, celui qui attend est pâle`, pale(ha) && pale(hb), { ha, hb });
    // Le tour ne remplace jamais le portrait par un symbole (l'ancien comportement).
    const activeLeft = ha[0].active;
    check(`${game.key} : le joueur au trait garde son portrait`, (activeLeft ? ha[0] : ha[1]).portrait !== 'empty' && !(activeLeft ? ha[0] : ha[1]).piece);
  }

  if (game.symbols) {
    const sides = [ha[0].side, ha[1].side, hb[0].side, hb[1].side];
    check(`${game.key} : sous chaque nom, son symbole — croix ou ronds`,
      sides.every(s => s === 'Croix' || s === 'Ronds') && ha[0].side !== ha[1].side, sides);
    check(`${game.key} : le même symbole pour le même joueur sur les deux écrans`, ha[0].side === hb[1].side && ha[1].side === hb[0].side, sides);
  }

  if (game.pieces) {
    const centre = page => page.evaluate(() => [...document.querySelectorAll('#top .top-center .score-row .snum')].map(n => ({ text: n.textContent.trim(), white: n.classList.contains('sw'), red: n.classList.contains('sr') })));
    const [ca, cb] = await Promise.all([centre(a), centre(b)]);
    check(`${game.key} : les Blancs (joueur 1) voient leurs pièces à gauche, en blanc`, ca[0].white && ca[1].red && ca[0].text === String(game.pieces), ca);
    check(`${game.key} : les Rouges (joueur 2) voient LEURS pièces à gauche, près de leur profil`, cb[0].red && cb[1].white && cb[0].text === String(game.pieces), cb);
  }

  // Les manches décisives : leur propre rangée, sous les manches prévues.
  // Morpion à 5 et Quoridor : la vraie fonction de la page, avec une série
  // en mort subite. Morpion, Penalty et Chifoumi gardent leur code dans une
  // fermeture : le module, sur la vraie page, et son branchement dans la source.
  const decisive = await a.evaluate(key => {
    const regularRow = document.getElementById('roundsProgress');
    if (key === 'gomoku' || key === 'quoridor') updateSeriesUI({ regularRounds: 6, roundsPlayed: 8, currentRound: 9, wins: { 1: 3, 2: 3 }, draws: 2, history: [1, 2, 1, 2, 1, 2], decisive: [0, 0], suddenDeath: true });
    else if (key === 'tictactoe' || key === 'penalty' || key === 'chifoumi') window.MindspilleHud.decisive(regularRow, key === 'chifoumi' ? ['draw'] : ['win'], true);
    else return null;
    const regular = document.getElementById('roundsProgress');
    const row = regular && regular.nextElementSibling;
    const box = r => r.getBoundingClientRect();
    return row && row.classList.contains('rounds-decisive') ? {
      regular: regular.querySelectorAll('.round-dot').length,
      dots: [...row.querySelectorAll('.ms-dec-dot')].map(d => d.className.replace('ms-dec-dot', '').trim()),
      label: (row.querySelector('.ms-dec-lbl') || {}).textContent,
      below: box(row).top >= box(regular).bottom - 1,
      visible: !row.hidden && box(row).height > 0
    } : { regular: regular ? regular.querySelectorAll('.round-dot').length : 0, missing: true };
  }, game.key);
  const SOURCES = { tictactoe: 'ttt_game.html', penalty: 'penalty-online.html', chifoumi: 'chifoumi-online.html' };
  if (SOURCES[game.key]) {
    const source = require('fs').readFileSync(path.join(REPO_ROOT, 'public', SOURCES[game.key]), 'utf8');
    check(`${game.key} : la page range ses manches décisives à part (mindspille-hud.js)`,
      /<script src="\/mindspille-hud\.js"><\/script>/.test(source) && /MindspilleHud\.decisive\(/.test(source));
  }
  if (decisive) {
    const expected = { tictactoe: ['win', 'current'], gomoku: ['draw', 'draw', 'current'], quoridor: ['draw', 'draw', 'current'], penalty: ['win', 'current'], chifoumi: ['draw', 'current'] }[game.key];
    check(`${game.key} : les manches décisives sur une rangée à part, sous les manches prévues`,
      !decisive.missing && decisive.visible && decisive.below && JSON.stringify(decisive.dots) === JSON.stringify(expected), decisive);
    check(`${game.key} : la rangée prévue garde son nombre de repères`, decisive.regular > 0 && decisive.regular <= 10, decisive);
    check(`${game.key} : la rangée se nomme`, /^Manches? décisives?$/.test(decisive.label || ''), decisive.label);
  }

  check(`${game.key} : aucune exception JavaScript`, match.errors.length === 0, [...new Set(match.errors)]);
  if (process.env.HUD_SHOTS) {
    for (const [i, page] of match.pages.entries()) await page.screenshot({ path: path.join(process.env.HUD_SHOTS, `hud-${game.key}-p${i + 1}.png`), clip: { x: 0, y: 0, width: 390, height: 170 } });
  }
  await match.close();
}

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — en-têtes non vérifiés');
    console.log('OK en-têtes des plateaux ignorés');
    return;
  }
  const db = mockDatabase();
  await new Promise(r => db.listen(DB_PORT, '127.0.0.1', r));
  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: { ...process.env, PORT: String(GAME_PORT), NODE_ENV: 'test', JWT_SECRET, SUPABASE_URL: DB_URL, SUPABASE_SERVICE_ROLE_KEY: 'test-service-role', ALLOWED_ORIGIN: GAME_URL },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));
  let browser;
  try {
    await waitForHealth();
    browser = await chromium.launch({ executablePath });
    for (const game of GAMES) {
      console.log(`  — ${game.key}`);
      await hud(browser, game);
    }
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
    await new Promise(r => db.close(r));
  }
  if (failures) process.exitCode = 1;
  else console.log('OK en-têtes des plateaux');
}

main().catch(error => { console.error(error); process.exitCode = 1; });
