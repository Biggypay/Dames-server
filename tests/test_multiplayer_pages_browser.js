/**
 * Les sept pages multijoueur, deux vrais navigateurs face à face.
 *
 * Trois pages plantaient au démarrage de chaque partie, et personne ne l'a vu
 * parce qu'aucun test n'ouvrait la page elle-même :
 *   - Quoridor : `startNewGame` retouchait la pastille `#dot-me`, que la photo
 *     de profil remplace sans id → TypeError, pas de « Partie commencée ».
 *   - Penalty : `showZones` appelait `startLocalTimer()`, qui n'existe pas.
 *   - Chifoumi : `isTiebreaker` jamais déclarée, en 'use strict' → ReferenceError.
 * Et `/tournament-pause-client.js`, inclus par les sept pages, répondait 404 :
 * ni l'overlay « Tournoi en pause » ni le garde-fou du Quoridor ne tournaient.
 * Servi, il n'aurait encore rien fait sur cinq pages sur sept, qui gardent leur
 * prise Socket.IO dans une fonction : elles la publient désormais.
 *
 * Chaque partie démarre ici pour de bon (serveur réel, base simulée), sans
 * aucune exception JavaScript ni ressource manquante ; les trois pages
 * corrigées jouent réellement un coup ou une manche ; et une pause de tournoi
 * couvre puis libère les deux plateaux, dans chacun des sept jeux.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3192;
const DB_PORT = 3193;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const DB_URL = `http://127.0.0.1:${DB_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';
const TOURNAMENT_ID = '30000000-0000-4000-8000-000000000299';
const P1 = { user: '30000000-0000-4000-8000-000000000281', supabase: '30000000-0000-4000-8000-000000000291', name: 'Alice' };
const P2 = { user: '30000000-0000-4000-8000-000000000282', supabase: '30000000-0000-4000-8000-000000000292', name: 'Bob' };

/* Une partie par jeu : chaque salle a son propre identifiant. */
const GAMES = [
  { key: 'quoridor', route: '/quoridor', type: 'quoridor', id: '30000000-0000-4000-8000-000000000201' },
  { key: 'penalty', route: '/penalty', type: 'penalty_shootout', id: '30000000-0000-4000-8000-000000000202' },
  { key: 'chifoumi', route: '/chifoumi', type: 'rock_paper_scissors', id: '30000000-0000-4000-8000-000000000203' },
  { key: 'tictactoe', route: '/ttt', type: 'tictactoe', id: '30000000-0000-4000-8000-000000000204' },
  { key: 'gomoku', route: '/gomoku', type: 'gomoku', id: '30000000-0000-4000-8000-000000000205' },
  { key: 'dames', route: '/dames', type: 'checkers', id: '30000000-0000-4000-8000-000000000206' },
  { key: 'echecs', route: '/echecs', type: 'chess', id: '30000000-0000-4000-8000-000000000207' }
];
const pausedGames = new Set();
let pauseRevision = 0;

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
        bet_amount: 1000, status: 'in_progress', is_ai_opponent: false,
        is_tournament: true, game_settings: { tournament_paused: false }
      }] : []));
    }
    if (request.method === 'POST' && url.pathname.endsWith('/server_tournament_game_controls')) {
      let body = '';
      request.on('data', chunk => { body += chunk; });
      return request.on('end', () => {
        let ids = [];
        try { ids = JSON.parse(body).p_game_ids || []; } catch (_) {}
        response.end(JSON.stringify(ids.map(id => ({
          game_id: id, tournament_id: TOURNAMENT_ID, is_paused: pausedGames.has(id), pause_revision: pauseRevision
        }))));
      });
    }
    if (request.method === 'POST' && url.pathname.endsWith('/load_game_server_room_states')) return response.end('[]');
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
    response.statusCode = 404;
    response.end('{}');
  });
}

async function openMatch(browser, game) {
  const errors = [];
  const pages = [];
  for (const slot of [1, 2]) {
    const context = await browser.newContext({ viewport: { width: 420, height: 860 } });
    /* Sans accès à Internet, le plateau 3D (dames, échecs) a besoin d'une copie
       locale de Three.js r128 : THREE_RUNTIME_FILE. */
    if (process.env.THREE_RUNTIME_FILE) {
      await context.route('**/vendor/three-r128.min.js', route =>
        route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
    }
    const page = await context.newPage();
    page.on('pageerror', e => errors.push(`joueur ${slot} : ${e.message}`));
    page.on('response', r => {
      if (r.url().startsWith(GAME_URL) && r.status() >= 400) errors.push(`joueur ${slot} : HTTP ${r.status()} ${r.url().slice(GAME_URL.length).split('?')[0]}`);
    });
    pages.push(page);
  }
  await Promise.all(pages.map((page, i) => page.goto(pageUrl(game, i + 1))));
  return { pages, errors, close: () => Promise.all(pages.map(p => p.context().close())) };
}

async function quoridor(browser, game) {
  const match = await openMatch(browser, game);
  const [p1, p2] = match.pages;
  const started = await waitFor(async () => {
    const states = await Promise.all(match.pages.map(p => p.evaluate(() => ({ ready: gameReady, slot: currentSlot }))));
    return states.every(s => s.ready) && states[0].slot === states[1].slot ? states[0].slot : null;
  }, 12000);
  check('Quoridor : la partie démarre chez les deux joueurs', started === 1 || started === 2, started);

  const guard = await p1.evaluate(() => String(handleTap).includes('sendAuthoritativeMove'));
  check('Quoridor : le garde-fou de synchronisation est actif', guard);

  const mover = started === 2 ? p2 : p1;
  const other = mover === p1 ? p2 : p1;
  const played = await mover.evaluate(() => {
    const mv = vmoves[0];
    if (!mv || mode !== 'move') return null;
    let x = cx(mv.c) + CS / 2, y = cy(mv.r) + CS / 2;
    if (MY_SLOT === 2) { x = canvas.width - x; y = canvas.height - y; }
    handleTap({ x, y });
    return { slot: MY_SLOT, r: mv.r, c: mv.c };
  });
  check('Quoridor : le joueur au trait a un déplacement jouable', !!played, played);
  if (played) {
    const seen = await waitFor(() => other.evaluate(({ slot, r, c }) => {
      const pos = slot === 1 ? s1Pos : s2Pos;
      return pos.r === r && pos.c === c && currentSlot !== slot;
    }, played), 6000);
    check('Quoridor : le coup, validé par le serveur, arrive chez l adversaire', seen === true);
    const moverSynced = await waitFor(() => mover.evaluate(({ slot, r, c }) => {
      const pos = slot === 1 ? s1Pos : s2Pos;
      return pos.r === r && pos.c === c && currentSlot !== slot && !isProcessing;
    }, played), 6000);
    check('Quoridor : le joueur voit son propre coup confirmé, sans retour en arrière', moverSynced === true);
  }

  /* Une manche entière, jusqu'à la ligne d'arrivée : chacun avance au plus
     court. La manche suivante appelait `applyServerState`, recopiée du
     Morpion à cinq mais absente de cette page — une exception à chaque
     nouvelle manche de la série. */
  const roundOver = () => Promise.all(match.pages.map(p => p.evaluate(() => seriesState.roundsPlayed >= 1)));
  for (let turn = 0; turn < 60 && !(await roundOver()).every(Boolean); turn++) {
    const states = await Promise.all(match.pages.map(p => p.evaluate(() => ({ ready: gameReady, slot: currentSlot, mine: MY_SLOT, waiting: isProcessing }))));
    const active = match.pages.find((p, i) => states[i].ready && states[i].slot === states[i].mine && !states[i].waiting);
    if (!active) { await sleep(150); continue; }
    await active.evaluate(() => {
      if (mode !== 'move' || !vmoves.length) return;
      const goal = MY_SLOT === 1 ? 0 : 8;
      const best = vmoves.slice().sort((a, b) => Math.abs(a.r - goal) - Math.abs(b.r - goal))[0];
      let x = cx(best.c) + CS / 2, y = cy(best.r) + CS / 2;
      if (MY_SLOT === 2) { x = canvas.width - x; y = canvas.height - y; }
      handleTap({ x, y });
    });
    await sleep(250);
  }
  check('Quoridor : une manche se joue jusqu à la ligne d arrivée', (await roundOver()).every(Boolean));
  const secondRound = await waitFor(async () => (await Promise.all(match.pages.map(p => p.evaluate(() =>
    gameReady && seriesState.currentRound === 2 && s1Pos.r === 8 && s2Pos.r === 0)))).every(Boolean), 12000);
  check('Quoridor : la manche 2 repart d un plateau neuf chez les deux joueurs', secondRound === true);
  const finalModal = await Promise.all(match.pages.map(p => p.evaluate(() =>
    document.getElementById('gameOverModal').classList.contains('show'))));
  check('Quoridor : perdre une manche n ouvre pas l écran de fin de match', finalModal.every(shown => !shown), finalModal);

  return match;
}

/* Les variables des pages Penalty et Chifoumi vivent dans une fonction : ces
   deux parcours lisent donc ce que le joueur voit, pas l'état interne. */
const text = (page, selector) => page.evaluate(sel => {
  const el = document.querySelector(sel);
  return el ? el.textContent.trim() : null;
}, selector);

async function tournamentPause(game, match) {
  const overlayShown = () => Promise.all(match.pages.map(p =>
    p.evaluate(() => !!document.getElementById('mindspille-tournament-pause'))));
  pausedGames.add(game.id); pauseRevision++;
  const shown = await waitFor(async () => (await overlayShown()).every(Boolean), 8000);
  check(`${game.key} : une pause de tournoi couvre les deux plateaux`, shown === true);
  pausedGames.delete(game.id); pauseRevision++;
  const gone = await waitFor(async () => (await overlayShown()).every(v => !v), 8000);
  check(`${game.key} : la reprise libère les deux plateaux`, gone === true);
}

async function penalty(browser, game) {
  const match = await openMatch(browser, game);
  const zones = await waitFor(async () => {
    const counts = await Promise.all(match.pages.map(p => p.evaluate(() => document.querySelectorAll('.zone-btn').length)));
    return counts.every(n => n === 3);
  }, 12000);
  check('Penalty : les zones de tir et de parade s affichent chez les deux joueurs', zones === true);
  const timing = await waitFor(async () => (await Promise.all(match.pages.map(p =>
    p.evaluate(() => parseFloat(document.getElementById('timer-fill').style.width) < 100)))).every(Boolean), 4000);
  check('Penalty : le minuteur de la manche tourne', timing === true);

  await match.pages[0].evaluate(() => document.querySelectorAll('.zone-btn')[0].click());
  await match.pages[1].evaluate(() => document.querySelectorAll('.zone-btn')[1].click());
  const resolved = await waitFor(async () => (await Promise.all(match.pages.map(p =>
    p.evaluate(() => document.querySelectorAll('#roundsProgress .round-dot.played').length >= 1)))).every(Boolean), 15000);
  check('Penalty : les deux choix donnent un tir résolu chez les deux joueurs', resolved === true);
  const round = await waitFor(async () => {
    const labels = await Promise.all(match.pages.map(p => text(p, '#round-lbl')));
    return labels.every(l => /^Manche 2 \//.test(l || '')) ? labels : null;
  }, 12000);
  check('Penalty : la manche suivante s ouvre', !!round, round);
  return match;
}

async function chifoumi(browser, game) {
  const match = await openMatch(browser, game);
  const [p1, p2] = match.pages;
  /* La manche est ouverte quand startRound() a allumé le profil du joueur ;
     avant, un clic est ignoré — c'est là que la page plantait. */
  const ready = await waitFor(async () => (await Promise.all(match.pages.map(p => p.evaluate(() => {
    const buttons = [...document.querySelectorAll('.choice-btn')];
    return document.getElementById('profile-human').classList.contains('human-active')
      && buttons.length === 3 && buttons.every(b => !b.classList.contains('disabled') && !b.classList.contains('locked'));
  })))).every(Boolean), 12000);
  check('Chifoumi : les boutons Pierre / Feuille / Ciseaux sont jouables', ready === true);

  const dots = await p1.evaluate(() => ({
    dots: document.querySelectorAll('#roundsProgress .round-dot').length,
    label: document.getElementById('roundLabel').textContent
  }));
  const announced = Number((/\/\s*(\d+)/.exec(dots.label) || [])[1]);
  check('Chifoumi : un repère par manche annoncée par le serveur', announced > 0 && dots.dots === announced, dots);

  await p1.evaluate(() => document.querySelector('.choice-btn[data-choice="pierre"]').click());
  await p2.evaluate(() => document.querySelector('.choice-btn[data-choice="ciseaux"]').click());
  const scored = await waitFor(async () => {
    const [a, b] = await Promise.all(match.pages.map(p => p.evaluate(() => ({
      me: document.getElementById('playerScore').textContent.trim(), op: document.getElementById('aiScore').textContent.trim()
    }))));
    return a.me === '1' && a.op === '0' && b.me === '0' && b.op === '1' ? true : null;
  }, 15000);
  check('Chifoumi : pierre bat ciseaux, le point est compté des deux côtés', scored === true);
  return match;
}

/* Les autres pages : la partie démarre, sans erreur. */
async function startsCleanly(browser, game) {
  const match = await openMatch(browser, game);
  await sleep(6000);
  return match;
}

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK pages multijoueur ignorées');
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
      ALLOWED_ORIGIN: GAME_URL,
      TOURNAMENT_CONTROL_INTERVAL_MS: '1000'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));

  let browser;
  try {
    await waitForHealth();

    const script = await new Promise((resolve, reject) => {
      http.get(`${GAME_URL}/tournament-pause-client.js`, res => {
        let body = ''; res.on('data', c => { body += c; });
        res.on('end', () => resolve({ status: res.statusCode, type: res.headers['content-type'], body }));
      }).on('error', reject);
    });
    check('/tournament-pause-client.js est servi en JavaScript', script.status === 200 && /javascript/.test(script.type || '') && /tournament:paused/.test(script.body), script.status);

    browser = await chromium.launch({ executablePath });
    const scenarios = { quoridor, penalty, chifoumi };
    for (const game of GAMES) {
      console.log(`  — ${game.key}`);
      const match = await (scenarios[game.key] || startsCleanly)(browser, game);
      await tournamentPause(game, match);
      check(`${game.key} : aucune exception JavaScript, aucune ressource manquante`, match.errors.length === 0, [...new Set(match.errors)]);
      await match.close();
    }
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
    await new Promise(r => db.close(r));
  }
  if (failures) process.exitCode = 1;
  else console.log('OK pages multijoueur');
}

main().catch(error => { console.error(error); process.exitCode = 1; });
