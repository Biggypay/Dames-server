/**
 * Fin d'une partie de dames : deux vrais navigateurs, serveur réel.
 *
 * Le plateau décidait seul de la fin de partie. Après un coup blanc qui laisse
 * les Blancs sans coup jouable alors que c'est aux Noirs de jouer, chaque page
 * concluait aussitôt (« Les Rouges gagnent ») et se figeait. Le serveur, lui,
 * attendait le coup noir : la partie finissait 90 s plus tard au temps… en
 * faveur des Blancs, contre ce que les deux écrans avaient affiché.
 *
 * Désormais seule l'annonce du serveur termine la page : ici, la partie
 * continue après le coup blanc, les Noirs prennent la dernière pièce, et
 * chaque joueur voit le vrai résultat.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3252;
const DB_PORT = 3253;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const DB_URL = `http://127.0.0.1:${DB_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';
const GAME_ID = '30000000-0000-4000-8000-000000000306';
const P1 = { user: '30000000-0000-4000-8000-000000000381', supabase: '30000000-0000-4000-8000-000000000391', name: 'Alice' };
const P2 = { user: '30000000-0000-4000-8000-000000000382', supabase: '30000000-0000-4000-8000-000000000392', name: 'Bob' };

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
  return `${GAME_URL}/dames?${params}#${new URLSearchParams({ token: tokenFor(slot === 1 ? P1 : P2) })}`;
}

// Un pion blanc (5,0) face à trois pions noirs. Après 5,0 → 4,1 les Blancs
// n'ont plus de coup, mais les Noirs ont le trait et prennent : la partie
// n'est pas finie tant qu'ils n'ont pas joué.
const WHITE = 1, BLACK = 2;
function savedRoom() {
  const board = Array.from({ length: 10 }, () => Array(10).fill(0));
  board[5][0] = WHITE;
  board[3][0] = BLACK; board[3][2] = BLACK; board[2][3] = BLACK;
  const clientBoard = board.map(row => row.map(p => (p ? { player: p === WHITE ? 0 : 1, king: false, dying: false } : null)));
  const players = {};
  for (const [slot, p] of [[1, P1], [2, P2]]) players[slot] = { slot, supabaseId: p.supabase, name: p.name, connected: false, socketId: null, userId: null };
  return {
    game_type: 'dames', room_id: GAME_ID, game_id: GAME_ID, status: 'paused', db_status: 'in_progress',
    state: { id: GAME_ID, databaseGameId: GAME_ID, players, status: 'paused', betAmount: 0, currency: 'HTG',
      engineBoard: board, boardState: JSON.stringify(clientBoard), currentPlayer: 0, stateVersion: 7, lastMove: null, startedAt: Date.now() }
  };
}

function mockDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, DB_URL);
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
      return response.end(JSON.stringify([{
        id: GAME_ID, game_type: 'checkers', player1_id: P1.supabase, player2_id: P2.supabase,
        bet_amount: 0, status: 'in_progress', is_ai_opponent: false, is_tournament: false, game_settings: {}
      }]));
    }
    if (request.method === 'POST' && url.pathname.endsWith('/load_game_server_room_states')) return response.end(JSON.stringify([savedRoom()]));
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
    response.statusCode = 404;
    response.end('{}');
  });
}

/* Le code de la page vit dans une fonction. Pour ce test seulement, la page
   servie au navigateur publie un accès en lecture à son état et à son propre
   geste de jeu ; la page réelle n'est pas modifiée. */
const TEST_HOOK = `window.__dames = {
  state: function(){ return { gameReady: gameReady, gameOver: gameOver, isProcessing: isProcessing, currentPlayer: currentPlayer, board: board }; },
  moves: function(c){ return getAllValidMoves(c).moves; },
  play: function(from, to){ executePlayerStep(from, to); }
};
})();`;
async function instrument(context) {
  await context.route(url => url.pathname === '/dames', async route => {
    const response = await route.fetch();
    const html = await response.text();
    const at = html.lastIndexOf('})();');
    route.fulfill({ response, body: html.slice(0, at) + TEST_HOOK + html.slice(at + 5) });
  });
}
const state = page => page.evaluate(() => window.__dames.state());

/** Joue, depuis la page, le seul coup de ce camp, comme un clic l'aurait fait. */
function playOnlyMove(page, color) {
  return page.evaluate(c => {
    const s = window.__dames.state(), moves = window.__dames.moves(c);
    if (!moves.length || s.currentPlayer !== c || s.isProcessing || s.gameOver) return null;
    window.__dames.play(moves[0].from, moves[0].to);
    return { from: moves[0].from, to: { row: moves[0].to.row, col: moves[0].to.col } };
  }, color);
}

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK fin de partie de dames ignorée');
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
      ALLOWED_ORIGIN: GAME_URL
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));

  let browser;
  const errors = [];
  try {
    await waitForHealth();
    // Une page servie par une route de test n'est plus vue comme « locale » :
    // Chromium bloquerait alors sa connexion au serveur de jeu en 127.0.0.1.
    browser = await chromium.launch({ executablePath, args: ['--disable-features=LocalNetworkAccessChecks'] });
    const pages = [];
    for (const slot of [1, 2]) {
      const context = await browser.newContext({ viewport: { width: 420, height: 860 } });
      if (process.env.THREE_RUNTIME_FILE) {
        await context.route('**/vendor/three-r128.min.js', route =>
          route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
      }
      await instrument(context);
      const page = await context.newPage();
      page.on('pageerror', e => errors.push(`joueur ${slot} : ${e.message}`));
      pages.push(page);
    }
    const [white, black] = pages;
    await Promise.all(pages.map((page, i) => page.goto(pageUrl(i + 1))));
    const ready = await waitFor(async () => (await Promise.all(pages.map(state))).every(s => s.gameReady && !s.isProcessing && s.board[5][0] !== null), 15000);
    check('la position est restaurée chez les deux joueurs', ready === true, JSON.stringify(await Promise.all(pages.map(async p => { const s = await state(p); return { ...s, board: s.board && s.board.length, loading: await p.evaluate(() => document.querySelector('#loading p') && document.querySelector('#loading p').textContent) }; }))));
    if (ready !== true) throw new Error('position non restaurée');

    const whiteMove = await playOnlyMove(white, 0);
    check('les Blancs jouent leur pion', !!whiteMove, whiteMove);
    const blackSees = await waitFor(async () => { const s = await state(black); return s.board[4][1] !== null && s.currentPlayer === 1 && !s.isProcessing; }, 8000);
    check('le coup blanc arrive chez les Noirs', blackSees === true);
    await sleep(1500);
    const afterWhite = await Promise.all(pages.map(async p => ({ gameOver: (await state(p)).gameOver, toast: await p.evaluate(() => document.getElementById('toast-title').textContent) })));
    check('Blancs bloqués mais Noirs au trait : aucune page ne déclare la partie finie',
      afterWhite.every(state => !state.gameOver), JSON.stringify(afterWhite));

    const blackMove = await playOnlyMove(black, 1);
    check('les Noirs peuvent toujours jouer (et prennent)', !!blackMove, blackMove);
    const titles = await waitFor(async () => {
      const states = await Promise.all(pages.map(async p => (await state(p)).gameOver && await p.evaluate(() => document.getElementById('toast-title').textContent)));
      return states.every(Boolean) ? states : null;
    }, 10000);
    check('les Blancs voient le vrai résultat : défaite', titles && /perdu/i.test(titles[0]), titles);
    check('les Noirs voient le vrai résultat : victoire', titles && /gagné/i.test(titles[1]), titles);
    check('aucune exception JavaScript', errors.length === 0, [...new Set(errors)]);
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
    await new Promise(r => db.close(r));
  }
  if (failures) process.exitCode = 1;
  else console.log('OK fin de partie de dames décidée par le serveur');
}

main().catch(error => { console.error(error); process.exitCode = 1; });
