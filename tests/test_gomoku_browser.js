/**
 * Morpion à cinq — parcours réel, dans deux vrais navigateurs.
 *
 * Le test précédent (`test_gomoku.js`) parle au serveur en Socket.IO et le
 * valide très bien. Il n'a pourtant pas vu passer un bug qui rendait CHAQUE
 * partie injouable : `startNewGame()` levait une TypeError sur un nœud détruit
 * par `applyProfiles()`, l'exception coupait la fonction avant que
 * `gameReady` ne passe à true, et plus aucun clic ne posait de pion. Le
 * plateau s'affichait normalement — rien ne trahissait la panne.
 *
 * Aucun test de protocole ne pouvait l'attraper : le serveur, lui, allait
 * parfaitement bien. Il fallait ouvrir la page.
 *
 * On lance donc le vrai serveur, on ouvre la vraie page dans Chromium pour
 * les deux joueurs, et on joue une partie entière en cliquant sur le plateau.
 */
const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3152;
const MOCK_DB_PORT = 3153;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';

const GAME_ID = '30000000-0000-4000-8000-000000000001';
const P1 = { user: '30000000-0000-4000-8000-000000000011', supabase: '30000000-0000-4000-8000-000000000021', name: 'Alice' };
const P2 = { user: '30000000-0000-4000-8000-000000000012', supabase: '30000000-0000-4000-8000-000000000022', name: 'Bob' };

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
        id: id || GAME_ID, game_type: 'gomoku',
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
function chromiumBinary() {
  if (process.platform === 'win32') {
    const windowsCandidates = [
      'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
      'C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe',
      'C:\\Program Files\\Microsoft\\Edge\\Application\\msedge.exe'
    ];
    return windowsCandidates.find(candidate => fs.existsSync(candidate));
  }
  const root = process.env.PLAYWRIGHT_BROWSERS_PATH || '/opt/pw-browsers';
  if (!fs.existsSync(root)) return undefined;
  const candidates = fs.readdirSync(root)
    .filter(name => name.startsWith('chromium'))
    .sort()
    .reverse()
    .flatMap(name => [
      path.join(root, name, 'chrome-linux', 'chrome'),
      path.join(root, name, 'chrome-linux', 'headless_shell')
    ]);
  return candidates.find(candidate => fs.existsSync(candidate));
}

const tokenFor = p => jwt.sign({ userId: p.user, supabaseId: p.supabase, username: p.name }, JWT_SECRET);

function boardUrl(slot) {
  const params = new URLSearchParams({
    room: GAME_ID, gameId: GAME_ID, player: String(slot),
    p1Id: P1.supabase, p2Id: P2.supabase,
    p1Name: P1.name, p2Name: P2.name,
    bet: '0', currency: 'HTG'
  });
  const token = tokenFor(slot === 1 ? P1 : P2);
  return `${GAME_URL}/gomoku?${params.toString()}#${new URLSearchParams({ token }).toString()}`;
}

/** Clique la case (r,c) en visant son centre réel sur le canvas. */
async function clickCell(page, r, c) {
  const box = await page.evaluate(([row, col]) => {
    const rect = document.getElementById('board').getBoundingClientRect();
    return { x: rect.left + ORIGIN + col * CELL + CELL / 2, y: rect.top + ORIGIN + row * CELL + CELL / 2 };
  }, [r, c]);
  await page.mouse.click(box.x, box.y);
}

const readState = page => page.evaluate(() => ({
  gameReady: window.gameReady === true,
  gameOver: window.gameOver === true,
  currentSlot: window.currentSlot,
  stones: (window.board || []).filter(Boolean).length,
  overlayHidden: document.getElementById('waiting-overlay').classList.contains('hidden'),
  modalShown: document.getElementById('gameOverModal').classList.contains('show')
}));

async function main() {
  /* Sans navigateur dans l'image (integration continue nue), on ne fait pas
     echouer la suite : on annonce le saut, et les tests de protocole restent
     la garantie minimale. */
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK parcours navigateur Gomoku ignoré');
    return;
  }

  const mockDb = startMockDatabase();
  await new Promise(r => mockDb.listen(MOCK_DB_PORT, '127.0.0.1', r));
  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT), NODE_ENV: 'test', JWT_SECRET,
      SUPABASE_URL: `http://127.0.0.1:${MOCK_DB_PORT}`,
      SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      // Le navigateur charge la page depuis cette origine : sans elle, la
      // poignee de main Socket.IO est refusee par le controle CORS et la
      // partie ne demarre jamais.
      ALLOWED_ORIGIN: GAME_URL
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));

  let browser;
  try {
    await waitForHealth();
    browser = await chromium.launch({ executablePath });

    const ctx1 = await browser.newContext({ viewport: { width: 420, height: 900 } });
    const ctx2 = await browser.newContext({ viewport: { width: 420, height: 900 } });
    const page1 = await ctx1.newPage();
    const page2 = await ctx2.newPage();

    const errors = [];
    for (const [tag, page] of [['J1', page1], ['J2', page2]]) {
      page.on('pageerror', e => errors.push(`${tag}: ${e.message}`));
    }

    await Promise.all([page1.goto(boardUrl(1)), page2.goto(boardUrl(2))]);
    // Le serveur arme le tour du slot 1 trois secondes apres le depart.
    await sleep(7000);

    const s1 = await readState(page1);
    const s2 = await readState(page2);

    check('aucune exception JavaScript sur les deux plateaux', errors.length === 0, errors);
    check('le voile de chargement se retire des deux cotes', s1.overlayHidden && s2.overlayHidden, { s1, s2 });
    // L'assertion qui manquait : un plateau visible mais gameReady=false est
    // un plateau mort, et rien a l'ecran ne le montre.
    check('les deux plateaux sont réellement jouables (gameReady)', s1.gameReady && s2.gameReady, { s1, s2 });
    const openingSlot = s1.currentSlot;
    check('le premier joueur est tire et synchronise',
      (openingSlot === 1 || openingSlot === 2) && s2.currentSlot === openingSlot,
      { s1, s2 });
    const openerPage = openingSlot === 1 ? page1 : page2;
    const responderPage = openingSlot === 1 ? page2 : page1;

    // Slot 1 pose une croix : elle doit apparaitre sur LES DEUX ecrans.
    await clickCell(openerPage, 7, 3);
    await sleep(900);
    check('le clic du slot 1 pose un pion', (await readState(page1)).stones === 1);
    check('le pion apparaît aussi chez le slot 2', (await readState(page2)).stones === 1);
    check('le trait passe a l adversaire', (await readState(page2)).currentSlot === (openingSlot === 1 ? 2 : 1));

    // Un clic hors tour ne doit rien poser.
    await clickCell(openerPage, 0, 0);
    await sleep(600);
    check('un clic hors tour est sans effet', (await readState(page1)).stones === 1);

    // Partie complete : le slot 1 aligne cinq croix en ligne 7.
    const replies = [[0, 0], [1, 0], [2, 0], [3, 0]];
    for (let i = 0; i < 4; i++) {
      await clickCell(responderPage, replies[i][0], replies[i][1]);
      await sleep(700);
      await clickCell(openerPage, 7, 4 + i);
      await sleep(700);
    }

    await sleep(1500);
    const afterRound1 = await readState(page1);
    check('manche 1 gagnée : la SÉRIE ne se termine pas (6 manches réglementaires)',
      afterRound1.gameOver === false, afterRound1);

    await sleep(2600);
    const round2State1 = await readState(page1);
    check('manche 2 : le plateau est réinitialisé et rejouable', round2State1.gameReady === true && round2State1.stones === 0, round2State1);

    async function playBrowserRoundToWin(winnerPage, loserPage, starterIsWinner) {
      const wCells = [[7, 3], [7, 4], [7, 5], [7, 6], [7, 7]];
      const lCells = [[0, 0], [2, 0], [4, 0], [6, 0], [8, 0]];
      let wi = 0, li = 0;
      let turn = starterIsWinner ? 'W' : 'L';
      const totalMoves = starterIsWinner ? 9 : 10;
      for (let i = 0; i < totalMoves; i++) {
        if (turn === 'W') {
          const [r, c] = wCells[wi++];
          await clickCell(winnerPage, r, c);
          await sleep(700);
          turn = 'L';
        } else {
          const [r, c] = lCells[li++];
          await clickCell(loserPage, r, c);
          await sleep(700);
          turn = 'W';
        }
      }
    }

    for (let round = 2; round <= 4; round++) {
      const starterIsWinner = (round % 2 === 1);
      await playBrowserRoundToWin(openerPage, responderPage, starterIsWinner);
      if (round < 4) {
        await sleep(2600);
        const mid = await readState(page1);
        check(`manche ${round} gagnée : la série continue`, mid.gameOver === false, mid);
      }
    }

    await sleep(1800);
    const end1 = await readState(page1);
    const end2 = await readState(page2);
    check('la série (4 manches à 0) termine bien la partie', end1.gameOver && end2.gameOver, { end1, end2 });
    check('la fenêtre de fin s’ouvre chez les deux joueurs', end1.modalShown && end2.modalShown, { end1, end2 });
    check('aucune exception pendant toute la partie', errors.length === 0, errors);
  } finally {
    if (browser) await browser.close().catch(() => undefined);
    server.kill('SIGKILL');
    await new Promise(r => mockDb.close(r));
  }

  if (failures) {
    console.error(`FAIL ${failures} vérification(s) navigateur`);
    process.exit(1);
  }
  console.log('OK parcours navigateur Gomoku passé');
}

main().catch(e => { console.error(e); process.exit(1); });
