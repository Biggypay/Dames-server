/**
 * Quoridor, intuitif et immersif (owner, 2026-11-18) — public/quoridor-ui.js et les trois pages.
 *
 * Deux vrais navigateurs, une vraie partie en ligne, puis l'IA et « entre amis » :
 * 1. en-tête : le score de la série en grand (« 0 – 0 ») et « Manche 1 · 6 » ; sous chaque profil, les
 *    cases qui restent jusqu'à l'arrivée ; le compteur de murs à la couleur du joueur ;
 * 2. plateau : chaque camp teinté de la couleur de son joueur (Blanc en bas pour le joueur 1, Rouge en
 *    haut), les deux bandes nommées (« Votre arrivée », « Votre camp ») ;
 * 3. un seul toucher pose un mur (owner, 2026-11-19 : « pas besoin de cliquer deux fois ») ; chez
 *    l'adversaire il apparaît à la couleur de celui qui l'a posé ; un pion GLISSE vers sa case ;
 *    aucun cadre autour des camps, aucun pointillé (« enlève les petits traits »), aucune lueur sur les murs ;
 *    chez l'adversaire il apparaît à la couleur de celui qui l'a posé — le serveur dit qui (hO / vO) ;
 * 4. fin de manche : la carte « Manche gagnée » / « Manche perdue » avec le score, chez chacun la
 *    sienne, et JAMAIS la fiche de fin de match chez le perdant (la page déclarait le match perdu dès
 *    que l'adversaire touchait son camp) ; puis la manche suivante repart des camps ;
 * 5. l'IA et « entre amis » : le même en-tête, les mêmes camps, le mur en deux temps.
 */
const { spawn } = require('child_process');
const http = require('http');
const fs = require('fs');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3216;
const DB_PORT = 3217;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const DB_URL = `http://127.0.0.1:${DB_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';
const SHOTS = process.env.QUORIDOR_SHOTS || '';
const P1 = { user: '41000000-0000-4000-8000-000000000281', supabase: '41000000-0000-4000-8000-000000000291', name: 'Alice' };
const P2 = { user: '41000000-0000-4000-8000-000000000282', supabase: '41000000-0000-4000-8000-000000000292', name: 'Bob' };
const GAME_ID = '41000000-0000-4000-8000-000000000201';

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : JSON.stringify(detail)); }
}
const sleep = ms => new Promise(r => setTimeout(r, ms));
async function waitFor(fn, timeoutMs = 10000, stepMs = 150) {
  const end = Date.now() + timeoutMs;
  let last = null;
  while (Date.now() < end) {
    try { last = await fn(); if (last) return last; } catch (_) {}
    await sleep(stepMs);
  }
  return last;
}
async function waitForHealth(retries = 60) {
  for (let i = 0; i < retries; i++) {
    const ok = await new Promise(resolve => http.get(`${GAME_URL}/health`, r => { r.resume(); resolve(r.statusCode === 200); }).on('error', () => resolve(false)));
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
    bet: '1000', currency: 'HTG'
  });
  return `${GAME_URL}/quoridor?${params}#${new URLSearchParams({ token: tokenFor(slot === 1 ? P1 : P2) })}`;
}
function mockDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, DB_URL);
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
      const id = String(url.searchParams.get('id') || '').replace(/^eq\./, '');
      return response.end(JSON.stringify(id === GAME_ID ? [{
        id: GAME_ID, game_type: 'quoridor', player1_id: P1.supabase, player2_id: P2.supabase,
        bet_amount: 1000, status: 'in_progress', is_ai_opponent: false, is_tournament: false, game_settings: {}
      }] : []));
    }
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
    response.statusCode = 404;
    response.end('{}');
  });
}
async function shot(page, name) {
  if (!SHOTS) return;
  fs.mkdirSync(SHOTS, { recursive: true });
  await page.screenshot({ path: path.join(SHOTS, name + '.png') });
}

/** Ce que montrent l'en-tête et la page. */
const readUi = page => page.evaluate(() => {
  const nums = [...document.querySelectorAll('#top .score-row .snum')].map(n => n.textContent);
  const chip = id => { const el = document.getElementById(id); return el ? getComputedStyle(el).backgroundColor : null; };
  const card = document.getElementById('q-result');
  return {
    score: nums,
    manche: (document.querySelector('#top .manche-lbl') || {}).textContent || '',
    goalMe: document.getElementById('goal-me').textContent,
    goalOp: document.getElementById('goal-op').textContent,
    chipMe: chip('chip-me'), chipOp: chip('chip-op'),
    result: card && card.classList.contains('q-show') ? (card.querySelector('.q-title') || {}).textContent : null,
    resultScore: card && card.classList.contains('q-show') ? [...card.querySelectorAll('.q-final b')].map(b => b.textContent) : null,
    modal: document.getElementById('gameOverModal').classList.contains('show'),
    ready: typeof gameReady !== 'undefined' && gameReady,
    mySlot: MY_SLOT, turn: currentSlot, s1: s1Pos, s2: s2Pos
  };
});

/** La couleur d'un point du plateau, en coordonnées du canevas (avant retournement). */
const pixelAt = (page, x, y) => page.evaluate(([x, y]) => {
  const flip = typeof IS_SPECTATOR !== 'undefined' && !IS_SPECTATOR && MY_SLOT === 2;
  const px = flip ? canvas.width - x : x, py = flip ? canvas.height - y : y;
  /* Le canevas est transparent : on compose sur le fond de la page (#2a2766 environ). */
  const d = ctx.getImageData(Math.round(px), Math.round(py), 1, 1).data, a = d[3] / 255, bg = [42, 39, 102];
  return [0, 1, 2].map(i => Math.round(d[i] * a + bg[i] * (1 - a)));
}, [x, y]);
const cellCenter = (page, r, c) => page.evaluate(([r, c]) => ({ x: cx(c) + CS / 2, y: cy(r) + CS / 2 }), [r, c]);
const wallCenter = (page, kind, r, c) => page.evaluate(([kind, r, c]) => {
  const rect = kind === 'h' ? hwRect(r, c) : vwRect(r, c);
  return { x: rect.x + rect.w / 2, y: rect.y + rect.h / 2 };
}, [kind, r, c]);
/** Un vrai toucher sur le canevas, au point du plateau (r, c) donné. */
async function tapBoard(page, x, y) {
  const box = await page.evaluate(([x, y]) => {
    const rect = canvas.getBoundingClientRect(), flip = typeof IS_SPECTATOR !== 'undefined' && !IS_SPECTATOR && MY_SLOT === 2;
    const px = flip ? canvas.width - x : x, py = flip ? canvas.height - y : y;
    return { x: rect.left + px * rect.width / canvas.width, y: rect.top + py * rect.height / canvas.height };
  }, [x, y]);
  await page.mouse.click(box.x, box.y);
}
const isWhite = rgb => rgb[0] > 170 && rgb[1] > 170 && rgb[2] > 170;
const isRed = rgb => rgb[0] > 170 && rgb[1] < 140 && rgb[2] < 140;

async function online(browser) {
  const errors = [];
  const pages = [];
  for (const slot of [1, 2]) {
    const context = await browser.newContext({ viewport: { width: 390, height: 844 }, deviceScaleFactor: 1 });
    const page = await context.newPage();
    page.on('pageerror', e => errors.push(`joueur ${slot} : ${e.message}`));
    pages.push(page);
  }
  await Promise.all(pages.map((page, i) => page.goto(pageUrl(i + 1))));
  const [a, b] = pages;
  await waitFor(async () => (await Promise.all(pages.map(readUi))).every(u => u.ready), 15000);
  await sleep(400);

  const [ua, ub] = await Promise.all([readUi(a), readUi(b)]);
  check('en-tête : le score en grand, 0 – 0, des deux côtés', ua.score.join('-') === '0-0' && ub.score.join('-') === '0-0', { ua: ua.score, ub: ub.score });
  check('en-tête : « Manche 1 · 6 »', ua.manche === 'Manche 1 · 6' && ub.manche === 'Manche 1 · 6', [ua.manche, ub.manche]);
  check('sous chaque profil : les cases restantes (8 au départ)', ua.goalMe === '▲ 8 cases' && ua.goalOp === '▼ 8 cases' && ub.goalMe === '▲ 8 cases', [ua.goalMe, ua.goalOp, ub.goalMe]);
  check('compteur de murs à la couleur du joueur (Blanc / Rouge)',
    /226, 232, 240/.test(ua.chipMe) && /248, 113, 113/.test(ua.chipOp) && /248, 113, 113/.test(ub.chipMe) && /226, 232, 240/.test(ub.chipOp), [ua.chipMe, ua.chipOp, ub.chipMe, ub.chipOp]);

  // Les camps : la rangée 8 (camp du joueur 1) blanche, la 0 (camp du joueur 2) rouge — vus de chaque côté.
  for (const [page, who] of [[a, 'Alice'], [b, 'Bob']]) {
    const c8 = await cellCenter(page, 8, 0), c0 = await cellCenter(page, 0, 0), mid = await cellCenter(page, 4, 0);
    const [p8, p0, pm] = await Promise.all([pixelAt(page, c8.x, c8.y), pixelAt(page, c0.x, c0.y), pixelAt(page, mid.x, mid.y)]);
    check(`${who} : le camp Blanc est plus clair qu'une case du milieu, le camp Rouge plus rouge`,
      p8[0] + p8[1] + p8[2] > pm[0] + pm[1] + pm[2] + 60 && p0[0] - p0[2] > pm[0] - pm[2] + 25, { p8, p0, pm });
  }
  // Les bandes nommées : en haut de l'écran, au-dessus du plateau, il y a du texte (des pixels clairs).
  const bandInk = await a.evaluate(() => {
    const d = ctx.getImageData(0, 0, canvas.width, BAND).data;
    let ink = 0; for (let i = 0; i < d.length; i += 4) if (d[i + 3] > 0 && d[i] + d[i + 1] + d[i + 2] > 400) ink++;
    return { ink, band: BAND };
  });
  check('les bandes « Votre arrivée » / « Votre camp » sont écrites au-dessus et au-dessous du plateau', bandInk.band >= 16 && bandInk.ink > 40, bandInk);
  await shot(a, '01-depart-alice');
  await shot(b, '02-depart-bob');

  // Plus aucun trait : ni cadre autour des camps, ni pointillé autour de l'arrivée. Entre la rangée 0 et
  // le bord du plateau (la marge PAD), le canevas est vide.
  const frame = await a.evaluate(() => {
    const y = BAND + Math.max(1, Math.floor(PAD / 2)), d = ctx.getImageData(0, Math.max(0, y - 1), canvas.width, 2).data;
    let ink = 0; for (let i = 3; i < d.length; i += 4) if (d[i] > 30) ink++;
    return { ink, pad: PAD };
  });
  check('aucun cadre ni pointillé autour des camps', frame.ink === 0, frame);

  // Le joueur qui a la main pose un mur horizontal, d'un seul toucher.
  const turn = ua.turn;
  const actor = turn === 1 ? a : b, other = turn === 1 ? b : a;
  const wr = turn === 1 ? 5 : 2, wc = 3;
  await actor.evaluate(() => setMode('wallH'));
  const w = await wallCenter(actor, 'h', wr, wc);
  await tapBoard(actor, w.x, w.y);
  const arrived = await waitFor(() => other.evaluate(([r, c]) => hW[r][c] && hO[r][c], [wr, wc]), 6000);
  check('un seul toucher : le mur est posé, chez l\'adversaire à la couleur de celui qui l\'a posé', arrived === turn, arrived);
  // Aucune lueur sur les murs (owner, 2026-11-19 : « il y a des lueurs dans les murs, enlève-les ») :
  // pendant un dessin complet du plateau, aucune ombre floue n'est jamais réglée.
  const glows = await other.evaluate(() => {
    const proto = CanvasRenderingContext2D.prototype, desc = Object.getOwnPropertyDescriptor(proto, 'shadowBlur');
    let seen = 0;
    Object.defineProperty(proto, 'shadowBlur', { configurable: true, get() { return desc.get.call(this); }, set(v) { if (v > 0) seen++; desc.set.call(this, v); } });
    try { draw(); } finally { Object.defineProperty(proto, 'shadowBlur', desc); }
    return seen;
  });
  check('aucune lueur autour des murs (aucune ombre floue au dessin)', glows === 0, glows);
  await sleep(300);
  const wp = await wallCenter(other, 'h', wr, wc);
  const wallRgb = await pixelAt(other, wp.x, wp.y);
  check(`le mur se voit ${turn === 1 ? 'blanc' : 'rouge'} chez l'adversaire`, turn === 1 ? isWhite(wallRgb) : isRed(wallRgb), wallRgb);
  const wallsLeft = await other.evaluate(() => document.getElementById('walls-op').textContent);
  check('le compteur de murs de l\'adversaire passe à 9', wallsLeft === '9', wallsLeft);
  await shot(other, '04-mur-colore-chez-adversaire');

  // On joue la manche : Alice monte droit vers le camp de Bob ; Bob se range à gauche de son camp.
  let glide = false;
  for (let i = 0; i < 40; i++) {
    const [sa, sb] = await Promise.all([readUi(a), readUi(b)]);
    if (sa.result || sb.result) break;
    const mover = sa.ready && sa.turn === 1 ? a : sb.ready && sb.turn === 2 ? b : null;
    if (!mover) { await sleep(150); continue; }
    const target = await mover.evaluate(() => {
      setMode('move');
      if (!vmoves.length) return null;
      if (MY_SLOT === 1) {
        let best = vmoves[0], bd = 999;
        vmoves.forEach(m => { const save = s1Pos; s1Pos = m; const d = bfsDist(s1Pos, 0); s1Pos = save; if (d < bd) { bd = d; best = m; } });
        return best;
      }
      const left = vmoves.filter(m => m.r <= 1).sort((x, y) => x.c - y.c);
      return left[0] || vmoves[0];
    });
    if (!target) { await sleep(150); continue; }
    const cpos = await cellCenter(mover, target.r, target.c);
    await tapBoard(mover, cpos.x, cpos.y);
    if (!glide) {
      // Chez l'adversaire, le pion qui vient de jouer glisse : il passe par des positions intermédiaires.
      const watcher = mover === a ? b : a, slot = mover === a ? 1 : 2;
      const seen = await waitFor(() => watcher.evaluate(s => QuoridorUI.pawnMoving(s) ? 'moving' : null, slot), 1500, 20);
      glide = seen === 'moving';
    }
    await sleep(350);
  }
  const res = await waitFor(async () => { const [x, y] = await Promise.all([readUi(a), readUi(b)]); return x.result && y.result ? [x, y] : null; }, 8000);
  check('le pion glisse de sa case à la suivante chez l\'adversaire', glide === true, glide);
  check('fin de manche : « Manche gagnée » chez Alice, « Manche perdue » chez Bob', res && res[0].result === 'Manche gagnée' && res[1].result === 'Manche perdue', res && [res[0].result, res[1].result]);
  check('la carte donne le score de chacun (1 – 0 / 0 – 1)', res && res[0].resultScore.join('-') === '1-0' && res[1].resultScore.join('-') === '0-1', res && [res[0].resultScore, res[1].resultScore]);
  check('le score de l\'en-tête suit (1 – 0 chez Alice)', res && res[0].score.join('-') === '1-0', res && res[0].score);
  check('Bob ne voit PAS la fiche de fin de match pour une manche perdue', res && !res[1].modal && !res[0].modal, res && [res[0].modal, res[1].modal]);
  await sleep(300);
  await shot(a, '05-manche-gagnee');
  await shot(b, '06-manche-perdue');
  const next = await waitFor(async () => { const [x, y] = await Promise.all([readUi(a), readUi(b)]); return x.ready && y.ready && x.s1.r === 8 && y.s2.r === 0 && !x.result ? [x, y] : null; }, 9000);
  check('la manche suivante repart des camps, « Manche 2 · 6 », la carte rangée', next && next[0].manche === 'Manche 2 · 6' && next[1].manche === 'Manche 2 · 6', next && [next[0].manche, next[1].manche]);
  const fresh = next && await a.evaluate(() => hW.every(row => row.every(v => !v)) && hO.every(row => row.every(v => v === 0)));
  check('nouvelle manche : plus aucun mur, plus aucun propriétaire', fresh === true, fresh);
  check('aucune erreur JavaScript en ligne', errors.length === 0, errors);
  await Promise.all(pages.map(p => p.context().close()));
}

async function offline(browser, route, label, local) {
  const context = await browser.newContext({ viewport: { width: 390, height: 844 }, deviceScaleFactor: 1 });
  const page = await context.newPage();
  const errors = [];
  page.on('pageerror', e => errors.push(e.message));
  await page.goto(`${GAME_URL}${route}?difficulty=easy&name=Alice&p1Name=Alice&p2Name=Bob`);
  await waitFor(() => page.evaluate(() => gameReady), 8000);
  await sleep(600);
  const ui = await readUi(page);
  check(`${label} : score « 0 – 0 » et « Manche 1 · 6 »`, ui.score.join('-') === '0-0' && ui.manche === 'Manche 1 · 6', [ui.score, ui.manche]);
  check(`${label} : cases restantes sous les profils`, /cases$/.test(ui.goalMe) && /cases$/.test(ui.goalOp), [ui.goalMe, ui.goalOp]);
  check(`${label} : compteurs de murs Blanc / Rouge`, /226, 232, 240/.test(ui.chipMe) && /248, 113, 113/.test(ui.chipOp), [ui.chipMe, ui.chipOp]);
  // Le mur d'un seul toucher, au tour du joueur 1 (contre l'IA : on attend son tour).
  await waitFor(() => page.evaluate(() => currentSlot === 1 && gameReady && !isProcessing), 8000);
  await page.evaluate(() => setMode('wallH'));
  const w = await wallCenter(page, 'h', 4, 2);
  await tapBoard(page, w.x, w.y);
  await sleep(250);
  const placed = await page.evaluate(() => ({ placed: hW[4][2], owner: hO[4][2] }));
  check(`${label} : un seul toucher pose le mur, à la couleur du joueur 1`, placed.placed && placed.owner === 1, placed);
  await shot(page, `07-${local ? 'entre-amis' : 'ia'}`);
  check(`${label} : aucune erreur JavaScript`, errors.length === 0, errors);
  await context.close();
}

(async () => {
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
    browser = await chromium.launch({ executablePath: chromiumBinary() });
    console.log('  — en ligne, deux joueurs');
    await online(browser);
    console.log('  — contre l’IA');
    await offline(browser, '/quoridor-ai', 'IA', false);
    console.log('  — entre amis');
    await offline(browser, '/quoridor-local', 'entre amis', true);
  } catch (e) {
    failures++;
    console.error('  FAIL', e && e.stack || e);
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
    db.close();
  }
  console.log(failures ? `\n${failures} échec(s)` : '\nQuoridor : tout passe');
  process.exit(failures ? 1 : 0);
})();
