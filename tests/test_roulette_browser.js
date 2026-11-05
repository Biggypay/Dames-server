/**
 * Roulette Royale dans de vrais navigateurs : deux joueurs, un spectateur,
 * puis les pages contre l'IA et entre amis.
 *
 * Ce que ce test protège :
 *   • aucun écran ne montre la couleur de l'adversaire avant que les deux
 *     choix soient verrouillés — ni l'adversaire, ni le spectateur : « a
 *     choisi », un cadenas, rien d'autre ;
 *   • les trois écrans voient le même sceau avant les choix, puis « Tirage
 *     vérifié » : l'empreinte publiée correspond au tirage révélé ;
 *   • la roue s'arrête, sur les trois écrans, sur la couleur tirée par le
 *     serveur (la case sous le pointeur, calculée depuis la rotation réelle) ;
 *   • le point n'est compté qu'à l'arrêt de la roue ; la couleur la plus
 *     proche de la tirée marque, chaque puce dit sa distance ; à égale
 *     distance, manche nulle ; même couleur → on rechoisit ;
 *   • les manches décisives vont par deux : après la première, l'autre joueur
 *     répond (« À vous de répondre », « Vous menez ») ; 1-1, une nouvelle
 *     paire ; 2-0, la fin ;
 *   • la fiche de fin ne s'ouvre qu'une fois la roue arrêtée, en haut, sans
 *     cacher la roue ;
 *   • temps de grâce : le bandeau dit qui doit jouer ; une couleur touchée
 *     mais pas verrouillée part d'elle-même avant la fin (pas de défaite sur
 *     un oubli de bouton) ;
 *   • une page rechargée retrouve sa propre couleur verrouillée ;
 *   • la page tient sans défiler du 320×568 au paysage et à l'écran partagé ;
 *   • contre l'IA et entre amis : un match complet, `practice_over`, et entre
 *     amis la couleur du premier n'est jamais montrée au second ;
 *   • le tour de roue de casino, à vitesse réelle (7,2 s) : un léger élan en
 *     arrière, un départ lent, la pleine vitesse au milieu, une longue fin au
 *     ralenti, le pointeur qui claque jusque dans le freinage, l'arrêt sur la
 *     couleur tirée.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const jwt = require('jsonwebtoken');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3282;
const DB_PORT = 3197;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const DB_URL = `http://127.0.0.1:${DB_PORT}`;
const JWT_SECRET = 'test-only-secret-with-more-than-32-characters';
const P1 = { user: '30000000-0000-4000-8000-000000000481', supabase: '30000000-0000-4000-8000-000000000491', name: 'Alice' };
const P2 = { user: '30000000-0000-4000-8000-000000000482', supabase: '30000000-0000-4000-8000-000000000492', name: 'Bob' };
const VIEWER = { user: '30000000-0000-4000-8000-000000000483', supabase: '30000000-0000-4000-8000-000000000493', name: 'Carla' };
const GAME = {
  match: '30000000-0000-4000-8000-0000000004a1',
  grace: '30000000-0000-4000-8000-0000000004a2',
  reload: '30000000-0000-4000-8000-0000000004a3'
};
/* Les tirages imposés (NODE_ENV=test) : un match connu d'avance. */
const DRAWS = {
  // Une valeur par manche ouverte (le rechoix de la manche 4 compris) ; en
  // manche décisive, 0 = la plus petite des deux couleurs, 1 = la plus grande.
  [GAME.match]: [0, 0, 1, 5, 3, 5, 0, 0, 1, 1],
  [GAME.grace]: [4, 4, 4, 4, 4],
  [GAME.reload]: [2, 2, 2, 2, 2]
};

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : JSON.stringify(detail)); }
}
const sleep = ms => new Promise(r => setTimeout(r, ms));
async function waitFor(fn, timeoutMs = 10000, stepMs = 100) {
  const end = Date.now() + timeoutMs;
  let value;
  while (Date.now() < end) {
    try { value = await fn(); } catch (_) { value = undefined; }
    if (value) return value;
    await sleep(stepMs);
  }
  return value;
}

function mockDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, DB_URL);
    response.setHeader('Content-Type', 'application/json');
    if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
      const id = String(url.searchParams.get('id') || '').replace(/^eq\./, '');
      if (!Object.values(GAME).includes(id)) return response.end('[]');
      return response.end(JSON.stringify([{
        id, game_type: 'color_roulette', player1_id: P1.supabase, player2_id: P2.supabase,
        bet_amount: 1000, status: 'in_progress', is_ai_opponent: false, is_tournament: false, game_settings: {}
      }]));
    }
    if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) {
      request.resume();
      return response.end(url.pathname.endsWith('load_game_server_room_states') ? '[]' : 'null');
    }
    response.statusCode = 404;
    response.end('{}');
  });
}
async function waitForHealth() {
  for (let i = 0; i < 60; i++) {
    const ok = await new Promise(resolve => {
      http.get(`${GAME_URL}/health`, res => { res.resume(); resolve(res.statusCode === 200); }).on('error', () => resolve(false));
    });
    if (ok) return;
    await sleep(200);
  }
  throw new Error('game server unavailable');
}

const tokenFor = p => jwt.sign({ userId: p.user, supabaseId: p.supabase, username: p.name }, JWT_SECRET);
function playerUrl(gameId, slot) {
  const params = new URLSearchParams({
    room: gameId, gameId, player: String(slot), p1Id: P1.supabase, p2Id: P2.supabase,
    p1Name: P1.name, p2Name: P2.name, bet: '1000', currency: 'HTG'
  });
  return `${GAME_URL}/roulette?${params}#${new URLSearchParams({ token: tokenFor(slot === 1 ? P1 : P2) })}`;
}

async function newPage(browser, label, errors, viewport = { width: 390, height: 844 }) {
  const context = await browser.newContext({ viewport });
  const page = await context.newPage();
  page.on('pageerror', e => errors.push(`${label} : ${e.message}`));
  page.on('response', r => {
    if (r.url().startsWith(GAME_URL) && r.status() >= 400) errors.push(`${label} : HTTP ${r.status()} ${r.url().slice(GAME_URL.length).split('?')[0]}`);
  });
  return page;
}

/* ── Ce que montre l'écran ── */
const text = (page, selector) => page.evaluate(sel => {
  const el = document.querySelector(sel);
  return el ? el.textContent.replace(/\s+/g, ' ').trim() : null;
}, selector);
/* Les deux puces : `me` à gauche, `op` à droite. */
const chips = page => page.evaluate(() => {
  const all = document.querySelectorAll('#duel .rr-chip');
  const read = chip => chip ? {
    color: chip.getAttribute('data-color'), locked: chip.classList.contains('rr-locked'), winner: chip.classList.contains('rr-winner'),
    label: (chip.parentElement.querySelector('.rr-pick-label') || {}).textContent || ''
  } : null;
  return { me: read(all[0]), op: read(all[1]) };
});
const scores = page => page.evaluate(() => [document.getElementById('playerScore').textContent, document.getElementById('aiScore').textContent].join('-'));
/* La couleur sous le pointeur, depuis la rotation réellement appliquée à la roue. */
const underPointer = page => page.evaluate(() => {
  const rotor = document.querySelector('.rr-rotor');
  const m = new DOMMatrixReadOnly(getComputedStyle(rotor).transform);
  const angle = (Math.atan2(m.b, m.a) * 180 / Math.PI + 360) % 360;
  const segs = [...rotor.querySelectorAll('path.rr-seg')];
  const n = segs.length;
  const index = Math.floor(((360 - angle) % 360) / (360 / n));
  const seg = segs.find(s => Number(s.getAttribute('data-seg')) === index);
  return { color: seg ? Number(seg.getAttribute('data-color')) : null, colors: [...new Set(segs.map(s => s.getAttribute('data-color')))].length, hit: Number((rotor.querySelector('path.rr-hit') || {}).getAttribute?.('data-color')) };
});
async function choose(page, color) {
  await page.waitForFunction(() => {
    const lock = document.getElementById('lockBtn');
    return lock && !lock.hidden && document.querySelector('.rr-swatch:not(.rr-off)');
  }, null, { timeout: 15000 });
  await page.click(`.rr-swatch[data-color="${color}"]`);
  await page.click('#lockBtn');
}
const waitResult = (page, round) => page.waitForFunction(r => {
  const status = document.getElementById('status').textContent;
  return /gagnée|perdue|égale distance|Même couleur|marque/.test(status) && document.querySelectorAll('.rr-hist').length >= r;
}, round, { timeout: 15000 });
/* Le résultat attendu d'une manche, sur cet écran (le statut change entre deux manches). */
const waitStatus = (page, re) => page.waitForFunction(src => new RegExp(src).test(document.getElementById('status').textContent), re.source, { timeout: 15000 });

async function noOverflow(page) {
  return page.evaluate(() => {
    const root = document.documentElement;
    return { v: root.scrollHeight <= innerHeight + 1, h: root.scrollWidth <= innerWidth + 1, sh: root.scrollHeight, ih: innerHeight, sw: root.scrollWidth, iw: innerWidth };
  });
}

/* ══ 1. Un match complet, deux joueurs et un spectateur ══ */
async function fullMatch(browser) {
  console.log('Roulette Royale : un match complet, deux joueurs et un spectateur');
  const errors = [];
  const p1 = await newPage(browser, 'Alice', errors);
  const p2 = await newPage(browser, 'Bob', errors);
  const viewer = await newPage(browser, 'Carla', errors);
  await Promise.all([p1.goto(playerUrl(GAME.match, 1)), p2.goto(playerUrl(GAME.match, 2))]);
  await p1.waitForFunction(() => !document.getElementById('lockBtn').hidden, null, { timeout: 15000 });
  await viewer.goto(`${GAME_URL}/roulette?spectate=1&gameId=${GAME.match}`);
  await viewer.evaluate(({ gameId, token }) => window.postMessage({ type: 'spectator:init', gameId, token, player1Name: 'Alice', player2Name: 'Bob' }, '*'), { gameId: GAME.match, token: tokenFor(VIEWER) });
  const viewerReady = await waitFor(async () => (await text(viewer, '#seal .rr-hash')) || null, 10000);
  check('le spectateur rejoint le direct et voit le sceau', !!viewerReady);

  const seals = await Promise.all([p1, p2, viewer].map(p => p.evaluate(() => {
    const seal = document.getElementById('seal');
    return seal && !seal.hidden ? seal.getAttribute('data-state') + ':' + seal.querySelector('.rr-hash').textContent : null;
  })));
  check('les trois écrans affichent le même sceau avant les choix', seals[0] && seals[0].startsWith('sealed:') && seals.every(s => s === seals[0]), seals);

  /* Alice choisit : ni Bob ni Carla n'apprennent sa couleur. */
  await choose(p1, 0);
  const locked = await waitFor(async () => {
    const [mine, theirs, watch] = await Promise.all([chips(p1), chips(p2), chips(viewer)]);
    return theirs.op.locked && watch.me.locked ? { mine, theirs, watch } : null;
  }, 6000);
  check('Alice voit sa propre couleur verrouillée', locked && locked.mine.me.color === '0', locked);
  check('Bob voit « a choisi », sans la couleur', locked && locked.theirs.op.locked && locked.theirs.op.color === null, locked);
  check('le spectateur voit « a choisi », sans la couleur', locked && locked.watch.me.locked && locked.watch.me.color === null, locked);
  check('le bouton d’Alice dit « Couleur verrouillée »', (await text(p1, '#lockBtn')) === 'Couleur verrouillée');
  check('le bouton de Bob lui dit que c’est à lui', /à vous/.test(await text(p2, '#lockBtn')), await text(p2, '#lockBtn'));

  /* Bob choisit : la roue tourne, le point attend l'arrêt. */
  await choose(p2, 4);
  const spinning = await waitFor(async () => /tourne/.test(await text(p1, '#status')) ? true : null, 4000, 40);
  check('la roue tourne chez Alice', spinning === true);
  check('pendant le tour de roue, le score reste 0-0', (await scores(p1)) === '0-0' && (await scores(p2)) === '0-0');
  const revealed = await chips(p2);
  check('au tour de roue, les deux couleurs sont montrées', revealed.me.color === '4' && revealed.op.color === '0', revealed);

  // Couleurs : 0 Rouge, 1 Orange, 2 Jaune, 3 Vert, 4 Bleu, 5 Violet. Alice à gauche chez elle, Bob chez lui.
  const plays = [
    { c: [0, 4], drawn: 0, a: /🎉 Manche gagnée · Rouge/, b: /💀 Manche perdue · Rouge/, v: /Alice marque · Rouge/, s: ['1-0', '0-1'],
      labels: { a: ['Pile !', '2 cases'], b: ['2 cases', 'Pile !'] }, title: 'Rouge tiré : pile sur Alice' },
    { c: [2, 1], drawn: 0, a: /💀 Manche perdue · Rouge/, b: /🎉 Manche gagnée · Rouge/, v: /Bob marque · Rouge/, s: ['1-1', '1-1'],
      labels: { a: ['2 cases', '1 case'], b: ['1 case', '2 cases'] }, title: 'Rouge tiré : l’Orange de Bob, plus proche, marque' },
    { c: [0, 2], drawn: 1, a: /À égale distance · Orange/, b: /À égale distance · Orange/, v: /À égale distance · Orange/, s: ['1-1', '1-1'],
      labels: { a: ['1 case', '1 case'] }, title: 'Orange tiré : Rouge et Jaune à égale distance, manche nulle' },
    { c: [3, 3], drawn: null, a: /Même couleur/, b: /Même couleur/, v: /Même couleur/, s: ['1-1', '1-1'], title: 'même couleur : on rechoisit' },
    { c: [4, 5], drawn: 3, a: /🎉 Manche gagnée · Vert/, b: /💀 Manche perdue · Vert/, v: /Alice marque · Vert/, s: ['2-1', '1-2'],
      label: 'Manche 4 / 5', title: 'Vert tiré : le Bleu d’Alice (1 case) bat le Violet (2 cases)' },
    { c: [1, 0], drawn: 5, a: /💀 Manche perdue · Violet/, b: /🎉 Manche gagnée · Violet/, v: /Bob marque · Violet/, s: ['2-2', '2-2'],
      title: 'Violet tiré : le Rouge de Bob (1 case) bat l’Orange (2 cases)' },
    { c: [5, 2], drawn: 2, a: /💀 Manche perdue · Jaune/, b: /🎉 Manche gagnée · Jaune/, v: /Bob marque · Jaune/, s: ['2-3', '3-2'],
      decisive: true, title: 'décisive 1/2 : Bob gagne la première' },
    { c: [0, 3], drawn: 0, a: /🎉 Manche gagnée · Rouge/, b: /💀 Manche perdue · Rouge/, v: /Alice marque · Rouge/, s: ['3-3', '3-3'],
      decisive: true, answer: true, title: 'décisive 2/2 : Alice répond et égalise, 1-1' },
    { c: [1, 4], drawn: 4, a: /💀 Manche perdue · Bleu/, b: /🎉 Manche gagnée · Bleu/, v: /Bob marque · Bleu/, s: ['3-4', '4-3'],
      decisive: true, title: 'nouvelle paire, décisive 1/2 : Bob' },
    { c: [2, 5], drawn: 5, a: /💀 Manche perdue · Violet/, b: /🎉 Manche gagnée · Violet/, v: /Bob marque · Violet/, s: ['3-5', '5-3'],
      decisive: true, answer: true, title: 'décisive 2/2 : Bob gagne aussi, 2-0, match joué' }
  ];
  for (let i = 0; i < plays.length; i++) {
    const play = plays[i];
    if (play.answer) {
      /* Bob a gagné la première de la paire : le match continue, Alice répond. */
      await Promise.all([p1, p2, viewer].map(p => p.waitForFunction(() => /répond/.test(document.getElementById('status').textContent), null, { timeout: 15000 })));
      const [ta, tb, tv, label] = await Promise.all([text(p1, '#status'), text(p2, '#status'), text(viewer, '#status'), text(p1, '#roundLabel')]);
      check(`manche ${i + 1} : chacun joue sa manche décisive — « ${ta} » / « ${tb} » / « ${tv} »`,
        /À vous de répondre/.test(ta) && /Vous menez/.test(tb) && /Bob mène · Alice répond/.test(tv), [ta, tb, tv]);
      check(`manche ${i + 1} : « Décisive 2/2 » en haut`, label === 'Décisive 2/2', label);
      check(`manche ${i + 1} : la fiche de fin n’est pas ouverte (personne n’a encore gagné)`,
        !(await p1.evaluate(() => document.getElementById('gameOverModal').classList.contains('show'))));
    }
    if (i > 0) { await choose(p1, play.c[0]); await choose(p2, play.c[1]); }
    await Promise.all([waitStatus(p1, play.a), waitStatus(p2, play.b), waitStatus(viewer, play.v)]);
    const [ta, tb, tv] = await Promise.all([text(p1, '#status'), text(p2, '#status'), text(viewer, '#status')]);
    check(`manche ${i + 1} (${play.title}) : chaque écran dit le bon résultat`, play.a.test(ta) && play.b.test(tb) && play.v.test(tv), [ta, tb, tv]);
    if (play.drawn !== null) {
      const where = await Promise.all([p1, p2, viewer].map(underPointer));
      check(`manche ${i + 1} : la roue s'arrête sur la couleur tirée, sur les trois écrans`, where.every(w => w.color === play.drawn && w.hit === play.drawn), where);
      if (play.decisive) check(`manche ${i + 1} : décisive, la roue ne garde que les deux couleurs choisies`, where[0].colors === 2, where[0]);
    }
    if (play.labels) {
      const [ca, cb] = await Promise.all([chips(p1), chips(p2)]);
      check(`manche ${i + 1} : chaque puce dit sa distance à la couleur tirée (${play.labels.a.join(' / ')})`,
        ca.me.label === play.labels.a[0] && ca.op.label === play.labels.a[1] && (!play.labels.b || (cb.me.label === play.labels.b[0] && cb.op.label === play.labels.b[1])),
        { alice: [ca.me.label, ca.op.label], bob: [cb.me.label, cb.op.label] });
      if (play.a.source.includes('gagnée')) check(`manche ${i + 1} : la puce gagnante s’éclaire`, ca.me.winner && !ca.op.winner, ca);
    }
    if (play.label) check(`manche ${i + 1} : le rechoix ne compte pas (« ${play.label} »)`, (await text(p1, '#roundLabel')) === play.label, await text(p1, '#roundLabel'));
    const [sa, sb] = await Promise.all([scores(p1), scores(p2)]);
    check(`manche ${i + 1} : le score après l'arrêt (${play.s.join(' / ')})`, sa === play.s[0] && sb === play.s[1], [sa, sb]);
    if (play.drawn !== null || i === 3) {
      const verified = await waitFor(async () => (await Promise.all([p1, p2, viewer].map(p => p.getAttribute('#seal', 'data-state')))).every(s => s === 'verified'), 4000);
      check(`manche ${i + 1} : « Tirage vérifié » sur les trois écrans`, verified === true);
    }
  }

  const decisiveRow = await p1.evaluate(() => {
    const row = document.querySelector('.rounds-decisive');
    return row && !row.hidden ? row.querySelectorAll('.ms-dec-dot').length : 0;
  });
  check('les manches décisives ont leur rangée : quatre repères (le rechoix n’y compte pas)', decisiveRow === 4, decisiveRow);
  const regularRow = await p1.evaluate(() => [...document.querySelectorAll('#roundsProgress .round-dot')].map(d => d.className.replace('round-dot', '').trim()));
  check('les cinq manches comptées ont chacune leur repère (le rechoix non)', regularRow.length === 5 && regularRow.every(c => /played/.test(c)), regularRow);

  const ends = await waitFor(async () => {
    const shown = await Promise.all([p1, p2, viewer].map(p => p.evaluate(() => document.getElementById('gameOverModal').classList.contains('show'))));
    return shown.every(Boolean) ? true : null;
  }, 10000);
  check('la fiche de fin s’ouvre chez les deux joueurs et le spectateur', ends === true);
  check('Alice : défaite 3 - 5', (await text(p1, '#modalTitle')).includes('DÉFAITE') && (await text(p1, '#finalScore')) === '3 - 5', await text(p1, '#finalScore'));
  check('Bob : victoire 5 - 3, gain net affiché', (await text(p2, '#modalTitle')).includes('VICTOIRE') && (await text(p2, '#finalScore')) === '5 - 3' && /\+1800 HTG/.test(await text(p2, '#prizeLine')), [await text(p2, '#modalTitle'), await text(p2, '#prizeLine')]);
  check('le spectateur : Bob remporte la Roulette Royale', /Bob remporte la Roulette Royale/.test(await text(viewer, '#finalMessage')));
  const rows = await p2.evaluate(() => document.querySelectorAll('#modalHistoryList .modal-history-item').length);
  check('l’historique de fin compte les 10 manches ouvertes (le rechoix compris)', rows === 10, rows);
  const labels = await p2.evaluate(() => [...document.querySelectorAll('#modalHistoryList .modal-history-item > span:first-child')].map(el => el.textContent).reverse());
  check('l’historique numérote les manches comptées (le rechoix reprend le numéro)', JSON.stringify(labels.slice(0, 6)) === JSON.stringify(['Manche 1', 'Manche 2', 'Manche 3', 'Manche 4', 'Manche 4', 'Manche 5']), labels);
  const proof = await p2.evaluate(() => {
    const card = document.querySelector('#gameOverModal .modal').getBoundingClientRect();
    const close = getComputedStyle(document.getElementById('closeBtn')).display;
    const wheel = document.getElementById('wheel').getBoundingClientRect();
    return { top: Math.round(card.top), close, cardBottom: Math.round(card.bottom), wheelBottom: Math.round(wheel.bottom) };
  });
  check('la fiche de fin se pose en haut, sans « Fermer », la roue reste visible dessous', proof.top < 40 && proof.close === 'none' && proof.wheelBottom > proof.cardBottom, proof);

  check('aucune erreur JavaScript ni ressource manquante', errors.length === 0, errors);
  await Promise.all([p1, p2, viewer].map(p => p.context().close()));
}

/* ══ 2. Le temps de grâce : le bandeau, puis la couleur touchée part seule ══ */
async function graceAutoLock(browser) {
  console.log('Roulette Royale : temps de grâce et verrouillage automatique');
  const errors = [];
  const p1 = await newPage(browser, 'Alice', errors);
  const p2 = await newPage(browser, 'Bob', errors);
  await Promise.all([p1.goto(playerUrl(GAME.grace, 1)), p2.goto(playerUrl(GAME.grace, 2))]);
  await choose(p2, 4);
  await p1.waitForFunction(() => document.querySelector('.rr-swatch:not(.rr-off)'), null, { timeout: 15000 });
  await p1.click('.rr-swatch[data-color="3"]');
  const ringMoves = await waitFor(async () => {
    const a = await p1.evaluate(() => parseFloat(document.getElementById('timer-arc-human').style.strokeDashoffset) || 0);
    await sleep(400);
    const b = await p1.evaluate(() => parseFloat(document.getElementById('timer-arc-human').style.strokeDashoffset) || 0);
    return b > a ? true : null;
  }, 3000);
  check('l’anneau du chronomètre d’Alice avance', ringMoves === true);
  const bars = await waitFor(async () => {
    const [a, b] = await Promise.all([p1, p2].map(p => p.evaluate(() => {
      const bar = document.getElementById('forfeit-bar');
      return bar.classList.contains('show') ? { text: bar.textContent, tone: bar.dataset.tone } : null;
    })));
    return a && b ? { a, b } : null;
  }, 8000);
  check('grâce : « Jouez maintenant · défaite dans … » chez Alice, en rouge', bars && /Jouez maintenant · défaite dans \d+ s/.test(bars.a.text) && bars.a.tone === 'urgent', bars);
  check('grâce : « L’adversaire doit jouer · … » chez Bob', bars && /L’adversaire doit jouer · \d+ s/.test(bars.b.text) && bars.b.tone === 'wait', bars);
  await waitResult(p1, 1);
  const afterwards = await chips(p1);
  check('la couleur touchée est partie d’elle-même : pas de défaite au temps', afterwards.me.color === '3' && !(await p1.evaluate(() => document.getElementById('gameOverModal').classList.contains('show'))), afterwards);
  check('Bob marque (Bleu tiré)', /Manche perdue · Bleu/.test(await text(p1, '#status')), await text(p1, '#status'));
  check('aucune erreur JavaScript', errors.length === 0, errors);
  await Promise.all([p1, p2].map(p => p.context().close()));
}

/* ══ 3. Une page rechargée retrouve sa couleur, jamais celle de l'autre ══ */
async function reloadKeepsChoice(browser) {
  console.log('Roulette Royale : rechargement pendant la manche');
  const errors = [];
  const p1 = await newPage(browser, 'Alice', errors);
  const p2 = await newPage(browser, 'Bob', errors);
  await Promise.all([p1.goto(playerUrl(GAME.reload, 1)), p2.goto(playerUrl(GAME.reload, 2))]);
  await choose(p2, 5);
  await choose(p1, 2);
  await waitResult(p1, 1);
  await choose(p1, 2);
  await sleep(300);
  await p1.reload();
  const restored = await waitFor(async () => {
    const c = await chips(p1);
    return c.me.color === '2' && c.op.color === null ? c : null;
  }, 10000);
  check('rechargée, la page d’Alice retrouve son Jaune verrouillé', !!restored, await chips(p1));
  check('… et le bouton dit « Couleur verrouillée »', (await text(p1, '#lockBtn')) === 'Couleur verrouillée');
  check('… sans connaître la couleur de Bob', restored && restored.op.color === null);
  await choose(p2, 0);
  await waitResult(p1, 2);
  check('la manche se joue après le rechargement (Jaune tiré : Alice marque)', /Manche gagnée · Jaune/.test(await text(p1, '#status')) && (await scores(p1)) === '2-0', [await text(p1, '#status'), await scores(p1)]);

  /* Les tailles d'écran, sur cette partie en cours. */
  await waitFor(async () => !(await p1.evaluate(() => document.getElementById('lockBtn').hidden)), 8000);
  for (const [w, h] of [[320, 568], [375, 667], [390, 844], [844, 390], [740, 360], [1280, 800]]) {
    await p1.setViewportSize({ width: w, height: h });
    await sleep(350);
    const fit = await noOverflow(p1);
    if (!fit.h && process.env.RR_DEBUG) console.log(await p1.evaluate(() => [...document.querySelectorAll('body *')].filter(el => el.getBoundingClientRect().right > innerWidth + 1).slice(0, 8).map(el => el.tagName + '#' + el.id + '.' + String(el.className && el.className.baseVal !== undefined ? el.className.baseVal : el.className).slice(0, 40) + ' r=' + Math.round(el.getBoundingClientRect().right) + ' pos=' + getComputedStyle(el).position)));
    check(`${w}×${h} : tout tient sans défiler`, fit.v && fit.h, fit);
  }
  await p1.setViewportSize({ width: 844, height: 390 });
  await sleep(300);
  const columns = await p1.evaluate(() => {
    const wheel = document.getElementById('wheel').getBoundingClientRect();
    const palette = document.getElementById('palette').getBoundingClientRect();
    return { wheelRight: Math.round(wheel.right), paletteLeft: Math.round(palette.left), wheel: Math.round(wheel.width) };
  });
  check('paysage : la roue à gauche, les couleurs à droite', columns.wheelRight <= columns.paletteLeft && columns.wheel >= 180, columns);
  /* L'écran partagé de l'application : l'en-tête part, le plateau garde tout. */
  await p1.addStyleTag({ content: 'html.ms-split #top{display:none!important}' });
  await p1.evaluate(() => document.documentElement.classList.add('ms-split'));
  for (const [w, h] of [[440, 344], [900, 760]]) {
    await p1.setViewportSize({ width: w, height: h });
    await sleep(350);
    const fit = await noOverflow(p1);
    check(`écran partagé ${w}×${h} : tout tient`, fit.v && fit.h, fit);
  }
  check('aucune erreur JavaScript', errors.length === 0, errors);
  await Promise.all([p1, p2].map(p => p.context().close()));
}

/* ══ 4. Contre l'IA, et entre amis ══ */
async function offline(browser, mode) {
  console.log(`Roulette Royale : ${mode === 'ai' ? 'contre l’IA' : 'entre amis'}`);
  const errors = [];
  const page = await newPage(browser, mode, errors);
  await page.addInitScript(() => { window.__msgs = []; window.addEventListener('message', e => window.__msgs.push(e.data)); });
  await page.goto(GAME_URL + (mode === 'ai' ? '/roulette-ai?fast=1&name=Ritchy&difficulty=hard' : '/roulette-local?fast=1&name=Ana&p2Name=Bea'));
  let secretKept = true, curtains = 0;
  for (let guard = 0; guard < 400; guard++) {
    if (await page.evaluate(() => document.getElementById('gameOverModal').classList.contains('show'))) break;
    const st = await page.evaluate(() => window.RouletteOffline.state());
    if (st.phase !== 'choosing') { await sleep(60); continue; }
    if (st.curtain) {
      curtains++;
      await page.click('#curtain-btn');
      /* Le second à choisir ne voit pas la couleur du premier. */
      const now = await page.evaluate(() => window.RouletteOffline.state());
      if (now.picked[1] || now.picked[2]) {
        const c = await chips(page);
        const first = now.picked[1] ? c.me : c.op;
        if (first.color !== null || !first.locked) secretKept = false;
      }
      continue;
    }
    const ready = await page.evaluate(() => !!document.querySelector('.rr-swatch:not(.rr-off)'));
    if (!ready) { await sleep(60); continue; }
    await page.click(`.rr-swatch[data-color="${(st.round * 2 + st.chooser) % 6}"]`);
    await page.click('#lockBtn');
    await sleep(40);
  }
  const over = await page.evaluate(() => document.getElementById('gameOverModal').classList.contains('show'));
  check('le match va jusqu’à la fiche de fin', over);
  const st = await page.evaluate(() => window.RouletteOffline.state());
  const total = st.scores[0] + st.scores[1];
  check('le score final désigne un vainqueur', st.scores[0] !== st.scores[1] && total >= 1, st.scores);
  check('la fiche liste chaque manche', (await page.evaluate(() => document.querySelectorAll('#modalHistoryList .modal-history-item').length)) === st.history.length);
  if (mode === 'ai') {
    const msgs = await page.evaluate(() => window.__msgs.filter(m => m && m.event === 'practice_over'));
    check('practice_over part vers l’application, avec le score', msgs.length === 1 && msgs[0].game === 'roulette' && msgs[0].scores.me === st.scores[0], msgs);
    check('le titre suit le score', (await text(page, '#modalTitle')).includes(st.scores[0] > st.scores[1] ? 'VICTOIRE' : 'DÉFAITE'));
  } else {
    check('un rideau avant chaque choix', curtains >= st.history.length * 2 - 2, { curtains, rounds: st.history.length });
    check('la couleur du premier n’est jamais montrée au second', secretKept);
    check('le titre nomme le gagnant', (await text(page, '#modalTitle')).includes(st.scores[0] > st.scores[1] ? 'Ana' : 'Bea'));
  }
  await page.click('#replayBtn');
  const again = await waitFor(async () => {
    const s = await page.evaluate(() => window.RouletteOffline.state());
    return s.round === 1 && s.scores[0] === 0 && s.scores[1] === 0 && (s.phase === 'choosing' || s.phase === 'sealing') ? s : null;
  }, 5000);
  check('« Rejouer » repart d’un match neuf', !!again);
  check('aucune erreur JavaScript', errors.length === 0, errors);
  await page.context().close();
}

/*
 * Le tour de roue de casino (owner, 2026-11-05 : « ralentie au début… prend de
 * la vitesse… s'arrêter comme dans les grands jeux de roulette »), à la vitesse
 * réelle de la page contre l'IA (sans ?fast=1). Le moteur écrit l'angle absolu
 * dans le style du rotor à chaque image : on le relève image par image.
 */
async function casinoSpin(browser) {
  console.log('Roulette Royale : le tour de roue de casino (vitesse réelle)');
  const errors = [];
  const page = await newPage(browser, 'casino', errors);
  await page.goto(GAME_URL + '/roulette-ai?name=Ritchy&difficulty=hard');
  const ready = await waitFor(() => page.evaluate(() => !!window.RouletteOffline
    && window.RouletteOffline.state().phase === 'choosing' && !!document.querySelector('.rr-swatch:not(.rr-off)')), 15000);
  check('la page contre l’IA est prête', !!ready);
  const samplesP = page.evaluate(() => new Promise(resolve => {
    const rotor = document.querySelector('.rr-rotor'), pointer = document.querySelector('.rr-pointer');
    const rot = el => { const m = /rotate\((-?[\d.]+)deg\)/.exec(el.style.transform || ''); return m ? Number(m[1]) : 0; };
    const out = [];
    let t0 = null;
    const tick = now => {
      const phase = window.RouletteOffline.state().phase;
      if (t0 === null) {
        if (phase !== 'spinning') { requestAnimationFrame(tick); return; }
        t0 = now;
      }
      out.push({ t: now - t0, angle: rot(rotor), pointer: rot(pointer) });
      if (phase !== 'spinning' || now - t0 > 12000) { resolve(out); return; }
      requestAnimationFrame(tick);
    };
    requestAnimationFrame(tick);
  }));
  await page.click('.rr-swatch[data-color="2"]');
  await page.click('#lockBtn');
  const samples = await samplesP;
  const at = t => { let best = samples[0]; for (const x of samples) if (x.t <= t) best = x; return best.angle; };
  const end = samples[samples.length - 1].t;
  const start = samples[0].angle;
  const speeds = [];
  for (let t = 0; t + 250 <= end; t += 50) speeds.push({ t, v: (at(t + 250) - at(t)) / 0.25 });
  const peak = speeds.reduce((a, b) => (b.v > a.v ? b : a), { t: 0, v: 0 });
  const early = (at(1000) - at(0)) / 1;
  const late = (at(end) - at(end - 1500)) / 1.5;
  const dip = start - Math.min(...samples.filter(x => x.t < 700).map(x => x.angle));
  const kicks = samples.filter(x => Math.abs(x.pointer) > 0.5);
  const lastKick = kicks.length ? kicks[kicks.length - 1].t : 0;
  const detail = { end: Math.round(end), peak: Math.round(peak.v), peakAt: Math.round(peak.t), early: Math.round(early), late: Math.round(late), dip: Math.round(dip * 10) / 10, turns: Math.round((at(end) - start) / 36) / 10, kicks: kicks.length, lastKick: Math.round(lastKick), frames: samples.length };
  check(`un tour de 7 s environ (${detail.end} ms, ${detail.frames} images)`, end > 6400 && end < 9500, detail);
  check(`un léger élan en arrière d’abord (${detail.dip}°)`, dip >= 3 && dip <= 12, detail);
  check(`un départ lent : la première seconde à moins d’un quart de la pleine vitesse (${detail.early} contre ${detail.peak} °/s)`, early < peak.v * 0.25, detail);
  check(`la pleine vitesse au milieu du tour (${detail.peakAt} ms)`, peak.t > 1000 && peak.t < 4200 && peak.v > 400, detail);
  check(`une longue fin au ralenti : la dernière seconde et demie à moins de 12 % (${detail.late} °/s)`, late < peak.v * 0.12, detail);
  check(`au moins cinq tours (${detail.turns})`, (at(end) - start) >= 1800, detail);
  check(`le pointeur claque sur les taquets, jusque dans le freinage (dernier à ${detail.lastKick} ms)`, kicks.length >= 10 && lastKick > 4000, detail);
  check('le pointeur revient droit à l’arrêt', Math.abs(samples[samples.length - 1].pointer) < 0.5 || (await page.evaluate(() => !document.querySelector('.rr-pointer').style.transform)), detail);
  const final = await page.evaluate(() => {
    const st = window.RouletteOffline.state();
    const last = st.history[st.history.length - 1];
    const m = /rotate\((-?[\d.]+)deg\)/.exec(document.querySelector('.rr-rotor').style.transform || '');
    return { drawn: last ? last.drawn : null, repick: !!(last && last.repick), angle: m ? Number(m[1]) : null };
  });
  const under = final.angle === null ? null : Math.floor((((360 - (final.angle % 360)) % 360) + 360) % 360 / 60);
  check('la roue s’arrête sur la couleur tirée', final.repick || under === final.drawn, final);
  check('aucune erreur JavaScript', errors.length === 0, errors);
  await page.context().close();
}

async function main() {
  const db = mockDatabase();
  await new Promise(resolve => db.listen(DB_PORT, '127.0.0.1', resolve));
  const server = spawn(process.execPath, ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT), NODE_ENV: 'test', JWT_SECRET,
      SUPABASE_URL: DB_URL, SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: GAME_URL,
      ROULETTE_TEST_DRAWS: JSON.stringify(DRAWS),
      ROULETTE_SPIN_MS: '1400', ROUND_PROOF_MS: '700', ROULETTE_REPICK_MS: '500', ROULETTE_FINAL_HOLD_MS: '400',
      TURN_DURATION_MS: '4000', GRACE_DURATION_MS: '4500', RECONNECT_DURATION_MS: '15000'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => {
    const line = String(d);
    if (!/JWT_SECRET|persistence|summary|Missing games\.id/.test(line)) process.stderr.write(line);
  });
  let browser;
  try {
    await waitForHealth();
    const executablePath = chromiumBinary();
    if (!executablePath) { console.log('Chromium introuvable : parcours ignoré'); return; }
    browser = await chromium.launch({ executablePath, args: ['--no-sandbox'] });
    await fullMatch(browser);
    await graceAutoLock(browser);
    await reloadKeepsChoice(browser);
    await offline(browser, 'ai');
    await offline(browser, 'local');
    await casinoSpin(browser);
  } catch (error) {
    failures++;
    console.error('  FAIL exception', error && error.stack ? error.stack : error);
  } finally {
    if (browser) await browser.close();
    server.kill();
    db.close();
  }
  if (failures) { console.error(`\n${failures} échec(s)`); process.exit(1); }
  console.log('\nOK Roulette Royale dans le navigateur : en ligne, spectateur, IA, entre amis');
}

main();
