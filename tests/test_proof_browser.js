/**
 * La preuve du résultat reste visible, dans un vrai navigateur (owner,
 * 2026-10-26 : « une fois que les cinq pions sont bien alignés, ça doit rester
 * visible pendant quelques secondes »).
 *
 * Sur les sept plateaux en ligne, à 390×844 (téléphone) et 740×360 (téléphone
 * tourné), le message de manche (#toast) et la fiche de fin (#gameOverModal) :
 *
 * - se posent EN HAUT de l'écran, centrés, dans l'écran ;
 * - laissent le milieu de l'écran — le plateau — à découvert ;
 * - n'ont ni voile ni flou sur le plateau, ni bouton « Fermer » ;
 *
 * et le serveur garde le plateau final d'une manche 4 secondes avant la
 * suivante (Tic-Tac-Toe, Morpion à 5, Quoridor).
 */
const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const PUBLIC = path.join(REPO_ROOT, 'public');
const GAME_PORT = 3214;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const PAGES = ['dames_multi.html', 'echecs_multi.html', 'ttt_game.html', 'gomoku-online.html', 'quoridor-online.html', 'penalty-online.html', 'chifoumi-online.html'];

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : JSON.stringify(detail)); }
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

/* Ouvre le message de manche et la fiche de fin comme la page le fait, puis les mesure. */
function measure() {
  return (async () => {
    const out = { loaded: !!document.getElementById('mindspille-proof'), width: innerWidth, height: innerHeight };
    for (const id of ['loading', 'waiting-overlay']) { const el = document.getElementById(id); if (el) el.style.display = 'none'; }
    const toast = document.getElementById('toast');
    if (toast) {
      // Exactement ce que fait le showToast de chaque page (sa portée est privée).
      document.getElementById('toast-emoji').textContent = '🏆';
      document.getElementById('toast-title').textContent = 'Manche gagnée';
      document.getElementById('toast-sub').textContent = 'Score : 1 — 0';
      toast.style.cssText = 'display:block;opacity:1;transform:translate(-50%,-50%) scale(1);transition:none;';
      await new Promise(r => setTimeout(r, 100));
      const t = toast.getBoundingClientRect();
      out.toast = { top: t.top, bottom: t.bottom, left: t.left, right: t.right, center: t.left + t.width / 2, visible: getComputedStyle(toast).display !== 'none' };
      toast.style.display = 'none';
    }
    const modal = document.getElementById('gameOverModal');
    if (modal) {
      const title = document.getElementById('modalTitle'); if (title) title.textContent = 'Victoire !';
      const msg = document.getElementById('finalMessage'); if (msg) msg.textContent = 'Cinq pions alignés. Bien joué !';
      const prize = document.getElementById('prizeLine'); if (prize) { prize.style.display = 'block'; prize.textContent = '🤑 +180 HTG (net)'; }
      modal.classList.add('show');
      await new Promise(r => setTimeout(r, 450));
      const list = document.getElementById('modalHistoryList');
      if (list) list.innerHTML = Array.from({ length: 5 }, (_, i) => `<div class="modal-history-item ${i % 2 ? 'lose' : 'win'}">Manche ${i + 1}</div>`).join('');
      const card = modal.querySelector('.modal').getBoundingClientRect();
      out.history = !!list;
      const cs = getComputedStyle(modal);
      const close = document.getElementById('closeBtn');
      out.modal = {
        top: card.top, bottom: card.bottom, left: card.left, right: card.right, center: card.left + card.width / 2,
        background: cs.backgroundColor, blur: cs.backdropFilter || cs.webkitBackdropFilter || 'none', pointer: cs.pointerEvents,
        closeShown: !!close && getComputedStyle(close).display !== 'none'
      };
    }
    return out;
  })();
}

async function main() {
  // Le serveur : la preuve d'une manche dure 4 secondes, pour les trois jeux à manches.
  const server = fs.readFileSync(path.join(REPO_ROOT, 'server.js'), 'utf8');
  check('la preuve d\'une manche : 4 s par défaut', /const ROUND_PROOF_MS = testDurationMs\('ROUND_PROOF_MS', 4000\);/.test(server));
  check('Tic-Tac-Toe, Morpion à 5 et Quoridor l\'attendent', (server.match(/\}, ?ROUND_PROOF_MS\);/g) || []).length === 3);
  for (const name of PAGES) {
    const source = fs.readFileSync(path.join(PUBLIC, name), 'utf8');
    check(`${name} : inclut le module de la preuve`, source.includes('<script src="/mindspille-proof.js"></script>'));
  }

  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    if (failures) process.exit(1);
    return;
  }

  const child = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT), NODE_ENV: 'test', JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      SUPABASE_URL: 'http://127.0.0.1:9', SUPABASE_SERVICE_ROLE_KEY: 'test-service-role', ALLOWED_ORIGIN: GAME_URL
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  child.stderr.on('data', d => process.stderr.write(String(d)));

  let browser;
  try {
    await waitForHealth();
    browser = await chromium.launch({ executablePath });
    const errors = [];
    for (const viewport of [{ width: 390, height: 844 }, { width: 740, height: 360 }]) {
      const context = await browser.newContext({ viewport, isMobile: true, hasTouch: true });
      if (process.env.THREE_RUNTIME_FILE) {
        await context.route('**/vendor/three-r128.min.js', route =>
          route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
      }
      for (const name of PAGES) {
        const page = await context.newPage();
        page.on('pageerror', e => errors.push(`${name}: ${e.message}`));
        await page.goto(`${GAME_URL}/${name}`, { waitUntil: 'load' });
        await sleep(500);
        const m = await page.evaluate(measure);
        const at = `${name} ${viewport.width}×${viewport.height}`;
        check(`${at} : module chargé`, m.loaded);
        // Le milieu de l'écran (le plateau) reste à découvert : rien ne descend sous 40 % de la hauteur.
        const freeLine = m.height * 0.4;
        if (m.toast) {
          check(`${at} : le message de manche en haut`, m.toast.visible && m.toast.top >= 0 && m.toast.top <= 24, m.toast);
          check(`${at} : le message ne couvre pas le plateau`, m.toast.bottom <= freeLine, { bottom: m.toast.bottom, free: freeLine });
          check(`${at} : le message centré, dans l'écran`, m.toast.left >= 0 && m.toast.right <= m.width && Math.abs(m.toast.center - m.width / 2) <= 1.5, m.toast);
        } else {
          check(`${at} : la page a un message de manche`, false);
        }
        if (m.modal) {
          check(`${at} : la fiche de fin en haut`, m.modal.top >= 0 && m.modal.top <= 28, m.modal);
          // L'historique des tirs / manches (Penalty, Chifoumi) a droit à un peu plus sur un écran haut.
          const modalLine = m.history && m.height > 520 ? m.height * 0.45 : freeLine;
          check(`${at} : la fiche ne couvre pas le plateau`, m.modal.bottom <= modalLine, { bottom: m.modal.bottom, free: modalLine });
          check(`${at} : ni voile ni flou sur le plateau`, /rgba\(0, 0, 0, 0\)|transparent/.test(m.modal.background) && /none/.test(m.modal.blur), m.modal);
          check(`${at} : plus de bouton « Fermer »`, !m.modal.closeShown);
          check(`${at} : la fiche ne prend pas le doigt`, m.modal.pointer === 'none', m.modal.pointer);
        }
        await page.close();
      }
      await context.close();
    }
    check('aucune erreur JavaScript', errors.length === 0, errors);
  } finally {
    if (browser) await browser.close();
    child.kill('SIGTERM');
  }
  if (failures) { console.error(`\n${failures} échec(s)`); process.exit(1); }
  console.log('OK la preuve du résultat reste visible');
}

main().catch(error => { console.error(error); process.exit(1); });
