/**
 * Les bandeaux d'information des plateaux, dans un vrai navigateur.
 *
 * En haut, ce que la position impose (« Prise obligatoire », « Échec au roi ») ;
 * en bas, le temps (« Jouez maintenant · défaite dans 56 s », « L’adversaire
 * doit jouer · 56 s »). Pour chaque page qui en porte, sur un grand et un tout
 * petit téléphone, le texte le plus long doit :
 *
 * - tenir sur UNE ligne, sans être coupé, dans l'écran, centré — même avec la
 *   police de secours, plus large, tant que Inter n'est pas chargée (la CI n'a
 *   pas Inter : le texte se resserre, jamais sous 9 px) ;
 * - être écrit dans la police de l'application (Inter), jamais en Cinzel ;
 * - en haut : juste sous l'en-tête ;
 * - en bas : posé sur la barre du bas (au pixel près), ou, sans barre (Penalty,
 *   Chifoumi), au pied de l'écran et au-dessus du bouton de discussion qui y
 *   flotte ;
 * - et passer dans la langue du joueur.
 *
 * Plus aucune page n'écrit les anciens textes à émojis.
 */
const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const PUBLIC = path.join(REPO_ROOT, 'public');
const GAME_PORT = 3212;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;

/* Le texte le plus long que chaque bandeau peut porter. */
const LONGEST = {
  'forfeit-bar': 'Jouez maintenant · annulation dans 56 s',
  capture: 'L’adversaire doit prendre',
  check: 'Le roi adverse est en échec'
};
const OLD_TEXTS = ['⚠️ Jouez maintenant —', '⏳ Adversaire doit jouer —', '⏳ Adversaire absent —', 'forfait dans \' +',
  '⚡ Prise obligatoire !', 'doit prendre !', '⚔️'];

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

/* Les pages qui portent un bandeau. */
const PAGES = fs.readdirSync(PUBLIC)
  .filter(name => name.endsWith('.html'))
  .filter(name => /id="(forfeit-bar|force-jump-hint)"/.test(fs.readFileSync(path.join(PUBLIC, name), 'utf8')))
  .sort();

/* Les pages « ami » ne sont servies que par leur route (/ttt-local…). */
const routeOf = name => (name.endsWith('_local.html') ? '/' + name.replace(/_local\.html$/, '-local') : '/' + name);

/* Mesure, dans la page, chaque bandeau rendu visible avec son texte le plus long. */
function measure(longest) {
  return (async () => {
    const out = { banners: [], loaded: !!document.getElementById('mindspille-banners') };
    const loading = document.getElementById('loading');
    if (loading) loading.style.display = 'none';
    const waiting = document.getElementById('waiting-overlay');
    if (waiting) waiting.style.display = 'none';
    /* La page peut retirer un bandeau à tout instant (fin de tour) : on le garde affiché le temps de mesurer. */
    const keep = document.createElement('style');
    keep.textContent = '#force-jump-hint,#forfeit-bar{display:block!important}';
    document.head.appendChild(keep);
    const top = document.getElementById('top');
    const foot = document.getElementById('bot');
    out.topBottom = top ? top.getBoundingClientRect().bottom : null;
    out.footTop = foot && foot.getClientRects().length ? foot.getBoundingClientRect().top : null;
    out.width = window.innerWidth;
    out.height = window.innerHeight;
    for (const id of ['force-jump-hint', 'forfeit-bar']) {
      const el = document.getElementById(id);
      if (!el) continue;
      const kind = id === 'forfeit-bar' ? id : (el.dataset.kind === 'check' ? 'check' : 'capture');
      el.dataset.tone = 'urgent';
      el.textContent = longest[kind];
      el.classList.add('show');
      await Promise.resolve();
      /* La place finale, pas l'image d'entrée de l'animation. */
      el.getAnimations().forEach(animation => animation.finish());
      const r = el.getBoundingClientRect();
      const cs = getComputedStyle(el);
      out.banners.push({
        id, kind,
        top: r.top, bottom: r.bottom, left: r.left, right: r.right, height: r.height,
        center: r.left + r.width / 2,
        clipped: el.scrollWidth > el.clientWidth + 1,
        size: parseFloat(cs.fontSize),
        font: cs.fontFamily,
        transform: cs.transform,
        animation: cs.animationName,
        footShown: document.documentElement.classList.contains('ms-foot-shown')
      });
    }
    out.docked = document.documentElement.classList.contains('ms-foot-docked');
    out.float = document.documentElement.classList.contains('ms-foot-float');
    /* Penalty, Chifoumi : le bouton de discussion de l'application flotte en bas à gauche. */
    if (out.float) {
      document.documentElement.classList.add('ms-chat-on');
      const bar = document.getElementById('forfeit-bar');
      bar.getAnimations().forEach(animation => animation.finish());
      out.withChatBottom = bar.getBoundingClientRect().bottom;
      document.documentElement.classList.remove('ms-chat-on');
    }
    return out;
  })();
}

async function main() {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    console.log('OK bandeaux ignorés');
    return;
  }

  check('dix-neuf pages portent un bandeau', PAGES.length === 19, PAGES);
  for (const name of PAGES) {
    const source = fs.readFileSync(path.join(PUBLIC, name), 'utf8');
    const old = OLD_TEXTS.filter(text => source.includes(text));
    check(`${name} : plus aucun ancien texte à émojis`, old.length === 0, old);
    check(`${name} : inclut le module des bandeaux`, source.includes('<script src="/mindspille-banners.js"></script>'));
  }

  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT), NODE_ENV: 'test', JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      SUPABASE_URL: 'http://127.0.0.1:9', SUPABASE_SERVICE_ROLE_KEY: 'test-service-role', ALLOWED_ORIGIN: GAME_URL
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', d => process.stderr.write(String(d)));

  let browser;
  try {
    await waitForHealth();
    const script = await new Promise((resolve, reject) => {
      http.get(`${GAME_URL}/mindspille-banners.js`, res => {
        res.resume();
        resolve({ status: res.statusCode, type: res.headers['content-type'] });
      }).on('error', reject);
    });
    check('le module des bandeaux est servi', script.status === 200 && /javascript/.test(script.type || ''), script);

    browser = await chromium.launch({ executablePath });
    const errors = [];
    for (const viewport of [{ width: 390, height: 844 }, { width: 320, height: 568 }]) {
      const context = await browser.newContext({ viewport, isMobile: true, hasTouch: true });
      if (process.env.THREE_RUNTIME_FILE) {
        await context.route('**/vendor/three-r128.min.js', route =>
          route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
      }
      for (const name of PAGES) {
        const page = await context.newPage();
        page.on('pageerror', e => errors.push(`${name}: ${e.message}`));
        await page.goto(GAME_URL + routeOf(name), { waitUntil: 'load' });
        await sleep(600);
        const m = await page.evaluate(measure, LONGEST);
        const at = `${name} ${viewport.width}×${viewport.height}`;
        check(`${at} : module chargé`, m.loaded);
        for (const b of m.banners) {
          const what = `${at} ${b.id}`;
          check(`${what} : une seule ligne, rien de coupé`, b.height <= 36 && !b.clipped, b);
          /* Resserré s'il le faut (petit écran, police de secours avant Inter), jamais illisible. */
          check(`${what} : lisible (9 px au moins)`, b.size >= 9, b.size);
          check(`${what} : dans l'écran, centré`,
            b.left >= 0 && b.right <= m.width && Math.abs(b.center - m.width / 2) <= 1.5, b);
          check(`${what} : police de l'application`, /^["']?Inter/.test(b.font) && !/Cinzel/.test(b.font), b.font);
          if (b.id === 'force-jump-hint') {
            check(`${what} : juste sous l'en-tête`, m.topBottom !== null && b.top - m.topBottom >= 0 && b.top - m.topBottom <= 16,
              { top: b.top, header: m.topBottom });
            check(`${what} : plus de pulsation`, b.animation !== 'pulse-hint', b.animation);
          } else if (m.docked) {
            check(`${what} : posé sur la barre du bas`, m.footTop !== null && Math.abs(b.bottom - m.footTop) <= 1,
              { bottom: b.bottom, foot: m.footTop });
            check(`${what} : le mode d'emploi s'efface dessous`, b.footShown);
          } else {
            check(`${what} : au pied de l'écran`, m.float && b.bottom <= m.height - 14 && b.bottom >= m.height - 40,
              { bottom: b.bottom, height: m.height });
            check(`${what} : au-dessus du bouton de discussion flottant`, m.withChatBottom <= m.height - 14 - 44 - 4,
              { bottom: m.withChatBottom, height: m.height });
          }
        }
        await page.close();
      }
      await context.close();
    }

    /* La langue du joueur : le texte passe par le traducteur des plateaux. */
    const english = await browser.newContext({ viewport: { width: 390, height: 844 } });
    await english.addInitScript(() => { try { localStorage.setItem('mindspille_language', 'en'); } catch (_) {} });
    if (process.env.THREE_RUNTIME_FILE) {
      await english.route('**/vendor/three-r128.min.js', route =>
        route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
    }
    const page = await english.newPage();
    await page.goto(`${GAME_URL}/dames_ai.html`, { waitUntil: 'load' });
    await sleep(600);
    const translated = await page.evaluate(async () => {
      const out = {};
      const samples = {
        mine: 'Jouez maintenant · défaite dans 56 s',
        cancel: 'Jouez maintenant · annulation dans 9 s',
        theirs: 'L’adversaire doit jouer · 41 s',
        away: 'Adversaire absent · victoire dans 30 s'
      };
      const bar = document.getElementById('forfeit-bar');
      for (const [key, text] of Object.entries(samples)) {
        bar.textContent = text;
        await new Promise(r => setTimeout(r, 80));
        out[key] = bar.textContent;
      }
      const hint = document.getElementById('force-jump-hint');
      for (const [key, text] of Object.entries({ capture: 'Prise obligatoire', theirCapture: 'L’adversaire doit prendre' })) {
        hint.textContent = text;
        await new Promise(r => setTimeout(r, 80));
        out[key] = hint.textContent;
      }
      return out;
    });
    check('en anglais : « Play now · defeat in 56 s »', translated.mine === 'Play now · defeat in 56 s', translated);
    check('en anglais : l annulation', translated.cancel === 'Play now · cancelled in 9 s', translated);
    check('en anglais : le tour de l adversaire', translated.theirs === 'Your opponent must play · 41 s', translated);
    check('en anglais : l adversaire absent', translated.away === 'Opponent away · victory in 30 s', translated);
    check('en anglais : la prise obligatoire', translated.capture === 'Capture required', translated);
    check('en anglais : la prise de l adversaire', translated.theirCapture === 'Your opponent must capture', translated);
    await english.close();

    check('aucune exception JavaScript', errors.length === 0, errors);
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
  }
  if (failures) process.exitCode = 1;
  else console.log('OK bandeaux des plateaux');
}

main().catch(error => { console.error(error); process.exitCode = 1; });
