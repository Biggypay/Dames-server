/**
 * Les plateaux 3D sur la durée (public/mindspille-3d.js), dans un vrai navigateur.
 *
 * 1. Les neuf pages 3D chargent le module juste après Three.js, et le serveur
 *    le sert.
 * 2. Une vraie partie contre l'IA, coup après coup (clics projetés sur les
 *    cases) : la mémoire graphique ne grandit plus. Avant, chaque sélection,
 *    chaque surbrillance, chaque prise laissait ses formes derrière elle.
 * 3. Plateau immobile : les ombres ne sont plus recalculées à chaque image ;
 *    une pièce qui bouge les fait recalculer.
 * 4. L'image est la même : rien de ce qu'on voit ne dépend du module.
 */
const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const PORT = 3214;
const URL = `http://127.0.0.1:${PORT}`;
const PAGES_3D = ['dames_ai', 'dames_local', 'dames_multi', 'echecs_ai', 'echecs_local', 'echecs_multi', 'ttt_ai', 'ttt_game', 'ttt_local'];

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : JSON.stringify(detail)); }
}
const sleep = ms => new Promise(r => setTimeout(r, ms));

async function waitForHealth(retries = 50) {
  for (let i = 0; i < retries; i++) {
    const ok = await new Promise(resolve => {
      http.get(`${URL}/health`, res => { res.resume(); resolve(res.statusCode === 200); }).on('error', () => resolve(false));
    });
    if (ok) return;
    await sleep(200);
  }
  throw new Error('game server unavailable');
}

async function openPage(browser, route) {
  const page = await browser.newPage({ viewport: { width: 420, height: 760 }, deviceScaleFactor: 1 });
  const errors = [];
  page.on('pageerror', e => errors.push(String(e)));
  if (process.env.THREE_RUNTIME_FILE) {
    await page.route('**/vendor/three-r128.min.js', route =>
      route.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
  }
  await page.goto(URL + route, { waitUntil: 'load' });
  await page.waitForFunction(() => window.MS3D && window.MS3D.last && window.MS3D.stats.frames > 5, null, { timeout: 20000 });
  return { page, errors };
}

/* Un coup : une de mes pièces, puis une des cases proposées. */
async function playOneMove(page, seed) {
  return page.evaluate(async seed => {
    const { scene, camera, renderer } = window.MS3D.last;
    const rect = renderer.domElement.getBoundingClientRect();
    const toScreen = obj => {
      const v = new THREE.Vector3();
      obj.getWorldPosition(v);
      v.project(camera);
      return { x: rect.left + (v.x + 1) / 2 * rect.width, y: rect.top + (1 - v.y) / 2 * rect.height };
    };
    const click = async p => {
      for (const type of ['mousedown', 'mouseup', 'click']) {
        renderer.domElement.dispatchEvent(new MouseEvent(type, { bubbles: true, clientX: p.x, clientY: p.y }));
      }
      await new Promise(r => setTimeout(r, 120));
    };
    const mine = [];
    scene.traverse(o => { if (o.userData && o.userData.player === 0 && o.parent && o.parent.type === 'Group') mine.push(o); });
    for (let k = 0; k < mine.length; k++) {
      await click(toScreen(mine[(k + seed * 7) % mine.length]));
      const marks = [];
      scene.traverse(o => {
        if (!o.isMesh || !o.geometry || o.geometry.type !== 'CircleGeometry' || o.position.y <= 0.19) return;
        const hex = o.material.color && o.material.color.getHex();
        if (hex !== 0xfbbf24 && hex !== 0x88ccff) marks.push(o);
      });
      if (!marks.length) continue;
      await click(toScreen(marks[seed % marks.length]));
      return true;
    }
    return false;
  }, seed);
}

/* La part des pixels qui diffèrent nettement entre deux captures (décodées par le navigateur). */
async function pixelDiff(browser, a, b) {
  const page = await browser.newPage();
  const result = await page.evaluate(async ([a, b]) => {
    const load = async b64 => createImageBitmap(await (await fetch(`data:image/png;base64,${b64}`)).blob());
    const [x, y] = await Promise.all([load(a), load(b)]);
    if (x.width !== y.width || x.height !== y.height) return { sameSize: false, share: 1 };
    const pixels = img => {
      const c = new OffscreenCanvas(img.width, img.height);
      const ctx = c.getContext('2d');
      ctx.drawImage(img, 0, 0);
      return ctx.getImageData(0, 0, img.width, img.height).data;
    };
    const p = pixels(x), q = pixels(y);
    let off = 0;
    for (let i = 0; i < p.length; i += 4) {
      if (Math.abs(p[i] - q[i]) > 12 || Math.abs(p[i + 1] - q[i + 1]) > 12 || Math.abs(p[i + 2] - q[i + 2]) > 12) off++;
    }
    return { sameSize: true, share: off / (p.length / 4) };
  }, [a.toString('base64'), b.toString('base64')]);
  await page.close();
  return result;
}

const graphics = page => page.evaluate(() => {
  const r = window.MS3D.last.renderer;
  return { geometries: r.info.memory.geometries, textures: r.info.memory.textures };
});

(async () => {
  const executablePath = chromiumBinary();
  if (!executablePath) {
    console.log('  (ignoré) Chromium absent de cette machine — parcours navigateur non exécuté');
    return;
  }

  console.log('\n1. Les pages chargent le module, juste après Three.js');
  for (const name of PAGES_3D) {
    const html = fs.readFileSync(path.join(REPO_ROOT, 'public', `${name}.html`), 'utf8');
    check(`${name} : mindspille-3d.js suit three-r128`, /<script src="\/vendor\/three-r128\.min\.js"><\/script>\s*<script src="\/mindspille-3d\.js"><\/script>/.test(html));
  }

  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: { ...process.env, PORT: String(PORT), NODE_ENV: 'test', JWT_SECRET: 'test-only-secret-with-more-than-32-characters' },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  let browser;
  try {
    await waitForHealth();
    const served = await new Promise((resolve, reject) => {
      http.get(`${URL}/mindspille-3d.js`, res => { res.resume(); resolve({ status: res.statusCode, type: res.headers['content-type'] }); }).on('error', reject);
    });
    check('le serveur sert /mindspille-3d.js', served.status === 200 && /javascript/.test(served.type), served);

    browser = await chromium.launch({ executablePath });

    console.log('\n2. Une vraie partie contre l\'IA : la mémoire graphique ne grandit plus');
    {
      const { page, errors } = await openPage(browser, '/echecs-ai?difficulty=easy');
      await sleep(1500);
      const start = await graphics(page);
      let played = 0;
      for (let m = 0; m < 10; m++) {
        if (!(await playOneMove(page, m))) break;
        played++;
        await sleep(2400);
      }
      await page.evaluate(() => window.MS3D.sweep());
      const end = await graphics(page);
      check(`dix coups joués (${played})`, played >= 8, played);
      check('les formes retirées sont rendues (aucune accumulation)', end.geometries <= start.geometries + 4, { start, end });
      check('aucune erreur JavaScript', errors.length === 0, errors);
      await page.close();
    }

    console.log('\n3. Les ombres : recalculées quand une pièce bouge, pas à chaque image');
    for (const route of ['/echecs-ai?difficulty=easy', '/echecs-local', '/ttt-local']) {
      const { page, errors } = await openPage(browser, route);
      await sleep(1500);
      const idle = await page.evaluate(async () => {
        const raf = () => new Promise(r => requestAnimationFrame(r));
        const r = window.MS3D.last.renderer;
        const s0 = window.MS3D.stats.shadowUpdates;
        const f0 = window.MS3D.stats.frames;
        for (let i = 0; i < 20; i++) await raf();
        return { autoUpdate: r.shadowMap.autoUpdate, frames: window.MS3D.stats.frames - f0, updates: window.MS3D.stats.shadowUpdates - s0 };
      });
      check(`${route} : au repos, ${idle.updates} recalcul(s) d'ombre pour ${idle.frames} images`, idle.autoUpdate === false && idle.updates <= 2 && idle.frames >= 15, idle);
      if (route.startsWith('/echecs-ai')) {
        const before = await page.evaluate(() => window.MS3D.stats.shadowUpdates);
        await playOneMove(page, 3);
        await sleep(900);
        const after = await page.evaluate(() => window.MS3D.stats.shadowUpdates);
        check('une pièce qui bouge fait recalculer l\'ombre', after > before, { before, after });
      }
      check(`${route} : aucune erreur JavaScript`, errors.length === 0, errors);
      await page.close();
    }

    console.log('\n4. L\'image ne change pas');
    for (const route of ['/echecs-local', '/ttt-local']) {
      const shots = [];
      for (const withModule of [true, false]) {
        const page = await browser.newPage({ viewport: { width: 420, height: 760 }, deviceScaleFactor: 1 });
        if (process.env.THREE_RUNTIME_FILE) {
          await page.route('**/vendor/three-r128.min.js', r => r.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
        }
        if (!withModule) await page.route('**/mindspille-3d.js', r => r.fulfill({ body: '', contentType: 'application/javascript' }));
        await page.goto(URL + route, { waitUntil: 'load' });
        await sleep(4500);
        shots.push(await page.locator('canvas').first().screenshot());
        await page.close();
      }
      const diff = await pixelDiff(browser, shots[0], shots[1]);
      check(`${route} : la même image avec ou sans le module (${(diff.share * 100).toFixed(2)} % de pixels différents)`, diff.sameSize && diff.share < 0.005, diff);
    }
  } catch (error) {
    failures++;
    console.error('  FAIL', error && error.stack || error);
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
  }
  console.log(failures ? `\n${failures} échec(s)` : '\nOK plateaux 3D fluides sur la durée');
  process.exit(failures ? 1 : 0);
})();
