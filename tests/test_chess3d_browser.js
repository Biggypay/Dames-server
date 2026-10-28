/**
 * Les échecs en 3D (public/mindspille-chess3d.js), dans un vrai navigateur.
 * Owner, 2026-10-28 : « des pièces plus raffinées… un vrai plateau en 3D… ne me
 * fais pas des chevaux à l'envers ».
 *
 * 1. Le module est servi et chargé par les trois pages ; il ne reste rien des
 *    Noirs rouges ; la page « Jouer avec un ami » ne parle plus d'IA.
 * 2. Chaque cavalier regarde le camp adverse : les naseaux du cavalier blanc
 *    sont du côté des Noirs, ceux du noir du côté des Blancs — vu de la place
 *    des Blancs comme de celle des Noirs. Avant, les quatre regardaient leur
 *    propre camp.
 * 3. Ivoire et ébène, plateau d'érable et de noyer, 64 cases repérables, et les
 *    coordonnées gravées des deux côtés du cadre.
 * 4. Les pièces prises s'affichent en figurines avec l'avance matérielle ; un
 *    pion promu n'est pas une prise.
 * 5. Les surfaces que le module construit (pièces tournées, tête et crinière du
 *    cavalier) sont fermées et tournées vers l'extérieur, et les 32 pièces
 *    restent sous 80 000 triangles : à 205 000, le rendu logiciel de la CI
 *    tombait à 3 images/s et les tests d'en-tête et de messagerie échouaient.
 */
const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const { chromium } = require('playwright-core');
const { chromiumBinary } = require('./helpers/chromium');

const REPO_ROOT = path.join(__dirname, '..');
const PORT = 3216;
const URL = `http://127.0.0.1:${PORT}`;
const PAGES = ['echecs_multi', 'echecs_ai', 'echecs_local'];

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

function get(route) {
  return new Promise((resolve, reject) => {
    http.get(URL + route, res => {
      let body = '';
      res.setEncoding('utf8');
      res.on('data', c => { body += c; });
      res.on('end', () => resolve({ status: res.statusCode, type: res.headers['content-type'] || '', body }));
    }).on('error', reject);
  });
}

async function openPage(browser, route) {
  const page = await browser.newPage({ viewport: { width: 390, height: 844 }, deviceScaleFactor: 1 });
  const errors = [];
  page.on('pageerror', e => errors.push(String(e)));
  if (process.env.THREE_RUNTIME_FILE) {
    await page.route('**/vendor/three-r128.min.js', r =>
      r.fulfill({ path: process.env.THREE_RUNTIME_FILE, contentType: 'application/javascript' }));
  }
  await page.goto(URL + route, { waitUntil: 'load' });
  await page.waitForFunction(() => window.MS3D && window.MS3D.last && window.MS3D.stats.frames > 5, null, { timeout: 30000 });
  /* Les pages font apparaître les pièces (échelle 0 → 1 en 0,6 s) : une mesure
     prise pendant l'animation verrait un cavalier réduit à un point. */
  await page.waitForFunction(() => {
    let count = 0, settled = true;
    window.MS3D.last.scene.traverse(o => {
      if (!o.userData || o.userData.type !== 'piece') return;
      count++;
      if (Math.abs(o.scale.x - 1) > 1e-3) settled = false;
    });
    return count === 32 && settled;
  }, null, { timeout: 30000 });
  await sleep(300);
  return { page, errors };
}

/* Un vrai clic au centre d'une case (rangée 0 = 8e rangée, colonne 0 = a). */
async function clickSquare(page, row, col) {
  const pt = await page.evaluate(([r, c]) => {
    const { camera, renderer } = window.MS3D.last;
    const CELL = 1.4, BO = 3.5 * CELL;
    const v = new THREE.Vector3(c * CELL - BO, 0.1, r * CELL - BO).project(camera);
    const rect = renderer.domElement.getBoundingClientRect();
    return { x: rect.left + (v.x + 1) / 2 * rect.width, y: rect.top + (1 - v.y) / 2 * rect.height };
  }, [row, col]);
  await page.mouse.click(pt.x, pt.y);
}
async function play(page, from, to) {
  await clickSquare(page, from[0], from[1]);
  await sleep(250);
  await clickSquare(page, to[0], to[1]);
  await sleep(1200);
}
const square = alg => [8 - Number(alg[1]), 'abcdefgh'.indexOf(alg[0])];

/*
 * Les cavaliers, vus d'une place (theta 0 = côté des Blancs, π = côté des
 * Noirs) : pour chacun, ses naseaux sont-ils plus loin ou plus près de cette
 * place que le centre de la pièce ? Un cavalier tourne le dos à son propre
 * joueur (il regarde l'adversaire) et fait face à l'autre.
 */
function knightsSeenFrom(page, theta) {
  return page.evaluate(theta => {
    const { scene } = window.MS3D.last;
    const eye = new THREE.Vector3(Math.sin(theta) * 20, 14, Math.cos(theta) * 20);
    const out = [];
    scene.traverse(o => {
      if (!o.isGroup || !o.userData || o.userData.ptype !== 2) return;
      const center = new THREE.Vector3();
      o.getWorldPosition(center);
      /* Les naseaux : la pièce de détail la plus éloignée de l'axe, devant les yeux. */
      let nose = null, far = -1;
      o.children.forEach(m => {
        if (!m.isMesh || !m.material || !/-detail$/.test(m.material.name)) return;
        m.geometry.computeBoundingSphere();
        const p = m.geometry.boundingSphere.center.clone().applyMatrix4(m.matrixWorld);
        const d = Math.hypot(p.x - center.x, p.z - center.z);
        if (d > far) { far = d; nose = p; }
      });
      if (!nose) return;
      out.push({
        player: o.userData.player,
        row: o.userData.row,
        col: o.userData.col,
        /* > 0 : les naseaux sont plus loin de la place que la pièce, à plat
           (les naseaux sont plus hauts que le pied : la hauteur ne compte pas). */
        away: Math.hypot(nose.x - eye.x, nose.z - eye.z) - Math.hypot(center.x - eye.x, center.z - eye.z),
        noseDz: nose.z - center.z
      });
    });
    return out;
  }, theta);
}

async function main() {
  console.log('1. Le module, les pages, plus de rouge');
  for (const name of PAGES) {
    const html = fs.readFileSync(path.join(REPO_ROOT, 'public', `${name}.html`), 'utf8');
    check(`${name} : charge mindspille-chess3d.js juste après le moteur`,
      /<script src="\/echecs-engine\.js"><\/script>\s*<script src="\/mindspille-chess3d\.js"><\/script>/.test(html));
    const left = ['0xc02818', '0xd63020', '🔴', 'av-red', 'sym-red', 'cap-dot-red', "'Rouges'"].filter(w => html.includes(w));
    check(`${name} : plus aucun Noir dessiné en rouge`, left.length === 0, left);
  }
  const local = fs.readFileSync(path.join(REPO_ROOT, 'public', 'echecs_local.html'), 'utf8');
  check('« Jouer avec un ami » ne s\'annonce plus « Entraînement · IA »',
    local.includes('<span class="manche-lbl">Jouer avec un ami</span>') && !local.includes('Entraînement · IA'));

  const server = spawn('node', ['server.js'], {
    cwd: REPO_ROOT,
    env: { ...process.env, PORT: String(PORT), NODE_ENV: 'test', JWT_SECRET: 'test-only-secret-with-more-than-32-characters' },
    stdio: ['ignore', 'ignore', 'inherit']
  });
  let browser;
  try {
    await waitForHealth();
    const served = await get('/mindspille-chess3d.js');
    check('le serveur sert /mindspille-chess3d.js en JavaScript',
      served.status === 200 && /javascript/.test(served.type) && served.body.includes('MindspilleChess3D'), served.status);

    browser = await chromium.launch({ executablePath: chromiumBinary(), args: ['--use-gl=angle', '--use-angle=swiftshader', '--enable-unsafe-swiftshader'] });

    console.log('\n2. Les cavaliers regardent le camp adverse');
    const { page, errors } = await openPage(browser, '/echecs-local');
    const fromWhite = await knightsSeenFrom(page, 0);
    const fromBlack = await knightsSeenFrom(page, Math.PI);
    check('quatre cavaliers sur le plateau', fromWhite.length === 4, fromWhite);
    const white = fromWhite.filter(k => k.player === 0), black = fromWhite.filter(k => k.player === 1);
    check('les naseaux des cavaliers blancs pointent vers les Noirs (8e rangée)',
      white.length === 2 && white.every(k => k.noseDz < -0.1), white);
    check('les naseaux des cavaliers noirs pointent vers les Blancs (1re rangée)',
      black.length === 2 && black.every(k => k.noseDz > 0.1), black);
    check('vus de la place des Blancs : leurs cavaliers regardent devant eux, ceux des Noirs leur font face',
      white.every(k => k.away > 0.05) && black.every(k => k.away < -0.05), fromWhite);
    const wB = fromBlack.filter(k => k.player === 0), bB = fromBlack.filter(k => k.player === 1);
    check('vus de la place des Noirs : leurs cavaliers regardent devant eux, ceux des Blancs leur font face',
      bB.every(k => k.away > 0.05) && wB.every(k => k.away < -0.05), fromBlack);

    /* La vue tourne : les pièces ne tournent pas avec elle. */
    const before = await page.evaluate(() => {
      const r = [];
      window.MS3D.last.scene.traverse(o => { if (o.isGroup && o.userData && o.userData.ptype) r.push(o.rotation.y); });
      return r;
    });
    await page.click('#btn-topview');
    await sleep(900);
    await page.click('#btn-topview');
    await sleep(900);
    const after = await page.evaluate(() => {
      const r = [];
      window.MS3D.last.scene.traverse(o => { if (o.isGroup && o.userData && o.userData.ptype) r.push(o.rotation.y); });
      return r;
    });
    check('changer de vue ne fait tourner aucune pièce', before.length === 32 && JSON.stringify(before) === JSON.stringify(after), { before: before.length, after: after.length });

    console.log('\n3. Ivoire et ébène, un vrai plateau');
    const look = await page.evaluate(() => {
      const { scene } = window.MS3D.last;
      const bodies = {}, squares = [];
      let frameMap = null, red = 0;
      scene.traverse(o => {
        if (!o.isMesh) return;
        const mats = Array.isArray(o.material) ? o.material : [o.material];
        mats.forEach(m => {
          if (!m || !m.color) return;
          if (m.name === 'chess-ivory' || m.name === 'chess-ebony') {
            const hsl = {}; m.color.getHSL(hsl); bodies[m.name] = hsl.l;
          }
          const hsl = {}; m.color.getHSL(hsl);
          if (o.parent && o.parent.userData && o.parent.userData.ptype && hsl.s > 0.5 && (hsl.h < 0.05 || hsl.h > 0.95)) red++;
          if (m.map && m.map.image && m.map.image.width >= 1024) frameMap = m.map.image;
        });
        if (o.userData && typeof o.userData.row === 'number' && !(o.parent && o.parent.userData && o.parent.userData.ptype)) squares.push(o.userData.row * 8 + o.userData.col);
      });
      /* Les coordonnées : des lettres de laiton au milieu de la bande des Blancs
         (en bas du canevas) et de celle des Noirs (en haut) — sous et au-dessus
         des filets dorés, qui ne sont pas comptés. */
      let brassBottom = 0, brassTop = 0;
      if (frameMap) {
        const ctx = frameMap.getContext('2d'), W = frameMap.width;
        const count = (from, to) => {
          const y0 = Math.round(W * from), h = Math.round(W * (to - from));
          const d = ctx.getImageData(0, y0, W, h).data;
          let n = 0;
          for (let i = 0; i < d.length; i += 4) if (d[i] > 170 && d[i + 1] > 130 && d[i + 2] < 120) n++;
          return n;
        };
        brassBottom = count(0.967, 0.99);
        brassTop = count(0.01, 0.033);
      }
      return { bodies, red, squares: new Set(squares).size, frame: !!frameMap, brassBottom, brassTop };
    });
    check('Blancs en ivoire (clairs), Noirs en ébène (sombres)',
      look.bodies['chess-ivory'] > 0.45 && look.bodies['chess-ebony'] < 0.2, look.bodies);
    check('aucune pièce rouge', look.red === 0, look.red);
    check('64 cases repérables (rangée, colonne)', look.squares === 64, look.squares);
    check('le cadre porte les coordonnées, côté Blancs et côté Noirs',
      look.frame && look.brassBottom > 50 && look.brassTop > 50, look);

    console.log('\n4. Les pièces prises, en figurines');
    await play(page, square('e2'), square('e4'));
    await play(page, square('d7'), square('d5'));
    await play(page, square('e4'), square('d5'));
    const afterExd5 = await page.evaluate(() => ({
      human: document.getElementById('cap-human').textContent, humanCount: document.getElementById('cap-human').getAttribute('data-count'),
      ai: document.getElementById('cap-ai').textContent
    }));
    check('après exd5 : un pion noir sous les Blancs, avance +1',
      afterExd5.humanCount === '1' && afterExd5.human.includes('♟') && afterExd5.human.includes('+1') && afterExd5.ai === '', afterExd5);
    await play(page, square('d8'), square('d5'));
    const afterQxd5 = await page.evaluate(() => ({
      human: document.getElementById('cap-human').textContent, ai: document.getElementById('cap-ai').textContent,
      aiCount: document.getElementById('cap-ai').getAttribute('data-count')
    }));
    check('après Dxd5 : un pion de chaque côté, plus d\'avance affichée',
      afterQxd5.aiCount === '1' && !afterQxd5.human.includes('+') && !afterQxd5.ai.includes('+'), afterQxd5);

    const pure = await page.evaluate(() => {
      const start = [-4, -2, -3, -5, -6, -3, -2, -4, -1, -1, -1, -1, -1, -1, -1, -1].concat(new Array(32).fill(0), [1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 6, 3, 2, 4]);
      const promoted = start.slice(); promoted[48] = 0; promoted[20] = 5;            // un pion blanc devenu dame
      const knightDown = start.slice(); knightDown[1] = 0; knightDown[9] = 0;        // les Noirs ont perdu Cb8 et un pion
      const C = window.MindspilleChess3D.captured;
      return { start: C(start), promoted: C(promoted), knightDown: C(knightDown) };
    });
    check('position de départ : rien de pris, aucune avance',
      pure.start[0].pieces.length === 0 && pure.start[1].pieces.length === 0 && pure.start[0].advantage === 0, pure.start);
    check('un pion promu n\'est pas une prise (avance +8 pour la dame en plus)',
      pure.promoted[1].pieces.length === 0 && pure.promoted[0].pieces.length === 0 && pure.promoted[0].advantage === 8, pure.promoted);
    check('les prises de la plus lourde à la plus légère (cavalier puis pion), avance +4',
      JSON.stringify(pure.knightDown[0].pieces) === '[2,1]' && pure.knightDown[0].advantage === 4, pure.knightDown);

    console.log('\n5. Des surfaces fermées, tournées vers l’extérieur, et légères');
    /* Les surfaces que le module construit lui-même : chaque pièce tournée, la
       tête et la crinière du cavalier. Fermée = chaque arête (par position)
       borde exactement deux triangles : ni trou ni triangle de trop. */
    const meshes = await page.evaluate(() => {
      const report = {}, total = { triangles: 0 };
      const count = { 1: 16, 2: 4, 3: 4, 4: 4, 5: 2, 6: 2 };
      for (let type = 1; type <= 6; type++) {
        const g = window.MindspilleChess3D.piece(0, type);
        g.children.forEach(m => {
          const geo = m.geometry;
          total.triangles += count[type] * (geo.index ? geo.index.count : geo.attributes.position.count) / 3;
        });
        report[type] = (type === 2 ? [0, 1, 2] : [0]).map(i => {
          const geo = g.children[i].geometry, pos = geo.attributes.position, nor = geo.attributes.normal, idx = geo.index;
          const at = k => idx ? idx.getX(k) : k;
          const key = j => [pos.getX(j), pos.getY(j), pos.getZ(j)].map(v => Math.round(v * 1e5)).join(',');
          const edges = new Map();
          let faces = 0, flipped = 0;
          const A = new THREE.Vector3(), B = new THREE.Vector3(), C = new THREE.Vector3(), N = new THREE.Vector3(), V = new THREE.Vector3();
          for (let k = 0; k < (idx ? idx.count : pos.count); k += 3) {
            const a = at(k), b = at(k + 1), c = at(k + 2), ka = key(a), kb = key(b), kc = key(c);
            if (ka === kb || kb === kc || kc === ka) continue;
            faces++;
            for (const [u, v] of [[ka, kb], [kb, kc], [kc, ka]]) {
              const e = u < v ? u + '|' + v : v + '|' + u;
              edges.set(e, (edges.get(e) || 0) + 1);
            }
            A.fromBufferAttribute(pos, a); B.fromBufferAttribute(pos, b); C.fromBufferAttribute(pos, c);
            N.subVectors(B, A).cross(C.sub(A));
            V.fromBufferAttribute(nor, a).add(A.fromBufferAttribute(nor, b)).add(B.fromBufferAttribute(nor, c));
            if (N.dot(V) < 0) flipped++;
          }
          let open = 0;
          edges.forEach(n => { if (n !== 2) open++; });
          return { faces, open, flipped };
        });
      }
      return { report, triangles: Math.round(total.triangles) };
    });
    const surfaces = Object.values(meshes.report).flat();
    check('chaque surface sculptée est fermée : chaque arête borde exactement deux triangles',
      surfaces.length === 8 && surfaces.every(r => r.faces > 0 && r.open === 0), meshes.report);
    check('chaque triangle regarde du même côté que ses normales (vers l’extérieur)',
      surfaces.every(r => r.flipped === 0), meshes.report);
    /* Le rendu logiciel des tests et les téléphones modestes paient chaque
       triangle : 205 000 pour 32 pièces faisaient tomber la page à 3 images/s. */
    check(`les 32 pièces tiennent en moins de 80 000 triangles (${meshes.triangles})`, meshes.triangles < 80000, meshes.triangles);

    check('/echecs-local : aucune erreur JavaScript', errors.length === 0, errors);
    await page.close();

    for (const route of ['/echecs-ai?difficulty=easy']) {
      const opened = await openPage(browser, route);
      const knights = await knightsSeenFrom(opened.page, 0);
      check(`${route} : les cavaliers regardent le camp adverse`,
        knights.length === 4 && knights.every(k => (k.player === 0 ? k.noseDz < -0.1 : k.noseDz > 0.1)), knights);
      check(`${route} : aucune erreur JavaScript`, opened.errors.length === 0, opened.errors);
      await opened.page.close();
    }
  } finally {
    if (browser) await browser.close();
    server.kill();
  }

  if (failures) {
    console.error(`\n${failures} vérification(s) en échec`);
    process.exit(1);
  }
  console.log('\nOK échecs 3D : pièces, cavaliers, plateau, prises');
}

main().catch(err => { console.error(err); process.exit(1); });
