'use strict';

// Alerte de sécurité Render du 26 octobre 2026 (Node.js du 21 octobre, certificats
// eMudhra compromis). Ce que ce fichier garantit :
//
//  1. Le runtime : `.node-version` épingle une version corrigée de la branche 24
//     (24.22.1 ou plus), `engines` ne descend jamais en dessous, la CI lit le même
//     fichier ; en CI, le Node qui exécute les tests est bien celui-là.
//  2. Three.js n'est servi que s'il a l'empreinte épinglée : le fichier vendorisé
//     est le bon, la route le renvoie octet pour octet, et un fichier altéré n'est
//     JAMAIS envoyé à un joueur (le serveur retombe sur un CDN, tenu à la même
//     empreinte, ou répond 503).
//  3. Les jetons du serveur : HS256 seulement — un jeton signé avec le même
//     secret mais un autre algorithme, ou sans signature, est refusé.
//  4. Plus de workflow GitHub qui exécute le code d'une autre branche avec un
//     jeton en écriture sur `main`.

const { spawn } = require('child_process');
const crypto = require('crypto');
const fs = require('fs');
const os = require('os');
const path = require('path');
const jwt = require('jsonwebtoken');
const { io } = require('socket.io-client');

const ROOT = path.join(__dirname, '..');
const PORT = 3241;
const URL = `http://127.0.0.1:${PORT}`;
const JWT_SECRET = 'test-only-security-runtime-secret-0123456789abcdef';

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : JSON.stringify(detail)); }
}
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
const semver = v => String(v).replace(/^v/, '').trim().split('.').map(Number);
const atLeast = (v, min) => { const a = semver(v), b = semver(min); for (let i = 0; i < 3; i++) { if ((a[i] || 0) !== (b[i] || 0)) return (a[i] || 0) > (b[i] || 0); } return true; };

// ── 1. Runtime ─────────────────────────────────────────────────────────────
console.log('\n— Runtime Node.js —');
const pinned = fs.readFileSync(path.join(ROOT, '.node-version'), 'utf8').trim();
check('.node-version épingle une version exacte de la branche 24', /^24\.\d+\.\d+$/.test(pinned), pinned);
check('.node-version ≥ 24.22.1 (correctifs du 21 octobre 2026)', atLeast(pinned, '24.22.1'), pinned);
const pkg = JSON.parse(fs.readFileSync(path.join(ROOT, 'package.json'), 'utf8'));
check('engines.node impose le plancher corrigé et reste sur la branche 24', pkg.engines && pkg.engines.node === '>=24.22.1 <25', pkg.engines);
const ci = fs.readFileSync(path.join(ROOT, '.github/workflows/server-ci.yml'), 'utf8');
check('la CI installe la version de .node-version', /node-version-file:\s*\.node-version/.test(ci));
if (process.env.CI) {
  check('en CI, les tests tournent sur la version épinglée', process.versions.node === pinned, process.versions.node);
} else {
  console.log(`  (info) Node local : ${process.versions.node} — la CI vérifie l'égalité avec ${pinned}`);
}

// ── 4. Workflows ───────────────────────────────────────────────────────────
console.log('\n— Workflows GitHub —');
const workflows = fs.readdirSync(path.join(ROOT, '.github/workflows'));
check('les générateurs temporaires « hotseat » (écriture sur main) ont disparu',
  !workflows.includes('bootstrap-real-hotseat.yml') && !workflows.includes('real-hotseat-pr-generator.yml'), workflows);
for (const name of workflows) {
  const text = fs.readFileSync(path.join(ROOT, '.github/workflows', name), 'utf8');
  check(`${name} : aucun droit d'écriture sur le dépôt`, !/contents:\s*write/.test(text));
}

// ── 2. Three.js ────────────────────────────────────────────────────────────
console.log('\n— Three.js vendorisé —');
const server = fs.readFileSync(path.join(ROOT, 'server.js'), 'utf8');
const pinnedDigest = (server.match(/const THREE_RUNTIME_SHA384 = '([^']+)'/) || [])[1];
const vendored = fs.readFileSync(path.join(ROOT, 'vendor/three-r128.min.js'));
const digest = body => crypto.createHash('sha384').update(body).digest('base64');
check('le fichier vendorisé a l\'empreinte épinglée dans server.js', !!pinnedDigest && digest(vendored) === pinnedDigest, { pinnedDigest, actual: digest(vendored) });
check('c\'est bien Three.js r128 (licence MIT conservée)', vendored.slice(0, 200).toString().includes('Three.js Authors') && vendored.toString().includes('const e="128"') && vendored.toString().includes('REVISION=e'));
check('server.js ne sert jamais une copie de CDN sans vérifier son empreinte', /if \(!threeRuntimeDigestOk\(body\)\) throw new Error\('three_runtime_digest_mismatch'\)/.test(server));

function startServer(extraEnv = {}) {
  const child = spawn(process.execPath, ['server.js'], {
    cwd: ROOT,
    env: { ...process.env, NODE_ENV: 'test', PORT: String(PORT), JWT_SECRET, SUPABASE_URL: '', ...extraEnv },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  child.stdout.on('data', () => {});
  child.stderr.on('data', () => {});
  return child;
}
async function waitUp() {
  for (let i = 0; i < 60; i++) {
    try { const r = await fetch(URL + '/health'); if (r.ok) return true; } catch {}
    await sleep(150);
  }
  return false;
}
async function stop(child) {
  child.kill('SIGKILL');
  await new Promise(resolve => child.once('exit', resolve));
}

function connect(token) {
  return new Promise(resolve => {
    const socket = io(URL, { transports: ['websocket'], auth: { token }, reconnection: false, timeout: 4000 });
    socket.on('connect', () => { socket.close(); resolve('connected'); });
    socket.on('connect_error', error => { socket.close(); resolve(String(error && error.message)); });
  });
}

(async () => {
  let child = startServer();
  try {
    check('le serveur démarre', await waitUp());
    const response = await fetch(URL + '/vendor/three-r128.min.js');
    const body = Buffer.from(await response.arrayBuffer());
    check('la route renvoie le fichier vendorisé octet pour octet', response.status === 200 && body.equals(vendored), { status: response.status, length: body.length });
    check('servi comme JavaScript', /javascript/.test(response.headers.get('content-type') || ''), response.headers.get('content-type'));

    // ── 3. Jetons ───────────────────────────────────────────────────────────
    console.log('\n— Jetons du serveur —');
    const claims = { userId: crypto.randomUUID(), username: 'Testeur', supabaseId: crypto.randomUUID() };
    check('un jeton HS256 du serveur est accepté', await connect(jwt.sign(claims, JWT_SECRET, { algorithm: 'HS256', expiresIn: '5m' })) === 'connected');
    check('le même secret avec HS512 est refusé', await connect(jwt.sign(claims, JWT_SECRET, { algorithm: 'HS512', expiresIn: '5m' })) === 'unauthorized');
    const unsigned = Buffer.from(JSON.stringify({ alg: 'none', typ: 'JWT' })).toString('base64url') + '.' + Buffer.from(JSON.stringify(claims)).toString('base64url') + '.';
    check('un jeton sans signature (alg none) est refusé', await connect(unsigned) === 'unauthorized');
    check('un jeton signé avec un autre secret est refusé', await connect(jwt.sign(claims, 'another-secret-entirely-0123456789', { algorithm: 'HS256' })) === 'unauthorized');
  } finally {
    await stop(child);
  }

  // Un fichier altéré sur le disque n'est jamais envoyé.
  console.log('\n— Fichier altéré —');
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'three-tampered-'));
  const tampered = Buffer.concat([vendored, Buffer.from('\n;window.__injected=1;\n')]);
  const tamperedPath = path.join(tmp, 'three.min.js');
  fs.writeFileSync(tamperedPath, tampered);
  child = startServer({ THREE_RUNTIME_PATH: tamperedPath });
  try {
    check('le serveur démarre avec un fichier altéré', await waitUp());
    const response = await fetch(URL + '/vendor/three-r128.min.js');
    const body = Buffer.from(await response.arrayBuffer());
    check('le fichier altéré n\'est jamais servi', !body.equals(tampered) && !body.includes('__injected'));
    check('réponse : la copie CDN vérifiée, ou 503 sans réseau',
      (response.status === 200 && digest(body) === pinnedDigest) || response.status === 503, { status: response.status });
  } finally {
    await stop(child);
    fs.rmSync(tmp, { recursive: true, force: true });
  }

  if (failures) {
    console.error(`\nFAIL ${failures} vérification(s) de sécurité`);
    process.exit(1);
  }
  console.log('\nOK sécurité du runtime');
})().catch(error => { console.error(error); process.exit(1); });
