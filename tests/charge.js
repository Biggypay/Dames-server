// Jusqu'où tient le serveur de jeu tel qu'il est aujourd'hui ?
//
// On ne discute pas de fournisseurs : on monte en charge sur le vrai
// server.js, avec de vraies parties de dames validées par le moteur, et on
// relève trois chiffres — mémoire par joueur, latence d'un coup, coups par
// seconde. Le reste n'est que de l'extrapolation, annoncée comme telle.
const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const { io } = require('socket.io-client');

const REPO = require('path').join(__dirname, '..');
const PORT = 3140;
const URL = 'http://127.0.0.1:' + PORT;
const PALIERS = (process.argv[2] || '250,500,1000,2000').split(',').map(Number);

const sleep = ms => new Promise(r => setTimeout(r, ms));
const pct = (a, p) => a.length ? a.slice().sort((x, y) => x - y)[Math.min(a.length - 1, Math.floor(a.length * p))] : 0;

function waitHealth(retries = 80) {
  return new Promise((res, rej) => {
    const t = n => http.get(URL + '/health', r => { r.resume(); r.statusCode === 200 ? res() : again(n); }).on('error', () => again(n));
    const again = n => n <= 0 ? rej(new Error('serveur injoignable')) : setTimeout(() => t(n - 1), 250);
    t(retries);
  });
}
function rss(pid) {
  try {
    const m = /VmRSS:\s+(\d+) kB/.exec(fs.readFileSync(`/proc/${pid}/status`, 'utf8'));
    return m ? Math.round(Number(m[1]) / 1024) : null;   // Mo
  } catch { return null; }
}
function cpuSeconds(pid) {
  try {
    const f = fs.readFileSync(`/proc/${pid}/stat`, 'utf8').split(' ');
    return (Number(f[13]) + Number(f[14])) / 100;        // utime + stime, en secondes
  } catch { return null; }
}

// Quatre coups d'ouverture légaux qui ne créent aucune prise obligatoire :
// les blancs restent à gauche, les noirs à droite, personne ne se touche.
const OUVERTURE = [
  { joueur: 1, from: { row: 6, col: 1 }, to: { row: 5, col: 0 } },
  { joueur: 2, from: { row: 3, col: 8 }, to: { row: 4, col: 9 } },
  { joueur: 1, from: { row: 6, col: 3 }, to: { row: 5, col: 2 } },
  { joueur: 2, from: { row: 3, col: 6 }, to: { row: 4, col: 7 } }
];

let ipCounter = 0;
function nextIp() {                       // un joueur = une adresse, comme en vrai
  ipCounter++;
  return `10.${(ipCounter >> 16) & 255}.${(ipCounter >> 8) & 255}.${ipCounter & 255}`;
}

function connect(id, nom) {
  return new Promise((resolve, reject) => {
    const s = io(URL, {
      transports: ['websocket'], reconnection: false,
      extraHeaders: { 'x-forwarded-for': nextIp() }
    });
    const t = setTimeout(() => reject(new Error('connexion expirée')), 20000);
    s.on('connect_error', e => { clearTimeout(t); reject(e); });
    s.on('connect', () => {
      s.emit('auth:supabase', { supabaseId: id, username: nom });
      s.once('auth:ok', () => { clearTimeout(t); resolve(s); });
    });
  });
}

let roomCounter = 0;
async function ouvrirPartie() {
  // Un nom de room neuf à chaque fois : une room déjà jouée refuserait
  // l'ouverture scriptée, et on compterait des refus au lieu de mesurer.
  const n = ++roomCounter;
  const room = `charge-${n}`;
  const [a, b] = await Promise.all([
    connect(`charge-a-${n}`, `A${n}`),
    connect(`charge-b-${n}`, `B${n}`)
  ]);
  const demarre = new Promise(res => { let vus = 0; const f = () => { if (++vus === 2) res(); };
    a.once('dames_start', f); b.once('dames_start', f); });
  a.emit('dames_join', { room, player: 1, supabaseId: `charge-a-${n}`, name: `A${n}`, bet: 0, currency: 'HTG' });
  b.emit('dames_join', { room, player: 2, supabaseId: `charge-b-${n}`, name: `B${n}`, bet: 0, currency: 'HTG' });
  await Promise.race([demarre, sleep(20000)]);
  return { room, a, b };
}

// Un coup : on chronomètre de l'émission jusqu'à ce que l'ADVERSAIRE le reçoive.
// C'est ce que le joueur d'en face attend réellement.
function jouer(partie, coup) {
  const emetteur = coup.joueur === 1 ? partie.a : partie.b;
  const recepteur = coup.joueur === 1 ? partie.b : partie.a;
  return new Promise(resolve => {
    const debut = process.hrtime.bigint();
    const fini = ok => { clearTimeout(t); recepteur.off('dames_move', onMove); emetteur.off('game:error', onErr); resolve(ok); };
    const t = setTimeout(() => fini({ ok: false, raison: 'silence' }), 15000);
    const onMove = () => fini({ ok: true, ms: Number(process.hrtime.bigint() - debut) / 1e6 });
    const onErr = d => fini({ ok: false, raison: (d && d.message) || 'refus' });
    recepteur.on('dames_move', onMove);
    emetteur.on('game:error', onErr);
    emetteur.emit('dames_move', { room: partie.room, player: coup.joueur, from: coup.from, to: coup.to });
  });
}

(async () => {
  const srv = spawn('node', ['server.js'], {
    cwd: REPO,
    env: { ...process.env, PORT: String(PORT), NODE_ENV: 'test', ALLOWED_ORIGIN: '*', FRAME_ANCESTORS: '*' },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  srv.stdout.on('data', () => {});
  srv.stderr.on('data', d => { const s = String(d); if (!/JWT_SECRET|SUPABASE/.test(s)) process.stderr.write('[srv] ' + s.slice(0, 200)); });

  await waitHealth();
  const base = rss(srv.pid);
  console.log(`Serveur démarré (pid ${srv.pid}) — mémoire au repos : ${base} Mo\n`);
  console.log('parties  joueurs  mémoire  Mo/joueur  connexion_p95  coup_p50  coup_p95  coup_p99  coups/s  échecs');
  console.log('─'.repeat(104));

  const parties = [];
  let ouvertes = 0;

  for (const cible of PALIERS) {
    const latencesConnexion = [];
    let echecsConnexion = 0;
    // Par vagues de 50 pour ne pas noyer le client, qui partage les mêmes cœurs.
    while (ouvertes < cible) {
      const lot = Math.min(50, cible - ouvertes);
      const debut = Date.now();
      const res = await Promise.allSettled(Array.from({ length: lot }, () => ouvrirPartie()));
      for (const r of res) {
        if (r.status === 'fulfilled') { parties.push(r.value); latencesConnexion.push(Date.now() - debut); }
        else echecsConnexion++;
      }
      ouvertes += lot;
      await sleep(20);
    }

    await sleep(500);
    const memoire = rss(srv.pid);
    const cpuAvant = cpuSeconds(srv.pid);

    // Toutes les parties jouent leurs quatre coups en même temps : c'est la
    // pointe, pas la moyenne — le pire moment d'un tournoi.
    const latences = [];
    let refus = 0;
    const debutCoups = Date.now();
    for (const coup of OUVERTURE) {
      const r = await Promise.all(parties.map(p => jouer(p, coup)));
      for (const x of r) x.ok ? latences.push(x.ms) : refus++;
    }
    const dureeCoups = (Date.now() - debutCoups) / 1000;
    const cpuUtilise = cpuSeconds(srv.pid) - cpuAvant;

    const joueurs = parties.length * 2;
    console.log(
      String(parties.length).padEnd(9) +
      String(joueurs).padEnd(9) +
      (memoire + ' Mo').padEnd(9) +
      ((memoire - base) / joueurs).toFixed(2).padEnd(11) +
      (pct(latencesConnexion, 0.95) + ' ms').padEnd(15) +
      (Math.round(pct(latences, 0.50)) + ' ms').padEnd(10) +
      (Math.round(pct(latences, 0.95)) + ' ms').padEnd(10) +
      (Math.round(pct(latences, 0.99)) + ' ms').padEnd(10) +
      Math.round(latences.length / dureeCoups).toString().padEnd(9) +
      String(echecsConnexion + refus)
    );
    console.log(`         (cpu serveur pour ces ${latences.length} coups : ${cpuUtilise.toFixed(2)} s → ${(cpuUtilise / Math.max(latences.length, 1) * 1000).toFixed(3)} ms de cpu par coup)`);

    // On remet les parties à zéro pour le palier suivant : nouvelles rooms.
    for (const p of parties) { p.a.disconnect(); p.b.disconnect(); }
    parties.length = 0;
    ouvertes = 0;
    await sleep(1500);
  }

  srv.kill('SIGTERM');
  process.exit(0);
})().catch(e => { console.error('ÉCHEC :', e.message); process.exit(1); });
