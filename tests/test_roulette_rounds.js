/**
 * Roulette Royale en ligne : de vrais matchs contre le serveur.
 *
 * Ce que ce test protège :
 *   • le tirage de chaque manche est scellé AVANT les choix, et la révélation
 *     correspond à l'empreinte publiée ;
 *   • l'adversaire et les spectateurs n'apprennent que « a choisi », jamais la
 *     couleur, avant que les deux choix soient verrouillés ;
 *   • les points : un seul joueur a la couleur tirée → +1 ; personne, ou les
 *     deux → manche nulle ;
 *   • cinq manches, fin anticipée quand l'écart ne peut plus être comblé ;
 *   • égalité → manche décisive sur les deux couleurs choisies ; même couleur
 *     → on rechoisit ;
 *   • une couleur invalide ou un second choix sont ignorés ;
 *   • 30 s + 60 s de grâce : celui qui n'a pas choisi perd ; personne → annulé ;
 *   • une reconnexion retrouve son propre choix, jamais celui de l'adversaire ;
 *   • un match déjà décidé se règle même si un joueur part pendant le dernier
 *     tour de roue ;
 *   • le règlement part avec le bon vainqueur, le résumé avec ses couleurs.
 */
const { spawn } = require('child_process');
const http = require('http');
const path = require('path');
const crypto = require('crypto');
const { io } = require('socket.io-client');
const Rules = require('../public/roulette-rules.js');

const REPO_ROOT = path.join(__dirname, '..');
const GAME_PORT = 3141;
const MOCK_DB_PORT = 3142;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;
const PLAYER_1 = '30000000-0000-4000-8000-000000000011';
const PLAYER_2 = '30000000-0000-4000-8000-000000000012';
const SPECTATOR = '30000000-0000-4000-8000-000000000013';
const GAME = {
  full: '30000000-0000-4000-8000-0000000000a1',
  early: '30000000-0000-4000-8000-0000000000a2',
  timeout: '30000000-0000-4000-8000-0000000000a3',
  cancel: '30000000-0000-4000-8000-0000000000a4',
  secret: '30000000-0000-4000-8000-0000000000a5',
  reconnect: '30000000-0000-4000-8000-0000000000a6'
};
const DRAWS = {
  [GAME.full]: [0, 1, 2, 3, 4, 1, 0],
  [GAME.early]: [0, 0, 0],
  [GAME.secret]: [5],
  [GAME.reconnect]: [2, 2, 2, 2, 2]
};
let failures = 0;
const rpcCalls = [];

function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.log(`  FAIL ${label}${detail === undefined ? '' : ` -> ${JSON.stringify(detail)}`}`); }
}
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));

function onceWhere(socket, event, predicate = () => true, timeoutMs = 8000) {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => { socket.off(event, handler); reject(new Error(`timeout waiting for ${event}`)); }, timeoutMs);
    const handler = data => {
      if (!predicate(data)) return;
      clearTimeout(timer);
      socket.off(event, handler);
      resolve(data);
    };
    socket.on(event, handler);
  });
}

function startMockDatabase() {
  return http.createServer((request, response) => {
    const url = new URL(request.url, `http://127.0.0.1:${MOCK_DB_PORT}`);
    let body = '';
    request.on('data', chunk => { body += chunk; });
    request.on('end', () => {
      response.setHeader('Content-Type', 'application/json');
      if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
        const id = (url.searchParams.get('id') || '').replace(/^eq\./, '');
        return response.end(JSON.stringify([{
          id, game_type: 'color_roulette', player1_id: PLAYER_1, player2_id: PLAYER_2,
          bet_amount: 100, status: 'in_progress', is_ai_opponent: false, is_tournament: false,
          result: null, winner_id: null, game_settings: {}
        }]));
      }
      if (request.method === 'POST' && url.pathname.startsWith('/rest/v1/rpc/')) {
        const name = url.pathname.split('/').pop();
        let payload = null;
        try { payload = body ? JSON.parse(body) : null; } catch (_) {}
        rpcCalls.push({ name, payload });
        return response.end(name === 'load_game_server_room_states' ? '[]' : 'null');
      }
      response.statusCode = 404;
      response.end('{}');
    });
  });
}

function waitHealth(retries = 60) {
  return new Promise((resolve, reject) => {
    const attempt = left => {
      http.get(`${GAME_URL}/health`, res => { res.resume(); res.statusCode === 200 ? resolve() : retry(left); })
        .on('error', () => retry(left));
    };
    const retry = left => (left <= 0 ? reject(new Error('server unavailable')) : setTimeout(() => attempt(left - 1), 200));
    attempt(retries);
  });
}

async function connectUser(supabaseId, username) {
  const socket = io(GAME_URL, { transports: ['websocket'], reconnection: false });
  await onceWhere(socket, 'connect');
  socket.emit('auth:supabase', { supabaseId, username });
  await onceWhere(socket, 'auth:ok');
  return socket;
}

/** Les deux joueurs rejoignent ; rend la première manche ouverte (avec son sceau). */
async function startMatch(p1, p2, gameId) {
  const ready = onceWhere(p1, 'roulette_round_ready', d => d.room === gameId && d.round === 1);
  const started = onceWhere(p2, 'roulette_start', d => d.room === gameId);
  p1.emit('roulette_join', { room: gameId, gameId, player: 1, supabaseId: PLAYER_1, name: 'Alice', bet: 100, currency: 'HTG' });
  p2.emit('roulette_join', { room: gameId, gameId, player: 2, supabaseId: PLAYER_2, name: 'Bob', bet: 100, currency: 'HTG' });
  const start = await started;
  check(`[${gameId.slice(-2)}] la partie annonce cinq manches`, start.totalRounds === 5, start.totalRounds);
  return ready;
}

/** Joue une manche : rend le tour de roue public. */
async function playRound(p1, p2, gameId, round, c1, c2) {
  const spin = onceWhere(p1, 'roulette_spin', d => d.room === gameId && d.round === round);
  p1.emit('roulette_choice', { room: gameId, player: 1, color: c1 });
  p2.emit('roulette_choice', { room: gameId, player: 2, color: c2 });
  return spin;
}

function sealOk(gameId, spin, publishedHash) {
  const text = Rules.sealText(gameId, spin.round, spin.seal.kind, spin.seal.value, spin.seal.salt);
  return crypto.createHash('sha256').update(text).digest('hex') === publishedHash && spin.seal.hash === publishedHash;
}

async function main() {
  const mockDb = startMockDatabase();
  await new Promise(resolve => mockDb.listen(MOCK_DB_PORT, '127.0.0.1', resolve));
  const server = spawn(process.execPath, ['server.js'], {
    cwd: REPO_ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT),
      NODE_ENV: 'test',
      JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      SUPABASE_URL: `http://127.0.0.1:${MOCK_DB_PORT}`,
      SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app',
      ROULETTE_TEST_DRAWS: JSON.stringify(DRAWS),
      ROULETTE_SPIN_MS: '300',
      ROUND_PROOF_MS: '300',
      ROULETTE_FINAL_HOLD_MS: '100',
      ROULETTE_REPICK_MS: '200',
      TURN_DURATION_MS: '1500',
      GRACE_DURATION_MS: '1500',
      RECONNECT_DURATION_MS: '4000'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stderr.on('data', data => {
    const line = String(data);
    if (!/JWT_SECRET|Missing games\.id|persistence|summary/.test(line)) process.stderr.write(line);
  });

  const sockets = [];
  try {
    await waitHealth();
    const p1 = await connectUser(PLAYER_1, 'Alice');
    const p2 = await connectUser(PLAYER_2, 'Bob');
    const spectator = await connectUser(SPECTATOR, 'Claire');
    sockets.push(p1, p2, spectator);

    // ── A. Un match complet : manches nulles, égalité, manche décisive ─────
    console.log('A. Cinq manches, égalité, manche décisive (même couleur → on rechoisit)');
    let ready = await startMatch(p1, p2, GAME.full);
    check('la manche 1 publie une empreinte SHA-256 avant les choix', /^[0-9a-f]{64}$/.test(ready.seal || ''), ready);
    check('personne n’a encore choisi', ready.chosen && ready.chosen[1] === false && ready.chosen[2] === false, ready.chosen);

    // Plan : tirages 0,1,2,3,4 puis décisive (bits 1, puis 0).
    const plan = [
      { c: [0, 5], winner: 1, scores: [1, 0], label: 'seul Alice a le rouge : +1 Alice' },
      { c: [3, 1], winner: 2, scores: [1, 1], label: 'seul Bob a l’orange : +1 Bob' },
      { c: [2, 2], winner: 0, scores: [1, 1], label: 'les deux ont le jaune : manche nulle' },
      { c: [4, 5], winner: 0, scores: [1, 1], label: 'personne n’a le vert : manche nulle' },
      { c: [0, 1], winner: 0, scores: [1, 1], label: 'personne n’a le bleu : manche nulle' }
    ];
    for (let i = 0; i < plan.length; i++) {
      const round = i + 1;
      const step = plan[i];
      const spin = await playRound(p1, p2, GAME.full, round, step.c[0], step.c[1]);
      check(`manche ${round} : ${step.label}`, spin.winnerSlot === step.winner && JSON.stringify(spin.scores) === JSON.stringify(step.scores), spin);
      check(`manche ${round} : la révélation correspond à l’empreinte publiée`, sealOk(GAME.full, spin, ready.seal), { seal: spin.seal, published: ready.seal });
      check(`manche ${round} : la couleur tirée est la couleur scellée`, spin.drawn === DRAWS[GAME.full][i] && spin.seal.kind === 'color', spin.drawn);
      check(`manche ${round} : la roue a ses six couleurs et s’arrête sur la couleur tirée`,
        spin.wheel.length === 6 && spin.wheel[spin.landing.segment] === spin.drawn, spin.landing);
      if (round < 5) {
        const result = await onceWhere(p1, 'roulette_round_result', d => d.room === GAME.full && d.round === round);
        check(`manche ${round} : résultat public après le tour de roue`, result.winnerSlot === step.winner && result.next === 'next', result);
        ready = await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.full && d.round === round + 1);
      }
    }
    const tied = await onceWhere(p1, 'roulette_round_result', d => d.room === GAME.full && d.round === 5);
    check('1-1 après cinq manches : manche décisive annoncée', tied.next === 'decisive', tied);
    ready = await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.full && d.round === 6);
    check('la manche 6 est décisive', ready.decisive === true, ready);

    const repick = await playRound(p1, p2, GAME.full, 6, 2, 2);
    check('décisive, même couleur : rien n’est tiré, on rechoisit', repick.repick === true && repick.drawn === null && repick.winnerSlot === 0, repick);
    check('décisive, même couleur : sans tour de roue', repick.duration === 0, repick.duration);
    ready = await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.full && d.round === 7);
    check('une nouvelle manche décisive s’ouvre', ready.decisive === true, ready);

    const over = onceWhere(p1, 'game:over', d => d.room === GAME.full, 8000);
    const decisive = await playRound(p1, p2, GAME.full, 7, 5, 1);
    check('décisive : la roue ne garde que le orange et le violet, alternés', JSON.stringify(decisive.wheel) === JSON.stringify([1, 5, 1, 5, 1, 5]), decisive.wheel);
    check('décisive : le bit scellé 0 désigne la plus petite couleur (orange) → Bob', decisive.drawn === 1 && decisive.winnerSlot === 2 && decisive.seal.kind === 'bit', decisive);
    check('décisive : la révélation correspond à l’empreinte', sealOk(GAME.full, decisive, ready.seal));
    check('le tour de roue annonce la fin du match', decisive.final === true && decisive.matchWinnerSlot === 2, decisive);
    const end = await over;
    check('fin du match : Bob gagne 2-1', end.winnerSlot === 2 && end.result === 'loss' && JSON.stringify(end.scores) === JSON.stringify([1, 2]), end);
    check('l’historique de fin compte les sept tours de roue', Array.isArray(end.history) && end.history.length === 7, end.history && end.history.length);
    await sleep(400);
    const settlementA = rpcCalls.find(call => call.name === 'submit_game_result' && call.payload?.p_game_id === GAME.full);
    check('règlement : Bob vainqueur, résultat « win »', settlementA && settlementA.payload.p_winner_id === PLAYER_2 && settlementA.payload.p_result === 'win', settlementA);
    const summaryA = rpcCalls.find(call => call.name === 'record_match_summary' && call.payload?.p_game_id === GAME.full);
    const logA = summaryA?.payload?.p_summary?.log?.e || [];
    check('résumé : 7 manches, score 1-2', summaryA && summaryA.payload.p_summary.rounds === 7
      && summaryA.payload.p_summary.players[PLAYER_1].score === 1 && summaryA.payload.p_summary.players[PLAYER_2].score === 2, summaryA?.payload?.p_summary);
    check('journal : chaque couleur choisie (v) et tirée (t), manche (g)',
      logA.length === 14 && logA[0].p === 1 && logA[0].g === 1 && logA[0].v === '0' && logA[0].t === 0
      && logA[1].p === 2 && logA[1].v === '5' && logA.filter(e => e.g === 6).every(e => e.t === undefined), logA.slice(0, 4));

    // ── B. Fin anticipée et départ pendant le dernier tour de roue ─────────
    console.log('B. Fin anticipée (3-0 après trois manches)');
    ready = await startMatch(p1, p2, GAME.early);
    for (let round = 1; round <= 2; round++) {
      await playRound(p1, p2, GAME.early, round, 0, 1);
      await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.early && d.round === round + 1);
    }
    const earlyOver = onceWhere(p1, 'game:over', d => d.room === GAME.early);
    const third = await playRound(p1, p2, GAME.early, 3, 0, 1);
    check('3-0 avec deux manches restantes : le match est joué', third.final === true && third.matchWinnerSlot === 1 && JSON.stringify(third.scores) === JSON.stringify([3, 0]), third);
    // Bob quitte pendant le dernier tour de roue : le match décidé se conclut quand même.
    p2.disconnect();
    const earlyEnd = await earlyOver;
    check('départ pendant le dernier tour : Alice gagne quand même, sans forfait', earlyEnd.winnerSlot === 1 && earlyEnd.reason === 'normal', earlyEnd);
    const p2b = await connectUser(PLAYER_2, 'Bob');
    sockets.push(p2b);

    // ── C. Secret des choix, couleurs refusées, spectateur ────────────────
    console.log('C. Secret des choix et spectateur');
    ready = await startMatch(p1, p2b, GAME.secret);
    const spectatorState = onceWhere(spectator, 'spectator_state', d => d.gameId === GAME.secret);
    spectator.emit('spectator_join', { gameId: GAME.secret });
    const snap = await spectatorState;
    check('le spectateur reçoit l’état de la Roulette Royale', snap.gameType === 'color_roulette' && snap.state && snap.state.round === 1, snap);
    check('l’état du spectateur ne contient ni choix ni sceau secret', snap.state.seal === ready.seal && !JSON.stringify(snap.state).includes('"salt"') && !('choices' in snap.state), snap.state);

    const seenByBob = [], seenBySpectator = [];
    const recordBob = (event, data) => seenByBob.push({ event, data });
    const recordSpectator = (event, data) => seenBySpectator.push({ event, data });
    p2b.onAny(recordBob);
    spectator.onAny(recordSpectator);
    // Des couleurs invalides : ignorées, rien n'est verrouillé.
    for (const bad of [6, -1, 'rouge', 2.5, null, '9']) p1.emit('roulette_choice', { room: GAME.secret, player: 1, color: bad });
    await sleep(250);
    check('une couleur invalide n’est jamais verrouillée', !seenByBob.some(e => e.event === 'roulette_opponent_choice'), seenByBob.map(e => e.event));
    const locked = onceWhere(p1, 'roulette_choice_locked', d => d.round === 1);
    p1.emit('roulette_choice', { room: GAME.secret, player: 1, color: 3 });
    const lockedData = await locked;
    check('Alice reçoit la confirmation de SA couleur', lockedData.color === 3, lockedData);
    // Un second choix ne remplace pas le premier.
    p1.emit('roulette_choice', { room: GAME.secret, player: 1, color: 4 });
    await sleep(250);
    const bobSaw = seenByBob.find(e => e.event === 'roulette_opponent_choice');
    check('Bob apprend seulement qu’Alice a choisi', !!bobSaw && bobSaw.data.player === 1 && !('color' in bobSaw.data), bobSaw);
    const leak = [...seenByBob, ...seenBySpectator].some(e => e.event !== 'roulette_choice_locked' && JSON.stringify(e.data || {}).includes('"color":3'));
    check('aucun message à Bob ni au spectateur ne contient la couleur d’Alice', !leak);
    const spinSecret = onceWhere(spectator, 'roulette_spin', d => d.room === GAME.secret);
    p2b.emit('roulette_choice', { room: GAME.secret, player: 2, color: 5 });
    const spunForSpectator = await spinSecret;
    check('le spectateur voit les deux couleurs une fois verrouillées', spunForSpectator.choice1 === 3 && spunForSpectator.choice2 === 5, spunForSpectator);
    check('le second choix d’Alice a été ignoré', spunForSpectator.choice1 === 3);
    check('Bob a le violet tiré : +1 Bob', spunForSpectator.drawn === 5 && spunForSpectator.winnerSlot === 2, spunForSpectator);
    p2b.offAny(recordBob);
    spectator.offAny(recordSpectator);

    // ── D. Reconnexion au milieu d'une manche ─────────────────────────────
    console.log('D. Reconnexion : chacun retrouve son propre choix');
    await startMatch(p1, p2b, GAME.reconnect);
    p1.emit('roulette_choice', { room: GAME.reconnect, player: 1, color: 4 });
    await sleep(200);
    p1.disconnect();
    await sleep(300);
    const p1b = await connectUser(PLAYER_1, 'Alice');
    sockets.push(p1b);
    const back = onceWhere(p1b, 'roulette_start', d => d.room === GAME.reconnect);
    p1b.emit('roulette_join', { room: GAME.reconnect, gameId: GAME.reconnect, player: 1, supabaseId: PLAYER_1, name: 'Alice', bet: 100, currency: 'HTG' });
    const restored = await back;
    check('reconnexion : la manche 1 est retrouvée', restored.reconnected === true && restored.gameState.round === 1, restored.gameState);
    check('reconnexion : Alice retrouve son choix (bleu)', restored.gameState.myChoice === 4, restored.gameState);
    check('reconnexion : Bob n’a pas encore choisi', restored.gameState.opponentHasChosen === false, restored.gameState);
    const spinAfter = onceWhere(p1b, 'roulette_spin', d => d.room === GAME.reconnect && d.round === 1);
    p2b.emit('roulette_choice', { room: GAME.reconnect, player: 2, color: 2 });
    const resumedSpin = await spinAfter;
    check('après la reconnexion, la manche se joue normalement', resumedSpin.choice1 === 4 && resumedSpin.choice2 === 2 && resumedSpin.winnerSlot === 2, resumedSpin);
    const bobBack = onceWhere(p2b, 'roulette_start', d => d.room === GAME.reconnect);
    p2b.emit('roulette_join', { room: GAME.reconnect, gameId: GAME.reconnect, player: 2, supabaseId: PLAYER_2, name: 'Bob', bet: 100, currency: 'HTG' });
    const bobState = await bobBack;
    check('l’historique rendu à un joueur : la manche révélée, sans sel ni sceau',
      Array.isArray(bobState.gameState.history) && bobState.gameState.history.length === 1 && !JSON.stringify(bobState.gameState.history).includes('salt'), bobState.gameState.history);
    // Mutual quit pour libérer la room.
    p1b.emit('game_mutual_quit', { room: GAME.reconnect, game: 'roulette', player: 1 });
    p2b.emit('game_mutual_quit', { room: GAME.reconnect, game: 'roulette', player: 2 });
    await sleep(300);
    const quitSettlement = rpcCalls.find(call => call.name === 'submit_game_result' && call.payload?.p_game_id === GAME.reconnect);
    check('abandon d’un commun accord : réglé sans vainqueur', quitSettlement && quitSettlement.payload.p_result === 'mutual_quit' && quitSettlement.payload.p_winner_id === null, quitSettlement);

    // ── E. Le temps : celui qui n'a pas choisi perd ; personne → annulé ────
    console.log('E. Chronomètre : 30 s + 60 s de grâce (raccourcis ici)');
    await startMatch(p1b, p2b, GAME.timeout);
    const timeoutOver = onceWhere(p1b, 'game:over', d => d.room === GAME.timeout, 9000);
    p1b.emit('roulette_choice', { room: GAME.timeout, player: 1, color: 1 });
    const timedOut = await timeoutOver;
    check('Bob n’a pas choisi à temps : Alice gagne au temps', timedOut.winnerSlot === 1 && timedOut.reason === 'timeout', timedOut);

    await startMatch(p1b, p2b, GAME.cancel);
    const cancelled = await onceWhere(p1b, 'game:over', d => d.room === GAME.cancel, 9000);
    check('personne n’a choisi : match annulé', cancelled.result === 'cancel' && cancelled.reason === 'both_disconnected', cancelled);
  } catch (error) {
    failures++;
    console.log('  FAIL scénario interrompu :', error.message);
  } finally {
    for (const socket of sockets) { try { socket.disconnect(); } catch (_) {} }
    server.kill('SIGTERM');
    await new Promise(resolve => mockDb.close(resolve));
  }

  if (failures) {
    console.log(`\n${failures} échec(s)`);
    process.exit(1);
  }
  console.log('\nOK Roulette Royale en ligne : matchs joués contre le serveur');
}

main();
