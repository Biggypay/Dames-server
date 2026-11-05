/**
 * Roulette Royale en ligne : de vrais matchs contre le serveur.
 *
 * Ce que ce test protège :
 *   • le tirage de chaque manche est scellé AVANT les choix, et la révélation
 *     correspond à l'empreinte publiée ;
 *   • l'adversaire et les spectateurs n'apprennent que « a choisi », jamais la
 *     couleur, avant que les deux choix soient verrouillés ;
 *   • les points (règles du 2026-11-05) : la couleur la plus proche de la
 *     couleur tirée → +1 ; à égale distance → manche nulle ; même couleur
 *     pour les deux → rien ne tourne, on rechoisit, la manche ne compte pas ;
 *   • cinq manches comptées, fin anticipée quand l'écart ne peut plus être
 *     comblé ;
 *   • égalité → manches décisives sur les deux couleurs choisies, DEUX PAR
 *     DEUX : après la première d'une paire, l'autre joueur joue toujours la
 *     seconde ; 1-1 → une nouvelle paire ; 2-0 → victoire ;
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
  // Une valeur par manche ouverte, rechoix compris (manches 3 et 9) ; en
  // manche décisive, 0 = la plus petite des deux couleurs, 1 = la plus grande.
  [GAME.full]: [3, 1, 5, 5, 2, 4, 1, 0, 1, 0, 1],
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

    // ── A. Un match complet : la plus proche, l'égale distance, le rechoix,
    //       puis deux paires de manches décisives (1-1, puis 2-0) ─────────
    console.log('A. Cinq manches comptées, égalité, manches décisives deux par deux');
    let ready = await startMatch(p1, p2, GAME.full);
    check('la manche 1 publie une empreinte SHA-256 avant les choix', /^[0-9a-f]{64}$/.test(ready.seal || ''), ready);
    check('personne n’a encore choisi', ready.chosen && ready.chosen[1] === false && ready.chosen[2] === false, ready.chosen);
    check('aucune manche jouée, pas de paire décisive', ready.played === 0 && ready.decisiveStep === 0, ready);

    // Couleurs : 0 Rouge, 1 Orange, 2 Jaune, 3 Vert, 4 Bleu, 5 Violet (dans cet ordre sur la roue).
    const plan = [
      { c: [4, 0], winner: 1, scores: [1, 0], played: 1, label: 'Vert tiré : le Bleu d’Alice (1 case) bat le Rouge de Bob (3 cases)' },
      { c: [0, 2], winner: 0, scores: [1, 0], played: 2, label: 'Orange tiré : Rouge et Jaune à égale distance, manche nulle' },
      { c: [3, 3], winner: 0, scores: [1, 0], played: 2, repick: true, label: 'même couleur (Vert) : rien ne tourne, on rechoisit, la manche ne compte pas' },
      { c: [2, 0], winner: 2, scores: [1, 1], played: 3, label: 'Violet tiré : le Rouge de Bob (1 case, par le haut de la roue) bat le Jaune (3 cases)' },
      { c: [2, 1], winner: 1, scores: [2, 1], played: 4, label: 'Jaune tiré : pile sur la couleur d’Alice' },
      { c: [0, 5], winner: 2, scores: [2, 2], played: 5, label: 'Bleu tiré : le Violet de Bob (1 case) bat le Rouge (2 cases)' }
    ];
    for (let i = 0; i < plan.length; i++) {
      const round = i + 1;
      const step = plan[i];
      const spin = await playRound(p1, p2, GAME.full, round, step.c[0], step.c[1]);
      check(`manche ${round} : ${step.label}`, spin.winnerSlot === step.winner && JSON.stringify(spin.scores) === JSON.stringify(step.scores), spin);
      check(`manche ${round} : la révélation correspond à l’empreinte publiée`, sealOk(GAME.full, spin, ready.seal), { seal: spin.seal, published: ready.seal });
      if (step.repick) {
        check(`manche ${round} : rien n’est tiré, sans tour de roue`, spin.repick === true && spin.drawn === null && spin.duration === 0, spin);
      } else {
        check(`manche ${round} : la couleur tirée est la couleur scellée`, spin.drawn === DRAWS[GAME.full][i] && spin.seal.kind === 'color', spin.drawn);
        check(`manche ${round} : la roue a ses six couleurs et s’arrête sur la couleur tirée`,
          spin.wheel.length === 6 && spin.wheel[spin.landing.segment] === spin.drawn, spin.landing);
      }
      if (round < plan.length) {
        const result = await onceWhere(p1, 'roulette_round_result', d => d.room === GAME.full && d.round === round);
        check(`manche ${round} : résultat public après le tour de roue`, result.winnerSlot === step.winner && result.next === 'next' && result.repick === (step.repick === true), result);
        ready = await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.full && d.round === round + 1);
        check(`manche ${round + 1} : ${step.played} manche(s) comptée(s) avant elle`, ready.played === step.played && ready.decisive === false, ready);
      }
    }
    const tied = await onceWhere(p1, 'roulette_round_result', d => d.room === GAME.full && d.round === 6);
    check('2-2 après cinq manches comptées (six ouvertes) : manches décisives annoncées', tied.next === 'decisive', tied);

    // Paire 1 : Bob gagne la première… et Alice joue quand même la seconde, qu'elle gagne : 1-1.
    ready = await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.full && d.round === 7);
    check('manche 7 : première décisive de la paire', ready.decisive === true && ready.decisiveStep === 1, ready);
    const d1 = await playRound(p1, p2, GAME.full, 7, 1, 4);
    check('décisive : la roue ne garde que l’orange et le bleu, alternés', JSON.stringify(d1.wheel) === JSON.stringify([1, 4, 1, 4, 1, 4]), d1.wheel);
    check('décisive : le bit scellé 1 désigne la plus grande couleur (bleu) → Bob', d1.drawn === 4 && d1.winnerSlot === 2 && d1.seal.kind === 'bit' && JSON.stringify(d1.scores) === JSON.stringify([2, 3]), d1);
    check('décisive : la révélation correspond à l’empreinte', sealOk(GAME.full, d1, ready.seal));
    check('Bob a gagné la première décisive : le match n’est PAS fini, Alice répond', d1.final === false, d1);
    const r7 = await onceWhere(p1, 'roulette_round_result', d => d.room === GAME.full && d.round === 7);
    check('après la première décisive : encore une décisive', r7.next === 'decisive', r7);
    ready = await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.full && d.round === 8);
    check('manche 8 : la réponse (2e de la paire)', ready.decisive === true && ready.decisiveStep === 2, ready);
    const d2 = await playRound(p1, p2, GAME.full, 8, 0, 3);
    check('Alice égalise (rouge, bit 0) : 1-1 dans la paire, 3-3', d2.drawn === 0 && d2.winnerSlot === 1 && JSON.stringify(d2.scores) === JSON.stringify([3, 3]) && d2.final === false, d2);
    await onceWhere(p1, 'roulette_round_result', d => d.room === GAME.full && d.round === 8);

    // Paire 2 : un rechoix (ne compte pas), puis Alice gagne les deux : 2-0.
    ready = await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.full && d.round === 9);
    check('manche 9 : une nouvelle paire commence', ready.decisive === true && ready.decisiveStep === 1, ready);
    const d3 = await playRound(p1, p2, GAME.full, 9, 5, 5);
    check('décisive, même couleur : rien n’est tiré, on rechoisit', d3.repick === true && d3.drawn === null && d3.winnerSlot === 0 && d3.duration === 0 && d3.final === false, d3);
    ready = await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.full && d.round === 10);
    check('le rechoix ne compte pas : toujours la première de la paire', ready.decisive === true && ready.decisiveStep === 1, ready);
    const d4 = await playRound(p1, p2, GAME.full, 10, 2, 5);
    check('Alice gagne la première de la paire (jaune) : on attend la réponse de Bob', d4.drawn === 2 && d4.winnerSlot === 1 && d4.final === false, d4);
    ready = await onceWhere(p1, 'roulette_round_ready', d => d.room === GAME.full && d.round === 11);
    check('manche 11 : la réponse de Bob', ready.decisiveStep === 2, ready);
    const over = onceWhere(p1, 'game:over', d => d.room === GAME.full, 8000);
    const d5 = await playRound(p1, p2, GAME.full, 11, 4, 1);
    check('Bob ne répond pas (bleu d’Alice tiré) : 2-0 dans la paire, match joué', d5.drawn === 4 && d5.winnerSlot === 1 && d5.final === true && d5.matchWinnerSlot === 1, d5);
    const end = await over;
    check('fin du match : Alice gagne 5-3', end.winnerSlot === 1 && JSON.stringify(end.scores) === JSON.stringify([5, 3]), end);
    check('l’historique de fin garde les onze manches ouvertes (rechoix compris)', Array.isArray(end.history) && end.history.length === 11, end.history && end.history.length);
    await sleep(400);
    const settlementA = rpcCalls.find(call => call.name === 'submit_game_result' && call.payload?.p_game_id === GAME.full);
    check('règlement : Alice vainqueur, résultat « win »', settlementA && settlementA.payload.p_winner_id === PLAYER_1 && settlementA.payload.p_result === 'win', settlementA);
    const summaryA = rpcCalls.find(call => call.name === 'record_match_summary' && call.payload?.p_game_id === GAME.full);
    const logA = summaryA?.payload?.p_summary?.log?.e || [];
    check('résumé : 9 manches jouées (sans les deux rechoix), score 5-3', summaryA && summaryA.payload.p_summary.rounds === 9
      && summaryA.payload.p_summary.players[PLAYER_1].score === 5 && summaryA.payload.p_summary.players[PLAYER_2].score === 3, summaryA?.payload?.p_summary);
    check('journal : chaque couleur choisie (v) et tirée (t), manche (g) ; un rechoix sans couleur tirée',
      logA.length === 22 && logA[0].p === 1 && logA[0].g === 1 && logA[0].v === '4' && logA[0].t === 3
      && logA[1].p === 2 && logA[1].v === '0' && logA.filter(e => e.g === 3 || e.g === 9).every(e => e.t === undefined), logA.slice(0, 4));

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
