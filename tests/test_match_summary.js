'use strict';

// Le résumé de match envoyé à l'application pour la carte publique d'un match
// (page joueur) : coups joués par chacun, score, manches.
//
//  1. La logique pure (lib/match-summary.js) : compteur, score par jeu, ids.
//  2. Chaque gestionnaire de coup du serveur compte le coup ACCEPTÉ.
//  3. Le vrai serveur, contre une base simulée : un mat de l'imbécile aux
//     échecs (2 coups chacun) et une défaite au temps aux dames (1 coup contre
//     0). Le résumé part APRÈS le règlement, et un échec de son envoi ne
//     touche pas le règlement.

const { spawn } = require('child_process');
const fs = require('fs');
const http = require('http');
const path = require('path');
const crypto = require('crypto');
const { io } = require('socket.io-client');
const { countMove, buildMatchSummary } = require('../lib/match-summary.js');

const ROOT = path.join(__dirname, '..');
const GAME_PORT = 3222;
const DB_PORT = 3223;
const GAME_URL = `http://127.0.0.1:${GAME_PORT}`;

let failures = 0;
function check(label, condition, detail) {
  if (condition) console.log(`  OK ${label}`);
  else { failures++; console.error(`  FAIL ${label}`, detail === undefined ? '' : JSON.stringify(detail)); }
}
const sleep = ms => new Promise(resolve => setTimeout(resolve, ms));
const A = '11111111-1111-4111-8111-111111111111';
const B = '22222222-2222-4222-8222-222222222222';

// ── 1. Logique pure ──────────────────────────────────────────────────────────
console.log('\n— Logique pure —');
{
  const room = { players: { 1: { supabaseId: A }, 2: { supabaseId: B } } };
  countMove(room, 1); countMove(room, 2); countMove(room, 1);
  countMove(room, 3); countMove(null, 1);
  check('le compteur compte par place et ignore une place invalide', room.movesPlayed[1] === 2 && room.movesPlayed[2] === 1, room.movesPlayed);
  const summary = buildMatchSummary('dames', room, 'checkmate');
  check('dames : coups par joueur (id Supabase), total, raison, pas de score',
    JSON.stringify(summary) === JSON.stringify({ players: { [A]: { moves: 2 }, [B]: { moves: 1 } }, moves_total: 3, reason: 'checkmate' }), summary);
}
{
  const room = { players: { 1: { supabaseId: A }, 2: { supabaseId: B } }, gameState: { matchW: 3, matchR: 1, manchesDone: 4 }, movesPlayed: { 1: 9, 2: 8 } };
  const summary = buildMatchSummary('tictactoe', room, 'normal');
  check('tic-tac-toe : manches gagnées comme score, manches jouées',
    summary.players[A].score === 3 && summary.players[B].score === 1 && summary.rounds === 4 && summary.moves_total === 17, summary);
}
{
  const room = { players: { 1: { supabaseId: A }, 2: { supabaseId: B } }, series: { wins: { 1: 1, 2: 4 }, roundsPlayed: 6 } };
  const summary = buildMatchSummary('gomoku', room, 'normal');
  check('morpion à 5 : victoires de la série, manches jouées, 0 coup compté',
    summary.players[A].score === 1 && summary.players[B].score === 4 && summary.rounds === 6 && summary.moves_total === 0, summary);
}
{
  const room = { players: { 1: { supabaseId: A }, 2: { supabaseId: B } }, scores: { p1: 4, p2: 3 }, movesPlayed: { 1: 10, 2: 9 } };
  const summary = buildMatchSummary('penalty', room, 'normal');
  check('penalty : buts, et une manche = un tir où les deux ont choisi',
    summary.players[A].score === 4 && summary.players[B].score === 3 && summary.rounds === 9, summary);
}
{
  const room = { players: { 1: { supabaseId: A }, 2: { supabaseId: B } }, scores: [2, 3], history: [1, 2, 0, 2, 1, 2], movesPlayed: { 1: 6, 2: 6 } };
  const summary = buildMatchSummary('chifoumi', room, 'normal');
  check('chifoumi : manches gagnées, manches jouées',
    summary.players[A].score === 2 && summary.players[B].score === 3 && summary.rounds === 6, summary);
}
{
  check('sans deux joueurs identifiés, aucun résumé',
    buildMatchSummary('dames', { players: { 1: { supabaseId: A }, 2: { supabaseId: 'bob' } } }, 'x') === null
    && buildMatchSummary('dames', { players: { 1: { supabaseId: A }, 2: { supabaseId: A } } }, 'x') === null
    && buildMatchSummary('dames', null, 'x') === null);
  const summary = buildMatchSummary('echecs', { players: { 1: { supabaseId: A }, 2: { supabaseId: B } } }, 'Time-Out<script>');
  check('la raison est réduite à [a-z_]', summary.reason === 'timeoutscript', summary.reason);
  check('ludo (hors ligne) : ni coups ni score',
    JSON.stringify(buildMatchSummary('ludo', { players: { 1: { supabaseId: A }, 2: { supabaseId: B } } }, 'normal'))
      === JSON.stringify({ players: { [A]: {}, [B]: {} }, reason: 'normal' }));
}

// ── 2. Chaque gestionnaire de coup compte ────────────────────────────────────
console.log('\n— Les gestionnaires de coup —');
{
  const source = fs.readFileSync(path.join(ROOT, 'server.js'), 'utf8');
  const handlers = ['dames_move', 'echecs_move', 'ttt_move', 'quoridor_move', 'gomoku_move', 'penalty_choice', 'chifoumi_choice'];
  for (const name of handlers) {
    const start = source.indexOf(`socket.on('${name}'`);
    const next = source.indexOf('socket.on(', start + 10);
    const body = source.slice(start, next);
    check(`${name} compte le coup accepté`, start > 0 && (body.match(/MatchSummary\.countMove\(/g) || []).length === 1);
  }
  check('le résumé part après le règlement confirmé',
    /room\.pendingSettlement = null;\s*\n\s*sendMatchSummary\(room, game, reason\);/.test(source));
}

// ── 3. Le vrai serveur ───────────────────────────────────────────────────────
const games = new Map();
const summaries = [];
const order = [];
let failSummary = false;
function mockDatabase() {
  return http.createServer((request, response) => {
    let body = '';
    request.on('data', chunk => { body += chunk; });
    request.on('end', () => {
      const url = new URL(request.url, `http://127.0.0.1:${DB_PORT}`);
      response.setHeader('Content-Type', 'application/json');
      if (request.method === 'GET' && url.pathname === '/rest/v1/games') {
        const row = games.get(String(url.searchParams.get('id') || '').replace(/^eq\./, ''));
        return response.end(JSON.stringify(row ? [row] : []));
      }
      if (url.pathname.endsWith('/submit_game_result')) {
        const payload = JSON.parse(body || '{}');
        const row = games.get(payload.p_game_id);
        if (row) Object.assign(row, { status: 'completed', result: payload.p_result, winner_id: payload.p_winner_id });
        order.push('settle:' + payload.p_game_id);
        return response.end('null');
      }
      if (url.pathname.endsWith('/record_match_summary')) {
        const payload = JSON.parse(body || '{}');
        order.push('summary:' + payload.p_game_id);
        summaries.push(payload);
        if (failSummary) { response.statusCode = 500; return response.end('{"message":"boom"}'); }
        return response.end(JSON.stringify(payload.p_summary));
      }
      if (url.pathname.startsWith('/rest/v1/rpc/')) return response.end('null');
      response.statusCode = 404;
      response.end('{}');
    });
  });
}

let serverLog = '';
function startServer() {
  const server = spawn(process.execPath, ['server.js'], {
    cwd: ROOT,
    env: {
      ...process.env,
      PORT: String(GAME_PORT), NODE_ENV: 'test',
      JWT_SECRET: 'test-only-secret-with-more-than-32-characters',
      SUPABASE_URL: `http://127.0.0.1:${DB_PORT}`,
      SUPABASE_SERVICE_ROLE_KEY: 'test-service-role',
      ALLOWED_ORIGIN: 'https://mindspille.lovable.app',
      TURN_DURATION_MS: '500',
      GRACE_DURATION_MS: '700'
    },
    stdio: ['ignore', 'pipe', 'pipe']
  });
  server.stdout.on('data', chunk => { serverLog += chunk; });
  server.stderr.on('data', chunk => { serverLog += chunk; });
  return server;
}
async function health() {
  for (let i = 0; i < 50; i++) {
    const ok = await new Promise(resolve => {
      http.get(`${GAME_URL}/health`, response => { response.resume(); resolve(response.statusCode === 200); })
        .on('error', () => resolve(false));
    });
    if (ok) return;
    await sleep(200);
  }
  throw new Error('server unavailable');
}

let addressCounter = 0;
async function connectAs(userId, name) {
  addressCounter++;
  const socket = io(GAME_URL, {
    transports: ['websocket'], reconnection: false, forceNew: true,
    extraHeaders: { 'x-forwarded-for': `10.88.0.${addressCounter}` }
  });
  socket.events = [];
  socket.onAny((event, data) => socket.events.push({ event, data }));
  await new Promise((resolve, reject) => { socket.once('connect', resolve); socket.once('connect_error', reject); });
  socket.emit('auth:supabase', { supabaseId: userId, username: name });
  await waitFor(socket, 'auth:ok');
  return socket;
}
function waitFor(socket, event, timeout = 6000) {
  return new Promise((resolve, reject) => {
    const seen = socket.events.find(entry => entry.event === event);
    if (seen) return resolve(seen.data);
    const listener = (name, data) => {
      if (name !== event) return;
      clearTimeout(timer); socket.offAny(listener); resolve(data);
    };
    const timer = setTimeout(() => { socket.offAny(listener); reject(new Error('timeout ' + event)); }, timeout);
    socket.onAny(listener);
  });
}
async function waitUntil(predicate, timeout = 5000) {
  const until = Date.now() + timeout;
  while (Date.now() < until) { if (predicate()) return true; await sleep(50); }
  return false;
}

async function startMatch(gameName, dbType, joinEvent) {
  const id = crypto.randomUUID();
  const users = { 1: crypto.randomUUID(), 2: crypto.randomUUID() };
  games.set(id, { id, game_type: dbType, player1_id: users[1], player2_id: users[2], bet_amount: 0,
    status: 'in_progress', is_ai_opponent: false, is_tournament: false, game_settings: {} });
  const sockets = {};
  for (const slot of [1, 2]) {
    sockets[slot] = await connectAs(users[slot], 'Joueur ' + slot);
    sockets[slot].emit(joinEvent, { room: id, player: slot, supabaseId: users[slot], name: 'Joueur ' + slot, bet: 0, currency: 'HTG', gameId: id });
  }
  return { id, users, sockets };
}

const sq = alg => ({ row: 8 - parseInt(alg[1], 10), col: 'abcdefgh'.indexOf(alg[0]) });

async function foolsMate() {
  console.log('\n— Échecs : mat de l\'imbécile —');
  const match = await startMatch('echecs', 'chess', 'echecs_join');
  await waitFor(match.sockets[1], 'echecs_start');
  await waitFor(match.sockets[2], 'echecs_start');
  const moves = [[1, 'f2', 'f3'], [2, 'e7', 'e5'], [1, 'g2', 'g4'], [2, 'd8', 'h4']];
  for (const [slot, from, to] of moves) {
    const other = match.sockets[slot === 1 ? 2 : 1];
    const seen = other.events.filter(e => e.event === 'echecs_move').length;
    match.sockets[slot].emit('echecs_move', { room: match.id, player: slot, from: sq(from), to: sq(to), promo: 0 });
    await waitUntil(() => other.events.filter(e => e.event === 'echecs_move').length > seen || other.events.some(e => e.event === 'game:over'));
  }
  // Un coup refusé (partie finie) ne compte pas.
  match.sockets[1].emit('echecs_move', { room: match.id, player: 1, from: sq('a2'), to: sq('a3'), promo: 0 });
  const arrived = await waitUntil(() => summaries.some(s => s.p_game_id === match.id));
  const sent = summaries.find(s => s.p_game_id === match.id);
  check('le résumé est envoyé', arrived, serverLog.slice(-800));
  if (sent) {
    const s = sent.p_summary;
    check('2 coups chacun, 4 au total, raison « checkmate »',
      s.players[match.users[1]].moves === 2 && s.players[match.users[2]].moves === 2 && s.moves_total === 4 && s.reason === 'checkmate', s);
    check('le règlement passe AVANT le résumé',
      order.indexOf('settle:' + match.id) >= 0 && order.indexOf('settle:' + match.id) < order.indexOf('summary:' + match.id), order);
  }
  for (const socket of Object.values(match.sockets)) socket.disconnect();
}

async function damesTimeout() {
  console.log('\n— Dames : un coup, puis le temps —');
  failSummary = true;                      // la base refuse le résumé
  const match = await startMatch('dames', 'checkers', 'dames_join');
  await waitFor(match.sockets[1], 'dames_start');
  const first = await waitFor(match.sockets[1], 'dames_turn_start');
  const mover = first.player === 2 ? 2 : 1;
  const steps = mover === 1 ? [{ from: { row: 6, col: 1 }, to: { row: 5, col: 2 } }] : [{ from: { row: 3, col: 0 }, to: { row: 4, col: 1 } }];
  match.sockets[mover].emit('dames_move', { room: match.id, player: mover, steps });
  const over = await waitFor(match.sockets[mover], 'game:over', 6000).catch(() => null);
  check('l autre perd au temps', over && over.reason === 'timeout' && over.result === 'win', over);
  const arrived = await waitUntil(() => summaries.some(s => s.p_game_id === match.id));
  const sent = summaries.find(s => s.p_game_id === match.id);
  check('le résumé est envoyé', arrived);
  if (sent) {
    const s = sent.p_summary;
    const idle = mover === 1 ? 2 : 1;
    check('1 coup contre 0, raison « timeout »',
      s.players[match.users[mover]].moves === 1 && s.players[match.users[idle]].moves === 0 && s.moves_total === 1 && s.reason === 'timeout', s);
  }
  await sleep(300);
  check('un résumé refusé ne touche pas le règlement', games.get(match.id).status === 'completed'
    && !/settlement\] failed/.test(serverLog) && /\[summary\] résumé non transmis/.test(serverLog));
  failSummary = false;
  for (const socket of Object.values(match.sockets)) socket.disconnect();
}

(async () => {
  const db = mockDatabase();
  await new Promise(resolve => db.listen(DB_PORT, '127.0.0.1', resolve));
  const server = startServer();
  try {
    await health();
    await foolsMate();
    await damesTimeout();
  } catch (error) {
    failures++;
    console.error('  FAIL', error.message, serverLog.slice(-1500));
  } finally {
    await new Promise(resolve => { server.once('exit', resolve); server.kill('SIGTERM'); });
    db.close();
  }
  console.log(failures ? `\n${failures} échec(s)` : '\nTous les tests du résumé de match passent');
  process.exit(failures ? 1 : 0);
})();
