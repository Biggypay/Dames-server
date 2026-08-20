'use strict';

const fs = require('fs');
const path = require('path');
const Module = require('module');

const ROOT = path.join(__dirname, '..');
const SERVER_FILE = path.join(ROOT, 'server.js');
const PUBLIC_SRC = path.join(ROOT, 'public');
const PUBLIC_RUNTIME = path.join(ROOT, '.runtime-public');

function replaceOnce(source, needle, replacement, label) {
  const index = source.indexOf(needle);
  if (index === -1) throw new Error(`Gomoku series patch failed: ${label}`);
  if (source.indexOf(needle, index + needle.length) !== -1) {
    throw new Error(`Gomoku series patch ambiguous: ${label}`);
  }
  return source.slice(0, index) + replacement + source.slice(index + needle.length);
}

function patchServer(raw) {
  let source = raw.replace(/\r\n/g, '\n');

  source = replaceOnce(
    source,
    "const PUBLIC = path.join(__dirname, 'public');",
    "const PUBLIC = path.join(__dirname, '.runtime-public');",
    'runtime public directory'
  );

  source = replaceOnce(
    source,
    "const crypto     = require('crypto');",
    "const crypto     = require('crypto');\nconst { ensureSeriesState, seriesPayload, recordRoundResult, advanceRoundStarter } = require('./lib/gomoku-series');",
    'series module import'
  );

  source = replaceOnce(
    source,
    "groom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: gomokuInitialState(), currentSlot: 1, stateVersion: 0, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null };",
    "groom = { id: room, players: {}, status: 'waiting', betAmount: bet || 0, currency: currency || 'HTG', disconnectTimer: null, gameState: gomokuInitialState(), currentSlot: 1, stateVersion: 0, turnTimer: null, graceTimer: null, turnStartTime: null, graceStartTime: null, turnPlayer: null };\n      ensureSeriesState(groom);",
    'room series initialization'
  );

  source = replaceOnce(
    source,
    "groom.currentSlot = randomOpeningSlot();\n      groom.gameState.currentSlot = groom.currentSlot;",
    "groom.currentSlot = randomOpeningSlot();\n      ensureSeriesState(groom).roundStarter = groom.currentSlot;\n      groom.gameState.currentSlot = groom.currentSlot;",
    'opening round starter'
  );

  source = replaceOnce(
    source,
    "const gameState = {\n    board:",
    "const gameState = {\n    series: seriesPayload(groom),\n    board:",
    'snapshot series payload'
  );

  const finishRoundFunction = `function finishGomokuRound(groom, roomId, winnerSlot, reason = 'normal') {\n  if (!groom || groom.status !== 'playing') return;\n  clearGomokuTurnTimers(groom);\n  groom.status = 'round_break';\n\n  const summary = recordRoundResult(groom, winnerSlot);\n  const payload = {\n    room: roomId,\n    roundWinner: summary.roundWinner,\n    reason,\n    series: summary.series,\n    serverTime: Date.now()\n  };\n  io.to(roomId).emit('gomoku_round_end', payload);\n  persistRoomSoon('gomoku', groom);\n\n  if (summary.matchOver) {\n    return setTimeout(() => {\n      notifyGomokuRoomOver(groom, roomId, summary.matchWinner, reason);\n    }, 1600);\n  }\n\n  setTimeout(() => {\n    if (!groom || groom.status !== 'round_break') return;\n    const starter = advanceRoundStarter(groom);\n    groom.gameState = gomokuInitialState();\n    groom.currentSlot = starter;\n    groom.gameState.currentSlot = starter;\n    groom.gameState.slotSymbols = starter === 1 ? { 1: 'X', 2: 'O' } : { 1: 'O', 2: 'X' };\n    groom.stateVersion = Math.max(0, Number(groom.stateVersion) || 0) + 1;\n    groom.status = 'playing';\n    const nextPayload = {\n      room: roomId,\n      currentSlot: groom.currentSlot,\n      gameState: JSON.stringify(groom.gameState),\n      version: groom.stateVersion,\n      series: seriesPayload(groom),\n      serverTime: Date.now()\n    };\n    io.to(roomId).emit('gomoku_round_start', nextPayload);\n    io.to(roomId).emit('gomoku_state_sync', gomokuSnapshot(groom));\n    persistRoomSoon('gomoku', groom);\n    startGomokuTurnTimer(groom, roomId, groom.currentSlot);\n  }, 2200);\n}\n\n`;

  source = replaceOnce(
    source,
    "function notifyGomokuRoomOver(groom, roomId, winnerSlot, reason = 'normal') {",
    finishRoundFunction + "function notifyGomokuRoomOver(groom, roomId, winnerSlot, reason = 'normal') {",
    'round finalizer insertion'
  );

  source = replaceOnce(
    source,
    "if (winLine) return notifyGomokuRoomOver(groom, room, player, 'normal');\n    if (boardFull) return notifyGomokuRoomOver(groom, room, 0, 'draw');",
    "if (winLine) return finishGomokuRound(groom, room, player, 'normal');\n    if (boardFull) return finishGomokuRound(groom, room, 0, 'draw');",
    'move result routing'
  );

  return source;
}

function patchGomokuHtml(raw) {
  let html = raw.replace(/\r\n/g, '\n');

  html = replaceOnce(
    html,
    '/* ── CANVAS ── */',
    `.series-score{flex:0 0 auto;display:flex;align-items:center;justify-content:center;gap:9px;margin:0 auto 2px;padding:5px 12px;border:1px solid rgba(251,191,36,.28);border-radius:999px;background:rgba(15,23,42,.34);font-family:'Inter',sans-serif;font-size:10px;color:#fff;letter-spacing:.4px}\n.series-score strong{color:#fbbf24;font-size:12px}.series-score .sep{opacity:.45}.series-score .round{opacity:.7}\n\n/* ── CANVAS ── */`,
    'series score styles'
  );

  html = replaceOnce(
    html,
    '</div>\n\n<div id="canvasWrap">',
    `</div>\n<div class="series-score" id="seriesScore"><span>0</span><span class="sep">—</span><span>0</span><span class="round">Manche 1/6</span></div>\n\n<div id="canvasWrap">`,
    'series score markup'
  );

  html = replaceOnce(
    html,
    "var board, currentSlot, lastMove, winLine;\nvar gameOver = false, gameReady = false, resultSent = false;",
    `var board, currentSlot, lastMove, winLine;\nvar seriesState = { regularRounds: 6, roundsPlayed: 0, currentRound: 1, wins: {1:0,2:0}, draws: 0, suddenDeath: false };\nfunction updateSeriesUI(next) {\n  if (next && typeof next === 'object') seriesState = next;\n  var el = document.getElementById('seriesScore');\n  if (!el) return;\n  var wins = seriesState.wins || {1:0,2:0};\n  var mine = Number(wins[MY_SLOT]) || 0;\n  var theirs = Number(wins[MY_SLOT === 1 ? 2 : 1]) || 0;\n  var label = seriesState.suddenDeath ? ('Mort subite · manche ' + (seriesState.currentRound || 7)) : ('Manche ' + (seriesState.currentRound || 1) + '/' + (seriesState.regularRounds || 6));\n  el.innerHTML = '<strong>' + mine + '</strong><span class="sep">—</span><strong>' + theirs + '</strong><span class="round">' + label + '</span>';\n}\nvar gameOver = false, gameReady = false, resultSent = false;`,
    'series client state'
  );

  html = replaceOnce(
    html,
    "socket.on('gomoku_start', function (data) {\n    document.getElementById('waiting-overlay').classList.add('hidden');",
    "socket.on('gomoku_start', function (data) {\n    document.getElementById('waiting-overlay').classList.add('hidden');\n    if (data && data.series) updateSeriesUI(data.series);",
    'start series sync'
  );

  html = replaceOnce(
    html,
    "socket.on('gomoku_move', function (data) {",
    `socket.on('gomoku_round_end', function (data) {\n    if (!data) return;\n    if (data.series) updateSeriesUI(data.series);\n    gameReady = false;\n    stopTimer(); stopGraceTimer();\n    var mineWon = data.roundWinner === MY_SLOT;\n    var drawn = !data.roundWinner;\n    var title = drawn ? 'Manche nulle' : (mineWon ? 'Manche gagnée' : 'Manche perdue');\n    var score = seriesState.wins || {1:0,2:0};\n    var sub = 'Score : ' + (Number(score[MY_SLOT]) || 0) + ' — ' + (Number(score[MY_SLOT === 1 ? 2 : 1]) || 0);\n    if (!data.series || !data.series.suddenDeath) sub += '\\nProchaine manche dans un instant';\n    showToast(drawn ? '🤝' : (mineWon ? '🏆' : '🎯'), title, sub, 1700);\n  });\n\n  socket.on('gomoku_round_start', function (data) {\n    if (!data || gameOver) return;\n    if (data.series) updateSeriesUI(data.series);\n    var st = data.gameState;\n    if (typeof st === 'string') { try { st = JSON.parse(st); } catch (e) { st = null; } }\n    winLine = null;\n    if (st) applyServerState(st, typeof data.version === 'number' ? data.version : null, true);\n    gameReady = true;\n    updUI(); draw();\n  });\n\n  socket.on('gomoku_move', function (data) {`,
    'round event handlers'
  );

  html = replaceOnce(
    html,
    "socket.on('gomoku_state_sync', function (data) {\n    if (!data || gameOver) return;",
    "socket.on('gomoku_state_sync', function (data) {\n    if (!data || gameOver) return;\n    if (data.series) updateSeriesUI(data.series);",
    'state series sync'
  );

  return html;
}

fs.rmSync(PUBLIC_RUNTIME, { recursive: true, force: true });
fs.cpSync(PUBLIC_SRC, PUBLIC_RUNTIME, { recursive: true });

const gomokuFile = path.join(PUBLIC_RUNTIME, 'gomoku-online.html');
fs.writeFileSync(gomokuFile, patchGomokuHtml(fs.readFileSync(gomokuFile, 'utf8')), 'utf8');

const patchedServer = patchServer(fs.readFileSync(SERVER_FILE, 'utf8'));
const runtimeServer = path.join(ROOT, '.runtime-server.js');
fs.writeFileSync(runtimeServer, patchedServer, 'utf8');

const runtimeModule = new Module(runtimeServer, module);
runtimeModule.filename = runtimeServer;
runtimeModule.paths = Module._nodeModulePaths(ROOT);
runtimeModule._compile(patchedServer, runtimeServer);
