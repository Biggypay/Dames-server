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
    "function gomokuSnapshot(groom) {\n  const state = groom.gameState || gomokuInitialState();\n  const gameState = {\n    board:",
    "function gomokuSnapshot(groom) {\n  const state = groom.gameState || gomokuInitialState();\n  const gameState = {\n    series: seriesPayload(groom),\n    board:",
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
    `.rounds-progress{display:flex;gap:6px;margin-top:5px;align-items:center;justify-content:center}\n.round-dot{width:30px;height:6px;border-radius:3px;background:rgba(255,255,255,0.08);transition:all .3s ease}\n.round-dot.played{background:rgba(255,255,255,0.2)}\n.round-dot.win{background:#22c55e}\n.round-dot.lose{background:#ef4444}\n.round-dot.draw{background:#fbbf24}\n.round-dot.current{background:rgba(255,255,255,0.4);box-shadow:0 0 8px rgba(255,255,255,0.5)}\n\n/* ── CANVAS ── */`,
    'round progress styles'
  );

  html = replaceOnce(
    html,
    `    <div class="sub">ALIGNEZ CINQ PIONS</div>\n    <div class="bet-badge" id="betBadge"></div>`,
    `    <div class="sub">ALIGNEZ CINQ PIONS</div>\n    <div class="rounds-progress" id="roundsProgress"></div>\n    <div class="bet-badge" id="betBadge"></div>`,
    'round progress markup'
  );

  html = replaceOnce(
    html,
    "var board, currentSlot, lastMove, winLine;\nvar gameOver = false, gameReady = false, resultSent = false;",
    `var board, currentSlot, lastMove, winLine;\nvar seriesState = { regularRounds: 6, roundsPlayed: 0, currentRound: 1, wins: {1:0,2:0}, draws: 0, history: [], suddenDeath: false };\nfunction updateSeriesUI(next) {\n  if (next && typeof next === 'object') seriesState = next;\n  var el = document.getElementById('roundsProgress');\n  if (!el) return;\n  var total = 6;\n  var history = Array.isArray(seriesState.history) ? seriesState.history : [];\n  var played = Math.min(total, Number(seriesState.roundsPlayed) || 0);\n  el.innerHTML = '';\n  for (var i = 0; i < total; i++) {\n    var bar = document.createElement('span');\n    bar.className = 'round-dot';\n    if (i < played) {\n      var result = history[i];\n      if (result === MY_SLOT) bar.className += ' win';\n      else if (result === 0) bar.className += ' draw';\n      else if (result === 1 || result === 2) bar.className += ' lose';\n      else bar.className += ' played';\n    } else if (i === played && played < total && !seriesState.suddenDeath) {\n      bar.className += ' current';\n    }\n    el.appendChild(bar);\n  }\n}\nvar gameOver = false, gameReady = false, resultSent = false;`,
    'series client state'
  );

  html = replaceOnce(
    html,
    "socket.on('gomoku_start', function (data) {\n    document.getElementById('waiting-overlay').classList.add('hidden');",
    "socket.on('gomoku_start', function (data) {\n    document.getElementById('waiting-overlay').classList.add('hidden');\n    if (data && (data.yourSlot === 1 || data.yourSlot === 2)) MY_SLOT = data.yourSlot;\n    if (data && data.series) updateSeriesUI(data.series); else updateSeriesUI(seriesState);",
    'authoritative player slot and series sync'
  );

  html = replaceOnce(
    html,
    "socket.on('gomoku_move', function (data) {",
    `socket.on('gomoku_round_end', function (data) {\n    if (!data) return;\n    if (data.series) updateSeriesUI(data.series);\n    gameReady = false;\n    stopTimer(); stopGraceTimer();\n    var mineWon = data.roundWinner === MY_SLOT;\n    var drawn = !data.roundWinner;\n    var title = drawn ? 'Manche nulle' : (mineWon ? 'Manche gagnée' : 'Manche perdue');\n    var score = seriesState.wins || {1:0,2:0};\n    var sub = 'Score : ' + (Number(score[MY_SLOT]) || 0) + ' — ' + (Number(score[MY_SLOT === 1 ? 2 : 1]) || 0);\n    showToast(drawn ? '🤝' : (mineWon ? '🏆' : '🎯'), title, sub, 1700);\n  });\n\n  socket.on('gomoku_round_start', function (data) {\n    if (!data || gameOver) return;\n    if (data.series) updateSeriesUI(data.series);\n    var st = data.gameState;\n    if (typeof st === 'string') { try { st = JSON.parse(st); } catch (e) { st = null; } }\n    winLine = null;\n    if (st) applyServerState(st, typeof data.version === 'number' ? data.version : null, true);\n    gameReady = true;\n    updUI(); draw();\n  });\n\n  socket.on('gomoku_move', function (data) {`,
    'round event handlers'
  );

  html = replaceOnce(
    html,
    "socket.on('gomoku_state_sync', function (data) {\n    if (!data || gameOver) return;",
    "socket.on('gomoku_state_sync', function (data) {\n    if (!data || gameOver) return;\n    if (data.series) updateSeriesUI(data.series);\n    else if (data.gameState && data.gameState.series) updateSeriesUI(data.gameState.series);",
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
