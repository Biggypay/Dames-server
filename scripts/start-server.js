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
  if (index === -1) throw new Error(`Runtime patch failed: ${label}`);
  if (source.indexOf(needle, index + needle.length) !== -1) {
    throw new Error(`Runtime patch ambiguous: ${label}`);
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
    "const { ChessEngineFactory } = require('./public/echecs-engine.js');",
    "const { ChessEngineFactory } = require('./lib/chess-competition-engine.js');",
    'competition chess engine'
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

  source = replaceOnce(
    source,
    "  socket.on('echecs_result', (data) => {\n    if (!data || !validRoom(data.room)) return;\n    // Résultat d'affichage uniquement : seul le moteur autoritatif du serveur\n    // peut terminer un match d'échecs (mat, pat, nulle, temps, abandon).\n  });",
    `  socket.on('echecs_claim_draw', ({ room, player } = {}) => {\n    if (!validRoom(room) || !validPlayerSlot(player)) return;\n    const eroom = echecsRooms.get(room);\n    if (!eroom || eroom.status !== 'playing' || eroom.players[player]?.socketId !== socket.id) return;\n    if (eroom.currentPlayer !== player - 1) {\n      rejectSocket(socket, 'La nulle ne peut être réclamée que lorsque vous avez le trait.');\n      return void socket.emit('echecs_state_sync', echecsSnapshot(eroom));\n    }\n    const state = ensureEchecsEngineState(eroom);\n    const status = ChessEngine.gameStatus(state);\n    if (!status.claimable) {\n      rejectSocket(socket, 'Aucune nulle FIDE ne peut être réclamée dans cette position.');\n      return void socket.emit('echecs_state_sync', echecsSnapshot(eroom));\n    }\n    eroom.endDetail = status.claimable;\n    io.to(room).emit('echecs_draw_claimed', { room, player, reason: status.claimable, serverTime: Date.now() });\n    return notifyEchecsRoomOver(eroom, room, 0, 'draw');\n  });\n\n  socket.on('echecs_result', (data) => {\n    if (!data || !validRoom(data.room)) return;\n    // Résultat d'affichage uniquement : seul le moteur autoritatif du serveur\n    // peut terminer un match d'échecs (mat, pat, nulle, temps, abandon).\n  });`,
    'FIDE draw claim handler'
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

function patchChessEngineRuntime(raw) {
  const source = raw.replace(/\r\n/g, '\n');
  return source + `\n\n/* Competition draw-rule facade injected at runtime. */\n(function(){\n  var BaseFactory = ChessEngineFactory;\n  ChessEngineFactory = function(){\n    var base = BaseFactory();\n    function normalize(next, light){\n      if(!next || next.ep < 0) return next;\n      var hasLegalEp = base.legalMoves(next).some(function(m){ return m && m.ep === true; });\n      if(hasLegalEp) return next;\n      var oldKey = next.key;\n      next.ep = -1;\n      next.key = base.positionKey(next);\n      if(!light && next.reps && oldKey !== next.key){\n        var reps = {}, k; for(k in next.reps) reps[k] = next.reps[k];\n        if(reps[oldKey]){ reps[oldKey]--; if(reps[oldKey] <= 0) delete reps[oldKey]; }\n        reps[next.key] = (reps[next.key] || 0) + 1;\n        next.reps = reps;\n      }\n      return next;\n    }\n    function applyMove(s,mv,light){ return normalize(base.applyMove(s,mv,light), !!light); }\n    function claimableDraw(s){\n      if(!s) return null;\n      var reps = s.reps && s.key ? Number(s.reps[s.key] || 0) : 0;\n      if(Number(s.h || 0) >= 100) return 'fifty';\n      if(reps >= 3) return 'repetition';\n      return null;\n    }\n    function gameStatus(s,moves){\n      moves = moves || base.legalMoves(s);\n      if(moves.length === 0){\n        if(base.inCheck(s,s.t)) return {over:true,winner:1-s.t,reason:'checkmate',claimable:null};\n        return {over:true,winner:null,reason:'stalemate',claimable:null};\n      }\n      var reps = s.reps && s.key ? Number(s.reps[s.key] || 0) : 0;\n      if(Number(s.h || 0) >= 150) return {over:true,winner:null,reason:'seventyfive',claimable:null};\n      if(reps >= 5) return {over:true,winner:null,reason:'fivefold',claimable:null};\n      if(base.insufficientMaterial(s.b)) return {over:true,winner:null,reason:'insufficient',claimable:null};\n      return {over:false,winner:null,reason:null,claimable:claimableDraw(s)};\n    }\n    return Object.assign({}, base, {applyMove:applyMove, gameStatus:gameStatus, claimableDraw:claimableDraw});\n  };\n})();\n`;
}

function patchEchecsHtml(raw) {
  let html = raw.replace(/\r\n/g, '\n');

  html = replaceOnce(
    html,
    `  <div class="btns">\n    <button class="btn" id="btn-cam">⟳ Auto</button>\n  </div>`,
    `  <div class="btns">\n    <button class="btn" id="btn-claim-draw" style="display:none" title="Réclamer une nulle FIDE">½ Nulle</button>\n    <button class="btn" id="btn-cam">⟳ Auto</button>\n  </div>`,
    'chess draw claim button'
  );

  html = replaceOnce(
    html,
    "var pendingPromotion = null;        // {fromIdx, toIdx} en attente du choix ♛♜♝♞",
    "var pendingPromotion = null;        // {fromIdx, toIdx} en attente du choix ♛♜♝♞\nvar pendingDrawReason = null;",
    'chess draw state'
  );

  html = replaceOnce(
    html,
    "  socket.on('game:over', function(d){\n    if(gameOver) return; hideLoading(); stopForfeitCountdown();",
    "  socket.on('echecs_draw_claimed', function(d){\n    if(d && d.reason) pendingDrawReason = d.reason;\n  });\n\n  socket.on('game:over', function(d){\n    if(gameOver) return; hideLoading(); stopForfeitCountdown();",
    'chess draw claim event'
  );

  html = replaceOnce(
    html,
    "      handleGameEnd(-1, d.reason || 'draw');",
    "      handleGameEnd(-1, pendingDrawReason || d.reason || 'draw');",
    'claimed draw reason on game over'
  );

  html = replaceOnce(
    html,
    "  if(reason === 'fifty') return 'Règle des 50 coups.';\n  if(reason === 'repetition') return 'Triple répétition de la position.';\n  if(reason === 'insufficient') return 'Matériel insuffisant pour mater.';",
    "  if(reason === 'fifty') return 'Nulle réclamée — règle des 50 coups.';\n  if(reason === 'repetition') return 'Nulle réclamée — triple répétition.';\n  if(reason === 'seventyfive') return 'Nulle automatique — règle des 75 coups.';\n  if(reason === 'fivefold') return 'Nulle automatique — cinq répétitions.';\n  if(reason === 'insufficient') return 'Matériel insuffisant pour mater.';",
    'FIDE draw labels'
  );

  html = replaceOnce(
    html,
    "  updateScores();\n  updateCheckDisplay();\n}",
    `  updateScores();\n  updateCheckDisplay();\n  var claimBtn = document.getElementById('btn-claim-draw');\n  if(claimBtn){\n    var st = (!IS_SPECTATOR && gameReady && !gameOver) ? Chess.gameStatus(S) : null;\n    var canClaim = !!(st && !st.over && st.claimable && S.t === MY_PLAYER);\n    claimBtn.style.display = canClaim ? '' : 'none';\n    claimBtn.setAttribute('data-reason', canClaim ? st.claimable : '');\n  }\n}`,
    'draw claim button visibility'
  );

  html = replaceOnce(
    html,
    "function startMultiGame(){",
    `var _claimDrawButton = document.getElementById('btn-claim-draw');\nif(_claimDrawButton){\n  _claimDrawButton.addEventListener('click', function(){\n    if(IS_SPECTATOR || gameOver || !gameReady || !socket || !socket.connected) return;\n    var st = Chess.gameStatus(S);\n    if(!st || st.over || !st.claimable || S.t !== MY_PLAYER) return updUI();\n    pendingDrawReason = st.claimable;\n    this.style.display = 'none';\n    socket.emit('echecs_claim_draw', {room:ROOM_ID, player:MY_SLOT});\n  });\n}\n\nfunction startMultiGame(){`,
    'draw claim click handler'
  );

  return html;
}

fs.rmSync(PUBLIC_RUNTIME, { recursive: true, force: true });
fs.cpSync(PUBLIC_SRC, PUBLIC_RUNTIME, { recursive: true });

const gomokuFile = path.join(PUBLIC_RUNTIME, 'gomoku-online.html');
fs.writeFileSync(gomokuFile, patchGomokuHtml(fs.readFileSync(gomokuFile, 'utf8')), 'utf8');

const chessEngineFile = path.join(PUBLIC_RUNTIME, 'echecs-engine.js');
fs.writeFileSync(chessEngineFile, patchChessEngineRuntime(fs.readFileSync(chessEngineFile, 'utf8')), 'utf8');

const chessMultiFile = path.join(PUBLIC_RUNTIME, 'echecs_multi.html');
fs.writeFileSync(chessMultiFile, patchEchecsHtml(fs.readFileSync(chessMultiFile, 'utf8')), 'utf8');

const patchedServer = patchServer(fs.readFileSync(SERVER_FILE, 'utf8'));
const runtimeServer = path.join(ROOT, '.runtime-server.js');
fs.writeFileSync(runtimeServer, patchedServer, 'utf8');

const runtimeModule = new Module(runtimeServer, module);
runtimeModule.filename = runtimeServer;
runtimeModule.paths = Module._nodeModulePaths(ROOT);
runtimeModule._compile(patchedServer, runtimeServer);
