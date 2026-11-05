/*
 * Roulette Royale hors ligne : contre l'IA, et entre amis sur le même
 * appareil (`<body data-mode="ai" | "local">`).
 *
 * Les mêmes règles que le serveur (roulette-rules.js) et le même plateau
 * (roulette-board.js). Comme en ligne, la couleur de la manche est tirée et
 * scellée AVANT les choix ; l'IA choisit au hasard, sans jamais connaître le
 * tirage — dans un jeu de hasard, aucun niveau ne « joue mieux ».
 *
 * Entre amis, chacun choisit à son tour derrière un rideau : la couleur du
 * premier n'est jamais montrée au second avant le tour de roue. Celui qui
 * choisit en premier alterne d'une manche à l'autre.
 *
 * Aucun réseau, aucun argent. En fin de partie contre l'IA, la page prévient
 * l'application (`practice_over`).
 */
(function () {
  'use strict';
  var R = window.RouletteRules;
  var Board = window.RouletteBoard;
  if (!R || !Board) return;

  var MODE = document.body.getAttribute('data-mode') === 'local' ? 'local' : 'ai';
  var P = new URLSearchParams(window.location.search);
  var DIFFICULTY = String(P.get('difficulty') || P.get('level') || 'medium').toLowerCase();
  /* ?fast=1 : des manches accélérées, pour les tests de la page. */
  var FAST = P.get('fast') === '1';
  var SPIN_MS = FAST ? 500 : 4800;
  var BETWEEN_MS = FAST ? 300 : 2600;
  var REPICK_MS = FAST ? 300 : 2200;
  var FINAL_HOLD_MS = FAST ? 200 : 1300;
  var TURN_MS = FAST ? 3000 : 30000;
  var CIRC_SMALL = 163.4;
  var ROOM = MODE + '-' + Date.now().toString(36) + '-' + Board.randomInt(1000000000).toString(36);

  function clean(name, fallback) {
    var s = String(name || '').replace(/\s+/g, ' ').trim().slice(0, 24);
    return s || fallback;
  }
  var NAMES = MODE === 'ai'
    ? { 1: clean(P.get('name') || P.get('username'), 'Vous'), 2: 'IA' }
    : { 1: clean(P.get('p1Name') || P.get('name'), 'Joueur 1'), 2: clean(P.get('p2Name'), 'Joueur 2') };

  function $(id) { return document.getElementById(id); }
  var lockBtn = $('lockBtn'), actionEl = $('action');
  var roundLabelEl = $('roundLabel'), roundsProgress = $('roundsProgress');
  var profileHuman = $('profile-human'), profileAi = $('profile-ai');
  var timerArcHuman = $('timer-arc-human'), timerArcAi = $('timer-arc-ai');
  var gameOverModal = $('gameOverModal'), modalContent = $('modalContent');
  var curtain = $('curtain');

  var board = Board.mount({
    stage: $('wheel'), palette: $('palette'), duel: $('duel'), history: $('history'),
    seal: $('seal'), sealBox: $('sealBox'), status: $('status'), onPick: onPick
  });
  Board.fitWheel({
    wrap: $('wrap'), board: document.querySelector('.rr-board'), stage: $('wheel'),
    stack: [$('duel'), $('action'), $('palette'), document.querySelector('.rr-foot')],
    under: document.querySelector('.rr-foot'), min: 120, max: 400
  });

  var rulesBtn = $('rulesBtn'), rulesBox = $('rulesBox');
  if (rulesBtn && rulesBox) {
    rulesBtn.addEventListener('click', function (e) {
      e.preventDefault();
      rulesBox.hidden = !rulesBox.hidden;
      rulesBtn.setAttribute('aria-expanded', rulesBox.hidden ? 'false' : 'true');
    });
  }

  /* ══ État ══ */
  var scores = [0, 0], round = 1, decisive = false, history = [];
  var phase = 'idle';           /* idle | sealing | choosing | spinning | between | over */
  var seal = null;              /* le tirage de la manche : { kind, value, salt, hash } */
  var picks = { 1: null, 2: null };
  var selected = null;          /* la couleur touchée par celui qui choisit */
  var chooser = 1;              /* qui choisit (entre amis) ; contre l'IA, toujours le joueur */
  var curtainShown = false;
  var matchToken = 0;
  var turnStart = 0, turnRAF = null, aiTimer = null, nextTimer = null, lastHubKey = '';

  function leftName() { return MODE === 'ai' ? 'Vous' : NAMES[1]; }
  function rightName() { return NAMES[2]; }
  function resultOf(ws) { return ws === 1 ? 'win' : ws === 2 ? 'lose' : 'draw'; }

  /* ══ Messages, confettis ══ */
  var toastTimer = null;
  function showToast(emoji, title, sub, delay) {
    var el = $('toast');
    $('toast-emoji').textContent = emoji;
    $('toast-title').textContent = title;
    $('toast-sub').textContent = sub || '';
    if (toastTimer) clearTimeout(toastTimer);
    el.style.cssText = 'display:block;opacity:0;transform:translate(-50%,-50%) scale(0.8);transition:none;';
    setTimeout(function () {
      el.style.transition = 'all 0.35s cubic-bezier(0.175,0.885,0.32,1.275)';
      el.style.opacity = '1'; el.style.transform = 'translate(-50%,-50%) scale(1)';
    }, 20);
    toastTimer = setTimeout(function () {
      toastTimer = null;
      el.style.opacity = '0'; el.style.transform = 'translate(-50%,-50%) scale(0.85)';
      setTimeout(function () { el.style.display = 'none'; }, 300);
    }, delay || 2000);
  }
  var confettiCanvas = $('confetti-canvas'), confettiCtx = confettiCanvas.getContext('2d');
  var confettiParts = [], confettiActive = false;
  function resizeConfetti() { confettiCanvas.width = window.innerWidth; confettiCanvas.height = window.innerHeight; }
  window.addEventListener('resize', resizeConfetti);
  resizeConfetti();
  function createConfetti(count) {
    var colors = R.COLORS.map(function (c) { return c.hex; }).concat(['#fbbf24', '#ffffff']);
    for (var i = 0; i < (count || 150); i++) {
      confettiParts.push({
        x: confettiCanvas.width / 2, y: confettiCanvas.height / 2,
        vx: (Math.random() - 0.5) * 18, vy: (Math.random() - 0.5) * 18 - 5,
        color: colors[Math.floor(Math.random() * colors.length)], size: Math.random() * 8 + 4,
        rotation: Math.random() * 360, rotSpeed: (Math.random() - 0.5) * 10, life: 1
      });
    }
    if (!confettiActive) { confettiActive = true; requestAnimationFrame(updateConfetti); }
  }
  function updateConfetti() {
    confettiCtx.clearRect(0, 0, confettiCanvas.width, confettiCanvas.height);
    for (var i = confettiParts.length - 1; i >= 0; i--) {
      var p = confettiParts[i];
      p.x += p.vx; p.y += p.vy; p.vy += 0.28; p.vx *= 0.985; p.vy *= 0.985; p.rotation += p.rotSpeed; p.life -= 0.004;
      if (p.life <= 0 || p.y > confettiCanvas.height + 60) { confettiParts.splice(i, 1); continue; }
      confettiCtx.save();
      confettiCtx.translate(p.x, p.y); confettiCtx.rotate(p.rotation * Math.PI / 180);
      confettiCtx.globalAlpha = p.life; confettiCtx.fillStyle = p.color;
      confettiCtx.fillRect(-p.size / 2, -p.size / 2, p.size, p.size);
      confettiCtx.restore();
    }
    if (confettiParts.length) requestAnimationFrame(updateConfetti);
    else { confettiActive = false; confettiCtx.clearRect(0, 0, confettiCanvas.width, confettiCanvas.height); }
  }

  /* ══ Affichage ══ */
  function renderAll() {
    $('playerScore').textContent = scores[0];
    $('aiScore').textContent = scores[1];
    roundLabelEl.textContent = decisive ? 'Manche décisive' : 'Manche ' + Math.min(round, R.REGULAR_ROUNDS) + ' / ' + R.REGULAR_ROUNDS;
    var dots = roundsProgress.querySelectorAll('.round-dot');
    dots.forEach(function (dot) { dot.className = 'round-dot'; });
    var extra = [];
    history.forEach(function (h) {
      if (h.decisive) { if (!h.repick) extra.push(resultOf(h.winnerSlot)); return; }
      if (dots[h.round - 1]) dots[h.round - 1].classList.add('played', resultOf(h.winnerSlot));
    });
    var live = phase === 'choosing' || phase === 'sealing' || phase === 'spinning';
    if (live && !decisive && dots[round - 1] && !history.some(function (h) { return h.round === round; })) dots[round - 1].classList.add('current');
    if (window.MindspilleHud) MindspilleHud.decisive(roundsProgress, extra, live && decisive);
    board.setHistory(history.map(function (h) {
      return { round: h.round, drawn: h.drawn, repick: h.repick, result: h.winnerSlot === 1 ? 'me' : h.winnerSlot === 2 ? 'op' : '' };
    }));
  }
  function hubLabel() { return decisive ? 'Décisive' : 'Manche ' + Math.min(round, R.REGULAR_ROUNDS); }

  var LOCK_ICON = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="5" y="11" width="14" height="10" rx="2"/><path d="M8 11V8a4 4 0 0 1 8 0v3"/></svg>';
  function canPick() {
    return phase === 'choosing' && picks[chooser] === null && !curtainShown && gameOverModal.className.indexOf('show') < 0;
  }
  function renderLock() {
    var show = phase === 'choosing' || phase === 'sealing';
    lockBtn.hidden = !show;
    actionEl.classList.toggle('rr-locking', show);
    if (!show) return;
    lockBtn.classList.remove('rr-done');
    if (picks[chooser] !== null) {
      lockBtn.disabled = true; lockBtn.classList.add('rr-done');
      lockBtn.innerHTML = LOCK_ICON + '<span>Couleur verrouillée</span>';
      return;
    }
    if (selected === null || !canPick()) {
      lockBtn.disabled = true;
      lockBtn.innerHTML = '<span>Touchez une couleur</span>';
      return;
    }
    var c = R.COLORS[selected];
    lockBtn.disabled = false;
    lockBtn.innerHTML = '<span class="rr-lock-dot" style="background:' + c.hex + '"></span><span>Verrouiller</span><span class="rr-lock-name"></span>';
    lockBtn.querySelector('.rr-lock-name').textContent = c.name;
  }
  /* La puce d'un joueur pendant le choix. Entre amis, une couleur verrouillée
     n'est jamais montrée avant le tour de roue : l'autre regarde l'écran. */
  function chipFor(slot) {
    var name = slot === 1 ? leftName() : rightName();
    if (MODE === 'ai' && slot === 2) {
      return picks[2] !== null ? { name: name, kind: 'locked', label: 'A choisi' } : { name: name, kind: 'waiting', label: 'Réfléchit…' };
    }
    if (picks[slot] !== null) {
      if (MODE === 'ai') return { name: name, kind: 'color', color: picks[slot], label: 'Verrouillée' };
      return { name: name, kind: 'locked', label: 'A choisi' };
    }
    if (slot === chooser && !curtainShown && phase === 'choosing') {
      if (selected !== null) return { name: name, kind: 'color', color: selected, miss: true, label: 'Non verrouillée' };
      return { name: name, kind: 'waiting', label: MODE === 'ai' ? 'Votre couleur' : 'À vous' };
    }
    return { name: name, kind: 'waiting', label: 'En attente' };
  }
  function renderChoosing() {
    board.setChip('me', chipFor(1));
    board.setChip('op', chipFor(2));
    board.setPalette({ selected: canPick() ? selected : null, enabled: canPick() });
    renderLock();
    if (MODE === 'ai') {
      profileHuman.classList.toggle('active', picks[1] === null);
      profileAi.classList.toggle('active', picks[2] === null);
    } else {
      profileHuman.classList.toggle('active', picks[1] === null && chooser === 1);
      profileAi.classList.toggle('active', picks[2] === null && chooser === 2);
    }
    if (MODE === 'local' && phase === 'choosing') {
      var hubKey = 'local|' + round + '|' + decisive;
      if (hubKey !== lastHubKey) { lastHubKey = hubKey; board.setHub(decisive ? 'Décisive' : 'Manche', decisive ? '⚖' : String(round), null, null); }
    }
  }

  /* ══ Le chronomètre (contre l'IA) : 30 s, puis la couleur part d'elle-même ══ */
  function startTurnTimer() {
    stopTurnTimer();
    turnStart = Date.now();
    turnRAF = requestAnimationFrame(tickTurn);
  }
  function stopTurnTimer() {
    if (turnRAF) cancelAnimationFrame(turnRAF);
    turnRAF = null;
    lastHubKey = '';
    timerArcHuman.style.strokeDashoffset = CIRC_SMALL;
    timerArcAi.style.strokeDashoffset = CIRC_SMALL;
    profileHuman.classList.remove('timer-urgent');
  }
  function tickTurn() {
    turnRAF = null;
    if (MODE !== 'ai' || phase !== 'choosing') return;
    var remaining = Math.max(0, turnStart + TURN_MS - Date.now());
    var progress = Math.min(1, 1 - remaining / TURN_MS);
    var urgent = progress >= 0.67;
    if (picks[1] === null) timerArcHuman.style.strokeDashoffset = CIRC_SMALL * progress;
    profileHuman.classList.toggle('timer-urgent', urgent && picks[1] === null);
    var secs = Math.ceil(remaining / 1000);
    var hubKey = hubLabel() + '|' + secs + '|' + urgent;
    if (hubKey !== lastHubKey) { lastHubKey = hubKey; board.setHub(hubLabel(), secs, urgent ? 'urgent' : null, null); }
    if (remaining <= 0 && picks[1] === null) {
      /* Temps écoulé : la couleur touchée, sinon une au hasard. */
      var auto = selected === null;
      if (auto) selected = Board.randomInt(R.COLOR_COUNT);
      var color = selected;
      lockChoice();
      if (auto) showToast('⏱️', 'Choix automatique', R.colorName(color), 1600);
      return;
    }
    turnRAF = requestAnimationFrame(tickTurn);
  }

  /* ══ Le rideau (entre amis) ══ */
  function showCurtain(kind) {
    if (!curtain) return;
    curtainShown = true;
    var name = NAMES[chooser], other = NAMES[chooser === 1 ? 2 : 1];
    $('curtain-title').textContent = name + ', à vous de choisir';
    $('curtain-sub').textContent = kind === 'pass'
      ? 'Passez l’appareil à ' + name + '. ' + other + ' ne regarde pas !'
      : 'Choisissez votre couleur en secret : ' + other + ' ne regarde pas.';
    $('curtain-btn').textContent = 'Je suis ' + name;
    curtain.hidden = false;
    renderChoosing();
  }
  function hideCurtain() {
    if (!curtain || curtain.hidden) return;
    curtain.hidden = true;
    curtainShown = false;
    renderChoosing();
  }
  if (curtain) $('curtain-btn').addEventListener('click', function (e) { e.preventDefault(); hideCurtain(); });

  /* ══ Choisir, puis verrouiller ══ */
  function onPick(id) {
    if (!canPick()) return;
    if (selected === id) { lockChoice(); return; }
    selected = id;
    renderChoosing();
  }
  function lockChoice() {
    if (phase !== 'choosing' || selected === null || picks[chooser] !== null || curtainShown) return;
    picks[chooser] = selected;
    selected = null;
    if (MODE === 'ai') {
      stopTurnTimer();
      board.setHub(hubLabel(), '', null, null);
      renderChoosing();
      maybeSpin();
      return;
    }
    var other = chooser === 1 ? 2 : 1;
    if (picks[other] === null) { chooser = other; showCurtain('pass'); }
    else { renderChoosing(); maybeSpin(); }
  }
  lockBtn.addEventListener('click', function (e) { e.preventDefault(); lockChoice(); });

  function scheduleAi() {
    var token = matchToken, r = round;
    if (aiTimer) clearTimeout(aiTimer);
    aiTimer = setTimeout(function () {
      aiTimer = null;
      if (token !== matchToken || round !== r || phase !== 'choosing') return;
      /* Au hasard : l'IA ne connaît pas le tirage, et aucun choix n'est meilleur qu'un autre. */
      picks[2] = Board.randomInt(R.COLOR_COUNT);
      renderChoosing();
      maybeSpin();
    }, FAST ? 120 : 600 + Board.randomInt(1200));
  }
  function maybeSpin() {
    if (phase === 'choosing' && picks[1] !== null && picks[2] !== null) spin();
  }

  /* ══ Les manches ══ */
  function openRound() {
    var token = matchToken;
    phase = 'sealing';
    picks = { 1: null, 2: null };
    selected = null;
    chooser = MODE === 'local' ? (round % 2 === 1 ? 1 : 2) : 1;
    lastHubKey = '';
    board.resetWheel();
    board.setHub(hubLabel(), '', null, null);
    board.setSeal(null);
    board.setStatus('');
    renderAll();
    renderChoosing();
    /* Le tirage est fait et scellé avant les choix, comme sur le serveur. */
    Board.localSeal(ROOM, round, decisive).then(function (s) {
      if (token !== matchToken) return;
      seal = s;
      phase = 'choosing';
      board.setSeal(s.hash ? { hash: s.hash, state: 'sealed' } : null);
      renderAll();
      if (MODE === 'ai') { renderChoosing(); startTurnTimer(); scheduleAi(); }
      else showCurtain('first');
    });
  }

  function spin() {
    var token = matchToken;
    phase = 'spinning';
    stopTurnTimer();
    if (aiTimer) { clearTimeout(aiTimer); aiTimer = null; }
    var c1 = picks[1], c2 = picks[2];
    var drawn = R.drawnColor(seal, c1, c2);
    var entry = R.publicRound({
      round: round, choice1: c1, choice2: c2, drawn: drawn,
      winnerSlot: R.roundWinner(c1, c2, drawn), decisive: decisive, repick: decisive && drawn === null
    });
    board.setChip('me', { name: leftName(), kind: 'color', color: c1, reveal: true });
    board.setChip('op', { name: rightName(), kind: 'color', color: c2, reveal: true });
    board.setPalette({ selected: MODE === 'ai' ? c1 : null, enabled: false });
    renderLock();
    profileHuman.classList.add('active'); profileAi.classList.add('active');
    renderAll();
    if (drawn === null) { finish(entry, token); return; }
    var wheel = R.wheelFor(decisive, c1, c2);
    board.setStatus(decisive ? 'Une chance sur deux…' : 'La roue tourne…');
    board.setHub(decisive ? 'Décisive' : 'Tirage', '', null, null);
    board.spinTo(wheel, R.landingFor(wheel, drawn, seal.salt), SPIN_MS).then(function () {
      if (token === matchToken) finish(entry, token);
    });
  }

  function finish(entry, token) {
    if (token !== matchToken) return;
    if (entry.winnerSlot) scores[entry.winnerSlot - 1] += 1;
    history.push(entry);
    var ws = entry.winnerSlot, drawn = entry.drawn;
    var c1 = entry.choice1, c2 = entry.choice2;
    if (entry.repick) {
      board.setChip('me', { name: leftName(), kind: 'color', color: c1 });
      board.setChip('op', { name: rightName(), kind: 'color', color: c2 });
      board.setHub('Décisive', '=', null, null);
      board.setStatus('🎨 Même couleur · on rechoisit', 'draw');
      showToast('🎨', 'Même couleur !', 'Vous avez choisi la même couleur : chacun rechoisit.', 2000);
    } else {
      board.setChip('me', { name: leftName(), kind: 'color', color: c1, winner: ws === 1, miss: c1 !== drawn });
      board.setChip('op', { name: rightName(), kind: 'color', color: c2, winner: ws === 2, miss: c2 !== drawn });
      board.setHub('Tirée', '', null, drawn);
      var name = R.colorName(drawn);
      if (MODE === 'ai') {
        if (ws === 1) board.setStatus('🎉 Manche gagnée · ' + name, 'win');
        else if (ws === 2) board.setStatus('💀 Manche perdue · ' + name, 'lose');
      } else if (ws) board.setStatus('🎯 ' + NAMES[ws] + ' marque · ' + name, 'win');
      if (!ws) board.setStatus(c1 === drawn && c2 === drawn ? '🤝 Tous les deux sur ' + name : '➖ Personne n’avait ' + name, 'draw');
      if (ws === 1 || (MODE === 'local' && ws)) createConfetti(50);
    }
    Board.verifySpin(ROOM, { round: entry.round, seal: seal }, seal && seal.hash).then(function (res) {
      if (token !== matchToken || !seal || !seal.hash) return;
      board.setSeal({ hash: seal.hash, state: res.ok === true ? 'verified' : res.ok === false ? 'failed' : 'sealed', revealed: res.text });
    });
    var played = history.filter(function (h) { return !h.decisive; }).length;
    var next = R.matchDecision({ scores: scores, roundsPlayed: played, totalRounds: R.REGULAR_ROUNDS, decisive: entry.decisive, lastWinner: ws });
    if (next.over) {
      phase = 'over';
      renderAll();
      nextTimer = setTimeout(function () { if (token === matchToken) showEnd(next.winnerSlot); }, FINAL_HOLD_MS);
      return;
    }
    phase = 'between';
    renderAll();
    if (next.decisive && !entry.decisive) setTimeout(function () {
      if (token === matchToken) showToast('⚖️', 'Égalité !', 'Manche décisive : la roue ne gardera que vos deux couleurs.', 2400);
    }, 700);
    nextTimer = setTimeout(function () {
      nextTimer = null;
      if (token !== matchToken) return;
      round += 1;
      decisive = decisive || next.decisive === true;
      openRound();
    }, entry.repick ? REPICK_MS : BETWEEN_MS + (next.decisive && !entry.decisive ? 1400 : 0));
  }

  /* ══ Fin de partie ══ */
  function miniChip(color) {
    if (!R.isColor(color)) return '<span class="rr-mini rr-none"></span>';
    return '<span class="rr-mini" style="background:' + R.COLORS[color].hex + '">' + Board.colorIcon(color) + '</span>';
  }
  function showEnd(winnerSlot) {
    phase = 'over';
    stopTurnTimer();
    var title, message, cls;
    if (MODE === 'ai') {
      var won = winnerSlot === 1;
      title = won ? '🏆 VICTOIRE !' : '💀 DÉFAITE';
      message = won ? 'Vous battez l’IA à la Roulette Royale !' : 'L’IA remporte la Roulette Royale.';
      cls = won ? 'win-modal' : 'lose-modal';
      if (won) { createConfetti(); createConfetti(); }
      try {
        window.parent.postMessage({
          type: 'mindspille', source: 'roulette-ai', event: 'practice_over', game: 'roulette',
          result: won ? 'win' : 'lose', reason: 'normal', difficulty: DIFFICULTY, scores: { me: scores[0], ia: scores[1] }
        }, '*');
      } catch (_) {}
    } else {
      title = '🏆 ' + NAMES[winnerSlot] + ' gagne !';
      message = 'Une revanche ?';
      cls = 'win-modal';
      createConfetti(); createConfetti();
    }
    $('modalTitle').textContent = title;
    $('finalScore').textContent = scores[0] + ' - ' + scores[1];
    $('finalMessage').textContent = message;
    modalContent.className = 'modal ' + cls;
    var list = $('modalHistoryList');
    list.innerHTML = '';
    for (var i = history.length - 1; i >= 0; i--) {
      var h = history[i];
      var res = h.repick ? 'draw' : resultOf(h.winnerSlot);
      var item = document.createElement('div');
      item.className = 'modal-history-item ' + res;
      var label = document.createElement('span');
      label.textContent = h.decisive ? 'Décisive' : 'Manche ' + h.round;
      item.appendChild(label);
      var pair = document.createElement('span');
      pair.className = 'rr-pair';
      pair.innerHTML = miniChip(h.choice1) + '<span class="rr-arrow">vs</span>' + miniChip(h.choice2);
      item.appendChild(pair);
      var drawnEl = document.createElement('span');
      drawnEl.className = 'rr-pair';
      drawnEl.innerHTML = '<span class="rr-arrow">→</span>' + miniChip(h.drawn);
      item.appendChild(drawnEl);
      var mark = document.createElement('span');
      mark.textContent = h.repick ? '🎨' : res === 'win' ? (MODE === 'ai' ? '✅' : '①') : res === 'lose' ? (MODE === 'ai' ? '❌' : '②') : '➖';
      item.appendChild(mark);
      list.appendChild(item);
    }
    renderLock();
    gameOverModal.classList.add('show');
  }

  function startMatch() {
    matchToken += 1;
    if (aiTimer) { clearTimeout(aiTimer); aiTimer = null; }
    if (nextTimer) { clearTimeout(nextTimer); nextTimer = null; }
    stopTurnTimer();
    scores = [0, 0]; round = 1; decisive = false; history = []; seal = null;
    picks = { 1: null, 2: null }; selected = null; phase = 'idle';
    gameOverModal.classList.remove('show');
    if (curtain) { curtain.hidden = true; curtainShown = false; }
    board.resetWheel();
    board.setSeal(null);
    board.setStatus('');
    board.setHub('Roulette', '', null, null);
    renderAll();
    renderChoosing();
    var token = matchToken;
    showToast('🎡', 'Roulette Royale', R.REGULAR_ROUNDS + ' manches · six couleurs', FAST ? 400 : 1600);
    setTimeout(function () { if (token === matchToken) openRound(); }, FAST ? 100 : 1100);
  }

  function close() {
    try {
      if (MODE === 'ai') window.parent.postMessage({ type: 'mindspille', source: 'roulette-ai', event: 'back' }, '*');
      window.parent.postMessage({ type: 'close_game' }, '*');
    } catch (_) {}
    gameOverModal.classList.remove('show');
  }
  $('replayBtn').addEventListener('click', function (e) { e.preventDefault(); startMatch(); });
  $('closeBtn').addEventListener('click', function (e) { e.preventDefault(); close(); });

  /* Les noms et les portraits : le joueur (son initiale), l'IA (son robot). */
  $('name-human').textContent = NAMES[1];
  $('name-ai').textContent = NAMES[2];
  if (window.MindspilleHud) {
    MindspilleHud.paint('avatar-human', '');
    if (MODE === 'local') MindspilleHud.paint('avatar-ai', '');
  }

  window.RouletteOffline = {
    mode: MODE,
    /* Pour les tests de la page : l'état, jamais le tirage avant le tour de roue. */
    state: function () {
      return { phase: phase, round: round, decisive: decisive, scores: scores.slice(), chooser: chooser, curtain: curtainShown, picked: { 1: picks[1] !== null, 2: picks[2] !== null }, history: history.slice() };
    }
  };
  startMatch();
})();
