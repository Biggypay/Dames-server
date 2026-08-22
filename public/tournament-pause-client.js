(function () {
  if (typeof socket === 'undefined' || !socket || typeof socket.on !== 'function') return;

  function removeOverlay() {
    var overlay = document.getElementById('mindspille-tournament-pause');
    if (overlay) overlay.remove();
  }

  function showOverlay(payload) {
    removeOverlay();
    var overlay = document.createElement('div');
    overlay.id = 'mindspille-tournament-pause';
    overlay.setAttribute('role', 'status');
    overlay.setAttribute('aria-live', 'assertive');
    overlay.innerHTML = '<div class="mindspille-pause-card">'
      + '<div class="mindspille-pause-icon">Ⅱ</div>'
      + '<strong>Tournoi en pause</strong>'
      + '<p>' + ((payload && payload.message) || 'Le plateau est conservé exactement dans son état actuel.') + '</p>'
      + '<small>La partie reprendra automatiquement après la décision de l’administration.</small>'
      + '</div>';
    var style = document.createElement('style');
    style.textContent = '#mindspille-tournament-pause{position:fixed;inset:0;z-index:2147483646;display:flex;align-items:center;justify-content:center;padding:24px;background:rgba(2,6,23,.46);backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px)}'
      + '.mindspille-pause-card{width:min(420px,100%);padding:28px 24px;text-align:center;color:#fff;border:1px solid rgba(251,191,36,.38);border-radius:24px;background:linear-gradient(145deg,rgba(30,41,59,.84),rgba(15,23,42,.68));box-shadow:0 24px 80px rgba(0,0,0,.48),inset 0 1px rgba(255,255,255,.12);font-family:system-ui,sans-serif}'
      + '.mindspille-pause-icon{width:54px;height:54px;margin:0 auto 14px;display:grid;place-items:center;border-radius:50%;color:#fcd34d;background:rgba(245,158,11,.16);border:1px solid rgba(251,191,36,.35);font-size:25px;font-weight:800}'
      + '.mindspille-pause-card strong{display:block;font-size:20px}.mindspille-pause-card p{margin:10px 0 6px;color:rgba(255,255,255,.78);line-height:1.45}.mindspille-pause-card small{color:rgba(255,255,255,.5);line-height:1.4}';
    overlay.appendChild(style);
    document.body.appendChild(overlay);
  }

  socket.on('tournament:paused', showOverlay);
  socket.on('tournament:resumed', removeOverlay);
})();

/*
 * Quoridor online — garde-fou de synchronisation.
 *
 * Le plateau principal est volontairement autoritatif côté serveur. Une ancienne
 * voie client appliquait toutefois le coup immédiatement, puis recevait les
 * snapshots périodiques du serveur. Si un snapshot de la version précédente
 * arrivait pendant cette fenêtre, le pion semblait revenir en arrière avant
 * d'être resynchronisé. La même voie incrémentale déclenchait aussi l'écran
 * « Défaite -50 HTG » dès que l'adversaire atteignait la ligne, alors que le
 * serveur venait seulement de terminer UNE manche de la série.
 *
 * Ce correctif est strictement limité à la page Quoridor online : on envoie le
 * coup, on verrouille l'input et on attend l'état autoritatif diffusé par le
 * serveur. La fin d'une manche reste gérée par quoridor_round_end ; seul le vrai
 * game:over de fin de série peut ouvrir le modal financier.
 */
(function () {
  var path = String(window.location && window.location.pathname || '').toLowerCase();
  if (path.indexOf('quoridor') === -1) return;
  if (typeof socket === 'undefined' || !socket || typeof socket.on !== 'function') return;
  if (typeof handleTap !== 'function' || typeof nearestHWSlot !== 'function' || typeof nearestVWSlot !== 'function') return;

  var pendingMove = false;
  var pendingBaseVersion = -1;
  var pendingTimer = null;

  function clearPendingMove() {
    pendingMove = false;
    pendingBaseVersion = -1;
    if (pendingTimer) {
      clearTimeout(pendingTimer);
      pendingTimer = null;
    }
    if (typeof isProcessing !== 'undefined') isProcessing = false;
  }

  function enforcePendingUi() {
    if (!pendingMove) return;
    if (typeof isProcessing !== 'undefined') isProcessing = true;
    if (typeof mode !== 'undefined') mode = 'wait';
    if (typeof vmoves !== 'undefined') vmoves = [];
    if (typeof vhw !== 'undefined') vhw = [];
    if (typeof vvw !== 'undefined') vvw = [];
    if (typeof lockButtons === 'function') lockButtons();
    var status = document.getElementById('statusTxt');
    if (status) status.innerHTML = 'Validation<br>du coup';
    if (typeof draw === 'function') draw();
  }

  function sendAuthoritativeMove(moveType, data) {
    if (pendingMove || typeof gameReady === 'undefined' || !gameReady || (typeof gameOver !== 'undefined' && gameOver)) return;
    if (typeof currentSlot !== 'undefined' && typeof MY_SLOT !== 'undefined' && currentSlot !== MY_SLOT) return;
    if (!socket || !socket.connected) return;

    pendingMove = true;
    pendingBaseVersion = (typeof lastStateVersion !== 'undefined' && Number.isFinite(Number(lastStateVersion)))
      ? Number(lastStateVersion)
      : -1;
    if (typeof stopTimer === 'function') stopTimer();
    enforcePendingUi();

    socket.emit('quoridor_move', {
      room: typeof ROOM_ID !== 'undefined' ? ROOM_ID : '',
      player: typeof MY_SLOT !== 'undefined' ? MY_SLOT : 1,
      moveType: moveType,
      data: { r: data.r, c: data.c }
    });

    pendingTimer = setTimeout(function () {
      if (!pendingMove || !socket || !socket.connected) return;
      socket.emit('quoridor_request_state', { room: typeof ROOM_ID !== 'undefined' ? ROOM_ID : '' });
    }, 2200);
  }

  /* Les listeners du canvas appellent le nom global handleTap au moment du tap.
     On remplace donc seulement la décision locale, sans toucher au dessin ni aux
     règles de validation déjà présentes. */
  handleTap = function (pt) {
    if (pendingMove) return;
    if (typeof gameReady === 'undefined' || !gameReady || (typeof gameOver !== 'undefined' && gameOver) || (typeof isProcessing !== 'undefined' && isProcessing)) return;
    if (typeof currentSlot !== 'undefined' && typeof MY_SLOT !== 'undefined' && currentSlot !== MY_SLOT) return;

    var x = pt.x, y = pt.y, i, mv, slot;
    if (typeof MY_SLOT !== 'undefined' && MY_SLOT === 2) {
      x = canvas.width - x;
      y = canvas.height - y;
    }

    if (mode === 'move') {
      for (i = 0; i < vmoves.length; i++) {
        mv = vmoves[i];
        if (x >= cx(mv.c) && x <= cx(mv.c) + CS && y >= cy(mv.r) && y <= cy(mv.r) + CS) {
          sendAuthoritativeMove('move', mv);
          return;
        }
      }
    } else if (mode === 'wallH') {
      slot = nearestHWSlot(x, y);
      if (slot && canHW(slot.r, slot.c)) {
        sendAuthoritativeMove('wallH', slot);
        return;
      }
    } else if (mode === 'wallV') {
      slot = nearestVWSlot(x, y);
      if (slot && canVW(slot.r, slot.c)) {
        sendAuthoritativeMove('wallV', slot);
      }
    }
  };

  /* Plus aucune mutation incrémentale de l'adversaire : le même événement
     quoridor_move transporte déjà gameState + version, puis le listener
     principal applique cet état autoritatif. Surtout, on ne déclenche JAMAIS
     handleGameEnd depuis un simple coup atteignant la ligne d'une manche. */
  applyOpponentMove = function () {
    if (typeof isProcessing !== 'undefined') isProcessing = true;
  };

  socket.on('quoridor_move', function (data) {
    if (!pendingMove || !data) return;
    var version = Number(data.version);
    var mine = typeof MY_SLOT !== 'undefined' && data.player === MY_SLOT;
    if (mine && (!Number.isFinite(version) || version > pendingBaseVersion)) {
      clearPendingMove();
    }
  });

  socket.on('quoridor_state_sync', function (data) {
    if (!pendingMove) return;
    var version = Number(data && data.version);
    if (Number.isFinite(version) && version > pendingBaseVersion) {
      clearPendingMove();
      return;
    }
    /* Un snapshot de la version précédente peut encore être en transit. Il ne
       doit jamais réactiver l'input pendant que le serveur valide le coup. */
    enforcePendingUi();
  });

  socket.on('game:error', function () {
    if (!pendingMove) return;
    clearPendingMove();
  });

  socket.on('quoridor_round_end', function () {
    clearPendingMove();
    /* Une manche n'est pas le match : aucune modale de gain/perte ici. */
    var modal = document.getElementById('gameOverModal');
    if (modal) modal.classList.remove('show');
    var prize = document.getElementById('prizeLine');
    if (prize) prize.style.display = 'none';
    if (typeof gameOver !== 'undefined') gameOver = false;
  });

  socket.on('quoridor_round_start', function () {
    clearPendingMove();
    var modal = document.getElementById('gameOverModal');
    if (modal) modal.classList.remove('show');
    var prize = document.getElementById('prizeLine');
    if (prize) prize.style.display = 'none';
    if (typeof gameOver !== 'undefined') gameOver = false;
  });
})();
