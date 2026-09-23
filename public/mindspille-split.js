/*
 * Écran partagé de l'application Mindspille.
 *
 * Sur un grand écran, ou un téléphone couché, l'application affiche le plateau
 * à gauche et son propre panneau de partie à droite : les deux joueurs, le
 * score, la mise, le tour, chaque coup. Tout cela figurait déjà au-dessus du
 * plateau (#top) — deux fois la même information, et un plateau rétréci
 * d'autant. En écran partagé, l'application le signale à la page
 * (`mindspille:layout`) : l'en-tête et les bandeaux posés sur le plateau
 * s'effacent, le plateau reprend la place, et la barre du bas — vue, figer,
 * rotation — reste. Les bandeaux ne sont pas perdus : leur texte est relayé à
 * l'application (`mindspille:board-notices`), qui l'affiche dans son panneau.
 *
 * En portrait, ou hors de l'application, rien ne change. Les spectateurs ne
 * sont pas concernés : leur page a déjà sa propre vue dépouillée.
 *
 * Entraînement contre l'IA et partie entre amis sur le même appareil : il n'y
 * a là aucun direct à suivre, l'application ne sait de la partie que ce que la
 * page lui dit. Quand elle le demande (`hud: true`), le contenu de l'en-tête
 * masqué part donc vers son panneau (`mindspille:board-hud`) : les deux
 * joueurs, celui qui a la main, le score, l'intitulé, ce que chacun a pris.
 */
(function () {
  'use strict';
  if (window.parent === window) return;
  var params = new URLSearchParams(window.location.search);
  if (params.get('spectate') === '1' || params.get('spectator') === '1') return;

  var parentOrigin = null;
  try { if (document.referrer) parentOrigin = new URL(document.referrer).origin; } catch (_) {}
  var gameId = params.get('gameId') || params.get('room') || '';

  /* Ce que le panneau de l'application affiche déjà. */
  var HIDDEN = ['#top', '#forfeit-bar', '#force-jump-hint'];
  /* Bandeaux masqués ici dont le texte part vers le panneau. */
  var NOTICES = ['forfeit-bar', 'force-jump-hint'];

  var style = document.createElement('style');
  style.textContent = HIDDEN.map(function (selector) { return 'html.ms-split ' + selector; }).join(',') + '{display:none!important}';
  (document.head || document.documentElement).appendChild(style);

  var split = false;
  var lastSent = null;
  var wantHud = false;
  var lastHud = null;
  var hudTimer = null;

  function post(message) {
    try { window.parent.postMessage(message, parentOrigin || '*'); } catch (_) {}
  }

  function currentNotices() {
    var list = [];
    NOTICES.forEach(function (id) {
      var el = document.getElementById(id);
      if (!el || !el.classList.contains('show')) return;
      var text = (el.textContent || '').replace(/\s+/g, ' ').trim();
      if (text) list.push({ id: id, text: text.slice(0, 160) });
    });
    return list;
  }

  function publish() {
    var notices = split ? currentNotices() : [];
    var key = JSON.stringify(notices);
    if (key === lastSent) return;
    lastSent = key;
    post({ type: 'mindspille:board-notices', gameId: gameId, notices: notices });
  }

  function text(el) {
    return el ? (el.textContent || '').replace(/\s+/g, ' ').trim().slice(0, 60) : '';
  }
  function numberIn(el) {
    if (!el) return null;
    var n = parseInt(String(el.textContent || '').replace(/[^\d-]+/g, ''), 10);
    return isFinite(n) ? n : null;
  }
  /* Pièces prises : « ×7 » quand la page l'écrit, sinon une marque par pièce. */
  function capturedIn(row) {
    if (!row) return null;
    var total = row.querySelector('.cap-count');
    if (total) return numberIn(total) || 0;
    return row.children.length;
  }
  function side(profile) {
    return {
      name: text(profile.querySelector('.profile-name')),
      active: profile.classList.contains('active'),
      role: text(profile.querySelector('.profile-role')) || null,
      captured: capturedIn(profile.querySelector('.captured-row')),
      walls: numberIn(profile.querySelector('.walls-num'))
    };
  }
  function readHud() {
    var top = document.getElementById('top');
    if (!top) return null;
    var profiles = [];
    for (var i = 0; i < top.children.length; i++) {
      if (top.children[i].classList.contains('profile')) profiles.push(top.children[i]);
    }
    if (profiles.length < 2) return null;
    var center = top.querySelector('.top-center');
    var numbers = center ? center.querySelectorAll('.score-row .snum') : [];
    var score = numbers.length === 2 ? [numberIn(numbers[0]), numberIn(numbers[1])] : null;
    if (score && (score[0] === null || score[1] === null)) score = null;
    return {
      left: side(profiles[0]),
      right: side(profiles[1]),
      score: score,
      label: center ? (text(center.querySelector('.manche-lbl')) || text(center.querySelector('.sub'))) : ''
    };
  }
  function publishHud() {
    hudTimer = null;
    if (!split || !wantHud) return;
    var hud = readHud();
    var key = JSON.stringify(hud);
    if (key === lastHud) return;
    lastHud = key;
    post({ type: 'mindspille:board-hud', gameId: gameId, hud: hud });
  }
  /* Un changement de tour touche plusieurs nœuds d'un coup : un seul envoi. */
  function scheduleHud() {
    if (!hudTimer) hudTimer = setTimeout(publishHud, 60);
  }

  /* Chaque plateau recalcule sa taille et son cadrage sur `resize` : on le lui
     envoie une fois la nouvelle mise en page appliquée, puis de nouveau au cas
     où le navigateur l'aurait différée. */
  function relayout() {
    [0, 80, 300].forEach(function (delay) {
      setTimeout(function () { window.dispatchEvent(new Event('resize')); }, delay);
    });
  }

  function apply(next, hud) {
    if (hud !== wantHud) {
      wantHud = hud;
      lastHud = null;
    }
    if (next !== split) {
      split = next;
      document.documentElement.classList.toggle('ms-split', split);
      relayout();
      publish();
      lastHud = null;
    }
    scheduleHud();
  }

  window.addEventListener('message', function (event) {
    if (event.source !== window.parent) return;
    if (parentOrigin && event.origin !== parentOrigin) return;
    var data = event.data;
    if (!data || data.type !== 'mindspille:layout') return;
    if (data.gameId && gameId && data.gameId !== gameId) return;
    apply(data.split === true, data.hud === true);
  });

  function start() {
    if (typeof MutationObserver === 'function') {
      NOTICES.forEach(function (id) {
        var el = document.getElementById(id);
        if (el) new MutationObserver(publish).observe(el, { attributes: true, attributeFilter: ['class'], childList: true, characterData: true, subtree: true });
      });
      var top = document.getElementById('top');
      if (top) new MutationObserver(scheduleHud).observe(top, { attributes: true, attributeFilter: ['class'], childList: true, characterData: true, subtree: true });
    }
    /* L'application attend ce signal pour annoncer la mise en page : un
       message envoyé avant que la page n'écoute serait perdu. */
    post({ type: 'mindspille:layout-ready', gameId: gameId });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start, { once: true });
  else start();
})();
