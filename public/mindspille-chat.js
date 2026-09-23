/*
 * Messagerie de partie — le bouton du plateau.
 *
 * Les deux joueurs d'un match en ligne peuvent s'écrire pendant la partie. La
 * conversation vit dans l'application (table `chat_messages`, la même que le
 * chat d'avant-partie) ; le plateau n'en porte que le bouton, à sa place dans
 * la barre du bas : juste après le premier bouton (la vue). Un clic le signale
 * à l'application (`mindspille:chat-toggle`), qui remplace son panneau de
 * partie par la conversation, puis le remet à la fermeture.
 *
 * C'est l'application qui décide de tout ce que le bouton affiche
 * (`mindspille:chat`) : s'il existe, s'il est ouvert, et combien de messages
 * attendent — le nombre s'affiche dans une pastille. Hors de l'application, ou
 * tant qu'elle ne l'a pas demandé, le bouton reste invisible : une vieille
 * version de l'application ne verrait jamais un bouton qui ne fait rien.
 *
 * Penalty et Chifoumi n'ont pas de barre du bas : le bouton y flotte dans le
 * coin inférieur gauche. Les spectateurs ne sont pas concernés.
 */
(function () {
  'use strict';
  if (window.parent === window) return;
  var params = new URLSearchParams(window.location.search);
  if (params.get('spectate') === '1' || params.get('spectator') === '1') return;

  var parentOrigin = null;
  try { if (document.referrer) parentOrigin = new URL(document.referrer).origin; } catch (_) {}
  var gameId = params.get('gameId') || params.get('room') || '';

  var ICON = '<svg width="19" height="19" viewBox="0 0 24 24" fill="none" aria-hidden="true">'
    + '<path d="M20.5 11.6c0 4.2-3.8 7.6-8.5 7.6-1.1 0-2.2-.2-3.2-.5L4 20.2l1.3-3.7c-1.1-1.3-1.8-3-1.8-4.9C3.5 7.4 7.3 4 12 4s8.5 3.4 8.5 7.6z" stroke="currentColor" stroke-width="1.7" stroke-linejoin="round"/>'
    + '<circle cx="8.4" cy="11.7" r="1.05" fill="currentColor"/><circle cx="12" cy="11.7" r="1.05" fill="currentColor"/><circle cx="15.6" cy="11.7" r="1.05" fill="currentColor"/>'
    + '</svg>';

  var style = document.createElement('style');
  style.textContent = ''
    + '.ms-chat-btn{position:relative;display:flex;align-items:center;justify-content:center;width:40px;height:40px;padding:0;flex:0 0 40px;'
    + 'border-radius:50%;background:rgba(255,255,255,0.10);border:1px solid rgba(255,255,255,0.28);color:rgba(255,255,255,0.8);'
    + 'cursor:pointer;-webkit-tap-highlight-color:transparent;-webkit-appearance:none;outline:none;transition:background .2s,border-color .2s,color .2s,box-shadow .2s,transform .15s}'
    + '.ms-chat-btn:active{transform:scale(0.94)}'
    + '.ms-chat-btn:focus-visible{box-shadow:0 0 0 2px rgba(251,191,36,0.8)}'
    + '.ms-chat-btn.ms-open{background:rgba(251,191,36,0.2);border-color:rgba(251,191,36,0.7);color:#fbbf24;box-shadow:0 0 12px rgba(251,191,36,0.3)}'
    + '.ms-chat-btn.ms-unread{color:#fff;border-color:rgba(248,113,113,0.8)}'
    + '.ms-chat-badge{position:absolute;top:-6px;right:-6px;display:none;min-width:19px;height:19px;padding:0 5px;box-sizing:border-box;border-radius:10px;'
    + 'background:#ef4444;color:#fff;font:700 10.5px/19px system-ui,-apple-system,sans-serif;text-align:center;letter-spacing:0;'
    + 'box-shadow:0 0 0 2px rgba(15,23,42,0.92);pointer-events:none}'
    + '.ms-chat-btn.ms-unread .ms-chat-badge{display:block}'
    + '.ms-chat-btn.ms-bump{animation:ms-chat-bump .5s ease}'
    + '@keyframes ms-chat-bump{0%{transform:scale(1)}30%{transform:scale(1.18)}60%{transform:scale(0.96)}100%{transform:scale(1)}}'
    + '.ms-chat-float{position:fixed;z-index:30;left:calc(12px + env(safe-area-inset-left,0px));bottom:calc(14px + env(safe-area-inset-bottom,0px));'
    + 'width:44px;height:44px;flex:none;background:rgba(15,23,42,0.72);-webkit-backdrop-filter:blur(10px);backdrop-filter:blur(10px)}'
    + 'html:not(.ms-chat-on) .ms-chat-btn{display:none!important}'
    /* Quoridor : sa barre porte déjà trois boutons de jeu et le statut ; ils
       se resserrent d'autant pour que « Mur H » tienne sur une ligne. */
    + 'html.ms-chat-on #btnMove,html.ms-chat-on #btnH,html.ms-chat-on #btnV{letter-spacing:0.2px;padding-left:3px;padding-right:3px;white-space:nowrap}'
    + 'html.ms-chat-on #bot > #statusTxt{min-width:46px}'
    + '@media (max-width:400px){html.ms-chat-on #bot{padding-left:8px;padding-right:8px;gap:5px}'
    + 'html.ms-chat-on #btnMove,html.ms-chat-on #btnH,html.ms-chat-on #btnV{font-size:10px;letter-spacing:0}'
    + 'html.ms-chat-on #bot > .ms-chat-btn{width:36px;height:36px;flex-basis:36px}}'
    + '@media (max-width:340px){html.ms-chat-on #bot{padding-left:6px;padding-right:6px;gap:4px}'
    + 'html.ms-chat-on #btnMove,html.ms-chat-on #btnH,html.ms-chat-on #btnV{font-size:9px;padding-left:2px;padding-right:2px}'
    + 'html.ms-chat-on #bot > #statusTxt{min-width:40px;font-size:9px;letter-spacing:0.5px}'
    + 'html.ms-chat-on #bot > .ms-chat-btn{width:32px;height:32px;flex-basis:32px}}';
  (document.head || document.documentElement).appendChild(style);

  var state = { enabled: false, unread: 0, open: false };
  var button = null;
  var badge = null;

  function post(message) {
    try { window.parent.postMessage(message, parentOrigin || '*'); } catch (_) {}
  }

  function label() {
    if (state.open) return 'Fermer la messagerie';
    if (state.unread > 0) return state.unread + (state.unread > 1 ? ' nouveaux messages' : ' nouveau message');
    return 'Messagerie de la partie';
  }

  function render(previousUnread) {
    document.documentElement.classList.toggle('ms-chat-on', state.enabled);
    if (!button) return;
    button.classList.toggle('ms-open', state.open);
    button.classList.toggle('ms-unread', state.unread > 0 && !state.open);
    badge.textContent = state.unread > 99 ? '99+' : String(state.unread);
    button.setAttribute('aria-label', label());
    button.setAttribute('aria-pressed', state.open ? 'true' : 'false');
    button.title = label();
    if (state.unread > previousUnread && !state.open) {
      button.classList.remove('ms-bump');
      void button.offsetWidth;
      button.classList.add('ms-bump');
    }
  }

  /* Deuxième bouton de la barre : juste après la vue. Quoridor : après
     « Déplacer ». Morpion à cinq : sa barre n'a que le statut. Penalty et
     Chifoumi n'ont pas de barre : le bouton flotte. */
  function mount() {
    button = document.createElement('button');
    button.type = 'button';
    button.className = 'ms-chat-btn';
    button.innerHTML = ICON + '<span class="ms-chat-badge"></span>';
    badge = button.querySelector('.ms-chat-badge');
    button.addEventListener('click', function (event) {
      event.preventDefault();
      event.stopPropagation();
      post({ type: 'mindspille:chat-toggle', gameId: gameId });
    });

    var first = document.getElementById('btn-topview') || document.getElementById('btnMove');
    var bar = document.getElementById('bot');
    if (first && first.parentNode) first.parentNode.insertBefore(button, first.nextSibling);
    else if (bar) bar.insertBefore(button, bar.firstChild);
    else {
      button.classList.add('ms-chat-float');
      document.body.appendChild(button);
    }
    render(state.unread);
  }

  window.addEventListener('message', function (event) {
    if (event.source !== window.parent) return;
    if (parentOrigin && event.origin !== parentOrigin) return;
    var data = event.data;
    if (!data || data.type !== 'mindspille:chat') return;
    if (data.gameId && gameId && data.gameId !== gameId) return;
    var previousUnread = state.unread;
    state.enabled = data.enabled === true;
    state.open = data.open === true;
    var unread = Number(data.unread);
    state.unread = Number.isFinite(unread) && unread > 0 ? Math.floor(unread) : 0;
    render(previousUnread);
  });

  function start() {
    mount();
    /* Un message de l'application envoyé avant que la page n'écoute serait
       perdu : elle attend ce signal pour annoncer l'état de la messagerie. */
    post({ type: 'mindspille:chat-ready', gameId: gameId });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start, { once: true });
  else start();
})();
