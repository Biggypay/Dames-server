/* Mindspille — l'en-tête des plateaux en ligne : les profils et les manches
 * (owner, 2026-10-25).
 *
 * 1. Un profil montre TOUJOURS le joueur : sa photo, sinon l'initiale de son
 *    pseudo — jamais un pion, un symbole ou un émoji à sa place. Les pages
 *    appellent MindspilleHud.paint(avatar, url) ; un gardien remet le
 *    portrait si un ancien code de la page y écrit encore une pastille. Le
 *    joueur qui attend son tour est pâle (`.profile:not(.active)`, dans les
 *    pages).
 * 2. Sous le nom, le camp du joueur quand le jeu en a un :
 *    MindspilleHud.side(profil, 'x' | 'o' | 'white' | 'red').
 * 3. Les manches décisives (égalité après les manches prévues, mort subite)
 *    ont leur propre rangée, sous les manches prévues :
 *    MindspilleHud.decisive(rangée, résultats, enCours).
 *
 * Chargé dans <head>, avant le script de la page : il ne touche au document
 * qu'une fois celui-ci prêt.
 */
(function () {
  'use strict';
  if (window.MindspilleHud) return;

  var FONT = "Inter, system-ui, -apple-system, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif";
  var CSS = [
    '.profile-avatar .ms-initial{display:flex;align-items:center;justify-content:center;width:100%;height:100%;border-radius:50%;',
    'background:linear-gradient(145deg,#41465e,#262a3d);color:#fff;font:700 21px/1 ' + FONT + ';letter-spacing:0;text-transform:uppercase;',
    '-webkit-user-select:none;user-select:none;pointer-events:none}',
    '.profile-side{display:flex;align-items:center;justify-content:center;gap:4px;min-height:13px;margin-top:-1px;',
    'font:600 10px/1.2 ' + FONT + ';letter-spacing:.2px;color:rgba(255,255,255,.66);white-space:nowrap}',
    '.profile-side .ms-sym{font-size:12px;font-weight:700;line-height:1}',
    '.profile-side .ms-sym.x{color:#e2e8f0}',
    '.profile-side .ms-sym.o{color:#f87171}',
    '.profile-side .ms-dot{width:8px;height:8px;border-radius:50%;flex:0 0 8px}',
    '.profile-side .ms-dot.white{background:radial-gradient(circle at 35% 35%,#faf6ea,#b9b19f);box-shadow:0 0 0 1px rgba(255,255,255,.35)}',
    '.profile-side .ms-dot.red{background:radial-gradient(circle at 35% 35%,#ea4d3b,#8c1b1b);box-shadow:0 0 0 1px rgba(255,120,100,.35)}',
    /* Les manches décisives : une rangée sous les manches prévues. */
    '.rounds-decisive{display:flex;align-items:center;justify-content:center;gap:5px;margin-top:4px;max-width:100%}',
    '.rounds-decisive[hidden]{display:none}',
    '.rounds-decisive .ms-dec-lbl{font:700 8px/1 ' + FONT + ';letter-spacing:1.1px;text-transform:uppercase;color:#fbbf24;margin-right:2px;white-space:nowrap}',
    '.rounds-decisive .ms-dec-dot{width:18px;height:6px;border-radius:3px;background:rgba(255,255,255,.08);',
    'box-shadow:inset 0 0 0 1px rgba(251,191,36,.75);transition:background .3s ease,box-shadow .3s ease}',
    '.rounds-decisive .ms-dec-dot.win{background:#22c55e}',
    '.rounds-decisive .ms-dec-dot.lose{background:#ef4444}',
    '.rounds-decisive .ms-dec-dot.draw{background:#fbbf24}',
    '.rounds-decisive .ms-dec-dot.played{background:rgba(255,255,255,.22)}',
    '.rounds-decisive .ms-dec-dot.current{background:rgba(251,191,36,.35);box-shadow:inset 0 0 0 1px #fbbf24,0 0 8px rgba(251,191,36,.55)}'
  ].join('');

  function injectStyle() {
    if (document.getElementById('ms-hud-style')) return;
    var style = document.createElement('style');
    style.id = 'ms-hud-style';
    style.textContent = CSS;
    (document.head || document.documentElement).appendChild(style);
  }
  injectStyle();

  // ── 1. Le portrait ────────────────────────────────────────────────────────

  var states = typeof WeakMap === 'function' ? new WeakMap() : null;
  function stateOf(host) { return states ? states.get(host) : host.__msState; }
  function setState(host, state) { if (states) states.set(host, state); else host.__msState = state; }

  function nameOf(host) {
    var profile = host.closest ? host.closest('.profile') : null;
    var name = profile && profile.querySelector('.profile-name');
    return name ? String(name.textContent || '').trim() : '';
  }
  function initialOf(name) {
    var s = String(name || '').trim().replace(/^@+/, '');
    var first = s ? (Array.from ? Array.from(s)[0] : s.charAt(0)) : '';
    return first ? first.toLocaleUpperCase('fr') : '?';
  }
  function isPortrait(node) {
    return !!node && node.nodeType === 1 && (node.classList.contains('ms-initial') || node.classList.contains('profile-photo'));
  }
  /* Ce qu'une page pose PAR-DESSUS le portrait (la couronne des Dames, le ballon
     ou la cage du Penalty) reste. */
  function isBadge(node) {
    return !!node && node.nodeType === 1 && (node.classList.contains('king-badge') || node.classList.contains('role-badge'));
  }
  /** Le portrait seul (photo ou initiale), suivi au plus de ses insignes. */
  function portraitOf(host) {
    var nodes = host.childNodes;
    if (!nodes.length || !isPortrait(nodes[0])) return null;
    for (var i = 1; i < nodes.length; i++) if (!isBadge(nodes[i])) return null;
    return nodes[0];
  }
  function put(host, node) {
    var badges = [];
    for (var i = 0; i < host.childNodes.length; i++) if (isBadge(host.childNodes[i])) badges.push(host.childNodes[i]);
    host.innerHTML = '';
    host.appendChild(node);
    for (var j = 0; j < badges.length; j++) host.appendChild(badges[j]);
  }
  function drawInitial(host) {
    var letter = initialOf(nameOf(host));
    var current = portraitOf(host);
    if (current && current.classList.contains('ms-initial') && current.textContent === letter) return;
    var span = document.createElement('span');
    span.className = 'ms-initial';
    span.setAttribute('aria-hidden', 'true');
    span.textContent = letter;
    put(host, span);
  }
  function restore(host) {
    var state = stateOf(host);
    if (state && state.img) {
      if (portraitOf(host) !== state.img) put(host, state.img);
    } else {
      drawInitial(host);
    }
  }
  function watch(host) {
    if (host.__msWatched || typeof MutationObserver !== 'function') return;
    host.__msWatched = true;
    // Un ancien code de la page (pastille de repli, symbole du tour) écrit
    // dans l'avatar : on remet le portrait avant l'affichage.
    new MutationObserver(function () {
      var portrait = portraitOf(host);
      if (portrait) {
        if (portrait.classList.contains('profile-photo')) {
          var state = stateOf(host);
          if (!state || state.img !== portrait) setState(host, { url: portrait.currentSrc || portrait.src || '', img: portrait });
        }
        return;
      }
      restore(host);
    }).observe(host, { childList: true });
    // L'initiale suit le pseudo (le nom arrive parfois après le premier dessin).
    var profile = host.closest ? host.closest('.profile') : null;
    var name = profile && profile.querySelector('.profile-name');
    if (name) {
      new MutationObserver(function () {
        var state = stateOf(host);
        if (!state || !state.img) drawInitial(host);
      }).observe(name, { childList: true, characterData: true, subtree: true });
    }
  }

  function paint(host, url) {
    if (typeof host === 'string') host = document.getElementById(host);
    if (!host) return;
    watch(host);
    url = typeof url === 'string' ? url.trim() : '';
    var current = stateOf(host);
    if (current && current.url === url && (current.img || current.pending || !url)) {
      restore(host);
      return;
    }
    var state = { url: url, img: null, pending: !!url };
    setState(host, state);
    drawInitial(host);
    if (!url) return;
    var img = new Image();
    img.className = 'profile-photo';
    img.alt = '';
    img.referrerPolicy = 'no-referrer';
    img.onload = function () {
      if (stateOf(host) !== state) return;
      state.pending = false;
      state.img = img;
      restore(host);
    };
    img.onerror = function () {
      if (stateOf(host) !== state) return;
      state.pending = false;
      state.img = null;
      drawInitial(host);
    };
    img.src = url;
  }

  // ── 2. Le camp, sous le nom ───────────────────────────────────────────────

  var SIDES = {
    x: { mark: '<span class="ms-sym x">✗</span>', label: 'Croix' },
    o: { mark: '<span class="ms-sym o">◯</span>', label: 'Ronds' },
    white: { mark: '<span class="ms-dot white"></span>', label: 'Blancs' },
    red: { mark: '<span class="ms-dot red"></span>', label: 'Rouges' }
  };
  function side(profile, kind) {
    if (typeof profile === 'string') profile = document.getElementById(profile);
    if (!profile) return;
    var spec = SIDES[String(kind || '').toLowerCase()] || null;
    var el = profile.querySelector('.profile-side');
    if (!spec) { if (el) el.remove(); return; }
    if (!el) {
      el = document.createElement('div');
      el.className = 'profile-side';
      var name = profile.querySelector('.profile-name');
      if (name && name.nextSibling) profile.insertBefore(el, name.nextSibling);
      else profile.appendChild(el);
    }
    if (el.getAttribute('data-side') === kind) return;
    el.setAttribute('data-side', kind);
    // Le libellé est un nœud texte à lui seul : le traducteur des plateaux le voit entier.
    el.innerHTML = spec.mark + '<span class="ms-side-lbl"></span>';
    el.lastChild.textContent = spec.label;
  }

  // ── 3. Les manches décisives ──────────────────────────────────────────────

  /**
   * results : les manches décisives jouées, dans l'ordre — 'win' | 'lose' |
   * 'draw' | 'played' ; current : une manche décisive est en cours. Rien à
   * montrer : la rangée se cache.
   */
  function decisive(regularRow, results, current) {
    if (typeof regularRow === 'string') regularRow = document.getElementById(regularRow);
    if (!regularRow || !regularRow.parentNode) return;
    var list = Array.isArray(results) ? results.slice(0, 12) : [];
    var row = regularRow.nextElementSibling && regularRow.nextElementSibling.classList.contains('rounds-decisive')
      ? regularRow.nextElementSibling
      : null;
    if (!list.length && !current) { if (row) row.hidden = true; return; }
    if (!row) {
      row = document.createElement('div');
      row.className = 'rounds-decisive';
      row.setAttribute('role', 'group');
      regularRow.parentNode.insertBefore(row, regularRow.nextSibling);
    }
    row.hidden = false;
    var label = list.length + (current ? 1 : 0) > 1 ? 'Manches décisives' : 'Manche décisive';
    row.setAttribute('aria-label', label);
    row.innerHTML = '<span class="ms-dec-lbl"></span>';
    row.firstChild.textContent = label;
    list.forEach(function (result) {
      var dot = document.createElement('span');
      dot.className = 'ms-dec-dot ' + (/^(win|lose|draw)$/.test(result) ? result : 'played');
      row.appendChild(dot);
    });
    if (current) {
      var live = document.createElement('span');
      live.className = 'ms-dec-dot current';
      row.appendChild(live);
    }
  }

  function boot() {
    injectStyle();
    var hosts = document.querySelectorAll('#top .profile-avatar');
    for (var i = 0; i < hosts.length; i++) {
      watch(hosts[i]);
      if (!portraitOf(hosts[i])) restore(hosts[i]);
    }
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
  else boot();

  window.MindspilleHud = { paint: paint, side: side, decisive: decisive, initialOf: initialOf };
})();
