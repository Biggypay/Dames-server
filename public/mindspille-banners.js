/*
 * Les bandeaux d'information posés sur le plateau, d'une seule écriture pour
 * tous les jeux.
 *
 * - En haut, ce que la position impose (« Prise obligatoire », « L’adversaire
 *   doit prendre », « Échec au roi ») : juste sous l'en-tête, centré.
 * - En bas, le temps (« Jouez maintenant · défaite dans 56 s », « L’adversaire
 *   doit jouer · 56 s », « Adversaire absent · victoire dans 56 s ») : posé
 *   sur la barre du bas, comme un onglet qui en sort, quelle que soit la façon
 *   dont la page le place ; sans barre du bas (Penalty, Chifoumi), au pied de
 *   l'écran, à côté du bouton de discussion.
 *
 * Toujours sur une ligne (le texte se resserre sur un petit écran plutôt que
 * de passer à la ligne), dans la police de l'application, chiffres de même
 * largeur : le compte à rebours ne fait pas bouger le texte. Une icône dessinée
 * (horloge, éclair, couronne aux échecs) remplace les émojis. La page donne le
 * ton (`data-tone="urgent"` quand c'est au joueur d'agir) ; le reste de la page
 * ne change pas.
 */
(function () {
  'use strict';

  var FONT = "'Inter', system-ui, -apple-system, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif";
  function icon(body) {
    return 'url("data:image/svg+xml,' + encodeURIComponent(
      '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 24 24">' + body + '</svg>'
    ) + '")';
  }
  var LINE = ' fill="none" stroke="#000" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"';
  var ICON = {
    clock: icon('<circle cx="12" cy="12" r="9"' + LINE + '/><path d="M12 7.5V12l3 2"' + LINE + '/>'),
    bolt: icon('<path d="M13.5 2 4.5 13.5H11L10 22l9.5-12H13l.5-8z"/>'),
    crown: icon('<path d="M3 7.5l4.6 4.1L12 4.5l4.4 7.1L21 7.5 19.2 18H4.8L3 7.5zM5 20h14v1.6H5z"/>')
  };

  var B = 'html body ';
  var both = B + '#force-jump-hint,' + B + '#forfeit-bar';
  var css =
    both + '{left:50%;right:auto;transform:translateX(-50%);box-sizing:border-box;'
      + 'width:auto;width:max-content;max-width:calc(100% - 24px);height:32px;padding:0 15px 0 35px;'
      + 'overflow:hidden;white-space:nowrap;text-overflow:ellipsis;text-align:left;'
      + 'font-family:' + FONT + ';font-size:clamp(11px,3.3vw,13px);font-weight:600;font-style:normal;'
      + 'line-height:32px;letter-spacing:0.005em;text-transform:none;'
      + 'font-variant-numeric:tabular-nums;font-feature-settings:"tnum" 1;'
      + 'color:#f8fafc;background:rgba(17,15,46,0.86);border:1px solid rgba(255,255,255,0.14);border-radius:999px;'
      + 'box-shadow:0 8px 24px rgba(0,0,0,0.3);-webkit-backdrop-filter:blur(12px);backdrop-filter:blur(12px);'
      + 'pointer-events:none;animation:none;--ms-accent:#fbbf24}'
    + B + '#force-jump-hint::before,' + B + '#forfeit-bar::before{content:"";position:absolute;left:13px;top:50%;'
      + 'width:15px;height:15px;margin-top:-7.5px;background-color:var(--ms-accent);'
      + '-webkit-mask:var(--ms-icon) center/contain no-repeat;mask:var(--ms-icon) center/contain no-repeat}'
    + B + '#force-jump-hint[data-tone="urgent"],' + B + '#forfeit-bar[data-tone="urgent"]{--ms-accent:#f87171;color:#fee2e2;'
      + 'background:rgba(56,13,26,0.88);border-color:rgba(248,113,113,0.5)}'

    /* En haut : sous l'en-tête. */
    + B + '#force-jump-hint{top:8px;bottom:auto;--ms-icon:' + ICON.bolt + '}'
    + B + '#force-jump-hint[data-kind="check"]{--ms-icon:' + ICON.crown + '}'
    + B + '#force-jump-hint.show{animation:ms-banner-drop .32s cubic-bezier(.22,1,.36,1) both}'

    /* En bas : un onglet qui sort de la barre du bas. */
    + B + '#forfeit-bar{position:fixed;top:auto;bottom:var(--ms-foot,76px);z-index:19;--ms-icon:' + ICON.clock + '}'
    + B + '#forfeit-bar.show{animation:ms-banner-rise .34s cubic-bezier(.22,1,.36,1) both}'
    + 'html.ms-foot-docked body #forfeit-bar{height:34px;line-height:34px;border-bottom:0;border-radius:14px 14px 0 0;'
      + 'background:rgba(30,28,70,0.94);box-shadow:0 -8px 22px rgba(0,0,0,0.22)}'
    + 'html.ms-foot-docked body #forfeit-bar[data-tone="urgent"]{background:rgba(62,16,32,0.95)}'
    /* L'onglet sort de derrière la barre (Quoridor et le Morpion à 5 ne lui
       donnaient pas de plan ; c'est un élément flex, sa mise en page ne bouge pas). */
    + 'html.ms-foot-docked body > #bot{z-index:20}'
    /* Sans barre du bas : au pied de l'écran ; juste au-dessus du bouton de
       discussion quand il flotte là (à côté, le compte à rebours serait coupé
       sur un petit téléphone). */
    + 'html.ms-foot-float body #forfeit-bar{bottom:calc(20px + env(safe-area-inset-bottom,0px))}'
    + 'html.ms-foot-float.ms-chat-on body #forfeit-bar{bottom:calc(68px + env(safe-area-inset-bottom,0px))}'
    /* Le mode d'emploi en bas du plateau s'efface sous l'onglet. */
    + 'html.ms-foot-shown body #hint{opacity:0;transition:opacity .2s}'

    + '@keyframes ms-banner-drop{from{opacity:0;transform:translate(-50%,-8px)}to{opacity:1;transform:translate(-50%,0)}}'
    + '@keyframes ms-banner-rise{from{opacity:0;transform:translate(-50%,100%)}to{opacity:1;transform:translate(-50%,0)}}'

    /* La reconnexion garde sa place, en haut, dans la même police ; de même
       les deux bulles du Penalty (« Choisissez votre zone de tir »,
       « Adversaire réfléchit… »). */
    + B + '#reconn-bar{font-family:' + FONT + ';font-size:12px;font-weight:600;letter-spacing:0.04em}'
    + B + '#status-bar,' + B + '#waiting-badge{font-family:' + FONT + ';font-size:clamp(11px,3.3vw,13px);font-weight:600;'
      + 'letter-spacing:0.01em;text-transform:none}'
    + '@media (prefers-reduced-motion:reduce){' + both + '{animation:none!important}}';

  var style = document.createElement('style');
  style.id = 'mindspille-banners';
  style.textContent = css;
  (document.head || document.documentElement).appendChild(style);

  var root = document.documentElement;

  /* Une ligne, jamais coupée : quand le texte ne tient pas — un très petit
     écran, ou la police de secours, plus large, tant que Inter n'est pas
     arrivée — il se resserre jusqu'à tenir (9 px au plus petit). */
  var MIN_FONT_PX = 9;
  function fit(el) {
    el.style.removeProperty('font-size');
    if (!el.classList.contains('show') || el.scrollWidth <= el.clientWidth + 1) return;
    var size = parseFloat(window.getComputedStyle(el).fontSize) || 13;
    while (size > MIN_FONT_PX && el.scrollWidth > el.clientWidth + 1) {
      size = Math.max(MIN_FONT_PX, size - 0.5);
      el.style.setProperty('font-size', size + 'px', 'important');
    }
  }
  function fitAll() {
    ['force-jump-hint', 'forfeit-bar'].forEach(function (id) {
      var el = document.getElementById(id);
      if (el) fit(el);
    });
  }
  function watchFit() {
    ['force-jump-hint', 'forfeit-bar'].forEach(function (id) {
      var el = document.getElementById(id);
      if (!el) return;
      fit(el);
      /* Le texte change (compte à rebours, traduction) ou le bandeau s'affiche :
         ajusté avant d'être peint. */
      if (typeof MutationObserver === 'function') {
        new MutationObserver(function () { fit(el); })
          .observe(el, { attributes: true, attributeFilter: ['class'], childList: true, characterData: true, subtree: true });
      }
    });
    window.addEventListener('resize', fitAll);
    if (document.fonts) {
      if (document.fonts.addEventListener) document.fonts.addEventListener('loadingdone', fitAll);
      if (document.fonts.ready) document.fonts.ready.then(fitAll, function () {});
    }
  }

  function start() {
    watchFit();
    var bar = document.getElementById('forfeit-bar');
    if (!bar) return;
    var foot = document.getElementById('bot');
    var scheduled = false;

    /* La hauteur entre le bas de l'écran et le haut de la barre du bas. */
    function place() {
      scheduled = false;
      var visible = foot && foot.getClientRects().length > 0;
      root.classList.toggle('ms-foot-docked', !!visible);
      root.classList.toggle('ms-foot-float', !visible);
      if (!visible) return;
      var gap = Math.max(0, Math.round(window.innerHeight - foot.getBoundingClientRect().top));
      root.style.setProperty('--ms-foot', gap + 'px');
    }
    function schedule() {
      if (scheduled) return;
      scheduled = true;
      requestAnimationFrame(place);
    }
    function shown() {
      root.classList.toggle('ms-foot-shown', bar.classList.contains('show'));
    }

    place();
    shown();
    window.addEventListener('resize', schedule);
    window.addEventListener('orientationchange', schedule);
    if (window.visualViewport) window.visualViewport.addEventListener('resize', schedule);
    if (typeof ResizeObserver === 'function') {
      var observer = new ResizeObserver(schedule);
      observer.observe(document.body);
      if (foot) observer.observe(foot);
    }
    /* La barre du bas peut apparaître ou disparaître (vue sans habillage). */
    new MutationObserver(function () { schedule(); shown(); })
      .observe(bar, { attributes: true, attributeFilter: ['class'] });
    new MutationObserver(schedule).observe(document.body, { attributes: true, attributeFilter: ['class', 'style'] });
    if (foot) new MutationObserver(schedule).observe(foot, { attributes: true, attributeFilter: ['class', 'style'] });
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start, { once: true });
  else start();
})();
