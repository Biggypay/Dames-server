/*
 * Roulette Royale — le plateau, commun aux trois pages (en ligne, contre
 * l'IA, entre amis).
 *
 * Repris du Casino Royal : la roue cerclée d'or et son moyeu, le pointeur, le
 * résultat qui s'allume. Le reste du Casino Royal (blackjack, mises, jetons,
 * roulette à 37 numéros) a disparu : ici, six couleurs et deux joueurs.
 *
 * Le tour de roue est celui d'un casino (owner, 2026-11-05 : « ralentie au
 * début, elle prend de la vitesse pour aller s'arrêter comme dans les grands
 * jeux de roulette… du suspens ») : un léger élan en arrière, l'accélération,
 * la pleine vitesse, puis une longue décélération où la roue franchit les
 * dernières lignes au ralenti ; le pointeur claque sur chaque taquet. Le
 * point d'arrêt — la case tirée, et l'endroit dans la case, parfois juste
 * après la ligne ou juste avant la suivante — vient du serveur (le sel du
 * tirage scellé) : le spectacle est le même sur tous les écrans et ne change
 * jamais la couleur tirée. En manche décisive (7e, 8e…), le tour dure plus
 * longtemps et le halo de la roue bat comme un cœur, de plus en plus vite.
 *
 * Chaque couleur porte sa forme (cercle, triangle, étoile, carré, losange,
 * hexagone) : on la reconnaît aussi sans distinguer les couleurs.
 *
 * Ce module ne décide rien : il dessine ce que la page lui dit (les règles
 * sont dans roulette-rules.js, le tirage chez le serveur).
 */
(function () {
  'use strict';
  if (window.RouletteBoard) return;
  var R = window.RouletteRules;

  var CSS = [
    '.rr-stage{position:relative;width:var(--rr-size,min(76vw,300px));aspect-ratio:1/1;flex:0 0 auto;margin:6px auto 0;-webkit-user-select:none;user-select:none;container-type:inline-size}',
    '.rr-pointer{position:absolute;top:-7px;left:50%;transform:translateX(-50%);transform-origin:50% 0;width:0;height:0;border-left:13px solid transparent;border-right:13px solid transparent;border-top:25px solid #fbbf24;filter:drop-shadow(0 3px 4px rgba(0,0,0,.6));z-index:4}',
    '.rr-pointer::after{content:"";position:absolute;left:-5px;top:-22px;width:10px;height:10px;border-radius:50%;background:#fde68a;box-shadow:0 0 6px rgba(253,230,138,.8)}',
    /* La roue tourne dans un cadre rond qui, lui, ne tourne pas : la boîte carrée
       de la roue, une fois tournée, ne déborde jamais de la page. */
    '.rr-rotor-clip{position:absolute;inset:0;border-radius:50%;overflow:hidden}',
    '.rr-rotor{position:absolute;inset:0;border-radius:50%;will-change:transform;transform:rotate(0deg)}',
    '.rr-rotor svg{display:block;width:100%;height:100%;overflow:visible}',
    '.rr-glow{position:absolute;inset:-6%;border-radius:50%;background:radial-gradient(circle,rgba(251,191,36,.28),transparent 62%);pointer-events:none;z-index:0}',
    '.rr-stage.rr-spinning .rr-glow{animation:rr-pulse 1.2s ease-in-out infinite alternate}',
    /* Manche décisive : le halo bat comme un cœur (piloté image par image dans spinTo). */
    /* Un anneau rouge autour de la jante (la roue cache le centre du halo). */
    '.rr-stage.rr-tense .rr-glow{animation:none;inset:-13%;background:radial-gradient(circle closest-side,transparent 74%,rgba(239,68,68,.72) 82%,rgba(244,63,94,.34) 91%,transparent 100%);will-change:transform,opacity}',
    '@keyframes rr-pulse{from{opacity:.55}to{opacity:1}}',
    '.rr-hub{position:absolute;inset:35%;border-radius:50%;z-index:3;display:flex;flex-direction:column;align-items:center;justify-content:center;gap:1px;',
    'background:radial-gradient(circle at 35% 30%,#fde68a,#f59e0b 55%,#b45309);border:3px solid #78350f;color:#3b1d06;',
    'box-shadow:inset 0 2px 6px rgba(255,255,255,.4),0 5px 14px rgba(0,0,0,.5)}',
    '.rr-hub-top{font:700 8.5px/1 Inter,system-ui,sans-serif;font-size:clamp(6.5px,2.9cqw,10px);letter-spacing:1.1px;text-transform:uppercase;opacity:.78;white-space:nowrap;max-width:92%;overflow:hidden;text-overflow:ellipsis}',
    '.rr-hub-main{display:flex;align-items:center;justify-content:center;font:800 20px/1.05 Cinzel,Georgia,serif;font-size:clamp(12px,9cqw,30px);font-variant-numeric:tabular-nums;white-space:nowrap}',
    '.rr-hub-main svg{display:block;width:clamp(16px,11cqw,40px);height:auto;filter:drop-shadow(0 1px 2px rgba(0,0,0,.35))}',
    '.rr-hub.rr-urgent .rr-hub-main{color:#7f1d1d}',
    '.rr-hub.rr-result{color:#fff;text-shadow:0 1px 2px rgba(0,0,0,.45);border-color:rgba(255,255,255,.75);',
    'background:radial-gradient(circle at 34% 28%,rgba(255,255,255,.55),rgba(255,255,255,0) 46%),radial-gradient(circle,var(--rr-hub,#f59e0b) 58%,var(--rr-hub-deep,#b45309))}',
    /* Sur le jaune, l'écriture et la forme passent en sombre : lisibles. */
    '.rr-hub.rr-result.rr-light{color:#3b2a04;text-shadow:none}',
    '.rr-hub.rr-result.rr-light svg polygon,.rr-hub.rr-result.rr-light svg circle,.rr-hub.rr-result.rr-light svg rect{fill:#3b2a04}',
    '.rr-seg{transition:opacity .35s ease,filter .35s ease}',
    '.rr-rotor.rr-dim .rr-seg{opacity:.38}',
    '.rr-rotor.rr-dim .rr-seg.rr-hit{opacity:1;filter:drop-shadow(0 0 6px rgba(255,255,255,.9))}',
    /* Les deux choix, face à face. */
    '.rr-duel{display:flex;align-items:center;justify-content:center;gap:14px;width:100%}',
    '.rr-pick{display:flex;flex-direction:column;align-items:center;gap:5px;min-width:96px}',
    '.rr-chip{position:relative;width:52px;height:52px;border-radius:50%;display:flex;align-items:center;justify-content:center;',
    'background:rgba(255,255,255,.05);border:2px dashed rgba(255,255,255,.22);color:rgba(255,255,255,.55);font:700 20px/1 Cinzel,serif;transition:transform .3s ease,box-shadow .3s ease,border-color .3s ease,background .3s ease}',
    '.rr-chip svg{width:62%;height:62%}',
    '.rr-chip.rr-waiting{animation:rr-breathe 1.4s ease-in-out infinite}',
    '@keyframes rr-breathe{from{opacity:.55}to{opacity:1}}',
    '.rr-chip.rr-locked{border-style:solid;border-color:rgba(251,191,36,.6);background:rgba(251,191,36,.12);color:#fbbf24}',
    '.rr-chip.rr-color{border:2px solid rgba(255,255,255,.75);box-shadow:0 4px 14px rgba(0,0,0,.4)}',
    '.rr-chip.rr-reveal{animation:rr-flip .45s cubic-bezier(.2,.8,.2,1)}',
    '@keyframes rr-flip{0%{transform:rotateY(90deg) scale(.8)}100%{transform:rotateY(0) scale(1)}}',
    '.rr-chip.rr-winner{transform:scale(1.12);box-shadow:0 0 0 3px #22c55e,0 0 22px rgba(34,197,94,.65)}',
    '.rr-chip.rr-miss{opacity:.55}',
    '.rr-pick-label{font:600 11px/1.2 Inter,system-ui,sans-serif;color:rgba(255,255,255,.62);max-width:110px;text-align:center;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}',
    '.rr-pick-name{font:600 9px/1 Cinzel,serif;letter-spacing:1.4px;text-transform:uppercase;color:rgba(255,255,255,.4);max-width:110px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}',
    '.rr-vs{font:700 18px/1 Cinzel,serif;color:rgba(255,255,255,.28);letter-spacing:2px}',
    /* Les six couleurs. */
    '.rr-palette{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:9px;width:100%;max-width:360px}',
    '.rr-swatch{position:relative;display:flex;align-items:center;gap:9px;min-height:54px;padding:8px 10px;border-radius:14px;cursor:pointer;color:#fff;',
    'background:rgba(255,255,255,.05);border:2px solid rgba(255,255,255,.13);font:600 13px/1.1 Inter,system-ui,sans-serif;text-align:left;',
    '-webkit-tap-highlight-color:transparent;touch-action:manipulation;transition:transform .15s ease,border-color .2s ease,background .2s ease,opacity .2s ease}',
    '.rr-swatch:active{transform:scale(.96)}',
    '.rr-swatch .rr-dot{flex:0 0 28px;width:28px;height:28px;border-radius:50%;display:flex;align-items:center;justify-content:center;box-shadow:inset 0 -3px 6px rgba(0,0,0,.25),0 2px 6px rgba(0,0,0,.35)}',
    '.rr-swatch .rr-dot svg{width:64%;height:64%}',
    '.rr-swatch .rr-name{min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}',
    '@media (hover:hover){.rr-swatch:hover:not(.rr-off){border-color:rgba(255,255,255,.4);background:rgba(255,255,255,.1)}}',
    '.rr-swatch.rr-selected{border-color:#fbbf24;background:rgba(251,191,36,.16);box-shadow:0 0 18px rgba(251,191,36,.35)}',
    '.rr-swatch.rr-selected::after{content:"";position:absolute;top:6px;right:8px;width:8px;height:8px;border-radius:50%;background:#fbbf24;box-shadow:0 0 6px #fbbf24}',
    '.rr-swatch.rr-off{opacity:.32;pointer-events:none;cursor:default}',
    '.rr-swatch.rr-selected.rr-off{opacity:1}',
    /* Les derniers tirages et le sceau. */
    '.rr-foot{display:flex;flex-direction:column;align-items:center;gap:7px;width:100%;max-width:360px}',
    '.rr-history{display:flex;align-items:center;gap:6px;min-height:22px;flex-wrap:nowrap;max-width:100%;overflow:hidden}',
    /* Vide, la bande garde sa place (invisible) : la roue ne rétrécit pas au premier résultat. */
    '.rr-history.rr-empty{visibility:hidden}',
    '.rr-history-lbl{font:600 9px/1 Inter,system-ui,sans-serif;letter-spacing:1px;text-transform:uppercase;color:rgba(255,255,255,.38);white-space:nowrap;margin-right:2px}',
    '.rr-hist{position:relative;width:20px;height:20px;border-radius:50%;flex:0 0 20px;display:flex;align-items:center;justify-content:center;box-shadow:0 1px 4px rgba(0,0,0,.4)}',
    '.rr-hist svg{width:60%;height:60%}',
    '.rr-hist.rr-me{box-shadow:0 0 0 2px #22c55e}',
    '.rr-hist.rr-op{box-shadow:0 0 0 2px #ef4444}',
    '.rr-hist.rr-repick{background:transparent!important;border:2px dashed rgba(255,255,255,.35)}',
    '.rr-seal{display:inline-flex;align-items:center;gap:6px;max-width:100%;padding:5px 11px;border-radius:999px;cursor:pointer;',
    'background:rgba(255,255,255,.05);border:1px solid rgba(255,255,255,.12);color:rgba(255,255,255,.62);font:600 10.5px/1.2 Inter,system-ui,sans-serif;',
    '-webkit-tap-highlight-color:transparent;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}',
    '.rr-seal .rr-hash{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;color:rgba(255,255,255,.78)}',
    '.rr-seal[data-state="verified"]{color:#86efac;border-color:rgba(34,197,94,.45);background:rgba(34,197,94,.08)}',
    '.rr-seal[data-state="failed"]{color:#fca5a5;border-color:rgba(239,68,68,.45)}',
    '.rr-seal[hidden]{display:none}',
    '.rr-seal-box{width:100%;max-width:360px;padding:10px 12px;border-radius:12px;background:rgba(10,8,30,.72);border:1px solid rgba(255,255,255,.12);',
    'font:500 11px/1.45 Inter,system-ui,sans-serif;color:rgba(255,255,255,.72);word-break:break-all}',
    '.rr-seal-box[hidden]{display:none}',
    '.rr-seal-box code{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;color:#fde68a;font-size:10.5px}',
    /* Téléphone couché, petit écran : la roue à gauche, le reste à droite. */
    '@media (orientation:landscape) and (max-height:540px){',
    '.rr-stage{--rr-size:min(62vh,42vw)}',
    '.rr-palette{grid-template-columns:repeat(3,minmax(0,1fr));gap:7px}',
    '.rr-swatch{min-height:42px;padding:6px 8px;font-size:12px}',
    '.rr-swatch .rr-dot{flex-basis:22px;width:22px;height:22px}',
    '.rr-chip{width:42px;height:42px}',
    '}',
    '@media (prefers-reduced-motion:reduce){.rr-chip.rr-waiting,.rr-stage.rr-spinning .rr-glow{animation:none}}'
  ].join('');

  function injectStyle() {
    if (document.getElementById('rr-board-style')) return;
    var style = document.createElement('style');
    style.id = 'rr-board-style';
    style.textContent = CSS;
    (document.head || document.documentElement).appendChild(style);
  }
  injectStyle();

  var NS = 'http://www.w3.org/2000/svg';

  /** La forme d'une couleur, en SVG, centrée sur (x, y). */
  function shapeMarkup(shape, x, y, size, fill, stroke) {
    var s = size, attrs = ' fill="' + fill + '" stroke="' + stroke + '" stroke-width="' + (s * 0.12).toFixed(2) + '" stroke-linejoin="round"';
    function pts(list) { return list.map(function (p) { return (x + p[0] * s).toFixed(2) + ',' + (y + p[1] * s).toFixed(2); }).join(' '); }
    switch (shape) {
      case 'circle': return '<circle cx="' + x + '" cy="' + y + '" r="' + (s * 0.46).toFixed(2) + '"' + attrs + '/>';
      case 'triangle': return '<polygon points="' + pts([[0, -0.56], [0.52, 0.42], [-0.52, 0.42]]) + '"' + attrs + '/>';
      case 'square': return '<rect x="' + (x - s * 0.42).toFixed(2) + '" y="' + (y - s * 0.42).toFixed(2) + '" width="' + (s * 0.84).toFixed(2) + '" height="' + (s * 0.84).toFixed(2) + '" rx="' + (s * 0.08).toFixed(2) + '"' + attrs + '/>';
      case 'diamond': return '<polygon points="' + pts([[0, -0.58], [0.46, 0], [0, 0.58], [-0.46, 0]]) + '"' + attrs + '/>';
      case 'hexagon': {
        var hex = [];
        for (var i = 0; i < 6; i++) { var a = Math.PI / 6 + i * Math.PI / 3; hex.push([Math.cos(a) * 0.5, Math.sin(a) * 0.5]); }
        return '<polygon points="' + pts(hex) + '"' + attrs + '/>';
      }
      case 'star': default: {
        var star = [];
        for (var k = 0; k < 10; k++) { var r = k % 2 ? 0.25 : 0.58, b = -Math.PI / 2 + k * Math.PI / 5; star.push([Math.cos(b) * r, Math.sin(b) * r]); }
        return '<polygon points="' + pts(star) + '"' + attrs + '/>';
      }
    }
  }

  /** Une couleur dans un petit cercle : pastille, puce, historique. */
  function colorIcon(id, light) {
    var c = R.COLORS[id];
    if (!c) return '';
    return '<svg viewBox="0 0 20 20" aria-hidden="true">' + shapeMarkup(c.shape, 10, 10, 16, light ? 'rgba(255,255,255,.95)' : '#fff', 'rgba(0,0,0,.35)') + '</svg>';
  }

  function point(angleDeg, radius) {
    var a = angleDeg * Math.PI / 180;
    return [100 + radius * Math.sin(a), 100 - radius * Math.cos(a)];
  }

  /** Les cases de la roue (svg 200×200), dans l'ordre des aiguilles d'une montre depuis le haut. */
  function wheelMarkup(wheel) {
    var n = wheel.length, seg = 360 / n, out = ['<svg viewBox="-4 -4 208 208" xmlns="' + NS + '"><defs>'];
    R.COLORS.forEach(function (c) {
      out.push('<radialGradient id="rr-g' + c.id + '" gradientUnits="userSpaceOnUse" cx="100" cy="100" r="100">'
        + '<stop offset="0.32" stop-color="' + c.hex + '"/><stop offset="0.82" stop-color="' + c.hex + '"/><stop offset="1" stop-color="' + c.deep + '"/></radialGradient>');
    });
    out.push('</defs>');
    out.push('<circle cx="100" cy="100" r="101" fill="#1c1408"/>');
    for (var i = 0; i < n; i++) {
      var c = R.COLORS[wheel[i]];
      var a0 = i * seg, a1 = (i + 1) * seg;
      var p0 = point(a0, 96), p1 = point(a1, 96);
      out.push('<path class="rr-seg" data-seg="' + i + '" data-color="' + c.id + '" d="M100,100 L' + p0[0].toFixed(2) + ',' + p0[1].toFixed(2)
        + ' A96,96 0 0 1 ' + p1[0].toFixed(2) + ',' + p1[1].toFixed(2) + ' Z" fill="url(#rr-g' + c.id + ')" stroke="rgba(255,255,255,.55)" stroke-width="1.2"/>');
      var mid = point(a0 + seg / 2, 70);
      out.push('<g class="rr-seg" data-seg="' + i + '" data-color="' + c.id + '">' + shapeMarkup(c.shape, mid[0], mid[1], n > 6 ? 14 : 19, 'rgba(255,255,255,.95)', 'rgba(0,0,0,.28)') + '</g>');
    }
    out.push('<circle cx="100" cy="100" r="97" fill="none" stroke="#fbbf24" stroke-width="6"/>');
    out.push('<circle cx="100" cy="100" r="100.5" fill="none" stroke="#78350f" stroke-width="1.6"/>');
    out.push('<circle cx="100" cy="100" r="93.5" fill="none" stroke="rgba(120,53,15,.85)" stroke-width="1.4"/>');
    for (var j = 0; j < n; j++) {
      var peg = point(j * seg, 97);
      out.push('<circle cx="' + peg[0].toFixed(2) + '" cy="' + peg[1].toFixed(2) + '" r="2.4" fill="#fde68a" stroke="#78350f" stroke-width=".8"/>');
    }
    out.push('</svg>');
    return out.join('');
  }

  /*
   * Le mouvement d'un tour de roue, en temps normalisé u ∈ [0, 1] :
   *   0 → 0,07   l'élan : la roue recule un peu, puis repart (vitesse nulle aux deux bouts) ;
   *   → 0,27     l'accélération (lente au début, de plus en plus vite) ;
   *   → 0,42     la pleine vitesse ;
   *   → 1        le freinage, (1 − s)^2,6 : une longue fin au ralenti, où les
   *              dernières lignes passent une à une sous le pointeur.
   * `progress(u)` : la part du chemin vers l'avant parcourue (table intégrée une fois).
   */
  var MOTION = (function () {
    var WIND_END = 0.07, ACC_END = 0.27, CRUISE_END = 0.42, K = 2.6, N = 720;
    function velocity(u) {
      if (u < WIND_END) return 0;
      if (u < ACC_END) { var x = (u - WIND_END) / (ACC_END - WIND_END); return x * x; }
      if (u < CRUISE_END) return 1;
      return Math.pow(Math.max(0, 1 - (u - CRUISE_END) / (1 - CRUISE_END)), K);
    }
    var table = new Float64Array(N + 1), sum = 0;
    for (var i = 1; i <= N; i++) { sum += (velocity((i - 1) / N) + velocity(i / N)) / (2 * N); table[i] = sum; }
    for (var j = 0; j <= N; j++) table[j] /= sum;
    return {
      progress: function (u) {
        if (u <= 0) return 0;
        if (u >= 1) return 1;
        var x = u * N, k = Math.floor(x);
        return table[k] + (table[Math.min(N, k + 1)] - table[k]) * (x - k);
      },
      /** L'élan en arrière (degrés, ≤ 0) : 0 au départ et au bout de l'élan, sans à-coup. */
      windup: function (u, depth) {
        if (u <= 0 || u >= WIND_END) return 0;
        return -depth * (1 - Math.cos(2 * Math.PI * u / WIND_END)) / 2;
      }
    };
  })();

  /*
   * Le cœur d'une manche décisive : la cadence monte de 76 à 150 battements par
   * minute pendant que la roue ralentit, chaque battement en deux temps
   * (« boum-boum »). `pulse(p)`, p ∈ [0, 1) la place dans le battement : 0 à 1.
   */
  var HEART = {
    bpm: function (u) {
      var x = Math.max(0, Math.min(1, (u - 0.25) / 0.6));
      return 76 + 74 * x * x * (3 - 2 * x);
    },
    pulse: function (p) {
      var lub = Math.exp(-Math.pow((p - 0.06) / 0.045, 2));
      var dub = 0.65 * Math.exp(-Math.pow((p - 0.26) / 0.05, 2));
      return Math.max(lub, dub);
    }
  };

  function mount(opts) {
    var els = opts || {};
    var stage = els.stage;
    stage.classList.add('rr-stage');
    stage.innerHTML = '<div class="rr-glow"></div><div class="rr-pointer"></div><div class="rr-rotor-clip"><div class="rr-rotor"></div></div>'
      + '<div class="rr-hub"><span class="rr-hub-top"></span><span class="rr-hub-main"></span></div>';
    var rotor = stage.querySelector('.rr-rotor');
    var pointer = stage.querySelector('.rr-pointer');
    var glow = stage.querySelector('.rr-glow');
    var hub = stage.querySelector('.rr-hub');
    var hubTop = stage.querySelector('.rr-hub-top');
    var hubMain = stage.querySelector('.rr-hub-main');
    var rotation = 0;
    var currentWheel = null;
    var spinTimer = null;
    var spinFrame = 0;
    var finishSpin = null;
    var reduced = false;
    try { reduced = window.matchMedia('(prefers-reduced-motion: reduce)').matches; } catch (_) {}

    function setWheel(wheel) {
      var key = JSON.stringify(wheel);
      if (key === currentWheel) return;
      currentWheel = key;
      rotor.innerHTML = wheelMarkup(wheel);
    }
    setWheel(R.wheelFor(false));

    function clearHit() {
      rotor.classList.remove('rr-dim');
      Array.prototype.forEach.call(rotor.querySelectorAll('.rr-hit'), function (el) { el.classList.remove('rr-hit'); });
    }
    function markHit(segment) {
      clearHit();
      Array.prototype.forEach.call(rotor.querySelectorAll('[data-seg="' + segment + '"]'), function (el) { el.classList.add('rr-hit'); });
      rotor.classList.add('rr-dim');
    }

    function setPointer(deg) {
      pointer.style.transform = deg ? 'translateX(-50%) rotate(' + deg.toFixed(2) + 'deg)' : '';
    }
    /* Le halo du cœur (manche décisive) : plus vif et un peu plus large à chaque battement. */
    function setGlow(pulse, on) {
      if (!glow) return;
      if (!on) { glow.style.opacity = ''; glow.style.transform = ''; return; }
      glow.style.opacity = (0.3 + 0.7 * pulse).toFixed(3);
      glow.style.transform = 'scale(' + (1 + 0.05 * pulse).toFixed(4) + ')';
    }
    /* Un tour en cours s'arrête net (nouveau tour, remise à zéro) : la promesse se tient quand même. */
    function stopSpin() {
      if (spinFrame) { cancelAnimationFrame(spinFrame); spinFrame = 0; }
      if (spinTimer) { clearTimeout(spinTimer); spinTimer = null; }
      if (finishSpin) { var done = finishSpin; finishSpin = null; done(false); }
    }

    /*
     * Le tour de roue jusqu'à la case `landing` : depuis l'angle actuel,
     * toujours en avant, six tours (quatre pour un tour court), avec l'élan,
     * l'accélération et la longue fin au ralenti de MOTION. Chaque ligne qui
     * passe sous le pointeur le fait claquer, d'autant plus visiblement que la
     * roue ralentit. Un minuteur de secours conclut le tour si l'onglet, caché,
     * ne dessine plus (le résultat n'attend jamais l'image suivante).
     * `options.tension` (manche décisive) : le halo de la roue bat comme un
     * cœur — 76 battements par minute au départ, 150 quand la roue rampe vers
     * la dernière ligne (owner : « ça doit faire battre vite les cœurs »).
     */
    function spinTo(wheel, landing, durationMs, options) {
      stopSpin();
      setWheel(wheel);
      clearHit();
      var target = R.landingAngle(wheel.length, landing);
      var duration = Math.max(0, Number(durationMs) || 0);
      var turns = duration >= 4000 ? 6 : duration > 1200 ? 4 : duration > 300 ? 2 : 0;
      var from = rotation;
      rotation += turns * 360 + ((target - (rotation % 360) + 360) % 360);
      var to = rotation;
      rotor.style.transition = 'none';
      if (reduced || duration < 120) {
        rotor.style.transform = 'rotate(' + to + 'deg)';
        setPointer(0);
        markHit(landing.segment);
        return Promise.resolve();
      }
      stage.classList.add('rr-spinning');
      var seg = 360 / wheel.length;
      var depth = Math.min(9, seg * 0.15);
      var tense = !!(options && options.tension);
      var beat = 0;
      stage.classList.toggle('rr-tense', tense);
      /* Le temps part de l'appel (comme le minuteur de secours), pas de la première image. */
      var started = window.performance && performance.now ? performance.now() : null;
      var lastLine = Math.floor(from / seg), kick = 0, lastFrame = started || 0;
      return new Promise(function (resolve) {
        finishSpin = function (landed) {
          if (spinFrame) { cancelAnimationFrame(spinFrame); spinFrame = 0; }
          if (spinTimer) { clearTimeout(spinTimer); spinTimer = null; }
          finishSpin = null;
          stage.classList.remove('rr-spinning');
          stage.classList.remove('rr-tense');
          setGlow(0, false);
          setPointer(0);
          if (landed !== false) {
            rotor.style.transform = 'rotate(' + to + 'deg)';
            markHit(landing.segment);
          }
          resolve();
        };
        function frame(now) {
          spinFrame = 0;
          if (started === null) { started = now; lastFrame = now; }
          var u = Math.max(0, Math.min(1, (now - started) / duration));
          var angle = from + MOTION.windup(u, depth) + (to - from) * MOTION.progress(u);
          rotor.style.transform = 'rotate(' + angle.toFixed(3) + 'deg)';
          /* Le pointeur : chaque taquet qui passe le pousse (la roue tourne vers la droite en haut). */
          var line = Math.floor(angle / seg);
          var dt = Math.max(0, now - lastFrame);
          lastFrame = now;
          kick *= Math.exp(-dt / 75);
          if (line !== lastLine) { kick = -16; lastLine = line; }
          setPointer(Math.abs(kick) < 0.2 ? 0 : kick);
          if (tense) {
            beat += dt * HEART.bpm(u) / 60000;
            setGlow(HEART.pulse(beat % 1), true);
          }
          if (u >= 1) { if (finishSpin) finishSpin(true); return; }
          spinFrame = requestAnimationFrame(frame);
        }
        spinFrame = requestAnimationFrame(frame);
        spinTimer = setTimeout(function () { spinTimer = null; if (finishSpin) finishSpin(true); }, duration + 250);
      });
    }

    function landNow(wheel, landing) {
      return spinTo(wheel, landing, 0);
    }

    /* Le moyeu : une ligne (« Manche 2 », « Tirage ») et le temps qui reste ;
       la roue arrêtée, il prend la couleur tirée et montre sa forme. */
    function setHub(top, main, tone, colorId) {
      hubTop.textContent = top || '';
      var c = R.isColor(colorId) ? R.COLORS[colorId] : null;
      if (c && (main == null || main === '')) hubMain.innerHTML = colorIcon(c.id);
      else hubMain.textContent = main == null ? '' : String(main);
      hub.classList.toggle('rr-urgent', tone === 'urgent');
      hub.classList.toggle('rr-result', !!c);
      hub.classList.toggle('rr-light', !!c && c.key === 'jaune');
      if (c) { hub.style.setProperty('--rr-hub', c.hex); hub.style.setProperty('--rr-hub-deep', c.deep); }
      else { hub.style.removeProperty('--rr-hub'); hub.style.removeProperty('--rr-hub-deep'); }
    }

    function resetWheel() {
      stopSpin();
      stage.classList.remove('rr-spinning');
      stage.classList.remove('rr-tense');
      setGlow(0, false);
      clearHit();
      setWheel(R.wheelFor(false));
    }

    // ── Les six couleurs à choisir ──
    var palette = els.palette;
    var swatches = [];
    if (palette) {
      palette.classList.add('rr-palette');
      palette.setAttribute('role', 'group');
      palette.innerHTML = '';
      R.COLORS.forEach(function (c) {
        var b = document.createElement('button');
        b.type = 'button';
        b.className = 'rr-swatch';
        b.setAttribute('data-color', String(c.id));
        b.setAttribute('aria-label', c.name);
        b.innerHTML = '<span class="rr-dot" style="background:' + c.hex + '">' + colorIcon(c.id) + '</span><span class="rr-name"></span>';
        b.querySelector('.rr-name').textContent = c.name;
        var fire = function (event) {
          if (event) { event.preventDefault(); event.stopPropagation(); }
          if (b.classList.contains('rr-off')) return;
          if (typeof els.onPick === 'function') els.onPick(c.id);
        };
        b.addEventListener('click', fire);
        palette.appendChild(b);
        swatches.push(b);
      });
    }
    function setPalette(state) {
      var s = state || {};
      swatches.forEach(function (b, id) {
        b.classList.toggle('rr-selected', s.selected === id);
        b.classList.toggle('rr-off', !s.enabled);
        b.setAttribute('aria-pressed', s.selected === id ? 'true' : 'false');
      });
    }

    // ── Les deux choix ──
    var duel = els.duel;
    var picks = {};
    if (duel) {
      duel.classList.add('rr-duel');
      duel.innerHTML = '';
      ['me', 'op'].forEach(function (side, index) {
        if (index === 1) {
          var vs = document.createElement('span'); vs.className = 'rr-vs'; vs.textContent = 'VS'; duel.appendChild(vs);
        }
        var wrap = document.createElement('div');
        wrap.className = 'rr-pick';
        wrap.innerHTML = '<span class="rr-pick-name"></span><span class="rr-chip">?</span><span class="rr-pick-label"></span>';
        duel.appendChild(wrap);
        picks[side] = { name: wrap.querySelector('.rr-pick-name'), chip: wrap.querySelector('.rr-chip'), label: wrap.querySelector('.rr-pick-label') };
      });
    }
    /* Un pseudo n'est jamais traduit (mindspille-i18n.js) ; « Vous » et « IA », si. */
    var UI_NAMES = { 'Vous': true, 'IA': true };
    function setName(p, name) {
      p.name.textContent = name;
      if (UI_NAMES[name]) p.name.removeAttribute('data-player-name');
      else p.name.setAttribute('data-player-name', 'true');
    }
    var LOCK = '<svg viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><rect x="5" y="11" width="14" height="10" rx="2"/><path d="M8 11V8a4 4 0 0 1 8 0v3"/></svg>';
    function setChip(side, state) {
      var p = picks[side];
      if (!p) return;
      var s = state || {};
      /* Sans `kind` : seul le nom change, la puce reste telle quelle. */
      if (s.name !== undefined) setName(p, s.name);
      if (s.kind === undefined) return;
      var chip = p.chip;
      var was = chip.getAttribute('data-color');
      chip.className = 'rr-chip';
      chip.style.background = '';
      if (s.kind === 'color' && R.isColor(s.color)) {
        var c = R.COLORS[s.color];
        chip.classList.add('rr-color');
        chip.style.background = c.hex;
        chip.innerHTML = colorIcon(c.id);
        if (s.reveal && was !== String(c.id)) chip.classList.add('rr-reveal');
        chip.setAttribute('data-color', String(c.id));
        if (s.winner) chip.classList.add('rr-winner');
        if (s.miss) chip.classList.add('rr-miss');
        p.label.textContent = s.label || c.name;
        return;
      }
      chip.removeAttribute('data-color');
      if (s.kind === 'locked') { chip.classList.add('rr-locked'); chip.innerHTML = LOCK; }
      else { chip.innerHTML = '?'; if (s.kind === 'waiting') chip.classList.add('rr-waiting'); }
      p.label.textContent = s.label || '';
    }

    // ── Les derniers tirages ──
    var history = els.history;
    function setHistory(entries) {
      if (!history) return;
      var list = (entries || []).slice(-8);
      history.className = 'rr-history';
      history.innerHTML = '';
      history.hidden = false;
      if (!list.length) {
        history.classList.add('rr-empty');
        history.setAttribute('aria-hidden', 'true');
        return;
      }
      history.removeAttribute('aria-hidden');
      var lbl = document.createElement('span');
      lbl.className = 'rr-history-lbl';
      lbl.textContent = 'Tirages';
      history.appendChild(lbl);
      list.forEach(function (entry) {
        var dot = document.createElement('span');
        dot.className = 'rr-hist';
        if (entry.repick || !R.isColor(entry.drawn)) {
          dot.classList.add('rr-repick');
          dot.title = 'Même couleur — rechoisie';
        } else {
          var c = R.COLORS[entry.drawn];
          dot.style.background = c.hex;
          dot.innerHTML = colorIcon(c.id);
          dot.title = 'Manche ' + entry.round + ' : ' + c.name;
          if (entry.result === 'me') dot.classList.add('rr-me');
          if (entry.result === 'op') dot.classList.add('rr-op');
        }
        history.appendChild(dot);
      });
    }

    setHistory([]);

    // ── Le sceau du tirage ──
    var seal = els.seal;
    var sealBox = els.sealBox;
    var sealDetail = '';
    if (seal) {
      seal.classList.add('rr-seal');
      seal.hidden = true;
      seal.addEventListener('click', function (event) {
        event.preventDefault();
        if (!sealBox || !sealDetail) return;
        sealBox.hidden = !sealBox.hidden;
      });
    }
    if (sealBox) { sealBox.classList.add('rr-seal-box'); sealBox.hidden = true; }
    function shortHash(hash) { return hash ? hash.slice(0, 6) + '…' + hash.slice(-4) : ''; }
    function setSeal(state) {
      if (!seal) return;
      var s = state || {};
      if (!s.hash) { seal.hidden = true; if (sealBox) sealBox.hidden = true; sealDetail = ''; return; }
      seal.hidden = false;
      seal.setAttribute('data-state', s.state || 'sealed');
      var text = s.state === 'verified' ? 'Tirage vérifié' : s.state === 'failed' ? 'Vérification impossible' : 'Tirage scellé';
      seal.innerHTML = '<span aria-hidden="true">' + (s.state === 'verified' ? '✓' : '🔒') + '</span><span class="rr-seal-txt"></span><span class="rr-hash"></span>';
      seal.querySelector('.rr-seal-txt').textContent = text;
      seal.querySelector('.rr-hash').textContent = shortHash(s.hash);
      if (!sealBox) return;
      sealBox.innerHTML = '';
      var intro = document.createElement('div');
      intro.textContent = s.revealed
        ? 'Le tirage a été fait avant vos choix. Empreinte SHA-256 du texte révélé :'
        : 'La couleur de cette manche est déjà tirée et scellée. Son empreinte SHA-256 :';
      sealBox.appendChild(intro);
      var code = document.createElement('code'); code.textContent = s.hash; sealBox.appendChild(code);
      if (s.revealed) {
        var label = document.createElement('div'); label.textContent = 'Texte révélé :'; label.style.marginTop = '6px'; sealBox.appendChild(label);
        var raw = document.createElement('code'); raw.textContent = s.revealed; sealBox.appendChild(raw);
      }
      sealDetail = s.hash;
    }

    var status = els.status;
    function setStatus(text, tone) {
      if (!status) return;
      status.textContent = text || '';
      status.className = 'status' + (text ? ' visible' : '') + (tone ? ' result ' + tone : '');
    }

    return {
      setWheel: setWheel, spinTo: spinTo, landNow: landNow, resetWheel: resetWheel, setHub: setHub,
      setPalette: setPalette, setChip: setChip, setHistory: setHistory, setSeal: setSeal, setStatus: setStatus,
      markHit: markHit, clearHit: clearHit
    };
  }

  /**
   * La roue prend la place qui reste à l'écran, sans jamais faire défiler la
   * page : la hauteur visible sous l'en-tête, moins ce qui s'empile avec elle
   * (en portrait : les deux choix, l'action, les couleurs, les tirages ; en
   * paysage, deux colonnes : seulement les tirages sous la roue).
   * opts : { wrap, board, stage, stack: [éléments empilés en portrait], under: élément sous la roue en paysage, min, max }
   */
  function fitWheel(opts) {
    var wrap = opts.wrap, board = opts.board, stage = opts.stage;
    var stack = opts.stack || [], under = opts.under || null;
    var min = opts.min || 110, max = opts.max || 330;
    var frame = 0;
    function px(v) { return parseFloat(v) || 0; }
    function measure() {
      frame = 0;
      if (!wrap.isConnected) return;
      var ws = window.getComputedStyle(wrap);
      var bs = window.getComputedStyle(board);
      var row = bs.flexDirection === 'row';
      /* Depuis le haut du plateau jusqu'au bas de l'écran : indépendant de la taille de la roue. */
      var height = window.innerHeight - wrap.offsetTop - px(ws.paddingTop) - px(ws.paddingBottom);
      var width = wrap.clientWidth - px(ws.paddingLeft) - px(ws.paddingRight);
      var margin = px(window.getComputedStyle(stage).marginTop);
      var size;
      if (row) {
        var col = stage.parentNode && stage.parentNode !== board ? window.getComputedStyle(stage.parentNode) : bs;
        var below = under && under.offsetParent !== null ? under.offsetHeight + px(col.rowGap) : 0;
        size = Math.min(height - below - margin, width * 0.46, opts.maxLandscape || 420);
      } else {
        var used = 0, count = 0;
        stack.forEach(function (el) { if (el && el.offsetParent !== null) { used += el.offsetHeight; count++; } });
        size = Math.min(height - used - px(bs.rowGap) * count - margin, width * 0.92, max);
      }
      size = Math.max(min, Math.floor(size));
      if (stage.__rrSize !== size) { stage.__rrSize = size; stage.style.width = size + 'px'; }
    }
    function schedule() { if (!frame) frame = requestAnimationFrame(measure); }
    window.addEventListener('resize', schedule);
    window.addEventListener('orientationchange', schedule);
    if (window.visualViewport) window.visualViewport.addEventListener('resize', schedule);
    if (typeof ResizeObserver === 'function') {
      var observer = new ResizeObserver(schedule);
      [wrap].concat(stack, under ? [under] : []).forEach(function (el) { if (el) observer.observe(el); });
      var top = document.getElementById('top');
      if (top) observer.observe(top);
    }
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(schedule, function () {});
    measure();
    return { refresh: schedule };
  }

  /** L'empreinte SHA-256 (hex) d'un texte, ou null si le navigateur ne sait pas la calculer. */
  function sha256Hex(text) {
    try {
      if (!window.crypto || !window.crypto.subtle || typeof TextEncoder !== 'function') return Promise.resolve(null);
      return window.crypto.subtle.digest('SHA-256', new TextEncoder().encode(text)).then(function (buf) {
        var bytes = new Uint8Array(buf), hex = '';
        for (var i = 0; i < bytes.length; i++) hex += (bytes[i] < 16 ? '0' : '') + bytes[i].toString(16);
        return hex;
      }, function () { return null; });
    } catch (_) { return Promise.resolve(null); }
  }

  /**
   * Vérifie le tour de roue révélé : son texte donne bien l'empreinte publiée
   * avant les choix (`published`, quand la page l'a reçue). Rend
   * { ok, text } — ok vaut null quand le navigateur ne sait pas calculer.
   */
  function verifySpin(roomId, spin, published) {
    if (!spin || !spin.seal) return Promise.resolve({ ok: null, text: '' });
    var text = R.sealText(roomId, spin.round, spin.seal.kind, spin.seal.value, spin.seal.salt);
    return sha256Hex(text).then(function (hex) {
      if (!hex) return { ok: null, text: text };
      var ok = hex === spin.seal.hash && (!published || published === spin.seal.hash);
      return { ok: ok, text: text };
    });
  }

  /** Un aléa de 0 à n-1, tiré par le navigateur (IA, entre amis). */
  function randomInt(n) {
    try {
      var buf = new Uint32Array(1), limit = Math.floor(4294967296 / n) * n, v;
      do { window.crypto.getRandomValues(buf); v = buf[0]; } while (v >= limit);
      return v % n;
    } catch (_) {
      return Math.floor(Math.random() * n);
    }
  }
  function randomSalt() {
    var hex = '';
    for (var i = 0; i < 16; i++) { var b = randomInt(256); hex += (b < 16 ? '0' : '') + b.toString(16); }
    return hex;
  }
  /** Un tirage scellé local (IA, entre amis) : même forme que celui du serveur — une couleur, toute manche. */
  function localSeal(roomId, round, decisive) {
    var kind = 'color';
    var value = randomInt(R.COLOR_COUNT);
    var salt = randomSalt();
    return sha256Hex(R.sealText(roomId, round, kind, value, salt)).then(function (hash) {
      return { kind: kind, value: value, salt: salt, hash: hash || '' };
    });
  }

  window.RouletteBoard = { mount: mount, fitWheel: fitWheel, colorIcon: colorIcon, verifySpin: verifySpin, sha256Hex: sha256Hex, randomInt: randomInt, localSeal: localSeal };
})();
