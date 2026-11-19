/*
 * Quoridor — le dessin commun aux trois pages (en ligne, contre l'IA, entre amis).
 *
 * Owner, 2026-11-18 : « on ne peut pas différencier les murs … de l'adversaire, ils sont tous de même
 * couleur, il n'y a pas de score, et pas d'alerte en cas de victoire ou de défaite, l'espace du point de
 * départ des joueurs n'est pas foncé avec une couleur appropriée qui pourra aider à mieux voir où aller et
 * où on sortait … le jeu doit être immersif et intuitif ».
 *
 * - Chaque mur prend la couleur de celui qui l'a posé (Blanc = joueur 1, Rouge = joueur 2) ; le dernier
 *   posé s'illumine un instant. Un mur dont on ne connaît pas l'auteur (salle d'avant) reste doré.
 * - Chaque camp de départ est teinté de la couleur de son joueur, et nommé dans une bande au-dessus et
 *   au-dessous du plateau : « Votre arrivée · camp de X » en haut, « Votre camp · départ » en bas.
 *   L'arrivée du joueur est cerclée d'un pointillé doré.
 * - Le dernier déplacement laisse une trace : la case quittée, cerclée, reliée à la nouvelle.
 * - Un mur se pose en deux temps : le premier toucher le montre à sa place, le second le pose.
 * - En-tête : le score de la série en grand (« 2 – 1 ») et « Manche 4 · 6 ».
 * - Fin de manche et fin de match : une carte en haut de l'écran (le plateau reste lisible dessous),
 *   une lueur sur les bords à la couleur du résultat, la rangée atteinte qui clignote, une vibration.
 *
 * Aucune règle ici : les pages et le serveur gardent la logique du jeu, ce module ne fait que dessiner.
 */
(function (root) {
  'use strict';

  var COLORS = {
    0: { light: '#fde68a', fill: '#fbbf24', deep: '#b45309', rgb: '251,191,36', name: 'Or' },
    1: { light: '#ffffff', fill: '#e2e8f0', deep: '#64748b', rgb: '226,232,240', name: 'Blanc' },
    2: { light: '#fecaca', fill: '#f87171', deep: '#991b1b', rgb: '248,113,113', name: 'Rouge' }
  };
  function color(slot) { return COLORS[slot === 1 || slot === 2 ? slot : 0]; }
  /* Le camp de départ de chaque rangée du bord : la rangée 8 est celle du joueur 1 (Blanc), la 0 celle du 2. */
  function campOwner(row) { return row === 8 ? 1 : row === 0 ? 2 : 0; }
  function goalRow(slot) { return slot === 1 ? 0 : 8; }
  function now() { return (root.performance && performance.now) ? performance.now() : Date.now(); }

  /* ── Grilles des propriétaires de murs ─────────────────────────────── */
  function ownerGrid() {
    var g = [];
    for (var r = 0; r < 8; r++) { g[r] = []; for (var c = 0; c < 8; c++) g[r][c] = 0; }
    return g;
  }
  /* L'état reçu fait foi ; à défaut (ancienne salle, replay), on garde ce que la page savait déjà. */
  function mergeOwners(incoming, walls, known) {
    var out = ownerGrid();
    for (var r = 0; r < 8; r++) for (var c = 0; c < 8; c++) {
      if (!(walls && walls[r] && walls[r][c] === true)) continue;
      var v = incoming && incoming[r] ? Number(incoming[r][c]) : 0;
      if (v !== 1 && v !== 2) v = known && known[r] ? Number(known[r][c]) : 0;
      out[r][c] = v === 1 || v === 2 ? v : 0;
    }
    return out;
  }

  /* ── Dessin ─────────────────────────────────────────────────────────── */
  function roundRect(ctx, x, y, w, h, rad) {
    var r = Math.max(0, Math.min(rad, w / 2, h / 2));
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  /* Plus de cadre autour des camps ni de pointillé autour de l'arrivée (owner, 2026-11-19) : la teinte
     des cases et la bande nommée suffisent. Gardées vides pour une page encore en cache. */
  function drawCampBands() {}

  /* Le style d'une case : les deux camps sont teintés franchement, le reste reste sobre. */
  function cellStyle(row, highlighted) {
    if (highlighted) return { fill: 'rgba(251,191,36,0.30)', stroke: 'rgba(251,191,36,0.75)', width: 1.6 };
    var owner = campOwner(row);
    if (owner) {
      var col = color(owner);
      return { fill: 'rgba(' + col.rgb + ',' + (owner === 1 ? 0.24 : 0.30) + ')', stroke: 'rgba(' + col.rgb + ',0.45)', width: 1 };
    }
    return { fill: 'rgba(255,255,255,0.05)', stroke: 'rgba(255,255,255,0.07)', width: 1 };
  }

  function drawGoal() {}

  function wallFill(ctx, rect, horizontal, owner, glow, alpha) {
    var col = color(owner);
    ctx.save();
    ctx.globalAlpha = alpha == null ? 1 : alpha;
    var grad = horizontal
      ? ctx.createLinearGradient(0, rect.y, 0, rect.y + rect.h)
      : ctx.createLinearGradient(rect.x, 0, rect.x + rect.w, 0);
    grad.addColorStop(0, col.light); grad.addColorStop(0.5, col.fill); grad.addColorStop(1, col.deep);
    ctx.beginPath(); roundRect(ctx, rect.x, rect.y, rect.w, rect.h, Math.min(rect.w, rect.h) / 2);
    ctx.fillStyle = grad; ctx.fill();
    ctx.lineWidth = 1; ctx.strokeStyle = 'rgba(15,10,40,0.45)'; ctx.stroke();
    ctx.restore();
  }

  /* Tous les murs posés, chacun à la couleur de son auteur, nets : aucune lueur (propriétaire, 2026-11-19). */
  function drawWalls(ctx, g, hW, vW, hO, vO, fx) {
    var last = fx && fx.lastWall, t = now();
    for (var r = 0; r < 8; r++) for (var c = 0; c < 8; c++) {
      if (hW[r][c]) {
        var gh = last && last.kind === 'h' && last.r === r && last.c === c ? pulseGlow(last.t0, t) : 0;
        wallFill(ctx, g.hwRect(r, c), true, hO && hO[r] ? hO[r][c] : 0, gh);
      }
      if (vW[r][c]) {
        var gv = last && last.kind === 'v' && last.r === r && last.c === c ? pulseGlow(last.t0, t) : 0;
        wallFill(ctx, g.vwRect(r, c), false, vO && vO[r] ? vO[r][c] : 0, gv);
      }
    }
  }
  function pulseGlow(t0, t) {
    var k = (t - t0) / 1600;
    if (!(k >= 0 && k < 1)) return 0;
    return (1 - k) * (0.6 + 0.4 * Math.sin(k * Math.PI * 6));
  }

  /* L'emplacement choisi, avant de le poser : le mur à sa place, qui respire. */
  function drawPreview(ctx, rect, horizontal, owner) {
    var a = 0.62 + 0.28 * Math.sin(now() / 160);
    wallFill(ctx, rect, horizontal, owner, 0.6, a);
    ctx.save();
    ctx.setLineDash([4, 3]);
    ctx.lineWidth = 1.5; ctx.strokeStyle = 'rgba(255,255,255,0.9)';
    ctx.beginPath(); roundRect(ctx, rect.x - 3, rect.y - 3, rect.w + 6, rect.h + 6, Math.min(rect.w, rect.h) / 2 + 3);
    ctx.stroke(); ctx.restore();
  }

  /* Le dernier déplacement : la case quittée garde une pastille douce de la couleur du pion — sans trait
     ni pointillé (owner, 2026-11-19 : « enlève les petits traits et les contours transparents »). */
  function drawTrail(ctx, g, mv) {
    if (!mv || !mv.from || !mv.to) return;
    var col = color(mv.slot);
    var fx = g.cx(mv.from.c) + g.CS / 2, fy = g.cy(mv.from.r) + g.CS / 2;
    ctx.save();
    ctx.beginPath(); ctx.arc(fx, fy, g.CS * 0.16, 0, Math.PI * 2);
    ctx.fillStyle = 'rgba(' + col.rgb + ',0.28)'; ctx.fill();
    ctx.restore();
  }

  /* Le pion glisse de sa case à la suivante (owner, 2026-11-19 : « rajoute de l'animation dans le
     déplacement des pions ») : 260 ms en décélération, un léger soulèvement au milieu du trajet ; un saut
     par-dessus l'adversaire prend un peu plus. Un retour au camp (nouvelle manche, resynchronisation)
     ne glisse pas : le pion y est posé. */
  var PAWN_MS = 260, pawnAnim = {};
  function reducedMotion() {
    try { return !!(root.matchMedia && matchMedia('(prefers-reduced-motion: reduce)').matches); } catch (_) { return false; }
  }
  function pawnAt(a, t) {
    var k = a.dur ? Math.min(1, Math.max(0, (t - a.t0) / a.dur)) : 1;
    var e = 1 - Math.pow(1 - k, 3);
    return { r: a.from.r + (a.to.r - a.from.r) * e, c: a.from.c + (a.to.c - a.from.c) * e, lift: k < 1 ? Math.sin(Math.PI * k) : 0, moving: k < 1 };
  }
  function animPos(slot, pos, drawFn) {
    if (!pos) return { r: 0, c: 0, lift: 0 };
    var t = now(), a = pawnAnim[slot];
    if (!a) a = pawnAnim[slot] = { from: { r: pos.r, c: pos.c }, to: { r: pos.r, c: pos.c }, t0: 0, dur: 0 };
    if (a.to.r !== pos.r || a.to.c !== pos.c) {
      var cur = pawnAt(a, t), dist = Math.abs(cur.r - pos.r) + Math.abs(cur.c - pos.c);
      if (dist > 2.5 || reducedMotion()) { a.from = { r: pos.r, c: pos.c }; a.dur = 0; }
      else { a.from = { r: cur.r, c: cur.c }; a.dur = PAWN_MS + (dist > 1.5 ? 90 : 0); pulse(drawFn, a.dur + 40); }
      a.to = { r: pos.r, c: pos.c }; a.t0 = t;
    }
    return pawnAt(a, t);
  }
  function pawnMoving(slot) { var a = pawnAnim[slot]; return !!a && pawnAt(a, now()).moving; }

  /* Fin de manche : la rangée atteinte clignote à la couleur du vainqueur, un anneau part de son pion. */
  function drawRoundFx(ctx, g, fx) {
    if (!fx || !fx.t0) return;
    var k = (now() - fx.t0) / 3200;
    if (!(k >= 0 && k < 1)) return;
    var col = color(fx.winner), row = goalRow(fx.winner);
    ctx.save();
    if (fx.winner === 1 || fx.winner === 2) {
      var a = (1 - k) * (0.25 + 0.25 * Math.sin(k * Math.PI * 10));
      for (var c = 0; c < 9; c++) {
        ctx.beginPath(); roundRect(ctx, g.cx(c), g.cy(row), g.CS, g.CS, 4);
        ctx.fillStyle = 'rgba(' + col.rgb + ',' + Math.max(0, a) + ')'; ctx.fill();
      }
    }
    if (fx.pos) {
      var px = g.cx(fx.pos.c) + g.CS / 2, py = g.cy(fx.pos.r) + g.CS / 2, ring = (k * 3) % 1;
      ctx.lineWidth = 3;
      ctx.strokeStyle = 'rgba(' + col.rgb + ',' + (1 - ring) * (1 - k) + ')';
      ctx.beginPath(); ctx.arc(px, py, g.CS * (0.35 + ring * 0.9), 0, Math.PI * 2); ctx.stroke();
    }
    ctx.restore();
  }

  /* Les bandes sont dessinées : le traducteur des plateaux (mindspille-i18n.js) ne lit pas un canevas.
     Il pose la langue choisie sur <html lang>, on la suit ici ; le pseudo ne se traduit jamais. */
  var BAND_WORDS = {
    ht: { arrival: 'ARIVE OU', camp: 'KAN PA W', start: 'depa', campOf: function (n) { return 'kan ' + n; }, CampOf: function (n) { return 'Kan ' + n; }, arrivalOf: function (n) { return 'arive ' + n; } },
    en: { arrival: 'YOUR FINISH', camp: 'YOUR CAMP', start: 'start', campOf: function (n) { return n + '’s camp'; }, CampOf: function (n) { return n + '’s camp'; }, arrivalOf: function (n) { return n + '’s finish'; } },
    es: { arrival: 'TU LLEGADA', camp: 'TU CAMPO', start: 'salida', campOf: function (n) { return 'campo de ' + n; }, CampOf: function (n) { return 'Campo de ' + n; }, arrivalOf: function (n) { return 'llegada de ' + n; } }
  };
  function bandText(text) {
    var lang = String((document.documentElement && document.documentElement.lang) || 'fr').slice(0, 2);
    var w = BAND_WORDS[lang];
    if (!w || !text) return text;
    var m;
    if (text === '▲ VOTRE ARRIVÉE' || text === 'VOTRE ARRIVÉE') return w.arrival;
    if (text === 'VOTRE CAMP') return w.camp;
    if (text === 'départ') return w.start;
    if ((m = /^camp de (.+)$/.exec(text))) return w.campOf(m[1]);
    if ((m = /^Camp de (.+)$/.exec(text))) return w.CampOf(m[1]);
    if ((m = /^arrivée de (.+)$/.exec(text))) return w.arrivalOf(m[1]);
    return text;
  }

  /* Les bandes nommées au-dessus et au-dessous du plateau (coordonnées de l'écran, jamais retournées). */
  function drawBandLabels(ctx, width, height, band, labels) {
    if (!band || !labels) return;
    ctx.save();
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    var size = Math.max(9, Math.min(12, Math.round(band * 0.5)));
    [['top', band / 2], ['bottom', height - band / 2]].forEach(function (entry) {
      var label = labels[entry[0]];
      if (!label || !label.text) return;
      var col = color(label.slot);
      var arrow = /^▲\s*/.test(label.text);
      var text = bandText(label.text).replace(/^▲\s*/, '') + (label.sub ? '  ·  ' + bandText(label.sub) : '');
      ctx.font = '700 ' + size + 'px Inter, system-ui, -apple-system, sans-serif';
      try { ctx.letterSpacing = '1.2px'; } catch (_) {}
      var w = ctx.measureText(text).width, y = entry[1];
      /* Une pastille de la couleur du camp, puis le texte. */
      var dot = size * 0.42, x0 = width / 2 - w / 2 - dot * 2.2;
      if (arrow) {
        /* L'arrivée : un chevron doré à la place de la pastille. */
        ctx.save();
        ctx.lineCap = 'round'; ctx.lineJoin = 'round';
        ctx.lineWidth = Math.max(1.6, size * 0.17);
        ctx.strokeStyle = 'rgba(251,191,36,0.98)';
        drawChevron(ctx, x0 + dot, y + dot * 0.15, dot * 1.05, -1);
        ctx.restore();
      } else {
        ctx.beginPath(); ctx.arc(x0 + dot, y, dot, 0, Math.PI * 2);
        ctx.fillStyle = col.fill; ctx.fill();
      }
      ctx.fillStyle = label.gold ? 'rgba(251,191,36,0.98)' : 'rgba(' + col.rgb + ',0.92)';
      ctx.fillText(text, width / 2 + dot * 1.1, y + 0.5);
    });
    ctx.restore();
  }

  /* La hauteur de chaque bande nommée, selon la taille des cases ; aucune quand la place manque
     (téléphone couché sans l'application autour) : les camps restent teintés et l'arrivée cerclée. */
  function bandHeight(cs, freeHeight) {
    if (freeHeight != null && freeHeight < 300) return 0;
    return Math.max(16, Math.min(26, Math.round(cs * 0.42)));
  }

  /* ── Animation : quelques images seulement, le temps d'un effet ─────── */
  var anim = { raf: 0, until: 0, hold: false, draw: null };
  function step() {
    anim.raf = 0;
    if (anim.draw) { try { anim.draw(); } catch (_) {} }
    if (anim.hold || now() < anim.until) anim.raf = requestAnimationFrame(step);
  }
  function pulse(drawFn, ms) {
    anim.draw = drawFn;
    anim.until = Math.max(anim.until, now() + (ms || 1600));
    if (!anim.raf) anim.raf = requestAnimationFrame(step);
  }
  function hold(drawFn, on) {
    anim.draw = drawFn;
    anim.hold = !!on;
    if (on && !anim.raf) anim.raf = requestAnimationFrame(step);
  }

  /* ── En-tête : le score et la manche ────────────────────────────────── */
  var STYLE = [
    'html body .q-score{display:flex;align-items:baseline;justify-content:center;gap:10px;margin-top:2px;font-family:Inter,system-ui,sans-serif;font-variant-numeric:tabular-nums;line-height:1}',
    'html body .q-score .snum{font-size:26px;font-weight:800;min-width:20px;text-align:center;transition:transform .25s ease}',
    'html body .q-score .snum.q-bump{transform:scale(1.35)}',
    'html body .q-score .q-sep{font-size:16px;font-weight:600;color:rgba(255,255,255,.4)}',
    'html body .q-manche{font-family:Inter,system-ui,sans-serif;font-size:10px;font-weight:600;letter-spacing:.08em;text-transform:uppercase;color:rgba(255,255,255,.6);margin-top:3px;white-space:nowrap}',
    'html body .q-manche[data-decisive="1"]{color:#fbbf24}',
    'html body .top-center h1{font-size:13px!important;letter-spacing:4px!important}',
    'html body .top-center .sub{display:none!important}',
    'html body .bet-badge{margin-top:6px!important}',
    'html body .goal-hint{font-family:Inter,system-ui,sans-serif!important;font-size:10px!important;font-weight:600;letter-spacing:.02em!important;color:rgba(255,255,255,.72)!important;white-space:nowrap;display:inline-flex!important;align-items:center;gap:3px}',
    'html body .goal-hint .q-chev{width:11px;height:11px;flex:none;color:rgba(255,255,255,.55)}',
    'html body .goal-hint[data-dir="up"] .q-chev{color:#fbbf24}',
    'html body .walls-badge{gap:5px!important;font-family:Inter,system-ui,sans-serif}',
    'html body .q-wall-chip{display:inline-block;width:16px;height:5px;border-radius:3px;background:var(--q-c,#fbbf24);}',
    /* La carte de fin de manche : en haut, au-dessus de l'en-tête, le plateau reste lisible. */
    'html body #q-result{position:fixed;left:50%;top:calc(env(safe-area-inset-top,0px) + 10px);z-index:170;display:flex;align-items:center;gap:12px;'
      + 'max-width:calc(100% - 24px);width:max-content;box-sizing:border-box;padding:10px 16px 10px 12px;border-radius:18px;'
      + 'background:linear-gradient(135deg,rgba(24,20,62,.97),rgba(45,40,110,.97));border:1.5px solid var(--q-tone,#fbbf24);'
      + 'box-shadow:0 14px 40px rgba(0,0,0,.55),0 0 24px var(--q-tone-glow,rgba(251,191,36,.35));font-family:Inter,system-ui,sans-serif;'
      + 'transform:translate(-50%,-140%);opacity:0;transition:transform .42s cubic-bezier(.2,1.2,.3,1),opacity .25s ease;pointer-events:none}',
    'html body #q-result.q-show{transform:translate(-50%,0);opacity:1}',
    'html body #q-result .q-ico{flex:0 0 auto;width:40px;height:40px;border-radius:50%;display:flex;align-items:center;justify-content:center;background:var(--q-tone-soft,rgba(251,191,36,.16));color:var(--q-tone,#fbbf24)}',
    'html body #q-result .q-ico svg{width:24px;height:24px}',
    'html body #q-result .q-body{min-width:0}',
    'html body #q-result .q-title{font-size:16px;font-weight:800;color:var(--q-tone,#fbbf24);line-height:1.2;white-space:nowrap}',
    'html body #q-result .q-sub{font-size:12px;color:rgba(255,255,255,.75);line-height:1.3;margin-top:2px;white-space:normal}',
    'html body #q-result .q-final{flex:0 0 auto;display:flex;align-items:baseline;gap:6px;padding-left:12px;margin-left:2px;border-left:1px solid rgba(255,255,255,.15);font-variant-numeric:tabular-nums}',
    'html body #q-result .q-final b{font-size:24px;font-weight:800;line-height:1}',
    'html body #q-result .q-final i{font-style:normal;color:rgba(255,255,255,.45);font-size:14px}',
    'html body #q-flash{position:fixed;inset:0;pointer-events:none;z-index:165;opacity:0;box-shadow:inset 0 0 70px 18px var(--q-tone-glow,rgba(251,191,36,.5));transition:opacity .5s ease}',
    'html body #q-flash.q-show{opacity:1;transition:opacity .12s ease}',
    /* Un petit écran : les six repères de manche rétrécissent au lieu de pousser le profil de droite hors de l'écran. */
    'html body #top .rounds-progress{max-width:100%}',
    'html body #top .round-dot{flex:0 1 24px;min-width:8px}',
    '@media (max-width:360px){html body #top .profile{min-width:58px!important}html body .goal-hint{font-size:9px!important}html body .q-score .snum{font-size:22px}html body .q-score{gap:7px}}',
    '@media (max-width:360px){html body #q-result{gap:9px;padding:9px 12px 9px 10px}html body #q-result .q-title{font-size:14px}html body #q-result .q-final b{font-size:20px}}',
    '@media (prefers-reduced-motion:reduce){html body #q-result{transition:opacity .2s ease}html body .q-score .snum{transition:none}}'
  ].join('\n');
  function injectStyle() {
    if (document.getElementById('quoridor-ui-style')) return;
    var s = document.createElement('style');
    s.id = 'quoridor-ui-style';
    s.textContent = STYLE;
    (document.head || document.documentElement).appendChild(s);
  }
  injectStyle();

  /* Le score de la série (« 2 – 1 ») et « Manche 4 · 6 », sous le titre. Les deux `.snum` et
     `.manche-lbl` sont lus par mindspille-split.js pour le panneau de l'application. */
  function setScore(center, mine, theirs, label, mineSlot, theirSlot, decisive) {
    if (!center) return;
    var row = center.querySelector('.q-score');
    if (!row) {
      row = document.createElement('div');
      row.className = 'score-row q-score';
      row.innerHTML = '<span class="snum" data-q="me">0</span><span class="q-sep">–</span><span class="snum" data-q="op">0</span>';
      var lbl = document.createElement('div');
      lbl.className = 'manche-lbl q-manche';
      var h1 = center.querySelector('h1');
      if (h1 && h1.nextSibling) { center.insertBefore(row, h1.nextSibling); center.insertBefore(lbl, row.nextSibling); }
      else { center.appendChild(row); center.appendChild(lbl); }
    }
    var a = row.querySelector('[data-q="me"]'), b = row.querySelector('[data-q="op"]');
    bump(a, mine); bump(b, theirs);
    a.style.color = color(mineSlot).fill; b.style.color = color(theirSlot).fill;
    var l = center.querySelector('.q-manche');
    if (l) { l.textContent = label || ''; l.setAttribute('data-decisive', decisive ? '1' : '0'); }
  }
  function bump(el, value) {
    var text = String(Math.max(0, Number(value) || 0));
    if (el.textContent === text) return;
    var first = el.getAttribute('data-set') !== '1';
    el.textContent = text;
    el.setAttribute('data-set', '1');
    if (first) return;
    el.classList.add('q-bump');
    setTimeout(function () { el.classList.remove('q-bump'); }, 320);
  }
  /* « Manche 4 · 6 », puis « Manche 8 · décisive » en mort subite. */
  function roundLabel(series) {
    var s = series || {}, regular = Number(s.regularRounds) || 6;
    var played = Number(s.roundsPlayed) || 0;
    var w = s.wins || {};
    var tied = (Number(w[1]) || 0) === (Number(w[2]) || 0);
    if (s.suddenDeath && tied) return { text: 'Manche ' + (played + 1) + ' · décisive', decisive: true };
    return { text: 'Manche ' + Math.min(regular, played + 1) + ' · ' + regular, decisive: false };
  }

  function paintChip(el, slot) {
    if (!el) return;
    var col = color(slot);
    el.style.setProperty('--q-c', col.fill);
    el.style.setProperty('--q-g', 'rgba(' + col.rgb + ',0.6)');
  }

  function distanceText(n) {
    if (!(n >= 0) || n >= 999) return '';
    if (n === 0) return 'Arrivé';
    return n === 1 ? '1 case' : n + ' cases';
  }

  /* Le sens de la marche, dessiné (owner, 2026-11-19 : « change le design de la flèche montante… quelque
     chose de plus professionnel ») : un chevron fin, jamais un caractère ▲ / ▼. */
  var CHEVRON = {
    up: '<svg class="q-chev" viewBox="0 0 12 12" aria-hidden="true"><path d="M2.5 8L6 4.5 9.5 8" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>',
    down: '<svg class="q-chev" viewBox="0 0 12 12" aria-hidden="true"><path d="M2.5 4L6 7.5 9.5 4" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/></svg>'
  };
  /* Sous un profil : le chevron, puis « 6 cases » dans son propre nœud (le traducteur des plateaux le lit). */
  function paintGoal(el, text, dir) {
    if (!el) return;
    var key = text ? dir + '|' + text : '';
    if (el.getAttribute('data-goal') === key) return;
    el.setAttribute('data-goal', key);
    el.setAttribute('data-dir', dir);
    if (!text) { el.innerHTML = ''; return; }
    el.innerHTML = (CHEVRON[dir] || CHEVRON.up) + '<span class="q-goal-txt"></span>';
    el.lastChild.textContent = text;
  }

  /* Le geste du départ : trois chevrons au-dessus du pion, qui s'allument l'un après l'autre dans le sens
     de la marche — une vague dorée, sans lueur. `dir` : -1 vers le haut de l'écran, 1 vers le bas. */
  function drawChevron(ctx, x, y, w, dir) {
    var k = dir < 0 ? 1 : -1;
    ctx.beginPath();
    ctx.moveTo(x - w, y + k * w * 0.55);
    ctx.lineTo(x, y - k * w * 0.45);
    ctx.lineTo(x + w, y + k * w * 0.55);
    ctx.stroke();
  }
  function drawDirectionCue(ctx, x, y, cs, dir, redraw) {
    var still = reducedMotion();
    var w = Math.max(7, cs * 0.24), gap = Math.max(7, cs * 0.21), lw = Math.max(2.2, cs * 0.07);
    var base = y + dir * cs * 0.66, t = now() / 1000;
    ctx.save();
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    for (var i = 0; i < 3; i++) {
      var yy = base + dir * i * gap, a;
      if (still || now() - cue.since >= 6000) a = [0.95, 0.7, 0.45][i];
      else {
        var ph = (t / 1.5 - i * 0.17) % 1;
        if (ph < 0) ph += 1;
        a = 0.28 + 0.72 * Math.pow(Math.max(0, Math.sin(ph * Math.PI)), 1.6);
      }
      ctx.lineWidth = lw + 2;
      ctx.strokeStyle = 'rgba(12,8,36,' + (0.32 * a).toFixed(3) + ')';
      drawChevron(ctx, x, yy, w, dir);
      ctx.lineWidth = lw;
      ctx.strokeStyle = 'rgba(251,191,36,' + a.toFixed(3) + ')';
      drawChevron(ctx, x, yy, w, dir);
    }
    ctx.restore();
    /* La vague tourne 6 s à 20 images par seconde, puis reste immobile : le plateau entier se redessine à
       chaque image, un téléphone n'a pas à le faire 60 fois par seconde pendant qu'on réfléchit. */
    var tNow = now();
    if (tNow - cue.last > 1000) cue.since = tNow;
    cue.last = tNow;
    if (!still && redraw && tNow - cue.since < 6000 && !cue.timer) {
      cue.timer = setTimeout(function () { cue.timer = 0; if (!document.hidden) redraw(); }, 50);
    }
  }
  var cue = { since: 0, last: 0, timer: 0 };

  /* ── Fin de manche, fin de match ────────────────────────────────────── */
  var ICONS = {
    trophy: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M8 21h8M12 17v4M7 4h10v4a5 5 0 0 1-10 0z"/><path d="M17 5h3v2a3 3 0 0 1-3 3M7 5H4v2a3 3 0 0 0 3 3"/></svg>',
    flag: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M5 21V4M5 4h11l-2 4 2 4H5"/></svg>',
    scale: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M12 3v18M7 21h10M5 7h14M5 7l-3 6a3 3 0 0 0 6 0zM19 7l-3 6a3 3 0 0 0 6 0z"/></svg>',
    clock: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="9"/><path d="M12 7v5l3 2"/></svg>',
    crown: '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M3 8l4 4 5-7 5 7 4-4-2 11H5z"/></svg>'
  };
  var TONES = {
    win: { tone: '#4ade80', glow: 'rgba(74,222,128,.45)', soft: 'rgba(74,222,128,.16)' },
    lose: { tone: '#f87171', glow: 'rgba(248,113,113,.45)', soft: 'rgba(248,113,113,.16)' },
    draw: { tone: '#fbbf24', glow: 'rgba(251,191,36,.4)', soft: 'rgba(251,191,36,.16)' },
    info: { tone: '#a5b4fc', glow: 'rgba(165,180,252,.4)', soft: 'rgba(165,180,252,.16)' }
  };
  var resultTimer = 0, flashTimer = 0;
  function el(id, tag) {
    var node = document.getElementById(id);
    if (!node) { node = document.createElement(tag || 'div'); node.id = id; document.body.appendChild(node); }
    return node;
  }
  function applyTone(node, tone) {
    var t = TONES[tone] || TONES.info;
    node.style.setProperty('--q-tone', t.tone);
    node.style.setProperty('--q-tone-glow', t.glow);
    node.style.setProperty('--q-tone-soft', t.soft);
  }
  function escape(text) {
    return String(text == null ? '' : text).replace(/[&<>"]/g, function (ch) {
      return { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[ch];
    });
  }
  /* opts : { tone: 'win'|'lose'|'draw'|'info', icon, title, sub, score: [a, b], scoreSlots: [s1, s2], ms } */
  function showResult(opts) {
    var o = opts || {};
    var card = el('q-result');
    card.setAttribute('role', 'status');
    card.setAttribute('aria-live', 'polite');
    applyTone(card, o.tone);
    var icon = ICONS[o.icon] || ICONS[o.tone === 'win' ? 'trophy' : o.tone === 'lose' ? 'flag' : 'scale'];
    var score = '';
    if (o.score && o.score.length === 2) {
      var s = o.scoreSlots || [1, 2];
      score = '<div class="q-final"><b style="color:' + color(s[0]).fill + '">' + Number(o.score[0] || 0) + '</b><i>–</i><b style="color:'
        + color(s[1]).fill + '">' + Number(o.score[1] || 0) + '</b></div>';
    }
    /* Le titre et le sous-titre restent deux nœuds de texte entiers : le traducteur des plateaux les reconnaît. */
    card.innerHTML = '<div class="q-ico">' + icon + '</div><div class="q-body"><div class="q-title">' + escape(o.title)
      + '</div>' + (o.sub ? '<div class="q-sub">' + escape(o.sub) + '</div>' : '') + '</div>' + score;
    card.classList.remove('q-show');
    void card.offsetWidth;
    card.classList.add('q-show');
    clearTimeout(resultTimer);
    if (o.ms !== 0) resultTimer = setTimeout(hideResult, o.ms || 3400);
    flash(o.tone);
    if (o.tone === 'win') vibrate([30, 50, 70]);
    else if (o.tone === 'lose') vibrate([140]);
  }
  function hideResult() {
    clearTimeout(resultTimer);
    var card = document.getElementById('q-result');
    if (card) card.classList.remove('q-show');
  }
  function flash(tone) {
    var f = el('q-flash');
    applyTone(f, tone);
    f.classList.add('q-show');
    clearTimeout(flashTimer);
    flashTimer = setTimeout(function () { f.classList.remove('q-show'); }, 700);
  }
  function vibrate(pattern) {
    try {
      if (root.matchMedia && matchMedia('(prefers-reduced-motion: reduce)').matches) return;
      if (navigator.vibrate) navigator.vibrate(pattern);
    } catch (_) {}
  }

  /* La fiche de fin de match (#gameOverModal) : une icône, le titre, le score final. */
  function decorateMatchCard(opts) {
    var o = opts || {};
    var title = document.getElementById('modalTitle');
    var box = document.getElementById('modalContent');
    if (!title || !box) return;
    var tone = TONES[o.tone] || TONES.info;
    title.innerHTML = '<span class="q-match-ico" style="display:inline-flex;vertical-align:-4px;margin-right:8px;color:' + tone.tone
      + '">' + (ICONS[o.icon] || ICONS[o.tone === 'win' ? 'crown' : 'flag']).replace('<svg ', '<svg width="24" height="24" ')
      + '</span><span>' + escape(o.title) + '</span>';
    var fs = box.querySelector('.final-score');
    if (!fs) {
      fs = document.createElement('div');
      fs.className = 'final-score';
      fs.style.cssText = 'font-family:Inter,system-ui,sans-serif;font-weight:800;font-variant-numeric:tabular-nums;margin:2px 0 6px';
      box.insertBefore(fs, title.nextSibling);
    }
    if (o.score && o.score.length === 2) {
      var s = o.scoreSlots || [1, 2];
      fs.innerHTML = '<span style="color:' + color(s[0]).fill + '">' + Number(o.score[0] || 0) + '</span> <span style="color:rgba(255,255,255,.45);font-weight:600">–</span> <span style="color:'
        + color(s[1]).fill + '">' + Number(o.score[1] || 0) + '</span>';
      fs.style.display = '';
    } else fs.style.display = 'none';
    hideResult();
    flash(o.tone);
    if (o.tone === 'win') vibrate([40, 60, 40, 60, 120]);
    else if (o.tone === 'lose') vibrate([200]);
  }

  root.QuoridorUI = {
    COLORS: COLORS,
    color: color,
    campOwner: campOwner,
    goalRow: goalRow,
    ownerGrid: ownerGrid,
    mergeOwners: mergeOwners,
    cellStyle: cellStyle,
    drawCampBands: drawCampBands,
    drawGoal: drawGoal,
    drawWalls: drawWalls,
    drawPreview: drawPreview,
    drawTrail: drawTrail,
    animPos: animPos,
    pawnMoving: pawnMoving,
    drawRoundFx: drawRoundFx,
    drawBandLabels: drawBandLabels,
    bandHeight: bandHeight,
    pulse: pulse,
    hold: hold,
    setScore: setScore,
    roundLabel: roundLabel,
    paintChip: paintChip,
    distanceText: distanceText,
    paintGoal: paintGoal,
    drawDirectionCue: drawDirectionCue,
    showResult: showResult,
    hideResult: hideResult,
    decorateMatchCard: decorateMatchCard,
    icons: ICONS
  };
})(typeof window !== 'undefined' ? window : this);
