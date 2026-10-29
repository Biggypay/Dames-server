/*
 * mindspille-chess3d.js — le plateau et les pièces des trois pages d'échecs
 * (en ligne, contre l'IA, entre amis). Owner, 2026-10-28 : « des pièces plus
 * raffinées, un aspect plus réel… un vrai plateau en 3D… ne me fais pas des
 * chevaux à l'envers ».
 *
 * Les trois pages avaient chacune leur copie du même code : des cylindres et
 * des boîtes, les Noirs dessinés en rouge, un damier beige et bleu nuit, et
 * des cavaliers qui regardaient LEUR PROPRE camp (les Blancs tournés de 180°
 * vers la 1re rangée, les Noirs vers la 8e). Désormais, un seul module :
 *
 * - des pièces Staunton tournées (LatheGeometry : pied, gorge, perle, fût,
 *   collerette) — tour crénelée, fou à mitre fendue, dame à couronne, roi à
 *   croix — et un cavalier sculpté (une silhouette de tête de cheval extrudée,
 *   arêtes arrondies, museau affiné, oreilles et yeux) ;
 * - Blancs en ivoire, Noirs en ébène : les Noirs ne sont plus rouges ;
 * - chaque cavalier regarde le camp adverse. Les Blancs (rangées 6-7, z > 0)
 *   avancent vers -z, les Noirs vers +z : c'est fixé dans la scène, jamais
 *   dans la caméra, donc aucune vue, aucune rotation ne le retourne ;
 * - un vrai plateau de bois : cases érable et noyer (les teintes du replay de
 *   l'application), cadre en noyer arrondi, filet doré, coordonnées a–h et
 *   1–8 lisibles des deux côtés, comme sur un plateau de tournoi.
 *
 * Les formes sont construites une fois et partagées par toutes les pièces du
 * même type ; mindspille-3d.js ne libère une forme que quand plus rien dans la
 * scène ne l'utilise.
 */
(function () {
  'use strict';
  var THREE = window.THREE;
  if (!THREE || window.MindspilleChess3D) return;

  var PAWN = 1, KNIGHT = 2, BISHOP = 3, ROOK = 4, QUEEN = 5, KING = 6;
  /* Budget : les 32 pièces tiennent en ≈ 60 000 triangles (le rendu logiciel
     des tests et les téléphones modestes paient chaque triangle). Le contour
     d'une pièce tournée reste à moins d'un dixième de pixel du profil dessiné
     sur un téléphone : 24 facettes, et le profil ne garde que les points qui
     s'en écartent de plus de 2,5 millièmes. */
  var LATHE_SEGMENTS = 24;
  var PROFILE_TOLERANCE = 0.0025;
  /* Au-delà de 60° entre deux segments du profil, l'arête est vive. */
  var CREASE = Math.cos(60 * Math.PI / 180);

  /* ── Teintes ───────────────────────────────────────────────────────────── */
  var WOOD = {
    /* Couleurs de matériau : l'éclairage des pages multiplie environ par 1,6.
       Rendu visé : érable #e6d2ad et noyer #8c6145, les teintes du replay. */
    light: 0x958a74,
    dark: 0x5c3d29,
    frame: 0x3b2416,   // noyer foncé du cadre
    base: 0x24160d,    // dessous du plateau
    brass: '#d4ae5a'   // filet et coordonnées
  };
  var SIDES = [
    { body: 0xcfbf9d, roughness: 0.42, env: 0.35, detail: 0x4a3828 },  // ivoire
    { body: 0x2a2320, roughness: 0.27, env: 1.0, detail: 0x0b0908 }    // ébène
  ];

  /* ── Matériaux (un jeu par camp, partagé) ─────────────────────────────── */
  var materialCache = [null, null];
  var envTexture = null;
  function sideMaterials(player) {
    var side = player === 0 ? 0 : 1;
    if (materialCache[side]) return materialCache[side];
    var spec = SIDES[side];
    var body = new THREE.MeshStandardMaterial({ color: spec.body, roughness: spec.roughness, metalness: 0 });
    body.envMapIntensity = spec.env;
    var detail = new THREE.MeshStandardMaterial({ color: spec.detail, roughness: 0.6, metalness: 0 });
    if (envTexture) { body.envMap = envTexture; detail.envMap = envTexture; }
    body.name = side === 0 ? 'chess-ivory' : 'chess-ebony';
    detail.name = body.name + '-detail';
    materialCache[side] = { body: body, detail: detail };
    return materialCache[side];
  }

  /* ── Profils tournés ──────────────────────────────────────────────────── */
  function Profile() { this.pts = []; }
  Profile.prototype.to = function (r, y) {
    this.pts.push(new THREE.Vector2(Math.max(0, r), y));
    return this;
  };
  Profile.prototype.arc = function (cx, cy, radius, a0, a1, steps) {
    for (var i = 1; i <= steps; i++) {
      var a = a0 + (a1 - a0) * i / steps;
      this.to(cx + radius * Math.cos(a), cy + radius * Math.sin(a));
    }
    return this;
  };
  /* Courbe de Bézier cubique depuis le dernier point. */
  Profile.prototype.bez = function (r1, y1, r2, y2, r, y, steps) {
    var p = this.pts[this.pts.length - 1], r0 = p.x, y0 = p.y;
    for (var i = 1; i <= steps; i++) {
      var t = i / steps, u = 1 - t;
      this.to(u * u * u * r0 + 3 * u * u * t * r1 + 3 * u * t * t * r2 + t * t * t * r,
        u * u * u * y0 + 3 * u * u * t * y1 + 3 * u * t * t * y2 + t * t * t * y);
    }
    return this;
  };
  /* Une perle (tore vu en coupe) posée sur le dernier point, vers l'extérieur. */
  Profile.prototype.bead = function (radius, steps) {
    var p = this.pts[this.pts.length - 1];
    return this.arc(p.x, p.y + radius, radius, -Math.PI / 2, Math.PI / 2, steps || 6);
  };

  /* Le pied Staunton commun : semelle arrondie, gorge, perle. Rend la hauteur atteinte. */
  function foot(pf, R) {
    var h = 0.075, e = 0.022;
    pf.to(0, 0).to(R - e, 0);
    pf.arc(R - e, e, e, -Math.PI / 2, 0, 4);
    pf.to(R, h - e);
    pf.arc(R - e, h - e, e, 0, Math.PI / 2, 4);
    pf.bez(R * 0.86, h, R * 0.82, h + 0.012, R * 0.80, h + 0.032, 5);   // gorge
    pf.bead(0.021, 7);                                                // perle
    pf.bez(R * 0.79, h + 0.082, R * 0.74, h + 0.088, R * 0.70, h + 0.092, 4);
    return h + 0.092;
  }

  /* Une collerette : disque arrondi, puis retour au fût. */
  function collar(pf, rIn, rOut, y, thick) {
    var e = Math.min(0.014, thick / 2.2);
    pf.to(rIn, y);
    pf.bez(rIn + (rOut - rIn) * 0.4, y, rOut - e, y + 0.002, rOut - e, y + 0.004, 3);
    pf.arc(rOut - e, y + e + 0.004, e, -Math.PI / 2, 0, 3);
    pf.to(rOut, y + thick - e);
    pf.arc(rOut - e, y + thick - e, e, 0, Math.PI / 2, 3);
    pf.bez(rOut - e - 0.02, y + thick, rIn + 0.01, y + thick, rIn, y + thick + 0.006, 3);
    return y + thick + 0.006;
  }

  /* Douglas-Peucker : ne garde du profil que les points qui s'écartent de plus
     de `tol` de la corde (une ligne droite n'a besoin que de ses deux bouts). */
  function simplify(pts, tol) {
    var keep = new Uint8Array(pts.length), stack = [0, pts.length - 1];
    keep[0] = keep[pts.length - 1] = 1;
    while (stack.length) {
      var b = stack.pop(), a = stack.pop();
      var ax = pts[a].x, ay = pts[a].y, dx = pts[b].x - ax, dy = pts[b].y - ay, len = dx * dx + dy * dy;
      var far = -1, best = tol * tol;
      for (var i = a + 1; i < b; i++) {
        var t = len > 0 ? ((pts[i].x - ax) * dx + (pts[i].y - ay) * dy) / len : 0;
        t = t < 0 ? 0 : t > 1 ? 1 : t;
        var ex = ax + dx * t - pts[i].x, ey = ay + dy * t - pts[i].y, d = ex * ex + ey * ey;
        if (d > best) { best = d; far = i; }
      }
      if (far >= 0) { keep[far] = 1; stack.push(a, far, far, b); }
    }
    return pts.filter(function (p, i) { return keep[i]; });
  }

  /* Le profil tourné autour de l'axe. Les normales viennent du profil : lisses
     dans les courbes, vives aux arêtes (collerettes, perles, gorges), où le
     sommet est dédoublé. LatheGeometry moyennait les faces voisines : il lui
     fallait beaucoup de points pour garder les arêtes nettes. */
  function lathe(pf) {
    var src = [];
    pf.pts.forEach(function (p) {
      var q = src[src.length - 1];
      if (!q || Math.abs(q.x - p.x) + Math.abs(q.y - p.y) > 1e-6) src.push(p);
    });
    var pts = simplify(src, PROFILE_TOLERANCE), n = pts.length, S = LATHE_SEGMENTS, i, c;
    /* Le profil monte le long de la pièce : (dy, -dx) regarde vers l'extérieur. */
    var segN = [];
    for (i = 0; i < n - 1; i++) {
      var dx = pts[i + 1].x - pts[i].x, dy = pts[i + 1].y - pts[i].y, l = Math.sqrt(dx * dx + dy * dy) || 1;
      segN.push([dy / l, -dx / l]);
    }
    /* Un anneau de sommets par point du profil, deux à une arête vive. */
    var rings = [], startOf = [], endOf = [];
    function ring(p, nr, ny) { rings.push([p.x, p.y, nr, ny]); return rings.length - 1; }
    for (i = 0; i < n; i++) {
      var before = i > 0 ? segN[i - 1] : null, after = i < n - 1 ? segN[i] : null;
      if (before && after && before[0] * after[0] + before[1] * after[1] > CREASE) {
        var bx = before[0] + after[0], by = before[1] + after[1], bl = Math.sqrt(bx * bx + by * by) || 1;
        endOf[i - 1] = startOf[i] = ring(pts[i], bx / bl, by / bl);
      } else {
        if (before) endOf[i - 1] = ring(pts[i], before[0], before[1]);
        if (after) startOf[i] = ring(pts[i], after[0], after[1]);
      }
    }
    var positions = new Float32Array(rings.length * S * 3), normals = new Float32Array(rings.length * S * 3);
    for (var k = 0; k < rings.length; k++) {
      for (c = 0; c < S; c++) {
        var phi = c / S * Math.PI * 2, sn = Math.sin(phi), cs = Math.cos(phi), o = (k * S + c) * 3, rg = rings[k];
        positions[o] = rg[0] * sn; positions[o + 1] = rg[1]; positions[o + 2] = rg[0] * cs;
        normals[o] = rg[2] * sn; normals[o + 1] = rg[3]; normals[o + 2] = rg[2] * cs;
      }
    }
    /* Sur l'axe, l'anneau se réduit à un point : un seul triangle par facette. */
    var index = [];
    for (i = 0; i < n - 1; i++) {
      var A = startOf[i] * S, B = endOf[i] * S, axisA = pts[i].x < 1e-9, axisB = pts[i + 1].x < 1e-9;
      for (c = 0; c < S; c++) {
        var c1 = (c + 1) % S;
        if (!axisA) index.push(A + c, A + c1, B + c);
        if (!axisB) index.push(A + c1, B + c1, B + c);
      }
    }
    var geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.BufferAttribute(positions, 3));
    geo.setAttribute('normal', new THREE.BufferAttribute(normals, 3));
    geo.setIndex(index);
    geo.computeBoundingSphere();
    return geo;
  }

  /* ── Extrusions lissées (cavalier, croix, créneaux, cadre) ────────────── */
  /* ExtrudeGeometry calcule une normale par triangle : l'arrondi des arêtes
     paraît facetté. On lisse les parois (groupe 1) en moyennant les normales
     des sommets confondus ; les faces planes (groupe 0) restent nettes. */
  function smoothSides(geo) {
    var pos = geo.attributes.position, nor = geo.attributes.normal;
    var side = geo.groups && geo.groups[1];
    if (!pos || !nor || !side) return geo;
    var acc = {}, a = new THREE.Vector3(), b = new THREE.Vector3(), c = new THREE.Vector3();
    var ab = new THREE.Vector3(), cb = new THREE.Vector3();
    function key(i) {
      return Math.round(pos.getX(i) * 1e4) + ',' + Math.round(pos.getY(i) * 1e4) + ',' + Math.round(pos.getZ(i) * 1e4);
    }
    var end = side.start + side.count;
    for (var i = side.start; i + 2 < end; i += 3) {
      a.fromBufferAttribute(pos, i); b.fromBufferAttribute(pos, i + 1); c.fromBufferAttribute(pos, i + 2);
      cb.subVectors(c, b); ab.subVectors(a, b); cb.cross(ab);
      for (var k = 0; k < 3; k++) {
        var id = key(i + k), v = acc[id];
        if (!v) acc[id] = v = new THREE.Vector3();
        v.add(cb);
      }
    }
    for (var j = side.start; j < end; j++) {
      var s = acc[key(j)];
      if (s && s.lengthSq() > 0) { s = s.clone().normalize(); nor.setXYZ(j, s.x, s.y, s.z); }
    }
    nor.needsUpdate = true;
    return geo;
  }

  function extrude(shape, depth, bevel, bevelSegments, curveSegments) {
    var geo = new THREE.ExtrudeGeometry(shape, {
      depth: depth, bevelEnabled: bevel > 0, bevelThickness: bevel, bevelSize: bevel * 0.9,
      bevelOffset: 0, bevelSegments: bevelSegments || 3, curveSegments: curveSegments || 10, steps: 1
    });
    return geo;
  }

  /* ── Les pièces ───────────────────────────────────────────────────────── */
  var geometryCache = {};

  function pawnParts() {
    var pf = new Profile(), y = foot(pf, 0.30);
    pf.bez(0.17, y + 0.02, 0.105, y + 0.07, 0.098, 0.30, 6);          // fût en gorge
    y = collar(pf, 0.094, 0.162, 0.30, 0.034);
    pf.to(0.082, y + 0.012);
    var cy = 0.455, rr = 0.112, a0 = -Math.acos(0.080 / rr);
    pf.to(rr * Math.cos(a0), cy + rr * Math.sin(a0));
    pf.arc(0, cy, rr, a0, Math.PI / 2, 14);                           // tête
    return [{ geo: lathe(pf), mat: 'body' }];
  }

  function rookParts() {
    var pf = new Profile(), y = foot(pf, 0.36);
    pf.bez(0.24, y + 0.05, 0.205, y + 0.15, 0.205, 0.43, 6);          // tour légèrement galbée
    pf.bez(0.205, 0.46, 0.235, 0.475, 0.255, 0.49, 4);
    pf.bead(0.012, 4);
    pf.to(0.262, 0.52).to(0.268, 0.60);
    pf.arc(0.256, 0.60, 0.012, 0, Math.PI / 2, 3);
    pf.to(0.19, 0.612).to(0.186, 0.585).to(0, 0.585);                  // tête creuse
    var parts = [{ geo: lathe(pf), mat: 'body' }];
    /* Cinq merlons : des secteurs d'anneau extrudés vers le haut. */
    var count = 5, gap = 0.36, span = (Math.PI * 2) / count - gap;
    for (var i = 0; i < count; i++) {
      var a0 = i * (Math.PI * 2) / count + gap / 2, a1 = a0 + span;
      var sh = new THREE.Shape();
      sh.moveTo(Math.cos(a0) * 0.196, Math.sin(a0) * 0.196);
      sh.absarc(0, 0, 0.256, a0, a1, false);
      sh.lineTo(Math.cos(a1) * 0.196, Math.sin(a1) * 0.196);
      sh.absarc(0, 0, 0.196, a1, a0, true);
      var g = extrude(sh, 0.07, 0.010, 2, 4);
      g.rotateX(-Math.PI / 2);
      g.translate(0, 0.602, 0);
      g.computeVertexNormals();
      smoothSides(g);
      parts.push({ geo: g, mat: 'body' });
    }
    return parts;
  }

  /* Ligne sombre de la fente de la mitre : l'intersection d'un plan incliné et
     de la surface tournée, légèrement décollée, en tube fin. */
  function mitreSlit(radiusAt, yMin, yMax) {
    var n = new THREE.Vector3(0.62, 0.78, 0).normalize();   // plan incliné vers +x
    var d = n.dot(new THREE.Vector3(0.05, 0.705, 0));
    var pts = [];
    for (var k = 0; k <= 24; k++) {
      var phi = -1.25 + 2.5 * k / 24;
      var cos = Math.cos(phi), sin = Math.sin(phi);
      var f = function (yy) { var r = radiusAt(yy); return n.x * r * cos + n.y * yy + n.z * r * sin - d; };
      var lo = yMin, hi = yMax, flo = f(lo), fhi = f(hi);
      if (flo * fhi > 0) continue;
      for (var it = 0; it < 30; it++) {
        var mid = (lo + hi) / 2, fm = f(mid);
        if (flo * fm <= 0) { hi = mid; } else { lo = mid; flo = fm; }
      }
      var yy = (lo + hi) / 2, r = radiusAt(yy) + 0.003;
      pts.push(new THREE.Vector3(r * cos, yy, r * sin));
    }
    if (pts.length < 4) return null;
    return new THREE.TubeGeometry(new THREE.CatmullRomCurve3(pts), 20, 0.011, 5, false);
  }

  function bishopParts() {
    var pf = new Profile(), y = foot(pf, 0.345);
    pf.bez(0.20, y + 0.03, 0.115, y + 0.12, 0.105, 0.47, 7);
    y = collar(pf, 0.10, 0.168, 0.47, 0.03);
    y = collar(pf, 0.10, 0.142, y + 0.004, 0.022);
    pf.to(0.086, y + 0.012);
    /* La mitre : un œuf, plus large en bas, pointu en haut. */
    var m0 = y + 0.012;
    pf.bez(0.135, m0 + 0.01, 0.158, m0 + 0.07, 0.15, m0 + 0.12, 6);
    pf.bez(0.142, m0 + 0.17, 0.08, m0 + 0.225, 0.024, m0 + 0.245, 7);
    var top = m0 + 0.245;
    pf.to(0.02, top + 0.004);
    pf.arc(0, top + 0.036, 0.034, -Math.acos(0.018 / 0.034), Math.PI / 2, 8);   // bouton
    var geo = lathe(pf);
    /* Rayon de la mitre à une hauteur donnée, lu sur le profil. */
    var prof = pf.pts.filter(function (p) { return p.y >= m0 && p.y <= top; });
    function radiusAt(yy) {
      for (var i = 1; i < prof.length; i++) {
        if (prof[i].y >= yy) {
          var p = prof[i - 1], q = prof[i], t = (yy - p.y) / ((q.y - p.y) || 1);
          return p.x + (q.x - p.x) * t;
        }
      }
      return prof.length ? prof[prof.length - 1].x : 0;
    }
    var parts = [{ geo: geo, mat: 'body' }];
    var slit = mitreSlit(radiusAt, m0 + 0.02, top - 0.01);
    if (slit) parts.push({ geo: slit, mat: 'detail' });
    return parts;
  }

  function crownedBody(pf, R, bodyTop, cupTop, cupR) {
    var y = foot(pf, R);
    pf.bez(R * 0.62, y + 0.04, 0.12, y + 0.16, 0.108, bodyTop, 8);
    y = collar(pf, 0.104, 0.182, bodyTop, 0.032);
    y = collar(pf, 0.104, 0.155, y + 0.004, 0.022);
    pf.to(0.098, y + 0.01);
    /* La coupe de la couronne s'évase vers le haut. */
    pf.bez(0.10, y + 0.06, cupR * 0.82, cupTop - 0.07, cupR, cupTop - 0.012, 7);
    pf.arc(cupR - 0.012, cupTop - 0.012, 0.012, 0, Math.PI / 2, 3);
    return cupTop;
  }

  function queenParts() {
    var pf = new Profile();
    var rim = crownedBody(pf, 0.385, 0.60, 0.865, 0.188);
    pf.to(0.15, rim + 0.004);
    pf.bez(0.12, rim + 0.02, 0.07, rim + 0.05, 0.036, rim + 0.06, 5);  // dôme
    pf.arc(0, rim + 0.098, 0.044, -Math.acos(0.032 / 0.044), Math.PI / 2, 9);  // perle sommitale
    var parts = [{ geo: lathe(pf), mat: 'body' }];
    /* Les fleurons de la couronne. */
    var ball = new THREE.SphereGeometry(0.03, 10, 8);
    for (var i = 0; i < 8; i++) {
      var a = i * Math.PI / 4 + Math.PI / 8;
      var g = ball.clone();
      g.translate(Math.cos(a) * 0.168, rim + 0.012, Math.sin(a) * 0.168);
      parts.push({ geo: g, mat: 'body' });
    }
    return parts;
  }

  function kingParts() {
    var pf = new Profile();
    var rim = crownedBody(pf, 0.395, 0.64, 0.905, 0.178);
    pf.to(0.14, rim + 0.004);
    pf.bez(0.11, rim + 0.02, 0.06, rim + 0.04, 0.04, rim + 0.045, 5);
    pf.to(0.036, rim + 0.05).to(0.052, rim + 0.056).to(0.052, rim + 0.07).to(0, rim + 0.072);  // socle de la croix
    var parts = [{ geo: lathe(pf), mat: 'body' }];
    /* La croix, de face pour les deux joueurs (bras le long de x). */
    var w = 0.026, arm = 0.078, low = 0.0, high = 0.205, armY = 0.13;
    var sh = new THREE.Shape();
    sh.moveTo(-w, low); sh.lineTo(w, low); sh.lineTo(w, armY - w); sh.lineTo(arm, armY - w);
    sh.lineTo(arm, armY + w); sh.lineTo(w, armY + w); sh.lineTo(w, high); sh.lineTo(-w, high);
    sh.lineTo(-w, armY + w); sh.lineTo(-arm, armY + w); sh.lineTo(-arm, armY - w); sh.lineTo(-w, armY - w);
    sh.lineTo(-w, low);
    var cross = extrude(sh, 0.034, 0.008, 2);
    cross.translate(0, rim + 0.07, -0.017);
    cross.computeVertexNormals();
    smoothSides(cross);
    parts.push({ geo: cross, mat: 'body' });
    return parts;
  }

  /* Une silhouette 2D (x, y) gonflée en volume, symétrique en z : épaisseur
     = halfWidth(x, y) × arrondi(distance au contour). Le contour est
     rééchantillonné, l'intérieur couvert d'une grille en quinconce (plus deux
     rangées serrées le long du bord), triangulé par Delaunay ; hauteurs et
     normales sont lissées sur les voisins. Tout en tableaux typés : le
     cavalier se construisait en 0,4 s (1,3 s sur un téléphone moyen), il lui
     faut maintenant 30 ms (100 ms). */
  function inflate(points, halfWidth, rounding, spacing) {
    var raw = points.slice(), i, j, k, q;
    if (raw.length > 2 && raw[0].distanceTo(raw[raw.length - 1]) < 1e-6) raw.pop();
    if (THREE.ShapeUtils.isClockWise(raw)) raw.reverse();

    /* 1. Le contour, à pas régulier (≈ l'espacement intérieur) : Delaunay en
       garde alors les bords. */
    var perimeter = 0;
    for (i = 0; i < raw.length; i++) perimeter += raw[i].distanceTo(raw[(i + 1) % raw.length]);
    var steps = Math.max(24, Math.round(perimeter / (spacing * 0.8))), stepLen = perimeter / steps;
    var cxs = [raw[0].x], cys = [raw[0].y], acc = 0;
    for (i = 0; i < raw.length && cxs.length < steps; i++) {
      var A = raw[i], B = raw[(i + 1) % raw.length], seg = A.distanceTo(B), t0 = 0;
      while (seg > 0 && acc + (seg - t0) >= stepLen && cxs.length < steps) {
        t0 += stepLen - acc; acc = 0;
        cxs.push(A.x + (B.x - A.x) * t0 / seg); cys.push(A.y + (B.y - A.y) * t0 / seg);
      }
      acc += seg - t0;
    }
    var n = cxs.length, CXs = new Float64Array(cxs), CYs = new Float64Array(cys);
    function distToContour(x, y) {
      var best = Infinity;
      for (var e = 0; e < n; e++) {
        var ax = CXs[e], ay = CYs[e], f = e + 1 === n ? 0 : e + 1;
        var dx = CXs[f] - ax, dy = CYs[f] - ay, len = dx * dx + dy * dy;
        var t = len > 0 ? ((x - ax) * dx + (y - ay) * dy) / len : 0;
        t = t < 0 ? 0 : t > 1 ? 1 : t;
        var px = ax + dx * t - x, py = ay + dy * t - y, d = px * px + py * py;
        if (d < best) best = d;
      }
      return Math.sqrt(best);
    }
    function inside(x, y) {
      var c = false;
      for (var e = 0, f = n - 1; e < n; f = e++) {
        var ay = CYs[e], by = CYs[f];
        if ((ay > y) !== (by > y) && x < (CXs[f] - CXs[e]) * (y - ay) / (by - ay) + CXs[e]) c = !c;
      }
      return c;
    }
    function lift(d) { var u = 1 - Math.min(d, rounding) / rounding; return Math.sqrt(Math.max(0, 1 - u * u)); }

    /* 2. Les points intérieurs. */
    var minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
    for (i = 0; i < n; i++) {
      if (CXs[i] < minX) minX = CXs[i]; if (CXs[i] > maxX) maxX = CXs[i];
      if (CYs[i] < minY) minY = CYs[i]; if (CYs[i] > maxY) maxY = CYs[i];
    }
    var pxs = cxs.slice(), pys = cys.slice(), rowH = spacing * 0.866;
    for (var gy = minY + rowH / 2, row = 0; gy < maxY; gy += rowH, row++) {
      for (var gx = minX + (row % 2 ? spacing / 2 : 0); gx < maxX; gx += spacing) {
        if (inside(gx, gy) && distToContour(gx, gy) > spacing * 1.05) { pxs.push(gx); pys.push(gy); }
      }
    }
    /* Deux rangées serrées le long du contour : c'est là que la surface est la
       plus pentue (elle rejoint le contour à la verticale). Contour
       anti-horaire : l'intérieur est à gauche du sens de parcours. */
    for (var ring = 0; ring < 2; ring++) {
      var off = spacing * (ring === 0 ? 0.28 : 0.62);
      for (i = 0; i < n; i++) {
        var pa = i === 0 ? n - 1 : i - 1, pb = i + 1 === n ? 0 : i + 1;
        var tx = CXs[pb] - CXs[pa], ty = CYs[pb] - CYs[pa], tl = Math.sqrt(tx * tx + ty * ty) || 1;
        var ix = CXs[i] - ty / tl * off, iy = CYs[i] + tx / tl * off;
        if (inside(ix, iy) && distToContour(ix, iy) > off * 0.7) { pxs.push(ix); pys.push(iy); }
      }
    }
    var count = pxs.length;

    /* 3. Delaunay (Bowyer-Watson) : chaque point retire les triangles dont le
       cercle circonscrit le contient, puis referme la cavité. Les points
       entrent de gauche à droite : un triangle dont le cercle est tout entier
       à gauche du point courant ne peut plus être touché, il quitte la liste
       des triangles à tester (sinon chaque point les parcourait tous). */
    var npts = count + 3, X = new Float64Array(npts), Y = new Float64Array(npts);
    for (i = 0; i < count; i++) { X[i] = pxs[i]; Y[i] = pys[i]; }
    var span = Math.max(maxX - minX, maxY - minY) * 10, mx = (minX + maxX) / 2, my = (minY + maxY) / 2;
    X[count] = mx - span; Y[count] = my - span;
    X[count + 1] = mx + span; Y[count + 1] = my - span;
    X[count + 2] = mx; Y[count + 2] = my + span;
    var cap = 2 * npts + 8, nt = 0;
    var TA = new Int32Array(cap), TB = new Int32Array(cap), TC = new Int32Array(cap);
    var OX = new Float64Array(cap), OY = new Float64Array(cap), OR = new Float64Array(cap);
    var bad = new Int32Array(cap), eu = new Int32Array(cap * 3), ev = new Int32Array(cap * 3);
    var FA = new Int32Array(cap), FB = new Int32Array(cap), FC = new Int32Array(cap), nf = 0;
    var order = [];
    for (i = 0; i < count; i++) order.push(i);
    order.sort(function (a1, b1) { return X[a1] - X[b1] || Y[a1] - Y[b1]; });
    var queue = [[count, count + 1, count + 2]];
    for (var s3 = -1; s3 < count; s3++) {
      var p = s3 < 0 ? -1 : order[s3];
      if (p >= 0) {
        var px = X[p], py = Y[p], nb = 0, ne = 0, last;
        for (j = 0; j < nt;) {
          var ddx = px - OX[j];
          if (ddx > 0 && ddx * ddx > OR[j]) {
            FA[nf] = TA[j]; FB[nf] = TB[j]; FC[nf] = TC[j]; nf++;
            last = --nt;
            TA[j] = TA[last]; TB[j] = TB[last]; TC[j] = TC[last];
            OX[j] = OX[last]; OY[j] = OY[last]; OR[j] = OR[last];
            continue;
          }
          var ddy = py - OY[j];
          if (ddx * ddx + ddy * ddy < OR[j]) bad[nb++] = j;
          j++;
        }
        for (k = 0; k < nb; k++) {
          var t = bad[k];
          eu[ne] = TA[t]; ev[ne++] = TB[t];
          eu[ne] = TB[t]; ev[ne++] = TC[t];
          eu[ne] = TC[t]; ev[ne++] = TA[t];
        }
        /* Retirés du plus grand indice au plus petit : le dernier comble le trou. */
        for (k = nb - 1; k >= 0; k--) {
          var r = bad[k]; last = --nt;
          TA[r] = TA[last]; TB[r] = TB[last]; TC[r] = TC[last];
          OX[r] = OX[last]; OY[r] = OY[last]; OR[r] = OR[last];
        }
        /* Le bord de la cavité : les arêtes d'un seul triangle retiré (tous
           tournent dans le même sens : une arête commune y figure dans les deux). */
        queue.length = 0;
        for (k = 0; k < ne; k++) {
          var u = eu[k], v = ev[k], shared = false;
          for (q = 0; q < ne; q++) if (eu[q] === v && ev[q] === u) { shared = true; break; }
          if (!shared) queue.push([u, v, p]);
        }
      }
      for (k = 0; k < queue.length; k++) {
        var a = queue[k][0], b = queue[k][1], c = queue[k][2];
        var ax = X[a], ay = Y[a], bx = X[b], by = Y[b], cx = X[c], cy = Y[c];
        var dd = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by));
        var a2 = ax * ax + ay * ay, b2 = bx * bx + by * by, c2 = cx * cx + cy * cy;
        var ux = (a2 * (by - cy) + b2 * (cy - ay) + c2 * (ay - by)) / dd;
        var uy = (a2 * (cx - bx) + b2 * (ax - cx) + c2 * (bx - ax)) / dd;
        TA[nt] = a; TB[nt] = b; TC[nt] = c; OX[nt] = ux; OY[nt] = uy;
        OR[nt] = (ax - ux) * (ax - ux) + (ay - uy) * (ay - uy);
        nt++;
      }
    }
    for (j = 0; j < nt; j++) { FA[nf] = TA[j]; FB[nf] = TB[j]; FC[nf] = TC[j]; nf++; }

    /* 4. On garde les triangles dont le centre et le milieu des arêtes sont
       dans la silhouette (rien ne traverse la gorge ni l'encolure). */
    var faces = [];
    function nearMid(e1, e2, gx2, gy2) {
      var mx2 = (X[e1] + X[e2]) / 2, my2 = (Y[e1] + Y[e2]) / 2;
      return inside(mx2 + (gx2 - mx2) * 0.02, my2 + (gy2 - my2) * 0.02);
    }
    for (j = 0; j < nf; j++) {
      var fa = FA[j], fb = FB[j], fc = FC[j];
      if (fa >= count || fb >= count || fc >= count) continue;
      var gx3 = (X[fa] + X[fb] + X[fc]) / 3, gy3 = (Y[fa] + Y[fb] + Y[fc]) / 3;
      if (!inside(gx3, gy3) || !nearMid(fa, fb, gx3, gy3) || !nearMid(fb, fc, gx3, gy3) || !nearMid(fc, fa, gx3, gy3)) continue;
      var area = (X[fb] - X[fa]) * (Y[fc] - Y[fa]) - (X[fc] - X[fa]) * (Y[fb] - Y[fa]);
      if (area > 0) faces.push(fa, fb, fc); else faces.push(fa, fc, fb);
    }

    /* Voisins de chaque point (adjacence compacte), pour les lissages. */
    function neighbours(vcount, idx) {
      var deg = new Int32Array(vcount + 1);
      for (var e = 0; e < idx.length; e++) deg[idx[e]] += 2;
      var start = new Int32Array(vcount + 1);
      for (var e2 = 0; e2 < vcount; e2++) start[e2 + 1] = start[e2] + deg[e2];
      var fill = start.slice(0, vcount), list = new Int32Array(start[vcount]);
      for (var f = 0; f < idx.length; f += 3) {
        for (var s2 = 0; s2 < 3; s2++) {
          var from = idx[f + s2], to = idx[f + (s2 + 1) % 3];
          list[fill[from]++] = to; list[fill[to]++] = from;
        }
      }
      return { start: start, list: list };
    }

    /* 5. Épaisseurs, lissées : la distance au contour forme une arête le long de
       l'axe médian de la silhouette, qui se verrait en reflet sur le bois
       verni. Le contour reste à z = 0. */
    var heights = new Float64Array(count);
    for (i = n; i < count; i++) heights[i] = halfWidth(X[i], Y[i]) * lift(distToContour(X[i], Y[i]));
    var adj = neighbours(count, faces), next = new Float64Array(count);
    for (var pass = 0; pass < 6; pass++) {
      for (i = 0; i < n; i++) next[i] = 0;
      for (i = n; i < count; i++) {
        var s0 = adj.start[i], s1 = adj.start[i + 1], sum = 0;
        if (s1 === s0) { next[i] = heights[i]; continue; }
        for (k = s0; k < s1; k++) sum += heights[adj.list[k]];
        next[i] = heights[i] * 0.5 + 0.5 * sum / (s1 - s0);
      }
      var swap = heights; heights = next; next = swap;
    }

    /* Sommets : le contour (z = 0) est commun aux deux faces ; les points
       intérieurs existent deux fois, devant (+z) et derrière (-z). */
    var vcount = count + (count - n);
    var positions = new Float32Array(vcount * 3);
    for (i = 0; i < count; i++) { positions[i * 3] = X[i]; positions[i * 3 + 1] = Y[i]; positions[i * 3 + 2] = heights[i]; }
    for (i = n; i < count; i++) {
      var o = (i + count - n) * 3;
      positions[o] = X[i]; positions[o + 1] = Y[i]; positions[o + 2] = -heights[i];
    }
    var index = new (vcount > 65535 ? Uint32Array : Uint16Array)(faces.length * 2);
    for (k = 0; k < faces.length; k += 3) {
      var f0 = faces[k], f1 = faces[k + 1], f2 = faces[k + 2];
      index[k] = f0; index[k + 1] = f1; index[k + 2] = f2;
      var b0 = f0 < n ? f0 : f0 + count - n, b1 = f1 < n ? f1 : f1 + count - n, b2i = f2 < n ? f2 : f2 + count - n;
      index[faces.length + k] = b0; index[faces.length + k + 1] = b2i; index[faces.length + k + 2] = b1;
    }
    var geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.BufferAttribute(positions, 3));
    geo.setIndex(new THREE.BufferAttribute(index, 1));
    geo.computeVertexNormals();

    /* 6. Les normales d'un maillage irrégulier font un froissé sous un reflet :
       moyennées avec leurs voisines (trois passes), la forme ne bouge pas. */
    var normals = geo.attributes.normal, cur = Float32Array.from(normals.array), out = new Float32Array(cur.length);
    var vadj = neighbours(vcount, index);
    for (var np = 0; np < 3; np++) {
      for (i = 0; i < vcount; i++) {
        var sx = cur[i * 3], sy = cur[i * 3 + 1], sz = cur[i * 3 + 2];
        for (k = vadj.start[i]; k < vadj.start[i + 1]; k++) {
          var w = vadj.list[k] * 3;
          sx += cur[w] * 0.5; sy += cur[w + 1] * 0.5; sz += cur[w + 2] * 0.5;
        }
        var ln = Math.sqrt(sx * sx + sy * sy + sz * sz) || 1;
        out[i * 3] = sx / ln; out[i * 3 + 1] = sy / ln; out[i * 3 + 2] = sz / ln;
      }
      var tmp = cur; cur = out; out = tmp;
    }
    normals.array.set(cur);
    normals.needsUpdate = true;
    geo.computeBoundingSphere();
    /* Où se trouve la surface (demi-épaisseur) en un point : pour poser les yeux. */
    geo.userData.surfaceAt = function (x, y) { return halfWidth(x, y) * lift(distToContour(x, y)); };
    return geo;
  }

  /* Le cavalier : la tête de cheval regarde vers +x dans la silhouette ; après
     rotation, vers -z — le sens où avancent les Blancs. */
  function knightParts() {
    var pf = new Profile(), y = foot(pf, 0.345);
    pf.bez(0.22, y + 0.02, 0.19, y + 0.05, 0.188, 0.245, 4);
    y = collar(pf, 0.186, 0.235, 0.245, 0.03);
    pf.to(0.17, y + 0.002).to(0, y + 0.002);
    var parts = [{ geo: lathe(pf), mat: 'body' }];
    var baseY = y - 0.012;

    /* La silhouette d'une tête de cheval Staunton, regard vers +x : dos de
       l'encolure, nuque, front, chanfrein, naseaux, bouche, menton, ganache,
       gorge, poitrail. Une spline passe par ces points. */
    var P = [
      [-0.176, -0.070], [-0.200, 0.040], [-0.204, 0.140], [-0.188, 0.250], [-0.142, 0.360], [-0.092, 0.430],
      [-0.040, 0.466], [0.022, 0.463], [0.080, 0.428], [0.146, 0.357], [0.200, 0.295], [0.236, 0.262],
      [0.258, 0.236], [0.266, 0.205], [0.256, 0.181], [0.230, 0.168], [0.192, 0.168], [0.148, 0.180],
      [0.098, 0.198], [0.046, 0.222], [0.012, 0.204], [0.012, 0.150], [0.046, 0.090], [0.092, 0.040],
      [0.118, -0.010], [0.120, -0.070]
    ].map(function (q) { return new THREE.Vector2(q[0], q[1]); });
    var s = new THREE.Shape();
    s.moveTo(P[0].x, P[0].y);
    s.splineThru(P.slice(1));
    s.lineTo(P[0].x, P[0].y);
    /* La tête est « gonflée » à partir de la silhouette : chaque point prend une
       épaisseur qui dépend de sa distance au bord (arrondi circulaire), puis de
       sa place (l'encolure s'élargit vers le pied comme sur un cavalier sculpté,
       le museau s'affine). Aucune face plane, aucune arête : les deux côtés se
       rejoignent en douceur sur le contour. */
    function clamp01(v) { return v < 0 ? 0 : v > 1 ? 1 : v; }
    function widthAt(hx, hy) {
      var neck = 1 + 0.42 * Math.pow(clamp01(1 - hy / 0.24), 1.5);
      var muzzle = 1 - 0.22 * clamp01((hx - 0.05) / 0.2);
      var crown = 1 - 0.08 * clamp01((hy - 0.36) / 0.12);
      return 0.128 * neck * muzzle * crown;
    }
    var head = inflate(s.getPoints(8), widthAt, 0.13, 0.022);
    head.rotateY(Math.PI / 2);          // silhouette +x → scène -z ; épaisseur le long de x
    head.translate(0, baseY, 0);
    parts.push({ geo: head, mat: 'body' });
    var surfaceAt = head.userData.surfaceAt;

    /* La crinière : une arête qui suit le dos de l'encolure jusqu'à la nuque. */
    var back = new THREE.SplineCurve(P.slice(1, 8));
    var outer = [], inner = [];
    for (var k = 0; k <= 24; k++) {
      var t = 0.02 + 0.80 * k / 24;
      var pt = back.getPoint(t), tg = back.getTangent(t);
      var nx = -tg.y, ny = tg.x;                   // à gauche du sens de parcours = vers l'extérieur
      outer.push(new THREE.Vector2(pt.x + nx * 0.03, pt.y + ny * 0.03));
      inner.push(new THREE.Vector2(pt.x - nx * 0.03, pt.y - ny * 0.03));
    }
    var crest = inflate(outer.concat(inner.reverse()), function () { return 0.03; }, 0.022, 0.02);
    crest.rotateY(Math.PI / 2);
    crest.translate(0, baseY, 0);
    parts.push({ geo: crest, mat: 'body' });

    /* Oreilles : deux cônes sur la nuque, écartés, inclinés vers l'arrière. */
    var ear = new THREE.ConeGeometry(0.03, 0.095, 12);
    for (var side = -1; side <= 1; side += 2) {
      var e = ear.clone();
      e.rotateX(0.34);                              // pointe vers l'arrière (+z)
      e.rotateZ(-side * 0.18);                      // et un peu vers l'extérieur
      e.translate(side * 0.048, baseY + 0.515, 0.032);
      parts.push({ geo: e, mat: 'body' });
    }
    /* Yeux et naseaux, de chaque côté (x), posés sur la surface de la tête. */
    var eye = new THREE.SphereGeometry(0.017, 8, 6);
    for (var sd = -1; sd <= 1; sd += 2) {
      var ey = eye.clone();
      ey.scale(0.5, 1, 1.15);
      ey.translate(sd * (surfaceAt(0.07, 0.38) - 0.006), baseY + 0.38, -0.07);
      parts.push({ geo: ey, mat: 'detail' });
      var ns = eye.clone();
      ns.scale(0.35, 0.55, 0.6);
      ns.translate(sd * (surfaceAt(0.24, 0.212) - 0.006), baseY + 0.212, -0.24);
      parts.push({ geo: ns, mat: 'detail' });
    }
    return parts;
  }

  var BUILDERS = {};
  BUILDERS[PAWN] = pawnParts; BUILDERS[KNIGHT] = knightParts; BUILDERS[BISHOP] = bishopParts;
  BUILDERS[ROOK] = rookParts; BUILDERS[QUEEN] = queenParts; BUILDERS[KING] = kingParts;

  /* Les profils sont dessinés pour un roi de 1,18 ; la taille de jeu est un peu
     plus grande, pour reconnaître les pièces sur un téléphone. */
  var PIECE_SCALE = 1.14;
  function partsOf(type) {
    var t = BUILDERS[type] ? type : KING;
    if (!geometryCache[t]) {
      var parts = BUILDERS[t]();
      for (var i = 0; i < parts.length; i++) {
        parts[i].geo.scale(PIECE_SCALE, PIECE_SCALE, PIECE_SCALE);
        parts[i].geo.computeBoundingSphere();
      }
      geometryCache[t] = parts;
    }
    return geometryCache[t];
  }

  /* Le sens où avance un camp : les Blancs vers -z, les Noirs vers +z. */
  function facingY(player) { return player === 0 ? 0 : Math.PI; }

  function piece(player, type) {
    var mats = sideMaterials(player);
    var g = new THREE.Group();
    var parts = partsOf(type);
    for (var i = 0; i < parts.length; i++) {
      var mesh = new THREE.Mesh(parts[i].geo, mats[parts[i].mat] || mats.body);
      mesh.castShadow = true;
      mesh.receiveShadow = true;
      g.add(mesh);
    }
    /* Toute la pièce regarde l'adversaire : le cavalier surtout, mais aussi la
       fente du fou — chaque camp la voit du même côté. */
    g.rotation.y = facingY(player);
    g.userData.chessFacing = g.rotation.y;
    return g;
  }

  /* ── Le plateau ───────────────────────────────────────────────────────── */
  function roundedRect(path, x, y, w, h, r) {
    path.moveTo(x + r, y);
    path.lineTo(x + w - r, y); path.quadraticCurveTo(x + w, y, x + w, y + r);
    path.lineTo(x + w, y + h - r); path.quadraticCurveTo(x + w, y + h, x + w - r, y + h);
    path.lineTo(x + r, y + h); path.quadraticCurveTo(x, y + h, x, y + h - r);
    path.lineTo(x, y + r); path.quadraticCurveTo(x, y, x + r, y);
    return path;
  }

  /* Un peu de fil du bois, dessiné une fois. */
  function grainCanvas(base, size, seed, lines) {
    var cv = document.createElement('canvas');
    cv.width = cv.height = size;
    var ctx = cv.getContext('2d');
    ctx.fillStyle = base;
    ctx.fillRect(0, 0, size, size);
    var rnd = seed;
    function rand() { rnd = (rnd * 16807) % 2147483647; return (rnd - 1) / 2147483646; }
    for (var i = 0; i < lines; i++) {
      var y0 = rand() * size, amp = 2 + rand() * 6, freq = 1 + rand() * 2.5, phase = rand() * 6.28;
      ctx.strokeStyle = rand() < 0.5 ? 'rgba(0,0,0,' + (0.03 + rand() * 0.06) + ')' : 'rgba(255,255,255,' + (0.02 + rand() * 0.05) + ')';
      ctx.lineWidth = 0.6 + rand() * 1.6;
      ctx.beginPath();
      for (var x = 0; x <= size; x += 8) {
        var yy = y0 + Math.sin(x / size * Math.PI * freq + phase) * amp;
        if (x === 0) ctx.moveTo(x, yy); else ctx.lineTo(x, yy);
      }
      ctx.stroke();
    }
    return cv;
  }

  function hex(c) { return '#' + ('000000' + c.toString(16)).slice(-6); }

  function canvasTexture(cv) {
    var tex = new THREE.CanvasTexture(cv);
    tex.anisotropy = 4;
    return tex;
  }

  /* Le dessus du cadre : noyer, filet doré, coordonnées des deux côtés.
     Le canevas se lit comme le plateau vu d'en haut par les Blancs : haut = 8e
     rangée (z < 0), gauche = colonne a (x < 0). */
  function frameCanvas(W, inner, cell, size) {
    var cv = grainCanvas(hex(WOOD.frame), size, 7, 220);
    var ctx = cv.getContext('2d');
    var px = size / W;
    var half = inner / 2;
    function X(x) { return (x + W / 2) * px; }
    function Y(z) { return (z + W / 2) * px; }
    /* Filet doré autour des cases. */
    ctx.strokeStyle = WOOD.brass;
    ctx.lineWidth = Math.max(2, 0.045 * px);
    var m = 0.06 * px;
    ctx.strokeRect(X(-half) - m, Y(-half) - m, inner * px + 2 * m, inner * px + 2 * m);
    ctx.globalAlpha = 0.55;
    ctx.lineWidth = Math.max(1, 0.016 * px);
    var m2 = 0.13 * px;
    ctx.strokeRect(X(-half) - m2, Y(-half) - m2, inner * px + 2 * m2, inner * px + 2 * m2);
    ctx.globalAlpha = 1;
    /* Coordonnées : gravées en laiton, droites pour le joueur le plus proche. */
    var band = (W - inner) / 2;
    var fontPx = Math.round(Math.min(band * 0.52, cell * 0.30) * px);
    ctx.font = '700 ' + fontPx + 'px Georgia, "Times New Roman", serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    var bandMid = half + band * 0.48;
    function glyph(text, x, z, flip) {
      ctx.save();
      ctx.translate(X(x), Y(z));
      if (flip) ctx.rotate(Math.PI);
      ctx.fillStyle = 'rgba(0,0,0,0.45)';
      ctx.fillText(text, 0, Math.max(1, fontPx * 0.05));
      ctx.fillStyle = WOOD.brass;
      ctx.fillText(text, 0, 0);
      ctx.restore();
    }
    for (var i = 0; i < 8; i++) {
      var file = 'abcdefgh'.charAt(i), rank = String(8 - i);
      var c = (i - 3.5) * cell;
      glyph(file, c, bandMid, false);    // côté Blancs
      glyph(file, c, -bandMid, true);    // côté Noirs
      glyph(rank, -bandMid, c, false);   // colonne a, pour les Blancs
      glyph(rank, bandMid, c, true);     // colonne h, pour les Noirs
    }
    return cv;
  }

  var FRAME = 0.62;

  /*
   * board(group, {cell, size}) : pose le plateau dans `group`. Les cases gardent
   * `userData = {row, col}` ; le dessus des cases est à y = 0.10, comme avant.
   * Rend { fitRadius } : la demi-largeur du plateau cadre compris.
   */
  function board(group, opts) {
    opts = opts || {};
    var cell = opts.cell || 1.4, n = opts.size || 8;
    var inner = n * cell, W = inner + 2 * FRAME, BO = (n - 1) * cell / 2;
    var top = 0.10;

    /* Dessous. */
    var baseMat = new THREE.MeshStandardMaterial({ color: WOOD.base, roughness: 0.9 });
    var base = new THREE.Mesh(new THREE.BoxGeometry(W - 0.12, 0.2, W - 0.12), baseMat);
    base.position.y = -0.14;
    base.receiveShadow = true;
    group.add(base);

    /* Cadre : un anneau arrondi extrudé, le trou laisse la place aux cases. */
    var outer = roundedRect(new THREE.Shape(), -W / 2, -W / 2, W, W, 0.16);
    var hole = new THREE.Path();
    hole.moveTo(-inner / 2, -inner / 2); hole.lineTo(-inner / 2, inner / 2);
    hole.lineTo(inner / 2, inner / 2); hole.lineTo(inner / 2, -inner / 2); hole.lineTo(-inner / 2, -inner / 2);
    outer.holes.push(hole);
    var frameDepth = 0.2, bev = 0.045;
    var frameGeo = extrude(outer, frameDepth, bev, 3);
    frameGeo.rotateX(-Math.PI / 2);     // y de la forme → -z, épaisseur → +y
    frameGeo.translate(0, top - frameDepth - bev, 0);
    frameGeo.computeVertexNormals();
    smoothSides(frameGeo);
    var texSize = (window.devicePixelRatio || 1) > 1.5 ? 2048 : 1024;
    var frameTex = canvasTexture(frameCanvas(W, inner, cell, texSize));
    frameTex.repeat.set(1 / W, 1 / W);
    frameTex.offset.set(0.5, 0.5);
    var frameTop = new THREE.MeshStandardMaterial({ map: frameTex, roughness: 0.42, metalness: 0.05 });
    var frameSide = new THREE.MeshStandardMaterial({ color: WOOD.frame, roughness: 0.5, metalness: 0.02 });
    var frame = new THREE.Mesh(frameGeo, [frameTop, frameSide]);
    frame.receiveShadow = true;
    frame.castShadow = false;
    group.add(frame);

    /* Cases : érable et noyer, quatre variantes de fil chacune. */
    function squareMats(color, seed) {
      var out = [];
      for (var v = 0; v < 4; v++) {
        var tex = canvasTexture(grainCanvas(hex(color), 256, seed + v * 101, 34));
        if (v % 2) { tex.center.set(0.5, 0.5); tex.rotation = Math.PI; }
        var mat = new THREE.MeshStandardMaterial({ map: tex, roughness: 0.64, metalness: 0 });
        out.push(mat);
      }
      return out;
    }
    var lightMats = squareMats(WOOD.light, 11), darkMats = squareMats(WOOD.dark, 23);
    var squareGeo = new THREE.BoxGeometry(cell, 0.12, cell);
    for (var r = 0; r < n; r++) {
      for (var c = 0; c < n; c++) {
        var dark = (r + c) % 2 === 1;
        var mats = dark ? darkMats : lightMats;
        var sq = new THREE.Mesh(squareGeo, mats[(r * 3 + c * 5) % 4]);
        sq.position.set(c * cell - BO, top - 0.06, r * cell - BO);
        sq.receiveShadow = true;
        sq.userData = { row: r, col: c };
        group.add(sq);
      }
    }
    return { fitRadius: W / 2, frame: FRAME };
  }

  /* ── Éclairage de studio ─────────────────────────────────────────────
     Les pages additionnaient six lumières (≈ ×2,2 sur une face éclairée) :
     l'ivoire et l'érable saturaient au blanc, et le brouillard, qui commence à
     22 unités, assombrissait le plateau vu de loin — les couleurs changeaient
     avec le zoom. Ici : une lumière principale (les mêmes ombres qu'avant), un
     ciel doux, un contre-jour froid qui détache l'ébène du fond, la lueur dorée
     de Mindspille en plus discret, et le brouillard repoussé derrière le plateau. */
  function lights(scene) {
    var amb = new THREE.AmbientLight(0xffffff, 0.16);
    var hemi = new THREE.HemisphereLight(0xd6dcf5, 0x3b2a1d, 0.42);
    var key = new THREE.DirectionalLight(0xfff3e2, 0.78);
    key.position.set(6, 18, 12);
    key.castShadow = true;
    key.shadow.mapSize.width = 1024; key.shadow.mapSize.height = 1024;
    key.shadow.camera.near = 0.5; key.shadow.camera.far = 45;
    key.shadow.camera.left = -13; key.shadow.camera.right = 13;
    key.shadow.camera.top = 13; key.shadow.camera.bottom = -13;
    key.shadow.bias = -0.0004;
    key.shadow.radius = 3;
    var fill = new THREE.DirectionalLight(0xffe2c4, 0.22); fill.position.set(13, 8, 2);
    var rim = new THREE.DirectionalLight(0xbcd0ff, 0.34); rim.position.set(-11, 9, -9);
    var glow = new THREE.SpotLight(0xfbbf24, 0.16); glow.position.set(-5, 14, -4);
    glow.angle = Math.PI / 5.5; glow.penumbra = 0.7;
    [amb, hemi, key, fill, rim, glow].forEach(function (l) { scene.add(l); });
    if (scene.fog && scene.fog.isFog) { scene.fog.near = 34; scene.fog.far = 110; }
    return { key: key, fill: fill, rim: rim, glow: glow };
  }

  /* ── Reflets : un petit studio, rendu une fois dans une carte cubique ──
     128 px par face et ses niveaux de flou (mipmaps) : la rugosité de chaque
     matière y choisit son niveau. Le préfiltrage PMREM de Three.js bloquait la
     page plus de 5 s en rendu logiciel (tests, téléphones sans accélération). */
  function attach(renderer) {
    if (envTexture || !renderer || !THREE.WebGLCubeRenderTarget || !THREE.CubeCamera) return envTexture;
    var studio = new THREE.Scene(), made = [];
    function add(geo, color, side) {
      var mat = new THREE.MeshBasicMaterial({ color: color, side: side });
      made.push(geo, mat);
      var m = new THREE.Mesh(geo, mat);
      studio.add(m);
      return m;
    }
    function panel(w, h, color, x, y, z) {
      var m = add(new THREE.PlaneGeometry(w, h), color, THREE.DoubleSide);
      m.position.set(x, y, z);
      m.lookAt(0, 0, 0);
    }
    try {
      add(new THREE.SphereGeometry(30, 24, 16), 0x1b1830, THREE.BackSide);
      panel(26, 26, 0xbfc4d6, 0, 22, 0);        // grande boîte à lumière au plafond
      panel(10, 14, 0xffe0b8, 18, 8, 14);       // lumière chaude de face, à droite
      panel(12, 8, 0x8fa4ff, -20, 6, -10);      // contre-jour froid
      panel(30, 4, 0x3a3046, 0, -6, 24);        // reflet bas, discret
      var target = new THREE.WebGLCubeRenderTarget(128, {
        generateMipmaps: true, minFilter: THREE.LinearMipmapLinearFilter, magFilter: THREE.LinearFilter
      });
      new THREE.CubeCamera(0.5, 100, target).update(renderer, studio);
      envTexture = target.texture;
      for (var s = 0; s < 2; s++) {
        var mats = materialCache[s];
        if (mats) { mats.body.envMap = envTexture; mats.detail.envMap = envTexture; mats.body.needsUpdate = true; mats.detail.needsUpdate = true; }
      }
    } catch (e) {
      envTexture = null;
    }
    /* Le studio a servi : ses formes quittent la scène et la mémoire graphique. */
    while (studio.children.length) studio.remove(studio.children[0]);
    made.forEach(function (x) { x.dispose(); });
    return envTexture;
  }

  /* ── Pièces prises (en-tête) ──────────────────────────────────────────── */
  var START = { 1: 8, 2: 2, 3: 2, 4: 2, 5: 1 };
  var VALUE = { 1: 1, 2: 3, 3: 3, 4: 5, 5: 9 };
  var GLYPH = { 1: '♟︎', 2: '♞︎', 3: '♝︎', 4: '♜︎', 5: '♛︎' };

  /*
   * captured(b) : pour chaque camp, les pièces qu'il a PRISES (types, de la
   * plus lourde à la plus légère) et son avance matérielle. Un pion promu n'a
   * pas été pris : la pièce en surplus le rembourse (comme l'application).
   */
  function captured(b) {
    var count = [{ 1: 0, 2: 0, 3: 0, 4: 0, 5: 0 }, { 1: 0, 2: 0, 3: 0, 4: 0, 5: 0 }];
    for (var i = 0; i < 64; i++) {
      var p = b[i];
      if (!p) continue;
      var side = p > 0 ? 0 : 1, t = p > 0 ? p : -p;
      if (t >= 1 && t <= 5) count[side][t]++;
    }
    var lost = [[], []], material = [0, 0];
    for (var s = 0; s < 2; s++) {
      var promoted = 0, t2;
      for (t2 = 2; t2 <= 5; t2++) promoted += Math.max(0, count[s][t2] - START[t2]);
      var pawnsMissing = Math.max(0, START[1] - count[s][1] - promoted);
      for (t2 = 5; t2 >= 2; t2--) {
        var missing = Math.max(0, START[t2] - count[s][t2]);
        for (var k = 0; k < missing; k++) lost[s].push(t2);
      }
      for (var k2 = 0; k2 < pawnsMissing; k2++) lost[s].push(1);
      for (t2 = 1; t2 <= 5; t2++) material[s] += count[s][t2] * VALUE[t2];
    }
    /* Ce que les Blancs ont pris, ce sont les pièces perdues par les Noirs. */
    return [
      { pieces: lost[1], advantage: Math.max(0, material[0] - material[1]) },
      { pieces: lost[0], advantage: Math.max(0, material[1] - material[0]) }
    ];
  }

  window.MindspilleChess3D = {
    PAWN: PAWN, KNIGHT: KNIGHT, BISHOP: BISHOP, ROOK: ROOK, QUEEN: QUEEN, KING: KING,
    FRAME: FRAME,
    WOOD: WOOD,
    piece: piece,
    board: board,
    attach: attach,
    lights: lights,
    facing: facingY,
    captured: captured,
    glyph: function (type) { return GLYPH[type] || ''; },
    /* Couleurs des éclats d'une pièce prise. */
    sparkColor: function (player) { return player === 0 ? 0xf3ead6 : 0x4a3a30; }
  };
})();
