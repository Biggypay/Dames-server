/*
 * mindspille-3d.js — les plateaux 3D (Dames, Échecs, Tic-Tac-Toe) fluides sur
 * la durée, sur tous les appareils, SANS rien changer à ce qu'on voit.
 *
 * Chargé juste après Three.js (`/vendor/three-r128.min.js`), avant le code de
 * la page : il habille `THREE.WebGLRenderer` et `Object3D.add`, et la page ne
 * change pas une ligne.
 *
 * Pourquoi une partie finissait par ramer :
 *
 * 1. Rien n'était jamais libéré. Chaque sélection, chaque surbrillance, chaque
 *    dernier coup, chaque explosion de prise, chaque recalage du plateau crée
 *    de nouvelles formes et de nouveaux matériaux ; retirés de la scène, ils
 *    gardaient leur mémoire graphique (tampons, états de sommets) jusqu'à la
 *    fin de la page. Une longue partie en accumulait des milliers.
 *    → `sweep` : toutes les 2 s, ce qui a quitté la scène est rendu (dispose).
 *      Une forme encore utilisée n'est jamais touchée ; une forme rendue puis
 *      remise dans la scène se recharge toute seule (Three.js le gère).
 *
 * 2. Les ombres étaient recalculées à CHAQUE image — une seconde passe sur
 *    toutes les pièces, 60 fois par seconde, même plateau immobile. Le
 *    téléphone chauffait, puis ralentissait de lui-même.
 *    → les ombres ne sont recalculées que quand une pièce (ou le plateau)
 *      bouge : l'image est identique, le travail divisé par deux au repos.
 *
 * 3. Un appareil trop juste pour la définition demandée ramait tout du long.
 *    → la définition s'adapte : si les images n'arrivent plus à temps, on
 *      baisse un peu la définition (jamais sous 1), et on la remonte quand
 *      l'appareil suit à nouveau (jamais au-dessus de ce que la page demande).
 */
(function () {
  'use strict';
  var THREE = window.THREE;
  if (!THREE || !THREE.WebGLRenderer || THREE.__mindspille3d) return;
  THREE.__mindspille3d = true;

  /* Toutes les 2 s : ce qui a quitté la scène depuis rend sa mémoire. */
  var SWEEP_MS = 2000;
  /* Définition adaptative : une image plus lente que ceci (en moyenne) est « en retard ». */
  var SLOW_FRAME_MS = 24;
  var FAST_FRAME_MS = 18;
  var STEP = 0.25;

  var known = { geometries: new Set(), materials: new Set(), textures: new Set() };
  var TEXTURE_KEYS = ['map', 'alphaMap', 'aoMap', 'bumpMap', 'emissiveMap', 'envMap', 'lightMap',
    'metalnessMap', 'normalMap', 'roughnessMap', 'displacementMap', 'specularMap', 'gradientMap'];

  function materialsOf(object) {
    var material = object.material;
    if (!material) return [];
    return Array.isArray(material) ? material : [material];
  }
  function texturesOf(material, into) {
    for (var i = 0; i < TEXTURE_KEYS.length; i++) {
      var texture = material[TEXTURE_KEYS[i]];
      if (texture && texture.isTexture) into.add(texture);
    }
    if (material.uniforms) {
      for (var key in material.uniforms) {
        var value = material.uniforms[key] && material.uniforms[key].value;
        if (value && value.isTexture) into.add(value);
      }
    }
  }
  function register(object) {
    object.traverse(function (node) {
      if (node.geometry && node.geometry.isBufferGeometry) known.geometries.add(node.geometry);
      var materials = materialsOf(node);
      for (var i = 0; i < materials.length; i++) {
        known.materials.add(materials[i]);
        texturesOf(materials[i], known.textures);
      }
    });
  }

  /* Tout ce qui entre dans une scène est noté (pour savoir, plus tard, ce qui en est sorti). */
  var add = THREE.Object3D.prototype.add;
  THREE.Object3D.prototype.add = function () {
    var result = add.apply(this, arguments);
    for (var i = 0; i < arguments.length; i++) {
      if (arguments[i] && arguments[i].isObject3D) register(arguments[i]);
    }
    return result;
  };

  var scenes = new Set();
  function sweep() {
    var live = { geometries: new Set(), materials: new Set(), textures: new Set() };
    scenes.forEach(function (scene) {
      if (scene.background && scene.background.isTexture) live.textures.add(scene.background);
      if (scene.environment && scene.environment.isTexture) live.textures.add(scene.environment);
      scene.traverse(function (node) {
        if (node.geometry) live.geometries.add(node.geometry);
        var materials = materialsOf(node);
        for (var i = 0; i < materials.length; i++) {
          live.materials.add(materials[i]);
          texturesOf(materials[i], live.textures);
        }
      });
    });
    var released = 0;
    ['geometries', 'materials', 'textures'].forEach(function (kind) {
      known[kind].forEach(function (item) {
        if (live[kind].has(item)) return;
        known[kind].delete(item);
        try { item.dispose(); released++; } catch (_) {}
      });
      /* Ce qui est vivant reste connu (y compris ce qui y est entré autrement). */
      live[kind].forEach(function (item) { known[kind].add(item); });
    });
    stats.released += released;
    stats.sweeps++;
  }

  /* L'empreinte de ce qui fait une ombre (les pièces, le plateau, la lumière
     qui la porte), en deux parts :
     - `firm` : place, taille, inclinaison, visibilité, nombre — elle change
       quand une pièce bouge, apparaît, part ou penche : l'ombre est refaite à
       l'image même ;
     - `spin` : la seule rotation autour de l'axe vertical (les pions de dames
       tournent doucement sur eux-mêmes, sans fin) — l'ombre d'un disque qui
       tourne ne change pas : elle n'est rafraîchie que dix fois par seconde. */
  function addPrint(state, node) {
    state.count++;
    var e = node.matrixWorld.elements;
    var w = state.count * 0.618034;
    state.firm += (e[12] * 7 + e[13] * 11 + e[14] * 13 + e[1] * 17 + e[5] * 19 + e[9] * 23 +
      (e[0] * e[0] + e[2] * e[2]) * 29 + (e[8] * e[8] + e[10] * e[10]) * 31) * w;
    state.spin += (e[0] + e[2] * 3 + e[8] * 5 + e[10] * 7) * w;
    if (!node.visible) state.firm += w * 37;
  }
  function casterPrint(scene) {
    var state = { firm: 0, spin: 0, count: 0 };
    scene.traverse(function (node) {
      if (!node.castShadow) return;
      if (node.isMesh) addPrint(state, node);
      else if (node.isLight) {
        addPrint(state, node);
        if (node.target) addPrint(state, node.target);
      }
    });
    state.firm += state.count * 1e6;
    return state;
  }

  var stats = { released: 0, sweeps: 0, shadowUpdates: 0, frames: 0, pixelRatio: 0, renderers: 0, redraws: 0 };

  function enhance(renderer) {
    stats.renderers++;
    var shadowPrints = new WeakMap();
    var wanted = Math.min(window.devicePixelRatio || 1, 2);
    var cap = Infinity;
    var setPixelRatio = renderer.setPixelRatio.bind(renderer);
    function applyRatio() {
      var ratio = Math.max(1, Math.min(wanted, cap));
      var changed = Math.abs(renderer.getPixelRatio() - ratio) > 1e-3;
      if (changed) setPixelRatio(ratio);
      stats.pixelRatio = ratio;
      return changed;
    }
    renderer.setPixelRatio = function (value) {
      wanted = value;
      applyRatio();
    };

    /* Les ombres ne se recalculent que si quelque chose a bougé. */
    renderer.shadowMap.autoUpdate = false;
    renderer.shadowMap.needsUpdate = true;

    var last = 0, sum = 0, squares = 0, count = 0, goodSince = 0, shadowAt = 0;
    var render = renderer.render;
    renderer.render = function (scene, camera) {
      window.MS3D.last = { renderer: renderer, scene: scene, camera: camera };
      if (scene && scene.isScene && !scenes.has(scene)) {
        scenes.add(scene);
        register(scene);
      }
      if (scene && renderer.shadowMap.enabled) {
        if (scene.autoUpdate !== false) scene.updateMatrixWorld();
        var print = casterPrint(scene);
        var before = shadowPrints.get(scene);
        var stamp = performance.now();
        var moved = !before || print.firm !== before.firm;
        var spun = before && print.spin !== before.spin && stamp - shadowAt >= 100;
        // Une fois toutes les 5 s quoi qu'il arrive : un filet, pour rien de visible.
        if (moved || spun || stamp - shadowAt > 5000) {
          shadowPrints.set(scene, print);
          shadowAt = stamp;
          renderer.shadowMap.needsUpdate = true;
          stats.shadowUpdates++;
        }
      }
      var auto = scene && scene.autoUpdate;
      if (scene && renderer.shadowMap.enabled) scene.autoUpdate = false;
      try {
        render.call(renderer, scene, camera);
      } finally {
        if (scene && renderer.shadowMap.enabled) scene.autoUpdate = auto;
      }
      stats.frames++;

      /* Définition adaptative, sur la cadence réelle des images. */
      var now = performance.now();
      var gap = last ? now - last : 0;
      last = now;
      if (!gap || gap > 250) return; // onglet caché, première image : on ne compte pas
      sum += gap; squares += gap * gap; count++;
      if (count < 45) return;
      var average = sum / count;
      var resized = false;
      var spread = Math.sqrt(Math.max(0, squares / count - average * average));
      sum = 0; squares = 0; count = 0;
      // Une cadence régulière à 30 images/s (iPhone en économie d'énergie) est
      // un plafond de l'appareil, pas une surcharge : on n'y touche pas.
      var capped = spread < 2.5 && average < 40;
      if (average > SLOW_FRAME_MS && !capped && Math.min(wanted, cap) > 1) {
        cap = Math.max(1, Math.min(wanted, cap) - STEP);
        goodSince = 0;
        resized = applyRatio();
      } else if (average < FAST_FRAME_MS && cap < wanted) {
        if (!goodSince) goodSince = now;
        else if (now - goodSince > 8000) {
          cap = cap + STEP >= wanted ? Infinity : cap + STEP;
          goodSince = 0;
          resized = applyRatio();
        }
      } else {
        goodSince = 0;
      }
      /* Changer la définition redimensionne le canevas, ce qui EFFACE l'image
         qui vient d'être dessinée : le navigateur affichait alors une image
         noire — un « éclairage qui s'éteint » un instant, à chaque palier
         (owner, 2026-10-29, aux échecs). L'image est redessinée aussitôt, à
         la nouvelle définition, avant d'être montrée. */
      if (resized) {
        stats.redraws++;
        if (scene && renderer.shadowMap.enabled) scene.autoUpdate = false;
        try {
          render.call(renderer, scene, camera);
        } finally {
          if (scene && renderer.shadowMap.enabled) scene.autoUpdate = auto;
        }
      }
    };
    return renderer;
  }

  var Original = THREE.WebGLRenderer;
  function MindspilleRenderer(parameters) {
    return enhance(new Original(parameters));
  }
  MindspilleRenderer.prototype = Original.prototype;
  THREE.WebGLRenderer = MindspilleRenderer;

  setInterval(sweep, SWEEP_MS);

  /* Lisible de l'extérieur : tests, débogage. */
  window.MS3D = { stats: stats, sweep: sweep, scenes: scenes, last: null };
})();
