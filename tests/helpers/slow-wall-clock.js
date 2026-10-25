'use strict';
/*
 * Préchargé dans le serveur (node --require) par test_chess_clock_runtime :
 * l'horloge murale (Date.now) avance 0,1 % moins vite que celle des minuteurs,
 * comme une horloge système que NTP ralentit. Un minuteur réglé sur le temps
 * restant sonne alors 1 à 2 ms « avant » l'heure que lit Date.now() — ce qui
 * arrive aussi, en vrai, par simple arrondi entre les deux horloges (une fois
 * en CI, le 2026-10-25). Le drapeau doit tomber quand même.
 */
const realNow = Date.now.bind(Date);
const origin = realNow();
Date.now = () => Math.floor(origin + (realNow() - origin) * 0.999);
