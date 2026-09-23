'use strict';

/**
 * Chronomètre par coup — la règle de toutes les parties en ligne :
 * 30 s pour jouer, puis 60 s de grâce, puis la défaite.
 *
 * Un tour a UN budget (turnMs + graceMs), et rien ne le recharge :
 *  - ni une reconnexion : recharger la page reprend le tour là où il en était ;
 *  - ni une déconnexion : tant que celui qui doit jouer est absent, son temps
 *    continue de couler (le serveur appelle `run` pendant son absence) ;
 *  - ni un redémarrage du serveur : le temps déjà consommé voyage avec la
 *    partie sauvegardée (`forSave` / `sanitize`).
 * Le budget n'est gelé (`freeze`) que lorsque celui qui doit jouer ne PEUT pas
 * jouer pour une raison qui ne dépend pas de lui : adversaire déconnecté,
 * pause d'arbitrage, serveur arrêté.
 *
 * Un tour est identifié par `key` (version du plateau, manche…) : le serveur
 * reprend l'horloge existante si la clé n'a pas changé, en crée une neuve
 * sinon. C'est ce qui rend impossible de « redémarrer » un tour.
 *
 * Module pur : ni minuterie, ni réseau. Le serveur arme ses setTimeout
 * d'après `msUntilNextPhase`. Testé par tests/test_turn_clock.js.
 */

const MAX_BUDGET_MS = 60 * 60 * 1000; // garde-fou contre un état corrompu

function create(key, now, turnMs, graceMs) {
  return { key: String(key), turnMs, graceMs, usedMs: 0, runningSince: now };
}

function usedMs(clock, now) {
  if (!clock) return 0;
  const running = clock.runningSince === null || clock.runningSince === undefined
    ? 0
    : Math.max(0, now - clock.runningSince);
  return clock.usedMs + running;
}

/** Arrête le temps : ce qui a été consommé est acquis. */
function freeze(clock, now) {
  if (!clock) return clock;
  clock.usedMs = usedMs(clock, now);
  clock.runningSince = null;
  return clock;
}

/** Relance le temps, sans rien rendre de ce qui a été consommé. */
function run(clock, now) {
  if (clock && (clock.runningSince === null || clock.runningSince === undefined)) clock.runningSince = now;
  return clock;
}

function totalMs(clock) {
  return clock.turnMs + clock.graceMs;
}

/** 'turn' (les 30 s), 'grace' (les 60 s) ou 'expired' (défaite). */
function phase(clock, now) {
  const used = usedMs(clock, now);
  if (used < clock.turnMs) return 'turn';
  if (used < totalMs(clock)) return 'grace';
  return 'expired';
}

function remainingMs(clock, now) {
  return Math.max(0, totalMs(clock) - usedMs(clock, now));
}

/** Délai avant le prochain changement de phase (fin des 30 s, puis défaite). */
function msUntilNextPhase(clock, now) {
  const used = usedMs(clock, now);
  if (used < clock.turnMs) return clock.turnMs - used;
  return Math.max(0, totalMs(clock) - used);
}

/**
 * Début « virtuel » de chaque phase, tel que les pages l'affichent : elles
 * comptent `startTime + duration - maintenant`. Un tour repris après 20 s
 * annonce donc un début 20 s dans le passé, et le compte à rebours est juste.
 */
function phaseStarts(clock, now) {
  const used = usedMs(clock, now);
  return {
    turnStartTime: now - used,
    graceStartTime: used >= clock.turnMs ? now - (used - clock.turnMs) : null
  };
}

/** Copie à sauvegarder : le temps écoulé est acquis, l'horloge est à l'arrêt. */
function forSave(clock, now) {
  if (!clock) return null;
  return { key: clock.key, turnMs: clock.turnMs, graceMs: clock.graceMs, usedMs: usedMs(clock, now), runningSince: null };
}

const validMs = value => Number.isFinite(value) && value >= 0 && value <= MAX_BUDGET_MS;

/** Relit une horloge sauvegardée ; `null` si elle n'a pas la forme attendue. */
function sanitize(raw) {
  if (!raw || typeof raw !== 'object') return null;
  if (typeof raw.key !== 'string' || !raw.key) return null;
  if (!validMs(raw.turnMs) || !validMs(raw.graceMs) || raw.turnMs + raw.graceMs <= 0) return null;
  if (!validMs(raw.usedMs)) return null;
  return { key: raw.key, turnMs: raw.turnMs, graceMs: raw.graceMs, usedMs: raw.usedMs, runningSince: null };
}

module.exports = {
  create,
  usedMs,
  freeze,
  run,
  phase,
  remainingMs,
  msUntilNextPhase,
  phaseStarts,
  forSave,
  sanitize
};
