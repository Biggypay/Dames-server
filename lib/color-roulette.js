'use strict';

/**
 * Roulette Royale côté serveur : les règles partagées (public/roulette-rules.js)
 * et ce que seul le serveur peut faire — tirer au hasard et sceller ce tirage.
 *
 * Le tirage d'une manche est fait AVANT les choix des joueurs, avec
 * `crypto.randomInt` (aléa cryptographique, uniforme), puis scellé : le
 * serveur publie l'empreinte SHA-256 de « la valeur tirée + un sel secret de
 * 128 bits ». Après les choix, il révèle la valeur et le sel ; chacun peut
 * recalculer l'empreinte. La couleur ne peut donc pas avoir été choisie en
 * connaissant les choix — ni pour un joueur, ni contre lui.
 */

const crypto = require('crypto');
const Rules = require('../public/roulette-rules.js');

function hashSeal(roomId, round, kind, value, salt) {
  return crypto.createHash('sha256').update(Rules.sealText(roomId, round, kind, value, salt)).digest('hex');
}

/**
 * Le tirage scellé d'une manche. Manche normale : une couleur sur six.
 * Manche décisive : un bit (la plus petite ou la plus grande des deux couleurs
 * qui seront choisies).
 */
function sealDraw(roomId, round, decisive, random = crypto) {
  const kind = decisive ? 'bit' : 'color';
  const value = decisive ? random.randomInt(0, 2) : random.randomInt(0, Rules.COLOR_COUNT);
  const salt = random.randomBytes(16).toString('hex');
  return { kind, value, salt, hash: hashSeal(roomId, round, kind, value, salt) };
}

/** Le sceau publié correspond-il à la valeur et au sel révélés ? */
function verifySeal(roomId, round, seal) {
  if (!seal || typeof seal.hash !== 'string') return false;
  if (seal.kind !== 'color' && seal.kind !== 'bit') return false;
  return hashSeal(roomId, round, seal.kind, seal.value, seal.salt) === seal.hash;
}

/** Un sceau relu après un redémarrage : intact, ou rien. */
function sanitizeSeal(roomId, round, seal) {
  if (!seal || typeof seal !== 'object') return null;
  const clean = {
    kind: seal.kind === 'bit' ? 'bit' : 'color',
    value: Number(seal.value),
    salt: typeof seal.salt === 'string' ? seal.salt : '',
    hash: typeof seal.hash === 'string' ? seal.hash : ''
  };
  return /^[0-9a-f]{32}$/.test(clean.salt) && verifySeal(roomId, round, clean) ? clean : null;
}

module.exports = { ...Rules, Rules, hashSeal, sealDraw, verifySeal, sanitizeSeal };
