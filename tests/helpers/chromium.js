'use strict';
/*
 * Ou est le navigateur ? Reponse unique pour tous les parcours navigateur.
 *
 * Cette fonction existait en deux copies qui ont diverge : celle de
 * test_gomoku_ai_browser.js ne connaissait que des chemins Windows et rendait
 * donc toujours `undefined` ailleurs — le parcours s'annoncait « ignore » et
 * ne verifiait rien. C'est ce silence qui a laisse passer une ReferenceError
 * bloquant le mode IA du Gomoku des la deuxieme manche.
 *
 * L'autre copie ne connaissait que l'ancienne arborescence `chrome-linux/`.
 * Playwright livre desormais « Chrome for Testing », range dans
 * `chrome-linux64/`, et les runners GitHub telechargent cette version-la :
 * le navigateur etait bien installe, mais introuvable. On explore donc le
 * dossier au lieu de deviner sa forme.
 */
const fs = require('fs');
const path = require('path');

const EXECUTABLES = new Set(['chrome', 'headless_shell', 'chrome-headless-shell']);

const WINDOWS_CANDIDATES = [
  'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
  'C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe',
  'C:\\Program Files\\Microsoft\\Edge\\Application\\msedge.exe'
];

function chromiumBinary() {
  if (process.platform === 'win32') return WINDOWS_CANDIDATES.find(c => fs.existsSync(c));

  const root = process.env.PLAYWRIGHT_BROWSERS_PATH || '/opt/pw-browsers';
  if (!fs.existsSync(root)) return undefined;

  let installs;
  try {
    /* Le Chrome complet d'abord, le « headless shell » en repli : il suffit aux
       parcours sans interface, mais le navigateur entier reste plus proche de
       ce que voit un joueur. A version egale, la plus recente en tete. */
    installs = fs.readdirSync(root)
      .filter(name => name.startsWith('chromium'))
      .sort()
      .reverse()
      .sort((a, b) => Number(a.includes('headless')) - Number(b.includes('headless')));
  } catch {
    return undefined;
  }

  for (const install of installs) {
    const base = path.join(root, install);
    let layouts;
    try {
      layouts = fs.readdirSync(base, { withFileTypes: true }).filter(e => e.isDirectory()).map(e => e.name);
    } catch {
      continue;
    }
    for (const layout of layouts) {
      for (const executable of EXECUTABLES) {
        const candidate = path.join(base, layout, executable);
        if (fs.existsSync(candidate)) return candidate;
      }
    }
  }
  return undefined;
}

module.exports = { chromiumBinary };
