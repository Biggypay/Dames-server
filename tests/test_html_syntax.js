const fs = require('fs');
const path = require('path');

const files = [
  'public/quoridor-online.html',
  'public/ttt_game.html',
  'public/chifoumi-online.html',
  'public/penalty-online.html',
  'public/gomoku-online.html',
  'public/gomoku_ai.html',
  'public/tikan-online.html',
  'public/local-pass-and-play.html',
  'public/roulette-online.html',
  'public/roulette_ai.html',
  'public/roulette_local.html',
  'public/roulette-rules.js',
  'public/roulette-board.js',
  'public/roulette-offline.js'
];

for (const relativePath of files) {
  const html = fs.readFileSync(path.join(__dirname, '..', relativePath), 'utf8');
  // Un module .js se vérifie tel quel ; une page, script par script.
  const scripts = relativePath.endsWith('.js') ? [html] : [...html.matchAll(/<script(?:\s[^>]*)?>([\s\S]*?)<\/script>/gi)]
    .map(match => match[1])
    .filter(script => script.trim());
  for (const script of scripts) new Function(script);
  console.log('  OK browser script syntax:', relativePath);
}

console.log('OK 2D browser script syntax tests passed');
