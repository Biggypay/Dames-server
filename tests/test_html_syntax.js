const fs = require('fs');
const path = require('path');

const files = [
  'public/quoridor-online.html',
  'public/ttt_game.html',
  'public/chifoumi-online.html',
  'public/penalty-online.html'
];

for (const relativePath of files) {
  const html = fs.readFileSync(path.join(__dirname, '..', relativePath), 'utf8');
  const scripts = [...html.matchAll(/<script(?:\s[^>]*)?>([\s\S]*?)<\/script>/gi)]
    .map(match => match[1])
    .filter(script => script.trim());
  for (const script of scripts) new Function(script);
  console.log('  OK browser script syntax:', relativePath);
}

console.log('OK 2D browser script syntax tests passed');
