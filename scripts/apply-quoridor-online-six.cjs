'use strict';
const fs=require('fs');
const cp=require('child_process');

// Keep the already-reviewed Quoridor presentation from the superseded branch.
cp.execSync('git fetch origin feat/quoridor-chess-six-rounds --quiet');
fs.writeFileSync('public/quoridor-online.html',cp.execFileSync('git',['show','origin/feat/quoridor-chess-six-rounds:public/quoridor-online.html'],{encoding:'utf8'}));

const f='server.js';
let s=fs.readFileSync(f,'utf8').replace(/\r\n/g,'\n');

// Earlier validation runs have already applied the Quoridor-only series wiring.
// Normalize the remaining opening payload/state without ever touching Chess/Dames.
const duplicateStarter=`      qroom.currentSlot = randomOpeningSlot();\n      qroom.gameState.currentSlot = qroom.currentSlot;\n      ensureSeriesState(qroom).roundStarter = qroom.currentSlot;\n      qroom.currentSlot = randomOpeningSlot();\n      qroom.gameState.currentSlot = qroom.currentSlot;`;
const singleStarter=`      qroom.currentSlot = randomOpeningSlot();\n      qroom.gameState.currentSlot = qroom.currentSlot;\n      ensureSeriesState(qroom).roundStarter = qroom.currentSlot;`;
if(s.includes(duplicateStarter)) s=s.replace(duplicateStarter,singleStarter);

s=s.replace(
  "io.to(p1.socketId).emit('quoridor_start', { room, yourSlot: 1, opponentName: p2.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });",
  "io.to(p1.socketId).emit('quoridor_start', { room, yourSlot: 1, opponentName: p2.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false, currentSlot: qroom.currentSlot, series: seriesPayload(qroom) });"
);
s=s.replace(
  "io.to(p2.socketId).emit('quoridor_start', { room, yourSlot: 2, opponentName: p1.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false });",
  "io.to(p2.socketId).emit('quoridor_start', { room, yourSlot: 2, opponentName: p1.name, bet: qroom.betAmount, currency: qroom.currency, reconnected: false, currentSlot: qroom.currentSlot, series: seriesPayload(qroom) });"
);

const required=[
  'function finishQuoridorRound(',
  "quoridor_round_start",
  'ensureSeriesState(qroom)',
  'series: seriesPayload(qroom)',
  "return finishQuoridorRound(qroom, room, winnerSlot, 'normal')"
];
for(const marker of required) if(!s.includes(marker)) throw new Error('Missing required Quoridor marker: '+marker);
if(s.includes('function finishEchecsRound(')||s.includes("echecs_round_start")) throw new Error('Safety: Chess must remain single-game');

fs.writeFileSync(f,s);
console.log('Quoridor online six-round state normalized; Chess and Checkers remain single-game.');
