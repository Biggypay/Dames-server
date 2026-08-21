'use strict';
const fs = require('fs');
const cp = require('child_process');

function run(cmd){ cp.execSync(cmd,{stdio:'inherit'}); }

// Reuse the already-tested Quoridor/Gomoku AI source from the superseded branch,
// but deliberately do NOT import any Chess, Checkers or server changes from it.
run('git fetch origin feat/quoridor-chess-six-rounds --quiet');
for (const file of ['public/quoridor_ai.html','public/gomoku_ai.html']) {
  const content = cp.execFileSync('git',['show',`origin/feat/quoridor-chess-six-rounds:${file}`],{encoding:'utf8'});
  fs.writeFileSync(file,content);
}

// Tic-Tac-Toe training already has the series UI/logic; its default was still 5.
const ttt = 'public/ttt_ai.html';
let s = fs.readFileSync(ttt,'utf8').replace(/\r\n/g,'\n');
s = s.replace("id=\"manche-lbl\">Manche 1 / 5<", "id=\"manche-lbl\">Manche 1 / 6<");
s = s.replace("var TOTAL_MANCHES=parseInt(P.get('manches')||'5',10);", "var TOTAL_MANCHES=parseInt(P.get('manches')||'6',10);");
if (!s.includes("P.get('manches')||'6'")) throw new Error('TicTacToe six-round default was not applied');
fs.writeFileSync(ttt,s);

console.log('Correct round contract ready: TTT, Quoridor and Gomoku AI use six rounds; Chess and Checkers remain single-game.');
