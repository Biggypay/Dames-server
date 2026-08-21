'use strict';
const fs=require('fs');
const p='scripts/apply-quoridor-chess-series.cjs';
let s=fs.readFileSync(p,'utf8');
s=s.replaceAll("let s=fs.readFileSync(file,'utf8');","let s=fs.readFileSync(file,'utf8').replace(/\\r\\n/g,'\\n');");
fs.writeFileSync(p,s);
console.log('patcher now normalizes CRLF inputs');
