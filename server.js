// ============================================================
//  SERVEUR JEU DE DAMES — Socket.io + Express
//  Matchmaking automatique + jeu hébergé sur /game
//  Render.com — Node 20
// ============================================================

require(‘dotenv’).config();

const express      = require(‘express’);
const http         = require(‘http’);
const fs           = require(‘fs’);
const path         = require(‘path’);
const { Server }   = require(‘socket.io’);
const bcrypt       = require(‘bcryptjs’);
const jwt          = require(‘jsonwebtoken’);
const { v4: uuid } = require(‘uuid’);

const app    = express();
const server = http.createServer(app);
const PUBLIC = path.join(__dirname, ‘public’);

const PORT       = process.env.PORT || 3000;
const JWT_SECRET = process.env.JWT_SECRET || ‘checkers_secret_2025’;
const ORIGIN     = process.env.ALLOWED_ORIGIN || ‘*’;

// ── COMMISSION PLATEFORME ─────────────────────────────────
const PLATFORM_FEE_RATE = 0.10; // 10%

const io = new Server(server, {
cors: { origin: ORIGIN, methods: [‘GET’, ‘POST’] }
});

app.use(express.json());
app.use((req, res, next) => {
res.setHeader(‘Access-Control-Allow-Origin’, ORIGIN);
res.setHeader(‘Access-Control-Allow-Headers’, ‘Content-Type, Authorization’);
res.setHeader(‘Access-Control-Allow-Methods’, ‘GET, POST, OPTIONS’);
res.setHeader(‘X-Frame-Options’, ‘ALLOWALL’);
res.setHeader(‘Content-Security-Policy’, ‘frame-ancestors *’);
if (req.method === ‘OPTIONS’) return res.sendStatus(204);
next();
});

// ── STOCKAGE EN MÉMOIRE ───────────────────────────────────
const users       = new Map();
const games       = new Map();
const queue       = new Map(); // betAmount → [joueurs en attente]
const socketUsers = new Map(); // socketId → userId
const tttGames    = new Map(); // gameId  → ttt game state

// ── MOTEUR DAMES 10x10 ────────────────────────────────────
const EMPTY=0,WHITE=1,BLACK=2,WKING=3,BKING=4;
const isKing  = p=>p===WKING||p===BKING;
const isWhite = p=>p===WHITE||p===WKING;
const isBlack = p=>p===BLACK||p===BKING;
const isOwn   = (p,pl)=>pl===‘white’?isWhite(p):isBlack(p);
const isEnemy = (p,pl)=>pl===‘white’?isBlack(p):isWhite(p);
const inBounds= (r,c)=>r>=0&&r<10&&c>=0&&c<10;
const copyB   = b=>b.map(r=>[…r]);

function initialBoard(){
const b=Array.from({length:10},()=>Array(10).fill(EMPTY));
for(let r=0;r<4;r++) for(let c=0;c<10;c++) if((r+c)%2===1) b[r][c]=BLACK;
for(let r=6;r<10;r++) for(let c=0;c<10;c++) if((r+c)%2===1) b[r][c]=WHITE;
return b;
}

function getSimpleMoves(r,c,b){
const piece=b[r][c],moves=[];
if(!isKing(piece)){
const dirs=isWhite(piece)?[[-1,-1],[-1,1]]:[[1,-1],[1,1]];
for(const[dr,dc]of dirs){const nr=r+dr,nc=c+dc;if(inBounds(nr,nc)&&b[nr][nc]===EMPTY)moves.push({to:[nr,nc],capturedPieces:[]});}
}else{
for(const[dr,dc]of[[-1,-1],[-1,1],[1,-1],[1,1]]){let nr=r+dr,nc=c+dc;while(inBounds(nr,nc)&&b[nr][nc]===EMPTY){moves.push({to:[nr,nc],capturedPieces:[]});nr+=dr;nc+=dc;}}
}
return moves;
}

function getCaptures(r,c,b,player,already=[]){
const piece=b[r][c],results=[];
if(!isKing(piece)){
for(const[dr,dc]of[[-1,-1],[-1,1],[1,-1],[1,1]]){
const mr=r+dr,mc=c+dc,lr=r+2*dr,lc=c+2*dc;
if(!inBounds(lr,lc)||!isEnemy(b[mr][mc],player)||b[lr][lc]!==EMPTY)continue;
const key=`${mr},${mc}`;if(already.includes(key))continue;
const nb=copyB(b),cp=b[mr][mc];nb[lr][lc]=piece;nb[r][c]=EMPTY;nb[mr][mc]=EMPTY;
const f=getCaptures(lr,lc,nb,player,[…already,key]);
if(f.length)for(const x of f)results.push({to:x.to,capturedPieces:[{r:mr,c:mc,piece:cp},…x.capturedPieces]});
else results.push({to:[lr,lc],capturedPieces:[{r:mr,c:mc,piece:cp}]});
}
}else{
for(const[dr,dc]of[[-1,-1],[-1,1],[1,-1],[1,1]]){
let nr=r+dr,nc=c+dc;
while(inBounds(nr,nc)&&b[nr][nc]===EMPTY){nr+=dr;nc+=dc;}
if(!inBounds(nr,nc)||!isEnemy(b[nr][nc],player))continue;
const key=`${nr},${nc}`;if(already.includes(key))continue;
const ep=b[nr][nc];let lr=nr+dr,lc=nc+dc;
while(inBounds(lr,lc)&&b[lr][lc]===EMPTY){
const nb=copyB(b);nb[lr][lc]=piece;nb[r][c]=EMPTY;nb[nr][nc]=EMPTY;
const f=getCaptures(lr,lc,nb,player,[…already,key]);
if(f.length)for(const x of f)results.push({to:x.to,capturedPieces:[{r:nr,c:nc,piece:ep},…x.capturedPieces]});
else results.push({to:[lr,lc],capturedPieces:[{r:nr,c:nc,piece:ep}]});
lr+=dr;lc+=dc;
}
}
}
return results;
}

function getAllCaptures(player,b){
const all=[];
for(let r=0;r<10;r++)for(let c=0;c<10;c++)
if(isOwn(b[r][c],player))for(const m of getCaptures(r,c,b,player))all.push({from:[r,c],…m});
return all;
}

function hasAnyMove(player,b){
for(let r=0;r<10;r++)for(let c=0;c<10;c++)
if(isOwn(b[r][c],player)){
if(getSimpleMoves(r,c,b).length)return true;
if(getCaptures(r,c,b,player).length)return true;
}
return false;
}

function applyMove(board,player,fromR,fromC,toR,toC){
if(!inBounds(fromR,fromC)||!inBounds(toR,toC))return{ok:false,reason:‘Hors limites’};
if(!isOwn(board[fromR][fromC],player))return{ok:false,reason:‘Pièce invalide’};
const allCaps=getAllCaptures(player,board);
const max=allCaps.length?Math.max(…allCaps.map(m=>m.capturedPieces.length)):0;
const forced=allCaps.filter(m=>m.capturedPieces.length===max&&max>0);
let chosen=null;
if(forced.length){
const mine=forced.filter(m=>m.from[0]===fromR&&m.from[1]===fromC);
if(!mine.length)return{ok:false,reason:‘Capturez avec une autre pièce’};
chosen=mine.find(m=>m.to[0]===toR&&m.to[1]===toC);
if(!chosen)return{ok:false,reason:‘Capture maximale obligatoire’};
}else{
chosen=getSimpleMoves(fromR,fromC,board).find(m=>m.to[0]===toR&&m.to[1]===toC);
if(!chosen)return{ok:false,reason:‘Mouvement illégal’};
}
const nb=copyB(board),piece=nb[fromR][fromC];
nb[toR][toC]=piece;nb[fromR][fromC]=EMPTY;
for(const cp of chosen.capturedPieces)nb[cp.r][cp.c]=EMPTY;
let promoted=false;
if(piece===WHITE&&toR===0){nb[toR][toC]=WKING;promoted=true;}
if(piece===BLACK&&toR===9){nb[toR][toC]=BKING;promoted=true;}
let w=0,bl=0;
for(let r=0;r<10;r++)for(let c=0;c<10;c++){if(isWhite(nb[r][c]))w++;if(isBlack(nb[r][c]))bl++;}
let winner=null;
if(w===0)winner=‘black’;
else if(bl===0)winner=‘white’;
const next=player===‘white’?‘black’:‘white’;
if(!winner&&!hasAnyMove(next,nb))winner=player;
return{ok:true,board:nb,captured:chosen.capturedPieces,promoted,winner,next:winner?null:next};
}

// ── AUTH MIDDLEWARE ────────────────────────────────────────
function requireAuth(req,res,next){
const h=req.headers[‘authorization’]||’’;
if(!h.startsWith(’Bearer ’))return res.status(401).json({error:‘Token manquant’});
try{req.userId=jwt.verify(h.slice(7),JWT_SECRET).userId;next();}
catch{res.status(401).json({error:‘Token invalide’});}
}

function emitToUser(userId,event,data){
for(const[sid,uid]of socketUsers.entries())
if(uid===userId)io.to(sid).emit(event,data);
}

// ══════════════════════════════════════════════════════════
//  RÉSOLUTION FINANCIÈRE — appelée à chaque fin de partie
//  Calcule la commission, le gain net, et envoie à chaque
//  joueur son payload personnalisé (gagnant ≠ perdant)
// ══════════════════════════════════════════════════════════
function resolveFinancials(betAmount) {
const bet        = Number(betAmount) || 0;
const totalPot   = bet * 2;
const commission = Math.round(totalPot * PLATFORM_FEE_RATE); // 10% arrondi
const payout     = totalPot - commission;                     // gain net du vainqueur
return { bet, totalPot, commission, payout };
}

// ── NOTIFICATION FIN DE PARTIE (DAMES) ───────────────────
function notifyGameOver(game, winner, reason = ‘checkmate’) {
if (game.status === ‘finished’) return; // éviter double notification
game.status  = ‘finished’;
game.winner  = winner;

if (game.disconnectTimer) {
clearTimeout(game.disconnectTimer);
game.disconnectTimer = null;
}

const winnerId = winner === ‘white’ ? game.playerWhite : game.playerBlack;
const loserId  = winner === ‘white’ ? game.playerBlack : game.playerWhite;
const wUser    = users.get(winnerId);
const lUser    = users.get(loserId);

// ── Calcul financier ──────────────────────────────────
const { bet, totalPot, commission, payout } = resolveFinancials(game.betAmount);

// ── Payload commun (données de la partie) ─────────────
const commonPayload = {
type:            ‘game_over’,
gameId:          game.id,
winnerColor:     winner,
winnerName:      wUser?.username,
loserName:       lUser?.username,
winnerSupabaseId: wUser?.supabaseId,
loserSupabaseId:  lUser?.supabaseId,
reason,
// Données financières complètes — visibles par les deux joueurs
bet,          // mise individuelle de chaque joueur
totalPot,     // pot total (bet × 2)
commission,   // frais plateforme (10%)
payout,       // gain net du vainqueur (totalPot - commission)
};

// ── Payload personnalisé GAGNANT ──────────────────────
const winnerPayload = {
…commonPayload,
winner:      ‘player1’,          // convention Lovable
result:      ‘win’,
amountDelta: +payout,            // positif → argent gagné
// newBalance: à calculer depuis Supabase si tu as l’accès ici
};

// ── Payload personnalisé PERDANT ──────────────────────
const loserPayload = {
…commonPayload,
winner:      ‘player1’,          // le gagnant reste player1
result:      ‘loss’,
amountDelta: -bet,               // négatif → argent perdu
};

// ── Émission individuelle ─────────────────────────────
// Chaque joueur reçoit son résultat personnel
emitToUser(winnerId, ‘game:over’,   winnerPayload);
emitToUser(winnerId, ‘game:result’, { postMessage: winnerPayload });

emitToUser(loserId,  ‘game:over’,   loserPayload);
emitToUser(loserId,  ‘game:result’, { postMessage: loserPayload });

// Broadcast room pour compatibilité (optionnel)
io.to(game.id).emit(‘game:over_broadcast’, commonPayload);

console.log(
`🏆 ${wUser?.username} bat ${lUser?.username} (${reason})` +
` | Mise: ${bet} HTG | Pot: ${totalPot} HTG | Commission: ${commission} HTG | Gain net: ${payout} HTG`
);
}

// ══════════════════════════════════════════════════════════
//  ROUTES
// ══════════════════════════════════════════════════════════

app.get(’/health’,(req,res)=>res.json({
status:‘ok’,time:new Date().toISOString(),
games:games.size,
queue:[…queue.entries()].map(([amt,p])=>({betAmount:amt,waiting:p.length}))
}));

app.get(’/game’,(req,res)=>{
const f=path.join(PUBLIC,‘game.html’);
if(fs.existsSync(f)){res.setHeader(‘Content-Type’,‘text/html; charset=utf-8’);res.send(fs.readFileSync(f,‘utf8’));}
else res.status(404).send(‘game.html introuvable dans /public’);
});

app.get(’/ttt’,(req,res)=>{
const f=path.join(PUBLIC,‘ttt_game.html’);
if(fs.existsSync(f)){res.setHeader(‘Content-Type’,‘text/html; charset=utf-8’);res.send(fs.readFileSync(f,‘utf8’));}
else res.status(404).send(‘ttt_game.html introuvable dans /public’);
});

// ── AUTH ──────────────────────────────────────────────────
app.post(’/auth/register’,(req,res)=>{
const{username,password,supabaseId}=req.body;
if(!username||!password)return res.status(400).json({error:‘Champs requis’});
for(const u of users.values())if(u.username===username)return res.status(409).json({error:‘Nom déjà pris’});
const id=uuid();
users.set(id,{id,username,password:bcrypt.hashSync(password,10),supabaseId:supabaseId||null});
const token=jwt.sign({userId:id},JWT_SECRET,{expiresIn:‘7d’});
res.json({token,userId:id,username});
});

app.post(’/auth/login’,(req,res)=>{
const{username,password,supabaseId}=req.body;
const user=[…users.values()].find(u=>u.username===username);
if(!user||!bcrypt.compareSync(password,user.password))return res.status(401).json({error:‘Identifiants incorrects’});
if(supabaseId)user.supabaseId=supabaseId;
const token=jwt.sign({userId:user.id},JWT_SECRET,{expiresIn:‘7d’});
res.json({token,userId:user.id,username:user.username});
});

// ── MATCHMAKING ───────────────────────────────────────────
app.post(’/matchmaking/join’,requireAuth,(req,res)=>{
const{betAmount,supabaseId,username}=req.body;
if(!betAmount||betAmount<=0)return res.status(400).json({error:‘Montant invalide’});

const userId=req.userId;
let user=users.get(userId);
if(!user){user={id:userId,username:username||‘Joueur’,supabaseId:supabaseId||null};users.set(userId,user);}
else{if(username)user.username=username;if(supabaseId)user.supabaseId=supabaseId;}

const existing=queue.get(betAmount)||[];
if(existing.some(p=>p.userId===userId))
return res.json({status:‘waiting’,message:‘En attente d'un adversaire…’});

const opponent=existing.find(p=>p.userId!==userId);

if(opponent){
queue.set(betAmount,existing.filter(p=>p.userId!==opponent.userId));
const whiteIsMe=Math.random()<0.5;
const whiteId=whiteIsMe?userId:opponent.userId;
const blackId=whiteIsMe?opponent.userId:userId;
const gameId=uuid();

```
games.set(gameId,{
  id:gameId,playerWhite:whiteId,playerBlack:blackId,
  board:initialBoard(),currentPlayer:'white',
  status:'playing',winner:null,betAmount,
  disconnectTimer:null,
});

const wUser=users.get(whiteId);
const bUser=users.get(blackId);
const host=`${req.protocol}://${req.get('host')}`;
const base={gameId,betAmount,white:{userId:whiteId,username:wUser?.username,supabaseId:wUser?.supabaseId},black:{userId:blackId,username:bUser?.username,supabaseId:bUser?.supabaseId}};

emitToUser(whiteId,'match:found',{...base,youAre:'white',gameUrl:`${host}/game?gameId=${gameId}&player=${whiteId}`});
emitToUser(blackId,'match:found',{...base,youAre:'black',gameUrl:`${host}/game?gameId=${gameId}&player=${blackId}`});

console.log(`✅ Match: ${wUser?.username}(⬜) vs ${bUser?.username}(⬛) — ${betAmount} HTG`);
return res.json({status:'matched',gameId,youAre:whiteIsMe?'white':'black',opponent:opponent.username,betAmount,gameUrl:`${host}/game?gameId=${gameId}&player=${userId}`});
```

}else{
existing.push({userId,username:user.username,supabaseId:user.supabaseId});
queue.set(betAmount,existing);
console.log(`⏳ File: ${user.username} — ${betAmount} HTG (${existing.length} en attente)`);
return res.json({status:‘waiting’,message:‘En attente d'un adversaire…’});
}
});

app.post(’/matchmaking/leave’,requireAuth,(req,res)=>{
const{betAmount}=req.body;
if(betAmount){const ex=queue.get(betAmount)||[];queue.set(betAmount,ex.filter(p=>p.userId!==req.userId));}
else for(const[amt,pl]of queue.entries())queue.set(amt,pl.filter(p=>p.userId!==req.userId));
res.json({status:‘left’});
});

app.post(’/game/join’,requireAuth,(req,res)=>{
const{gameId,username,supabaseId,color,betAmount}=req.body;
if(!gameId)return res.status(400).json({error:‘gameId requis’});

const userId=req.userId;
let user=users.get(userId);
if(!user){user={id:userId,username:username||‘Joueur’,supabaseId:supabaseId||null};users.set(userId,user);}
else{if(username)user.username=username;if(supabaseId)user.supabaseId=supabaseId;}

let game=games.get(gameId);

if(!game){
game={
id:gameId,
playerWhite:color===‘black’?null:userId,
playerBlack:color===‘black’?userId:null,
board:initialBoard(),
currentPlayer:‘white’,
status:‘waiting’,
winner:null,
betAmount:betAmount||0,
disconnectTimer:null,
};
games.set(gameId,game);
console.log(‘🏠 Salle créée:’,gameId,user.username,’(’,color,’)’);
return res.json({status:‘waiting’,gameId,message:‘En attente du 2ème joueur…’});
}

if(game.status===‘playing’){
const myColor=game.playerWhite===userId?‘white’:game.playerBlack===userId?‘black’:color||‘white’;
return res.json({status:‘ready’,gameId,youAre:myColor});
}

if(!game.playerWhite)game.playerWhite=userId;
else if(!game.playerBlack)game.playerBlack=userId;

game.status=‘playing’;

const myColor=game.playerWhite===userId?‘white’:‘black’;
const wUser=users.get(game.playerWhite);
const bUser=users.get(game.playerBlack);
const host=req.protocol+’://’+req.get(‘host’);
const base={gameId,betAmount:game.betAmount,white:{userId:game.playerWhite,username:wUser?.username,supabaseId:wUser?.supabaseId},black:{userId:game.playerBlack,username:bUser?.username,supabaseId:bUser?.supabaseId}};

emitToUser(game.playerWhite,‘match:found’,{…base,youAre:‘white’,gameUrl:host+’/game?gameId=’+gameId+’&player=’+game.playerWhite});
emitToUser(game.playerBlack,‘match:found’,{…base,youAre:‘black’,gameUrl:host+’/game?gameId=’+gameId+’&player=’+game.playerBlack});

console.log(‘✅ Partie démarrée via /game/join:’,wUser?.username,‘vs’,bUser?.username,gameId);
return res.json({status:‘ready’,gameId,youAre:myColor,opponent:myColor===‘white’?bUser?.username:wUser?.username});
});

// ── PARTIES ───────────────────────────────────────────────
app.get(’/games/:id’,requireAuth,(req,res)=>{
const game=games.get(req.params.id);
if(!game)return res.status(404).json({error:‘Partie introuvable’});
const color=game.playerWhite===req.userId?‘white’:game.playerBlack===req.userId?‘black’:null;
if(!color)return res.status(403).json({error:‘Accès refusé’});
res.json({gameId:game.id,board:game.board,currentPlayer:game.currentPlayer,status:game.status,winner:game.winner,betAmount:game.betAmount,youAre:color,opponentName:color===‘white’?users.get(game.playerBlack)?.username:users.get(game.playerWhite)?.username});
});

app.post(’/games/:id/move’,requireAuth,(req,res)=>{
const game=games.get(req.params.id);
if(!game||game.status!==‘playing’)return res.status(400).json({error:‘Partie non disponible’});
const color=game.playerWhite===req.userId?‘white’:game.playerBlack===req.userId?‘black’:null;
if(!color)return res.status(403).json({error:‘Accès refusé’});
if(game.currentPlayer!==color)return res.status(400).json({error:‘Pas votre tour’});
const{fromRow,fromCol,toRow,toCol}=req.body;
const result=applyMove(game.board,color,+fromRow,+fromCol,+toRow,+toCol);
if(!result.ok)return res.status(400).json({error:result.reason});
game.board=result.board;
game.currentPlayer=result.winner?null:result.next;
const update={gameId:game.id,board:game.board,currentPlayer:game.currentPlayer,status:game.status,winner:game.winner,lastMove:{fromRow,fromCol,toRow,toCol,captured:result.captured},promoted:result.promoted};
io.to(game.id).emit(‘game:move’,update);
if(result.winner)notifyGameOver(game,result.winner,‘checkmate’);
res.json(update);
});

app.post(’/games/:id/resign’,requireAuth,(req,res)=>{
const game=games.get(req.params.id);
if(!game||game.status!==‘playing’)return res.status(400).json({error:‘Impossible’});
const color=game.playerWhite===req.userId?‘white’:‘black’;
notifyGameOver(game,color===‘white’?‘black’:‘white’,‘resign’);
res.json({ok:true});
});

// ── SOCKET.IO ─────────────────────────────────────────────
io.on(‘connection’,(socket)=>{
console.log(‘🔌’,socket.id);

socket.on(‘auth’,({token})=>{
try{
const{userId}=jwt.verify(token,JWT_SECRET);
socketUsers.set(socket.id,userId);socket.userId=userId;
socket.emit(‘auth:ok’,{userId});
}catch{socket.emit(‘auth:error’,{message:‘Token invalide’});}
});

socket.on(‘auth:supabase’,({supabaseId,username})=>{
if(!supabaseId)return;
let found=null;
for(const u of users.values())if(u.supabaseId===supabaseId){found=u;break;}
if(!found){const id=uuid();found={id,username:username||‘Joueur’,supabaseId};users.set(id,found);}
socketUsers.set(socket.id,found.id);socket.userId=found.id;
const token=jwt.sign({userId:found.id},JWT_SECRET,{expiresIn:‘7d’});
socket.emit(‘auth:ok’,{userId:found.id,token});
});

socket.on(‘game:join_room’,({gameId})=>{
socket.join(gameId);
});

// ── TTT : rejoindre la partie ─────────────────────────
socket.on(‘ttt:join’, ({gameId, playerId}) => {
if(!gameId) return;
socket.join(gameId);

```
let game = tttGames.get(gameId);
if(!game){
  game = {
    id: gameId,
    players: [{socketId: socket.id, userId: socket.userId || playerId, symbol: 'X'}],
    board: [null,null,null,null,null,null,null,null,null],
    curTurn: 'X',
    scores: {X:0, O:0},
    round: 1,
    tieBreak: false,
    nextStarter: 'X',
    status: 'waiting',
    betAmount: 0, // sera mis à jour si transmis
    disconnectTimer: null,
  };
  tttGames.set(gameId, game);
  console.log('🎮 TTT salle créée:', gameId);
} else if(game.players.length === 1 && game.players[0].socketId !== socket.id){
  game.players.push({socketId: socket.id, userId: socket.userId || playerId, symbol: 'O'});
  game.status = 'playing';
  console.log('🎮 TTT partie démarrée:', gameId);

  const p1 = game.players[0];
  const p2 = game.players[1];

  io.to(p1.socketId).emit('ttt:ready', {
    symbol: 'X', myName: 'Joueur 1', opponentName: 'Joueur 2', gameId,
  });
  io.to(p2.socketId).emit('ttt:ready', {
    symbol: 'O', myName: 'Joueur 2', opponentName: 'Joueur 1', gameId,
  });
} else if(game.players.length === 2){
  const me = game.players.find(p => p.userId === (socket.userId || playerId));
  if(!me) return;
  me.socketId = socket.id;

  if(game.disconnectTimer){
    clearTimeout(game.disconnectTimer);
    game.disconnectTimer = null;
    io.to(gameId).emit('player:reconnected', {message: 'Adversaire reconnecté !'});
  }

  socket.emit('ttt:state', {
    board: game.board, curTurn: game.curTurn,
    scores: game.scores, round: game.round,
    tieBreak: game.tieBreak, nextStarter: game.nextStarter,
    symbol: me.symbol, opponentName: 'Adversaire',
  });
}
```

});

// ── TTT : coup joué ───────────────────────────────────
socket.on(‘ttt:move’, ({gameId, cell, symbol}) => {
const game = tttGames.get(gameId);
if(!game || game.status !== ‘playing’) return;
if(game.curTurn !== symbol) return;
if(game.board[cell] !== null) return;
game.board[cell] = symbol;
game.curTurn = symbol === ‘X’ ? ‘O’ : ‘X’;
socket.to(gameId).emit(‘ttt:move’, {cell, symbol});
});

// ── TTT : fin de manche ───────────────────────────────
socket.on(‘ttt:round_end’, ({gameId, scores, round, nextStarter, tieBreak}) => {
const game = tttGames.get(gameId);
if(!game) return;
game.scores      = scores;
game.round       = round;
game.nextStarter = nextStarter;
game.tieBreak    = tieBreak;
game.board       = [null,null,null,null,null,null,null,null,null];
game.curTurn     = nextStarter;
});

// ── TTT : fin de match ────────────────────────────────
socket.on(‘ttt:match_over’, ({gameId, winner, scores, betAmount}) => {
const game = tttGames.get(gameId);
if(!game || game.status === ‘finished’) return;
game.status = ‘finished’;

```
// Récupérer le betAmount depuis le message ou depuis la partie
const effectiveBet = betAmount || game.betAmount || 0;

const winPlayer = winner ? game.players.find(p => p.symbol === winner) : null;
const losPlayer = winner ? game.players.find(p => p.symbol !== winner) : null;

const wUser = winPlayer ? users.get(winPlayer.userId) : null;
const lUser = losPlayer ? users.get(losPlayer.userId) : null;

// ── Calcul financier ──────────────────────────────
const { bet, totalPot, commission, payout } = resolveFinancials(effectiveBet);

// Payload commun
const commonPayload = {
  type:            'game_over',
  gameId,
  winner:          winner ? (winner === 'X' ? 'player1' : 'player2') : null,
  winnerSymbol:    winner,
  winnerName:      wUser?.username || winPlayer?.symbol,
  loserName:       lUser?.username || losPlayer?.symbol,
  winnerSupabaseId: wUser?.supabaseId || winPlayer?.userId,
  loserSupabaseId:  lUser?.supabaseId || losPlayer?.userId,
  scores,
  reason:          'match',
  // Données financières
  bet,
  totalPot,
  commission,
  payout,
};

// Payload personnalisé GAGNANT
if (winPlayer) {
  const winnerPayload = { ...commonPayload, result: 'win',  amountDelta: +payout };
  io.to(winPlayer.socketId).emit('ttt:over',    winnerPayload);
  io.to(winPlayer.socketId).emit('game:over',   winnerPayload);
  io.to(winPlayer.socketId).emit('game:result', { postMessage: winnerPayload });
}

// Payload personnalisé PERDANT
if (losPlayer) {
  const loserPayload = { ...commonPayload, result: 'loss', amountDelta: -bet };
  io.to(losPlayer.socketId).emit('ttt:over',    loserPayload);
  io.to(losPlayer.socketId).emit('game:over',   loserPayload);
  io.to(losPlayer.socketId).emit('game:result', { postMessage: loserPayload });
}

// Broadcast salle (nul ou compatibilité)
if (!winner) {
  io.to(gameId).emit('ttt:over',    { ...commonPayload, result: 'draw', amountDelta: 0 });
  io.to(gameId).emit('game:over',   { ...commonPayload, result: 'draw', amountDelta: 0 });
  io.to(gameId).emit('game:result', { postMessage: { ...commonPayload, result: 'draw' } });
}

console.log(
  `🏆 TTT match terminé: ${gameId} | Gagnant: ${winner || 'nul'}` +
  ` | Mise: ${bet} HTG | Pot: ${totalPot} HTG | Commission: ${commission} HTG | Gain: ${payout} HTG`
);
```

});

// ── RECONNEXION ───────────────────────────────────────
socket.on(‘game:rejoin’,({gameId})=>{
const game=games.get(gameId);
if(!game) return;
if(game.disconnectTimer){
clearTimeout(game.disconnectTimer);
game.disconnectTimer=null;
console.log(`✅ Reconnexion — timer forfait annulé (${gameId})`);
io.to(gameId).emit(‘player:reconnected’,{message:‘Adversaire reconnecté !’});
}
socket.join(gameId);
});

// ── DÉCONNEXION — forfait en 60s ──────────────────────
socket.on(‘disconnect’,()=>{
const userId=socketUsers.get(socket.id);
socketUsers.delete(socket.id);
if(!userId) return;

```
for(const [gameId,game] of games.entries()){
  if(game.status!=='playing') continue;
  const isWhite=game.playerWhite===userId;
  const isBlack=game.playerBlack===userId;
  if(!isWhite&&!isBlack) continue;
  if(game.disconnectTimer) continue;

  const disconnectedColor=isWhite?'white':'black';
  const winner=isWhite?'black':'white';

  console.log(`⚠️  ${disconnectedColor} déconnecté de ${gameId} — forfait dans 60s`);

  io.to(gameId).emit('player:disconnected',{
    color: disconnectedColor,
    countdown: 60,
    message: 'Adversaire déconnecté — victoire dans 60 secondes',
  });

  game.disconnectTimer=setTimeout(()=>{
    if(game.status!=='playing') return;
    console.log(`🏳️  Forfait ${disconnectedColor} — partie ${gameId}`);
    notifyGameOver(game,winner,'forfeit');
  },60000);

  break;
}

for(const [gameId, game] of tttGames.entries()){
  if(game.status !== 'playing') continue;
  const me = game.players.find(p => p.userId === userId);
  if(!me) continue;
  if(game.disconnectTimer) continue;

  const winner = me.symbol === 'X' ? 'O' : 'X';
  console.log('⚠️  TTT', me.symbol, 'déconnecté de', gameId, '— forfait dans 60s');

  io.to(gameId).emit('player:disconnected', {
    color: me.symbol,
    countdown: 60,
    message: 'Adversaire déconnecté — victoire dans 60 secondes',
  });

  game.disconnectTimer = setTimeout(() => {
    if(game.status !== 'playing') return;
    game.status = 'finished';
    const winPlayer = game.players.find(p => p.symbol === winner);
    const wUser = winPlayer ? users.get(winPlayer.userId) : null;
    const losPlayer = me;
    const lUser = users.get(losPlayer.userId);

    const { bet, totalPot, commission, payout } = resolveFinancials(game.betAmount);

    const commonPayload = {
      type: 'game_over', gameId,
      winner: winner === 'X' ? 'player1' : 'player2',
      winnerSymbol: winner,
      winnerSupabaseId: wUser?.supabaseId || winPlayer?.userId,
      loserSupabaseId:  lUser?.supabaseId || losPlayer?.userId,
      reason: 'forfeit',
      bet, totalPot, commission, payout,
    };

    if (winPlayer) {
      const wp = { ...commonPayload, result: 'win',  amountDelta: +payout };
      io.to(winPlayer.socketId).emit('ttt:over',    wp);
      io.to(winPlayer.socketId).emit('game:over',   wp);
      io.to(winPlayer.socketId).emit('game:result', { postMessage: wp });
    }
    const lp = { ...commonPayload, result: 'loss', amountDelta: -bet };
    io.to(losPlayer.socketId).emit('ttt:over',    lp);
    io.to(losPlayer.socketId).emit('game:over',   lp);
    io.to(losPlayer.socketId).emit('game:result', { postMessage: lp });

    console.log('🏳️  TTT forfait', me.symbol, '— partie', gameId);
  }, 60000);
  break;
}
```

});
});

server.listen(PORT,‘0.0.0.0’,()=>{
console.log(`✅ Serveur démarré sur le port ${PORT}`);
console.log(`   /game             → jeu HTML (iframe)`);
console.log(`   /matchmaking/join → matchmaking`);
console.log(`   /health           → status`);
});
