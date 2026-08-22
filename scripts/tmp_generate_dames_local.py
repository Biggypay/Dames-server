from pathlib import Path
import re
import subprocess
import tempfile

src_path = Path('public/dames_ai.html')
dst_path = Path('public/dames_local.html')
server_path = Path('server.js')

original = src_path.read_text(encoding='utf-8')
html = original

def replace_once(text, old, new, label):
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'{label}: expected exactly 1 occurrence, found {count}')
    return text.replace(old, new, 1)

html = replace_once(html, '<title>Dames 3D — Entraînement IA | Mindspille</title>', '<title>Dames 3D — Jouer avec un ami | Mindspille</title>', 'title')
html = replace_once(html, '<div class="profile-name" id="name-human">Vous</div>', '<div class="profile-name" id="name-human">Joueur 1</div>', 'player 1 header label')
html = replace_once(html, '<span class="manche-lbl">Entraînement · IA</span>', '<span class="manche-lbl">Jouer avec un ami</span>', 'mode header label')
html = replace_once(html, '<div class="profile-name" id="name-ai">Adv</div>', '<div class="profile-name" id="name-ai">Joueur 2</div>', 'player 2 header label')

old_mode = """// ── MODE ENTRAÎNEMENT vs IA (aucun argent, aucun réseau) ──
// L'humain est TOUJOURS Blanc (joue en premier), l'IA est Rouge.
var DIFFICULTY = (P.get('difficulty') || P.get('level') || 'expert').toLowerCase();
if(DIFFICULTY === 'max' || DIFFICULTY === 'extreme') DIFFICULTY = 'expert';
if(['easy','medium','hard','expert'].indexOf(DIFFICULTY) < 0) DIFFICULTY = 'expert';
var AI_DEBUG = !!P.get('debug');

var ROOM_ID = 'solo-ia';"""
new_mode = """// ── MODE HOTSEAT LOCAL (aucun argent, aucun réseau) ──
var HOTSEAT = true;
var AI_DEBUG = !!P.get('debug');
var DIFFICULTY = 'expert';

var ROOM_ID = 'local-hotseat';"""
html = replace_once(html, old_mode, new_mode, 'URL params hotseat mode')

html = replace_once(html, "var MY_NAME = P.get('name') || P.get('username') || 'Vous';\nvar OP_NAME = 'IA';", "var MY_NAME = P.get('name') || P.get('p1Name') || 'Joueur 1';\nvar OP_NAME = P.get('p2Name') || 'Joueur 2';", 'local player names')
html = replace_once(html, 'if(currentPlayer !== MY_PLAYER) return;', 'if(!HOTSEAT && currentPlayer !== MY_PLAYER) return;', 'hotseat input guard')

old_turn = """      currentPlayer = nextPlayer;
      showLastMoveOrigin(originRow, originCol);
      updUI(); stopTimer();
      // ── C'est au tour de l'IA (Rouge) ──
      isProcessing = true;                 // empêche l'humain de jouer pendant la réflexion
      startTimer(false, Date.now());       // timer visuel côté IA
      setTimeout(aiTurn, 650);"""
new_turn = """      currentPlayer = nextPlayer;
      showLastMoveOrigin(originRow, originCol);
      updUI(); stopTimer();
      isProcessing = true;
      startTimer(currentPlayer === MY_PLAYER, Date.now());
      var nextTheta = currentPlayer === 0 ? 0 : Math.PI;
      animCamTo(camD, 0.72, nextTheta, 650, function(){
        isProcessing = false;
        updateForcedHint();
      });"""
html = replace_once(html, old_turn, new_turn, 'local turn handoff')

html = replace_once(html, "var msg = { type:'mindspille', source:'dames-ai', event:'practice_over', game:'dames', result:outcome, reason:reason||'normal', difficulty:DIFFICULTY };", "var msg = { type:'mindspille', source:'dames-local', event:'local_over', game:'dames', result:outcome, reason:reason||'normal' };", 'local result message')

# Result wording: replace the self/AI-oriented presentation only, keeping the
# rule evaluation and sendResult mechanism intact.
result_start = "  var humanWon = (winner === MY_PLAYER);"
result_end = "  showToast(winnerEmoji, title, sub, 4000, function(){ sendResult(humanWon?'win':(reason==='draw'?'draw':'loss'), reason||'normal'); var rb=document.getElementById('replay-btn'); if(rb) rb.classList.add('show'); });"
start_idx = html.find(result_start)
end_idx = html.find(result_end, start_idx)
if start_idx < 0 or end_idx < 0:
    raise SystemExit(f'end-game local wording markers missing: start={start_idx}, end={end_idx}')
end_idx += len(result_end)
result_replacement = """  var isDraw = (reason === 'draw' || winner < 0);
  var winnerName = winner === 0 ? MY_NAME : OP_NAME;
  var winnerEmoji = isDraw ? '🤝' : (winner === 0 ? '⚪' : '🔴');
  var title = isDraw ? 'Match Nul' : (winnerName + ' gagne la partie !');
  var sub;
  if(isDraw) sub = '50 coups joués sans prise.';
  else if(reason === 'forfeit') sub = winnerName + ' gagne par abandon.';
  else sub = winnerName + ' remporte la partie.\\n' + wc + ' pions blancs restants contre ' + rc + ' pions rouges.';

  if(!isDraw) createConfetti();
  showToast(winnerEmoji, title, sub, 4000, function(){ sendResult(isDraw?'draw':(winner===MY_PLAYER?'win':'loss'), reason||'normal'); var rb=document.getElementById('replay-btn'); if(rb) rb.classList.add('show'); });"""
html = html[:start_idx] + result_replacement + html[end_idx:]

# Startup toast: remove the difficulty copy and identify the local white player.
start_toast_start = "  var diffLbl = DIFFICULTY==='easy' ? 'Facile' : DIFFICULTY==='medium' ? 'Moyen' : DIFFICULTY==='expert' ? 'Expert' : 'Difficile';"
start_toast_end = "  });"
st = html.find(start_toast_start)
if st < 0:
    raise SystemExit('start toast difficulty marker missing')
# The first closing `  });` after diffLbl belongs to this showToast callback.
et = html.find(start_toast_end, st)
if et < 0:
    raise SystemExit('start toast closing marker missing')
et += len(start_toast_end)
start_replacement = """  showToast('🎲','Jouer avec un ami', MY_NAME+' commence (Blancs)', 2400, function(){
    gameReady = true; updUI(); startTimer(true, Date.now());
  });"""
html = html[:st] + start_replacement + html[et:]

dst_path.write_text(html, encoding='utf-8', newline='')

server = server_path.read_text(encoding='utf-8')
ai_route = "app.get(['/dames-ai', '/dames_ai.html', '/dames-solo', '/dames-entrainement', '/dames-practice', '/dames-ia'], serveSmart(['dames_ai.html', 'dames-ai.html']));"
local_route = "app.get(['/dames-local', '/dames_local.html', '/dames-ami', '/dames-hotseat'], serveSmart(['dames_local.html', 'dames-local.html']));"
if local_route in server:
    raise SystemExit('server route already exists unexpectedly')
server = replace_once(server, ai_route, ai_route + '\n' + local_route, 'server local route')
server_path.write_text(server, encoding='utf-8', newline='')

# Syntax checks required by the task.
subprocess.run(['node', '--check', 'server.js'], check=True)
scripts = re.findall(r'<script(?:\s[^>]*)?>([\s\S]*?)</script>', html, flags=re.I)
checked = 0
for idx, script in enumerate(scripts):
    if not script.strip():
        continue
    p = Path(tempfile.gettempdir()) / f'dames-local-inline-{idx}.js'
    p.write_text(script, encoding='utf-8')
    subprocess.run(['node', '--check', str(p)], check=True)
    checked += 1
if checked == 0:
    raise SystemExit('no inline script found to validate')

# Scope/contract checks.
assert src_path.read_text(encoding='utf-8') == original
for marker in [
    'var HOTSEAT = true;',
    "var AI_DEBUG = !!P.get('debug');",
    "var DIFFICULTY = 'expert';",
    "var ROOM_ID = 'local-hotseat';",
    "var MY_NAME = P.get('name') || P.get('p1Name') || 'Joueur 1';",
    "var OP_NAME = P.get('p2Name') || 'Joueur 2';",
    "source:'dames-local'",
    "event:'local_over'",
    'Jouer avec un ami',
    'if(!HOTSEAT && currentPlayer !== MY_PLAYER) return;',
    "animCamTo(camD, 0.72, nextTheta, 650, function(){",
]:
    assert marker in html, marker
print(f'OK: server.js syntax; {checked} inline script(s) syntax')
