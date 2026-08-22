from pathlib import Path
import re
import subprocess
import tempfile

dames_path = Path('public/dames_local.html')
server_path = Path('server.js')
local_path = Path('public/local-pass-and-play.html')

dames = dames_path.read_text(encoding='utf-8')
server = server_path.read_text(encoding='utf-8')

def replace_once(text, old, new, label):
    count = text.count(old)
    if count != 1:
        raise SystemExit(f'{label}: expected exactly 1 occurrence, found {count}')
    return text.replace(old, new, 1)

dames = replace_once(
    dames,
    "function animCamTo(targetD,targetPhi,targetTheta,duration,onDone){\n  if(topViewAnimating) return;",
    "function animCamTo(targetD,targetPhi,targetTheta,duration,onDone){\n  if(boardLocked){ if(onDone) onDone(); return; }\n  if(topViewAnimating) return;",
    'animCamTo lock guard'
)

dames = replace_once(
    dames,
    "  }else if(e.touches.length===2){\n    var dx=e.touches[0].clientX-e.touches[1].clientX, dy=e.touches[0].clientY-e.touches[1].clientY;",
    "  }else if(e.touches.length===2 && !boardLocked){\n    var dx=e.touches[0].clientX-e.touches[1].clientX, dy=e.touches[0].clientY-e.touches[1].clientY;",
    'pinch zoom lock guard'
)

dames = replace_once(
    dames,
    "document.getElementById('btn-topview').addEventListener('click',function(){\n  if(topViewAnimating) return;",
    "document.getElementById('btn-topview').addEventListener('click',function(){\n  if(boardLocked || topViewAnimating) return;",
    'top view lock guard'
)

dames = replace_once(
    dames,
    "document.getElementById('btn-cam').addEventListener('click',function(){\n  autoRotate=!autoRotate;",
    "document.getElementById('btn-cam').addEventListener('click',function(){\n  if(boardLocked) return;\n  autoRotate=!autoRotate;",
    'auto camera lock guard'
)

old_lock = """document.getElementById('btn-lock').addEventListener('click',function(){
  boardLocked=!boardLocked;
  if(boardLocked){ autoRotate=false; document.getElementById('btn-cam').classList.remove('active-cam'); }
  this.classList[boardLocked?'add':'remove']('active-cam');
  this.textContent=boardLocked?'🔒':'🔓';
});"""
new_lock = """document.getElementById('btn-lock').addEventListener('click',function(){
  boardLocked=!boardLocked;
  if(boardLocked){
    autoRotate=false;
    document.getElementById('btn-cam').classList.remove('active-cam');
  }
  this.classList[boardLocked?'add':'remove']('active-cam');
  this.textContent=boardLocked?'🔒':'🔓';
  if(!boardLocked){
    var unlockTheta = currentPlayer === 0 ? 0 : Math.PI;
    animCamTo(camD, 0.72, unlockTheta, 520, function(){ updateForcedHint(); });
  }
});"""
dames = replace_once(dames, old_lock, new_lock, 'lock toggle behavior')

marker = "app.get(['/gomoku-ai', '/gomoku_ai.html', '/gomoku-solo', '/gomoku-entrainement', '/gomoku-ia', '/morpion5-ai', '/morpion5-ia'], serveSmart(['gomoku_ai.html', 'gomoku-ai.html']));"
helper = r"""

// ── MODES AMI OFFLINE / MÊME APPAREIL ─────────────────────
// Conserve les noms éventuels passés par l'app et force seulement le type de jeu.
function localFriendRoute(game) {
  return (req, res) => {
    const params = new URLSearchParams();
    for (const [key, value] of Object.entries(req.query || {})) {
      if (Array.isArray(value)) value.forEach(item => params.append(key, String(item)));
      else if (value !== undefined && value !== null) params.set(key, String(value));
    }
    params.set('game', game);
    res.redirect(302, '/local-pass-and-play.html?' + params.toString());
  };
}

app.get(['/local-pass-and-play', '/ami-offline', '/friend-offline'], (req, res) => {
  const params = new URLSearchParams();
  for (const [key, value] of Object.entries(req.query || {})) {
    if (Array.isArray(value)) value.forEach(item => params.append(key, String(item)));
    else if (value !== undefined && value !== null) params.set(key, String(value));
  }
  res.redirect(302, '/local-pass-and-play.html' + (params.toString() ? '?' + params.toString() : ''));
});

app.get(['/ttt-local', '/tictactoe-local', '/ttt-ami', '/tictactoe-ami'], localFriendRoute('tictactoe'));
app.get(['/quoridor-local', '/quoridor-ami'], localFriendRoute('quoridor'));
app.get(['/chifoumi-local', '/chifoumi-ami'], localFriendRoute('rock_paper_scissors'));
app.get(['/penalty-local', '/penalty-ami'], localFriendRoute('penalty_shootout'));
app.get(['/echecs-local', '/chess-local', '/echecs-ami', '/chess-ami'], localFriendRoute('chess'));
app.get(['/gomoku-local', '/morpion5-local', '/gomoku-ami', '/morpion5-ami'], localFriendRoute('gomoku'));
app.get(['/ludo-local', '/ludo-ami'], localFriendRoute('ludo'));
"""
if 'function localFriendRoute(game)' in server:
    raise SystemExit('local friend routes already present unexpectedly')
server = replace_once(server, marker, marker + helper, 'insert local friend routes')

dames_path.write_text(dames, encoding='utf-8', newline='')
server_path.write_text(server, encoding='utf-8', newline='')

subprocess.run(['node', '--check', 'server.js'], check=True)
for html_path in [dames_path, local_path]:
    html = html_path.read_text(encoding='utf-8')
    scripts = re.findall(r'<script(?:\s[^>]*)?>([\s\S]*?)</script>', html, flags=re.I)
    checked = 0
    for idx, script in enumerate(scripts):
        if not script.strip():
            continue
        tmp = Path(tempfile.gettempdir()) / f'{html_path.stem}-{idx}.js'
        tmp.write_text(script, encoding='utf-8')
        subprocess.run(['node', '--check', str(tmp)], check=True)
        checked += 1
    if checked == 0:
        raise SystemExit(f'no inline script found in {html_path}')
    print(f'OK {html_path}: {checked} inline script(s)')

for item in [
    "if(boardLocked){ if(onDone) onDone(); return; }",
    "e.touches.length===2 && !boardLocked",
    "if(boardLocked || topViewAnimating) return;",
    "if(boardLocked) return;\n  autoRotate=!autoRotate;",
]:
    if item not in dames:
        raise SystemExit('missing Dames lock marker: ' + item)

for route in ['/ttt-local', '/quoridor-local', '/chifoumi-local', '/penalty-local', '/echecs-local', '/gomoku-local', '/ludo-local']:
    if route not in server:
        raise SystemExit('missing local route ' + route)

print('OK: Dames camera lock + local routes for all live app games')
