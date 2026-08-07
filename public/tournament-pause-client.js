(function () {
  if (typeof socket === 'undefined' || !socket || typeof socket.on !== 'function') return;

  function removeOverlay() {
    var overlay = document.getElementById('mindspille-tournament-pause');
    if (overlay) overlay.remove();
  }

  function showOverlay(payload) {
    removeOverlay();
    var overlay = document.createElement('div');
    overlay.id = 'mindspille-tournament-pause';
    overlay.setAttribute('role', 'status');
    overlay.setAttribute('aria-live', 'assertive');
    overlay.innerHTML = '<div class="mindspille-pause-card">'
      + '<div class="mindspille-pause-icon">Ⅱ</div>'
      + '<strong>Tournoi en pause</strong>'
      + '<p>' + ((payload && payload.message) || 'Le plateau est conservé exactement dans son état actuel.') + '</p>'
      + '<small>La partie reprendra automatiquement après la décision de l’administration.</small>'
      + '</div>';
    var style = document.createElement('style');
    style.textContent = '#mindspille-tournament-pause{position:fixed;inset:0;z-index:2147483646;display:flex;align-items:center;justify-content:center;padding:24px;background:rgba(2,6,23,.46);backdrop-filter:blur(10px);-webkit-backdrop-filter:blur(10px)}'
      + '.mindspille-pause-card{width:min(420px,100%);padding:28px 24px;text-align:center;color:#fff;border:1px solid rgba(251,191,36,.38);border-radius:24px;background:linear-gradient(145deg,rgba(30,41,59,.84),rgba(15,23,42,.68));box-shadow:0 24px 80px rgba(0,0,0,.48),inset 0 1px rgba(255,255,255,.12);font-family:system-ui,sans-serif}'
      + '.mindspille-pause-icon{width:54px;height:54px;margin:0 auto 14px;display:grid;place-items:center;border-radius:50%;color:#fcd34d;background:rgba(245,158,11,.16);border:1px solid rgba(251,191,36,.35);font-size:25px;font-weight:800}'
      + '.mindspille-pause-card strong{display:block;font-size:20px}.mindspille-pause-card p{margin:10px 0 6px;color:rgba(255,255,255,.78);line-height:1.45}.mindspille-pause-card small{color:rgba(255,255,255,.5);line-height:1.4}';
    overlay.appendChild(style);
    document.body.appendChild(overlay);
  }

  socket.on('tournament:paused', showOverlay);
  socket.on('tournament:resumed', removeOverlay);
})();
