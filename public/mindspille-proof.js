/*
 * La preuve du résultat reste visible (owner, 2026-10-26 : « on doit pouvoir
 * consulter en temps réel la preuve que la personne a gagné … ça doit rester
 * visible pendant quelques secondes »).
 *
 * Le message de manche (#toast) et la fiche de fin de match (#gameOverModal)
 * s'ouvraient AU CENTRE de l'écran, sur le plateau : ils cachaient justement
 * les cinq pions alignés, la ligne du Tic-Tac-Toe, les deux cartes du Chifoumi.
 * Ils se posent désormais en haut, compacts, et le plateau reste lisible en
 * dessous ; la fiche de fin n'a plus de bouton « Fermer » — la fin du match se
 * joue dans l'application (la revanche, 15 secondes), pas dans le cadre.
 *
 * Les pages ne changent pas une ligne : elles posent `display`, l'opacité et
 * un `transform` en ligne sur #toast ; les règles ci-dessous ont le dernier mot
 * sur la position, la page garde son fondu.
 */
(function () {
  'use strict';

  var FONT = "'Inter', system-ui, -apple-system, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif";
  var TOP = 'calc(env(safe-area-inset-top, 0px) + 10px)';
  var B = 'html body ';
  var css =
    /* Le message de manche : une carte en haut, au-dessus de l'en-tête. */
    B + '#toast{position:fixed!important;top:' + TOP + '!important;bottom:auto!important;left:50%!important;'
      + 'transform:translateX(-50%)!important;min-width:0!important;width:max-content!important;max-width:calc(100% - 24px)!important;'
      + 'padding:9px 18px 10px!important;border-radius:16px!important;z-index:160!important;box-sizing:border-box}'
    + B + '#toast-emoji{font-size:22px!important;line-height:1!important;margin:0 0 4px!important;min-height:0!important}'
    + B + '#toast-emoji > *{transform:scale(.55);transform-origin:center;margin:-10px 0}'
    + B + '#toast-title{font-family:' + FONT + '!important;font-size:15px!important;line-height:1.25!important;margin:0 0 2px!important;letter-spacing:0!important}'
    + B + '#toast-sub{font-family:' + FONT + '!important;font-size:11.5px!important;line-height:1.35!important;letter-spacing:.01em!important}'

    /* La fiche de fin : même place, sans voile ni flou sur le plateau, sans bouton. */
    + B + '#gameOverModal{background:transparent!important;-webkit-backdrop-filter:none!important;backdrop-filter:none!important;'
      + 'align-items:flex-start!important;justify-content:center!important;padding-top:' + TOP + '!important;pointer-events:none!important;overflow:visible!important}'
    + B + '#gameOverModal .modal{width:auto!important;max-width:min(380px, calc(100% - 24px))!important;padding:12px 20px 13px!important;'
      + 'border-radius:18px!important;max-height:none!important;overflow:visible!important}'
    + B + '#gameOverModal .modal h2{font-family:' + FONT + '!important;font-size:18px!important;margin:0 0 4px!important;letter-spacing:0!important}'
    + B + '#gameOverModal .final-message{font-size:13px!important;margin:0!important;line-height:1.4!important}'
    + B + '#gameOverModal .prize-line{font-size:13px!important;margin:6px 0 0!important}'
    + B + '#gameOverModal .final-score{font-size:30px!important;line-height:1.1!important;margin:0 0 2px!important}'
    /* Penalty, Chifoumi : l'historique des tirs / des manches, court, et replié sur un écran bas. */
    + B + '#gameOverModal .modal-history{margin:8px 0 0!important;max-height:15vh!important}'
    + B + '#gameOverModal .modal-history h4{margin-bottom:6px!important}'
    + '@media (max-height:520px){' + B + '#gameOverModal .modal-history{display:none!important}}'
    + B + '#gameOverModal #closeBtn,' + B + '#gameOverModal .restart-btn{display:none!important}';

  var style = document.createElement('style');
  style.id = 'mindspille-proof';
  style.textContent = css;
  (document.head || document.documentElement).appendChild(style);
})();
