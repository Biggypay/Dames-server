'use strict';
/*
 * Lance TOUTE la suite, puis rend son verdict.
 *
 * `npm test` enchainait ses dix-huit fichiers avec « && » : le premier echec
 * masquait tous les suivants. Un test_resync rouge a ainsi cache pendant
 * longtemps que le mode IA du Gomoku n'etait jamais ouvert par la CI — ses
 * tests arrivent en fin de chaine et n'etaient tout simplement jamais
 * atteints. Et chaque correction ne revelait l'echec suivant qu'au tour
 * d'apres.
 *
 * Ici, chaque fichier s'execute dans son propre processus, comme avant, mais
 * jusqu'au bout. Rien n'est ignore ni tolere : un seul echec fait echouer la
 * commande.
 */
const { spawnSync } = require('child_process');
const path = require('path');

const ORDER = [
  'test_gomoku_series_logic', 'test_html_syntax', 'test_resync', 'test_tictactoe_server',
  'test_chess_engine', 'test_chess_competition_rules', 'test_chess_clock', 'test_echecs_server',
  'test_chess_clock_runtime', 'test_chess_competition_runtime', 'test_ludo_chifoumi',
  'test_chifoumi_rounds', 'test_penalty_rounds', 'test_spectator', 'test_tournament_pause',
  'test_turn_clock', 'test_turn_clock_runtime', 'test_match_summary',
  'test_gomoku', 'test_gomoku_browser', 'test_gomoku_ai_browser', 'test_split_layout_browser',
  'test_multiplayer_pages_browser', 'test_board_bridge_browser'
];

const failed = [];
for (const name of ORDER) {
  process.stdout.write(`\n═══ ${name}\n`);
  const run = spawnSync(process.execPath, [path.join(__dirname, `${name}.js`)], {
    cwd: path.join(__dirname, '..'),
    stdio: 'inherit'
  });
  if (run.status !== 0) failed.push(`${name} (code ${run.status === null ? run.signal : run.status})`);
}

console.log('\n══════════════════════════════');
console.log(`${ORDER.length - failed.length}/${ORDER.length} fichiers de test passent`);
if (failed.length) {
  console.log('\nEn echec :');
  for (const entry of failed) console.log('  ✗ ' + entry);
  process.exit(1);
}
console.log('Toute la suite passe.');
