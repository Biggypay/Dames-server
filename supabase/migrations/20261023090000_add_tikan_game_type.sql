-- TIKAN (football arcade 1 contre 1) — neuvième jeu de la plateforme.
--
-- Ajout purement additif : une nouvelle étiquette dans l'énumération
-- `game_type`. Aucune ligne existante n'est touchée et les huit jeux déjà en
-- production continuent de fonctionner à l'identique. C'est le strict minimum
-- côté base pour que le serveur de jeu autoritatif puisse créer, arbitrer et
-- régler une partie de TIKAN (RPC submit_game_result, séquestre des mises).
--
-- `ADD VALUE IF NOT EXISTS` rend la migration rejouable sans erreur.

alter type public.game_type add value if not exists 'tikan';
