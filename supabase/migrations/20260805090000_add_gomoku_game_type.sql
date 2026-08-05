-- Morpion à cinq (Gomoku) — huitième jeu de la plateforme.
--
-- Ajout purement additif : une nouvelle étiquette dans l'énumération
-- `game_type`. Aucune ligne existante n'est touchée, aucune contrainte n'est
-- resserrée, et les sept jeux déjà en production continuent de fonctionner à
-- l'identique. C'est le strict minimum côté base pour que le serveur de jeu
-- autoritatif puisse créer, arbitrer et régler une partie de morpion à cinq.
--
-- `ADD VALUE IF NOT EXISTS` rend la migration rejouable sans erreur.

alter type public.game_type add value if not exists 'gomoku';
