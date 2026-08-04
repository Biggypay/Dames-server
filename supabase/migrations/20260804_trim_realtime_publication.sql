-- ALLÉGER LA PUBLICATION TEMPS RÉEL
--
-- Appliquée le 4 août 2026 pendant une panne : plus personne ne pouvait se
-- connecter. L'authentification expirait en attendant une connexion à la base
-- (« context deadline exceeded »), la base annulait ses requêtes au bout du
-- délai imparti, et les tâches planifiées n'arrivaient plus à démarrer.
--
-- Le consommateur n'était pas l'application. Dans les statistiques de requêtes,
-- les deux premières places revenaient au pipeline temps réel : 339 569 et
-- 200 298 appels pour près de 4 600 secondes de base. La première requête
-- applicative n'arrivait qu'en troisième position.
--
-- La seconde de ces requêtes re-résout la liste des tables publiées à chaque
-- sondage, et son coût est proportionnel au nombre de tables. Il y en avait
-- trente-trois — pour neuf mille écritures cumulées, toutes tables confondues.
-- On payait surtout du vide.
--
-- Ne sont retirées ici que les tables jamais écrites (zéro insertion, zéro mise
-- à jour, zéro ligne), plus le classement public.
--
-- Ce qu'on perd exactement :
--   • les treize tables à zéro écriture : rien aujourd'hui. Le jour où l'une
--     d'elles servira, il faudra la remettre pour retrouver le direct.
--   • public_leaderboard : le classement ne se met plus à jour tout seul à
--     l'écran ; il se recharge à l'ouverture de la page. C'était le plus gros
--     producteur d'écritures de toute la publication (2 856), reconstruit
--     périodiquement, et chaque reconstruction était diffusée à tous les
--     clients connectés.
--
-- Restent diffusées les dix-neuf tables dont le direct fait la valeur du
-- produit : parties, notifications, file d'attente, chats, bracket, portefeuille.
--
-- Pour en remettre une :
--   ALTER PUBLICATION supabase_realtime ADD TABLE public.<nom>;

ALTER PUBLICATION supabase_realtime DROP TABLE public.game_moves;
ALTER PUBLICATION supabase_realtime DROP TABLE public.game_quit_requests;
ALTER PUBLICATION supabase_realtime DROP TABLE public.player_reports;
ALTER PUBLICATION supabase_realtime DROP TABLE public.announcements;
ALTER PUBLICATION supabase_realtime DROP TABLE public.announcement_user_states;
ALTER PUBLICATION supabase_realtime DROP TABLE public.events;
ALTER PUBLICATION supabase_realtime DROP TABLE public.event_bets;
ALTER PUBLICATION supabase_realtime DROP TABLE public.event_messages;
ALTER PUBLICATION supabase_realtime DROP TABLE public.event_spectator_bets;
ALTER PUBLICATION supabase_realtime DROP TABLE public.promo_slides;
ALTER PUBLICATION supabase_realtime DROP TABLE public.music_tracks;
ALTER PUBLICATION supabase_realtime DROP TABLE public.scheduled_matches;
ALTER PUBLICATION supabase_realtime DROP TABLE public.tournament_refund_requests;
ALTER PUBLICATION supabase_realtime DROP TABLE public.public_leaderboard;
