-- ============================================================
--  CORRECTIF MATCHMAKING MULTIJOUEUR — 2026-07-11
--  (migration déjà appliquée sur le projet Supabase MindSpille
--   sous le nom « fix_matchmaking_rls_game_creation » ;
--   ce fichier sert d'archive/référence dans le repo serveur)
-- ============================================================
--
--  SYMPTÔME
--  Deux joueurs lancent une recherche (Dames ou autre jeu) : le
--  serveur les voit tous les deux dans la file, l'adversaire est
--  détecté, mais la carte adversaire / l'écran de pré-partie ne
--  s'affiche jamais et les deux restent bloqués sur
--  « En attente de l'adversaire… ».
--
--  CAUSE
--  Un durcissement de sécurité récent a restreint la politique RLS
--  INSERT de public.games à :
--      (auth.uid() = player1_id) AND
--      (player2_id IS NULL OR player2_id = auth.uid())
--  Or le matchmaking du frontend (src/context/matchmaking.tsx) crée
--  la partie avec player2_id = l'adversaire trouvé → INSERT rejeté
--  (« new row violates row-level security policy for table games »).
--  Les entrées de file ayant déjà été consommées par le « claim »,
--  les deux joueurs restaient en recherche infinie. La ré-insertion
--  de l'entrée adverse lors du tie-break de claim simultané était
--  également bloquée sur matchmaking_queue (auth.uid() = user_id).
--
--  INVARIANTS À NE PAS RE-CASSER lors d'un futur audit sécurité :
--   1. Un joueur DOIT pouvoir insérer dans public.games une ligne
--      où player1_id = lui-même et player2_id = un AUTRE joueur
--      (c'est le cœur du matchmaking).
--   2. Un joueur DOIT pouvoir insérer/supprimer des entrées de
--      matchmaking_queue d'autres joueurs (claim + tie-break).
--   3. En revanche, player1_id ≠ auth.uid() doit rester interdit
--      (anti-usurpation), vérifié le 2026-07-11.
-- ============================================================

-- 1) games : le créateur (player1) peut créer une partie en nommant un
--    adversaire distinct comme player2 (flux matchmaking), ou sans player2
--    (parties IA / invitations). Interdit de se mettre soi-même en player2.
DROP POLICY IF EXISTS "Users can insert games" ON public.games;
CREATE POLICY "Users can insert games"
  ON public.games
  FOR INSERT
  TO authenticated
  WITH CHECK (
    auth.uid() = player1_id
    AND (player2_id IS NULL OR player2_id <> player1_id)
  );

-- 2) matchmaking_queue : la table est déjà ouverte en DELETE/UPDATE à tout
--    utilisateur authentifié (nécessaire au « claim » d'adversaire) ; on aligne
--    l'INSERT pour permettre la ré-insertion de l'entrée adverse lors du
--    tie-break de claim simultané.
DROP POLICY IF EXISTS "Users can insert own queue entry" ON public.matchmaking_queue;
CREATE POLICY "Authenticated users can insert queue entries"
  ON public.matchmaking_queue
  FOR INSERT
  TO authenticated
  WITH CHECK (auth.uid() IS NOT NULL);
