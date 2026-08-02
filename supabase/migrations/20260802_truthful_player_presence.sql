-- PRÉSENCE RÉELLE DES JOUEURS
--
-- Les colonnes `games.player1_last_heartbeat` / `player2_last_heartbeat` sont
-- censées dire quand chaque joueur a été vu pour la dernière fois. Personne ne
-- les écrivait pour les parties jouées sur le serveur autoritatif : elles
-- restaient NULL. Toute fonction qui lisait « dernière présence » retombait
-- alors sur `started_at`, et concluait « ce joueur est absent » quarante
-- secondes après la création de la partie — plateau ouvert, joueurs devant.
--
-- C'est ce qui a fait perdre un match de tournoi le 2 août : les deux joueuses
-- étaient présentes, l'application leur a annoncé « les deux joueurs ont été
-- déconnectés — délai écoulé », et le seul bouton restant déclarait forfait.
--
-- Deux corrections, indépendantes et cumulatives :
--   1. le serveur de jeu — seul à connaître l'état réel des sockets — publie la
--      présence de chaque joueur à chaque sauvegarde de salle ;
--   2. aucune fonction ne conclut plus à une déconnexion tant que la salle
--      autoritative est vivante, ni pendant les trois premières minutes d'une
--      partie, le temps que les deux plateaux se connectent.

-- ══════════════════════════════════════════════════════════════════════════
--  1. Le serveur de jeu publie la présence réelle
-- ══════════════════════════════════════════════════════════════════════════
-- `connected_players` est un tableau JSON d'identifiants Supabase : ceux dont
-- le socket est réellement ouvert sur la salle. Le champ est facultatif — un
-- serveur de jeu qui ne l'envoie pas encore garde exactement l'ancien
-- comportement.
CREATE OR REPLACE FUNCTION public.save_game_server_room_states(p_rooms jsonb)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'pg_catalog', 'public', 'private'
AS $function$
DECLARE
  item jsonb;
  item_game_type text;
  item_room_id text;
  item_game_id uuid;
  item_status text;
  item_state jsonb;
  item_connected jsonb;
  database_game_type text;
  expected_database_type text;
BEGIN
  IF jsonb_typeof(p_rooms) <> 'array' OR jsonb_array_length(p_rooms) > 500 THEN
    RAISE EXCEPTION 'invalid room state batch' USING ERRCODE = '22023';
  END IF;
  FOR item IN SELECT value FROM jsonb_array_elements(p_rooms)
  LOOP
    item_game_type := item->>'game_type';
    item_room_id := item->>'room_id';
    item_status := item->>'status';
    item_state := item->'state';
    item_connected := item->'connected_players';
    BEGIN
      item_game_id := (item->>'game_id')::uuid;
    EXCEPTION WHEN invalid_text_representation THEN
      RAISE EXCEPTION 'invalid game id' USING ERRCODE = '22023';
    END;
    IF item_game_type NOT IN ('dames', 'tictactoe', 'quoridor', 'penalty', 'chifoumi', 'echecs', 'ludo')
       OR item_room_id IS NULL OR item_room_id !~ '^[A-Za-z0-9_:.-]{1,100}$'
       OR item_status NOT IN ('waiting', 'playing', 'paused', 'finished')
       OR jsonb_typeof(item_state) <> 'object'
       OR pg_column_size(item_state) > 262144 THEN
      RAISE EXCEPTION 'invalid room state' USING ERRCODE = '22023';
    END IF;
    expected_database_type := CASE item_game_type
      WHEN 'dames' THEN 'checkers'
      WHEN 'tictactoe' THEN 'tictactoe'
      WHEN 'quoridor' THEN 'quoridor'
      WHEN 'penalty' THEN 'penalty_shootout'
      WHEN 'chifoumi' THEN 'rock_paper_scissors'
      WHEN 'echecs' THEN 'chess'
      WHEN 'ludo' THEN 'ludo'
    END;
    SELECT g.game_type::text INTO database_game_type
    FROM public.games AS g
    WHERE g.id = item_game_id;

    -- Partie introuvable ou type incohérent : on saute CETTE salle sans
    -- sacrifier tout le lot.
    IF database_game_type IS NULL OR database_game_type <> expected_database_type THEN
      CONTINUE;
    END IF;

    INSERT INTO private.game_server_room_states AS saved
      (game_type, room_id, game_id, status, state, updated_at)
    VALUES
      (item_game_type, item_room_id, item_game_id, item_status, item_state, now())
    ON CONFLICT (game_type, room_id) DO UPDATE
    SET game_id = EXCLUDED.game_id,
        status = EXCLUDED.status,
        state = EXCLUDED.state,
        updated_at = now();

    -- Une salle « playing » = deux joueurs réellement en train de jouer.
    -- On horodate la partie pour que le live la montre sans dépendre du
    -- navigateur. On ne touche pas au statut : le passage en « in_progress »
    -- reste géré par les fonctions de mise (séquestre des paris).
    IF item_status = 'playing' THEN
      UPDATE public.games
         SET server_live_at = now()
       WHERE id = item_game_id
         AND status = 'in_progress'::game_status
         AND is_ai_opponent = false
         AND player1_id IS NOT NULL
         AND player2_id IS NOT NULL
         AND (server_live_at IS NULL OR server_live_at < now() - interval '15 seconds');
    END IF;

    -- Présence, socket par socket. Le serveur de jeu est le seul à la
    -- connaître ; sans elle les colonnes de battement restaient NULL et « on
    -- ne sait pas » se lisait « ce joueur est parti ». On n'écrit que les
    -- présents : l'absence d'écriture fait naturellement vieillir la valeur
    -- d'un joueur qui s'en va, ce qui est exactement le signal recherché.
    -- Une salle terminée ne prouve plus rien.
    IF jsonb_typeof(item_connected) = 'array' AND item_status <> 'finished' THEN
      UPDATE public.games AS g
         SET player1_last_heartbeat = now()
       WHERE g.id = item_game_id
         AND g.status IN ('waiting'::game_status, 'in_progress'::game_status)
         AND g.player1_id IS NOT NULL
         AND item_connected ? g.player1_id::text
         AND (g.player1_last_heartbeat IS NULL
              OR g.player1_last_heartbeat < now() - interval '10 seconds');

      UPDATE public.games AS g
         SET player2_last_heartbeat = now()
       WHERE g.id = item_game_id
         AND g.status IN ('waiting'::game_status, 'in_progress'::game_status)
         AND g.player2_id IS NOT NULL
         AND item_connected ? g.player2_id::text
         AND (g.player2_last_heartbeat IS NULL
              OR g.player2_last_heartbeat < now() - interval '10 seconds');
    END IF;
  END LOOP;
END;
$function$;

-- ══════════════════════════════════════════════════════════════════════════
--  2. La fenêtre de reprise ne conclut plus à la place du serveur de jeu
-- ══════════════════════════════════════════════════════════════════════════
CREATE OR REPLACE FUNCTION public.get_game_resume_offer(p_game_id uuid DEFAULT NULL::uuid)
RETURNS TABLE(
  game_id uuid,
  game_type text,
  bet_amount numeric,
  opponent_id uuid,
  reconnect_deadline_at timestamp with time zone,
  server_now timestamp with time zone,
  seconds_remaining integer,
  opponent_waiting boolean,
  both_players_disconnected boolean
)
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
DECLARE
  -- Le temps qu'il faut aux deux plateaux pour s'ouvrir et rejoindre la salle
  -- du serveur de jeu. Le filet de sécurité de la base s'interdit déjà de
  -- conclure quoi que ce soit sur une partie plus jeune que cela.
  c_forming constant interval := interval '3 minutes';
  -- Au-delà, la salle autoritative est considérée muette (elle pulse toutes
  -- les 15 secondes tant qu'elle vit).
  c_room_silence constant interval := interval '90 seconds';

  v_uid uuid := auth.uid();
  g public.games%ROWTYPE;
  v_started_at timestamptz;
  v_room_alive boolean;
  v_my_seen_at timestamptz;
  v_opponent_seen_at timestamptz;
  v_deadline timestamptz;
  v_outcome text;
  v_stale interval := make_interval(secs => public.game_heartbeat_stale_seconds());
BEGIN
  IF v_uid IS NULL THEN
    RAISE EXCEPTION 'authentication required' USING ERRCODE = '42501';
  END IF;

  SELECT *
  INTO g
  FROM public.games
  WHERE status = 'in_progress'::public.game_status
    AND is_ai_opponent = false
    AND player1_id IS NOT NULL
    AND player2_id IS NOT NULL
    AND (p_game_id IS NULL OR id = p_game_id)
    AND (player1_id = v_uid OR player2_id = v_uid)
  ORDER BY COALESCE(last_move_at, updated_at, created_at) DESC
  LIMIT 1;

  IF g.id IS NULL THEN
    RETURN;
  END IF;

  v_started_at := COALESCE(g.started_at, g.created_at);

  -- Une partie qui vient de naître n'est pas une partie abandonnée. Entre la
  -- création de la ligne et l'ouverture réelle de la salle, il s'écoule le
  -- temps que les deux plateaux se connectent — deux minutes et demie le
  -- 2 août. Proposer de clore pendant ce temps-là, c'est proposer de perdre un
  -- match qui n'a pas encore commencé.
  IF v_started_at > now() - c_forming THEN
    RETURN;
  END IF;

  v_outcome := public.finalize_abandoned_game(g.id);
  IF v_outcome IN ('mutual_quit', 'timeout') THEN
    RETURN;
  END IF;

  v_room_alive := g.server_live_at IS NOT NULL
                  AND g.server_live_at > now() - c_room_silence;

  IF g.player1_id = v_uid THEN
    v_my_seen_at := COALESCE(g.player1_last_heartbeat, v_started_at, g.updated_at, g.created_at);
    v_opponent_seen_at := COALESCE(g.player2_last_heartbeat, v_started_at, g.updated_at, g.created_at);
  ELSE
    v_my_seen_at := COALESCE(g.player2_last_heartbeat, v_started_at, g.updated_at, g.created_at);
    v_opponent_seen_at := COALESCE(g.player1_last_heartbeat, v_started_at, g.updated_at, g.created_at);
  END IF;

  -- Une salle vivante prouve que le match tourne toujours, donc que l'adversaire
  -- y est. On ne l'utilise que pour lui : elle ne dit rien de la présence de
  -- l'appelant, dont le compte à rebours doit rester honnête.
  IF v_room_alive THEN
    v_opponent_seen_at := GREATEST(v_opponent_seen_at, g.server_live_at);
  END IF;

  v_deadline := v_my_seen_at + interval '75 seconds';

  RETURN QUERY
  SELECT
    g.id,
    g.game_type::text,
    g.bet_amount,
    CASE WHEN g.player1_id = v_uid THEN g.player2_id ELSE g.player1_id END,
    v_deadline,
    now(),
    GREATEST(0, FLOOR(EXTRACT(EPOCH FROM (v_deadline - now())))::integer),
    v_opponent_seen_at >= now() - v_stale,
    -- « Les deux joueurs sont déconnectés » est une affirmation forte : elle
    -- fait basculer l'interface dans son mode terminal. Une salle vivante la
    -- contredit à elle seule.
    NOT v_room_alive
      AND v_my_seen_at < now() - v_stale
      AND v_opponent_seen_at < now() - v_stale;
END;
$function$;

-- ══════════════════════════════════════════════════════════════════════════
--  3. Un joueur ne réclame plus une victoire que le serveur de jeu arbitre
-- ══════════════════════════════════════════════════════════════════════════
-- Tant que la salle autoritative vit, c'est elle qui décide d'un forfait (elle
-- laisse soixante secondes de reconnexion). Deux autorités concurrentes sur le
-- même match, c'est un résultat qui dépend de qui a cliqué le premier.
CREATE OR REPLACE FUNCTION public.resolve_disconnected_opponent(p_game_id uuid)
RETURNS void
LANGUAGE plpgsql
SECURITY DEFINER
SET search_path TO 'public', 'pg_temp'
AS $function$
DECLARE
  v_uid uuid := auth.uid();
  g public.games%ROWTYPE;
  v_my_seen_at timestamptz;
  v_opponent_seen_at timestamptz;
BEGIN
  IF v_uid IS NULL THEN
    RAISE EXCEPTION 'authentication required' USING ERRCODE = '42501';
  END IF;

  SELECT * INTO g
  FROM public.games
  WHERE id = p_game_id
  FOR UPDATE;

  IF g.id IS NULL OR g.status <> 'in_progress'::public.game_status THEN
    RAISE EXCEPTION 'active game not found' USING ERRCODE = 'P0002';
  END IF;

  IF g.server_live_at IS NOT NULL AND g.server_live_at > now() - interval '90 seconds' THEN
    RAISE EXCEPTION 'authoritative room is running' USING ERRCODE = '22023';
  END IF;

  IF COALESCE(g.started_at, g.created_at) > now() - interval '3 minutes' THEN
    RAISE EXCEPTION 'game has not been running long enough' USING ERRCODE = '22023';
  END IF;

  IF g.player1_id = v_uid THEN
    v_my_seen_at := COALESCE(g.player1_last_heartbeat, g.started_at, g.updated_at, g.created_at);
    v_opponent_seen_at := COALESCE(g.player2_last_heartbeat, g.started_at, g.updated_at, g.created_at);
  ELSIF g.player2_id = v_uid THEN
    v_my_seen_at := COALESCE(g.player2_last_heartbeat, g.started_at, g.updated_at, g.created_at);
    v_opponent_seen_at := COALESCE(g.player1_last_heartbeat, g.started_at, g.updated_at, g.created_at);
  ELSE
    RAISE EXCEPTION 'not a participant' USING ERRCODE = '42501';
  END IF;

  IF v_my_seen_at < now() - interval '15 seconds' THEN
    RAISE EXCEPTION 'caller must still be connected' USING ERRCODE = '42501';
  END IF;

  IF v_opponent_seen_at + interval '75 seconds' > now() THEN
    RAISE EXCEPTION 'opponent reconnect time has not expired' USING ERRCODE = '22023';
  END IF;

  PERFORM set_config('app.trusted_game_write', '1', true);
  UPDATE public.games
  SET status = 'completed'::public.game_status,
      result = 'timeout'::public.game_result,
      winner_id = v_uid,
      duration_seconds = GREATEST(
        0,
        FLOOR(EXTRACT(EPOCH FROM (now() - COALESCE(g.started_at, g.created_at))))::integer
      ),
      completed_at = now(),
      updated_at = now()
  WHERE id = g.id
    AND status = 'in_progress'::public.game_status;
  PERFORM set_config('app.trusted_game_write', '', true);

  IF NOT FOUND THEN
    RAISE EXCEPTION 'game was already settled or changed state' USING ERRCODE = 'P0001';
  END IF;
EXCEPTION WHEN OTHERS THEN
  PERFORM set_config('app.trusted_game_write', '', true);
  RAISE;
END;
$function$;

COMMENT ON FUNCTION public.get_game_resume_offer(uuid) IS
  'Propose de reprendre une partie réellement interrompue. Ne conclut jamais à une déconnexion pendant les trois premières minutes, ni tant que la salle du serveur de jeu est vivante.';
