\set ON_ERROR_STOP on

-- ══════════════════════════════════════════════════════════════════════
--  Le tableau final : croisement des groupes, places reservees,
--  finale et petite finale remplies ensemble.
-- ══════════════════════════════════════════════════════════════════════

CREATE OR REPLACE FUNCTION pg_temp.tid() RETURNS uuid LANGUAGE sql AS
  $$ SELECT '77777777-7777-4777-8777-777777777777'::uuid $$;

-- Trente-deux joueurs, un tournoi construit par la vraie fonction.
CREATE OR REPLACE FUNCTION pg_temp.seed_bracket() RETURNS void LANGUAGE plpgsql AS $$
DECLARE
  t uuid := pg_temp.tid();
  adm uuid := '44444444-4444-4444-8444-444444444444';
  u uuid;
  i integer;
BEGIN
  DELETE FROM public.notifications;
  DELETE FROM public.tournament_matches WHERE tournament_id = t;
  DELETE FROM public.tournament_participants WHERE tournament_id = t;
  DELETE FROM public.tournaments WHERE id = t;
  DELETE FROM public.user_roles;
  DELETE FROM public.profiles;
  DELETE FROM auth.users;

  INSERT INTO auth.users (id, email) VALUES (adm, 'admin@test');
  INSERT INTO public.user_roles (user_id, role) VALUES (adm, 'admin');

  -- starts_at renseigne : la notification de tirage le concatene, et un NULL
  -- y annulerait tout le message.
  INSERT INTO public.tournaments (id, name, game_type, status, starts_at, estimated_ends_at)
  VALUES (t, 'Tournoi de test', 'checkers', 'registration_open',
          now() + interval '1 hour', now() + interval '6 days');

  FOR i IN 1..32 LOOP
    u := ('a0000000-0000-4000-8000-' || lpad(i::text, 12, '0'))::uuid;
    INSERT INTO auth.users (id, email) VALUES (u, 'j' || i || '@test');
    INSERT INTO public.profiles (id, username) VALUES (u, 'joueur' || lpad(i::text, 2, '0'));
    INSERT INTO public.tournament_participants (tournament_id, user_id, status)
    VALUES (t, u, 'active');
  END LOOP;

  PERFORM set_config('test.uid', adm::text, false);
  PERFORM public.launch_tournament(t, true);
  UPDATE public.tournaments SET status = 'in_progress' WHERE id = t;
END;
$$;

-- Fait gagner un match a un joueur donne, par la voie officielle.
CREATE OR REPLACE FUNCTION pg_temp.win(p_match uuid, p_winner uuid) RETURNS void
LANGUAGE sql AS $$ SELECT public.advance_tournament_match_core(p_match, p_winner, 'test') $$;

CREATE OR REPLACE FUNCTION pg_temp.match_of(p_round text, p_group text, p_pos integer)
RETURNS public.tournament_matches LANGUAGE sql AS $$
  SELECT * FROM public.tournament_matches
   WHERE tournament_id = pg_temp.tid()
     AND round::text = p_round
     AND (p_group IS NULL OR group_letter = p_group)
     AND bracket_position = p_pos
$$;

SELECT pg_temp.seed_bracket();

-- ══════════════════════════════════════════════════════════════════════
--  1. La place reservee de chaque match
-- ══════════════════════════════════════════════════════════════════════
DO $$
BEGIN
  IF public.tournament_feeder_slot('group', 'A', 3) <> 1
     OR public.tournament_feeder_slot('group', 'C', 2) <> 1
     OR public.tournament_feeder_slot('group', 'B', 1) <> 2
     OR public.tournament_feeder_slot('group', 'D', 4) <> 2 THEN
    RAISE EXCEPTION 'ECHEC : les groupes ne tiennent pas la place attendue';
  END IF;
  IF public.tournament_feeder_slot('round_of_16', NULL, 3) <> 1
     OR public.tournament_feeder_slot('round_of_16', NULL, 4) <> 2
     OR public.tournament_feeder_slot('quarter', NULL, 1) <> 1
     OR public.tournament_feeder_slot('quarter', NULL, 2) <> 2
     OR public.tournament_feeder_slot('semi', NULL, 2) <> 2 THEN
    RAISE EXCEPTION 'ECHEC : les tours a elimination ne tiennent pas la place attendue';
  END IF;
  RAISE NOTICE 'OK  chaque match connait la place qu''il alimente';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  2. Les huitiemes croisent les groupes, en classement inverse
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  r record;
  v_expected integer;
BEGIN
  FOR r IN
    SELECT g.group_letter, g.bracket_position, nx.bracket_position AS ro16
      FROM public.tournament_matches g
      JOIN public.tournament_matches nx ON nx.id = g.next_match_id
     WHERE g.tournament_id = pg_temp.tid() AND g.round = 'group'
     ORDER BY g.group_letter, g.bracket_position
  LOOP
    v_expected := CASE r.group_letter
      WHEN 'A' THEN r.bracket_position
      WHEN 'B' THEN 5 - r.bracket_position
      WHEN 'C' THEN 4 + r.bracket_position
      ELSE 9 - r.bracket_position
    END;
    IF r.ro16 <> v_expected THEN
      RAISE EXCEPTION 'ECHEC : % % alimente le huitieme % au lieu de %',
        r.group_letter, r.bracket_position, r.ro16, v_expected;
    END IF;
  END LOOP;
  RAISE NOTICE 'OK  A1-B4, A2-B3, A3-B2, A4-B1, C1-D4, C2-D3, C3-D2, C4-D1';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  3. Deux qualifies d'un meme groupe ne se rencontrent jamais en 8es
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  t uuid := pg_temp.tid();
  m record;
  v_winner uuid;
  v_pairs integer;
BEGIN
  -- Chaque match de groupe est gagne par son joueur 1.
  FOR m IN
    SELECT id, player1_id FROM public.tournament_matches
     WHERE tournament_id = t AND round = 'group' ORDER BY group_letter, bracket_position
  LOOP
    PERFORM pg_temp.win(m.id, m.player1_id);
  END LOOP;

  SELECT count(*) INTO v_pairs
    FROM public.tournament_matches ro
    JOIN public.tournament_participants p1
      ON p1.user_id = ro.player1_id AND p1.tournament_id = t
    JOIN public.tournament_participants p2
      ON p2.user_id = ro.player2_id AND p2.tournament_id = t
   WHERE ro.tournament_id = t AND ro.round = 'round_of_16'
     AND p1.group_letter = p2.group_letter;

  IF v_pairs <> 0 THEN
    RAISE EXCEPTION 'ECHEC : % huitiemes opposent deux joueurs du meme groupe', v_pairs;
  END IF;

  SELECT count(*) INTO v_pairs
    FROM public.tournament_matches
   WHERE tournament_id = t AND round = 'round_of_16'
     AND player1_id IS NOT NULL AND player2_id IS NOT NULL;
  IF v_pairs <> 8 THEN
    RAISE EXCEPTION 'ECHEC : seuls % huitiemes sur 8 sont complets', v_pairs;
  END IF;
  RAISE NOTICE 'OK  les huit huitiemes sont complets, aucun duel intra-groupe';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  4. Le groupe A tient la gauche, le groupe B la droite
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  ro public.tournament_matches%rowtype;
  a1 uuid;
  b4 uuid;
BEGIN
  SELECT winner_id INTO a1 FROM pg_temp.match_of('group', 'A', 1);
  SELECT winner_id INTO b4 FROM pg_temp.match_of('group', 'B', 4);
  SELECT * INTO ro FROM pg_temp.match_of('round_of_16', NULL, 1);
  IF ro.player1_id <> a1 OR ro.player2_id <> b4 THEN
    RAISE EXCEPTION 'ECHEC : le huitieme 1 devrait etre A1 (gauche) contre B4 (droite)';
  END IF;
  RAISE NOTICE 'OK  la place de chacun est reservee, pas prise au premier arrive';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  5. Jusqu'aux demi-finales
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  t uuid := pg_temp.tid();
  m record;
  v_count integer;
BEGIN
  FOR m IN SELECT id, player1_id FROM public.tournament_matches
            WHERE tournament_id = t AND round = 'round_of_16' ORDER BY bracket_position
  LOOP PERFORM pg_temp.win(m.id, m.player1_id); END LOOP;

  SELECT count(*) INTO v_count FROM public.tournament_matches
   WHERE tournament_id = t AND round = 'quarter'
     AND player1_id IS NOT NULL AND player2_id IS NOT NULL;
  IF v_count <> 4 THEN RAISE EXCEPTION 'ECHEC : quarts complets = %', v_count; END IF;

  FOR m IN SELECT id, player1_id FROM public.tournament_matches
            WHERE tournament_id = t AND round = 'quarter' ORDER BY bracket_position
  LOOP PERFORM pg_temp.win(m.id, m.player1_id); END LOOP;

  SELECT count(*) INTO v_count FROM public.tournament_matches
   WHERE tournament_id = t AND round = 'semi'
     AND player1_id IS NOT NULL AND player2_id IS NOT NULL;
  IF v_count <> 2 THEN RAISE EXCEPTION 'ECHEC : demi-finales completes = %', v_count; END IF;
  RAISE NOTICE 'OK  quatre quarts puis deux demi-finales, alimentes par les seuls vainqueurs';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  6. Une seule demi-finale terminee ne remplit rien
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  sf1 public.tournament_matches%rowtype;
  fin public.tournament_matches%rowtype;
  third public.tournament_matches%rowtype;
BEGIN
  SELECT * INTO sf1 FROM pg_temp.match_of('semi', NULL, 1);
  PERFORM pg_temp.win(sf1.id, sf1.player1_id);

  SELECT * INTO fin FROM pg_temp.match_of('final', NULL, 1);
  SELECT * INTO third FROM pg_temp.match_of('third_place', NULL, 1);

  IF fin.player1_id IS NOT NULL OR fin.player2_id IS NOT NULL THEN
    RAISE EXCEPTION 'ECHEC : la finale est remplie apres une seule demi-finale';
  END IF;
  IF third.player1_id IS NOT NULL OR third.player2_id IS NOT NULL THEN
    RAISE EXCEPTION 'ECHEC : la petite finale est remplie apres une seule demi-finale';
  END IF;
  IF fin.status <> 'pending' OR third.status <> 'pending' THEN
    RAISE EXCEPTION 'ECHEC : finale/petite finale annoncees trop tot';
  END IF;
  RAISE NOTICE 'OK  finale et petite finale restent vides tant que les deux demies ne sont pas jouees';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  7. La seconde demi-finale remplit les deux matchs, du bon cote
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  sf1 public.tournament_matches%rowtype;
  sf2 public.tournament_matches%rowtype;
  fin public.tournament_matches%rowtype;
  third public.tournament_matches%rowtype;
  v_count integer;
BEGIN
  SELECT * INTO sf2 FROM pg_temp.match_of('semi', NULL, 2);
  PERFORM pg_temp.win(sf2.id, sf2.player1_id);

  SELECT * INTO sf1 FROM pg_temp.match_of('semi', NULL, 1);
  SELECT * INTO sf2 FROM pg_temp.match_of('semi', NULL, 2);
  SELECT * INTO fin FROM pg_temp.match_of('final', NULL, 1);
  SELECT * INTO third FROM pg_temp.match_of('third_place', NULL, 1);

  IF sf1.winner_id IS NULL OR sf1.loser_id IS NULL
     OR sf2.winner_id IS NULL OR sf2.loser_id IS NULL THEN
    RAISE EXCEPTION 'ECHEC : une demi-finale n''enregistre pas vainqueur ET perdant';
  END IF;

  IF fin.player1_id <> sf1.winner_id OR fin.player2_id <> sf2.winner_id THEN
    RAISE EXCEPTION 'ECHEC : la finale n''oppose pas les deux vainqueurs de demi-finale';
  END IF;
  IF third.player1_id <> sf1.loser_id OR third.player2_id <> sf2.loser_id THEN
    RAISE EXCEPTION 'ECHEC : la petite finale n''oppose pas les deux perdants de demi-finale';
  END IF;
  IF fin.status <> 'ready' OR third.status <> 'ready' THEN
    RAISE EXCEPTION 'ECHEC : finale/petite finale pas ouvertes (% / %)', fin.status, third.status;
  END IF;

  -- Aucun joueur des deux matchs ne doit apparaitre dans l'autre.
  IF fin.player1_id IN (third.player1_id, third.player2_id)
     OR fin.player2_id IN (third.player1_id, third.player2_id) THEN
    RAISE EXCEPTION 'ECHEC : un joueur figure a la fois en finale et en petite finale';
  END IF;

  SELECT count(*) INTO v_count FROM public.notifications
   WHERE data->>'kind' = 'tournament_third_place';
  IF v_count <> 2 THEN
    RAISE EXCEPTION 'ECHEC : notifications petite finale = %', v_count;
  END IF;
  RAISE NOTICE 'OK  vainqueurs en finale, perdants en petite finale, chacun dans un seul match';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  8. Relancer le remplissage ne duplique rien
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  fin_avant public.tournament_matches%rowtype;
  fin_apres public.tournament_matches%rowtype;
  v_before integer;
  v_after integer;
BEGIN
  SELECT * INTO fin_avant FROM pg_temp.match_of('final', NULL, 1);
  SELECT count(*) INTO v_before FROM public.notifications
   WHERE data->>'kind' IN ('tournament_third_place', 'tournament_final_ready');

  PERFORM public.fill_tournament_finals_if_ready(pg_temp.tid());
  PERFORM public.fill_tournament_finals_if_ready(pg_temp.tid());

  SELECT * INTO fin_apres FROM pg_temp.match_of('final', NULL, 1);
  SELECT count(*) INTO v_after FROM public.notifications
   WHERE data->>'kind' IN ('tournament_third_place', 'tournament_final_ready');

  IF fin_avant.player1_id IS DISTINCT FROM fin_apres.player1_id
     OR fin_avant.player2_id IS DISTINCT FROM fin_apres.player2_id THEN
    RAISE EXCEPTION 'ECHEC : relancer le remplissage change la finale';
  END IF;
  IF v_after <> v_before THEN
    RAISE EXCEPTION 'ECHEC : relancer le remplissage renvoie des notifications (% -> %)', v_before, v_after;
  END IF;
  RAISE NOTICE 'OK  le remplissage est idempotent';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  9. Le classement final : 1er, 2e, 3e, 4e
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  t uuid := pg_temp.tid();
  fin public.tournament_matches%rowtype;
  third public.tournament_matches%rowtype;
  v_rank integer;
BEGIN
  SELECT * INTO third FROM pg_temp.match_of('third_place', NULL, 1);
  PERFORM pg_temp.win(third.id, third.player1_id);

  SELECT * INTO fin FROM pg_temp.match_of('final', NULL, 1);
  PERFORM pg_temp.win(fin.id, fin.player1_id);

  SELECT * INTO fin FROM pg_temp.match_of('final', NULL, 1);
  SELECT * INTO third FROM pg_temp.match_of('third_place', NULL, 1);

  SELECT final_rank INTO v_rank FROM public.tournament_participants
   WHERE tournament_id = t AND user_id = fin.winner_id;
  IF v_rank <> 1 THEN RAISE EXCEPTION 'ECHEC : le champion est classe %', v_rank; END IF;

  SELECT final_rank INTO v_rank FROM public.tournament_participants
   WHERE tournament_id = t AND user_id = fin.loser_id;
  IF v_rank <> 2 THEN RAISE EXCEPTION 'ECHEC : le finaliste est classe %', v_rank; END IF;

  SELECT final_rank INTO v_rank FROM public.tournament_participants
   WHERE tournament_id = t AND user_id = third.winner_id;
  IF v_rank <> 3 THEN RAISE EXCEPTION 'ECHEC : le vainqueur de la petite finale est classe %', v_rank; END IF;

  SELECT final_rank INTO v_rank FROM public.tournament_participants
   WHERE tournament_id = t AND user_id = third.loser_id;
  IF v_rank <> 4 THEN RAISE EXCEPTION 'ECHEC : le perdant de la petite finale est classe %', v_rank; END IF;

  IF (SELECT status::text FROM public.tournaments WHERE id = t) <> 'completed' THEN
    RAISE EXCEPTION 'ECHEC : le tournoi ne se termine pas apres la finale';
  END IF;
  RAISE NOTICE 'OK  1er champion, 2e finaliste, 3e et 4e par la petite finale';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  10. Construire deux fois ne recree rien
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  v_before integer;
  v_after integer;
  v_result jsonb;
BEGIN
  SELECT count(*) INTO v_before FROM public.tournament_matches WHERE tournament_id = pg_temp.tid();
  PERFORM set_config('test.uid', '44444444-4444-4444-8444-444444444444', false);
  v_result := public.launch_tournament(pg_temp.tid(), true);
  SELECT count(*) INTO v_after FROM public.tournament_matches WHERE tournament_id = pg_temp.tid();
  IF v_after <> v_before THEN
    RAISE EXCEPTION 'ECHEC : relancer la construction cree % matchs de plus', v_after - v_before;
  END IF;
  IF (v_result ->> 'already_built') <> 'true' THEN
    RAISE EXCEPTION 'ECHEC : la construction ne se sait pas deja faite';
  END IF;
  RAISE NOTICE 'OK  le tableau ne se construit qu''une fois (31 matchs + petite finale)';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  11. Le match commence des que les deux joueurs sont la
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  t uuid := pg_temp.tid();
  m public.tournament_matches%rowtype;
  v_result jsonb;
BEGIN
  -- Un duel tout neuf, programme dans cinquante minutes, deux joueurs presents.
  INSERT INTO public.tournament_matches (
    tournament_id, round, group_letter, bracket_position, status, scheduled_at,
    player1_id, player2_id, player1_joined_at, player2_joined_at,
    player1_last_seen_at, player2_last_seen_at
  ) VALUES (
    t, 'group', 'A', 9, 'ready', now() + interval '50 minutes',
    'a0000000-0000-4000-8000-000000000001', 'a0000000-0000-4000-8000-000000000002',
    now(), now(), now(), now()
  ) RETURNING * INTO m;

  UPDATE public.tournaments SET status = 'in_progress' WHERE id = t;

  v_result := public.create_tournament_game_if_ready(m.id);
  IF nullif(v_result ->> 'game_id', '') IS NULL THEN
    RAISE EXCEPTION 'ECHEC : deux joueurs presents et le plateau ne s''ouvre pas (%)', v_result ->> 'status';
  END IF;
  RAISE NOTICE 'OK  les deux joueurs sont la, le plateau s''ouvre sans attendre l''heure';
END;
$$;

-- ══════════════════════════════════════════════════════════════════════
--  12. Mais jamais contre un joueur qui n'est plus la
-- ══════════════════════════════════════════════════════════════════════
DO $$
DECLARE
  t uuid := pg_temp.tid();
  m public.tournament_matches%rowtype;
  v_result jsonb;
BEGIN
  INSERT INTO public.tournament_matches (
    tournament_id, round, group_letter, bracket_position, status, scheduled_at,
    player1_id, player2_id, player1_joined_at, player2_joined_at,
    player1_last_seen_at, player2_last_seen_at
  ) VALUES (
    t, 'group', 'A', 10, 'ready', now() + interval '50 minutes',
    'a0000000-0000-4000-8000-000000000003', 'a0000000-0000-4000-8000-000000000004',
    now() - interval '40 minutes', now(),
    now() - interval '40 minutes', now()
  ) RETURNING * INTO m;

  v_result := public.create_tournament_game_if_ready(m.id);
  IF nullif(v_result ->> 'game_id', '') IS NOT NULL THEN
    RAISE EXCEPTION 'ECHEC : partie lancee contre un joueur absent depuis 40 minutes';
  END IF;
  IF (v_result ->> 'status') <> 'waiting_for_opponent_return' THEN
    RAISE EXCEPTION 'ECHEC : statut inattendu %', v_result ->> 'status';
  END IF;
  RAISE NOTICE 'OK  une presence qui date ne vaut pas presence';
END;
$$;

\echo 'TOUS LES TESTS DE BRACKET SONT PASSES'
