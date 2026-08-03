\set ON_ERROR_STOP on

-- ══════════════════════════════════════════════════════════════════════
--  La même structure, quel que soit le jeu
--
--  Le tableau ne doit rien savoir du jeu qu'on y joue. Ce fichier déroule
--  un tournoi ENTIER — trente-deux joueurs, quatre groupes, huitièmes
--  croisés, quarts, demies, petite finale, finale — pour chacun des jeux
--  de la plateforme, et vérifie à chaque fois les mêmes invariants.
--
--  Si un jour une règle de tableau devient particulière à un jeu, ce
--  fichier tombe.
-- ══════════════════════════════════════════════════════════════════════

DO $$
DECLARE
  c_jeux constant text[] := ARRAY[
    'checkers', 'chess', 'tictactoe', 'quoridor',
    'penalty_shootout', 'rock_paper_scissors', 'ludo', 'dominos'
  ];
  adm uuid := '44444444-4444-4444-8444-444444444444';
  g text;
  t uuid;
  u uuid;
  i integer;
  v_bad integer;
  v_count integer;
  m record;
  sf1 public.tournament_matches%rowtype;
  sf2 public.tournament_matches%rowtype;
  fin public.tournament_matches%rowtype;
  third public.tournament_matches%rowtype;
  v_result jsonb;
  v_game_type text;
BEGIN
  DELETE FROM public.user_roles;
  DELETE FROM auth.users;
  INSERT INTO auth.users (id, email) VALUES (adm, 'admin@test');
  INSERT INTO public.user_roles (user_id, role) VALUES (adm, 'admin');
  PERFORM set_config('test.uid', adm::text, false);

  FOREACH g IN ARRAY c_jeux LOOP
    t := gen_random_uuid();

    INSERT INTO public.tournaments (id, name, game_type, status, starts_at, estimated_ends_at)
    VALUES (t, 'Tournoi ' || g, g, 'registration_open',
            now() + interval '1 hour', now() + interval '6 days');

    FOR i IN 1..32 LOOP
      u := gen_random_uuid();
      INSERT INTO auth.users (id, email) VALUES (u, g || i || '@test');
      INSERT INTO public.profiles (id, username) VALUES (u, g || '-' || i);
      INSERT INTO public.tournament_participants (tournament_id, user_id, status)
      VALUES (t, u, 'active');
    END LOOP;

    PERFORM public.launch_tournament(t, true);
    UPDATE public.tournaments SET status = 'in_progress' WHERE id = t;

    -- ── Structure attendue : 16 + 8 + 4 + 2 + 1 + 1 = 32 matchs ──────────
    SELECT count(*) INTO v_count FROM public.tournament_matches WHERE tournament_id = t;
    IF v_count <> 32 THEN
      RAISE EXCEPTION 'ECHEC (%) : % matchs au lieu de 32', g, v_count;
    END IF;
    SELECT count(*) INTO v_count FROM public.tournament_matches
     WHERE tournament_id = t AND round = 'third_place';
    IF v_count <> 1 THEN
      RAISE EXCEPTION 'ECHEC (%) : % petite(s) finale(s)', g, v_count;
    END IF;

    -- ── Les groupes se croisent ─────────────────────────────────────────
    SELECT count(*) INTO v_bad
      FROM public.tournament_matches gm
      JOIN public.tournament_matches nx ON nx.id = gm.next_match_id
     WHERE gm.tournament_id = t AND gm.round = 'group'
       AND nx.bracket_position <> CASE gm.group_letter
             WHEN 'A' THEN gm.bracket_position
             WHEN 'B' THEN 5 - gm.bracket_position
             WHEN 'C' THEN 4 + gm.bracket_position
             ELSE 9 - gm.bracket_position
           END;
    IF v_bad <> 0 THEN
      RAISE EXCEPTION 'ECHEC (%) : % liaisons de groupe erronees', g, v_bad;
    END IF;

    FOR m IN SELECT id, player1_id FROM public.tournament_matches
              WHERE tournament_id = t AND round = 'group'
    LOOP PERFORM public.advance_tournament_match_core(m.id, m.player1_id, 'test'); END LOOP;

    SELECT count(*) INTO v_bad
      FROM public.tournament_matches ro
      JOIN public.tournament_participants a ON a.user_id = ro.player1_id AND a.tournament_id = t
      JOIN public.tournament_participants b ON b.user_id = ro.player2_id AND b.tournament_id = t
     WHERE ro.tournament_id = t AND ro.round = 'round_of_16'
       AND a.group_letter = b.group_letter;
    IF v_bad <> 0 THEN
      RAISE EXCEPTION 'ECHEC (%) : % huitiemes opposent deux joueurs d''un meme groupe', g, v_bad;
    END IF;

    -- ── Huitiemes, quarts ───────────────────────────────────────────────
    FOR m IN SELECT id, player1_id FROM public.tournament_matches
              WHERE tournament_id = t AND round = 'round_of_16'
    LOOP PERFORM public.advance_tournament_match_core(m.id, m.player1_id, 'test'); END LOOP;

    FOR m IN SELECT id, player1_id FROM public.tournament_matches
              WHERE tournament_id = t AND round = 'quarter'
    LOOP PERFORM public.advance_tournament_match_core(m.id, m.player1_id, 'test'); END LOOP;

    SELECT count(*) INTO v_count FROM public.tournament_matches
     WHERE tournament_id = t AND round = 'semi'
       AND player1_id IS NOT NULL AND player2_id IS NOT NULL;
    IF v_count <> 2 THEN
      RAISE EXCEPTION 'ECHEC (%) : % demi-finales completes', g, v_count;
    END IF;

    -- ── Une seule demie ne remplit rien ─────────────────────────────────
    SELECT * INTO sf1 FROM public.tournament_matches
     WHERE tournament_id = t AND round = 'semi' AND bracket_position = 1;
    PERFORM public.advance_tournament_match_core(sf1.id, sf1.player1_id, 'test');

    SELECT * INTO fin FROM public.tournament_matches WHERE tournament_id = t AND round = 'final';
    SELECT * INTO third FROM public.tournament_matches WHERE tournament_id = t AND round = 'third_place';
    IF fin.player1_id IS NOT NULL OR fin.player2_id IS NOT NULL
       OR third.player1_id IS NOT NULL OR third.player2_id IS NOT NULL THEN
      RAISE EXCEPTION 'ECHEC (%) : finale ou petite finale remplie apres une seule demie', g;
    END IF;

    -- ── La seconde demie remplit les deux ───────────────────────────────
    SELECT * INTO sf2 FROM public.tournament_matches
     WHERE tournament_id = t AND round = 'semi' AND bracket_position = 2;
    PERFORM public.advance_tournament_match_core(sf2.id, sf2.player1_id, 'test');

    SELECT * INTO sf1 FROM public.tournament_matches
     WHERE tournament_id = t AND round = 'semi' AND bracket_position = 1;
    SELECT * INTO sf2 FROM public.tournament_matches
     WHERE tournament_id = t AND round = 'semi' AND bracket_position = 2;
    SELECT * INTO fin FROM public.tournament_matches WHERE tournament_id = t AND round = 'final';
    SELECT * INTO third FROM public.tournament_matches WHERE tournament_id = t AND round = 'third_place';

    IF fin.player1_id <> sf1.winner_id OR fin.player2_id <> sf2.winner_id THEN
      RAISE EXCEPTION 'ECHEC (%) : la finale n''oppose pas les deux vainqueurs', g;
    END IF;
    IF third.player1_id <> sf1.loser_id OR third.player2_id <> sf2.loser_id THEN
      RAISE EXCEPTION 'ECHEC (%) : la petite finale n''oppose pas les deux perdants', g;
    END IF;

    -- ── Le plateau cree porte bien le jeu du tournoi ────────────────────
    UPDATE public.tournament_matches
       SET player1_joined_at = now(), player2_joined_at = now(),
           player1_last_seen_at = now(), player2_last_seen_at = now(),
           scheduled_at = now() + interval '30 minutes'
     WHERE id = fin.id;
    v_result := public.create_tournament_game_if_ready(fin.id);
    IF nullif(v_result ->> 'game_id', '') IS NULL THEN
      RAISE EXCEPTION 'ECHEC (%) : le plateau de finale ne s''ouvre pas (%)', g, v_result ->> 'status';
    END IF;
    SELECT game_type::text INTO v_game_type FROM public.games
     WHERE id = (v_result ->> 'game_id')::uuid;
    IF v_game_type <> g THEN
      RAISE EXCEPTION 'ECHEC (%) : la partie creee est de type %', g, v_game_type;
    END IF;

    -- ── Classement final ────────────────────────────────────────────────
    PERFORM public.advance_tournament_match_core(third.id, third.player1_id, 'test');
    PERFORM public.advance_tournament_match_core(fin.id, fin.player1_id, 'test');

    SELECT * INTO fin FROM public.tournament_matches WHERE tournament_id = t AND round = 'final';
    SELECT * INTO third FROM public.tournament_matches WHERE tournament_id = t AND round = 'third_place';

    SELECT count(*) INTO v_bad
      FROM public.tournament_participants tp
     WHERE tp.tournament_id = t
       AND (
         (tp.user_id = fin.winner_id AND tp.final_rank IS DISTINCT FROM 1) OR
         (tp.user_id = fin.loser_id AND tp.final_rank IS DISTINCT FROM 2) OR
         (tp.user_id = third.winner_id AND tp.final_rank IS DISTINCT FROM 3) OR
         (tp.user_id = third.loser_id AND tp.final_rank IS DISTINCT FROM 4)
       );
    IF v_bad <> 0 THEN
      RAISE EXCEPTION 'ECHEC (%) : classement final incorrect (% place(s))', g, v_bad;
    END IF;

    IF (SELECT status::text FROM public.tournaments WHERE id = t) <> 'completed' THEN
      RAISE EXCEPTION 'ECHEC (%) : le tournoi ne se cloture pas', g;
    END IF;

    RAISE NOTICE 'OK  % : 32 matchs, groupes croises, petite finale, classement 1-2-3-4', g;
  END LOOP;
END;
$$;

\echo 'MEME STRUCTURE POUR TOUS LES JEUX'
