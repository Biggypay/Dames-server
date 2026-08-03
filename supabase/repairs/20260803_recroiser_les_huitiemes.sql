-- RÉPARATION PONCTUELLE — Tournoi de Dames, première édition 2026
--
-- Appliquée le 3 août 2026 à 04h47 UTC, environ douze heures avant le premier
-- huitième de finale, alors qu'aucun n'avait démarré.
--
-- Le tableau avait été construit avant la correction de `launch_tournament` :
-- les quatre matchs d'un groupe alimentaient deux huitièmes de ce même groupe,
-- si bien que Pouchon et Blackburn — tous deux qualifiés du groupe A —
-- s'affrontaient dès les huitièmes, et que la moitié du tableau ne rencontrait
-- jamais l'autre.
--
-- Ce script ne touche qu'aux liens et aux places des huitièmes. Les groupes,
-- les qualifiés, les horaires et les résultats acquis restent intacts.
--
-- Rejouable : les trois étapes sont idempotentes.

\set tournoi '672345d1-6e55-421a-b7be-193a3b0253aa'

-- 1. Sauvegarde intégrale du tableau avant modification.
INSERT INTO public.tournament_repair_backup (note, payload)
SELECT 'avant croisement des groupes en 8es (A-B, C-D)',
       jsonb_agg(to_jsonb(tm) ORDER BY tm.round, tm.group_letter, tm.bracket_position)
  FROM public.tournament_matches tm
 WHERE tm.tournament_id = :'tournoi';

-- 2. Chaque match de groupe alimente désormais le bon huitième :
--    A1→1 A2→2 A3→3 A4→4, B1→4 B2→3 B3→2 B4→1,
--    C1→5 C2→6 C3→7 C4→8, D1→8 D2→7 D3→6 D4→5.
UPDATE public.tournament_matches g
   SET next_match_id = ro.id, updated_at = now()
  FROM public.tournament_matches ro
 WHERE g.tournament_id = :'tournoi'
   AND g.round = 'group'
   AND ro.tournament_id = g.tournament_id
   AND ro.round = 'round_of_16'
   AND ro.bracket_position = CASE g.group_letter
         WHEN 'A' THEN g.bracket_position
         WHEN 'B' THEN 5 - g.bracket_position
         WHEN 'C' THEN 4 + g.bracket_position
         ELSE 9 - g.bracket_position
       END
   AND g.next_match_id IS DISTINCT FROM ro.id;

-- 3. Les huitièmes déjà peuplés sont réattribués selon la même règle. Un
--    huitième déjà lancé ou joué n'est jamais touché.
WITH q AS (
  SELECT g.group_letter, g.bracket_position AS pos, g.winner_id
    FROM public.tournament_matches g
   WHERE g.tournament_id = :'tournoi'
     AND g.round = 'group'
)
UPDATE public.tournament_matches ro
   SET player1_id = l.winner_id,
       player2_id = r.winner_id,
       player1_slot_vacant = (l.winner_id IS NULL),
       player2_slot_vacant = (r.winner_id IS NULL),
       player1_joined_at = NULL,
       player2_joined_at = NULL,
       player1_last_seen_at = NULL,
       player2_last_seen_at = NULL,
       result_conflict = false,
       status = 'ready',
       updated_at = now()
  FROM q l, q r
 WHERE ro.tournament_id = :'tournoi'
   AND ro.round = 'round_of_16'
   AND ro.game_id IS NULL
   AND ro.status IN ('pending', 'ready')
   AND l.group_letter = CASE WHEN ro.bracket_position <= 4 THEN 'A' ELSE 'C' END
   AND l.pos = CASE WHEN ro.bracket_position <= 4 THEN ro.bracket_position ELSE ro.bracket_position - 4 END
   AND r.group_letter = CASE WHEN ro.bracket_position <= 4 THEN 'B' ELSE 'D' END
   AND r.pos = CASE WHEN ro.bracket_position <= 4 THEN 5 - ro.bracket_position ELSE 9 - ro.bracket_position END;

-- 4. Contrôle : aucun duel intra-groupe, seize joueurs distincts, aucun
--    qualifié oublié. Les trois chiffres attendus sont 0, 16 et 0.
WITH ro AS (
  SELECT player1_id, player2_id FROM public.tournament_matches
   WHERE tournament_id = :'tournoi' AND round = 'round_of_16'
), joueurs AS (
  SELECT player1_id AS id FROM ro UNION ALL SELECT player2_id FROM ro
)
SELECT
  (SELECT count(*) FROM ro
     JOIN public.tournament_participants a
       ON a.user_id = ro.player1_id AND a.tournament_id = :'tournoi'
     JOIN public.tournament_participants b
       ON b.user_id = ro.player2_id AND b.tournament_id = :'tournoi'
    WHERE a.group_letter = b.group_letter) AS duels_intra_groupe,
  (SELECT count(DISTINCT id) FROM joueurs) AS joueurs_distincts,
  (SELECT count(*) FROM public.tournament_matches g
    WHERE g.tournament_id = :'tournoi' AND g.round = 'group'
      AND g.winner_id IS NOT NULL
      AND g.winner_id NOT IN (SELECT id FROM joueurs)) AS qualifies_oublies;
