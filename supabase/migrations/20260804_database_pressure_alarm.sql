-- L'ALARME QUI MANQUAIT
--
-- Le relevé horaire (capture_db_load_snapshot) enregistrait fidèlement la montée
-- en charge pendant que l'application mourait, le 4 août. Il n'a prévenu
-- personne. Une mesure qui n'alerte pas n'est pas une surveillance : c'est une
-- autopsie.
--
-- `private.check_database_pressure()` tourne toutes les cinq minutes et prévient
-- les administrateurs par notification dès qu'un seuil est franchi. Elle ne
-- répète jamais le même signal dans l'heure : une alarme qui se répète est une
-- alarme qu'on apprend à ignorer.
--
-- Cinq signaux :
--   • connexions       : plus de 70 % des 60 disponibles — au-delà,
--                        l'authentification n'en obtient plus et personne ne se
--                        connecte. C'est exactement ce qui s'est produit.
--   • requete_longue   : une requête active depuis plus de 30 secondes.
--   • transaction_dormante : une transaction ouverte et inactive depuis plus de
--                        deux minutes retient verrous et connexions.
--   • temps_reel       : plus de 12 millions de blocs lus dans l'heure par le
--                        pipeline temps réel — le scénario du 4 août.
--   • publication_temps_reel : une table vient d'être ajoutée à la diffusion.
--                        C'est par cette dérive que la panne est arrivée
--                        (trente-trois tables publiées, treize jamais écrites).
--
-- Le détail complet du diagnostic et des leviers : docs/PANNE-BASE-DE-DONNEES.md
--
-- Consultation à la main : select private.check_database_pressure();

CREATE TABLE IF NOT EXISTS private.db_pressure_alerts (
  id bigserial PRIMARY KEY,
  raised_at timestamptz NOT NULL DEFAULT now(),
  kind text NOT NULL,
  detail jsonb
);

CREATE INDEX IF NOT EXISTS db_pressure_alerts_kind_raised_idx
  ON private.db_pressure_alerts (kind, raised_at DESC);

-- Liste de référence des tables diffusées. Toute addition ultérieure est
-- signalée par l'alarme.
CREATE TABLE IF NOT EXISTS private.realtime_publication_baseline (
  tablename text PRIMARY KEY,
  noted_at timestamptz NOT NULL DEFAULT now()
);

INSERT INTO private.realtime_publication_baseline (tablename)
SELECT tablename FROM pg_publication_tables WHERE pubname = 'supabase_realtime'
ON CONFLICT (tablename) DO NOTHING;

-- Corps de la fonction : voir la migration appliquée
-- `database_pressure_alarm_schedule` (identique à ce qui tourne en production).

SELECT cron.schedule('surveillance-pression-base', '*/5 * * * *',
                     'select private.check_database_pressure();');

SELECT cron.schedule('purge-alertes-pression', '41 4 * * *',
                     $$delete from private.db_pressure_alerts where raised_at < now() - interval '30 days'$$);
