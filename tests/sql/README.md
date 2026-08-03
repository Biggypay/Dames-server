# Essais des migrations Supabase

Une migration se lit bien et se comporte mal. Ces deux fichiers permettent de
faire tourner le SQL de `supabase/migrations/` sur un PostgreSQL jetable, avec
les vraies colonnes de production, **avant** de l'appliquer quelque part où des
joueurs attendent.

`fixture.sql` reconstitue le strict nécessaire : les types, les tables touchées
(colonnes réelles), `auth.uid()` pilotable par une variable de session, et des
souches pour les fonctions que les migrations appellent sans les définir.

`test_migrations.sql` joue les situations qui comptent et échoue bruyamment :
un joueur ordinaire qui tente de faire rejouer un match, un rejeu refusé parce
que le tour suivant est lancé, un rejeu nominal (duel remis à jouer, tour
suivant libéré, joueurs réactivés, notifications, trace administrative), la
partie encore ouverte close sans vainqueur, et les quatre situations de
`get_game_resume_offer` — dont celle qui a coûté un match de tournoi : une
partie de trente secondes ne doit déclencher aucune fenêtre de règlement.

## Lancer

```sh
BASE=/var/lib/postgresql/sqlcheck
mkdir -p "$BASE" && chown postgres:postgres "$BASE"
su postgres -c "/usr/lib/postgresql/16/bin/initdb -D $BASE/data -A trust -U postgres"
su postgres -c "/usr/lib/postgresql/16/bin/pg_ctl -D $BASE/data \
  -o '-k $BASE -p 5433 -c listen_addresses=' -w start"

psql -h "$BASE" -p 5433 -U postgres -q -c \
  'CREATE ROLE anon; CREATE ROLE authenticated; CREATE ROLE service_role;'

for f in tests/sql/fixture.sql \
         supabase/migrations/20260802_truthful_player_presence.sql \
         supabase/migrations/20260802_admin_tournament_match_replay.sql \
         tests/sql/test_migrations.sql \
         supabase/migrations/20260803_start_when_both_players_are_present.sql \
         supabase/migrations/20260803_bracket_cross_group_and_third_place.sql \
         tests/sql/test_bracket.sql \
         tests/sql/test_bracket_any_game.sql; do
  psql -h "$BASE" -p 5433 -U postgres -q -v ON_ERROR_STOP=1 -f "$f" || exit 1
done
```

Les dernières lignes affichent `TOUS LES TESTS SONT PASSES`,
`TOUS LES TESTS DE BRACKET SONT PASSES` et `MEME STRUCTURE POUR TOUS LES JEUX`. Toute autre sortie est
un échec : le fichier s'arrête à la première assertion fausse.

`test_bracket_any_game.sql` déroule un tournoi ENTIER — trente-deux joueurs,
quatre groupes, huitièmes croisés, quarts, demies, petite finale, finale — pour
chacun des huit jeux de la plateforme. Le tableau ne doit rien savoir du jeu
qu'on y joue : si une règle devient un jour particulière à un jeu, ce fichier
tombe.

## Quand une migration touche une nouvelle table

Ajoutez ses colonnes réelles à `fixture.sql` — elles se lisent en une requête :

```sql
SELECT column_name, udt_name, is_nullable, column_default
  FROM information_schema.columns
 WHERE table_schema = 'public' AND table_name = '<table>'
 ORDER BY ordinal_position;
```
