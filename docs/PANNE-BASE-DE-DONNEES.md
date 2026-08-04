# Quand plus personne ne peut se connecter

Le 4 août 2026, l'application est devenue inutilisable pendant plusieurs heures :
aucune connexion possible, pour personne. Le diagnostic a pris quarante minutes.
Il devrait en prendre deux. Voici comment.

## Le réflexe : ce n'est probablement pas l'authentification

L'authentification Supabase ne tombe presque jamais toute seule. Elle a besoin
d'une connexion à la base pour vérifier un jeton ; quand la base n'en donne plus,
l'authentification expire et **le symptôme visible est « personne ne peut se
connecter »**, alors que la cause est ailleurs.

Ses erreurs typiques, dans les journaux `auth` :

```
context deadline exceeded
unable to fetch records: timeout
500: error finding refresh token: context canceled
```

Si vous voyez cela, cherchez la saturation de la base, pas un problème de compte.

## Les quatre questions, dans l'ordre

### 1. Le projet est-il debout ?

Statut du projet Supabase. `ACTIVE_HEALTHY` ne veut pas dire « en bonne santé » :
la base peut être saturée sous un statut vert. `RESTARTING` explique tout et se
résout seul en quelques minutes.

### 2. La base accepte-t-elle une connexion ?

```sql
select 1;
```

Si cela répond par intermittence — une fois sur trois, avec des
`Connection terminated due to connection timeout` — c'est une saturation de
connexions, pas une panne.

### 3. Qui occupe les connexions ?

```sql
select state, count(*) as connexions,
       max(extract(epoch from (now() - query_start)))::int as plus_longue_requete_s
from pg_stat_activity
where backend_type = 'client backend'
group by state order by 2 desc;
```

Le plafond est bas : **60 connexions**. Des transactions `idle in transaction`
de plus d'une minute retiennent des verrous et des connexions ; elles se
libèrent avec `pg_terminate_backend(pid)`.

### 4. Qui consomme la base ?

La question décisive. Le classement ne ment pas :

```sql
select left(query, 90) as requete, calls,
       round(total_exec_time::numeric/1000, 1) as secondes_totales
from pg_stat_statements
order by total_exec_time desc limit 5;
```

Le 4 août, les deux premières places revenaient au pipeline **temps réel** —
339 569 et 200 298 appels pour près de 4 600 secondes — quand la première
requête applicative arrivait en troisième position, à 691 secondes.

## Ce qui s'était réellement passé

Trente-trois tables étaient publiées au temps réel, pour neuf mille écritures
cumulées, toutes tables confondues. Treize n'avaient **jamais** reçu la moindre
écriture. La plus écrite de toutes, `public_leaderboard`, était un classement
reconstruit périodiquement et rediffusé en entier à chaque client.

Or le pipeline temps réel re-résout la liste des tables publiées à chaque
sondage, et **ce coût suit le nombre de tables**. On payait du vide, en continu,
pour tout le monde.

S'y ajoutait un amplificateur côté application : `useLiveGames` s'abonnait à
toutes les modifications de `games`, sans filtre, et lançait quatre requêtes de
profil par événement reçu. Une mise à jour de partie devenait quatre requêtes
multipliées par le nombre de personnes connectées.

## L'alarme

`private.check_database_pressure()` tourne **toutes les cinq minutes** et
prévient les administrateurs par notification dès qu'un seuil est franchi :

| Signal | Seuil | Ce qu'il annonce |
|---|---|---|
| `connexions` | > 70 % de 60 | L'authentification va bientôt ne plus en obtenir |
| `requete_longue` | > 30 s | La base s'engorge |
| `transaction_dormante` | > 2 min | Verrous et connexions retenus pour rien |
| `temps_reel` | > 12 M blocs/h | Le scénario du 4 août recommence |
| `publication_temps_reel` | toute table ajoutée | La dérive qui a causé la panne |

Elle ne répète jamais le même signal dans l'heure : une alarme qui se répète est
une alarme qu'on apprend à ignorer. L'historique est dans
`private.db_pressure_alerts`, la charge horaire dans `public.db_load_snapshots`.

Pour la consulter à la main, sans attendre :

```sql
select private.check_database_pressure();
```

## Les leviers, du moins cher au plus cher

1. **Retirer une table de la diffusion temps réel.** Effet immédiat, coût nul si
   la table n'est pas écrite. La liste de référence est dans
   `private.realtime_publication_baseline` ; toute addition est signalée.

   ```sql
   alter publication supabase_realtime drop table public.<nom>;  -- retirer
   alter publication supabase_realtime add  table public.<nom>;  -- remettre
   ```

2. **Filtrer les abonnements du client.** Un abonnement sans filtre sur une table
   chaude coûte à *tous* les clients, pas seulement au sien.

3. **Agrandir l'instance.** Soixante connexions, c'est peu dès que le trafic
   monte. C'est le seul levier qui coûte de l'argent, et le dernier à envisager :
   les deux premiers rendent bien plus que ce qu'ils coûtent.

## Ce qu'il ne faut pas conclure trop vite

Le jour de la panne, le premier réflexe a été de soupçonner les migrations
appliquées la veille. Elles n'y étaient pour rien : la vérification a pris trois
minutes (`pg_stat_statements` ne les montrait nulle part, et la branche du
serveur de jeu n'était même pas déployée). **Vérifiez avant de revenir en
arrière** — un retour en arrière inutile ajoute une panne à la panne.
