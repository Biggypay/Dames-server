# Jusqu'où l'application tient-elle ?

La question se pose toujours de la même façon — « est-ce que tel service tiendrait
cinquante mille joueurs ? » — et elle se répond toujours de la même façon : en
mesurant ce qu'on a, avant de discuter de ce qu'on n'a pas.

Ce document contient une mesure, pas une opinion. Elle se refait :

```sh
node tests/charge.js 250,500,1000,2000,4000
```

`tests/charge.js` démarre le vrai `server.js`, ouvre autant de parties de dames,
et fait jouer chaque partie par le moteur autoritatif. Il chronomètre le coup de
bout en bout : de l'instant où un joueur l'envoie à l'instant où **l'adversaire**
le reçoit. C'est cette durée-là que quelqu'un ressent.

## Ce que le serveur de jeu encaisse aujourd'hui

Mesuré le 4 août 2026, sur une seule machine à quatre cœurs — le client de charge
tournant sur les mêmes cœurs que le serveur, ce qui rend les latences
**pessimistes** :

| Parties | Joueurs | Mémoire | Mo/joueur | Coup p50 | Coup p95 | Coups/s | Échecs |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 250 | 500 | 96 Mo | 0,05 | 46 ms | 94 ms | 2 793 | 0 |
| 500 | 1 000 | 132 Mo | 0,06 | 32 ms | 69 ms | 6 173 | 0 |
| 1 000 | 2 000 | 181 Mo | 0,05 | 66 ms | 159 ms | 6 231 | 0 |
| 2 000 | 4 000 | 281 Mo | 0,05 | 178 ms | 328 ms | 5 195 | 0 |
| 3 000 | 6 000 | 231 Mo | 0,03 | 195 ms | 525 ms | 6 263 | 0 |
| 4 000 | 8 000 | 484 Mo | 0,05 | 418 ms | 1 126 ms | 4 442 | 0 |

Trois chiffres à retenir :

- **0,05 Mo par joueur connecté.** La mémoire n'est pas le mur : cinquante mille
  joueurs tiendraient dans 2,5 Go.
- **0,2 à 0,3 ms de processeur par coup validé.** Un processus en soutient
  **4 000 à 6 000 par seconde**.
- **Zéro échec** jusqu'à huit mille joueurs simultanés. Rien n'a été refusé, rien
  n'a été perdu.

Le tableau mesure une pointe irréaliste : les quatre mille parties jouent
*exactement* en même temps. En vrai, un joueur de dames réfléchit cinq à trente
secondes. Vingt-cinq mille parties à un coup toutes les dix secondes, cela fait
2 500 coups par seconde — dans ce que tient un seul processus, sans marge.

## Sur une instance Render

Le tableau ci-dessus vient d'une machine à quatre cœurs. Render vend des
instances à un ou deux cœurs. `CPUS=0` épingle le serveur sur un seul cœur et
mesure ce que vaut réellement une instance **Standard** (1 cœur, 2 Go, 25 $) :

```sh
CPUS=0 node tests/charge.js 500,1000,2000,3000
```

| Parties | Joueurs | Mémoire | Coup p50 | Coup p95 | Coups/s | Échecs |
|---:|---:|---:|---:|---:|---:|---:|
| 500 | 1 000 | 133 Mo | 46 ms | 79 ms | 5 464 | 0 |
| 1 000 | 2 000 | 185 Mo | 131 ms | 215 ms | 4 410 | 0 |
| 2 000 | 4 000 | 260 Mo | 296 ms | 609 ms | 3 521 | 0 |
| 3 000 | 6 000 | 367 Mo | 238 ms | 534 ms | 5 170 | 0 |

**Six mille joueurs simultanés sur un seul cœur, 367 Mo, zéro échec** — et la
limite n'est toujours pas atteinte : c'est le banc d'essai qui s'arrête là, pas
le serveur. Un cœur tient 3 500 à 5 200 coups validés par seconde.

À retenir pour le choix d'instance :

- **Free** (0,1 cœur, 512 Mo) s'éteint après quinze minutes sans trafic. Une
  partie en cours meurt avec. À proscrire dès qu'un tournoi est annoncé.
- **Starter** (0,5 cœur, 512 Mo) : la mémoire est le problème avant le
  processeur — 4 000 joueurs occupaient déjà 260 Mo, et Node a besoin du reste.
- **Standard** (1 cœur, 2 Go) : mesuré ici. Confortable jusqu'à plusieurs
  milliers de joueurs.

## Ce qui cède en premier, et dans quel ordre

Le mur n'est pas là où on le cherche d'instinct.

1. **La diffusion Supabase (`postgres_changes`).** Le plan Pro compte ses
   connexions temps réel en *centaines*, pas en dizaines de milliers. C'est le
   premier plafond atteint, et de loin. Il ne concerne ni les coups, ni les
   chronomètres, ni la présence, ni les spectateurs — tout cela passe par le
   serveur de jeu — mais il concerne les notifications, le chat et les listes.

2. **Les soixante connexions Postgres.** Vingt-cinq mille parties qui
   enregistrent leur état, plus l'authentification, plus les portefeuilles : c'est
   le mur dur, celui qui coûte de l'argent à repousser (Supavisor, instance plus
   grande, moins d'écritures par partie).

3. **Le processus unique du serveur de jeu.** À 2 500 coups/s on est à sa limite,
   et un redémarrage perd l'état en mémoire de toutes les parties.

## Ce qu'il faut faire, dans cet ordre

**Le serveur de jeu se découpe — mais pas comme on le croit.** Une partie ne
parle jamais à une autre partie : deux joueurs, une room, rien de partagé. Reste
à envoyer les deux joueurs d'une même room sur le même processus.

Attention : **Render ne propose pas d'adhérence de session.** Son répartiteur
distribue les connexions au tour par tour. Augmenter le nombre d'instances d'un
même service enverrait le joueur 1 sur l'instance A et le joueur 2 sur
l'instance B — et `damesRooms` étant une `Map` en mémoire, l'instance B ne
connaîtrait pas la partie. Les coups tomberaient dans le vide.

Ce qu'il faut ici est plus fort qu'une adhérence de session : une **adhérence de
room**. L'adaptateur Redis de Socket.IO ne suffit pas — il partage la
*diffusion* entre processus, pas l'*état autoritatif*, qui est justement ce qui
compte.

La forme qui marche sur Render, sans Redis et sans toucher au moteur : faire
tourner N **services séparés**, chacun avec son URL. Le shard se décide au moment
où la partie est créée — `hash(room) % N` — et se range dans la ligne `games`.
Le client se connecte directement à l'URL de son shard.

Trois avantages, tous concrets :

- aucune adhérence à demander à Render, puisqu'il n'y a rien à répartir ;
- le repli en `polling` reste possible — précieux sur des réseaux difficiles, et
  perdu si l'on passait par plusieurs instances d'un même service ;
- une instance qui tombe n'emporte que son shard.

Un point à corriger le jour où l'on découpe : `restorePersistedRooms()` recharge
**toutes** les rooms au démarrage. Avec plusieurs shards, chacun croirait posséder
toutes les parties. Il faudra filtrer `load_game_server_room_states` sur le shard.

**La base, elle, ne se découpe pas.** C'est là que doit aller l'argent et le
travail : élargir l'instance, passer par le pooler, et surtout écrire moins —
une partie qui persiste son état à chaque coup coûte cent fois une partie qui le
persiste à chaque fin de tour.

**La diffusion se déplace.** Notifications, chat, listes de parties et de
tournois sont aujourd'hui sur `postgres_changes`. Deux issues : les faire passer
par le serveur de jeu qu'on a déjà, ou par un service de diffusion dédié.

## Faut-il un service de diffusion dédié (Ably, Pusher, PubNub) ?

Pour ce qu'il fait vraiment, oui, un jour :

- une diffusion massive vers des spectateurs — un match suivi par dix mille
  personnes, c'est un seul émetteur et dix mille récepteurs, exactement ce pour
  quoi ces services existent ;
- une présence mondiale et un historique de messages sans y penser ;
- un engagement de disponibilité contractuel.

Pour ce qu'il ne fait pas, non :

- il ne **valide** aucun coup. Un bus de messages transporte ; il ne sait pas si
  une prise est obligatoire. `server.js` reste, entier ;
- il n'enlève rien aux soixante connexions Postgres, qui sont le mur numéro deux ;
- il ne remplace ni les chronomètres autoritatifs, ni l'anti-triche, ni
  l'appariement.

Autrement dit : ce n'est pas une alternative au serveur de jeu, c'est un
remplaçant possible de `postgres_changes`. À décider quand la diffusion vers les
spectateurs deviendra le poste dominant — pas avant, et jamais à la place du
point 2.
