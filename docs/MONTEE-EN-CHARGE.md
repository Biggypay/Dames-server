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

**Le serveur de jeu se découpe sans rien réécrire.** Une partie ne parle jamais à
une autre partie : deux joueurs, une room, rien de partagé. Il suffit de faire
tourner plusieurs processus et d'envoyer chaque room toujours au même, par
adhérence sur le nom de la room. Trois à six processus couvrent cinquante mille
joueurs. Aucun fournisseur supplémentaire, aucune réécriture du moteur.

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
