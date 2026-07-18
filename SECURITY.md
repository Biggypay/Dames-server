# Sécurité MindSpille — état & feuille de route

> Vérité importante : la sécurité « à 100 % » n'existe pas, et **tout ne vit pas dans ce dépôt**.
> Ce dépôt = **le serveur de jeux** (Node/Express/Socket.io sur Render). L'auth, le portefeuille
> HTG et la base de données vivent dans **Supabase + Lovable**. Le mobile, le réseau et l'infra
> sont ailleurs. Ce document dit clairement, pour chaque risque, **qui doit le traiter et où**.

Légende du statut :
- ✅ **Fait** dans ce serveur de jeux (code livré, testé).
- 🟦 **À faire côté Supabase/Lovable** (base de données, portefeuille, auth applicative).
- 🟨 **À faire côté infra** (Render, réseau, CI/CD, secrets).
- 📱 **À faire côté mobile** (si app native).
- 🧠 **Règle métier** à faire respecter côté serveur autoritatif.

---

## ✅ Déjà implémenté dans ce serveur (commit sécurité)

| Protection | Détail |
|---|---|
| Secret JWT | Plus de valeur par défaut connue ; secret aléatoire si `JWT_SECRET` absent. **Action : définir `JWT_SECRET` (fort) dans Render.** |
| Anti-spoof des gains | Sur les 5 `*_result` : l'émetteur doit être un **joueur réel** de la room ; le gagnant déclaré doit correspondre à un **joueur réel** (sinon nul). Impossible de réclamer un gain non gagné ou de créditer un tiers. |
| Anti brute-force | Rate limit IP sur `/auth/login` et `/auth/register` (12 / 5 min → 429). |
| Anti-flood socket | Déconnexion > 500 événements / 10 s ; `maxHttpBufferSize` 100 KB ; limite sur les émissions de résultat. |
| Validation d'entrée | Identifiants de room validés ; raisons de fin normalisées ; corps HTTP limité à 64 KB. |
| Anti-gel dames (serveur autoritatif + re-synchro) | Chaque coup validé incrémente une **version d'état** ; le serveur rediffuse l'état exact toutes les 5 s et sur demande (`dames_request_state`), **accuse réception** de chaque coup, renvoie l'état correctif quand un coup est rejeté, et restaure le plateau complet à la reconnexion. Un événement perdu (réseau mobile) se **corrige tout seul** au lieu de geler la partie. Testé : `npm test`. |
| En-têtes de sécurité | `X-Content-Type-Options`, `Referrer-Policy`, `Permissions-Policy`, `HSTS` ; `x-powered-by` retiré. |

---

## 🔴 Failles critiques restantes (à traiter en priorité)

### 1. 🧠 Résultats de jeu non « autoritatifs » (fraude n°1)
Le serveur **fait confiance** au client pour l'état du jeu (`boardState`, coups, scores). Un client modifié
peut jouer des coups illégaux ou déclarer un score faux. L'anti-spoof actuel empêche de créditer un
**tiers**, mais **pas** un joueur de mentir sur SA partie.
**Fix (gros chantier) :** rendre le serveur **autoritatif** — il rejoue/valide chaque coup et **calcule
lui-même le gagnant**, sans jamais croire le client. **Fait pour les dames** (sockets : `applyMove`
+ version d'état + re-synchro automatique anti-gel) ; les coups Tic-Tac-Toe et Quoridor sont aussi
validés côté serveur. Reste : étendre la **re-synchro automatique** aux autres jeux et durcir
l'arbitrage de Penalty/Chifoumi.

### 2. 🟦 Portefeuille & anti double-dépense (Supabase)
Double dépôt/retrait, soldes négatifs, crédits en double : à sécuriser dans Supabase avec
**transactions atomiques**, **contraintes** (`balance >= 0`), **verrous** (`SELECT … FOR UPDATE`),
**idempotence** (clé unique par transaction), et **webhooks de paiement signés & vérifiés**.

### 3. 🟦 Row Level Security (Supabase)
Chaque table (users, wallet, matches, tournaments) doit avoir des **policies RLS** : un joueur ne lit/écrit
que **ses** données. C'est LA protection contre IDOR/BOLA et la manipulation de solde.

### 4. 🟨 Secrets & JWT (Render/GitHub)
Définir `JWT_SECRET` fort dans Render ; s'assurer qu'aucun secret n'est commité ; rotation régulière ;
`run_secret_scanning` sur le dépôt.

---

## Couverture des 20 catégories demandées

| # | Catégorie | Où / Statut |
|---|---|---|
| 1 | Comptes (auth, sessions, JWT, MFA, brute-force) | ✅ JWT+rate-limit ici · 🟦 MFA/OTP/sessions = Supabase Auth |
| 2 | API (BOLA, IDOR, XSS, CSRF, injection, rate-limit) | ✅ rate-limit + validation ici · 🟦 RLS Supabase · 🧠 autorisation par objet |
| 3 | Base de données (SQLi, transactions, verrous, race) | 🟦 Supabase : requêtes paramétrées (déjà), RLS, transactions atomiques, verrous |
| 4 | Argent & portefeuille (double dépense, webhooks) | 🟦 Supabase : atomicité + idempotence + webhooks signés (**priorité**) |
| 5 | Jeux (triche score, bots, speed hack, duplication) | 🧠 serveur autoritatif (fix #1) · ✅ anti-spoof gains ici |
| 6 | Tournois (faux vainqueurs, multi-comptes, collusion) | 🟦 **N'existe pas dans ce serveur** — à concevoir côté Supabase/Lovable |
| 7 | Mises (mise modifiée, annulation, race) | 🧠+🟦 mise figée à la validation, résolution serveur, verrous |
| 8 | Chat / social (spam, phishing, usurpation) | 🟦 Lovable/Supabase : modération, rate-limit, filtrage de liens |
| 9 | IA intégrée (prompt injection, jailbreak, coûts) | 🟦 selon usage — si LLM exposé, filtrage entrées/sorties + quotas |
| 10 | Mobile (reverse, root, Frida, SSL pinning) | 📱 si app native : obfuscation, détection root/émulateur, pinning |
| 11 | Réseau (MITM, DDoS, replay) | 🟨 TLS (Render OK), WAF/CDN (Cloudflare), idempotence anti-replay |
| 12 | Infra (Render, Docker, secrets, IAM, WAF) | 🟨 secrets Render, principe du moindre privilège, WAF, sauvegardes |
| 13 | CI/CD (fuite secrets, supply chain) | 🟨 secret scanning, `npm audit`, permissions GitHub minimales |
| 14 | Admin (escalade, faux admin, audit) | 🟦 rôles Supabase, MFA admin obligatoire, journal d'audit |
| 15 | Confidentialité (chiffrement, données perso) | 🟦 chiffrement au repos (Supabase) + en transit (TLS), logs sans secrets |
| 16 | Anti-fraude (bots, multi-comptes, fingerprint) | 🟦 fingerprint appareil, détection multi-comptes, analyse comportementale |
| 17 | Performance (rate-limit, cache, files) | ✅ rate-limit ici · 🟨 cache/CDN, files d'attente |
| 18 | Monitoring (alertes, IDS, surveillance financière) | 🟨 logs Render + alertes, surveillance des soldes anormaux |
| 19 | Tests (unitaires, charge, pentest, fuzz) | ✅ tests anti-fraude ici · 🟨 pentest + fuzz à planifier |
| 20 | Logique métier (détournement des règles) | 🧠 serveur autoritatif + règles anti-abus (abandons stratégiques, etc.) |

---

## Prochaines étapes recommandées (ordre de priorité)

1. **Définir `JWT_SECRET` fort dans Render** (5 min, énorme gain).
2. **Supabase : RLS + portefeuille atomique + webhooks signés** (le cœur de l'argent).
3. **Serveur autoritatif** pour les résultats de jeu — fait pour les dames (validation + re-synchro anti-gel) ; étendre la re-synchro à TTT/Quoridor puis à Penalty/Chifoumi.
4. **Concevoir le mode tournoi de façon sécurisée** s'il doit exister (anti multi-comptes, récompenses idempotentes).
5. **Monitoring financier** : alerte sur variations de solde anormales.

> Ce serveur a été durci de façon **additive et testée**, sans casser le jeu ni le crédit des gains
> légitimes. Le reste nécessite un travail côté Supabase / Lovable / infra / mobile, listé ci-dessus.
