# Agent de support IA MindSpille — guide de branchement

Un seul **cerveau** (IA + base de connaissances), deux **canaux** :

1. **Support in-app** (le plus rapide à lancer) — l'IA répond dans la messagerie de l'app
   en réutilisant 3 fonctions Supabase déjà en place. Ne nécessite **qu'une clé LLM**.
2. **WhatsApp** — l'IA répond sur WhatsApp. Nécessite en plus un **compte WhatsApp Business
   Cloud API** (Meta).

```
                 ┌──────────────────────────────┐
   Joueur ─────► │  n8n : le cerveau (OpenAI)   │ ◄───── system-prompt.md
  (app / WA)     │  + knowledge-base.md         │
                 └───────┬───────────────┬──────┘
                         │ reply         │ escalate
                         ▼               ▼
                 send_support_reply   flag_support_escalation
                 (répond au joueur)   (prévient un humain)
```

## Contenu du dossier

| Fichier | Rôle |
|---|---|
| `system-prompt.md` | Personnalité + règles de sécurité de l'IA. À coller comme system prompt. |
| `knowledge-base.md` | FAQ MindSpille. **À compléter** (frais, montants, délais → champs `⚠️ À PERSONNALISER`). |
| `n8n-workflow-inapp.json` | Workflow n8n à importer pour le support **in-app**. |
| `n8n-workflow-whatsapp.json` | Workflow n8n à importer pour **WhatsApp**. |

---

## Étape 0 — Ce que tu dois fournir

- **Une clé API LLM.** Les workflows sont écrits pour **OpenAI** — variable `OPENAI_API_KEY`
  (modèle `gpt-4o-mini`). Récupère la clé sur https://platform.openai.com/api-keys.
  (Pour utiliser Claude à la place, voir la section « Utiliser Claude » plus bas.)
- **La clé `service_role` Supabase** du projet MindSpille (Réglages → API → `service_role`).
  ⚠️ Secrète, ne jamais l'exposer côté client — elle ne vit que dans n8n.
- **(WhatsApp uniquement)** un compte **Meta WhatsApp Business Cloud API** (voir Étape 3).
- **Reconnecter le connecteur n8n** côté claude.ai si tu veux que je pousse/édite les workflows moi-même.

---

## Étape 1 — Variables d'environnement n8n

Dans n8n : **Settings → Variables** (ou variables d'environnement de ton hébergement n8n), ajoute :

| Variable | Valeur |
|---|---|
| `SUPABASE_URL` | `https://drmqjycbadnkbobfsxwp.supabase.co` |
| `SUPABASE_SERVICE_ROLE_KEY` | ta clé `service_role` |
| `OPENAI_API_KEY` | ta clé OpenAI |
| `MINDSPILLE_SYSTEM_PROMPT` | tout le contenu de `system-prompt.md` **+** `knowledge-base.md` collés à la suite |

> Astuce : mets d'abord le system prompt, puis « --- BASE DE CONNAISSANCES --- », puis la base de connaissances,
> le tout dans la seule variable `MINDSPILLE_SYSTEM_PROMPT`.

---

## Étape 2 — Support in-app (recommandé pour démarrer)

1. n8n → **Workflows → Import from File** → `n8n-workflow-inapp.json`.
2. Vérifie que les 4 variables de l'Étape 1 sont bien définies.
3. Ouvre le workflow, clique **Execute workflow** pour un test manuel.
   - S'il n'y a aucune conversation en attente, rien ne se passe : c'est normal.
   - Envoie-toi un message de support depuis un compte joueur de test, puis relance.
4. Vérifie dans l'app que la réponse arrive et que la conversation disparaît de la file « en attente ».
5. Quand c'est bon : **active** le workflow (il tournera toutes les minutes).

**Comment ça marche :** toutes les minutes, le workflow appelle `get_pending_support_conversations()`,
donne le contexte du joueur à Claude, qui décide `reply` (→ `send_support_reply`) ou
`escalate` (→ `flag_support_escalation` + petit message rassurant). Les messages déjà traités
sont marqués `ai_handled = true`, donc **jamais de double réponse**.

### Garde-fous à connaître
- L'IA **ne touche jamais** aux soldes (impossible techniquement : elle n'a que ces 3 fonctions).
- Tout litige d'argent est **escaladé**, pas résolu par l'IA.
- Tu restes prévenu par notification à chaque escalade → tu gardes la main.
- Pour **couper l'IA** à tout moment : désactive le workflow. Le support redevient 100 % humain.

---

## Étape 3 — WhatsApp (optionnel, après l'in-app)

Prérequis Meta (https://developers.facebook.com) :
1. Crée une **app** Meta → produit **WhatsApp**.
2. Récupère le **Phone Number ID** et un **token d'accès** (permanent de préférence).
3. Dans n8n, crée une **credential WhatsApp** (WhatsApp API + WhatsApp Trigger) avec ce token.
4. Importe `n8n-workflow-whatsapp.json`, ouvre les nœuds « Message WhatsApp reçu » et
   « Envoyer sur WhatsApp », et **sélectionne ta credential** (remplace `REMPLACER`).
5. Ajoute la variable `WHATSAPP_PHONE_NUMBER_ID` (ton Phone Number ID).
6. Copie l'**URL de production du webhook** du nœud trigger et configure-la dans Meta
   (Webhooks → WhatsApp → callback URL + verify token). Le nœud trigger n8n gère la vérification.
7. Teste en envoyant un message WhatsApp à ton numéro business. Active le workflow.

> Sur WhatsApp, le joueur n'est pas forcément relié à son compte MindSpille : l'IA répond aux
> questions générales (règles, dépôt/retrait, comment jouer) et renvoie vers le support in-app
> ou l'équipe pour tout ce qui touche à un compte précis.

---

## Utiliser Claude (Anthropic) au lieu d'OpenAI

Dans le nœud « Cerveau IA », remplace :
- URL → `https://api.anthropic.com/v1/messages`
- En-têtes → `x-api-key: {{$env.ANTHROPIC_API_KEY}}` + `anthropic-version: 2023-06-01`
- Corps JSON → `{ model: 'claude-haiku-4-5-20251001', max_tokens: 500, system: $env.MINDSPILLE_SYSTEM_PROMPT, messages: [ {role:'user', content: ...} ] }`
- Dans « Parser la décision », lis `src.content[0].text` au lieu de `src.choices[0].message.content`.

---

## Checklist de mise en production

- [ ] `knowledge-base.md` complété (plus aucun `⚠️ À PERSONNALISER`).
- [ ] Variables n8n définies (`SUPABASE_URL`, `SUPABASE_SERVICE_ROLE_KEY`, `OPENAI_API_KEY`, `MINDSPILLE_SYSTEM_PROMPT`).
- [ ] Workflow in-app testé sur un compte de test, puis activé.
- [ ] Tu reçois bien les notifications d'escalade.
- [ ] (WhatsApp) credential Meta OK, webhook vérifié, testé, activé.
- [ ] Tu sais **couper l'IA** en 1 clic (désactiver le workflow) en cas de souci.
