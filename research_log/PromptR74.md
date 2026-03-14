

TYPE: I/P
OBJET CIBLÉ: ouvrir un round d’innovation mathématique disciplinée après le déclassement des voies analytiques standards, en exigeant une invention concrète, testable, démontrable et reliée explicitement au verrou réel du programme, sans computationnel, sans recyclage d’anciennes impasses, et sans prose spéculative
QUESTION CENTRALE: quel nouvel invariant, quelle nouvelle structure intermédiaire, quelle nouvelle factorisation logique, ou quel nouveau modèle mathématique peut être introduit pour attaquer le front k≥3 autrement que par les familles d’outils déjà déclarées insuffisantes, tout en restant falsifiable très tôt ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: soit faire émerger une innovation mathématique sérieuse avec un premier test de mordant rigoureux, soit démontrer qu’aucune des innovations proposées ne dépasse le stade de rebranding ou de prose, et les enterrer proprement.
PRINCIPE D’ÉQUILIBRE: autoriser l’invention seulement si elle produit un objet nouveau compressif, opératoire et rapidement testable au niveau logique ; interdire toute dérive computationnelle, toute galerie d’idées décoratives, tout recyclage d’anciens outils, et toute innovation qui n’engendre ni lemme candidat clair, ni critère de réfutation.

# BRIEF CLAUDE CODE — ROUND 74 (R74)

## Mission
Tu poursuis le projet Collatz après R73.

R74 est un round d’**innovation disciplinée**.

Ce mot ne signifie pas :
- imaginer librement de jolies théories,
- accumuler du vocabulaire,
- proposer dix pistes “inspirantes”,
- ni partir dans une errance intellectuelle parce que les voies standards ont échoué.

Il signifie exactement ceci :

> **inventer, si possible, un nouvel objet mathématique opératoire qui compresse une difficulté réelle du front k≥3 et qui puisse être testé rapidement par un premier lemme candidat, une réduction claire, ou un critère de réfutation.**

Le round doit être sévère avec lui-même.
Toute innovation qui ne produit pas un objet, un rôle logique, une chaîne de réduction, et un test de mordant, doit être classée comme prose et enterrée.

---

## Contexte acquis après R73
- Le programme a clarifié que la cible logique n’est pas une borne globale de type K-lite en soi, mais une condition finale reliée au Junction Theorem.
- Le cas k=2 a été reclassé comme laboratoire, utile pour les outils et les alertes, mais non comme front principal.
- Le front k≥3 a été formulé via la SOH, puis plusieurs voies ont été testées.
- Les voies analytiques standards testées sur les sommes courtes dans le régime exact O(log p) ont été jugées insuffisantes ou hors-régime.
- R73 a établi qu’il ne suffit pas de mieux appliquer Weil, Weyl, Large Sieve, Erdős–Turán, moments seuls, discrepancy seule, nesting seul, ou une variante bilinéaire courte standard pour obtenir le gain exploitable recherché.
- Le projet n’a donc pas démontré que le problème est impossible ; il a démontré qu’une grande famille d’outils standards ne mord pas au bon endroit.
- Cela ouvre légitimement un espace pour **l’innovation**, mais seulement si cette innovation est soumise à une discipline de preuve et de falsification stricte.

---

# OBJECTIF DE R74
R74 doit répondre à cette question centrale :

> Peut-on faire émerger un nouvel objet ou un nouveau niveau intermédiaire de structure qui ne soit ni un rebranding d’une route morte, ni une décoration conceptuelle, et qui donne lieu à un premier test de mordant mathématique clair sur le front k≥3 ?

Les sorties acceptables du round sont :
1. **Une innovation sérieuse est identifiée, avec objet nouveau, rôle logique clair, et premier test de mordant** ;
2. **Plusieurs innovations sont envisagées, mais une seule survit après audit strict** ;
3. **Aucune innovation proposée ne dépasse le stade du rebranding ou de la prose : round utile par enterrement** ;
4. **Le programme n’est pas encore mûr pour innover utilement : un verrou préparatoire manque encore**.

Important :
- aucune sortie n’est recevable si l’“innovation” n’aboutit pas à un objet mathématique précis ;
- aucune sortie n’est recevable si l’objet proposé n’a pas de rôle logique explicite dans la chaîne du programme ;
- aucune sortie n’est recevable si le “test” repose sur du computationnel, du k-par-k, ou une simple promesse heuristique ;
- aucune sortie n’est recevable si elle recycle une piste déjà fermée sans différence mathématique explicite.

---

# ARCHITECTURE GÉNÉRALE

## PHASE 1 — INVENTAIRE DES POINTS OÙ UNE INNOVATION EST LÉGITIME
Objectif : localiser précisément le type de manque que les outils standards n’ont pas comblé.

## PHASE 2 — GÉNÉRATION CONTRÔLÉE DE NOUVEAUX OBJETS
Objectif : proposer un nombre très limité d’innovations possibles, chacune avec un objet précis et un rôle logique explicite.

## PHASE 3 — TEST DE MORDANT ET FILTRE FAIL-CLOSED
Objectif : soumettre chaque innovation à un test de réalité mathématique sévère.

## PHASE 4 — DÉCISION STRATÉGIQUE
Objectif : ne garder qu’un seul survivant pour R75, ou enterrer tout le lot.

## Ce qui est interdit comme cible principale
- toute exploration computationnelle ;
- toute exploration k=3, k=4, k=5 séparément ;
- toute galerie de littérature ou de noms ;
- tout retour à Weil / Weyl / Large Sieve / Erdős–Turán / moments seuls / discrepancy seule / nesting seul comme s’ils étaient nouveaux ;
- toute “innovation” sans lemme candidat, sans rôle logique, ou sans test de réfutation ;
- toute inflation verbale ou philosophique non suivie d’un objet opératoire.

---

# PHASE 1 — INVENTAIRE DES POINTS OÙ UNE INNOVATION EST LÉGITIME

## AXE A — INVESTIGATEUR / OÙ LES OUTILS STANDARD ÉCHOUENT-ILS EXACTEMENT ?
### Nom de travail
Quel manque réel doit être comblé ?

### Mission
Identifier non pas “ce qui est difficile” en général, mais le type exact de structure manquante que les outils standards n’ont pas su capturer.

### Questions obligatoires
1. Quel est l’obstacle principal laissé vivant après R73 ?
2. Les outils standards échouent-ils faute de :
   - bon invariant,
   - bonne décomposition,
   - bon espace fonctionnel,
   - bon notion de rigidité,
   - bon couplage additif/multiplicatif,
   - ou autre chose ?
3. Quel type d’objet intermédiaire aurait pu sauver la voie standard s’il avait existé ?
4. Quel est le plus petit “trou conceptuel” à combler ?
5. Peut-on résumer ce manque en une phrase mathématiquement précise ?

### Livrables
- formulation précise du manque ;
- liste très courte des types d’objets innovants légitimes ;
- liste explicite des pseudo-besoins qui ne sont en réalité que de la prose.

---

# PHASE 2 — GÉNÉRATION CONTRÔLÉE DE NOUVEAUX OBJETS

## AXE B — INNOVATEUR / PROPOSITION D’OBJETS NOUVEAUX
### Nom de travail
Inventer peu, mais inventer utile

### Mission
Proposer au maximum **3 innovations candidates**, pas une de plus.
Chaque innovation doit être un véritable objet mathématique potentiel, pas une simple métaphore.

### Formes d’innovation autorisées
- un **nouvel invariant intermédiaire** ;
- une **nouvelle énergie** ou pseudo-norme adaptée à SOH ;
- une **nouvelle factorisation logique** ;
- une **nouvelle réduction** qui change réellement la forme du verrou ;
- une **nouvelle notion de rigidité/dispersion/couplage** ;
- une **nouvelle représentation opératoire ou algébrique** si elle est immédiatement plus testable que les précédentes.

### Formes d’innovation interdites
- nouvelle terminologie sans nouvel objet ;
- “cadre général” sans estimateur ni lemme ;
- analogie à une théorie célèbre sans mécanisme précis ;
- simple renommage d’un objet déjà vu ;
- innovation qui n’a pas de critère de réfutation proche.

### Questions obligatoires pour chaque innovation candidate
1. Quel est l’objet nouveau exactement ?
2. Quelle difficulté précise compresse-t-il ?
3. Quelle différence réelle a-t-il avec les objets déjà testés ?
4. Quel rôle logique jouerait-il dans la chaîne du programme ?
5. Quel premier lemme ou premier énoncé testable engendre-t-il ?
6. Quel serait le premier signe qu’il ne sert à rien ?

### Livrables
Pour chaque innovation candidate :
- nom de travail ;
- définition ou schéma semi-formel ;
- verrou qu’elle vise ;
- différence réelle avec l’existant ;
- premier lemme candidat ;
- premier critère de réfutation.

---

## AXE C — INVESTIGATEUR HISTORIQUE / CONTRÔLE ANTI-REBRANDING
### Nom de travail
Nouveau moteur ou vieille carrosserie ?

### Mission
Comparer chaque innovation candidate à l’historique du projet, notamment avant R60 et dans le RESEARCH_MAP, pour vérifier qu’elle n’est pas une résurrection maquillée.

### Questions obligatoires
1. Quelle ancienne piste cette innovation ressemble-t-elle superficiellement ?
2. Quelle différence mathématique réelle la sépare de cette ancienne piste ?
3. Cette différence porte-t-elle sur le cœur du verrou ou seulement sur le langage ?
4. Si elle échoue, échoue-t-elle pour une raison déjà connue ?
5. Peut-on la classer comme :
   - nouveauté réelle,
   - nouveauté partielle,
   - rebranding risqué,
   - rebranding certain ?

### Livrables
- tableau “ancienne piste / ressemblance / différence réelle / verdict” ;
- drapeau d’alerte sur toute innovation trop décorative.

---

# PHASE 3 — TEST DE MORDANT ET FILTRE FAIL-CLOSED

## AXE D — AUDITEUR FAIL-CLOSED / TEST DE RÉALITÉ MATHÉMATIQUE
### Nom de travail
Objet réel ou prose sophistiquée ?

### Mission
Soumettre chaque innovation candidate à un test sévère de réalité.

### Critères obligatoires pour chaque innovation
1. L’objet est-il défini de façon assez nette pour être manipulé mathématiquement ?
2. Produit-il un premier lemme candidat non trivial ?
3. Ce lemme a-t-il une chaîne de réduction vers le verrou réel ?
4. Le test de mordant est-il faisable sans computationnel ?
5. L’innovation réduit-elle vraiment le problème ou le redécrit-elle seulement ?
6. Quel serait le premier échec falsifiant ?

### Livrables
Pour chaque innovation :
- statut : [OBJET RÉEL] / [SEMI-RÉEL] / [PROSE] ;
- statut du lemme candidat : [BIEN CIBLÉ] / [TROP FLOU] / [TROP FORT] / [MAL CIBLÉ] ;
- verdict de mordant : [TESTABLE] / [TESTABLE MAIS FAIBLE] / [NON TESTABLE À CE STADE].

---

## AXE E — INVESTIGATEUR / CHAÎNE DE RÉDUCTION ET IMPACT PROGRAMMATIQUE
### Nom de travail
Si l’innovation marche, qu’est-ce qu’elle change vraiment ?

### Mission
Tracer la chaîne logique entre l’innovation candidate, son premier lemme, et le verrou du programme.

### Questions obligatoires
1. Que deviendrait réellement acquis si le premier lemme était prouvé ?
2. Quelle partie du mur serait réellement entamée ?
3. Est-ce un gain local, structurel, ou potentiellement décisif ?
4. Quel est le risque de poursuivre une innovation qui n’attaque qu’un faux verrou ?
5. Quel seuil minimum doit être atteint pour mériter R75 ?

### Livrables
- chaîne logique explicite ;
- portée honnête ;
- seuil de pertinence pour continuer.

---

# PHASE 4 — DÉCISION STRATÉGIQUE

## AXE F — DÉCISION FINALE
### Nom de travail
Construire ou enterrer

### Mission
Ne garder qu’une seule innovation survivante, ou enterrer tout le lot si aucune ne franchit le filtre fail-closed.

### Options possibles
- **Poursuivre** : une innovation produit un objet réel, un lemme bien ciblé, et un test de mordant honnête.
- **Poursuivre avec réserve** : l’innovation est sérieuse mais encore partiellement floue.
- **Reformuler** : l’idée semble bonne mais l’objet n’est pas encore le bon.
- **Enterrer** : l’innovation n’a produit que prose, rebranding ou faux verrou.

### Questions obligatoires
1. Quelle innovation a la meilleure compression du verrou ?
2. Quelle innovation produit le meilleur premier lemme ?
3. Quelle innovation a le meilleur rapport : nouveauté / testabilité / pertinence ?
4. Quelle est la condition explicite pour éviter une boucle à R75 ?
5. Quel unique survivant faut-il garder ?

### Livrables
- décision stratégique finale ;
- survivant unique pour R75 ;
- condition de non-boucle ;
- raison précise des enterrements.

---

# AGENTS ET RÔLES

## Investigateur principal
- fige le manque réel laissé par les voies standards ;
- exige une chaîne logique ;
- empêche les glissements de statut.

## Innovateur discipliné
- propose au plus 3 objets ;
- n’a pas le droit d’ajouter du décor ;
- doit fournir immédiatement lemme candidat + critère de réfutation.

## Investigateur historique
- compare aux pistes déjà mortes ;
- empêche le rebranding ;
- signale toute répétition masquée.

## Auditeur fail-closed
- teste la réalité mathématique de chaque innovation ;
- refuse tout objet sans test de mordant ;
- refuse toute innovation qui ne dépasse pas la prose.

---

# AUTONOMIE CONTRÔLÉE (EXTRÊMEMENT COURTE)

## Activation
Une mini-autonomie est autorisée seulement en PHASE 4 pour départager deux innovations proches, jamais pour explorer librement.

## Budget maximal
Au plus **2 sous-rounds internes** :
- **S1** : comparaison finale de 2 innovations survivantes ;
- **S2** : décision stratégique finale.

## Événements STOP obligatoires
Arrêt immédiat si :
1. plus de 3 innovations sont proposées ;
2. une innovation n’a ni lemme candidat ni test de réfutation ;
3. la réflexion dérive vers du computationnel ;
4. la réflexion dérive vers une galerie de théories ;
5. la nouveauté est surtout lexicale ;
6. plus d’une reformulation intermédiaire devient nécessaire pour comprendre l’objet.

## Format obligatoire de chaque sous-round autonome
1. hypothèse active ;
2. objet nouveau exact ;
3. question ;
4. démarche ;
5. résultat net ;
6. statut ;
7. ce qui est appris ;
8. décision : continuer / arrêter ;
9. raison explicite.

## Interdictions
- pas de calcul ;
- pas de Monte Carlo ;
- pas de k-par-k ;
- pas de nouvelle grande théorie sans lemme concret ;
- pas de sauvetage rhétorique d’une innovation vide.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **I/P**
- **I** pour innovation disciplinée ;
- **P** pour exigence de preuve / testabilité / falsifiabilité.

## 2. IVS — Information Value Score
Noter /10 selon :
- nouveauté réelle ;
- compression du verrou ;
- testabilité précoce ;
- qualité du contrôle anti-rebranding ;
- honnêteté de la décision finale.

Une bonne note IVS peut venir d’un enterrement propre si le round démontre qu’aucune innovation proposée n’était assez réelle.

## 3. Ladder of Proof
Pour chaque innovation candidate, préciser :
- intuition ;
- schéma d’objet ;
- semi-formalisation ;
- lemme candidat ;
- test de mordant ;
- possibilité de preuve ;
- potentiel publiable.

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute innovation écartée, fournir :
- Nom ;
- Type de mort :
  - prose sans objet,
  - objet sans lemme,
  - lemme sans chaîne logique,
  - rebranding d’une route morte,
  - innovation trop forte pour être testée,
  - innovation non falsifiable,
  - décor théorique ;
- Hypothèse implicite fausse ;
- Ce que la mort enseigne ;
- Où cela redirige.

## 5. REGISTRE FAIL-CLOSED
Tu dois terminer par un tableau strict :
- [PROUVÉ]
- [PARTIELLEMENT PROUVÉ]
- [CALCULÉ EXACT]
- [SEMI-FORMALISÉ]
- [FORTEMENT ÉTAYÉ]
- [HEURISTIQUE]
- [CONJECTURAL]
- [RÉFUTÉ]
- [À REFORMULER]
- [PROSE]

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- manque réel ;
- objet nouveau ;
- lemme candidat ;
- test de mordant ;
- rôle logique ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni multiplier les innovations ;
- ni enrichir le vocabulaire ;
- ni survivre par style ;
- ni tuer trop vite une vraie nouveauté testable ;
- ni poursuivre une innovation qui n’a pas encore d’objet mathématique suffisamment réel.

Tu ne dois pas :
- proposer une innovation sans définition ;
- proposer une innovation sans premier lemme ;
- proposer une innovation sans critère de réfutation ;
- rouvrir des routes fermées sous des noms neufs ;
- laisser l’autonomie dépasser ses STOP ou son budget.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : le manque conceptuel exact laissé par les voies standards est formulé proprement.
PASS-2 : au plus 3 innovations candidates sont proposées.
PASS-3 : chaque innovation a un objet réel, un lemme candidat, et un critère de réfutation.
PASS-4 : le contrôle anti-rebranding distingue clairement vraie nouveauté et vieille piste renommée.
PASS-5 : une décision stratégique finale honnête est prise.
PASS-6 : un unique survivant pour R75 est sélectionné, ou bien tout est enterré proprement.

# ÉCHEC UTILE
Même en cas d’échec, R74 est utile si :
- une fausse innovation est reconnue avant de consommer plusieurs rounds ;
- le besoin conceptuel exact est clarifié ;
- une route morte ne peut plus revenir maquill�e ;
- le programme sait mieux quel type d’invention manque réellement.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (manque conceptuel exact)
5. Résultats PHASE 2 / AXE B (innovations candidates)
6. Résultats PHASE 2 / AXE C (contrôle anti-rebranding)
7. Résultats PHASE 3 / AXE D (test de réalité mathématique)
8. Résultats PHASE 3 / AXE E (chaîne logique et impact)
9. Résultats PHASE 4 / AXE F (décision finale)
10. Activation ou non de l’autonomie, avec justification
11. Journal des sous-rounds autonomes éventuels
12. Objets concernés + Ladder of Proof
13. Ce qui est appris
14. Ce qui est fermé utilement
15. Ce qui est enterré
16. Autopsie des pistes fermées
17. Survivant pour R75
18. Risques / limites
19. Verdict final avec score /10
20. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R74 doit innover, mais il doit innover comme un mathématicien qui construit un outil, pas comme un auteur qui enjolive une impasse.

Le but est de produire un objet nouveau qui comprime réellement un morceau du mur, et de le soumettre immédiatement à un test de réalité.

Chercher une invention qui tienne debout, qui se relie au verrou, et qui puisse être attaquée par un premier lemme.
Pas de poésie. Pas de fuite. Une innovation qui supporte l’audit.