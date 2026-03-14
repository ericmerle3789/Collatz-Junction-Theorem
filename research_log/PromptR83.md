TYPE: X/I/P
OBJET CIBLÉ: lancer un round plus profond et plus autonome pour faire émerger, tester, auditer et sélectionner un candidat réellement mordant — idéalement un lemme candidat pouvant être au moins semi-formalisé ou prouvé — à partir de la sortie théorique ouverte par R82, tout en verrouillant strictement les dérives computationnelles, le k-par-k, le rebranding, la prose et les fausses percées
QUESTION CENTRALE: à partir du front désormais identifié — le gap somme ↔ produit et la connexion corrSum → équations d'S-unités — Claude Code peut-il, avec une autonomie un peu plus profonde mais fortement sécurisée, faire émerger un candidat réellement plus fort qu’un simple cadre théorique, c’est-à-dire un objet/lemme susceptible de mordre, d’être vérifié, comparé, falsifié, et si possible partiellement prouvé ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: soit produire un unique survivant sérieux (objet + lemme candidat + chaîne logique + statut de preuve) issu d’un tournoi élargi mais verrouillé ; soit démontrer proprement que l’autonomie plus profonde n’a pas réussi à dépasser les limites déjà connues, et revenir avec un diagnostic utile au lieu d’une prose ambitieuse.
PRINCIPE D’ÉQUILIBRE: augmenter l’autonomie ne signifie pas relâcher la méthode ; au contraire, plus Claude Code va loin seul, plus il doit être tenu par des checkpoints explicites, des audits croisés, des critères de victoire et d’élimination, un registre fail-closed strict, et des STOP immédiats dès qu’il dérive vers le computationnel, le cas-par-cas, la réinvention décorative ou la rhétorique de percée non étayée.

# BRIEF CLAUDE CODE — ROUND 83 (R83)

## Mission
Tu poursuis le projet Collatz après R82 et toute la séquence R67→R82.

R83 est un round de **profondeur autonome contrôlée**.

Le but n’est plus seulement de cartographier, reformuler, ou ouvrir un pont théorique.
Le but est désormais d’utiliser tout ce qui a été appris pour pousser plus loin la machine de recherche, avec plus d’autonomie qu’avant, mais dans un cadre rigoureusement balisé, afin de tester jusqu’où Claude Code peut aller sans se perdre.

R83 doit donc viser quelque chose de plus ambitieux :

> **faire émerger, éprouver et auditer un candidat réellement mordant — idéalement un lemme candidat pouvant être semi-formalisé, ou mieux, partiellement prouvé — à partir du front théorique actuellement le plus sérieux, sans quitter le protocole de sécurité méthodologique.**

Ce round n’autorise pas :
- la prose mathématique,
- les slogans de solution,
- le computationnel comme béquille,
- le k-par-k,
- les micro-cas accumulés,
- ni les théories “prometteuses” sans objet, sans lemme, sans audit.

Il autorise en revanche :
- une autonomie un peu plus longue que d’habitude,
- un tournoi de candidats plus profond,
- des sous-rounds internes plus substantiels,
- à condition que chaque sous-round soit contrôlé, audité et stoppable.

---

## Contexte acquis avant R83
- La cible réelle a été clarifiée : il faut travailler en vue de N_0(d)=0, sans confondre cible, outil et laboratoire.
- Les voies standards analytiques dans le régime O(log p) ont été fermées ou bornées.
- Le laboratoire k=2 a été définitivement reclassé comme laboratoire et non comme cible.
- SAMC, la voie spectrale, la voie bilinéaire courte standard, le multiplicatif pur, puis plusieurs mécanismes associés ont été testés et déclassés ou bornés.
- R79 a isolé l’auto-référence arithmétique comme meilleure cause source candidate accessible.
- R80 a mis au jour un noyau irréductible dans F_p : beaucoup de reformulations internes n’apportent pas de prise nouvelle.
- R81 a structuré la logique “dehors du noyau / faux extérieur / objet externe”.
- R82 a fourni une vraie sortie théorique du noyau via la connexion corrSum → équations d'S-unités, et a clarifié le **gap somme ↔ produit** comme verrou précis.
- Mais R82 a aussi montré que cette ouverture théorique est encore **quantitativement trop faible** pour entamer directement le cœur du verrou.

Donc le point de départ de R83 est clair :
- il existe un front théorique sérieux ;
- il existe un manque concret très net ;
- il faut maintenant tester si une autonomie plus profonde peut faire émerger **un vrai candidat de lemme mordant**, et non un simple cadre conceptuel.

---

# OBJECTIF DE R83
R83 doit répondre à cette question centrale :

> En laissant à Claude Code une autonomie plus profonde mais fortement balisée, peut-on faire émerger un candidat réellement plus fort que le simple cadre BTL/S-unités — c’est-à-dire un objet et un lemme candidat vérifiable, auditable, comparatif, et si possible partiellement prouvable — ou bien l’autonomie plus longue ne produit-elle qu’un reconditionnement des limites déjà connues ?

Les sorties acceptables du round sont :
1. **Un survivant sérieux est produit : objet précis + lemme candidat + test de réfutation + statut de preuve au moins semi-formalisé** ;
2. **Deux survivants sérieux restent en lice, mais un seul est recommandé pour R84 avec justification forte** ;
3. **Aucun candidat ne dépasse les limites déjà connues : autonomie utile mais non concluante** ;
4. **Le front actuel est encore trop haut : il faut un verrou préparatoire avant tout lemme vraiment mordant.**

Important :
- aucune sortie n’est recevable sans au moins un lemme candidat explicite ;
- aucune sortie n’est recevable si ce lemme dépend en pratique de petites valeurs de k, d’un scan, d’un inventaire numérique ou de cas particuliers ;
- aucune sortie n’est recevable si le candidat survit seulement parce qu’il est original ou “profond” ;
- aucune sortie n’est recevable sans critère de réfutation, audit historique et chaîne logique claire vers le verrou.

---

# CE QU’IL FAUT MAINTENANT TENTER CONCRÈTEMENT
R83 doit essayer de transformer le front théorique de R82 en quelque chose de plus opératoire.

## Cibles légitimes de R83
1. **Un lemme-pont somme → produit plus mordant** que la simple réduction à une équation d'S-unités générique.
2. **Un raffinement source-compatible de BTL** qui exploite une structure spéciale de corrSum absente des cadres d'S-unités généraux.
3. **Une obstruction minimale de non-réalisation** plus forte qu’une simple borne de cardinalité ou de nombre de solutions.
4. **Un invariant/filtration hors noyau F_p** qui traduit une contrainte sur corrSum sans retomber dans les reformulations closes.
5. **Un lemme de rigidité spéciale** sur la forme exacte des coefficients ou sur l’architecture arithmétique de d = 2^S − 3^k.

## Ce qui doit être refusé immédiatement
- retour au computationnel ;
- retour à des petits k ;
- retour à des “tests à la main” comme moteur ;
- retour à une théorie générale prestigieuse sans prise précise ;
- simple variation sur Baker / S-unit sans structure propre à corrSum ;
- toute idée qui ne produit pas un lemme candidat rapidement.

---

# ARCHITECTURE GÉNÉRALE

## PHASE 1 — QUALIFICATION DU FRONT ET DU TYPE DE LEMME À CHERCHER
Objectif : préciser quel type de lemme mordant serait légitime et utile à ce stade.

## PHASE 2 — GÉNÉRATION CONTRÔLÉE DE CANDIDATS DE LEMMES
Objectif : faire émerger plusieurs candidats sérieux mais peu nombreux.

## PHASE 3 — AUTONOMIE APPROFONDIE SOUS CHECKPOINTS
Objectif : laisser Claude Code pousser plus loin les candidats, mais sous contrôle strict.

## PHASE 4 — AUDIT CROISÉ, TOURNOI ET SÉLECTION
Objectif : faire comparaître les candidats et garder un seul survivant sérieux, ou aucun.

## PHASE 5 — STATUT DE PREUVE ET DÉCISION STRATÉGIQUE
Objectif : classifier honnêtement le survivant : heuristique, semi-formalisé, partiellement prouvé, faux départ, etc.

## Ce qui est interdit comme cible principale
- computationnel ;
- k-par-k ;
- validation par cas ;
- galeries bibliographiques ;
- simples cadres théoriques sans lemme ;
- rebranding d’un ancien mécanisme ;
- survie d’un candidat sans audit croisé ni critère de défaite.

---

# PHASE 1 — QUALIFICATION DU FRONT ET DU TYPE DE LEMME À CHERCHER

## AXE A — INVESTIGATEUR CAUSAL / QUEL TYPE DE LEMME MANQUE VRAIMENT ?
### Nom de travail
Quel lemme serait utile, et pas seulement joli ?

### Mission
Transformer le verrou actif en un **type précis de lemme** à rechercher, et non en une ambition vague.

### Questions obligatoires
1. Quel type de lemme manque exactement aujourd’hui : pont, rigidité, exclusion, obstruction, transfert, compatibilité, autre ?
2. Quel type de lemme serait trop faible même s’il était vrai ?
3. Quel type de lemme serait trop haut ou prématuré ?
4. Quel lemme serait réellement utile au programme à ce stade ?
5. Quelle formulation minimale de ce type de lemme est autorisée pour la suite ?

### Livrables
- type de lemme recherché ;
- types de lemmes trop faibles / trop hauts à bannir ;
- formulation minimale autorisée.

---

## AXE B — INVESTIGATEUR HISTORIQUE / QU’EST-CE QUI A DÉJÀ ÉTÉ TUÉ SOUS FORME VOISINE ?
### Nom de travail
Quel lemme ressemble trop à un vieux mort ?

### Mission
Prévenir la résurrection d’anciens faux lemmes sous un habillage plus raffiné.

### Questions obligatoires
1. Quels styles de lemmes ont déjà été implicitement ou explicitement fermés ?
2. Quelle différence minimale un nouveau candidat doit-il montrer ?
3. Quel piège est le plus probable à ce stade : trop général, trop faible, trop décoratif, trop local ?
4. Quel test rapide permet de déclarer “rebranding” ?
5. Quels angles morts historiques doivent être rappelés avant la génération ?

### Livrables
- tableau anti-résurrection des lemmes ;
- test rapide de non-redondance ;
- angles morts prioritaires à surveiller.

---

# PHASE 2 — GÉNÉRATION CONTRÔLÉE DE CANDIDATS DE LEMMES

## AXE C — INNOVATEUR DISCIPLINÉ / PROPOSITION D’AU PLUS 4 CANDIDATS
### Nom de travail
Faire émerger plusieurs lemmes, pas plusieurs rêves

### Mission
Proposer au maximum **4 candidats**. Pas davantage.
Chaque candidat doit inclure :
- un objet précis,
- un lemme candidat,
- un test de réfutation,
- une raison de tournoi,
- un statut de plausibilité initial.

### Règle absolue
Un candidat n’est recevable que si la chaîne suivante est explicite :

verrou actif → type de lemme utile → objet précis → lemme candidat → test de réfutation → critère de victoire.

### Questions obligatoires pour chaque candidat
1. Quel objet précis porte le lemme ?
2. Pourquoi ce candidat est-il plus mordant que le simple cadre BTL ?
3. Quel test rapide montrerait qu’il n’est qu’un rebranding ?
4. Quelle serait sa première faiblesse prévisible ?
5. Pourquoi mérite-t-il d’entrer en autonomie approfondie ?

### Livrables
Pour chaque candidat :
- nom de travail ;
- objet ;
- lemme candidat ;
- critère de réfutation ;
- critère de victoire ;
- plausibilité initiale.

---

## AXE D — STYLES D’AGENTS POUR R83
### Nom de travail
Quelle équipe pour explorer profondément sans dériver ?

### Mission
Définir le dispositif agentique pour un round plus autonome.

### Agents requis
1. **Investigateur causal** : vérifie que le candidat part du bon verrou.
2. **Investigateur historique** : tue les rebrandings et les redondances.
3. **Innovateur discipliné** : propose les candidats.
4. **Auditeur fail-closed** : force les statuts et refuse les slogans.
5. **Arbitre de tournoi** : impose la compétition et l’élimination.
6. **Vérificateur de preuve** : examine si le candidat peut être semi-formalisé ou partiellement prouvé.
7. **Synthétiseur structurel** : relie le candidat au programme sans gonfler sa portée.

### Questions obligatoires
1. Quels agents doivent travailler en parallèle ?
2. Quels agents doivent se contredire explicitement ?
3. Quel agent doit arrêter immédiatement un candidat ?
4. Quel ordre d’intervention maximise la profondeur sans ouvrir le chaos ?
5. Quel checkpoint intermédiaire doit être obligatoire avant de prolonger l’autonomie ?

### Livrables
- protocole agentique de R83 ;
- ordre d’intervention ;
- checkpoints d’arrêt obligatoires.

---

# PHASE 3 — AUTONOMIE APPROFONDIE SOUS CHECKPOINTS

## MODE AUTONOME ÉTENDU MAIS FERMÉ
Objectif : laisser Claude Code pousser plus loin que d’habitude, mais uniquement dans une arène strictement séquencée.

### Budget d’autonomie
Au plus **5 sous-rounds internes**, chacun avec audit et STOP possibles :
- **S1** : qualification initiale des candidats ;
- **S2** : première poussée structurale sur les 2 ou 3 meilleurs ;
- **S3** : vérification historique + anti-rebranding ;
- **S4** : test de preuve / semi-formalisation / statut de lemme ;
- **S5** : tournoi final et décision.

### Règle fondamentale
L’autonomie est plus longue qu’avant, mais elle reste une autonomie de **pipeline fermé**, pas d’exploration libre.

### Checkpoints obligatoires
Après chaque sous-round, Claude Code doit explicitement répondre :
1. le candidat s’est-il renforcé ou affaibli ?
2. a-t-il gagné en mordant réel ?
3. a-t-il perdu sa non-redondance ?
4. son statut de preuve a-t-il progressé ?
5. faut-il le tuer maintenant ?

### Événements STOP immédiats
Arrêt d’un candidat si :
1. il retombe dans le computationnel ou le k-par-k ;
2. il devient essentiellement un ancien mécanisme rebrandé ;
3. il n’a plus de lemme candidat clair ;
4. il perd tout critère de réfutation ;
5. son statut de preuve n’évolue pas après deux sous-rounds ;
6. il n’apporte aucun gain par rapport au simple cadre BTL ;
7. son lien au verrou devient rhétorique.

### Format obligatoire de chaque sous-round autonome
1. candidat(s) actif(s) ;
2. objectif du sous-round ;
3. objet précis ;
4. lemme candidat actif ;
5. résultat net ;
6. statut ;
7. gain ou perte par rapport au checkpoint précédent ;
8. critère de victoire ou d’élimination ;
9. décision : continuer / tuer ;
10. raison explicite.

---

# PHASE 4 — AUDIT CROISÉ, TOURNOI ET SÉLECTION

## AXE E — AUDITEUR FAIL-CLOSED / TEST DE RÉALITÉ ET DE PREUVE
### Nom de travail
Quel candidat vit encore sous la lumière crue ?

### Mission
Soumettre les candidats restants à un audit final très sévère.

### Critères obligatoires
1. Le candidat est-il réellement non redondant ?
2. Son objet est-il suffisamment précis ?
3. Son lemme est-il général ?
4. Le test de réfutation est-il réel et proche ?
5. Son statut de preuve a-t-il progressé ?
6. A-t-il un mordant supérieur au simple cadre conceptuel ?
7. Résiste-t-il à l’historique et à l’audit croisé ?
8. Mérite-t-il d’être appelé “candidat de percée”, ou seulement “meilleure idée du moment” ?

### Livrables
Pour chaque candidat :
- statut : [QUALIFIÉ] / [QUALIFIÉ AVEC RÉSERVE] / [ÉLIMINÉ] ;
- statut de preuve : [HEURISTIQUE] / [SEMI-FORMALISÉ] / [PARTIELLEMENT PROUVÉ] / [BLOQUÉ] ;
- raison précise.

---

## AXE F — ARBITRE DE TOURNOI + SYNTHÉTISEUR / IMPACT PROGRAMMATIQUE RÉEL
### Nom de travail
Quel candidat ouvre le meilleur chemin concret ?

### Mission
Comparer les survivants restants et en choisir un seul, ou aucun.

### Questions obligatoires
1. Quel candidat gagne réellement sur la combinaison : nouveauté + mordant + auditabilité + statut de preuve ?
2. Quel candidat est trop élégant pour être utile ?
3. Quel candidat semble fort, mais n’entame pas le bon mur ?
4. Quel seuil minimum doit être atteint pour justifier R84 ?
5. Si aucun candidat ne gagne clairement, faut-il suspendre ?

### Livrables
- classement final ;
- survivant unique ou suspension ;
- justification comparative.

---

# PHASE 5 — DÉCISION STRATÉGIQUE

## AXE G — DÉCISION FINALE
### Nom de travail
A-t-on enfin un candidat qui mérite d’être poussé ?

### Mission
Décider si R83 a produit un véritable survivant pour le round suivant.

### Options possibles
- **Poursuivre** : un candidat réel, non redondant, mordant et au moins semi-formalisé survit.
- **Poursuivre avec réserve** : un candidat sérieux mais encore fragile survit.
- **Suspendre l’innovation** : l’autonomie plus profonde n’a pas produit de vrai gain.
- **Reformuler le front** : le bon type de lemme manque encore.

### Questions obligatoires
1. Quel candidat mérite vraiment R84 ?
2. Pourquoi n’est-il pas juste le moins mauvais ?
3. Quelle est la condition explicite de non-boucle pour R84 ?
4. Qu’a réellement gagné le programme ?
5. Qu’est-ce qui doit être enterré sans ambiguïté ?

### Livrables
- décision finale ;
- survivant pour R84 ;
- condition de non-boucle ;
- progrès réel vs élégance trompeuse.

---

# CONTRAINTES MÉTHODOLOGIQUES GLOBALES
Tu dois distinguer explicitement :
- verrou actif ;
- type de lemme ;
- objet candidat ;
- test de réfutation ;
- critère de victoire ;
- statut de preuve ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni sauter de la compréhension à la solution ;
- ni inventer trop haut ;
- ni survivre par profondeur rhétorique ;
- ni garder un candidat parce qu’il est “intéressant” ;
- ni laisser l’autonomie dériver hors du pipeline fermé.

Tu ne dois pas :
- proposer un candidat sans objet ;
- proposer un candidat sans lemme ;
- proposer un candidat sans réfutation ;
- recycler une voie fermée ;
- laisser l’autonomie dépasser ses checkpoints ;
- appeler “percée” un simple cadre théorique.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **X/I/P**
- **X** pour investigation et contrôle des angles morts ;
- **I** pour innovation disciplinée ;
- **P** pour preuve, vérification, audit et falsifiabilité.

## 2. IVS — Information Value Score
Noter /10 selon :
- précision du type de lemme visé ;
- qualité des candidats ;
- robustesse anti-redondance ;
- qualité du pipeline autonome ;
- honnêteté de la décision finale.

## 3. Ladder of Proof
Pour chaque candidat, préciser :
- intuition ;
- objet ;
- semi-formalisation ;
- lemme candidat ;
- tentative de preuve ;
- test de réfutation ;
- statut final.

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour tout candidat éliminé, fournir :
- Nom ;
- Type de mort :
  - redondant,
  - trop faible,
  - trop haut,
  - trop vague,
  - réfutation absente,
  - bloqué en preuve,
  - élégance trompeuse ;
- Cause du rejet ;
- Ce que la mort enseigne ;
- Où cela redirige.

## 5. REGISTRE FAIL-CLOSED
Tu dois terminer par un tableau strict :
- [QUALIFIÉ]
- [QUALIFIÉ AVEC RÉSERVE]
- [ÉLIMINÉ]
- [OBJET RÉEL]
- [SEMI-RÉEL]
- [REDONDANT]
- [SEMI-FORMALISÉ]
- [PARTIELLEMENT PROUVÉ]
- [HEURISTIQUE]
- [PROSE]
- [RÉFUTÉ]
- [BLOQUÉ]
- [À REFORMULER]
- [DIAGNOSTIC INSUFFISANT]

---

# CRITÈRES DE RÉUSSITE
PASS-1 : le type de lemme utile est formulé proprement.
PASS-2 : au plus 4 candidats entrent dans le pipeline autonome.
PASS-3 : chaque candidat a un objet, un lemme, une réfutation et un critère de victoire.
PASS-4 : le pipeline autonome produit un tri réel et non rhétorique.
PASS-5 : un survivant unique pour R84 est sélectionné, ou l’innovation est suspendue proprement.
PASS-6 : le statut de preuve du survivant est honnêtement évalué.

# ÉCHEC UTILE
Même en cas d’échec, R83 est utile si :
- il montre jusqu’où l’autonomie plus profonde peut aller sans se perdre ;
- il évite une fausse percée ;
- il clarifie quel type de lemme manque encore ;
- il remplace une exploration diffuse par un survivant clairement justifié — ou une suspension honnête.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (type de lemme utile)
5. Résultats PHASE 1 / AXE B (anti-résurrection)
6. Résultats PHASE 2 / AXE C (candidats entrants)
7. Résultats PHASE 2 / AXE D (protocole agentique)
8. Journal des sous-rounds autonomes S1→S5
9. Résultats PHASE 4 / AXE E (audit fail-closed)
10. Résultats PHASE 4 / AXE F (classement et impact)
11. Résultats PHASE 5 / AXE G (décision finale)
12. Objets concernés + Ladder of Proof
13. Ce qui est appris
14. Ce qui est fermé utilement
15. Ce qui est enterré
16. Autopsie des pistes fermées
17. Survivant pour R84
18. Risques / limites
19. Verdict final avec score /10
20. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R83 doit aller plus loin en autonomie, mais pas plus loin hors méthode.

Le but est de tester jusqu’où Claude Code peut aller pour faire émerger un vrai candidat de lemme mordant.

Chercher peu de candidats, les pousser plus loin, les faire auditer durement, et n’en garder qu’un seul — ou aucun.
Pas une promesse de percée. Un survivant qui a gagné le droit d’exister.
