

TYPE: P/T
OBJET CIBLÉ: formuler le front k≥3 de manière structurelle, non computationnelle, sans traitement k par k, et identifier le premier verrou analytique général réellement attaquable après la doctrine stabilisée en R70
QUESTION CENTRALE: quelle formulation générale, uniforme et non calculatoire de corrSum / T(t) pour k≥3 permet de poser le vrai obstacle analytique sans retomber dans les réflexes k=2, les scans par cas, ni les preuves proxy ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: remplacer toute tentation de progression computationnelle ou k-par-k par une carte analytique générale du front k≥3, avec un verrou principal unique et une première stratégie de preuve réellement adaptée à cette géométrie.
PRINCIPE D’ÉQUILIBRE: interdire la dérive calculatoire et les traitements fragmentés, tout en laissant une liberté contrôlée pour proposer une reformulation structurelle, un invariant pertinent, ou une factorisation logique nouvelle si elle est explicitement motivée par le mur analytique rencontré.

# BRIEF CLAUDE CODE — ROUND 71 (R71)

## Mission
Tu poursuis le projet Collatz après R70.

R71 doit ouvrir le front **k≥3** de façon **générale, analytique et structurelle**.

Le but n’est pas d’attaquer successivement k=3, puis k=4, puis k=5, etc.
Le but n’est pas non plus de compenser un manque de structure par du calcul, du Monte Carlo, du scan de petites valeurs, ou du catalogage de cas.

**R71 doit refuser explicitement toute dérive computationnelle ou k-par-k.**

Le round doit produire un cadrage mathématique général du nouvel objet, identifier son vrai verrou analytique, et proposer la première stratégie raisonnable d’attaque qui respecte la doctrine cible / stratégie / outil / laboratoire établie en R70.

---

## Contexte acquis après R70
- La cible logique du programme n’est pas une borne globale de type K-lite en soi, mais une condition ponctuelle finale reliée au Junction Theorem.
- K-lite, l’équidistribution, les outils de type Erdős–Turán et certaines réécritures restent des **stratégies/outils possibles**, pas la cible logique minimale.
- Le cas k=2 a été reclassé comme **laboratoire mathématique**, utile pour extraire des idées, des schémas, des outils ou des alertes, mais non comme front principal.
- R70 a préparé le passage à **k≥3** en identifiant que la structure change : on quitte une factorisation de type 2^a c_δ pour entrer dans un objet de type corrSum / somme de Horner monotone / somme exponentielle non factorisable de façon évidente.
- Le danger principal maintenant est double :
  1. retomber dans une mentalité de traitement local, computationnel, ou k-par-k ;
  2. recycler à tort des outils de k=2 comme s’ils se transféraient automatiquement.
- Le bon front de R71 est donc : **poser le problème général k≥3 correctement**.

---

# OBJECTIF DE R71
R71 doit répondre à cette question centrale :

> Quelle est la formulation analytique générale la plus propre du front k≥3, quel est son verrou principal, et quelle stratégie générale — non computationnelle, non k-par-k — mérite rationnellement de devenir le front suivant ?

Les sorties acceptables du round sont :
1. **Objet k≥3 formulé proprement + verrou analytique principal identifié + stratégie générale candidate** ;
2. **Objet k≥3 formulé proprement + plusieurs stratégies possibles, mais un survivant unique sélectionné** ;
3. **Objet k≥3 encore insuffisamment typé, avec obstacle de formulation précisément localisé** ;
4. **Transition k≥3 encore prématurée tant qu’un point doctrinal ou structurel non résolu subsiste**.

Important :
- aucune sortie n’est recevable si elle repose sur un traitement par petites valeurs de k ;
- aucune sortie n’est recevable si elle remplace une difficulté analytique par un protocole computationnel ;
- aucune stratégie n’est recevable si elle ne dit pas clairement pourquoi elle est générale et non locale.

---

# ARCHITECTURE GÉNÉRALE

## PHASE 1 — FORMULATION GÉNÉRALE DU FRONT k≥3
Objectif : définir l’objet général à étudier sans tomber dans le k-par-k.

## PHASE 2 — IDENTIFICATION DU VERROU ANALYTIQUE CENTRAL
Objectif : déterminer où se trouve la vraie difficulté structurelle.

## PHASE 3 — SÉLECTION D’UNE STRATÉGIE GÉNÉRALE
Objectif : choisir une unique stratégie de preuve ou de réduction qui respecte la nature générale du problème.

## Ce qui est interdit comme cible principale
- traitements séparés pour k=3, k=4, k=5, etc. ;
- expérimentation computationnelle large ;
- Monte Carlo ;
- cartographie numérique comme substitut à une formulation analytique ;
- retour déguisé à k=2 comme cible effective ;
- accumulation de micro-cas sans invariant commun.

---

# PHASE 1 — FORMULATION GÉNÉRALE DU FRONT k≥3

## AXE A — INVESTIGATEUR / DÉFINITION CANONIQUE DE L’OBJET
### Nom de travail
Quel est l’objet général, indépendamment de k pris un par un ?

### Mission
Écrire une formulation générale de corrSum / T(t) / somme de Horner monotone / contrainte de composition pour **k≥3**, en mettant l’accent sur les paramètres structurels et non sur des instances particulières.

### Questions obligatoires
1. Quel est l’objet canonique à étudier pour tout k≥3 dans une même écriture ?
2. Quels sont ses paramètres naturels ?
3. Quelle partie de la géométrie de l’objet dépend de k comme paramètre global, et quelle partie dépend seulement de la structure des compositions ?
4. Quelle représentation de l’objet est la plus informative : somme, polynôme, opérateur, arbre, support, autre ?
5. Quelle écriture rend visibles les collisions, les annulations possibles, la monotonie, ou la rigidité de structure ?
6. Quelle formulation évite explicitement la tentation de traiter k valeur par valeur ?

### Livrables
- définition canonique générale de l’objet k≥3 ;
- liste minimale des paramètres structurels ;
- représentation préférée avec justification ;
- paragraphe expliquant pourquoi cette formulation est générale et non k-par-k.

---

## AXE B — INVESTIGATEUR / DIFFÉRENCE STRUCTURELLE AVEC LE LABORATOIRE k=2
### Nom de travail
Qu’est-ce qui casse vraiment quand on quitte k=2 ?

### Mission
Identifier de façon conceptuelle ce qui faisait la relative tractabilité de k=2 et ce qui disparaît ou se déforme à partir de k≥3.

### Questions obligatoires
1. Quelle était la propriété structurante clé de k=2 ?
2. Cette propriété disparaît-elle, se généralise-t-elle, ou explose-t-elle en combinatoire pour k≥3 ?
3. Le nouvel objet est-il mieux vu comme une somme exponentielle, une corrélation, une famille de phases, une contrainte de support, ou autre chose ?
4. Quel est le premier énoncé naïf hérité de k=2 qu’il faut explicitement interdire sur k≥3 ?
5. Quelle leçon du laboratoire k=2 reste valable sans transfert abusif ?

### Livrables
- tableau “héritage utile / héritage interdit” depuis k=2 ;
- énoncé du premier faux réflexe à bannir ;
- reformulation claire du nouveau paysage structurel.

---

# PHASE 2 — IDENTIFICATION DU VERROU ANALYTIQUE CENTRAL

## AXE C — INVESTIGATEUR / LOCALISATION DU VRAI MUR
### Nom de travail
Où est la difficulté essentielle, une fois le décor computationnel interdit ?

### Mission
Distinguer les difficultés secondaires des difficultés centrales, afin d’isoler un verrou principal unique.

### Questions obligatoires
1. Le vrai mur vient-il de la non-factorisation, de la multiplicité des phases, de la géométrie du support, de collisions arithmétiques, d’un manque d’équidistribution, ou d’autre chose ?
2. Quel est le plus petit énoncé général qui, s’il était prouvé, ferait réellement avancer le front k≥3 ?
3. Quel énoncé paraît séduisant mais serait encore un proxy trop faible ou mal ciblé ?
4. Quelle difficulté semble technique mais n’est peut-être qu’un symptôme d’une mauvaise formulation ?
5. Peut-on condenser le problème en un verrou principal formulé en une ou deux phrases ?

### Livrables
- hiérarchie des obstacles ;
- verrou principal unique ;
- un anti-verrou : le faux problème qu’il ne faut pas prendre pour le vrai.

---

## AXE D — INVESTIGATEUR / ÉNONCÉ PIVOT GÉNÉRAL
### Nom de travail
Quel serait le premier vrai lemme qui compte ?

### Mission
Formuler un premier lemme pivot ou un premier énoncé de réduction qui soit :
- général ;
- non computationnel ;
- non k-par-k ;
- vraiment pertinent pour la cible future.

### Questions obligatoires
1. Quel est le premier énoncé général honnête qu’on voudrait établir ?
2. En quoi cet énoncé est-il supérieur à un simple test local ou numérique ?
3. Est-il un lemme de non-annulation, une borne de corrélation, une rigidité de support, une réduction à une classe de phases, ou autre chose ?
4. Quels seraient ses prérequis théoriques ?
5. Quel est le risque qu’il soit encore mal ciblé ?

### Livrables
- énoncé pivot candidat ;
- rôle logique visé ;
- dépendances et risques ;
- statut : [CANDIDAT SÉRIEUX] / [TROP FAIBLE] / [TROP FLOU] / [MAL CIBLÉ].

---

# PHASE 3 — SÉLECTION D’UNE STRATÉGIE GÉNÉRALE

## AXE E — INVESTIGATEUR / TABLE DES STRATÉGIES POSSIBLES
### Nom de travail
Par quelle porte générale entrer ?

### Mission
Évaluer plusieurs familles de stratégies possibles pour le front k≥3, mais sans les laisser se multiplier sans contrôle.

### Stratégies possibles à examiner, sans obligation de s’y limiter
- stratégie de **non-annulation structurale** ;
- stratégie de **corrélation / somme exponentielle générale** ;
- stratégie de **rigidité combinatoire des compositions** ;
- stratégie de **dilution géométrique / dispersion** ;
- stratégie de **réduction vers un invariant intermédiaire nouveau**.

### Questions obligatoires
1. Quelle stratégie parle le plus directement au verrou principal ?
2. Quelle stratégie n’est qu’un recyclage de k=2 sous un nouveau nom ?
3. Quelle stratégie semble générale mais se casse en réalité dès qu’on refuse le k-par-k ?
4. Quelle stratégie a la meilleure combinaison : pertinence / généricité / démontrabilité ?
5. Quel unique survivant doit être choisi pour la suite ?

### Livrables
Pour chaque stratégie candidate :
- formulation ;
- cible réelle ;
- force ;
- faiblesse ;
- risque de dérive computationnelle ;
- statut : [SURVIVANT] / [SECONDAIRE] / [À ÉCARTER].

---

## AXE F — INNOVATEUR / REFORMULATION STRUCTURELLE MINIMALE
### Nom de travail
Nommer le bon objet avant de vouloir le dompter

### Mission
Si le verrou principal révèle que la formulation actuelle reste trop proche d’un mauvais langage hérité de k=2, l’innovateur peut proposer **au plus une** reformulation structurelle minimale.

### Règles strictes
- cette reformulation doit être générale en k ;
- elle ne doit pas être une collection de cas ;
- elle doit améliorer la lisibilité du verrou ou la plausibilité d’un lemme pivot ;
- elle ne doit pas remplacer l’analyse par une taxonomie computationnelle ;
- elle doit dire explicitement ce qu’elle gagne et ce qu’elle risque.

### Livrables
Pour cette unique reformulation éventuelle :
1. énoncé intuitif ;
2. version semi-formelle ;
3. obstacle qu’elle rend plus lisible ;
4. ce qu’elle conserve de la doctrine R70 ;
5. risque de dérive ;
6. niveau estimé dans la Ladder of Proof.

---

# AUTONOMIE CONTRÔLÉE (TRÈS LIMITÉE)

## Activation
Une mini-autonomie n’est autorisée qu’en PHASE 3, jamais en PHASE 1 ni en PHASE 2.

## Budget maximal
Au plus **2 sous-rounds internes** :
- **S1** : comparaison finale de 2 ou 3 stratégies générales ;
- **S2** : choix du survivant + verrou pivot.

## Événements STOP obligatoires
Arrêt immédiat si :
1. la réflexion dérive vers un traitement k-par-k ;
2. un recours computationnel devient central ;
3. plus d’une reformulation innovante devient nécessaire ;
4. aucun verrou principal unique n’émerge ;
5. une stratégie candidate n’est défendable qu’à travers de petites valeurs de k.

## Format obligatoire de chaque sous-round autonome
1. hypothèse active ;
2. objet général manipulé ;
3. question ;
4. démarche ;
5. résultat net ;
6. statut ;
7. ce qui est appris ;
8. décision : continuer / arrêter ;
9. raison explicite de l’arrêt ou de la poursuite.

## Interdictions
- pas de campagne numérique ;
- pas de Monte Carlo ;
- pas de table k=3..n ;
- pas de preuve “par accumulation de cas” ;
- pas de régression vers une cible locale.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **P/T**
- **P** pour formulation / preuve structurelle ;
- **T** pour préparation d’un nouveau front général.

## 2. IVS — Information Value Score
Noter /10 selon :
- qualité de la formulation générale ;
- netteté du verrou principal ;
- capacité à éviter la dérive computationnelle ;
- valeur du lemme pivot proposé ;
- solidité du survivant stratégique.

Une bonne note IVS peut venir d’un verrou très bien formulé, même sans avancée technique immédiate.

## 3. Ladder of Proof
Pour chaque objet principal touché, préciser :
- intuition ;
- observation ;
- observation répétée ;
- calcul exact ;
- semi-formalisation ;
- schéma de preuve ;
- lemme candidat ;
- lemme prouvé ;
- résultat publiable.

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute piste écartée, fournir :
- Nom ;
- Type de mort :
  - dérive computationnelle,
  - k-par-k déguisé,
  - proxy trop faible,
  - transfert abusif depuis k=2,
  - mauvais invariant,
  - formulation trop floue,
  - stratégie non générale ;
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

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- cible logique ;
- verrou analytique ;
- lemme pivot ;
- stratégie générale ;
- outil auxiliaire ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni calculer pour masquer l’absence de structure ;
- ni découper le problème en petites valeurs de k ;
- ni recycler un succès de laboratoire comme s’il était une stratégie générale démontrée ;
- ni transformer une intuition géométrique en théorème sans passer par un lemme pivot clair.

Tu ne dois pas :
- proposer de traitement k=3, puis k=4, etc. ;
- utiliser des expériences numériques comme colonne vertébrale du round ;
- appeler “général” une méthode qui ne survit qu’à de petites valeurs ;
- multiplier les stratégies sans choisir un survivant ;
- laisser l’autonomie dépasser son budget ou ses STOP.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : l’objet k≥3 est formulé de façon générale, sans k-par-k.
PASS-2 : la différence structurale avec k=2 est clarifiée proprement.
PASS-3 : un verrou analytique principal unique est identifié.
PASS-4 : un lemme pivot général est formulé avec une portée honnête.
PASS-5 : une stratégie générale survivante est sélectionnée.
PASS-6 : toute dérive computationnelle est explicitement bannie ou enterrée.
PASS-7 : l’autonomie éventuelle reste très courte et ne sert qu’à trancher entre stratégies générales.

# ÉCHEC UTILE
Même en cas d’échec, R71 est utile si :
- une mauvaise formulation générale est éliminée ;
- un faux verrou est enterré ;
- une dérive computationnelle est évitée ;
- le prochain round est mieux posé analytiquement qu’avant.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (objet canonique k≥3)
5. Résultats PHASE 1 / AXE B (rupture structurelle avec k=2)
6. Résultats PHASE 2 / AXE C (verrou analytique principal)
7. Résultats PHASE 2 / AXE D (lemme pivot général)
8. Résultats PHASE 3 / AXE E (table des stratégies générales)
9. Résultats PHASE 3 / AXE F (reformulation structurelle éventuelle)
10. Activation ou non de l’autonomie, avec justification
11. Journal des sous-rounds autonomes éventuels
12. Objets concernés + Ladder of Proof
13. Ce qui est appris
14. Ce qui est fermé utilement
15. Ce qui est enterré
16. Autopsie des pistes fermées
17. Survivant pour R72
18. Risques / limites
19. Verdict final avec score /10
20. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R71 doit refuser les béquilles computationnelles et les progressions k-par-k.

Le but est de formuler le front k≥3 à la bonne altitude mathématique :
assez générale pour être fidèle au vrai problème,
assez précise pour faire émerger un verrou principal,
et assez disciplinée pour choisir une stratégie unique sans retomber dans la poussière des cas locaux.

Chercher le bon objet, le bon mur, et la bonne porte.
Pas une galerie d’exemples. Une architecture analytique générale.