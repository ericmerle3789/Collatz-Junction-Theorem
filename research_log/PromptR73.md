

TYPE: P/T
OBJET CIBLÉ: tester de façon rigoureuse si le sous-problème bilinéaire court extrait en R72 admet une borne non triviale réellement exploitable dans le régime logarithmique, sans galerie de littérature, sans computationnel, sans k-par-k, et sans rebranding d’anciennes routes mortes
QUESTION CENTRALE: dans le régime de longueur O(log p) issu de la reformulation SOH, existe-t-il une borne non triviale honnête sur les sommes courtes pondérées/emboîtées sur <2> qui constitue une vraie prise analytique, ou faut-il reconnaître que cette voie ne mord pas encore ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: obtenir un verdict propre sur le mordant réel de la voie bilinéaire courte — soit une borne candidate crédible avec chaîne logique explicite, soit un diagnostic argumenté montrant qu’aucun gain exploitable n’apparaît à ce stade.
PRINCIPE D’ÉQUILIBRE: imposer une discipline extrême contre la dérive computationnelle, la galerie de noms, le k-par-k et la résurrection de routes déjà fermées, tout en autorisant une réduction minimale si elle simplifie réellement le sous-problème sans en changer la nature.

# BRIEF CLAUDE CODE — ROUND 73 (R73)

## Mission
Tu poursuis le projet Collatz après R72.

R73 doit tester une seule chose :
**la voie bilinéaire courte issue de R72 permet-elle une borne non triviale réellement exploitable, ou n’est-elle encore qu’une zone de contact sans prise ?**

Le round ne doit pas devenir :
- une galerie de littérature sur Bourgain / Korobov / Konyagin / Shkredov / etc.,
- une comparaison superficielle d’outils célèbres,
- une relance computationnelle,
- un traitement k=3 puis k=4 puis k=5,
- ni une tentative de sauver la voie parce qu’elle est élégante.

Le round doit produire un verdict de mordant analytique sur le **régime logarithmique court** réellement issu du projet.

---

## Contexte acquis après R72
- R71 a correctement formulé le front k≥3 via la SOH, mais sa piste “opérateur / spectral / Toeplitz” a été jugée trop décorative.
- R72 a montré que la voie opérateur ne fournit pas encore de mécanisme réel de spectral gap ou de décorrélation démontrable.
- R72 a sauvé l’objet SOH mais a reformulé le premier test sérieux en un sous-problème de **cancellation bilinéaire / somme double courte sur <2>**.
- Le nouveau point de contact est une famille de sommes courtes pondérées/emboîtées de type :
  - sommes simples courtes sur <2>,
  - ou sommes doubles / bilinéaires obtenues après Cauchy–Schwarz,
  - dans une longueur de l’ordre O(log p).
- L’audit de R72 conclut :
  - la prise est **structurelle réelle**,
  - mais la prise **analytique** reste à démontrer.
- R73 doit donc décider si, dans ce régime court et spécifique, il existe ou non un vrai gain analytique exploitable.

---

# OBJECTIF DE R73
R73 doit répondre à cette question centrale :

> Dans le régime logarithmique court issu de la reformulation bilinéaire de R72, existe-t-il une borne non triviale honnête, générale et exploitable, ou faut-il reconnaître que cette voie ne fournit pas encore de gain suffisant ?

Les sorties acceptables du round sont :
1. **Une borne non triviale crédible est identifiée, avec chaîne logique explicite jusqu’au verrou visé** ;
2. **Une borne partielle ou trop faible est identifiée : prise analytique réelle mais insuffisante à ce stade** ;
3. **Aucune borne exploitable n’émerge dans le régime court : la voie bilinéaire doit être abaissée ou reformulée** ;
4. **Le sous-problème lui-même était mal calibré : reformulation minimale nécessaire avant tout round ultérieur**.

Important :
- aucune sortie n’est recevable sans distinguer clairement “borne non triviale”, “borne structurellement intéressante”, et “borne réellement exploitable pour le programme” ;
- aucune sortie n’est recevable si elle repose sur une littérature citée sans adaptation au régime exact O(log p) du projet ;
- aucune sortie n’est recevable si elle remplace un argument par une accumulation de noms, d’analogies ou de résultats hors-régime.

---

# ARCHITECTURE GÉNÉRALE

## PHASE 1 — FIXER LE SOUS-PROBLÈME EXACT
Objectif : définir sans ambiguïté la famille exacte de sommes courtes à étudier et le type précis de gain recherché.

## PHASE 2 — TESTER LE MORDANT DES BORNES NON TRIVIALES
Objectif : déterminer s’il existe un gain analytique réel dans le régime court O(log p), et de quel type.

## PHASE 3 — CONTRÔLE ANTI-BOUCLE ET DÉCISION
Objectif : vérifier qu’on ne repackage pas une ancienne impasse, puis décider honnêtement du statut de la voie bilinéaire.

## Ce qui est interdit comme cible principale
- littérature panoramique sans test sur le régime exact ;
- réactivation brute de Weil / Weyl / Large Sieve / Erdős–Turán / moments seuls / discrepancy seule / nesting seul ;
- calcul / Monte Carlo / petits k ;
- toute “preuve” par accumulation de cas ;
- toute inflation du vocabulaire spectral ;
- tout changement d’objet sans déclaration explicite.

---

# PHASE 1 — FIXER LE SOUS-PROBLÈME EXACT

## AXE A — INVESTIGATEUR / DÉFINITION PRÉCISE DU RÉGIME COURT
### Nom de travail
Quel est exactement l’objet à borner ?

### Mission
Figer proprement la famille exacte de sommes courtes issue de R72, avec ses poids, sa longueur, son domaine, et le type exact de gain recherché.

### Questions obligatoires
1. Quelle est la forme exacte des sommes simples / doubles / bilinéaires concernées ?
2. Quel est le rôle des poids et des dépendances en δ ?
3. Quelle est la longueur exacte pertinente : O(log p), S, ou autre ?
4. Quelle est la taille triviale de référence ?
5. Quel type de gain serait déjà non trivial ?
6. Quel type de gain serait vraiment exploitable pour la chaîne logique du projet ?

### Livrables
- définition canonique de l’objet court ;
- borne triviale de référence ;
- graduation explicite :
  - gain non trivial faible,
  - gain structurel intéressant,
  - gain exploitable pour le programme.

---

## AXE B — INVESTIGATEUR / CHAÎNE LOGIQUE VERS LE VERROU
### Nom de travail
À quoi servirait réellement une borne ?

### Mission
Relier explicitement le type de borne envisagé à la chaîne logique du programme, sans surestimer sa portée.

### Questions obligatoires
1. Si l’on obtient un petit gain sur la somme courte, qu’est-ce que cela donne réellement ?
2. Quel niveau de gain faudrait-il pour commencer à peser sur le verrou analytique principal ?
3. Quelle perte introduisent Cauchy–Schwarz, les couches δ, les poids, ou les réductions intermédiaires ?
4. Y a-t-il un seuil naturel entre “jolie borne” et “borne qui compte” ?
5. Si aucune borne assez forte n’est réaliste, faut-il conclure contre la voie ou contre le calibrage du sous-problème ?

### Livrables
- chaîne logique explicite ;
- tableau “niveau de gain / conséquence réelle” ;
- verdict provisoire sur le niveau minimal utile.

---

# PHASE 2 — TESTER LE MORDANT DES BORNES NON TRIVIALES

## AXE C — INVESTIGATEUR / QUELLES BORNES SURVIVENT AU RÉGIME O(log p) ?
### Nom de travail
Quel outil survit quand la somme est vraiment courte ?

### Mission
Examiner uniquement les familles d’arguments qui peuvent raisonnablement produire un gain dans le régime logarithmique court, en les testant contre l’objet exact de PHASE 1.

### Questions obligatoires
1. Les outils “classiques” produisent-ils ici autre chose qu’une borne triviale ou quasi triviale ?
2. Existe-t-il une famille d’arguments adaptée aux sous-groupes multiplicatifs courts / sommes pondérées courtes / phases emboîtées ?
3. Le gain potentiel vient-il de la structure du support, des poids, de la phase, ou d’une interaction spécifique entre eux ?
4. Quel premier estimateur non trivial peut-on écrire sans mentir sur sa portée ?
5. Ce gain est-il seulement formel, ou numériquement/logiquement significatif dans la chaîne du projet ?

### Livrables
- tableau des familles d’arguments testées ;
- pour chacune :
  - statut dans le régime O(log p),
  - type de gain possible,
  - limite de portée ;
- meilleure borne candidate honnête obtenue à ce stade.

---

## AXE D — INVESTIGATEUR / TEST DE PREUVE OU TEST D’IMPOSSIBILITÉ ?
### Nom de travail
La voie mord-elle, oui ou non ?

### Mission
Décider si l’état actuel permet :
- un début de preuve sur le sous-problème,
- seulement une borne trop faible,
- ou au contraire un diagnostic argumenté d’insuffisance de la voie.

### Questions obligatoires
1. Dispose-t-on d’un estimateur avec une chaîne de justification suffisamment nette ?
2. Cet estimateur produit-il un vrai gain au bon endroit ?
3. Si le gain est trop faible, est-ce accidentel ou structurel ?
4. Y a-t-il un obstacle intrinsèque au régime O(log p) qui tue l’approche bilinéaire ?
5. À ce stade, la voie doit-elle être poursuivie, abaissée, ou reformulée ?

### Livrables
- verdict de mordant : [MORD] / [MORD FAIBLEMENT] / [NE MORD PAS ENCORE] ;
- justification précise ;
- obstacle principal si la voie échoue.

---

# PHASE 3 — CONTRÔLE ANTI-BOUCLE ET DÉCISION

## AXE E — INVESTIGATEUR / CONTRÔLE ANTI-RÉINVENTION STRICT
### Nom de travail
Nouvelle prise ou vieille impasse renommée ?

### Mission
Comparer la meilleure borne candidate / la meilleure obstruction à l’historique du projet avant R60 et au RESEARCH_MAP, pour éviter tout faux progrès par rebranding.

### Questions obligatoires
1. Quelle différence réelle sépare l’argument retenu des anciennes routes mortes ?
2. Ce qui est nouveau tient-il dans l’objet, dans le régime, dans l’estimateur, ou seulement dans le langage ?
3. Y a-t-il un risque qu’on reconstitue une impasse “moments seuls” ou “ET/LS/Weil hors-régime” sous un autre nom ?
4. Quelle condition explicite garantit qu’un R74 n’entrera pas dans une boucle ?
5. Le round améliore-t-il vraiment le ciblage du verrou, ou seulement sa narration ?

### Livrables
- tableau “ancienne route / différence réelle / risque de boucle” ;
- verdict : [NOUVEAUTÉ RÉELLE] / [NOUVEAUTÉ PARTIELLE] / [REBRANDING RISQUÉ].

---

## AXE F — DÉCISION STRATÉGIQUE FINALE
### Nom de travail
Continue-t-on cette voie ?

### Mission
Décider honnêtement si la voie bilinéaire courte doit être :
- poursuivie,
- reformulée,
- ou déclassée.

### Options possibles
- **Poursuivre** : si une borne non triviale crédible et reliée au verrou est réellement identifiée.
- **Poursuivre avec réserve** : si la prise existe mais reste trop faible.
- **Reformuler** : si le sous-problème reste bon mais l’habillage analytique est mal calibré.
- **Déclasser** : si la voie ne produit aucun gain exploitable dans le régime exact du projet.

### Questions obligatoires
1. Quel est le meilleur acquis réel du round ?
2. Quelle est sa portée honnête ?
3. Quel est le principal obstacle restant ?
4. Le prochain round peut-il être formulé sans boucle ?
5. Quel unique survivant pour R74 doit être choisi ?

### Livrables
- décision stratégique ;
- justification ;
- survivant unique pour R74 ;
- condition explicite de non-boucle pour le prochain round.

---

## AXE G — INNOVATEUR / REFORMULATION MINIMALE SI ET SEULEMENT SI NÉCESSAIRE
### Nom de travail
Réduire encore, pas décorer

### Mission
Seulement si la décision finale est “Reformuler”, proposer au plus une reformulation minimale du sous-problème court ou du type de borne recherchée.

### Règles strictes
- la reformulation doit réduire le problème ;
- elle doit rester générale en k ;
- elle doit supprimer une ambiguïté réelle ;
- elle ne doit pas introduire de nouvelle grande théorie décorative ;
- elle ne doit pas rouvrir une route morte sous un autre nom.

### Livrables
Pour cette unique reformulation éventuelle :
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’elle simplifie réellement ;
4. ce qu’elle risque ;
5. pourquoi elle n’est pas un simple renommage.

---

# AGENTS ET RÔLES

## Investigateur principal
- fige l’objet exact ;
- mesure la portée réelle des bornes ;
- détruit les glissements de statut ;
- contrôle l’anti-boucle.

## Investigateur historique
- compare explicitement aux routes déjà fermées ;
- empêche le rebranding ;
- extrait les différences réelles avec l’historique.

## Innovateur minimal
- n’intervient qu’en cas de besoin ;
- réduit le sous-problème ou la formulation ;
- n’a pas le droit d’ajouter du décor.

## Auditeur fail-closed
- vérifie que chaque claim est correctement typé ;
- exige une distinction nette entre :
  - borne triviale,
  - borne non triviale,
  - borne exploitable,
  - heuristique,
  - conjectural.

---

# AUTONOMIE CONTRÔLÉE (TRÈS COURTE)

## Activation
Une mini-autonomie est autorisée seulement en PHASE 3 pour trancher entre 2 issues proches, jamais pour explorer librement.

## Budget maximal
Au plus **2 sous-rounds internes** :
- **S1** : comparaison finale de 2 calibrages du sous-problème ou de la borne ;
- **S2** : décision stratégique finale.

## Événements STOP obligatoires
Arrêt immédiat si :
1. la réflexion dérive vers une galerie de littérature ;
2. la réflexion dérive vers du computationnel ou du k-par-k ;
3. aucune borne précise n’est formulée ;
4. la nouveauté est surtout lexicale ;
5. plus d’une reformulation minimale devient nécessaire.

## Format obligatoire de chaque sous-round autonome
1. hypothèse active ;
2. objet exact ;
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
- pas de table par k ;
- pas de grande théorie ajoutée sans estimateur concret ;
- pas de relance des routes fermées comme cible principale.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **P/T**
- **P** pour test de prise analytique ;
- **T** pour décision de transition ou déclassement.

## 2. IVS — Information Value Score
Noter /10 selon :
- précision de l’objet court ;
- réalité du gain non trivial ;
- qualité du contrôle anti-boucle ;
- honnêteté de la décision stratégique ;
- réduction du flou entre “borne jolie” et “borne utile”.

Une bonne note IVS peut venir d’un déclassement propre si celui-ci évite une longue impasse analytique.

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
  - borne hors-régime,
  - joli gain sans utilité,
  - rebranding d’une route morte,
  - galerie de littérature,
  - dérive computationnelle,
  - sous-problème mal calibré,
  - heuristique prise pour méthode ;
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
- objet court exact ;
- borne triviale ;
- borne non triviale ;
- borne exploitable ;
- obstacle structurel ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni noyer le problème dans les noms ;
- ni survendre un gain trop faible ;
- ni enterrer trop vite une voie qui donne un début de prise ;
- ni poursuivre une voie qui ne produit qu’un contact esthétique.

Tu ne dois pas :
- citer des outils sans les tester sur le régime exact O(log p) ;
- appeler “prise analytique” une simple réduction ;
- proposer un R74 sans condition de non-boucle ;
- laisser l’autonomie dépasser ses STOP ou son budget.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : l’objet court exact et le type de gain recherché sont figés proprement.
PASS-2 : la chaîne logique entre niveau de gain et conséquence réelle est explicitée.
PASS-3 : au moins une borne candidate est évaluée honnêtement dans le régime O(log p).
PASS-4 : le contrôle anti-boucle distingue clairement nouveauté réelle et rebranding.
PASS-5 : une décision stratégique honnête est prise sur la voie bilinéaire courte.
PASS-6 : un unique survivant pour R74 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R73 est utile si :
- une borne “jolie mais inutile” est déclassée proprement ;
- une fausse nouveauté est reconnue avant de boucler ;
- le calibrage du sous-problème est amélioré ;
- le projet évite une impasse analytique coûteuse.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (objet court exact)
5. Résultats PHASE 1 / AXE B (chaîne logique niveau de gain → conséquence)
6. Résultats PHASE 2 / AXE C (familles de bornes testées)
7. Résultats PHASE 2 / AXE D (verdict de mordant)
8. Résultats PHASE 3 / AXE E (contrôle anti-réinvention)
9. Résultats PHASE 3 / AXE F (décision stratégique)
10. Résultats PHASE 3 / AXE G (reformulation minimale éventuelle)
11. Activation ou non de l’autonomie, avec justification
12. Journal des sous-rounds autonomes éventuels
13. Objets concernés + Ladder of Proof
14. Ce qui est appris
15. Ce qui est fermé utilement
16. Ce qui est enterré
17. Autopsie des pistes fermées
18. Survivant pour R74
19. Risques / limites
20. Verdict final avec score /10
21. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R73 doit décider si, dans le régime exact O(log p) du projet, il existe une borne non triviale qui compte vraiment.

Le but n’est pas de montrer qu’on sait nommer des outils.
Le but est de savoir si un outil donne un vrai gain au bon endroit, ou si la voie bilinéaire courte doit être abaissée.

Chercher une borne honnête, une portée honnête, et une décision sans complaisance.
Pas une vitrine. Une morsure réelle — ou un verdict d’insuffisance.