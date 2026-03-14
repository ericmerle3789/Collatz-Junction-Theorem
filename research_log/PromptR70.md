

TYPE: P/T
OBJET CIBLÉ: verrouiller canoniquement la lecture du Junction Theorem après R69, figer la distinction cible / outil / laboratoire, puis préparer de façon strictement contrôlée la transition vers le front k≥3
QUESTION CENTRALE: la lecture issue de R69 est-elle suffisamment canonique, traçable et stable pour devenir doctrine de travail, et si oui, comment traduire proprement cette doctrine en plan d’attaque sur corrSum pour k≥3 sans réintroduire les confusions R67–R69 ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: soit produire une doctrine canonique fail-closed sur le rôle exact de N_0(d), de K-lite et du laboratoire k=2, soit localiser précisément ce qui reste ambigu avant toute transition sérieuse vers k≥3.
PRINCIPE D’ÉQUILIBRE: verrouiller fortement les statuts, la cible et les dépendances logiques, tout en autorisant une préparation limitée du front k≥3 si et seulement si la doctrine issue de R69 survit à un audit de robustesse interne.

# BRIEF CLAUDE CODE — ROUND 70 (R70)

## Mission
Tu poursuis le projet Collatz après R69.

R70 a deux tâches hiérarchisées et non interchangeables :
1. **verrouiller doctrinalement ce que R69 affirme vraiment** ;
2. **préparer la transition vers k≥3 uniquement si ce verrouillage tient**.

Tu ne dois pas traiter ces deux tâches comme simultanées.
La préparation k≥3 n’est autorisée qu’après validation explicite de la doctrine issue de R69.

---

## Contexte acquis après audit de R69
- R69 propose un recadrage majeur : le Junction Theorem demanderait avant tout une condition ponctuelle de type **N_0(d)=0**, et non une borne globale de type **max_r N_r**.
- R69 soutient qu’à résidu **r=0**, la distinction entre **N_0^true** et **N_0^ind** devient sans effet pour le test binaire de nullité, car 2^a est inversible modulo p impair.
- R69 requalifie alors K-lite comme **outil auxiliaire**, non comme cible logique minimale du théorème.
- L’audit de R69 valide le cœur de cette distinction, mais refuse de traiter le bilan comme “définitif” sans verrouillage canonique supplémentaire.
- Les points à verrouiller sont donc :
  - la portée exacte de “JT requiert N_0(d)=0” ;
  - le statut exact de l’équivalence à r=0 entre compteurs ;
  - la bonne formule doctrinale : **cible / outil / laboratoire** ;
  - la place exacte du cas k=2 comme laboratoire et non comme cible finale.
- Le front k≥3 devient probablement le front principal, mais la transition ne doit pas réintroduire :
  - confusion de modèle,
  - confusion de compteur,
  - confusion entre propriété visée et outil technique.

---

# OBJECTIF DE R70
R70 doit répondre à cette double question, dans cet ordre :

> (A) La lecture issue de R69 peut-elle être figée en doctrine canonique de travail, sans sur-assertion ni angle mort logique ?
> (B) Si oui, quelle est la formulation minimale, propre et auditée du prochain front k≥3 ?

Les sorties acceptables du round sont :
1. **Doctrine R69 validée et transition k≥3 prête** ;
2. **Doctrine R69 validée mais transition k≥3 encore insuffisamment spécifiée** ;
3. **Doctrine R69 validée partiellement, avec points restant à figer avant transition** ;
4. **Doctrine R69 non encore canonique ; transition k≥3 prématurée**.

Important :
- aucune transition k≥3 n’est recevable si la doctrine n’est pas d’abord typée et stabilisée ;
- aucune validation doctrinale n’est recevable si elle repose sur une formulation rhétorique plus forte que les preuves réellement disponibles ;
- aucune nouvelle piste technique n’est recevable si elle ne dit pas explicitement quelle cible logique elle sert.

---

# ARCHITECTURE GÉNÉRALE

## PHASE 1 — VERROUILLAGE CANONIQUE DE R69
Objectif : transformer le cœur utile de R69 en doctrine de travail stable, brève, non ambiguë et réutilisable.

## PHASE 2 — TRADUCTION CONTRÔLÉE VERS k≥3
Objectif : définir proprement le front k≥3, ses objets, ses obstacles et ses réemplois possibles, sans lancer encore une campagne lourde.

## Ce qui est interdit comme cible principale
- relancer des preuves globales sur K-lite comme si elles redevenaient centrales par défaut ;
- traiter k=2 comme cible finale ;
- annoncer une percée sur k≥3 sans définir corrSum et sa géométrie exacte ;
- réécrire le programme entier sur simple enthousiasme doctrinal ;
- utiliser “définitif”, “sans objet”, “risque nul” sans justification bloc-par-bloc.

---

# PHASE 1 — VERROUILLAGE CANONIQUE DE R69

## AXE A — INVESTIGATEUR / AUDIT DE ROBUSTESSE DE LA DOCTRINE
### Nom de travail
La lecture R69 tient-elle sans gonfler sa portée ?

### Mission
Reprendre les claims centraux de R69 et les classer un par un selon leur vraie portée logique.

### Claims à auditer explicitement
1. **Le Junction Theorem requiert une condition ponctuelle de type N_0(d)=0.**
2. **Pour r=0, N_0^true = 0 si et seulement si N_0^ind = 0.**
3. **K-lite est un outil auxiliaire et non une cible logique minimale du théorème.**
4. **L’obstacle de R68 est neutralisé pour la cible ponctuelle r=0.**
5. **k=2 doit être reclassé comme laboratoire et non comme front principal.**

### Questions obligatoires
1. Quel est l’énoncé exact de chaque claim ?
2. Quelle preuve ou dérivation le soutient exactement ?
3. Quelle est sa portée maximale honnête ?
4. Quel mot ou syntagme de R69 était trop fort et doit être abaissé ?
5. Quel mot ou syntagme peut au contraire être conservé sans risque ?
6. Qu’est-ce qui est vraiment canonique, et qu’est-ce qui reste encore “fortement étayé” sans être complètement figé ?

### Livrables
Pour chaque claim :
- énoncé canonique ;
- statut : [PROUVÉ] / [PARTIELLEMENT PROUVÉ] / [FORTEMENT ÉTAYÉ] / [À REFORMULER] ;
- preuve ou appui exact ;
- limite de portée ;
- version doctrinale autorisée.

---

## AXE B — INVESTIGATEUR / CIBLE, OUTIL, LABORATOIRE
### Nom de travail
Ne plus jamais confondre les étages

### Mission
Figer une doctrine compacte distinguant clairement :
- la **cible logique** du programme ;
- les **outils techniques** utiles mais non requis ;
- les **laboratoires mathématiques** servant d’essai ou de transfert partiel.

### Questions obligatoires
1. Quelle est la cible logique minimale à ce stade ?
2. Quelles techniques restent utiles mais ne doivent plus être présentées comme cibles ?
3. Quelle est la bonne place de k=2 dans l’architecture ?
4. Quelles confusions passées doivent être interdites noir sur blanc dans la doctrine ?
5. Quel est le plus petit document doctrinal que tout round futur devra respecter ?

### Livrables
- un bloc **Doctrine canonique minimale** de 10 à 20 lignes maximum ;
- un tableau à trois colonnes : **cible / outil / laboratoire** ;
- une liste brève de confusions explicitement interdites pour les rounds futurs.

---

## AXE C — INVESTIGATEUR / REQUALIFICATION FINALE DE R62→R69
### Nom de travail
Que reste-t-il exactement de chaque round ?

### Mission
Requalifier proprement la séquence R62 à R69 à la lumière de la doctrine canonique de PHASE 1.

### Questions obligatoires
1. Quels rounds ont produit des résultats techniquement valides ?
2. Lesquels ont parlé d’un proxy insuffisant mais réutilisable ?
3. Lesquels ont surtout produit une clarification de statut ?
4. Quel est le gain réel de R68 après la doctrine R69 ?
5. Quel est le statut précis de R69 après son propre audit ?

### Livrables
Un tableau pour R62, R63, R64, R65, R66, R67, R68, R69 avec les colonnes :
- objet réellement traité ;
- type d’apport ;
- statut actuel ;
- utilité future ;
- risque de mauvaise lecture si non encadré.

---

# PHASE 2 — TRADUCTION CONTRÔLÉE VERS k≥3

## Condition d’activation
La PHASE 2 n’est autorisée que si la PHASE 1 conclut à l’une des sorties 1, 2 ou 3, avec au moins un bloc doctrinal canonique stable.

## But
Préparer le front k≥3 sans lancer encore une campagne de preuve lourde.
Le but est de **bien poser le prochain problème**, pas de faire semblant de l’avoir déjà résolu.

---

## AXE D — INVESTIGATEUR / DÉFINITION PROPRE DU FRONT k≥3
### Nom de travail
Quel est exactement le nouvel objet ?

### Mission
Écrire proprement l’objet corrSum / la somme à k termes / l’espace des compositions qui devient le vrai front après la doctrine R69.

### Questions obligatoires
1. Quel est l’objet canonique à étudier pour k≥3 ?
2. Quelle différence structurelle exacte le sépare du cas k=2 ?
3. Quelle partie de la factorisation de type 2^a c_δ disparaît ?
4. Quel type de somme exponentielle ou corrélation apparaît réellement ?
5. Quelles variables gouvernent la difficulté : k, support, coefficients, collisions, géométrie du support ?
6. Quel est le premier énoncé honnête qu’on voudrait établir sur cet objet ?

### Livrables
- définition canonique de l’objet k≥3 ;
- différence structurale avec k=2 ;
- première formulation honnête du verrou technique.

---

## AXE E — INVESTIGATEUR / TABLE DE TRANSFERT DES OUTILS
### Nom de travail
Qu’est-ce qu’on emporte, qu’est-ce qu’on laisse ?

### Mission
Déterminer ce qui, dans les outils développés sur k=2 / QR / K-lite / partitions d’ordre, peut être réutilisé, adapté, ou doit être abandonné sur le front k≥3.

### Questions obligatoires
1. Quels outils de R62–R65 restent mathématiquement réutilisables ?
2. Lesquels ne transfèrent pas du tout ?
3. Lesquels ne transfèrent qu’en vocabulaire, intuition ou schéma de preuve ?
4. Existe-t-il un invariant intermédiaire plus adapté à k≥3 que K-lite ?
5. Quelle est la première boîte à outils réaliste pour R71 ?

### Livrables
Un tableau à quatre colonnes :
- outil / résultat ;
- statut de transfert : [DIRECT] / [PARTIEL] / [ANALOGIQUE] / [NON TRANSFÉRABLE] ;
- justification ;
- utilité potentielle pour le front k≥3.

---

## AXE F — INNOVATEUR / REFORMULATION MINIMALE DU FRONT k≥3
### Nom de travail
Nommer juste le nouvel obstacle

### Mission
Si la PHASE 2 montre que le front k≥3 est encore mal formulé, l’innovateur peut proposer **au plus une** reformulation minimale permettant de mieux nommer l’obstacle technique principal.

### Règles strictes
- cette reformulation ne peut pas changer la cible logique ;
- elle doit être déclenchée par une difficulté identifiée dans AXE D ou E ;
- elle doit améliorer la contrôlabilité ou la lisibilité logique ;
- elle doit préciser ce qu’elle conserve de la doctrine de PHASE 1.

### Livrables
Pour cette unique reformulation éventuelle :
1. énoncé intuitif ;
2. version semi-formelle ;
3. obstacle absorbé ;
4. gain de lisibilité ou de contrôlabilité ;
5. risque de dérive ;
6. niveau estimé dans la Ladder of Proof.

---

# AUTONOMIE CONTRÔLÉE (OPTIONNELLE ET COURTE)

## Activation
Une mini-autonomie n’est autorisée qu’en PHASE 2, jamais en PHASE 1.

## Budget maximal
Au plus **2 sous-rounds internes** :
- **S1** : clarification finale de l’objet k≥3 ;
- **S2** : table de transfert + survivant.

## Événements STOP obligatoires
Arrêt immédiat si :
1. un changement de cible logique apparaît ;
2. une nouvelle ambiguïté doctrinale surgit ;
3. plus d’une reformulation innovante devient nécessaire ;
4. le front k≥3 ne peut pas être défini sans revenir réauditer R69 ;
5. aucun gain net n’apparaît après S1.

## Format obligatoire de chaque sous-round autonome
1. hypothèse active ;
2. objet exact ;
3. question ;
4. démarche ;
5. résultat net ;
6. statut ;
7. ce qui est appris ;
8. décision : continuer / arrêter ;
9. raison explicite de l’arrêt ou de la poursuite.

## Interdictions
- pas de campagne de preuve lourde ;
- pas de scans numériques larges ;
- pas de relance de K-lite comme cible ;
- pas de claim de percée sur k≥3 ;
- pas de dérive multi-fronts.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **P/T**
- **P** pour verrouillage de preuve / statut ;
- **T** pour préparation de transition propre vers un nouveau front.

## 2. IVS — Information Value Score
Noter /10 selon :
- robustesse de la doctrine ;
- réduction du risque de confusion future ;
- netteté de la transition k≥3 ;
- utilité des requalifications ;
- qualité des portes fermées.

Une bonne note IVS peut venir d’une doctrine brève mais très stabilisante.

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
Pour toute piste éliminée ou déclassée, fournir :
- Nom ;
- Type de mort :
  - confusion cible/outil,
  - confusion de compteur,
  - confusion de modèle,
  - insuffisance logique,
  - proxy non décisif,
  - mauvaise généralisation,
  - redondance ;
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
- outil technique ;
- laboratoire mathématique ;
- obstacle principal ;
- statut.

Tu dois favoriser les formulations minimales suffisantes :
- ni sur-vendre R69 ;
- ni sous-estimer son apport réel ;
- ni basculer trop tôt vers k≥3 sans objet canonique ;
- ni retransformer un outil en cible par paresse conceptuelle.

Tu ne dois pas :
- employer “définitif”, “sans objet”, “risque nul” sans justification bloc-par-bloc ;
- traiter k=2 comme front principal ;
- lancer une nouvelle architecture avant d’avoir figé la doctrine ;
- présenter une analogie comme un transfert ;
- laisser l’autonomie dépasser son budget ou ses STOP.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : les claims centraux de R69 sont reclassés avec une portée honnête.
PASS-2 : une doctrine canonique minimale cible / outil / laboratoire est produite.
PASS-3 : la séquence R62→R69 est requalifiée proprement.
PASS-4 : l’objet canonique du front k≥3 est défini au moins à un premier niveau propre.
PASS-5 : la table de transfert des outils est établie sans inflation rhétorique.
PASS-6 : l’autonomie éventuelle reste courte, utile et sous contrôle.
PASS-7 : un unique survivant rationnel pour R71 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R70 est utile si :
- une sur-assertion de R69 est correctement abaissée ;
- une doctrine plus sobre mais plus stable est obtenue ;
- un faux transfert vers k≥3 est évité ;
- le prochain front est mieux posé qu’avant.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats PHASE 1 / AXE A (audit des claims de R69)
5. Résultats PHASE 1 / AXE B (doctrine cible / outil / laboratoire)
6. Résultats PHASE 1 / AXE C (requalification R62→R69)
7. Verdict doctrinal principal
8. Activation ou non de la PHASE 2, avec justification
9. Résultats PHASE 2 / AXE D (définition du front k≥3)
10. Résultats PHASE 2 / AXE E (table de transfert des outils)
11. Résultats PHASE 2 / AXE F (reformulation minimale éventuelle)
12. Journal des sous-rounds autonomes éventuels
13. Objets concernés + Ladder of Proof
14. Ce qui est appris
15. Ce qui est fermé utilement
16. Ce qui est enterré
17. Autopsie des pistes fermées
18. Survivant pour R71
19. Risques / limites
20. Verdict final avec score /10
21. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R70 doit d’abord rendre R69 réutilisable sans emballement rhétorique.
Ensuite seulement, il peut préparer proprement le virage vers k≥3.

Le but n’est pas de courir plus loin.
Le but est de poser le prochain terrain sans emporter les anciennes confusions dans les bagages.

Chercher une doctrine stable, puis une transition propre.
Pas de triomphe. Pas de brouillard. Une architecture logique habitable.