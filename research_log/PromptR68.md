TYPE: P
OBJET CIBLÉ: pont de modèle entre l’objet Collatz fondé sur <2> et l’objet QR fondé sur <g^2>, avec test explicite de transférabilité d’un contrôle K-lite
QUESTION CENTRALE: une borne K-lite uniforme prouvée sur le modèle QR peut-elle se transférer mathématiquement au vrai modèle Collatz, et si non, quel est exactement l’obstacle structurel ou le plus petit énoncé sauvable ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: isoler proprement soit un lemme de transfert valide avec hypothèses exactes, soit une obstruction nette, avec autopsie complète des fausses pistes pour rouvrir d’autres directions rationnelles.
PRINCIPE D’ÉQUILIBRE: verrouiller les glissements de portée et les faux transferts, sans interdire les reformulations disciplinées, les sous-cas canoniques, ni les invariants plus faibles réellement motivés par l’obstacle rencontré.

# BRIEF CLAUDE CODE — ROUND 68 (R68)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R67.

R68 n’a qu’un seul verrou légitime :
**le pont de modèle entre la cible Collatz de R57/R60 et l’objet QR réellement traité en R62→R65.**

Le round ne doit pas “faire avancer un peu tout”.
Le round doit décider proprement si un transfert de type K-lite existe, sous quelles hypothèses, ou pourquoi il échoue.

---

## Contexte acquis
- R67 a établi qu’il existe une **substitution de modèle non justifiée** entre :
  - la cible Collatz de R57/R60, de forme
    c_δ = 1 + g_C 2^δ (mod p),
  - et l’objet QR traité à partir de R62, de forme
    c_δ = 1 + g^{2δ} (mod p).
- La chaîne **R62→R65 n’est pas rejetée en bloc** : elle reste valide **dans sa propre portée**.
- Le résultat solide actuel est donc :
  - **contrôle K-lite universel sur le modèle QR / <g^2>**.
- Le résultat non acquis est :
  - **contrôle K-lite universel sur le vrai modèle Collatz / <2>**.
- Le verrou principal n’est plus “R1/R2/R3”, ni “S_h”, ni “cross-résidu”, mais bien :
  - **le transfert de portée QR → Collatz**.
- Toute tentative de relancer cross-résidu, storytelling stratégique, ou généralisation prématurée est hors sujet tant que ce verrou n’est pas traité.

---

# OBJECTIF DE R68
R68 doit répondre à cette question centrale :

> Peut-on établir un transfert mathématiquement valide entre le modèle Collatz fondé sur <2> et le modèle QR fondé sur <g^2>, de façon suffisamment forte pour transférer un contrôle de type K-lite ?

Les sorties acceptables du round sont :
1. **Pont universel obtenu** ;
2. **Pont obtenu sous hypothèses explicites** ;
3. **Pont partiel obtenu avec portée strictement bornée** ;
4. **Pont universel réfuté / non transférable par cette voie** ;
5. **Aucun lemme de transfert suffisant trouvé ; verrou inchangé**.

Important : une sortie partielle n’est recevable que si sa portée est canonique, explicitement formulée, et utile pour la suite du programme.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Pont de modèle Collatz ↔ QR**

## Pièces auxiliaires autorisées mais subordonnées
- partition arithmétique des cas selon la position de 2 dans F_p^× ;
- étude locale d’inclusion de sous-groupes ou de cosets ;
- micro-tests numériques ciblés uniquement pour départager un lemme précis ;
- reformulation d’un invariant plus faible que K-lite si le transfert fort échoue.
- tentative de contre-lemme ou d’obstruction active pour casser un faux transfert plausible ;
- exploration de reformulations locales si elles sont déclenchées par un obstacle explicite et non par simple goût de variation.

## Pièces explicitement interdites comme cible principale
- cross-résidu ;
- relance frontale de S_h, D_∞ ou des preuves déjà closes dans leur portée QR ;
- scans numériques larges “pour voir” ;
- récit d’avancement sans théorème de transfert.

---

# AXE A — INVESTIGATEUR / FORMALISATION CANONIQUE DES OBJETS
## Nom de travail
Parle-t-on bien du même objet ?

## Mission
Écrire noir sur blanc, avec quantificateurs, notations propres et statuts explicites :
- l’objet exact de R57/R60 (modèle Collatz / <2>) ;
- l’objet exact de R62→R65 (modèle QR / <g^2>) ;
- la quantité exacte bornée dans chaque cadre ;
- le sens exact de “K-lite” ;
- l’endroit précis où la substitution de modèle s’est produite.

### Questions obligatoires
1. Quelle est la définition canonique de l’objet Collatz visé historiquement ?
2. Quelle est la définition canonique de l’objet QR réellement traité analytiquement ?
3. Qu’est-ce qui est identique entre les deux cadres ?
4. Qu’est-ce qui change réellement : ensemble indexé, sous-groupe, coset, multiplicité, quantificateur ?
5. Quel est le plus petit tableau de statuts impossible à mal lire ?
6. Quelle définition opérationnelle exacte de “K-lite” est autorisée dans ce round, sans variation implicite ?
7. Quels symboles, notations ou quantificateurs risquent de donner l’illusion qu’on parle du même objet alors que non ?

### Livrables
- mini section **Objets et statuts** ;
- tableau “même forme symbolique / objet réellement différent” ;
- localisation exacte de la rupture logique.

---

# AXE B — INVESTIGATEUR / AUDIT ARITHMÉTIQUE DU PONT
## Nom de travail
Quand <2> ressemble-t-il vraiment à un sous-objet de QR ?

## Mission
Partitionner proprement les cas arithmétiques et déterminer si un lien structurel exploitable existe entre le modèle Collatz et le modèle QR.

### Questions obligatoires
1. Quand 2 appartient-il à QR_p ?
2. Quand <2> est-il inclus dans QR_p ?
3. Quel est l’indice de <2> dans F_p^× en fonction de ord_p(2) ?
4. Dans quels cas obtient-on :
   - inclusion de sous-ensemble,
   - inclusion de sous-groupe,
   - coset contrôlable,
   - ou aucune structure utile ?
5. Parmi ces cas, lesquels sont réellement pertinents pour un transfert de borne ?

### Règle critique
**Ne pas confondre inclusion d’ensemble et transfert de multiplicité.**
Le fait que l’objet Collatz soit inclus dans un ensemble plus grand ne suffit pas automatiquement à transférer une borne K-lite.

### Livrables
- partition canonique des cas ;
- verdict sur chaque cas : structure exploitable ou non ;
- première carte des portes ouvertes / portes fermées.
- note explicite sur les cas qui semblent prometteurs mais ne donnent en réalité aucun transfert de borne.

---

# AXE C — INVESTIGATEUR / TEST DU TRANSFERT DE BORNE
## Nom de travail
QR ⇒ Collatz ? Vrai, faux, ou seulement parfois ?

## Mission
C’est le cœur du round.
Tu dois tester explicitement un énoncé du type :

> “Une borne K-lite uniforme sur le modèle QR implique une borne K-lite uniforme sur le modèle Collatz.”

### Questions obligatoires
1. Cet énoncé est-il vrai tel quel ?
2. S’il est faux, où casse-t-il exactement ?
3. S’il est vrai sous hypothèses, quelles sont-elles précisément ?
4. Faut-il dégrader la constante ?
5. Un invariant plus faible que K-lite se transfère-t-il plus naturellement ?
6. Quel est le meilleur argument en faveur du transfert ?
7. Quel est le meilleur argument contre le transfert ?

### Formes de sortie autorisées
- un lemme précis et prouvé ;
- un contre-exemple conceptuel ou une obstruction structurelle ;
- un énoncé restreint à une classe canonique de premiers ;
- une forme plus faible mais démontrable.

### Livrables
Pour chaque lemme candidat :
- énoncé ;
- statut : [PROUVÉ] / [RÉFUTÉ] / [PARTIEL] / [HEURISTIQUE] ;
- preuve ou obstruction ;
- dépendances exactes.

Tu dois aussi inclure, pour au moins le lemme principal, une mini section “contre-transfert” :
- pourquoi on pourrait croire que le lemme est vrai ;
- quel mécanisme concret pourrait le rendre faux ;
- et ce qui a effectivement survécu à cette confrontation.

---

# AXE D — INNOVATEUR / FORMULATIONS NOUVELLES SI LE TRANSFERT FORT ÉCHOUE
## Nom de travail
Que découvre-t-on quand le langage change l’objet ?

## Mission
Si le transfert universel QR ⇒ Collatz échoue, ne pas bricoler rhétoriquement.
Chercher au plus **2 reformulations innovantes mais mathématiquement disciplinées** qui transforment l’obstacle en nouvelle piste exploitable.

L’innovateur ne sert pas à rêver :
il sert à **nommer proprement une structure nouvelle** quand un échec révèle qu’on parlait mal de l’objet.
Comme découvrir une “multiplication” conceptuelle en observant des additions répétées :
il faut inventer le bon langage, le bon invariant, ou la bonne factorisation logique.

L’innovateur n’a pas le droit d’ouvrir une nouvelle piste seulement parce qu’elle est élégante. Toute reformulation doit être déclenchée par un obstacle identifié dans AXE B ou AXE C, et doit promettre soit une meilleure contrôlabilité, soit une meilleure lisibilité logique.

### Candidat 1 possible
Un **lemme de transfert plus faible** :
- transfert avec constante dégradée ;
- transfert sur une sous-classe de premiers ;
- transfert en moyenne mais non uniforme ;
- invariant plus faible que K-lite mais encore utile.

### Candidat 2 possible
Une **obstruction génératrice** :
- formalisation du mécanisme exact qui empêche le transfert ;
- nouvelle variable, nouvelle partition, nouveau critère de contrôlabilité ;
- reformulation qui ouvre R69 sur une cible mieux posée.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. quel obstacle de R68 il absorbe ;
4. ce qu’il permettrait d’attaquer ensuite ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R69 ;
- éliminer explicitement les autres ;
- justifier le choix par démontrabilité réelle ou pouvoir explicatif réel, pas par enthousiasme.

---

# AXE E — CONTRÔLE STRATÉGIQUE / IMPACT PROGRAMME
## Nom de travail
Ne pas mentir au programme

## Mission
Dire précisément ce que R68 change dans la cartographie globale du projet.
Sans relancer cross-résidu, il faut recaler le programme après verdict sur le pont de modèle.

### Questions obligatoires
1. Qu’est-ce qui devient réellement acquis après R68 ?
2. Qu’est-ce qui redevient explicitement conjectural ?
3. Cross-résidu reste-t-il interdit comme front principal ?
4. Quel est l’unique round suivant rationnel ?
5. Une nouvelle porte s’ouvre-t-elle parce qu’une fausse piste a été comprise et autopsiée ?
6. Quelle porte a été fermée utilement, et quelle porte nouvelle s’ouvre uniquement grâce à la compréhension de cette fermeture ?

### Livrables
- impact net sur la feuille de route ;
- aucune inflation rhétorique ;
- un seul survivant programmatique pour R69.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test numérique ciblé est autorisé si et seulement s’il sert à départager :
- deux formulations concurrentes d’un lemme de transfert ;
- un cas arithmétique exploitable contre un cas trompeur ;
- ou une obstruction structurelle précise.

Conditions strictes :
- annoncer l’énoncé exact testé ;
- annoncer le domaine exact testé ;
- expliquer en quoi le test soutient ou fragilise le lemme ;
- aucun tableau décoratif ;
- aucun “ça semble marcher” comme conclusion.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : **P**

## 2. IVS — Information Value Score
Donner une note /10 avec justification courte :
- potentiel de réfutation ;
- gain de structure ;
- proximité d’un vrai lemme ;
- risque d’accumulation stérile.

Une bonne note IVS peut venir d’une obstruction nette si elle réduit fortement l’espace des illusions.

## 3. Ladder of Proof
Pour chaque objet touché, préciser :
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
Pour toute piste éliminée, fournir :
- Nom ;
- Type de mort :
  - contredite,
  - mauvaise échelle,
  - trop faible,
  - non ciblante,
  - redondante,
  - absorbée,
  - substitution de modèle ;
- Hypothèse implicite fausse ;
- Ce que la mort enseigne ;
- Où cela redirige.

## 5. REGISTRE FAIL-CLOSED
Tu dois terminer par un tableau strict :
- [PROUVÉ]
- [CALCULÉ EXACT]
- [OBSERVÉ NUMÉRIQUEMENT]
- [HEURISTIQUE]
- [CONJECTURAL]
- [RÉFUTÉ]

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- prouvé ;
- semi-prouvé ;
- calculé exact ;
- semi-formalisé ;
- heuristique ;
- conjectural ;
- réfuté.

Tu dois favoriser les formulations minimales suffisantes : ni sur-généraliser trop tôt, ni refermer artificiellement une porte locale qui deviendrait exploitable une fois correctement nommée.

Tu ne dois pas :
- affirmer ou suggérer que le résultat QR vaut “donc” pour Collatz sans lemme de transfert explicite et prouvé ;
- confondre inclusion d’ensemble, domination uniforme des multiplicités, et transfert de borne K-lite ;
- recycler des arguments Jacobi / index 2 comme s’ils étaient automatiquement valides pour <2> ;
- relancer cross-résidu, heuristiques globales ou storytelling tant que le pont n’est pas établi ;
- changer d’objet, de notation ou de quantificateur sans le déclarer explicitement ;
- utiliser des observations numériques comme substitut à une preuve structurelle.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : les deux objets sont formalisés de façon canonique et impossible à confondre.
PASS-2 : les cas arithmétiques pertinents sont partitionnés proprement.
PASS-3 : au moins un lemme de transfert est classé honnêtement : vrai, faux ou partiel.
PASS-4 : au moins une illusion de type “inclusion donc transfert” est autopsiée proprement.
PASS-5 : un survivant unique pour R69 est sélectionné.
PASS-6 : au moins une porte fermée est transformée en enseignement structurant ou en reformulation utile.

# ÉCHEC UTILE
Même en cas d’échec, R68 est utile si :
- l’obstacle structurel exact au transfert est isolé ;
- un sous-cas réellement transférable est identifié ;
- une reformulation plus faible mais rigoureuse est sauvée ;
- une piste fermée est autopsiée de façon à ouvrir une nouvelle direction rationnelle.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (formalisation des objets)
5. Résultats AXE B (audit arithmétique)
6. Résultats AXE C (test du transfert de borne)
7. Résultats AXE D (reformulations innovantes)
8. Résultats AXE E (impact programme)
9. Contrôle secondaire éventuel
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est fermé utilement
13. Ce qui est enterré
14. Autopsie des pistes fermées
15. Survivant pour R69
16. Risques / limites
17. Verdict final avec score /10
18. Registre FAIL-CLOSED

---

# CONSIGNE FINALE
R68 doit traiter le vrai verrou révélé par R67.
Le but n’est pas de faire briller le proxy QR.
Le but est de décider proprement ce qu’il transmet — ou ne transmet pas — au vrai objet Collatz.
Et si une porte se ferme, il faut en extraire une information exploitable plutôt qu’un simple constat d’échec.

Chercher la prochaine fermeture rigoureuse, ou la prochaine impossibilité bien comprise.
Pas une belle histoire. Une carte logique fiable.
