

TYPE: P
OBJET CIBLÉ: Step 2 du survivant R53 + collisions h≥2 + polynomial vanishing sur simplexe, avec induction par dernière coordonnée comme plan B explicite
QUESTION CENTRALE: Peut-on faire monter le survivant “Min Hamming + polynomial vanishing” d’un cran vers un premier lemme semi-prouvé utile, en bornant les collisions à distance h≥2 en régime R1, ou en montrant qu’une induction par dernière coordonnée fournit un fallback plus démontrable ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier quelle des deux routes — polynomial vanishing ou induction — porte réellement la prochaine marche, et enterrer proprement toute sous-route trop fragile avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 54 (R54)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R53.

### Contexte acquis
- R52 a donné le premier contrôle quantitatif net en régime R1 :
  - V ≤ 1.42·C
  - donc μ−1 ≤ 1.42·p/C [OBSERVÉ]
- R53 a renversé la lecture du problème en régime R1 :
  - **E_excess < 0** sur l’échantillon étudié
  - il n’y a pas de “surplus à contrôler”, mais un **déficit de collisions** à expliquer
- R53 a prouvé la première exclusion structurelle dure :
  - **pas de collisions à distance h=1 en R1**
- Le survivant choisi en fin de R53 est :
  - **Min Hamming + polynomial vanishing**
  c’est-à-dire : utiliser l’absence de h=1 comme point d’appui, puis comprendre / borner les collisions pour h≥2.
- R53 a aussi clarifié un plan B crédible :
  - **induction par dernière coordonnée**
  si la route polynomiale sur simplexe se révèle à nouveau trop fragile.
- Le risque stratégique est maintenant :
  - s’obstiner dans une route polynomiale élégante mais insuffisamment robuste ;
  - ou au contraire abandonner trop tôt un levier peut-être décisif.

## Objectif de R54
R54 doit répondre à cette question centrale :

> Peut-on obtenir une première borne ou exclusion utile sur les collisions h≥2 en régime R1 par la route “Min Hamming + polynomial vanishing”, ou faut-il déjà basculer vers l’induction par dernière coordonnée comme route principale ?

R54 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de décider quelle route porte réellement la prochaine marche démontrable.

---

# ARCHITECTURE GÉNÉRALE

## Deux routes concurrentes explicites
- **Route A** : Min Hamming + polynomial vanishing (prioritaire au départ)
- **Route B** : induction par dernière coordonnée (plan B officiel)

Le round doit trancher honnêtement laquelle des deux routes devient prioritaire pour R55.

---

# AXE A — INVESTIGATEUR / COLLISIONS h≥2 PAR POLYNOMIAL VANISHING
## Nom de travail
Que peut-on vraiment exclure pour h≥2 ?

## Mission
Étudier les collisions entre paires monotones à distance minimale h≥2 en régime R1, et déterminer si l’approche par annulation/polynomial vanishing sur simplexe peut donner un premier lemme utile.

### Questions obligatoires
1. Quelle est la forme canonique de la condition de collision pour des paires à distance minimale h≥2 ?
2. Le cadre “polynomial vanishing sur simplexe monotone” donne-t-il une vraie contrainte de faible degré, ou bien un objet trop diffus pour être attaqué ?
3. Existe-t-il un sous-cas déjà accessible :
   - h=2 uniquement,
   - supports disjoints,
   - écarts minimaux spécifiques,
   - autres sous-familles naturelles ?
4. Peut-on produire une exclusion structurelle ou une borne grossière sur le nombre de telles collisions ?
5. Quel est le plus petit énoncé semi-formel utile que cette route pourrait livrer dès maintenant ?

### Livrables
- une reformulation canonique des collisions h≥2 ;
- verdict honnête sur la viabilité du polynomial vanishing ;
- un premier sous-lemme si possible, même faible.

---

# AXE B — INVESTIGATEUR / INDUCTION PAR DERNIÈRE COORDONNÉE
## Nom de travail
Le fallback devient-il la vraie route ?

## Mission
Étudier si une induction par dernière coordonnée permet de contrôler ou de décomposer les collisions h≥2 plus proprement que la route polynomiale.

### Questions obligatoires
1. Quelle est la meilleure reformulation des collisions quand on fixe la dernière coordonnée / dernière marche monotone ?
2. La structure monotone se comporte-t-elle mieux sous cette coupe qu’en formulation globale sur le simplexe ?
3. Peut-on espérer une récurrence naturelle :
   - sur k,
   - sur max_B,
   - sur la profondeur monotone,
   - autre ?
4. Quelle obstruction a déjà été vue dans les anciennes tentatives d’induction, et en quoi cette nouvelle coupe la contourne-t-elle ou non ?
5. Quel est le plus petit lemme inductif crédible et utile pour le contrôle de h≥2 ?

### Livrables
- une reformulation canonique de l’approche par dernière coordonnée ;
- verdict honnête sur sa force réelle ;
- un noyau de lemme inductif si possible.

---

# AXE C — INNOVATEUR / ARBITRAGE DES DEUX ROUTES
## Nom de travail
Premier noyau prouvable pour l’étape 2

## Mission
À partir des deux analyses précédentes, proposer au plus 2 formulations candidates d’un premier noyau prouvable utile.

### Candidat 1
**h≥2-lite par polynomial vanishing**
Une version faible mais utile de l’approche polynomiale exclut ou borne déjà une sous-famille de collisions h≥2, ce qui fait avancer le contrôle global de E_excess.

### Candidat 2
**h≥2-lite par induction**
Une version récursive faible par dernière coordonnée contrôle déjà une partie utile des collisions h≥2, avec un potentiel plus robuste pour la suite.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R55 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager la route polynomiale et la route inductive sur un sous-cas h≥2.
Pas de nouvelle base de données.
Pas de campagne de confort.

---

# REGISTRE MÉTHODOLOGIQUE OBLIGATOIRE

## 1. Type du round
Rappeler explicitement : P

## 2. IVS — Information Value Score
Donner une note /10 avec justification courte :
- potentiel de réfutation
- gain de structure
- proximité d’un lemme
- risque d’accumulation

## 3. Ladder of Proof
Pour chaque objet touché, préciser :
- intuition
- observation
- observation répétée
- calcul exact
- semi-formalisation
- schéma de preuve
- lemme candidat
- lemme prouvé
- résultat publiable

## 4. AUTOPSIE DES PISTES FERMÉES (OBLIGATOIRE)
Pour toute piste éliminée, fournir :
- Nom
- Type de mort :
  - contredite
  - mauvaise échelle
  - trop faible
  - non ciblante
  - redondante
  - absorbée
- Hypothèse implicite fausse
- Ce que la mort enseigne
- Où cela redirige

---

# CEC — CONSIGNE
CEC reste inchangé :
- Type A : obstruction première directe
- Type B : exclusion composite exacte
- Type C : exclusion composite par bornes combinées
- Type D : exclusion analytique via SPC / structure monotone composite

---

# CONTRAINTES MÉTHODOLOGIQUES
Tu dois distinguer explicitement :
- prouvé
- semi-prouvé
- calculé exact
- semi-formalisé
- heuristique
- conjectural
- réfuté

Tu ne dois pas :
- revenir à une taxonomie générale des collisions sans levier de preuve ;
- faire une campagne computationnelle large ;
- supposer que h=2 résout automatiquement tout h≥2 ;
- présenter le déficit E_excess<0 comme prouvé général alors qu’il est encore observé.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une reformulation utile des collisions h≥2 est obtenue.
PASS-2 : la viabilité réelle de la route polynomiale est clarifiée.
PASS-3 : un noyau de lemme utile est formulé soit côté polynomial, soit côté induction.
PASS-4 : au moins une des deux routes est hiérarchisée clairement par autopsie si elle échoue.
PASS-5 : un survivant unique pour R55 est sélectionné proprement.

# ÉCHEC UTILE
Même en cas d’échec, R54 est utile si :
- la route polynomiale est honnêtement déclarée trop fragile ;
- la route inductive est mieux formalisée ;
- un sous-cas h≥2 réellement démontrable est isolé.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (polynomial vanishing)
5. Résultats AXE B (induction)
6. Résultats AXE C (arbitrage)
7. Contrôle secondaire éventuel
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R55
14. Risques / limites
15. Verdict final avec score /10

---

# CONSIGNE FINALE
R54 doit décider quelle route peut réellement porter l’étape 2 du survivant R53.
Le but n’est pas de refaire une carte des collisions.
Le but est d’obtenir la première marche démontrable sur h≥2 ou de choisir honnêtement le bon fallback.
Chercher le bon levier de preuve, pas la théorie finale complète.