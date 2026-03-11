

TYPE: P
OBJET CIBLÉ: Weighted Inductive V-bound + base k=2 + contrôle explicite de α,β
QUESTION CENTRALE: Peut-on faire monter la route inductive pondérée d’un cran vers un premier lemme semi-prouvé utile, en formalisant une borne récursive de type V(k) ≤ α·Σ_b (C_b/C)V(k−1,b,p) + β·C avec constantes explicites, et en verrouillant une base k=2 exploitable ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier quelle pièce manque réellement à la machine inductive (la récurrence, la base, ou le contrôle de α/β), et enterrer proprement toute formulation trop optimiste avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 55 (R55)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R54.

### Contexte acquis
- R52 a obtenu un premier contrôle quantitatif net en régime R1 :
  - V ≤ 1.42·C
  - donc μ−1 ≤ 1.42·p/C [OBSERVÉ]
- R53 a montré qu’en régime R1 :
  - E_excess < 0 sur l’échantillon testé
  - aucune collision h=1 n’existe [PROUVÉ]
- R54 a tranché entre deux routes pour traiter h≥2 :
  - la route **polynomial vanishing** donne de beaux résultats locaux (notamment h=2), mais ne scale pas ;
  - la route **inductive pondérée** est désormais la route principale survivante.
- La structure observée est :
  - contraction pointwise FAUSSE
  - contraction pondérée VRAIE sur tous les cas testés
  - V_cross typiquement favorable (≤ 0 ou petit)
  - dominance de E_intra croissante avec k
- Le survivant de R54 est :
  - **Weighted Inductive V-bound**
- La dette centrale est maintenant très claire :
  1. formaliser rigoureusement la récurrence pondérée ;
  2. contrôler explicitement α et β ;
  3. verrouiller une base k=2 exploitable.
- Le risque stratégique est désormais :
  - croire que l’observation de contraction suffit ;
  - ou se perdre dans des raffinements locaux alors que la vraie machine est maintenant globale et récursive.

## Objectif de R55
R55 doit répondre à cette question centrale :

> Peut-on transformer la contraction pondérée observée en une première charpente de lemme inductif, avec une base k=2 crédible et des constantes α,β suffisamment explicites pour faire de V=O(C) un objectif réaliste ?

R55 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de faire démarrer la machine inductive pour de vrai.

---

# ARCHITECTURE GÉNÉRALE

## Route principale unique
**Weighted Inductive V-bound**

## Deux sous-axes concurrents à départager
- **Sous-axe A** : formalisation de la récurrence pondérée et contrôle de α,β
- **Sous-axe B** : base k=2 exploitable et transport effectif vers k≥3

Le round doit trancher quelle pièce est le vrai verrou pour R56 : la récurrence elle-même, ou sa base.

---

# AXE A — INVESTIGATEUR / RÉCURRENCE PONDÉRÉE
## Nom de travail
Peut-on écrire le vrai lemme inductif ?

## Mission
Formaliser la meilleure version crédible de la borne récursive pondérée sur V, et localiser précisément ce qui contrôle α et β.

### Questions obligatoires
1. Quelle est la forme canonique la plus propre de la récurrence visée ?
   - V(k) ≤ α·Σ_b (C_b/C)V(k−1,b,p) + β·C
   - une variante légèrement différente mais plus exacte
   - autre
2. D’où viennent exactement α et β ?
   - découpage within/between
   - termes croisés
   - erreurs de normalisation
   - contributions de petites tranches
   - autres sources
3. Peut-on rendre α,β explicites, même grossièrement, à ce stade ?
4. Quelle est la condition minimale sur α,β pour que la récurrence soit réellement utile vers V=O(C) ?
5. Quel est le plus petit lemme semi-formel utile déjà atteignable ?

### Livrables
- une récurrence candidate écrite proprement ;
- origine détaillée des constantes α,β ;
- verdict honnête sur la viabilité de cette récurrence ;
- un premier noyau de lemme si possible.

---

# AXE B — INVESTIGATEUR / BASE k=2
## Nom de travail
La machine inductive peut-elle démarrer ?

## Mission
Étudier la base k=2 comme cas spécial potentiellement prouvable, et déterminer si elle peut servir de socle rigoureux à l’induction.

### Questions obligatoires
1. Quelle est la meilleure reformulation de V(2,M,p) / C(2) ?
2. Quels outils deviennent disponibles à k=2 :
   - invariance par translation
   - Weyl / sommes exponentielles classiques
   - structure cyclique de 2 mod p
   - autres leviers spécifiques
3. Peut-on obtenir une borne uniforme utile sur V(2,M,p)/C(2) ?
4. Quelle dépendance en p et M est réaliste à court terme ?
5. Quelle forme de base serait déjà suffisante pour nourrir la récurrence ?

### Livrables
- reformulation canonique de la base k=2 ;
- meilleure borne cible réaliste ;
- verdict honnête sur la faisabilité immédiate ;
- un noyau de lemme de base si possible.

---

# AXE C — INNOVATEUR / PREMIER NOYAU PROUVABLE DE LA MACHINE INDUCTIVE
## Nom de travail
Induction-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile.

### Candidat 1
**Récurrence-lite**
Une version affaiblie mais rigoureuse de la récurrence pondérée suffit déjà à montrer que V ne peut pas croître trop vite, voire qu’il reste O(C) sous hypothèse de base raisonnable.

### Candidat 2
**Base-lite + bootstrap**
Une base k=2 suffisamment forte, combinée à une récurrence partielle ou empirique sur α,β, donne déjà un premier schéma crédible de bootstrap.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R56 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- la difficulté principale (récurrence vs base), ou
- deux formes concurrentes de α,β.
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
- revenir à la route h-par-h comme route principale ;
- faire une campagne computationnelle large ;
- supposer que la contraction observée implique automatiquement une preuve ;
- présenter V=O(C) comme acquis.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une récurrence pondérée candidate est formulée proprement.
PASS-2 : l’origine et le rôle de α,β sont clarifiés.
PASS-3 : une base k=2 crédible est identifiée ou sérieusement cadrée.
PASS-4 : un premier noyau de lemme inductif est formulé.
PASS-5 : un survivant unique pour R56 est sélectionné proprement.

# ÉCHEC UTILE
Même en cas d’échec, R55 est utile si :
- la machine inductive est mieux localisée ;
- la vraie difficulté (α/β ou base) est isolée ;
- une formulation trop optimiste de la récurrence est éliminée proprement.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (récurrence)
5. Résultats AXE B (base k=2)
6. Résultats AXE C (arbitrage)
7. Contrôle secondaire éventuel
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R56
14. Risques / limites
15. Verdict final avec score /10

---

# CONSIGNE FINALE
R55 doit faire démarrer la machine inductive pour de vrai.
Le but n’est pas de mieux raconter la contraction pondérée.
Le but est de savoir si la preuve peut maintenant s’appuyer sur une vraie récurrence avec base exploitable.
Chercher le bon noyau inductif, pas la théorie finale complète.