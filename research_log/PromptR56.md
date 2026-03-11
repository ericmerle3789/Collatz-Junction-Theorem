

TYPE: P
OBJET CIBLÉ: base k=2 + contrôle de V_cross + bootstrap sans récurrence universelle
QUESTION CENTRALE: Peut-on faire monter la machine post-R55 d’un cran vers un premier schéma semi-prouvé utile, en verrouillant une base k=2 rigoureuse et en identifiant une première borne structurale crédible sur V_cross suffisante pour un bootstrap, sans retomber dans l’illusion d’une récurrence universelle ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier clairement laquelle des deux pièces — la base k=2 ou le contrôle de V_cross — est désormais le vrai verrou, et enterrer proprement toute formulation trop optimiste avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 56 (R56)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R55.

### Contexte acquis
- R52 a donné un premier contrôle quantitatif net en régime R1 :
  - V ≤ 1.42·C
  - donc μ−1 ≤ 1.42·p/C [OBSERVÉ]
- R53 a montré qu’en régime R1 :
  - E_excess < 0 sur l’échantillon testé
  - aucune collision h=1 n’existe [PROUVÉ]
- R54 a abandonné la route h-par-h comme moteur principal au profit d’une route inductive pondérée globale.
- R55 a montré que la belle récurrence universelle espérée n’existe pas sous forme naïve.
- R55 a cependant produit deux résultats majeurs :
  1. **base k=2 très solide**, avec shift-invariance prouvée :
     P_{B+(1,1)} = 2g·P_B mod p
  2. **le vrai verrou est V_cross**, pas la base ni un mauvais calibrage local de la récurrence.
- L’invariant central observé devient :
  - |γ| = |V_cross / V_within| < 1
  sur les cas testés.
- La machine de preuve post-R55 n’est donc plus :
  - “une seule récurrence élégante”,
  mais plutôt :
  - **base k=2 solide + contrôle séparé de V_cross + bootstrap**.
- Le risque stratégique est maintenant :
  - reconstruire une pseudo-récurrence universelle qui a déjà échoué ;
  - ou rester trop descriptif sur la base et sur V_cross sans en extraire de levier de preuve.

## Objectif de R56
R56 doit répondre à cette question centrale :

> Peut-on transformer l’architecture post-R55 en premier schéma de preuve utile, en (i) rendant la base k=2 aussi rigoureuse que possible, et (ii) obtenant une première borne ou structure crédible sur V_cross suffisante pour un bootstrap, même faible ?

R56 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de savoir quelle pièce porte réellement la prochaine marche : la base, ou le cross.

---

# ARCHITECTURE GÉNÉRALE

## Deux pièces concurrentes à départager
- **Pièce A** : preuve / quasi-preuve de la base k=2
- **Pièce B** : première borne structurale utile sur V_cross

Le round doit trancher laquelle des deux est désormais le vrai verrou pour R57.

---

# AXE A — INVESTIGATEUR / BASE k=2
## Nom de travail
Peut-on verrouiller la base ?

## Mission
Transformer la base k=2 en lemme aussi rigoureux et exploitable que possible.

### Questions obligatoires
1. Quelle est la formulation la plus propre de la base visée ?
   - A(2) = V(2)/C(2) ≤ K uniforme en R1
   - variante légèrement plus faible mais prouvable
   - autre
2. La shift-invariance suffit-elle presque à elle seule, ou faut-il un second ingrédient essentiel ?
3. Quel rôle exact jouent :
   - les orbites complètes,
   - les points de bord,
   - la structure cyclique de 2 mod p,
   - les outils type Weyl/sommes exponentielles ?
4. Peut-on déjà produire une vraie borne rigoureuse, même grossière, sur A(2) ?
5. Quelle forme de base serait déjà suffisante pour nourrir un bootstrap ultérieur ?

### Livrables
- reformulation canonique de la base k=2 ;
- stratégie de preuve la plus crédible ;
- meilleur lemme de base atteignable immédiatement ;
- verdict honnête : prouvable maintenant / semi-formalisable / encore trop dur.

---

# AXE B — INVESTIGATEUR / CONTRÔLE DE V_cross
## Nom de travail
Comment borner le terme croisé ?

## Mission
Étudier la quantité V_cross et déterminer quelle forme de contrôle est réellement atteignable à court terme.

### Questions obligatoires
1. Quelle est la reformulation canonique la plus exploitable de V_cross ?
   - covariance inter-tranches,
   - somme de corrélations croisées,
   - somme de caractères croisés,
   - autre
2. Quel objectif paraît le plus réaliste à court terme ?
   - |V_cross| ≤ θ·V_within avec θ<1
   - |V_cross| = O(C)
   - |γ|<1 dans un sous-régime naturel
   - autre
3. Peut-on isoler des régimes ou sous-familles où V_cross est plus facile à contrôler ?
4. Quel mécanisme semble le plus prometteur :
   - cancellation de signes,
   - quasi-orthogonalité,
   - contrôle agrégé des tranches,
   - autre
5. Quelle est la plus petite borne utile déjà assez forte pour nourrir un bootstrap ?

### Livrables
- reformulation canonique de V_cross ;
- meilleure cible de borne réaliste ;
- un premier noyau de lemme si possible ;
- verdict honnête sur la faisabilité immédiate.

---

# AXE C — INNOVATEUR / BOOTSTRAP POST-R55
## Nom de travail
Premier schéma de preuve dissocié

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile pour la machine post-R55.

### Candidat 1
**Base-lite + cross-lite**
Une base k=2 uniforme combinée à une borne faible mais structurale sur V_cross suffit déjà à esquisser un bootstrap vers V=O(C) dans un sous-régime utile.

### Candidat 2
**Cross-first**
Le contrôle de V_cross est le vrai verrou ; une fois celui-ci dominé, la base k=2 actuelle est déjà assez bonne pour porter la suite.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R57 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- la difficulté principale (base vs cross), ou
- deux formes concurrentes de borne sur V_cross.
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
- reconstruire une récurrence universelle naïve déjà enterrée ;
- lancer une campagne computationnelle large ;
- supposer que la base seule suffit ;
- présenter |γ|<1 comme prouvé général alors qu’il est encore observé.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une formulation propre de la base k=2 est isolée.
PASS-2 : une cible réaliste de borne sur V_cross est sélectionnée.
PASS-3 : un premier noyau de bootstrap post-R55 est formulé.
PASS-4 : au moins une formulation trop optimiste est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R57 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R56 est utile si :
- la vraie difficulté principale (base ou cross) est clairement hiérarchisée ;
- une pseudo-récurrence résiduelle est définitivement éliminée ;
- une version plus pauvre mais plus prouvable du bootstrap est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (base k=2)
5. Résultats AXE B (V_cross)
6. Résultats AXE C (arbitrage)
7. Contrôle secondaire éventuel
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R57
14. Risques / limites
15. Verdict final avec score /10

---

# CONSIGNE FINALE
R56 doit transformer l’architecture post-R55 en première machine de preuve utilisable.
Le but n’est pas de mieux raconter la base ou le cross séparément.
Le but est d’identifier quelle pièce doit être verrouillée maintenant pour rendre un bootstrap réaliste.
Chercher le bon noyau de preuve dissocié, pas la théorie finale complète.