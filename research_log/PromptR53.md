

TYPE: P
OBJET CIBLÉ: μ-lite collision + E_excess + structure des collisions excédentaires en régime R1
QUESTION CENTRALE: Peut-on faire monter μ-lite collision d’un cran vers un premier lemme semi-prouvé utile, en identifiant quelles familles de paires (B,B') produisent réellement l’excès de collisions E_excess en régime R1, et en montrant qu’elles restent en nombre O(C) ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier la bonne taxonomie des collisions excédentaires, et enterrer proprement toute famille de paires supposée dominante mais en réalité négligeable avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 53 (R53)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R52.

### Contexte acquis
- R50 a unifié between et within via **TQL**.
- R51 a stabilisé la bonne métrique : **μ**, pas D∞.
- R52 a obtenu le premier contrôle quantitatif net en régime R1 :
  - V ≤ 1.42·C
  - donc μ−1 ≤ 1.42·p/C
  sur 232 cas R1+ [OBSERVÉ]
- La bonne reformulation est :
  - μ−1 = (p−1)/C + p·E_excess/C²
- Le vrai verrou devient donc :
  - **borner E_excess**, l’excès de collisions au-dessus du hasard uniforme.
- L’arbitrage de R52 est clair :
  - la route prioritaire est **μ-lite collision**
  - Horner reste route secondaire explicative, mais non principale pour R53.
- Le risque stratégique est maintenant :
  - continuer à raffiner μ sans comprendre qui produit réellement E_excess ;
  - ou faire une taxonomie descriptive sans levier de comptage.

## Objectif de R53
R53 doit répondre à cette question centrale :

> Quelles familles de paires monotones (B,B') produisent réellement l’excès de collisions E_excess en régime R1, et peut-on déjà montrer qu’elles sont suffisamment rares ou structurées pour rendre plausible une borne E_excess = O(C) ?

R53 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de transformer la borne observée de R52 en premier programme combinatoire démontrable.

---

# ARCHITECTURE GÉNÉRALE

## Route principale unique
**μ-lite collision via classification de E_excess**

## Deux sous-axes concurrents à départager
- **Sous-axe A** : taxonomie des collisions excédentaires par distance/structure
- **Sous-axe B** : comptage global / double comptage des familles dominantes

Le round doit trancher quelle approche donne la meilleure prochaine marche pour R54.

---

# AXE A — INVESTIGATEUR / TAXONOMIE DES COLLISIONS EXCÉDENTAIRES
## Nom de travail
Qui fabrique E_excess ?

## Mission
Décomposer les collisions excédentaires selon des familles structurelles naturelles, et identifier lesquelles peuvent réellement dominer en régime R1.

### Questions obligatoires
1. Quelle est la meilleure décomposition de E_excess ?
   - par distance de Hamming h
   - par taille des déplacements Δ
   - par géométrie des paires monotones
   - par ord_p(2) et contraintes modulaires
   - autre
2. Les contributions dominantes viennent-elles des faibles distances (h=1, h=2, near-collisions), ou de familles plus diffuses ?
3. Le résultat LSD h=1 [PROUVÉ R46] peut-il servir de point d’appui direct dans la décomposition ?
4. Peut-on identifier une famille “pathologique” mais petite, opposée à un fond quasi-uniforme ?
5. Quelle taxonomie est la plus utile pour un futur comptage O(C) ?

### Livrables
- une taxonomie claire des collisions excédentaires ;
- une hiérarchie honnête des familles dominantes / négligeables ;
- un verdict sur la meilleure variable de classement.

---

# AXE B — INVESTIGATEUR / DOUBLE COMPTAGE ET BORNES GLOBALES
## Nom de travail
Peut-on compter les paires excessives ?

## Mission
Chercher une première stratégie de double comptage, ou un schéma global, pour montrer que les familles dominantes de collisions restent en nombre O(C) en régime R1.

### Questions obligatoires
1. Comment reformuler E_excess comme comptage d’un ensemble de paires “collisionnelles excédentaires” ?
2. Peut-on majorer certaines familles via :
   - LSD h=1
   - contraintes de monotonie
   - ord_p(2)
   - simple arguments de volume/combinatoire
   - autres leviers structurels
3. Une majoration famille par famille paraît-elle plus réaliste qu’une majoration globale directe ?
4. Existe-t-il un schéma de double comptage naturel :
   - fixer B puis compter B'
   - fixer le profil de différences
   - fixer la classe modulaire puis remonter
   - autre
5. Quelle version faible mais utile de O(C) paraît réaliste à court terme ?
   - E_excess ≤ A·C
   - E_excess ≤ A·C·log C
   - E_excess dominé par familles de faible h
   - autre

### Livrables
- reformulation canonique de E_excess comme problème de comptage ;
- une ou deux stratégies de majoration crédibles ;
- un premier noyau de borne si possible.

---

# AXE C — INNOVATEUR / PREMIER NOYAU PROUVABLE POUR μ-LITE COLLISION
## Nom de travail
Collision-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile.

### Candidat 1
**Collision-lite par familles dominantes**
Les collisions excédentaires sont essentiellement concentrées sur un petit nombre de familles structurelles, chacune bornable séparément, ce qui donne E_excess = O(C) dans R1.

### Candidat 2
**Collision-lite par faible distance**
Les contributions excédentaires significatives proviennent principalement des faibles distances de Hamming ; au-delà, le fond devient quasi-uniforme et ne contribue plus qu’à l’ordre du hasard.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement sur μ−1 ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R54 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager deux taxonomies ou deux familles supposées dominantes.
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
- revenir à Horner comme route principale dans ce round ;
- faire une simple taxonomie descriptive sans levier de comptage ;
- lancer une campagne computationnelle large ;
- présenter E_excess = O(C) comme acquis.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une taxonomie utile de E_excess est produite.
PASS-2 : une stratégie crédible de comptage global ou famille par famille est identifiée.
PASS-3 : un premier noyau de lemme collision-lite est formulé.
PASS-4 : au moins une famille supposée dominante est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R54 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R53 est utile si :
- la bonne variable de classement des collisions est clarifiée ;
- une fausse famille dominante est éliminée ;
- une version plus pauvre mais plus prouvable de collision-lite est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (taxonomie)
5. Résultats AXE B (double comptage)
6. Résultats AXE C (arbitrage)
7. Contrôle secondaire éventuel
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R54
14. Risques / limites
15. Verdict final avec score /10

---

# CONSIGNE FINALE
R53 doit transformer μ-lite collision d’une borne observée convaincante en programme combinatoire démontrable.
Le but n’est pas de mieux décrire μ.
Le but est d’identifier quelles collisions excédentaires fabriquent réellement E_excess, et comment les borner.
Chercher la bonne taxonomie et le bon comptage, pas la théorie finale complète.