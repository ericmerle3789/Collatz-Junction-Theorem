

TYPE: P
OBJET CIBLÉ: TQL-mu direct + μ du problème standard + route Horner en régime R1
QUESTION CENTRALE: Peut-on faire monter TQL-mu direct d’un cran vers un premier lemme semi-prouvé utile, en bornant μ−1 pour le problème standard simplexe/Horner dans le sous-régime favorable R1, sans dépendre d’une induction naïve ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier la meilleure forme prouvable de borne sur μ−1 en régime R1, et enterrer proprement toute formulation trop forte ou mal ciblée avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 52 (R52)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R51.

### Contexte acquis
- R50 a réuni between et within sous une même cible structurelle : **TQL**.
- R51 a produit les avancées décisives suivantes :
  - **tail = sous-problème rotaté** [PROUVÉ]
  - la bonne métrique pour TQL est **μ**, pas D∞
  - la cascade naïve k→k−1 est [RÉFUTÉE]
  - le survivant est **TQL-mu direct**
- La forme candidate de travail est :
  - μ − 1 ≤ K · p / C
  dans un sous-régime naturel favorable.
- R51 a indiqué la bonne réduction :
  - revenir au **problème standard** (simplexe/Horner)
  - puis attaquer μ directement
  - en priorité dans le **régime R1**.
- Le risque stratégique est maintenant :
  - relancer des formulations trop générales ;
  - ou viser trop fort trop tôt sans verrouiller la première borne utile sur μ.

## Objectif de R52
R52 doit répondre à cette question centrale :

> Peut-on obtenir une première charpente crédible pour une borne du type μ−1 ≤ K·p/C dans le problème standard, au moins dans le sous-régime R1, via la route Horner ou une reformulation équivalente plus attaquable ?

R52 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de produire la première marche démontrable utile vers TQL-mu direct.

---

# ARCHITECTURE GÉNÉRALE

## Route principale unique
**TQL-mu direct via problème standard / Horner**

## Deux sous-axes concurrents à départager
- **Sous-axe A** : borne directe sur μ−1 via second moment / collisions dans le problème standard
- **Sous-axe B** : borne indirecte sur μ−1 via décomposition Horner / slicing / cancellation structurée

Le round doit trancher quelle formulation donne la meilleure prochaine marche pour R53.

---

# AXE A — INVESTIGATEUR / μ DANS LE PROBLÈME STANDARD
## Nom de travail
Quelle borne sur μ−1 est réaliste en R1 ?

## Mission
Étudier directement la quantité

μ − 1 = pV / C²

pour le problème standard, et déterminer la meilleure forme de borne réaliste à court terme dans le sous-régime R1.

### Questions obligatoires
1. Quelle reformulation canonique de μ−1 est la plus exploitable dans le problème standard ?
   - via V = M₂ − C²/p
   - via second moment des collisions
   - via Σ|S(r)|²
   - via une autre quantité équivalente
2. Quelle borne paraît réaliste à court terme en régime R1 ?
   - μ−1 ≤ K·p/C
   - μ−1 ≤ K·p·log C / C
   - μ−1 = o(1)
   - autre
3. Quelle partie du régime R1 est réellement utilisée ?
   - ord_p(2)
   - max_B
   - taille des tranches
   - autres paramètres naturels
4. Quel est le plus petit énoncé utile déjà assez fort pour réinjecter dans TQL-mu ?
5. Quelle obstruction principale empêche encore une borne plus propre ?

### Livrables
- reformulation canonique de μ−1 dans le problème standard ;
- meilleure borne cible réaliste ;
- obstacles localisés précisément ;
- un premier noyau de lemme si possible.

---

# AXE B — INVESTIGATEUR / HORNER POUR μ
## Nom de travail
Horner comme machine à borner μ

## Mission
Étudier si la décomposition Horner / slicing permet de contrôler le second moment ou la variance du problème standard en régime R1.

### Questions obligatoires
1. Quelle est la forme la plus utile de la décomposition Horner pour attaquer μ et non plus seulement S(r) ?
2. Le slicing fournit-il une décomposition naturelle de M₂ ou de V exploitable analytiquement ?
3. Peut-on transformer les termes croisés issus de Horner en quantités avec cancellation ou quasi-orthogonalité utilisable ?
4. Quelle version affaiblie de l’argument Horner serait déjà utile ?
5. Quelle est la plus petite sortie semi-formelle atteignable par cette route ?

### Livrables
- décomposition Horner adaptée à μ ;
- verdict honnête sur la viabilité de la route ;
- un sous-lemme Horner-lite si possible.

---

# AXE C — INNOVATEUR / PREMIER NOYAU PROUVABLE POUR TQL-MU DIRECT
## Nom de travail
μ-lite prouvable en régime R1

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile.

### Candidat 1
**μ-lite direct**
Dans le régime R1, on obtient une borne explicite du type
μ−1 ≤ K·p/C
ou une variante légèrement plus faible mais déjà réinjectable dans TQL-mu.

### Candidat 2
**μ-lite Horner**
Dans le régime R1, la structure Horner permet une borne intermédiaire sur V ou M₂ qui implique une version faible mais utile de TQL-mu.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R53 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il départage deux formes de borne ou deux usages du régime R1.
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
- relancer la cascade naïve k→k−1 comme route principale ;
- revenir à D∞ comme métrique cible ;
- lancer une campagne computationnelle large ;
- présenter TQL-mu direct comme quasi-prouvé.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une reformulation exploitable de μ−1 dans le problème standard est isolée.
PASS-2 : une borne cible réaliste en régime R1 est sélectionnée proprement.
PASS-3 : un premier noyau de lemme μ-lite est formulé.
PASS-4 : au moins une formulation trop forte ou mal ciblée est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R53 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R52 est utile si :
- le bon usage du régime R1 est clarifié ;
- une route Horner trop optimiste est recalibrée ;
- une version plus pauvre mais plus prouvable de μ-lite est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (μ standard)
5. Résultats AXE B (Horner pour μ)
6. Résultats AXE C (arbitrage)
7. Contrôle secondaire éventuel
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R53
14. Risques / limites
15. Verdict final avec score /10

---

# CONSIGNE FINALE
R52 doit transformer TQL-mu direct d’un bon programme en première marche démontrable réelle.
Le but n’est pas de raconter encore mieux μ.
Le but est d’identifier la première borne utile sur μ−1 en régime R1.
Chercher le bon lemme μ-lite, pas la théorie finale complète.