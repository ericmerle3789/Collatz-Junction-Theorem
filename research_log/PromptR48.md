TYPE: P
OBJET CIBLÉ: SDL (Slice Decorrelation Lemma) + ρ(k,p)
QUESTION CENTRALE: Peut-on faire monter SDL d’un cran, de quantité mesurable conjecturale vers une première version semi-formalisée dans un régime naturel, en priorité quand ord_p(2) ≥ max_B+1 ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier le meilleur sous-régime prouvable pour SDL, et autopsier proprement toute tentative trop faible ou non ciblante.

# BRIEF CLAUDE CODE — ROUND 48 (R48)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R47.

### Contexte acquis
- R47 a arbitré entre les deux routes survivantes :
  - **Route prioritaire : Horner / SDL**
  - **Route secondaire : LSD**
- La décomposition par tranches est [PROUVÉE] :
  S(r) = Σ_{b₀=0}^{max_B} ω^{r·2^{b₀}} · S_{b₀}^{(k-1)}(r)
- La décomposition
  |S(r)|² = D(r) + X(r)
  avec terme diagonal + terme croisé est [PROUVÉE]
- Le ratio
  ρ(k,p) = [Σ_{r≥1} X(r)] / [Σ_{r≥1} D(r)]
  est identifié comme la quantité clé pour la décorrélation des tranches.
- SDL est actuellement [CONJECTURAL], mais possède :
  - une quantité mesurable,
  - une base k=2 prouvée,
  - un mécanisme plausible via diversité de phases.
- Le cas favorable identifié est :
  **ord_p(2) ≥ max_B+1**
  où toutes les phases 2^{b₀} mod p sont distinctes.

## Objectif de R48
R48 doit répondre à cette question centrale :

> Peut-on obtenir une première version semi-formalisée de SDL dans un sous-régime naturel, en priorité le régime de diversité maximale des phases ord_p(2) ≥ max_B+1 ?

R48 doit être un round proof-oriented centré.
Pas de dispersion entre routes.
Pas de campagne computationnelle large.
LSD n’intervient qu’en contrôle secondaire si cela aide à trancher un mécanisme.

---

# ARCHITECTURE GÉNÉRALE

## Route principale : Horner / SDL
Toute l’énergie principale doit aller à SDL.

## Route secondaire : LSD (garde-fou uniquement)
Autorisée uniquement si un micro-usage de LSD aide à :
- tester une intuition sur les termes croisés,
- ou exclure un faux mécanisme côté SDL.

Pas de développement parallèle complet de LSD dans R48.

---

# AXE A — INVESTIGATEUR SDL
## Nom de travail
Sous-régime prouvable pour ρ

## Mission
Étudier la quantité ρ(k,p) dans le régime favorable
ord_p(2) ≥ max_B+1,
et déterminer quelle version de “ρ petit” paraît réellement atteignable.

### Questions obligatoires
1. Dans le régime ord_p(2) ≥ max_B+1, qu’apporte exactement la distinction complète des phases ?
2. Peut-on reformuler Σ_{r≥1} X(r) de manière à exploiter l’orthogonalité des caractères ou une quasi-orthogonalité effective ?
3. Quelle est la meilleure cible réaliste à court terme ?
   - ρ → 0 pour p fixé, k grand
   - |ρ| ≤ c < 1
   - |ρ| ≤ O(1/max_B)
   - autre
4. Peut-on identifier une version moyenne de SDL plus accessible qu’une borne uniforme forte ?
5. Quelle dépendance résiduelle empêche encore une preuve directe ?

### Livrables
- une reformulation canonique de ρ ;
- le meilleur sous-régime favorable identifié ;
- une hiérarchie honnête des cibles de preuve.

---

# AXE B — INNOVATEUR SDL
## Nom de travail
SDL-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier lemme atteignable autour de SDL.

### Candidat 1
**SDL-lite (régime distinct phases)**  
Dans le régime ord_p(2) ≥ max_B+1, les termes croisés sont globalement dominés par les termes diagonaux :
|ρ(k,p)| ≤ η(k,p)
avec η petit dans un sens utile.

### Candidat 2
**Lemme de cancellation moyenne des tranches**  
Sans viser ρ uniforme, montrer que la somme agrégée des termes croisés est petite en moyenne sur r, ce qui suffit déjà à améliorer le contrôle de V.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement sur μ−1 ou WEL ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R49 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle.

---

# AXE C — CONTRÔLE SECONDAIRE LSD (OPTIONNEL, MINIMAL)
## Nom de travail
Garde-fou mécanique

## Mission
Seulement si utile, utiliser LSD pour vérifier si un faux mécanisme candidat côté SDL contredit la structure locale déjà connue des collisions.

### Autorisé
- un micro-test logique ou numérique ciblé
- aucune exploration large
- aucun développement d’une nouvelle couche LSD

### Interdit
- refaire une campagne h=2 / h=3
- ouvrir une seconde route complète

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
- relancer LSD comme route parallèle principale ;
- faire une campagne computationnelle de confort ;
- présenter SDL comme quasi-prouvé si seul un cas favorable est compris ;
- confondre “phases distinctes” avec “décorrélation automatique”.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une reformulation exploitable de ρ est isolée.
PASS-2 : un sous-régime naturel où SDL-lite paraît crédible est identifié proprement.
PASS-3 : un survivant unique autour de SDL est sélectionné pour R49.
PASS-4 : au moins une fausse intuition sur les termes croisés est éliminée avec autopsie.
PASS-5 : le lien exact entre “phases distinctes” et “cancellation” est clarifié.

# ÉCHEC UTILE
Même en cas d’échec, R48 est utile si :
- un sous-régime supposé facile est montré trompeur ;
- la bonne forme de petiteur pour ρ est clarifiée ;
- une version plus pauvre mais vraiment prouvable de SDL est isolée.

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A
5. Résultats AXE B
6. Contrôle secondaire LSD éventuel
7. Arbitrage final
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R49
14. Risques / limites
15. Verdict final avec score /10

# CONSIGNE FINALE
R48 doit faire franchir à SDL une vraie marche de maturité.
Le but n’est pas de “mesurer encore ρ”.
Le but est d’identifier la première version de SDL qui soit vraiment attaquable mathématiquement.
Chercher un lemme plus pauvre mais plus prouvable.