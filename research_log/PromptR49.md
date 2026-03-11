

TYPE: P
OBJET CIBLÉ: ACaL + V_within + covariances Z_{b0,b0'}
QUESTION CENTRALE: Peut-on faire monter ACaL d’un cran, de cadre exact de décomposition vers premier lemme semi-formalisé utile, en obtenant soit une borne inductive sur ΣV_{b0}/C², soit une borne/cancellation non triviale sur les covariances inter-tranches Z_{b0,b0'} ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier quelle moitié de ACaL est la plus attaquable mathématiquement, et enterrer proprement toute sous-route trop faible avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 49 (R49)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R48.

### Contexte acquis
- R48 a produit la reformulation structurelle majeure : **SDL = ANOVA exacte**.
- On dispose désormais de la décomposition :
  - V = Σ V_{b0} + V_between
  - ρ = V_between / V_within
- Le verrou n’est plus une “décorrélation vague”, mais le contrôle précis de :
  1. la somme des variances intra-tranches ΣV_{b0}
  2. les covariances inter-tranches Z_{b0,b0'}
- **ACaL** survit comme meilleur cadre : il absorbe SDL-lite et localise exactement où la preuve doit mordre.
- Les intuitions suivantes sont maintenant enterrées :
  - “phases distinctes suffisent”
  - “ρ = O(1/max_B)”
- Le risque stratégique est désormais clair : croire que la belle forme d’ACaL équivaut déjà à une vraie preuve.

## Objectif de R49
R49 doit répondre à cette question centrale :

> Quelle moitié de ACaL est la plus proche d’un premier lemme utile : le contrôle inductif de ΣV_{b0}/C², ou le contrôle/cancellation des covariances Z_{b0,b0'} ?

R49 doit être un round proof-oriented centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de sélectionner la prochaine vraie marche démontrable.

---

# ARCHITECTURE GÉNÉRALE

## Route principale
**ACaL** est l’unique route principale de R49.

## Deux sous-axes concurrents à départager
- **Sous-axe A** : borne inductive sur ΣV_{b0}/C²
- **Sous-axe B** : borne/cancellation sur Σ_{b0≠b0'} Z_{b0,b0'}

Le round doit trancher honnêtement lequel des deux sous-axes est le meilleur levier pour R50.

---

# AXE A — INVESTIGATEUR ACaL / WITHIN
## Nom de travail
Contrôle inductif des variances intra-tranches

## Mission
Étudier si la quantité

Σ V_{b0} / C²

peut être contrôlée par récurrence en k, ou par une réduction propre aux objets de taille k−1.

### Questions obligatoires
1. Peut-on exprimer chaque V_{b0} en fonction d’un problème de même nature à taille k−1 ?
2. La somme sur b0 interagit-elle favorablement avec la combinatoire des tailles de tranches ?
3. Existe-t-il une borne naturelle du type :
   - ΣV_{b0}/C² = o(1)
   - ΣV_{b0}/C² ≤ A/max_B
   - ΣV_{b0}/C² ≤ A/C^β
   - autre
4. Quelle partie est structurellement inductive, et quelle partie casse l’induction ?
5. Quel est le plus petit énoncé semi-formel utile sur le terme within ?

### Livrables
- reformulation canonique de ΣV_{b0}
- verdict honnête sur la viabilité de l’induction
- un premier sous-lemme candidat si possible

---

# AXE B — INVESTIGATEUR ACaL / BETWEEN
## Nom de travail
Covariances inter-tranches

## Mission
Étudier la structure des covariances

Z_{b0,b0'}

et déterminer si une borne non triviale ou une cancellation agrégée paraît atteignable.

### Questions obligatoires
1. Quelle est la forme canonique la plus exploitable de Z_{b0,b0'} ?
2. Peut-on distinguer des régimes plus favorables selon :
   - |b0-b0'|
   - ord_p(2)
   - taille relative des tranches
   - autres paramètres naturels
3. Cauchy-Schwarz est trop faible ; quel raffinement paraît le plus crédible ?
   - quasi-orthogonalité
   - oscillation moyenne
   - cancellation par paires
   - autre
4. Quelle version affaiblie mais utile pourrait être prouvable ?
5. Le contrôle du between paraît-il plus prometteur que le contrôle du within ?

### Livrables
- reformulation canonique de ΣZ_{b0,b0'}
- hiérarchie honnête des régimes
- un premier sous-lemme candidat si possible

---

# AXE C — INNOVATEUR / ARBITRAGE DES DEUX MOITIÉS
## Nom de travail
Premier noyau prouvable d’ACaL

## Mission
À partir des deux analyses précédentes, proposer au plus 2 formulations candidates d’un premier noyau prouvable.

### Candidat 1
**ACaL-within-lite**
Un contrôle partiel du terme within suffit déjà à donner une amélioration utile sur V/C² ou μ−1 dans un régime naturel.

### Candidat 2
**ACaL-between-lite**
Une cancellation partielle des covariances inter-tranches suffit déjà à faire monter ACaL d’un cran.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R50 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité, pas par élégance.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test numérique ciblé est autorisé si et seulement s’il aide à départager within vs between.
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
- relancer SDL-lite sous un autre nom ;
- garder artificiellement les deux sous-axes s’il y a un gagnant net ;
- faire une campagne computationnelle large ;
- présenter ACaL comme quasi-prouvé.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une des deux moitiés de ACaL est clairement identifiée comme plus attaquable.
PASS-2 : un premier sous-lemme within-lite ou between-lite est formulé.
PASS-3 : au moins une fausse intuition sur within ou between est éliminée avec autopsie.
PASS-4 : un survivant unique pour R50 est sélectionné proprement.
PASS-5 : la dette théorique d’ACaL est mieux localisée.

# ÉCHEC UTILE
Même en cas d’échec, R49 est utile si :
- le bon sous-axe est mieux hiérarchisé ;
- une fausse piste séduisante est éliminée ;
- une version plus pauvre mais plus prouvable d’ACaL est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (within)
5. Résultats AXE B (between)
6. Résultats AXE C (arbitrage)
7. Contrôle secondaire éventuel
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R50
14. Risques / limites
15. Verdict final avec score /10

---

# CONSIGNE FINALE
R49 doit transformer ACaL d’un beau cadre exact en prochain levier démontrable.
Le but n’est pas de raffiner la description.
Le but est de savoir où la preuve peut mordre d’abord : within ou between.
Chercher le bon prochain lemme, pas la théorie finale complète.