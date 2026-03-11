

TYPE: P
OBJET CIBLÉ: ACaL-between-lite + ρ + excès de collisions inter-tranches Z
QUESTION CENTRALE: Peut-on faire monter ACaL-between-lite d’un cran vers un premier lemme semi-prouvé utile, en obtenant une borne non triviale sur |ρ| ou sur la somme des excès de collisions inter-tranches Z_{b0,b0'} dans un régime naturel favorable ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier le meilleur sous-régime où une borne sur le between est réellement attaquable, et enterrer proprement toute formulation trop ambitieuse avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 50 (R50)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R49.

### Contexte acquis
- R48 a donné la reformulation structurante : **SDL = ANOVA exacte**.
- R49 a tranché l’arbitrage interne à ACaL :
  - **within** = partie encore trop dure, proche d’une future GEH sur sous-intervalles
  - **between** = partie la plus attaquable immédiatement
- La quantité centrale est désormais :
  - ρ = V_between / V_within
- Le bon objet local pour le between est :
  - Z_{b0,b0'} = M₂(b0,b0') − C_{b0}C_{b0'}/p
  c’est-à-dire l’**excès de collisions inter-tranches** par rapport à l’uniforme.
- R49 a montré :
  - V_between n’a pas de signe fixe
  - V_{b0}/C_{b0}² ne se compare pas uniformément à V/C²
  - la bonne route immédiate est **ACaL-between-lite**.
- Le risque stratégique est maintenant : viser trop fort trop tôt (borne globale/uniforme), alors qu’un sous-régime favorable pourrait déjà fournir la première vraie marche démontrable.

## Objectif de R50
R50 doit répondre à cette question centrale :

> Peut-on obtenir une première borne utile sur le between — soit une borne sur |ρ|, soit une borne/cancellation sur Σ_{b0≠b0'} Z_{b0,b0'} — dans un sous-régime naturel où la structure des tranches est particulièrement favorable ?

R50 doit être un round proof-oriented centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est de produire le premier lemme utilisable sur la moitié “between” d’ACaL.

---

# ARCHITECTURE GÉNÉRALE

## Route unique
**ACaL-between-lite** est l’unique route principale de R50.

## Deux sous-axes concurrents à départager
- **Sous-axe A** : borne sur |ρ| dans un régime favorable
- **Sous-axe B** : borne/cancellation sur Σ Z_{b0,b0'} dans un régime favorable

Le round doit trancher laquelle de ces deux formulations est la plus démontrable et la plus utile pour R51.

---

# AXE A — INVESTIGATEUR / RÉGIMES FAVORABLES DU BETWEEN
## Nom de travail
Où le between devient-il attaquable ?

## Mission
Identifier les sous-régimes naturels où les interactions inter-tranches devraient être les plus contrôlables.

### Questions obligatoires
1. Quels paramètres semblent gouverner le between ?
   - ord_p(2)
   - max_B
   - séparation |b0−b0'|
   - taille relative des tranches C_{b0}
   - autres quantités naturelles
2. Quel est le régime le plus prometteur ?
   - ord_p(2) ≥ max_B+1
   - ord_p(2) très grand vs max_B
   - tranches très séparées
   - régime moyen sur b0,b0'
   - autre
3. La difficulté vient-elle surtout des petites séparations de tranches, des petites ordres multiplicatifs, ou d’un autre effet ?
4. Peut-on déjà hiérarchiser les paires (b0,b0') en “faciles”, “dures”, “pathologiques” ?
5. Quel est le plus petit sous-régime où un lemme between-lite paraît crédible ?

### Livrables
- hiérarchie claire des régimes favorables/difficiles ;
- sélection d’un sous-régime prioritaire ;
- obstacles localisés précisément.

---

# AXE B — INVESTIGATEUR / STRUCTURE DE Z_{b0,b0'}
## Nom de travail
Excès de collisions inter-tranches

## Mission
Analyser la structure exacte de

Z_{b0,b0'} = M₂(b0,b0') − C_{b0}C_{b0'}/p

et déterminer quelle forme de borne est la plus réaliste.

### Questions obligatoires
1. Quelle est la reformulation canonique la plus exploitable de Z_{b0,b0'} ?
   - collisions entre deux familles de polynômes/tranches
   - somme de caractères croisée
   - corrélation entre images résiduelles
   - autre
2. Peut-on obtenir une borne non triviale meilleure que Cauchy-Schwarz sur Z_{b0,b0'} dans un sous-régime ?
3. Une cancellation agrégée sur Σ_{b0≠b0'} Z_{b0,b0'} paraît-elle plus accessible qu’une borne paire par paire ?
4. La structure
   P_B = 2^{b0} + g·T(B_tail)
   permet-elle de séparer suffisamment l’effet de b0 de celui de la queue ?
5. Quelle forme de résultat est la plus réaliste à court terme ?
   - |ρ| < 1 dans un régime naturel
   - Σ Z ≤ θ·Σ C_{b0}C_{b0'}/p avec θ<1
   - moyenne des Z petite
   - autre

### Livrables
- reformulation canonique de Z ;
- meilleure forme de borne réaliste ;
- verdict honnête sur paire-à-paire vs agrégé.

---

# AXE C — INNOVATEUR / PREMIER LEMME BETWEEN-LITE
## Nom de travail
Premier noyau prouvable pour ACaL-between-lite

## Mission
Proposer au plus 2 formulations candidates d’un premier lemme between-lite réellement attaquable.

### Candidat 1
**ρ-lite**
Dans un sous-régime naturel favorable, |ρ(k,p)| ≤ c avec c < 1, ou |ρ(k,p)| → 0 dans un sens utile.

### Candidat 2
**Z-lite agrégé**
Dans un sous-régime naturel favorable, la somme agrégée des excès de collisions inter-tranches est contrôlée assez fortement pour donner une amélioration utile sur V_between.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R51 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il départage deux sous-régimes ou deux formes de borne.
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
- revenir au within comme route principale dans ce round ;
- supposer qu’une borne uniforme globale est le bon premier objectif ;
- lancer une campagne computationnelle large ;
- présenter ACaL-between-lite comme quasi-prouvé.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : un sous-régime favorable pour le between est identifié proprement.
PASS-2 : une reformulation exploitable de Z ou de ρ est isolée.
PASS-3 : un premier lemme between-lite réaliste est formulé.
PASS-4 : au moins une fausse intuition sur le between est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R51 est sélectionné proprement.

# ÉCHEC UTILE
Même en cas d’échec, R50 est utile si :
- le bon sous-régime est mieux hiérarchisé ;
- une cible trop ambitieuse est éliminée ;
- une version plus pauvre mais plus prouvable du between est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (régimes favorables)
5. Résultats AXE B (structure de Z)
6. Résultats AXE C (arbitrage)
7. Contrôle secondaire éventuel
8. CEC inchangé
9. Objets concernés + Ladder of Proof
10. Ce qui est appris
11. Ce qui est enterré
12. Autopsie des pistes fermées
13. Survivant pour R51
14. Risques / limites
15. Verdict final avec score /10

---

# CONSIGNE FINALE
R50 doit faire franchir à ACaL-between-lite sa première vraie marche de preuve.
Le but n’est pas de décrire encore mieux le between.
Le but est d’identifier le premier lemme démontrable utile sur cette moitié d’ACaL.
Chercher le bon sous-régime et la bonne forme de borne, pas la théorie finale complète.