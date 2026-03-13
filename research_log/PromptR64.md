

TYPE: P
OBJET CIBLÉ: somme de caractères décalée S_h sur le sous-groupe ⟨g²⟩ + borne racine carrée + chaîne S_h → D_∞ → ε-lite → K-lite
QUESTION CENTRALE: Peut-on faire monter le survivant de R63 d’un cran vers un premier schéma semi-prouvé utile, en attaquant directement la borne |S_h| ≤ C√p pour la somme de caractères décalée sur le sous-groupe d’indice 2, avec une réduction exacte vers des objets standards (complétion, caractères quadratiques, Jacobi, etc.) ou une autopsie précise si cette route échoue ?
RÉSULTAT ATTENDU MÊME EN CAS D’ÉCHEC: identifier exactement quelle décomposition de S_h est la bonne, quel terme résiduel reste vraiment difficile, et enterrer proprement toute route prestigieuse mais mal adaptée avec autopsie complète.

# BRIEF CLAUDE CODE — ROUND 64 (R64)

## Mission
Tu poursuis le projet Collatz dans la continuité stricte de R63.

### Contexte acquis
- R57–R59 ont transformé la base k=2 en problème de théorie des nombres bien posé via :
  - δ = b−a
  - c_δ = 1 + g·2^δ
  - N_r = #{δ : dlog(r/c_δ) ∈ [0, M−δ]}
- R59 a sélectionné la route prioritaire :
  - **Lemme K-lite via barrier counting**
  avec cible réaliste
  - max N_r ≤ C/p + α(M+1), α<1
- R60–R62 ont réduit le verrou à la sous-étape (c) :
  - contrôle du taux hit-hit
  - puis à une condition suffisante de type
    D_∞(d_δ) petit ⇒ τ<1 ⇒ α<1 ⇒ K-lite.
- R63 a enfin réduit ce verrou à un objet mathématique explicite :
  - en R3, via Erdős–Turán, il suffit de contrôler
    S_h = Σ_{t∈⟨g²⟩} χ_h(1+t)
  - où χ_h est un caractère du sous-groupe / du groupe multiplicatif adapté.
- R63 a montré que la vraie cible devient :
  - **borne racine carrée**
    |S_h| ≤ C√p
  - suffisante pour obtenir D_∞ = O(log p / √p), puis ε>0, puis K-lite.
- Les routes déjà enterrées restent enterrées :
  - pseudo-aléa naïf,
  - large sieve brut,
  - L²→L∞ générique,
  - combinatoire d’incidences comme route indépendante,
  - invocation vague de Weil/Bourgain sans réduction propre.
- Le risque stratégique est maintenant :
  - croire qu’“un grand théorème standard” s’applique automatiquement ;
  - ou rester au niveau du slogan “somme sur sous-groupe décalé” sans vraie décomposition exacte.

## Objectif de R64
R64 doit répondre à cette question centrale :

> Peut-on décomposer ou compléter rigoureusement la somme
>   S_h = Σ_{t∈⟨g²⟩} χ_h(1+t)
> de façon à la ramener à un objet standard réellement bornable par O(√p), ou à défaut isoler précisément le terme non standard qui constitue le vrai verrou restant ?

R64 doit être un round proof-oriented très centré.
Pas de dispersion.
Pas de campagne computationnelle large.
Le but est d’attaquer directement l’unique objet technique restant de la chaîne.

---

# ARCHITECTURE GÉNÉRALE

## Pièce principale unique
**Borne racine carrée sur la somme décalée S_h**

## Pièces auxiliaires autorisées mais subordonnées
- caractère quadratique η comme outil de complétion / indicatrice de ⟨g²⟩ ;
- sommes de Jacobi / Gauss / twists standards seulement si la réduction exacte le justifie ;
- cross conservé comme conséquence stratégique, sans nouvelle attaque frontale.

Le round doit dire explicitement si, après R64, l’objet restant est bien un standard attaquable, ou s’il subsiste un terme non standard plus profond.

---

# AXE A — INVESTIGATEUR / DÉCOMPOSITION EXACTE DE S_h
## Nom de travail
Comment réécrire S_h proprement ?

## Mission
Chercher la meilleure décomposition exacte de

S_h = Σ_{t∈⟨g²⟩} χ_h(1+t)

pour la ramener à des objets classiques ou quasi-classiques.

### Questions obligatoires
1. Quelle est la meilleure réécriture exacte de S_h ?
   - via l’indicatrice du sous-groupe d’indice 2 : (1+η(t))/2,
   - via complétion sur F_p^*,
   - via somme de Jacobi tordue,
   - via changement de variable,
   - autre
2. Cette réécriture sépare-t-elle S_h en :
   - terme principal standard,
   - terme résiduel non standard,
   - ou autre structure utile ?
3. Quels termes sont immédiatement bornables par des outils classiques ?
4. Quel terme résiduel, s’il existe, constitue le vrai verrou ?
5. Quelle est la formulation la plus exploitable pour un round suivant de preuve ?

### Livrables
- une décomposition exacte de S_h ;
- inventaire clair des termes standards vs non standards ;
- identification du vrai résidu difficile ;
- un premier sous-lemme si possible.

---

# AXE B — INVESTIGATEUR / OUTILS STANDARD RÉELLEMENT APPLICABLES
## Nom de travail
Quels théorèmes s’appliquent vraiment ?

## Mission
Vérifier rigoureusement quels outils standards s’appliquent réellement à la décomposition choisie, sans faire de prestige mathématique décoratif.

### Questions obligatoires
1. Une fois S_h décomposée, quels outils deviennent réellement valides ?
   - Jacobi sums,
   - Gauss sums,
   - Weil pour somme rationnelle sous caractère multiplicatif,
   - complétion + orthogonalité,
   - autre
2. Quels outils restent explicitement hors-cadre même après décomposition ?
3. Peut-on obtenir une borne non triviale rigoureuse tout de suite ?
4. Si la borne O(√p) complète n’est pas encore atteinte, quelle meilleure borne partielle peut-on établir ?
5. Quel outil paraît séduisant mais serait une redite déguisée ou une fausse application ?

### Livrables
- liste des outils vraiment applicables ;
- liste des faux amis / outils hors-cadre ;
- meilleure borne rigoureuse disponible à ce stade ;
- un premier sous-lemme candidat si possible.

---

# AXE C — INNOVATEUR / NOYAU PROUVABLE APRÈS R63
## Nom de travail
S_h-lite prouvable

## Mission
Proposer au plus 2 formulations candidates d’un premier noyau prouvable utile pour le verrou identifié par R63.

### Candidat 1
**S_h-lite standardisé**
La somme S_h se décompose en une combinaison finie d’objets standards déjà bornables, ce qui transforme le verrou en application contrôlée de théorèmes connus.

### Candidat 2
**S_h-lite avec résidu explicite**
La réduction standard ne ferme pas tout, mais elle isole un unique terme résiduel non standard de taille contrôlable ou clairement ciblé pour R65.

### Pour chaque candidat
1. énoncé intuitif ;
2. version semi-formelle ;
3. ce qu’il donnerait immédiatement ;
4. ce qu’il faudrait encore prouver ;
5. faiblesse potentielle ;
6. niveau estimé dans la Ladder of Proof.

## Règle obligatoire
À la fin :
- garder un seul survivant pour R65 ;
- éliminer l’autre explicitement ;
- justifier le choix par démontrabilité réelle, pas par élégance.

---

# AXE D — CONTRÔLE SECONDAIRE / CHAÎNE GLOBALE
## Nom de travail
Ne pas casser la logique S_h → D_∞ → ε → K-lite

## Mission
Sans faire du cross la cible principale, rappeler brièvement comment un progrès rigoureux sur S_h se réinjecte dans :
- D_∞,
- ε-lite,
- K-lite,
- base,
- puis cross.

### Questions obligatoires
1. Quel est le lien minimal “S_h bornée → D_∞ petit → τ<1 → α<1” à préserver ?
2. La nouvelle décomposition modifie-t-elle seulement l’objet technique, ou la chaîne logique entière ?
3. Quel rappel concis faut-il conserver pour éviter toute dérive future ?

### Livrables
- rappel propre de la chaîne de conséquences ;
- aucune nouvelle attaque frontale du cross ;
- aucune dérive hors du verrou principal.

---

# CONTRÔLE SECONDAIRE OPTIONNEL
Un seul micro-test ciblé est autorisé si et seulement s’il aide à départager :
- décomposition “tout standard” vs “standard + résidu”,
- ou deux formes concurrentes de la somme S_h après complétion.
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
- ressusciter pseudo-aléa naïf, large sieve brut, ou L²→L∞ générique sous un autre nom ;
- invoquer Weil/Bourgain/Jacobi sans décomposition exacte qui le justifie ;
- faire du cross la cible principale du round ;
- lancer une campagne computationnelle large ;
- présenter |S_h| ≤ C√p comme acquis tant que la décomposition utile n’est pas réellement verrouillée.

---

# CRITÈRES DE RÉUSSITE
PASS-1 : une décomposition exacte utile de S_h est obtenue.
PASS-2 : les outils réellement applicables sont identifiés proprement.
PASS-3 : un noyau de sous-lemme utile est formulé.
PASS-4 : au moins une fausse bonne route “prestigieuse” est éliminée avec autopsie complète.
PASS-5 : un survivant unique pour R65 est sélectionné.

# ÉCHEC UTILE
Même en cas d’échec, R64 est utile si :
- le vrai terme résiduel difficile est isolé ;
- une fausse application standard est éliminée ;
- une version plus pauvre mais plus prouvable de la borne sur S_h est isolée.

---

# FORMAT DE SORTIE ATTENDU
1. Résumé exécutif
2. Type du round + IVS
3. Méthode
4. Résultats AXE A (décomposition de S_h)
5. Résultats AXE B (outils applicables)
6. Résultats AXE C (S_h-lite)
7. Résultats AXE D (chaîne globale)
8. Contrôle secondaire éventuel
9. CEC inchangé
10. Objets concernés + Ladder of Proof
11. Ce qui est appris
12. Ce qui est enterré
13. Autopsie des pistes fermées
14. Survivant pour R65
15. Risques / limites
16. Verdict final avec score /10

---

# CONSIGNE FINALE
R64 doit attaquer directement l’unique objet technique restant issu de R63.
Le but n’est pas de redécrire D_∞.
Le but est de ramener S_h à une forme standard réellement bornable, ou d’isoler exactement le terme qui ne l’est pas encore.
Chercher la prochaine décomposition prouvable, pas la théorie finale complète.