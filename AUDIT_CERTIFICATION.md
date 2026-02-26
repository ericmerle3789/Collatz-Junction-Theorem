# PROTOCOLE D'AUDIT DE CERTIFICATION — Niveau Post-Doctoral
# Projet : Barrières Entropiques et Non-Surjectivité — Théorème de Jonction

**Date** : 26 février 2026
**Auditeur** : Bureau de contrôle de certification (IA)
**Classification** : CRITIQUE — Responsabilité de vol (certification complète)

---

## PROTOCOLE DE VÉRIFICATION

Le présent protocole couvre **9 axes d'inspection** systématiques, numérotés P0 à P8.
Chaque axe contient des points de contrôle (PC) identifiés par la notation `Pn.m`.
Chaque non-conformité est classée selon sa **gravité** :

| Niveau | Symbole | Signification |
|--------|---------|---------------|
| **BLOQUANT** | 🔴 | Erreur factuelle, incohérence qui invalide un résultat |
| **MAJEUR** | 🟠 | Incohérence inter-fichiers, confusion susceptible d'induire en erreur |
| **MINEUR** | 🟡 | Problème de forme, convention, documentation incomplète |
| **INFO** | 🔵 | Observation, recommandation d'amélioration |

---

## P0 — INTÉGRITÉ STRUCTURELLE (« L'avion existe-t-il ? »)

### PC 0.1 — Inventaire des fichiers

| Composant | Fichier | Présent | État |
|-----------|---------|---------|------|
| Paper (contenu) | `paper/preprint.md` | ✅ | 493 lignes, complet |
| Paper (LaTeX) | `paper/preprint.tex` | ✅ | 182 lignes, **stub** |
| Paper (PDF) | `paper/Merle_2026_*.pdf` | ✅ | Binaire |
| Lean principal | `lean/JunctionTheorem.lean` | ✅ | 626 lignes |
| Lean Syracuse | `lean/SyracuseHeight.lean` | ✅ | 463 lignes |
| Lean BinomialEntropy | `lean/BinomialEntropy.lean` | ✅ | 165 lignes |
| Lean EntropyBound | `lean/EntropyBound.lean` | ✅ | 66 lignes |
| Lean ConcaveTangent | `lean/ConcaveTangent.lean` | ✅ | 72 lignes |
| Lean LegendreApprox | `lean/LegendreApprox.lean` | ✅ | 76 lignes |
| Script Python | `scripts/verify_nonsurjectivity.py` | ✅ | 120 lignes |
| Research logs | `research_log/phase10c–13` | ✅ | 16 fichiers |
| README | `README.md` | ✅ | 133 lignes |
| License | `LICENSE` | ✅ | MIT |

### PC 0.2 — Chaîne de dépendances Lean

```
JunctionTheorem.lean
  ├── BinomialEntropy.lean  (aucune dépendance interne)
  ├── EntropyBound.lean     (← BinomialEntropy, ConcaveTangent)
  └── ConcaveTangent.lean   (aucune dépendance interne)

SyracuseHeight.lean
  └── LegendreApprox.lean   (aucune dépendance interne)
```

**Verdict P0** : ✅ Structure complète, pas de fichier manquant, dépendances cohérentes.

---

## P1 — COHÉRENCE DES CONSTANTES ET VARIABLES (« Le carburant est-il le bon ? »)

### PC 1.1 — La constante γ (gap entropie-module)

| Fichier | Formule | Valeur | Unité |
|---------|---------|--------|-------|
| `preprint.md` §3.3 | γ = 1 − h(ln 2 / ln 3) | 0.05004447281167 | **bits** |
| `preprint.tex` abstract | γ = 1 − h(1/log₂ 3) | ≈ 0,0500 | **bits** |
| `JunctionTheorem.lean` l.78 | gamma = 1 - binaryEntropy(log2/log3) | — | **bits** |
| `verify_nonsurjectivity.py` l.76 | gamma = 1.0 - h_alpha | 0.050044472812 | **bits** |
| `README.md` | γ ≈ 0.0500 | 0.0500 | **bits** |

**Verdict** : ✅ γ cohérent dans tous les fichiers du livrable final (preprint + Lean + script).

### 🟠 NC-1.1 — Valeur erronée de γ dans les research logs

| Fichier | Formule utilisée | Valeur | Problème |
|---------|-----------------|--------|----------|
| `phase10j` l.23 | γ = ln(3) − h(log₂(3)) | 0.05498 | **Formule incorrecte** |
| `phase10k` l.16 | γ = 0.0549 | 0.0549 | Valeur fausse |
| `phase10l` l.41,401,411,459,536,575,718 | γ = 0.0549 | 0.0549 | Propagation |
| `phase10m` l.118 | γ = ln(3) − h(log₂(3)) = 0.054979 | 0.054979 | **Calcul erroné** |
| `phase11a` l.370 | γ = 0.0549 | 0.0549 | Propagation |
| `phase11b` l.237 | γ = 0.0549 | 0.0549 | Propagation |

**Diagnostic** : Les research logs calculent γ = ln(3) − log₂(3) × h_nats(α) = 0.0549, ce qui est un **mélange d'unités** (nats × bits). La formule `h(log₂(3))` est en outre **non définie** car log₂(3) = 1.585 > 1, hors du domaine de Shannon [0,1]. Phase 12 corrige cette erreur avec un avertissement explicite.

**Gravité** : 🟠 MAJEUR — La valeur 0.0549 apparaît dans 6 fichiers de logs. Bien que le preprint final utilise la bonne valeur, un lecteur consultant les logs sera induit en erreur.

### PC 1.2 — Module cristallin d(k=17)

| Fichier | Valeur de d | Correcte ? |
|---------|-------------|------------|
| `preprint.md` §4.2 table l.216 | 5 077 565 | ✅ |
| `JunctionTheorem.lean` l.253,260 | 5 077 565 | ✅ |
| `verify_nonsurjectivity.py` | 5 077 565 (calculé) | ✅ |

### 🔴 NC-1.2 — Valeur fausse de d(k=17) dans preprint.md §4.4

**Fichier** : `paper/preprint.md`, ligne 270
**Texte** : « d = 7 340 033 = 2²⁷ − 3¹⁷ »
**Calcul** : 2²⁷ − 3¹⁷ = 134 217 728 − 129 140 163 = **5 077 565** ≠ 7 340 033

**Gravité** : 🔴 BLOQUANT — Le texte affirme une identité arithmétique fausse dans la section d'analyse des exceptions diophantiennes. Le tableau §4.2 donne la bonne valeur (5 077 565), créant une **contradiction interne** dans le même fichier.

### PC 1.3 — Convergents de log₂ 3

Calcul indépendant de la fraction continue [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, ...] :

| Index n | q_n (k) | p_n (S) | Lean list | Preprint | Match |
|---------|---------|---------|-----------|----------|-------|
| 0 | 1 | 1 | 1 | — | ✅ |
| 1 | 1 | 2 | 1 | 1 | ✅ |
| 2 | 2 | 3 | 2 | — | ✅ |
| 3 | 5 | 8 | 5 | 5 | ✅ |
| 4 | 12 | 19 | 12 | — | ✅ |
| 5 | 41 | 65 | 41 | 41 | ✅ |
| 6 | 53 | 84 | 53 | — | ✅ |
| 7 | 306 | 485 | 306 | 306 | ✅ |
| 8 | 665 | 1054 | 665 | — | ✅ |
| 9 | 15601 | 24727 | 15601 | 15601 | ✅ |
| 10 | 31867 | 50508 | 31867 | — | ✅ |
| 11 | 79335 | 125743 | 79335 | 79335 | ✅ |

**Verdict** : ✅ Convergents parfaitement cohérents entre `SyracuseHeight.lean` (convergentDenominators_12) et `preprint.md`.

### PC 1.4 — Exceptions {3, 5, 17}

| Fichier | Exceptions | Match |
|---------|-----------|-------|
| `preprint.md` §4.2 | {3, 5, 17} | ✅ |
| `JunctionTheorem.lean` exceptions_below_68 | {3, 5, 17} | ✅ |
| `verify_nonsurjectivity.py` | {3, 5, 17} | ✅ |
| `README.md` | {3, 5, 17} | ✅ |
| `phase12` | {3, 5, 17} | ✅ |

**Verdict** : ✅ Exceptions cohérentes partout.

### PC 1.5 — Seuils K₀ = 18 et K_SdW = 68

| Fichier | K₀ | K_SdW | Match |
|---------|-----|-------|-------|
| `preprint.md` | 18 | 68 | ✅ |
| `preprint.tex` | 18 | 68 | ✅ |
| `JunctionTheorem.lean` | 18 | 68 | ✅ |
| `README.md` | 18 | 68 | ✅ |

**Verdict** : ✅ Seuils cohérents.

### PC 1.6 — Valeurs numériques du tableau §4.2

| k | S | C (calculé) | C (preprint) | d (calculé) | d (preprint) | C/d (calculé) | C/d (preprint) |
|---|---|-------------|--------------|-------------|--------------|---------------|----------------|
| 3 | 5 | 6 | 6 | 5 | 5 | 1.2000 | 1.20 ✅ |
| 5 | 8 | 35 | 35 | 13 | 13 | 2.6923 | 2.69 ✅ |
| 17 | 27 | 5 311 735 | 5 311 735 | 5 077 565 | 5 077 565 | 1.0461 | 1.05 ✅ |

**Verdict** : ✅ Tableau §4.2 numériquement exact.

### PC 1.7 — Valeurs du tableau §5.4

| Convergent | k | S | log₂(C/d) calculé | log₂(C/d) preprint | Match |
|-----------|---|---|-------------------|-------------------|-------|
| q₃ | 5 | 8 | +1.43 | +1.43 | ✅ |
| q₅ | 41 | 65 | −0.75 | −0.75 | ✅ |
| q₇ | 306 | 485 | −19.7 | −19.7 | ✅ |

**Verdict** : ✅ Tableau §5.4 vérifié.

---

## P2 — VÉRIFICATION MATHÉMATIQUE (« Le moteur tourne-t-il correctement ? »)

### PC 2.1 — Équation de Steiner

**Énoncé** : n₀ · (2^S − 3^k) = Σ 3^{k−1−i} · 2^{A_i}

- Preprint §1.2 : ✅ Correctement énoncée
- Lean `steiner_equation` : ✅ Complètement prouvée (207 lignes de preuve)
- Méthode : somme télescopique + linear_combination

**Verdict** : ✅ Prouvée formellement.

### PC 2.2 — Théorème de Non-Surjectivité (Thm 1)

**Énoncé** : Pour k ≥ 18 avec d > 0 : C(S−1, k−1) < d

- Vérification numérique : ✅ Script Python vérifie pour k ∈ [18, 500]
- Lean `crystal_nonsurjectivity` : ⚠️ **1 sorry restant**
- Lean `deficit_linear_growth` : ✅ Prouvé (borne tangente)
- Borne tangente suffisante pour k ≥ ~190, insuffisante pour k ∈ [18, 190)

### 🟡 NC-2.1 — Sorry résiduel dans crystal_nonsurjectivity

Le théorème principal `crystal_nonsurjectivity` contient 1 sorry. La borne prouvée `deficit_linear_growth` donne log₂(C) ≤ S·(1−γ) + log₂(S), ce qui est insuffisant pour k ∈ [18, ~190) car la correction de Stirling (~log₂√(2πnp(1−p))) n'est pas formalisée.

**Gravité** : 🟡 MINEUR du point de vue mathématique (la preuve est complète sur papier et vérifiée numériquement), mais notable pour la certification formelle Lean.

### PC 2.3 — Théorème de Jonction (Thm 2)

**Énoncé** : Pour tout k ≥ 2, obstruction computationnelle (k < 68) OU entropique (k ≥ 18)

- Couverture : [1, 67] ∪ [18, ∞) = [1, ∞) ✅
- Lean `junction_unconditional` : ✅ Prouvé
- Lean `full_coverage` : ✅ Prouvé par `omega`

**Verdict** : ✅

### PC 2.4 — Hypothèse (H) et exclusion de 0

- Lean `QuasiUniformity` : ✅ Définie comme classe de types
- Lean `zero_exclusion_conditional` : ✅ Prouvé (conditionnel sur QuasiUniformity)
- Lean `no_positive_cycle` : ✅ Prouvé (combine SdW + exclusion)

**Verdict** : ✅ Correctement formalisé comme résultat conditionnel.

### PC 2.5 — Équation maîtresse (Syracuse Height)

- Lean `master_equation_positive` : ✅ Prouvé (189 lignes)
- Lean `master_equation_negative` : ✅ Prouvé
- Méthode : somme télescopique + permutation cyclique via Equiv.sum_comp

**Verdict** : ✅

### PC 2.6 — Bornes d'énergie

- Lean `energy_upper_bound` : ✅ Prouvé (ε ≤ k/(3n₀))
- Lean `energy_lower_bound` : ✅ Prouvé
- Utilise log(1+x) ≤ x et monotonie

**Verdict** : ✅

### PC 2.7 — Borne pour les non-convergents

- Lean `gap_non_convergent` : ✅ Prouvé via LegendreApprox
- `|Δ(k,S)| ≥ log(2)/(2k)` pour k non convergent

**Verdict** : ✅

### PC 2.8 — Inégalité de la droite tangente

- Lean `binEntropy_le_tangent` : ✅ Prouvé
- Lean `concave_le_tangent` : ✅ Prouvé (cas gauche + droite)
- Utilise ConcaveOn de Mathlib

**Verdict** : ✅

### PC 2.9 — γ > 0

- Lean `gamma_pos` : ✅ Prouvé
- Utilise `binary_entropy_lt_one` et `log_two_div_log_three_ne_half` (3 ≠ 4)

**Verdict** : ✅

### PC 2.10 — Croissance linéaire du déficit

- Lean `deficit_linear_growth` : ✅ Prouvé (158 lignes)
- log₂(C) ≤ S·(1−γ) + log₂(S)

**Verdict** : ✅

---

## P3 — VÉRIFICATION LEAN 4 (« Les instruments de bord fonctionnent-ils ? »)

### PC 3.1 — Census des sorry

| Fichier | Sorry | Axiomes | Tout prouvé ? |
|---------|-------|---------|--------------|
| `JunctionTheorem.lean` | **1** (crystal_nonsurjectivity) | 1 (simons_de_weger) | ❌ |
| `SyracuseHeight.lean` | 0 | 0 | ✅ |
| `BinomialEntropy.lean` | 0 | 0 | ✅ |
| `EntropyBound.lean` | 0 | 0 | ✅ |
| `ConcaveTangent.lean` | 0 | 0 | ✅ |
| `LegendreApprox.lean` | 0 | 0 | ✅ |

**Total** : 1 sorry + 1 axiome sur 6 fichiers.

### PC 3.2 — Axiome simons_de_weger

L'axiome `simons_de_weger` encode le résultat publié de Simons et de Weger (Acta Arithmetica 117, 2005).
C'est une pratique standard en formalisation Lean de marquer les résultats publiés vérifiés indépendamment comme axiomes.

**Verdict** : ✅ Usage légitime.

### PC 3.3 — Toolchain et dépendances

- Lean 4 version : v4.29.0-rc2 (release candidate)
- Mathlib : branche `master` (non verrouillée !)

### 🟡 NC-3.1 — Mathlib non verrouillée

`lakefile.lean` l.14-15 : `require mathlib from git ... @ "master"`

Utiliser la branche `master` de Mathlib sans hash de commit signifie que le build peut casser à tout moment si Mathlib fait un breaking change.

**Recommandation** : Verrouiller sur un commit spécifique de Mathlib.
**Gravité** : 🟡 MINEUR — Le `lake-manifest.json` verrouille de facto, mais le `lakefile.lean` ne reflète pas ce verrou.

### 🟡 NC-3.2 — Lean version release candidate

v4.29.0-**rc2** est une release candidate, pas une version stable. Pour une certification, une version stable est préférable.

**Gravité** : 🟡 MINEUR

### PC 3.4 — Cohérence du sorry census documenté

Le header de `JunctionTheorem.lean` (l.19-33) documente 1 sorry restant.
Vérification indépendante : `sorry` apparaît une seule fois (l.234). ✅

Le header de `SyracuseHeight.lean` (l.17-27) documente 0 sorry.
Vérification indépendante : aucun `sorry` dans le fichier. ✅

**Verdict** : ✅ Census auto-documenté exact.

---

## P4 — COHÉRENCE INTER-COMPOSANTS (« Les pièces s'emboîtent-elles ? »)

### PC 4.1 — Définition de corrSum

| Composant | Formule | Cohérent |
|-----------|---------|----------|
| Preprint §1.2 | Σ 3^{k−1−i} · 2^{A_i} | ✅ |
| Lean corrSum | Σ 3^(k-1-i.val) * 2^(A i) | ✅ |
| Phase 12 §1.2 | Σ 3^{k-1-i} · 2^{A_i} | ✅ |
| Script Python (implicite) | — | N/A |

### PC 4.2 — Définition de Comp(S, k)

| Composant | Définition | |Comp| | Cohérent |
|-----------|-----------|-------|----------|
| Preprint §2.1 | Suites strictement croissantes 0=A₀<...<A_{k-1}≤S-1 | C(S-1, k-1) | ✅ |
| Lean Composition | A : Fin k → ℕ, A₀=0, Σ A = S-k | C(S-1, k-1) | ✅ |
| Phase 12 §1.2 | Composition de S-k en k parts ≥ 0 avec A₀=0 | C(S-1, k-1) | ✅ |

**Note** : Lean encode les *gaps* tandis que le preprint encode les *positions cumulées*. La bijection entre les deux est mentionnée dans le preprint §2.1. `corrSum` et `steiner_equation` dans Lean utilisent les positions cumulées (`cumA`), pas les gaps.

### 🟡 NC-4.1 — Dualité gap/position non documentée dans Lean

La `structure Composition` stocke les gaps, mais `corrSum` attend des positions. Le pont entre les deux (via `cumA` dans `steiner_equation`) n'est pas explicité dans la documentation Lean.

**Gravité** : 🟡 MINEUR — Pas d'erreur, mais source potentielle de confusion.

### PC 4.3 — Théorème de Jonction dans les 3 composants

| Composant | Couverture | Thm 1 | SdW | Cohérent |
|-----------|-----------|-------|-----|----------|
| Preprint §5 | [1,67] ∪ [18,∞) | k≥18 | k<68 | ✅ |
| Lean junction_unconditional | k<68 → SdW ∧ k≥18 → nonsurj | ✅ | axiom | ✅ |
| README | [1,67] ∪ [18,∞) = [1,∞) | k≥18 | k<68 | ✅ |

### 🟠 NC-4.2 — preprint.tex est un stub vide

Le fichier `preprint.tex` ne contient que les en-têtes et des `% TODO: Convert from preprint.md`. Les sections 1–3, 5–7 sont entièrement vides. Seuls les théorèmes 1 et 2 (§4, §5) et l'hypothèse H (§6) sont rédigés.

**Gravité** : 🟠 MAJEUR — Le fichier LaTeX n'est pas compilable comme article complet.

### 🟠 NC-4.3 — README.md obsolète (sorry count)

Le README (l.47-48) dit :
> `JunctionTheorem.lean` — Lean 4 skeleton: Junction Theorem (**7 sorry + 1 axiom**)

Le fichier Lean actuel n'a plus que **1 sorry + 1 axiome**. Le README n'a pas été mis à jour.

**Gravité** : 🟠 MAJEUR — Information factuelle fausse visible en première page.

---

## P5 — RÉFÉRENCES BIBLIOGRAPHIQUES (« Le manifeste passagers est-il complet ? »)

### 🟠 NC-5.1 — Année de Barina incohérente

| Fichier | Année citée |
|---------|-------------|
| preprint.md §1.3 | 2020 |
| preprint.md §5.1 | 2020 |
| preprint.tex | 2021 |
| README.md | 2021 |
| phase12 | 2020 |

Le preprint arXiv de Barina date de 2020, la publication journal de 2021. La convention est d'utiliser l'année de publication journal (2021).

**Gravité** : 🟠 MAJEUR — Incohérence au sein du même projet.

### 🟡 NC-5.2 — Référence [13] Rozier absente du .tex

Le preprint.md cite [13] O. Rozier (2015). Cette référence n'apparaît pas dans `preprint.tex` \thebibliography.

**Gravité** : 🟡 MINEUR — Le .tex est un stub, mais la référence manquante crée un désynchronisation.

### 🟡 NC-5.3 — Nombre de références incohérent

| Fichier | Nombre de refs |
|---------|---------------|
| preprint.md | 13 |
| preprint.tex | 12 |
| README.md | 8 |

**Gravité** : 🟡 MINEUR

### 🔵 NC-5.4 — Code MSC 37P35 potentiellement incorrect

Le code 37P35 correspond à la dynamique non-archimédienne/p-adique. Pour le problème de Collatz (dynamique arithmétique sur ℤ), un code plus approprié serait 37A44 (dynamical systems of maps) ou 11B85 (automata sequences).

**Gravité** : 🔵 INFO

### 🟡 NC-5.5 — Description d'Eliahou inexacte dans phase12

Phase12 l.87 écrit : « Eliahou | 1993 | Pas de cycle de longueur 1 ».
Eliahou (1993) prouve des **bornes inférieures** sur la longueur des cycles, pas spécifiquement l'absence de cycles de longueur 1 (triviale).

**Gravité** : 🟡 MINEUR

---

## P6 — VÉRIFICATION NUMÉRIQUE (« Le tableau de bord affiche-t-il les bonnes valeurs ? »)

### PC 6.1 — Script Python verify_nonsurjectivity.py

Exécution indépendante :
```
Exceptions C ≥ d : {3, 5, 17}
Théorème 1 vérifié pour k ∈ [18, 500] : True (483/483)
SHA256(exceptions)[:16] : 262a7f2efa4c8255
✓ Tous les tests passent.
```

**Verdict** : ✅ Script reproductible, résultats conformes.

### PC 6.2 — Calcul de γ

Calcul indépendant en Python :
- α = ln(2)/ln(3) = 0.630929753571457...
- h(α) = 0.949955527188331...
- γ = 1 − h(α) = 0.050044472811669...
- Décomposition : −α·log₂(α) = 0.41922046, −(1−α)·log₂(1−α) = 0.53073507

Conforme aux valeurs du preprint (§3.3). ✅

### PC 6.3 — Valeurs d₅ et C/d pour q₅ = 41

- d₅ = 2⁶⁵ − 3⁴¹ = 420 491 770 248 316 829 ≈ 4.20 × 10¹⁷ ✅
- C(64, 40) = 250 649 105 469 666 120
- C/d = 0.596086 ✅

### PC 6.4 — Valeur log₂(C/d) pour q₇ = 306

- 306 × log₂(3) = 484.9985...
- S = 485
- log₂(C/d) ≈ −19.7 ✅

---

## P7 — LOGIQUE ARGUMENTAIRE (« L'avion vole-t-il droit ? »)

### PC 7.1 — Chaîne de raisonnement principale

```
Steiner (1977) → Cycle ⟹ n₀·d = corrSum(A)
                       ⟹ d | corrSum(A)
                       ⟹ 0 ∈ Im(Ev_d)

Thm 1 (k ≥ 18) → C < d ⟹ Ev_d non surjective
                         ⟹ ∃ résidus omis

SdW (k < 68)   → Pas de cycle pour k < 68

Jonction        → [1,67] ∪ [18,∞) = [1,∞)
                ⟹ Tout k couvert par au moins 1 obstruction

(H)             → 0 est parmi les résidus omis
                ⟹ Pas de cycle (conditionnel)
```

**Verdict** : ✅ La chaîne logique est correcte et complète. La distinction entre résultat inconditionnel (non-surjectivité) et conditionnel (exclusion de 0) est clairement maintenue.

### PC 7.2 — Lacune logique : non-surjectivité ≠ exclusion de 0

Le preprint reconnaît explicitement (§6.1) que la non-surjectivité n'implique pas l'exclusion du résidu 0. C'est honnête et correct.

### 🔵 NC-7.1 — Le preprint §4.2 Étape 2 est heuristique

L'Étape 2 de la démonstration du Théorème 1 (pour les non-convergents) invoque la « propriété de meilleure approximation des convergents » pour affirmer que d(k) ≥ d(q_n). Cette affirmation est correcte pour les convergents les plus proches, mais le passage « le taux entropique log₂ C / S reste voisin de 1 − γ (puisque k/S → 1/log₂ 3 indépendamment de la nature de k) » est asymptotique et non rigoureux pour k modéré.

La preuve complète repose sur la vérification numérique (Étape 3) pour k ∈ [18, 500] et la borne de Baker (Étape 4) pour k ≥ 500, ce qui couvre le gap.

**Gravité** : 🔵 INFO — L'argument est correct mais la rédaction pourrait être plus précise.

---

## P8 — HONNÊTETÉ SCIENTIFIQUE (« Les passagers savent-ils où ils vont ? »)

### PC 8.1 — Distinction inconditionnel / conditionnel

Le preprint, le README, et le Lean distinguent clairement :
- Résultat inconditionnel : Théorèmes 1 et 2 (non-surjectivité + jonction)
- Résultat conditionnel : exclusion de 0 sous Hypothèse (H)
- `no_positive_cycle` dans Lean requiert `[QuasiUniformity k S]`

**Verdict** : ✅ Honnêteté scientifique exemplaire.

### PC 8.2 — Auto-audit

Le `research_log/phase13_audit_kolmogorov_baker.md` documente un auto-audit d'une approche rejetée. Le preprint §7 mentionne la limitation (cycles positifs seulement).

**Verdict** : ✅

### PC 8.3 — Nota bene sur γ erroné

Le preprint §3.3 contient un Nota bene mentionnant que γ ≈ 0.04944 était une erreur dans une version antérieure.

**Verdict** : ✅ Transparence.

---

## SYNTHÈSE DES NON-CONFORMITÉS

### BLOQUANTES (🔴)

| ID | Fichier | Ligne | Description |
|----|---------|-------|-------------|
| NC-1.2 | `paper/preprint.md` | 270 | **d(k=17) = 7 340 033 est FAUX** (correct : 5 077 565). Contradiction interne avec le tableau l.216 |

### MAJEURES (🟠)

| ID | Fichier(s) | Description |
|----|-----------|-------------|
| NC-1.1 | 6 fichiers research_log | γ = 0.0549 issu d'un mélange d'unités. Formule h(log₂3) non définie |
| NC-4.2 | `paper/preprint.tex` | Fichier LaTeX stub avec 10 sections vides (TODO) |
| NC-4.3 | `README.md` l.47-48 | Annonce « 7 sorry + 1 axiom » alors qu'il reste 1 sorry + 1 axiome |
| NC-5.1 | Multiples | Année Barina : 2020 dans preprint.md/phase12, 2021 dans preprint.tex/README |

### MINEURES (🟡)

| ID | Fichier | Description |
|----|---------|-------------|
| NC-2.1 | `JunctionTheorem.lean` l.234 | 1 sorry résiduel (crystal_nonsurjectivity) |
| NC-3.1 | `lean/lakefile.lean` | Mathlib branche `master` non verrouillée |
| NC-3.2 | `lean/lean-toolchain` | Lean v4.29.0-rc2 (release candidate) |
| NC-4.1 | `JunctionTheorem.lean` | Dualité gap/position non documentée |
| NC-5.2 | `paper/preprint.tex` | Référence [13] Rozier absente de \thebibliography |
| NC-5.3 | Multiples | Nombre de références incohérent (13/12/8) |
| NC-5.5 | `phase12` l.87 | Description d'Eliahou inexacte |

### INFO (🔵)

| ID | Description |
|----|-------------|
| NC-5.4 | Code MSC 37P35 potentiellement incorrect |
| NC-7.1 | Étape 2 de Thm 1 est heuristique (couvert par Étapes 3-4) |

---

## VERDICT FINAL DE CERTIFICATION

### Ce qui vole ✅

1. **La mathématique fondamentale est correcte** : γ = 0.0500..., C < d pour k ≥ 18, jonction [1,67] ∪ [18,∞).
2. **La formalisation Lean est solide** : 20+ théorèmes prouvés, 1 seul sorry avec stratégie documentée.
3. **Le script Python est reproductible** : vérification indépendante conforme.
4. **L'honnêteté scientifique est exemplaire** : distinction claire inconditionnel/conditionnel.
5. **Les valeurs numériques sont exactes** dans les livrables finaux (preprint, Lean, script).

### Ce qui ne peut PAS voler ❌

1. **NC-1.2** : L'affirmation arithmétique `d = 7 340 033 = 2²⁷ − 3¹⁷` est fausse. Le preprint contient une contradiction interne sur une valeur numérique fondamentale. **Correction obligatoire avant publication.**

2. **NC-4.3** : Le README annonce 7 sorry alors qu'il en reste 1. **Mise à jour obligatoire.**

3. **NC-4.2** : Le fichier LaTeX n'est pas un article compilable. **Complétion nécessaire pour soumission.**

### Autorisation de vol

> **REFUSÉE** en l'état actuel.
>
> **CONDITIONNELLEMENT ACCORDÉE** après correction des non-conformités 🔴 et 🟠.
> Les corrections minimales requises sont :
> 1. Corriger d(k=17) = 5 077 565 dans preprint.md §4.4 (ligne 270)
> 2. Mettre à jour le README (sorry count : 1 sorry + 1 axiome)
> 3. Uniformiser l'année de Barina (2021 partout)
> 4. Compléter preprint.tex ou le supprimer du dépôt

---

*Fin du protocole d'audit — 26 février 2026*
