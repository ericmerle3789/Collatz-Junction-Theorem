# FINDING: Audit Confirmed — corrSum Formula Error
## Date: 18 Mars 2026

### Résultat de la vérification numérique

| k | Indiv N0 | Cumul N0 | Indiv range/d | Cumul range/d |
|---|----------|----------|---------------|---------------|
| 3 | 0        | 0        | 0.40          | 6.00          |
| 4 | **1**    | **0**    | 0.30          | 5.66          |
| 5 | 0        | 0        | 1.08          | 70.0          |
| 6 | 0        | 0        | 0.20          | 21.5          |
| 7-14 | 0     | 0        | <0.12         | 21-535        |

### Conclusions vérifiées

1. **INDIVIDUEL ≠ CUMULATIF** : Valeurs complètement différentes ✓
2. **k=4 PHANTOM DISPARU** : Avec la formule correcte (cumulative), N0(d(4))=0 ✓
3. **Range Exclusion IMPOSSIBLE** : cumul range/d >> 1, croît avec k ✓
4. **N0_cumulative = 0 pour k=3..14** : Vérifié exhaustivement ✓
5. **Article v5 values fausses** : Prétendait {26,34} pour k=3, correct = {32,34} ✓

### Implication cruciale

N0_cumulative(d(k)) = 0 pour tout k ≥ 3 est EXACTEMENT ÉQUIVALENT
à l'inexistence de cycles positifs non-triviaux de Collatz.

Steiner's equation: n₀ · d = corrSum_cumulative(σ)
=> corrSum ≡ 0 mod d <=> il existe un cycle de longueur k

### Ce qui reste valide

1. Junction Theorem (nonsurjectivité): C(S-1,k-1) < d pour k ≥ 18 ✓
2. Steiner equation formalisée en Lean (skeleton) ✓
3. SdW: pas de cycle k < 68 ✓
4. H → pas de cycle ✓
5. Path B (FCQ/spectral) : à re-examiner avec la bonne formule

### Nouvelle stratégie

Range Exclusion est mort. Nouvelles directions:
1. **DP modulaire** : calculer N0 exactement par programmation dynamique
2. **FCQ adapté** : bornes spectrales sur les séquences cumulatives
3. **Argument structurel** : exploiter la contrainte σ_0=0 + monotonie stricte
4. **Baker + valuation** : contraintes sur n₀ = corrSum/d
