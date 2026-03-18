# FINDING: ord_d(2) >> S-k for all k=3..20
## 18 Mars 2026

### Résultat

| k | d | ord_d(2) | S-k | ratio |
|---|---|----------|-----|-------|
| 3 | 5 | 4 | 2 | 2.0 |
| 4 | 47 | 23 | 3 | 7.7 |
| 5 | 13 | 12 | 3 | 4.0 |
| 6 | 295 | 116 | 4 | 29.0 |
| 7 | 1909 | 902 | 5 | 180.4 |
| 13 | 502829 | 502828 | 8 | 62853.5 |
| 20 | 808182895 | 6204084 | 12 | 517007.0 |

### Conséquence

Comme Δ = δ_i - δ_{i+1} ≤ S-k et ord_d(2) > S-k :
- 2^Δ ≢ 1 mod d pour tout Δ possible
- Donc (2^Δ - 1) ≢ 0 mod d
- Donc chaque correction de swap = ρ^{i+1}·3⁻¹·2^{δ_{i+1}}·(2^Δ-1) est une UNITÉ × une NON-NULLITÉ = NON-NULLE

### Implication

Chaque swap individuel produit une correction non-nulle.
Mais la SOMME de corrections non-nulles peut-elle être 0 mod d ?

Pour k=3..8 (vérifié exhaustivement) : NON.
Pour k ≥ 9 : ouvert.

### Pourquoi ord_d(2) >> S-k ?

d = 2^S - 3^k. L'ordre de 2 mod d est lié à l'exposant S :
2^S ≡ 3^k mod d (pas ≡ 1). Donc S n'est PAS un multiple de ord_d(2).
Mais S est "proche" d'un multiple : 2^S ≡ 3^k (petit résidu relatif à d).

La théorie de Baker donne : ord_d(2) ≥ exp(c·√(log d)) pour des constantes effectives.
Comme d ≈ 3^k et S-k ≈ 0.585k : ord_d(2) >> k >> S-k.

### Conjecture

**Conjecture (Individual Swap Nonvanishing)** :
Pour tout k ≥ 3 : ord_{d(k)}(2) > S(k) - k.

Cela impliquerait : chaque correction de swap est non-nulle dans Z/dZ.
C'est un résultat de théorie des nombres (borne sur l'ordre multiplicatif
de 2 modulo 2^S - 3^k) qui pourrait être prouvable par Baker.
