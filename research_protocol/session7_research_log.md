# Session 7 — Research Log

**Date** : 3 mars 2026
**Durée** : ~2h
**Objectif** : Explorer les pistes post-session 6 pour prouver l'Énoncé C

---

## Résumé exécutif

Quatre pistes explorées systématiquement. Toutes donnent des résultats NÉGATIFS
pour une preuve directe, mais une découverte structurelle majeure émerge :
**deux mécanismes distincts** (prime blocking vs CRT incompatibilité) expliquent
N₀(d) = 0, et aucune réduction à un modulus universel n'est possible.

## 1. Piste spectrale — FERMÉE

**Script** : `spectral_ordered_automaton.py`

- Matrice de transfert étendue T_ext (état × position) : **NILPOTENTE** (T_ext^S = 0)
- Fonction symétrique élémentaire e_{k-1} : gap spectral MASSIF (|λ₁|/|λ₂| de 2.1 à 52.2)
- T^{k-1}[0,1] ≠ 0 mais e_{k-1}[0,1] = 0 → cancellation exacte
- **Conclusion** : la piste spectrale naïve est fermée car la nilpotence de T_ext est triviale

## 2. Piste comptage/taille — INSUFFISANTE

**Script** : `counting_bound_approach.py`

### Exp 1 : Ratio C/d
- Pour k≥6, p=1 : C(S-p-2, k-3)/d < 0.12 → densité faible
- Mais pour k=5 : ratio = 0.77 (dense !)

### Exp 4 : Ratio compositions/multiples — RÉSULTAT CLÉ NÉGATIF
- k=5: 0.48, k=6: 5.0, k=9: 35.5, k=12: 324, k=14: 848
- **Croissance exponentielle** → pour grand k, compositions >>> multiples de d dans l'intervalle
- **CONSÉQUENCE : un argument de comptage pur NE PEUT PAS prouver N₀=0 pour tout k**

### Exp 5 : Filtrage n₀
- Pour tout k=5..12, p=1 : AUCUN n₀ ne donne un corrSum réalisable ✓

### Exp 6 : 2-adique
- corrSum TOUJOURS impair → n₀ impair. Élimine ~50% mais insuffisant.

## 3. Piste sommes de caractères — INSUFFISANTE

**Script** : `character_sum_analysis.py`

### Exp 1 : Vérification
- Σ F(t) = 0 confirmé numériquement pour k=5..8 (N₀ = 0 à 10^{-10})

### Exp 2 : Borne L₁ — ÉCHEC MASSIF
- Ratio L₁/seuil : 9.57 (k=5), 5.41 (k=6), 9.35 (k=7), 14.04 (k=8)
- **L₁ bound est 5 à 14 fois trop faible** → inutilisable

### Exp 5 : Parseval — IDENTITÉ EXACTE
- **Σ |F(t)|² = d · C** quand corrSum injectif (k=6,7)
- RMS(|F|) ≈ √C (pseudo-aléatoire), Max/√C = 1.4 à 6.9 (outliers)
- Cauchy-Schwarz : ratio 164× → inutilisable

### Exp 5 : Borne de Weil
- |F(t)| ~ O(√C) en moyenne mais outliers à O(C^{0.6})
- Fraction |F(t)| > 2√C : 2-3% des t

## 4. Piste facteurs premiers — DÉCOUVERTE STRUCTURELLE MAJEURE

**Script** : `prime_factor_obstruction.py`

### Exp 1 : Deux mécanismes distincts !

| k | d | Factorisation | N₀ = 0 par... |
|---|---|---------------|---------------|
| 5 | 13 | premier | prime block |
| 6 | 5×59 | semiprime | **CRT incompatibilité** |
| 7 | 23×83 | semiprime | prime block (83) |
| 8 | 7×233 | semiprime | prime block (233) |
| 9 | 5×2617 | semiprime | **CRT incompatibilité** |
| 10 | 13×499 | semiprime | **CRT incompatibilité** |
| 11 | 11×7727 | semiprime | prime block (7727) |
| 12 | 5×59×1753 | 3 facteurs | **CRT incompatibilité** |
| 13 | 502829 | premier | prime block |
| 14 | 79×45641 | semiprime | **CRT incompatibilité** |
| 15 | 13×186793 | semiprime | **CRT incompatibilité** |

- **Prime blocking** (k=5,7,8,11,13) : un facteur premier p | d donne N₀(p) = 0
  directement (aucune composition n'a corrSum ≡ 0 mod p)
- **CRT incompatibilité** (k=6,9,10,12,14,15) : chaque facteur premier permet
  des solutions individuelles, mais elles ne sont JAMAIS simultanées

### Exp 2-3 : Moduli universels
- **m=2 : N₀(2)=0 pour TOUT k** ← corrSum toujours impair (PROUVABLE)
- **m=3 : N₀(3)=0 pour TOUT k** ← corrSum ≡ 2^{q_{k-1}} mod 3 ≠ 0 (PROUVABLE)
- GCD(d(k), k=3..19) = 1 → **aucun modulus universel ne divise d**
- Les obstructions mod 2 et mod 3 sont réelles mais irrelevantes (gcd(d,6)=1)

### Exp 4 : CRT détaillée pour k=6 (d=5×59)
- mod 5 : full coverage (5/5), 11 compositions ≡ 0 mod 5
- mod 59 : 29/59 résidus, 1 composition ≡ 0 mod 59
- Paire (0,0) JAMAIS atteinte !
- Les 11 comps avec r₁≡0 mod 5 ont r₂ ∈ {16,20,24,...,54} (jamais 0 mod 59)
- La 1 comp avec r₂≡0 mod 59 a r₁ = 1 (≠ 0 mod 5)

## Preuves algébriques établies

### Lemme 1 : corrSum est toujours impair
**Preuve** : prefix = (9+5·2^p)·3^{k-3} est impair (produit de deux impairs).
Chaque terme du suffix a facteur 2^{q_j} avec q_j ≥ p+2 ≥ 3, donc suffix ≡ 0 mod 8.
corrSum = impair + pair = impair. □

### Lemme 2 : corrSum ≢ 0 mod 3
**Preuve** : Pour k ≥ 4 : prefix ≡ 0 mod 3 (car 3^{k-3} | prefix). Suffix mod 3 :
seul le dernier terme (j=k-1) contribue : 2^{q_{k-1}} ≡ (-1)^{q_{k-1}} mod 3.
Pour tout q_{k-1} ≥ 2 : 2^{q_{k-1}} ∈ {1,2} mod 3, jamais 0. □

**Limitation** : gcd(d, 6) = 1 pour tout k, donc ces lemmes ne prouvent pas N₀(d)=0.

## Conjecture formalisée

**Conjecture (Énoncé C)** : Pour tout k ≥ 3, tout p ≥ 1 :
N₀^C(k,p) := #{compositions (0,p,p+1,q₃,...,q_{k-1}) ordonnées, q_j ∈ {p+2,...,S-1},
corrSum ≡ 0 mod d} = 0.

**Vérification** : k=3,...,15, tous p applicables.

## Bilan des approches

| Approche | Résultat | Applicable ? |
|----------|----------|-------------|
| Spectrale (T_ext) | Nilpotente | ❌ FERMÉE |
| Comptage pur | comps >> multiples | ❌ IMPOSSIBLE grand k |
| L₁ character sums | ratio 5-14× | ❌ TROP FAIBLE |
| Cauchy-Schwarz | ratio 164× | ❌ TROP FAIBLE |
| Mod 2 (impair) | PROUVÉ | ❌ gcd(d,2)=1 |
| Mod 3 | PROUVÉ | ❌ gcd(d,3)=1 |
| Prime blocking | Marche pour certains k | ⚠️ PARTIEL |
| CRT incompatibilité | Marche pour autres k | ⚠️ PARTIEL |

## Prochaines pistes

1. **Baker / Énoncé A** : Prouver ord_d(2) > S-1, ce qui implique que les puissances
   de 2 sont toutes distinctes mod d. Cela donnerait une structure très contrainte
   au corrSum. Approche via théorèmes de Baker sur les formes linéaires en logarithmes.

2. **Preuve algébrique directe** : Exploiter 3^k ≡ 2^S mod d pour transformer
   corrSum en une expression purement en puissances de 2 (ou de 3).
   corrSum = Σ 3^{k-1-j}·2^{a_j} = 3^{k-1}·Σ (2/3)^{a_j}·3^{a_j-j} ... à explorer.

3. **Induction sur k** : Montrer que si N₀=0 pour k, alors N₀=0 pour k+1.
   La difficulté : d(k+1) ≠ d(k), les compositions changent.

4. **Approche p-adique** : Travailler dans Q_p pour un p bien choisi.
   La structure simultanée dans Q_2, Q_3, et Q_d pourrait être contraignante.

## Scripts créés cette session

1. `spectral_ordered_automaton.py` — analyse spectrale (4 expériences)
2. `counting_bound_approach.py` — bornes de comptage (6 expériences)
3. `character_sum_analysis.py` — sommes de caractères (6 expériences)
4. `prime_factor_obstruction.py` — facteurs premiers + CRT (5 expériences)
