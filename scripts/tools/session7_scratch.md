# Session 7 — Notes de travail

## Résultats approche par comptage (counting_bound_approach.py)

### Exp 1 — Ratio C/d
- Pour k≥6, p=1: C(S-p-2, k-3)/d << 1 (ex: 0.12 pour k=6, 0.047 pour k=12)
- EXCEPTION: k=5, p=1: ratio = 0.77 (proche de 1)
- Tendance: ratio ≈ C(S-3, k-3)/(2^S - 3^k), décroît mais pas uniformément

### Exp 2 — Distribution corrSum mod d
- Target JAMAIS atteint (confirmé k=5..8)
- k=5: 8/13 résidus couverts, distance 1 au target
- k=6,7: résidus INJECTIFS (chaque composition → résidu distinct)
- k=8: 248/1631 résidus, quelques collisions, distance 1 au target

### Exp 4 — Ratio compositions/multiples (RÉSULTAT CLÉ)
- k=5: 0.48 (< 1 → comptage POURRAIT marcher)
- k=6: 5.0 ; k=7: 15.8 ; k=9: 35.5 ; k=11: 85.8 ; k=12: 324 ; k=14: 848
- **CROISSANCE EXPONENTIELLE**: pour grand k, compositions >>> multiples de d
- **CONSÉQUENCE: Un argument de comptage pur NE PEUT PAS prouver N₀=0 pour tout k**

### Exp 5 — Filtrage n₀ candidats
- Pour tout k=5..12: AUCUN n₀ ne donne un corrSum réalisable
- Distances au multiple de d le plus proche parfois très petites (dist=1)

### Exp 6 — Contrainte 2-adique
- corrSum TOUJOURS impair (v₂=0) car prefix = 19·3^{k-3} est impair
- d TOUJOURS impair (2^S - 3^k = pair - impair = impair)
- Donc n₀ doit être impair → élimine ~50% des candidats, insuffisant

## Piste spectrale (spectral_ordered_automaton.py) — Session 6/7

- Matrice de transfert étendue T_ext: NILPOTENTE → piste naïve fermée
- e_{k-1}: gap spectral massif (ratio 2.1 à 52.2)
- T^{k-1}[0,1] ≠ 0 mais e_{k-1}[0,1] = 0 → cancellation exacte
- Σ F(t) = -C exactement (cancellation Fourier vérifiée)

## BILAN — Synthèse des approches testées

| Piste | Résultat | Conclusion |
|-------|----------|------------|
| 1. Spectrale (T_ext) | Nilpotente | FERMÉE (forme naïve) |
| 2. Comptage pur | comps >> multiples | IMPOSSIBLE pour grand k |
| 3. Mod 3 | Invalide (session 6) | FERMÉE |
| 4. 2-adique | Élimine ~50% | INSUFFISANT |
| 5. Double Peeling | Vérifié k=3..14 | Vérification, pas preuve |

## NOUVELLE PISTE : Sommes de caractères (méthode analytique)

### Idée
N₀ = (1/d) Σ_{t=0}^{d-1} F(t) où F(t) = Σ_C ω^{t·corrSum(C)}

Si on peut montrer |N₀ - C/d| < 1 et C/d < 1, alors N₀ = 0.

### Plan d'investigation
1. Calculer |F(t)| pour tous t≠0
2. Vérifier si (1/d)Σ_{t≠0}|F(t)| < 1 - C/d
3. Analyser la structure de F(t) (factorisation partielle ?)
4. Chercher des bornes uniformes sur |F(t)|

### Structure de F(t)
F(t) = ω^{t·prefix} · G(t)
G(t) = Σ_{b₁<...<b_{k-3}} Π_{j=1}^{k-3} ω^{t·3^{k-3-j}·2^{b_j}}

Avec α_j(q) = ω^{t·3^{k-3-j}·2^q}, on a:
G(t) = Σ_{b₁<...<b_{k-3}} Π_{j=1}^{k-3} α_j(b_j)

C'est un DÉTERMINANT de Cauchy-like / Schur-like si les α_j se factorisent.

## Résultats sommes de caractères (character_sum_analysis.py)

### Exp 1 — Vérification Sum F(t) = 0
- Confirmé pour k=5,6,7,8 : N₀ = 0.0000000000 (< 0.01)

### Exp 2 — Borne L₁ : ÉCHEC MASSIF
- k=5: L₁/seuil = 9.57 → L₁ bound INUTILE
- k=6: ratio = 5.41
- k=7: ratio = 9.35
- k=8: ratio = 14.04
- **CONCLUSION: L₁ character sum approach CANNOT prove N₀=0**

### Exp 4 — Déterminant : vérification recurrence vs directe OK

### Exp 5 — Parseval / Weil : RÉSULTAT CLÉ
- **PARSEVAL EXACT** : Σ|F(t)|²/d = C pour corrSum injectif (k=6,7)
- RMS |F(t)| ≈ √C (comportement pseudo-aléatoire)
- Max |F(t)|/√C = 1.4 à 6.9 (outliers massifs)
- Cauchy-Schwarz donne ratio 164× le threshold → INUTILE

## Résultats facteurs premiers (prime_factor_obstruction.py)

### Exp 1 — DÉCOUVERTE : Deux mécanismes distincts !
| k | d | Facteurs | Mécanisme |
|---|---|----------|-----------|
| 5 | 13 | premier | prime block (13) |
| 6 | 5×59 | composite | CRT incompatibilité |
| 7 | 23×83 | composite | prime block (83) |
| 8 | 7×233 | composite | prime block (233) |
| 9 | 5×2617 | composite | CRT incompatibilité |
| 10 | 13×499 | composite | CRT incompatibilité |
| 11 | 11×7727 | composite | prime block (7727) |
| 12 | 5×59×1753 | composite | CRT incompatibilité |
| 13 | 502829 | premier | prime block |
| 14 | 79×45641 | composite | CRT incompatibilité |
| 15 | 13×186793 | composite | CRT incompatibilité |

### Exp 2-3 — Moduli universels
- m=2: N₀=0 TOUJOURS (corrSum impair) → PROUVABLE mais gcd(d,2)=1
- m=3: N₀=0 TOUJOURS (corrSum ≡ 2^{q_{k-1}} mod 3 ≠ 0) → PROUVABLE mais gcd(d,3)=1
- m=4,6,8,9,10,12,16: même phénomène → tous copremiers à d
- GCD de tous les d(k) = 1 → pas de modulus universel divisant d

### Exp 4 — CRT détaillée pour k=6 (d=5×59)
- mod 5: TOUS les résidus atteints (full coverage)
- mod 59: 29/59 résidus, 0 atteint par 1 composition
- MAIS: la paire (0,0) jamais atteinte !
- Les 11 comps avec r₁=0 ont r₂ ∈ {16,20,24,26,30,36,37,38,43,45,54} (0 absent)
- La 1 comp avec r₂=0 a r₁=1 (≠ 0)
- → INCOMPATIBILITÉ CRT structurelle

## PREUVES ALGÉBRIQUES (nouvelles)

### Preuve que corrSum est toujours impair
- prefix = (9+5·2^p)·3^{k-3}. Pour p≥1: 9+5·2^p impair, 3^{k-3} impair → prefix impair
- suffix: chaque terme 3^{k-1-j}·2^{q_j} avec q_j ≥ p+2 ≥ 3, donc 2^{q_j} div par 8 → suffix ≡ 0 mod 2
- corrSum = impair + pair = impair. QED.

### Preuve que corrSum ≢ 0 mod 3
- Pour k≥4: prefix = (9+5·2^p)·3^{k-3} ≡ 0 mod 3 (car k-3 ≥ 1)
- suffix mod 3: termes j<k-1 ont facteur 3^{k-1-j≥1} → ≡ 0 mod 3
- Dernier terme (j=k-1): 2^{q_{k-1}} ≡ (-1)^{q_{k-1}} mod 3, jamais 0
- corrSum ≡ 2^{q_{k-1}} ≡ ±1 mod 3. QED.

### Note: ces preuves sont correctes mais IRRELEVANTES car gcd(d,6) = 1 toujours.

## CONJECTURE PRÉCISE

**Conjecture (Énoncé C)**: Pour tout k ≥ 3, tout p ≥ 1, et toute composition
A = (0, p, p+1, q₃, ..., q_{k-1}) avec p+2 ≤ q₃ < ... < q_{k-1} ≤ S-1 :

  corrSum(A) = Σ_{j=0}^{k-1} 3^{k-1-j}·2^{A_j} ≢ 0 (mod d)

où d = 2^S - 3^k, S = ⌈k·log₂3⌉.

**Vérifié** : k = 3, ..., 15, tous les p applicables.

**Approches testées et échouées** :
1. Spectrale (T_ext nilpotente)
2. Comptage pur (compositions >> multiples pour grand k)
3. L₁ / Cauchy-Schwarz character sums (trop faibles)
4. Modulus universel (n'existe pas)

**Approches restantes** :
1. Baker / formes linéaires en log (pour Énoncé A → qui aiderait indirectement)
2. Preuve directe algébrique exploitant la structure Horner + 3^k ≡ 2^S
3. Argument par induction sur k
4. Approche combinatoire (involution, bijection)
