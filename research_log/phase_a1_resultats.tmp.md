# Phase A1 — Résultats de la vérification exhaustive k=18..25
# Date : 3 mars 2026
# Script : scripts/exploration/phase_a1_exhaustive_k18_25.py

---

## Méthode

- Programmation dynamique (DP) sur les positions de composition
- État : (j positions sélectionnées, corrSum mod p)
- Horner : c₀ = 1, c_j = 3·c_{j-1} + 2^{A[j]}
- Complexité : O(S × k × p) par premier
- Vérification croisée DP vs énumération directe pour k=3..8 : 100% PASS

## Résultats

| k | S | d(k) | C = C(S-1,k-1) | Premiers | min N₀ | Verdict |
|---|---|------|----------------|----------|--------|---------|
| 18 | 29 | 149,450,423 | 21,474,180 | 137, 1090879 | 54 | NON RÉSOLU |
| 19 | 31 | 985,222,181 | 86,493,225 | 19, 23, 2254513* | 3,764,223 | NON RÉSOLU |
| 20 | 32 | 808,182,895 | 141,120,525 | 5, 13, 499, 24917 | 10,005 | NON RÉSOLU |
| 21 | 34 | 6,719,515,981 | 573,166,440 | 33587, 200063 | 2,814 | NON RÉSOLU |
| 22 | 35 | 2,978,678,759 | 927,983,760 | 7, 425525537* | 132,567,116 | NON RÉSOLU |
| 23 | 37 | 43,295,774,645 | 3,796,297,200 | 5, 31727, 272927 | 14,283 | NON RÉSOLU |
| 24 | 39 | 267,326,277,407 | 15,471,286,560 | 7, 233, 2113, 77569 | 195,360 | NON RÉSOLU |
| 25 | 40 | 252,223,018,333 | 25,140,840,660 | 11, 13, 191, 251, 36791 | 683,435 | NON RÉSOLU |

(*) Premier SKIP (trop grand pour DP, C trop grand pour énumération)

## Observations clés

1. **N₀(p) > 0 pour TOUS les premiers testés** : la distribution corrSum mod p est
   quasi-uniforme. Aucun premier n'exclut le résidu 0.

2. **χ²/(p-1) ≈ 1.0** dans la majorité des cas, confirmant la quasi-uniformité.

3. **Ratio N₀/(C/p) ≈ 1.0** : les counts sont proches de la valeur attendue
   pour une distribution uniforme.

4. **Cas extrême** : k=18, p=1,090,879 donne N₀=54 (attendu C/p ≈ 19.7,
   ratio 2.74). Excès mais pas 0.

5. **Primes skippés** : k=19 (p=2,254,513) et k=22 (p=425,525,537) n'ont pas
   été testés. Mais le pattern des autres primes suggère N₀ > 0.

## Diagnostic

Le résultat est **cohérent avec le diagnostic Phase 20** :
- Le CRT ne fonctionne pas pour k ≥ 18 (distributions trop uniformes)
- La seule exclusion chirurgicale connue est k=5 (q₃, p=13)
- Pour k ≥ 18, la preuve de H(k) nécessite une approche THÉORIQUE (Phase B)

## Implication pour la suite

- **Phase A2** : extension Régime B (calibration, pas exclusion)
- **Phase B** : indispensable — le mixing inconditionnel est la seule voie
- Les données E₂/E₂_unif ≈ 1.000 confirment la quasi-Sidon de Phase 23f

## Temps d'exécution

Total : 599.7s (10 min)
- Vérification croisée : < 1s
- k=18..25 : 599s (dominé par find_n₃ pour grands p avec ord₂(p) élevé)
- Aucune incohérence C_check ≠ C détectée
