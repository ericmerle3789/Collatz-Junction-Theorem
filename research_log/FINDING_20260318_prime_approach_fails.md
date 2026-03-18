# CRITICAL FINDING: Prime-by-Prime Approach Fails for Cumulative CorrSum
## Date: 18 Mars 2026

### Résultat

Pour les exposants CUMULATIFS (formule correcte de Steiner), l'approche
"trouver un premier p | d tel que N0(p) = 0" ÉCHOUE pour presque tous les k.

### Données

| k | Primes testés | N0(p) = 0 ? | Résultat |
|---|---------------|-------------|----------|
| 3 | p=5 | OUI | ✓ |
| 4 | p=47 | OUI | ✓ |
| 5 | p=13 | OUI | ✓ |
| 6 | p=5, 59 | NON (36, 6) | UNRESOLVED by primes |
| 7 | p=83 | OUI | ✓ |
| 8 | p=233 | OUI | ✓ |
| 9 | p=5, 2617 | NON | UNRESOLVED |
| 10 | p=13, 499 | NON | UNRESOLVED |
| 11 | p=7727 | OUI | ✓ |
| 12-35+ | multiples | NON | UNRESOLVED |

### Interpretation

Avec la formule CUMULATIVE, les valeurs corrSum sont très dispersées mod p.
Pour k=6, d=295=5·59:
- 36/126 séquences ont corrSum ≡ 0 mod 5 (29%)
- 6/126 ont corrSum ≡ 0 mod 59 (4.8%)
- Mais N0(295) = 0 (vérifié exhaustivement) — c'est l'interférence CRT

### Conséquence

L'approche Path B (FCQ/spectral) du PROOF_ASSEMBLY est INVALIDE pour
les exposants cumulatifs. Les bornes spectrales ρ_p < 1 ne suffisent pas
car N0(p) > 0 pour tous les petits premiers.

La preuve de la non-existence de cycles nécessite une approche
qui traite d en ENTIER, pas premier par premier.

### Ce qui est mort
1. Range Exclusion (exposants individuels = mauvaise formule)
2. FCQ prime-by-prime (N0(p) > 0 pour presque tous les p)
3. Baker argument tel que formulé dans PROOF_ASSEMBLY

### Ce qui survit
1. Junction Theorem: C(S-1,k-1) < d pour k ≥ 18 ✓
2. SdW: pas de cycle k < 68 ✓
3. Steiner equation formalisée (cumulative) ✓

### Nouvelle direction requise
Prouver N0(d) = 0 nécessite exploiter la structure COMPOSITE de d,
pas les facteurs individuels. L'interférence CRT est le mécanisme clé.
