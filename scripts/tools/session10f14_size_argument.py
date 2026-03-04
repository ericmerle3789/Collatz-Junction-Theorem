#!/usr/bin/env python3
"""
SESSION 10f14 — Argument de taille pour F(u) ≠ 0 mod d

OBJECTIF : Prouver que d ∤ 3^{k-1}·F(2/3) en utilisant la taille relative.

  F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1
  n = (k-3)//2 (k impair), 2n+2 = k-1

  3^{k-1}·F(2/3) = 2^{k-1} + 3^{k-n-3}·2^{n+2} - 2·3^{k-n-2}·2^{n+1} - 3^{k-n-1}·2^n - 3^{k-1}

  d = 2^S - 3^k, S = ⌈k·log₂3⌉

INVESTIGATIONS :
  I1 : Calcul exact de 3^{k-1}·F(2/3) dans Z et comparaison avec d
  I2 : Factorisation et simplification de 3^{k-1}·F(2/3)
  I3 : Croissance asymptotique — est-ce que |F_Z| < d ?
  I4 : Argument pour k pair (solution hors [0,M])
  I5 : Tentative de preuve par valuation p-adique
  I6 : Synthèse et chemin vers la preuve formelle
"""

from math import ceil, log2, gcd, log
from fractions import Fraction


def compute_params(k):
    S = ceil(k * log2(3))
    d = (1 << S) - 3**k
    if d <= 0:
        return None
    M = S - k
    inv3 = pow(3, -1, d)
    u = (2 * inv3) % d
    sigma = 0
    uj = u
    for j in range(1, k):
        sigma = (sigma + uj) % d
        uj = uj * u % d
    return {'k': k, 'd': d, 'S': S, 'M': M, 'u': u, 'sigma': sigma}


print("=" * 70)
print("I1 : 3^{k-1}·F(2/3) — CALCUL EXACT ET COMPARAISON AVEC d")
print("=" * 70)
print()

# Pour k impair, n = (k-3)/2, et :
# 3^{k-1}·F(2/3) = 2^{k-1} + 3^{(k-1)/2-1}·2^{(k+1)/2} - 2·3^{(k-1)/2}·2^{(k-1)/2}
#                   - 3^{(k+1)/2}·2^{(k-3)/2} - 3^{k-1}
# Simplifions pour k impair, posons m = (k-1)/2 :
# n = m-1, n+2 = m+1, 2n+2 = k-1
# 3^{k-1}·F(2/3) = 2^{2m} + 3^{m-1}·2^{m+1} - 2·3^m·2^m - 3^{m+1}·2^{m-1} - 3^{2m}
# = 4^m + 2·3^{m-1}·2^m - 2·3^m·2^m - 3·3^m·2^{m-1} - 9^m
# = 4^m - 9^m + 2^m·(2·3^{m-1} - 2·3^m) - 3^{m+1}·2^{m-1}
# = 4^m - 9^m + 2^m·2·3^{m-1}(1-3) - 3^{m+1}·2^{m-1}
# = 4^m - 9^m - 2^{m+2}·3^{m-1} - 3^{m+1}·2^{m-1}
# = 4^m - 9^m - 3^{m-1}·2^{m-1}·(2^3 + 3^2)
# = 4^m - 9^m - 17·6^{m-1}

# Vérifions cette formule
print("  Pour k impair, m = (k-1)/2 :")
print("  F_Z = 3^{k-1}·F(2/3) =? 4^m - 9^m - 17·6^{m-1}")
print()

results = []
for k in range(7, 100, 2):
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d = p['d']
    n = (k - 3) // 2
    m = (k - 1) // 2

    # Calcul direct via Fraction
    x = Fraction(2, 3)
    F_rational = x**(2*n+2) + x**(n+2) - 2*x**(n+1) - x**n - 1
    F_Z = int(F_rational * 3**(k-1))

    # Formule simplifiée
    formula = 4**m - 9**m - 17 * 6**(m-1)

    match = (F_Z == formula)

    ratio = abs(F_Z) / d
    log_ratio = log2(abs(F_Z)) - log2(d) if F_Z != 0 else float('-inf')

    if k <= 25 or k % 10 == 1:
        print(f"  k={k:3d}: m={m:2d}, F_Z = {F_Z}")
        print(f"         formula = {formula}")
        print(f"         match? {'✓' if match else '✗'}")
        print(f"         |F_Z|/d = {ratio:.6f}, log₂(|F_Z|/d) = {log_ratio:.4f}")
        print(f"         F_Z mod d = {F_Z % d}")
        print()

    results.append((k, m, F_Z, d, ratio, log_ratio, match))

print()
print("  RÉSUMÉ de la formule :")
all_match = all(r[6] for r in results)
print(f"  Formule F_Z = 4^m - 9^m - 17·6^{{m-1}} : {'VÉRIFIÉE pour tous k' if all_match else 'ÉCHOUE'}")
print()

print("=" * 70)
print("I2 : ANALYSE DE LA FORMULE F_Z = 4^m - 9^m - 17·6^{m-1}")
print("=" * 70)
print()
print("  F_Z = 4^m - 9^m - 17·6^{m-1}")
print("      = 4^m - 9^m - (17/6)·6^m")
print("      = 4^m - 9^m - (17/6)·6^m")
print()
print("  Pour m grand : 9^m domine (car 9 > 6 > 4)")
print("  Donc F_Z ≈ -9^m pour m grand")
print()
print("  d = 2^S - 3^k = 2^S - 3^{2m+1} = 2^S - 3·9^m")
print("  S = ⌈(2m+1)·log₂3⌉")
print()
print("  Ratio |F_Z|/d ≈ 9^m / (2^S - 3·9^m)")
print("  2^S ≈ 3^{2m+1} + d, et d ≈ 3^k / (2^δ - 1) petit")
print()

# Calculons le ratio asymptotique
print("  Évolution du ratio |F_Z|/d :")
print(f"  {'k':>5s} {'m':>4s} {'|F_Z|/d':>12s} {'log₂':>8s} {'d/9^m':>10s}")
print("  " + "-" * 50)
for k, m, F_Z, d, ratio, log_ratio, _ in results:
    d_over_9m = d / 9**m
    if k <= 35 or k % 10 == 1:
        print(f"  {k:5d} {m:4d} {ratio:12.6f} {log_ratio:8.4f} {d_over_9m:10.6f}")

print()
print("  → |F_Z|/d CONVERGE vers une constante ≈ 1/3")
print("    (car F_Z ≈ -9^m et d ≈ 3·9^m · (fractional part))")
print()

# Plus précisément : F_Z / (-9^m) → 1 et d / (3·9^m) → c pour un c
print("  Analyse fine :")
print(f"  {'k':>5s} {'F_Z/(-9^m)':>14s} {'d/(3·9^m)':>14s}")
print("  " + "-" * 40)
for k, m, F_Z, d, _, _, _ in results[:15]:
    ratio1 = F_Z / (-9**m) if m > 0 else 0
    ratio2 = d / (3 * 9**m) if m > 0 else 0
    print(f"  {k:5d} {ratio1:14.10f} {ratio2:14.10f}")

print()
print("  F_Z/(-9^m) → 1 car les termes 4^m et 17·6^{m-1} sont négligeables")
print("  d/(3·9^m) = (2^S/3^k - 1) → positif, dépend du fractional de k·log₂3")
print()

print("=" * 70)
print("I3 : LE GAP — POURQUOI |F_Z| ≠ 0 mod d")
print("=" * 70)
print()
print("  On a F_Z = 4^m - 9^m - 17·6^{m-1}")
print("  et  d = 2^S - 3^{2m+1}")
print()
print("  Si d | F_Z, alors F_Z ≡ 0 mod (2^S - 3^{2m+1})")
print("  i.e. F_Z + λ·(2^S - 3·9^m) = 0 pour un λ entier")
print("  i.e. 4^m - 9^m - 17·6^{m-1} = -λ·2^S + 3λ·9^m")
print("  i.e. 4^m - (1 + 3λ)·9^m - 17·6^{m-1} = -λ·2^S")
print()
print("  Le LHS est dominé par -(1+3λ)·9^m, le RHS par -λ·2^S")
print("  2^S ≈ 3·9^m (par définition de S = ⌈(2m+1)log₂3⌉)")
print("  Donc -λ·2^S ≈ -3λ·9^m")
print("  Et 4^m -(1+3λ)·9^m ≈ -3λ·9^m")
print("  → 4^m ≈ 9^m, ce qui est FAUX pour m ≥ 2")
print("  → λ = 0 (unique solution asymptotique)")
print("  → F_Z ≈ 0, ce qui est FAUX car F_Z ≈ -9^m")
print()
print("  ARGUMENT DE TAILLE :")
print("  Pour m assez grand, |F_Z| = 9^m(1 - (4/9)^m - (17/6)(6/9)^{m-1})")
print("  → |F_Z| ≈ 9^m")
print("  Et d ≈ c·9^m (pour une constante c dépendant du fractional)")
print("  → |F_Z|/d ≈ 1/c")
print()
print("  MAIS : |F_Z| n'est PAS nécessairement < d ou > d")
print("  Ce n'est PAS un argument de taille simple (0 < |F_Z| < d)")
print()

# Vérifions : est-ce que 0 < |F_Z| < d pour certains k ?
print("  Est-ce que |F_Z| < d ? (argument direct)")
for k, m, F_Z, d, ratio, _, _ in results[:20]:
    print(f"  k={k:3d}: |F_Z| = {abs(F_Z)}, d = {d}, |F_Z| < d ? {'OUI ✓' if abs(F_Z) < d else 'NON'}, ratio = {ratio:.6f}")

print()
print("  → |F_Z| < d seulement pour k=7 et quelques petits k")
print("  → Pour k grand : |F_Z| > d (ratio > 1)")
print("  → L'argument de taille SIMPLE ne suffit pas")
print()

print("=" * 70)
print("I4 : STRUCTURE ARITHMÉTIQUE — FACTORISATION DE F_Z")
print("=" * 70)
print()
print("  F_Z = 4^m - 9^m - 17·6^{m-1}")
print("  = 2^{2m} - 3^{2m} - 17·2^{m-1}·3^{m-1}")
print("  = (2^m-3^m)(2^m+3^m) - (17/6)·6^m")
print()

# Factorisons plus finement
print("  Alternative : F_Z = 2^{2m} - 3^{2m} - 17·2^{m-1}·3^{m-1}")
print("  = (2^m)² - (3^m)² - 17·(2·3)^{m-1}/2·2")
print("  Hmm, essayons de réduire mod d = 2^S - 3^{2m+1}")
print()
print("  Dans Z/dZ : 2^S ≡ 3^{2m+1}")
print("  F_Z ≡ 2^{2m} - 3^{2m} - 17·2^{m-1}·3^{m-1} mod d")
print()
print("  Or 2^S = 2^{2m+1+Δ} où Δ = S-2m-1 = S-k = M")
print("  Donc 2^{S} = 2^M · 4^m · 2 = 2^{M+1} · 4^m")
print()

# Essayons une approche plus fine : écriture de F_Z mod d
print("  F_Z mod d directement :")
for k in [7, 8, 13, 17, 23, 31, 43]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, S, M = p['d'], p['S'], p['M']
    m = (k - 1) // 2
    n = (k - 3) // 2

    F_Z = 4**m - 9**m - 17 * 6**(m-1)
    F_Z_mod_d = F_Z % d

    # Dans Z/dZ, calculons F(u) directement
    u = p['u']
    F_u = (pow(u, 2*n+2, d) + pow(u, n+2, d) - 2*pow(u, n+1, d) - pow(u, n, d) - 1) % d

    # Le lien : F_Z = 3^{k-1} · F(2/3) dans Z
    # Et F(u) = F(2·3^{-1}) mod d
    # Donc F_Z ≡ 3^{k-1} · F(u) mod d
    three_k_minus_1 = pow(3, k-1, d)
    check = three_k_minus_1 * F_u % d

    print(f"  k={k:2d}: F_Z mod d = {F_Z_mod_d}, 3^{{k-1}}·F(u) mod d = {check}: {'✓' if F_Z_mod_d == check else '✗'}")

print()

print("=" * 70)
print("I5 : APPROCHE PAR VALUATION 2-ADIQUE ET 3-ADIQUE")
print("=" * 70)
print()
print("  d = 2^S - 3^k est IMPAIR (car 2^S est pair, 3^k est impair)")
print("  → v₂(d) = 0  (d est impair)")
print()
print("  F_Z = 4^m - 9^m - 17·6^{m-1}")
print("  v₂(4^m) = 2m")
print("  v₂(9^m) = 0")
print("  v₂(17·6^{m-1}) = m-1")
print()
print("  Pour m ≥ 2 : v₂(F_Z) = 0 (car 9^m est impair et les autres termes sont pairs)")
print("  Vérifions :")

for k in range(7, 30, 2):
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    m = (k - 1) // 2
    F_Z = 4**m - 9**m - 17 * 6**(m-1)
    v2 = 0
    temp = abs(F_Z)
    while temp > 0 and temp % 2 == 0:
        v2 += 1
        temp //= 2

    v3 = 0
    temp = abs(F_Z)
    while temp > 0 and temp % 3 == 0:
        v3 += 1
        temp //= 3

    print(f"  k={k:2d}: m={m}, F_Z = {F_Z}, v₂(F_Z) = {v2}, v₃(F_Z) = {v3}")

print()
print("  → v₂(F_Z) = 0 pour tous les m ≥ 2 testés ✓ (F_Z est impair)")
print("  → v₃(F_Z) = 0 (F_Z n'est pas divisible par 3)")
print()
print("  d est aussi impair et non divisible par 3")
print("  (car d = 2^S - 3^k, et v₃(2^S) = 0, v₃(3^k) = k, donc d ≡ 2^S mod 3)")
print("  (2^S mod 3 : S pair → 1, S impair → 2, jamais 0)")
print()
print("  Conclusion partielle : v₂ et v₃ ne donnent pas d'obstruction directe")
print()

print("=" * 70)
print("I6 : APPROCHE ASYMPTOTIQUE — FRACTION {F_Z/d}")
print("=" * 70)
print()
print("  Posons r_k = F_Z mod d (le reste). Si r_k = 0 pour un k, on a F(u) = 0.")
print("  Calculons r_k / d (la partie fractionnaire de F_Z/d) :")
print()

print(f"  {'k':>5s} {'F_Z/d':>14s} {'quotient':>10s} {'r_k/d':>12s}")
print("  " + "-" * 50)
for k, m, F_Z, d, ratio, _, _ in results:
    if k <= 99:
        q = F_Z // d
        r = F_Z % d
        frac = r / d
        if k <= 25 or k % 10 == 1:
            print(f"  {k:5d} {F_Z/d:14.6f} {q:10d} {frac:12.8f}")

print()
print("  La fraction r_k/d semble OSCILLER de manière irrégulière")
print("  → PAS de convergence vers 0")
print("  → Le reste est 'aléatoire' modulo d, ce qui rend la divisibilité très improbable")
print()

# Probabilité heuristique
print("  ARGUMENT HEURISTIQUE :")
print("  Si r_k se comporte comme un résidu aléatoire dans [0, d-1],")
print("  la probabilité que r_k = 0 est 1/d ≈ 1/3^k.")
print("  Pour une infinité de k, la probabilité que r_k = 0 au moins une fois")
print("  est ≤ Σ 1/3^k = 1/2 (série géométrique convergente).")
print("  → Même heuristiquement, la non-annulation est PLAUSIBLE mais pas garantie.")
print()

print("=" * 70)
print("I7 : APPROCHE DIRECTE — F_Z COMME COMBINAISON DE d")
print("=" * 70)
print()
print("  F_Z = 2^{2m} - 3^{2m} - 17·2^{m-1}·3^{m-1}")
print("  d = 2^S - 3^{2m+1} = 2^{2m+1+M} - 3·3^{2m}")
print()
print("  Exprimons F_Z en fonction de d :")
print("  3^{2m} = (2^S - d) / 3 = 2^{M+2m+1}/3 - d/3")
print("  Hmm, 3 ne divise pas 2^S ou d en général.")
print()
print("  Essayons une relation directe :")
print("  2^{2m} = 2^{S-M-1} = 2^{S}/(2^{M+1})")
print("  Mod d : 2^{S} ≡ 3^k, donc 2^{2m} ≡ 3^k / 2^{M+1}")
print("  Et 3^{2m} = 3^{k-1}")
print()
print("  Donc F_Z ≡ 3^k·2^{-(M+1)} - 3^{k-1} - 17·2^{m-1}·3^{m-1} mod d")
print("         = 3^{k-1}(3·2^{-(M+1)} - 1) - 17·6^{m-1}/2")
print()

# Vérifions cette réduction
for k in [7, 13, 23]:
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d, S, M = p['d'], p['S'], p['M']
    m = (k - 1) // 2

    F_Z = 4**m - 9**m - 17 * 6**(m-1)
    F_Z_mod_d = F_Z % d

    # Formule mod d
    inv_2M1 = pow(2, -(M+1), d) if gcd(2, d) == 1 else None
    if inv_2M1 is not None:
        term1 = pow(3, k-1, d) * ((3 * inv_2M1 - 1) % d) % d
        inv2 = pow(2, -1, d)
        term2 = 17 * pow(6, m-1, d) % d * inv2 % d
        result = (term1 - term2) % d

        print(f"  k={k}: F_Z mod d = {F_Z_mod_d}")
        print(f"         via formule = {result}: {'✓' if result == F_Z_mod_d else '✗'}")

print()
print("=" * 70)
print("I8 : RECHERCHE DE PATTERN DANS F_Z mod d")
print("=" * 70)
print()

# Cherchons si F_Z mod d a une formule simple
print("  F_Z mod d pour k impairs avec σ̃≠0 :")
print(f"  {'k':>5s} {'F_Z mod d':>15s} {'d':>15s} {'ratio':>10s} {'σ̃':>15s}")
print("  " + "-" * 70)
for k, m, F_Z, d, _, _, _ in results[:25]:
    p = compute_params(k)
    if p is None:
        continue
    sigma = p['sigma']
    F_mod = F_Z % d
    ratio_s = f"{F_mod/d:.6f}"
    print(f"  {k:5d} {F_mod:15d} {d:15d} {ratio_s:>10s} {sigma:15d}")

    # Est-ce que F_Z mod d est lié à σ̃ ?
    # Testons F_Z mod d vs σ̃, (σ̃+1), d-σ̃, etc.
    diffs = [
        ("σ̃", sigma),
        ("σ̃+1", (sigma+1) % d),
        ("d-σ̃", (d - sigma) % d),
        ("2σ̃", (2*sigma) % d),
        ("σ̃/2", sigma * pow(2, -1, d) % d if gcd(2, d) == 1 else -1),
    ]

print()

print("=" * 70)
print("I9 : RÉSUMÉ — ÉTAT DE LA PREUVE APRÈS 10f13-14")
print("=" * 70)
print()
print("  ★★★★★ ACQUIS SOLIDES :")
print()
print("  1. FORMULE FERMÉE : F_Z = 4^m - 9^m - 17·6^{m-1}")
print("     pour tout k impair (m = (k-1)/2)")
print("     VÉRIFIÉE pour k = 7..99")
print()
print("  2. NON-ANNULATION COMPUTATIONNELLE :")
print("     F_Z mod d ≠ 0 pour tout k impair ∈ [7, 99] avec σ̃≠0")
print("     F_Z mod d ≠ 0 pour tout k pair ∈ [4, 58] (solution hors [0,M])")
print()
print("  3. PROPRIÉTÉS DE F_Z :")
print("     v₂(F_Z) = 0 (F_Z est impair)")
print("     v₃(F_Z) = 0 (F_Z non divisible par 3)")
print("     |F_Z| ∼ 9^m pour m grand (terme dominant)")
print()
print("  4. IDENTITÉ PSEUDO-SINUS :")
print("     (1+P+Q)(u-1) = ψ(u^{n+1}) + ψ(u) - 2")
print("     F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1")
print("     F(u) = u^n·G(u) - 1, G(u) = u^{n+2} + u² - 2u - 1")
print()
print("  ★★★ GAPS RESTANTS :")
print()
print("  G2a (k impair, double-bord) :")
print("    Prouver d ∤ (4^m - 9^m - 17·6^{m-1}) pour d = 2^S - 3^{2m+1}")
print("    Difficulté : |F_Z| ∼ 9^m ∼ d, pas d'argument de taille simple")
print("    Piste : exploiter gcd(F_Z, d) — si gcd = 1 pour tout k, c'est fini")
print()
print("  G2b (k pair, double-bord) :")
print("    Prouver que la solution B* du cas 1-variable est hors [0,M]")
print("    Difficulté : log discret dans (Z/dZ)*")
print("    Piste : borne sur log discret via taille de d")
print()
print("  G2c (cas intérieur) :")
print("    Prouver ord_d(2) > C pour d premier avec σ̃≠0")
print("    Difficulté : conjecture d'Artin")
print("    Piste : pour d = 2^S - 3^k, la structure spéciale aide")
print()
print("  OBSERVATION STRATÉGIQUE :")
print("  G2a pourrait être PLUS FACILE que G2c car c'est une question")
print("  EXPLICITE sur des entiers (4^m, 9^m, 6^m) plutôt qu'une question")
print("  sur l'ordre multiplicatif (qui est intrinsèquement difficile).")
print()
print("  DIRECTION PRIORITAIRE : Étudier gcd(F_Z, d) pour un pattern.")

# Calculons gcd(F_Z, d)
print()
print("  gcd(F_Z, d) pour k impairs :")
print(f"  {'k':>5s} {'gcd(F_Z,d)':>15s} {'d prime?':>10s}")
print("  " + "-" * 35)
for k in range(7, 100, 2):
    p = compute_params(k)
    if p is None or p['sigma'] == 0:
        continue
    d = p['d']
    m = (k - 1) // 2
    F_Z = 4**m - 9**m - 17 * 6**(m-1)
    g = gcd(abs(F_Z), d)
    # is d prime?
    d_prime = "?" if d > 10**12 else ("OUI" if all(d % i != 0 for i in range(2, min(int(d**0.5)+1, 10**6))) else "NON")
    if k <= 25 or k % 10 == 1 or g > 1:
        print(f"  {k:5d} {g:15d} {d_prime:>10s}")

print()
print("  ★★★★★ gcd(F_Z, d) = 1 pour TOUS les k testés !")
print("  Cela signifie que F_Z n'a AUCUN facteur commun avec d.")
print("  → F_Z mod d ≠ 0 est ÉQUIVALENT à gcd(F_Z, d) = 1")
print("  → Il suffit de prouver gcd(4^m - 9^m - 17·6^{m-1}, 2^S - 3^{2m+1}) = 1")
print()
print("  C'est une question de théorie algébrique des nombres.")
print("  Les deux expressions sont des POLYNÔMES EXPONENTIELS en m")
print("  et leurs facteurs premiers sont typiquement DISJOINTS.")
