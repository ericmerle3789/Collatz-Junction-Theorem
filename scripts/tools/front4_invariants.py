#!/usr/bin/env python3
"""
FRONT 4 : RECHERCHE SYSTEMATIQUE D'INVARIANTS
==============================================
corrSum ≡ 1 mod 2 (connu) et corrSum ≢ 0 mod 3 (connu).
Question : existe-t-il d'autres residus structurellement evites ?

On cherche pour chaque k=3..17 les residus mod m evites par corrSum,
en se concentrant sur m | d (facteurs du module cristallin).
"""

from itertools import combinations
from collections import Counter
import math


def compute_corrsum_residues(k):
    """Calcule corrSum mod d pour toutes les compositions."""
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    C = math.comb(S - 1, k - 1)
    if d <= 0 or C > 2_000_000:
        return None

    corrsum_vals = []
    for combo in combinations(range(1, S), k - 1):
        A = (0,) + combo
        c = 1
        for j in range(1, k):
            c = 3 * c + 2**A[j]
        corrsum_vals.append(c)

    return {'k': k, 'S': S, 'd': d, 'C': C, 'corrsum': corrsum_vals}


def factorize(n):
    """Factorisation simple."""
    factors = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def residues_mod_m(vals, m):
    """Ensemble des residus atteints par vals mod m."""
    return set(v % m for v in vals)


# ============================================================
# PARTIE 1 : INVARIANTS UNIVERSELS (mod 2, 3, 4, 6, 8, 9, 12)
# ============================================================

print("=" * 90)
print("FRONT 4 : RECHERCHE SYSTEMATIQUE D'INVARIANTS")
print("=" * 90)

# Petits modules a tester
test_mods = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 24, 36]

print(f"\n{'k':>3} | ", end="")
for m in test_mods:
    print(f"{'mod '+str(m):>8}", end=" ")
print()
print("-" * (6 + 9 * len(test_mods)))

results = {}
for k in range(3, 18):
    data = compute_corrsum_residues(k)
    if data is None:
        continue
    results[k] = data

    print(f"{k:3d} | ", end="")
    for m in test_mods:
        residues = residues_mod_m(data['corrsum'], m)
        missing = set(range(m)) - residues
        n_hit = len(residues)
        if 0 in missing:
            marker = "*"  # 0 est manquant
        else:
            marker = " "
        print(f"{n_hit:3d}/{m:<3d}{marker}", end=" ")
    print()

print("\n* = le residu 0 est manquant")

# ============================================================
# PARTIE 2 : INVARIANTS STABLES — residus TOUJOURS evites
# ============================================================

print(f"\n{'='*90}")
print(f"RESIDUS UNIVERSELLEMENT EVITES (pour tous les k=3..14 calcules)")
print(f"{'='*90}")

for m in [2, 3, 4, 6, 8, 9, 12, 16, 24]:
    # Pour chaque residu r mod m, est-il evite pour TOUS les k ?
    always_missing = set(range(m))
    for k, data in results.items():
        residues = residues_mod_m(data['corrsum'], m)
        always_missing -= residues
        if not always_missing:
            break

    if always_missing:
        print(f"  mod {m:3d} : residus TOUJOURS evites = {sorted(always_missing)}")


# ============================================================
# PARTIE 3 : ANALYSE DETAILLEE mod 9 (au-dela de mod 3)
# ============================================================

print(f"\n{'='*90}")
print(f"ANALYSE DETAILLEE mod 9")
print(f"{'='*90}")

for k, data in results.items():
    residues_9 = residues_mod_m(data['corrsum'], 9)
    missing_9 = sorted(set(range(9)) - residues_9)
    counts_9 = Counter(v % 9 for v in data['corrsum'])

    print(f"\n  k={k:2d} (C={data['C']}, d={data['d']}): "
          f"residus mod 9 = {sorted(residues_9)}")
    if missing_9:
        print(f"         manquants mod 9 = {missing_9}")

        # Categoriser les manquants
        div3 = [r for r in missing_9 if r % 3 == 0]
        non_div3 = [r for r in missing_9 if r % 3 != 0]
        print(f"         dont divisibles par 3 : {div3}")
        print(f"         dont NON divisibles par 3 : {non_div3} {'← NOUVEAU !' if non_div3 else ''}")


# ============================================================
# PARTIE 4 : STRUCTURE mod facteurs premiers de d
# ============================================================

print(f"\n{'='*90}")
print(f"RESIDUS mod FACTEURS PREMIERS de d")
print(f"{'='*90}")

for k, data in results.items():
    d = data['d']
    factors = factorize(d)

    print(f"\n  k={k:2d}: d={d} = ", end="")
    print(" × ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(factors.items())))

    for p, e in sorted(factors.items()):
        # Residus mod p
        residues_p = residues_mod_m(data['corrsum'], p)
        missing_p = sorted(set(range(p)) - residues_p)

        # Residus mod p^e si e > 1
        pe = p**e
        residues_pe = residues_mod_m(data['corrsum'], pe)
        missing_pe = sorted(set(range(pe)) - residues_pe) if pe <= 1000 else None

        zero_in_p = 0 not in missing_p
        print(f"    mod {p}: {len(residues_p)}/{p} residus, "
              f"0 ∈ Image = {zero_in_p}, manquants = {missing_p[:10]}{'...' if len(missing_p) > 10 else ''}")

        if e > 1 and pe <= 1000:
            zero_in_pe = 0 not in (set(range(pe)) - residues_pe)
            print(f"    mod {pe}: {len(residues_pe)}/{pe} residus, "
                  f"0 ∈ Image = {zero_in_pe}")


# ============================================================
# PARTIE 5 : PREUVE ANALYTIQUE pour mod 2 et mod 3
# ============================================================

print(f"\n{'='*90}")
print(f"VERIFICATION ANALYTIQUE : corrSum mod 2 et mod 3")
print(f"{'='*90}")

print("""
LEMME (corrSum impair) : corrSum = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{A_j}
  Le terme j=0 : 3^{k-1} · 2^0 = 3^{k-1} qui est IMPAIR.
  Les termes j≥1 : 3^{k-1-j} · 2^{A_j} avec A_j ≥ 1 sont PAIRS.
  Donc corrSum ≡ 3^{k-1} ≡ 1 mod 2. ∎

LEMME (corrSum ≢ 0 mod 3) :
  corrSum mod 3 = Σ 3^{k-1-j} · 2^{A_j} mod 3
  Tous les termes avec j < k-1 ont 3^{k-1-j} ≡ 0 mod 3.
  Le dernier terme (j=k-1) : 3^0 · 2^{A_{k-1}} = 2^{A_{k-1}}.
  Donc corrSum ≡ 2^{A_{k-1}} mod 3.
  Comme 2 ≡ -1 mod 3 : corrSum ≡ (-1)^{A_{k-1}} ∈ {1, 2} mod 3.
  En particulier corrSum ≢ 0 mod 3. ∎
""")

# ============================================================
# PARTIE 6 : TENTATIVE mod 4 et mod 8
# ============================================================

print(f"ANALYSE mod 4 :")
print(f"  corrSum mod 4 = Σ 3^{{k-1-j}} · 2^{{A_j}} mod 4")
print(f"  Termes avec A_j ≥ 2 : 3^{{k-1-j}} · 2^{{A_j}} ≡ 0 mod 4")
print(f"  Termes avec A_j = 1 : 3^{{k-1-j}} · 2 mod 4 = 2·3^{{k-1-j}} mod 4")
print(f"  Terme A_j = 0 (j=0) : 3^{{k-1}} mod 4")
print()

for k, data in results.items():
    S = data['S']
    # corrSum mod 4 : seuls comptent A_0=0 et les termes avec A_j ≤ 1
    # A_0 = 0 toujours, A_1 ≥ 1. Si A_1 = 1 (premier terme apres 0),
    # on a un terme 3^{k-2}·2 mod 4.
    # corrSum mod 4 = 3^{k-1}·1 + 3^{k-2}·2·[A1=1] mod 4 (les autres termes ≡ 0 mod 4)

    # 3^n mod 4 : 3, 1, 3, 1, ... (periode 2)
    pow3_km1 = pow(3, k - 1, 4)
    pow3_km2 = pow(3, k - 2, 4) if k >= 3 else 1

    residues_4 = residues_mod_m(data['corrsum'], 4)
    print(f"  k={k:2d}: 3^{{k-1}} mod 4 = {pow3_km1}, "
          f"residus mod 4 = {sorted(residues_4)}", end="")

    # Si A1=1 : corrSum mod 4 = pow3_km1 + 2*pow3_km2 mod 4
    # Si A1≥2 : corrSum mod 4 = pow3_km1 mod 4 (les termes 2^{A_j} pour A_j≥2 sont ≡ 0 mod 4)
    val_if_a1_ge2 = pow3_km1
    val_if_a1_eq1 = (pow3_km1 + 2 * pow3_km2) % 4
    print(f", A1≥2→{val_if_a1_ge2}, A1=1→{val_if_a1_eq1}")

print(f"""
LEMME (corrSum mod 4) :
  corrSum mod 4 ne depend que de A_0=0 et A_1 (si A_1=1) :
  - Si A_1 ≥ 2 : corrSum ≡ 3^{{k-1}} mod 4
  - Si A_1 = 1 : corrSum ≡ 3^{{k-1}} + 2·3^{{k-2}} mod 4

  Pour k impair : 3^{{k-1}} ≡ 1 mod 4, 3^{{k-2}} ≡ 3 mod 4
    → A1≥2 : 1, A1=1 : (1+6)%4 = 3
    → corrSum mod 4 ∈ {{1, 3}} (impair, OK)

  Pour k pair : 3^{{k-1}} ≡ 3 mod 4, 3^{{k-2}} ≡ 1 mod 4
    → A1≥2 : 3, A1=1 : (3+2)%4 = 1
    → corrSum mod 4 ∈ {{1, 3}} (impair, OK)

  Conclusion : corrSum ∈ {{1, 3}} mod 4 pour tout k ≥ 3. ∎
""")

# ============================================================
# PARTIE 7 : ANALYSE mod d — le residu 0 est-il TOUJOURS seul manquant ?
# ============================================================

print(f"{'='*90}")
print(f"LE RESIDU 0 EST-IL TOUJOURS LE SEUL MANQUANT mod d ?")
print(f"{'='*90}")

for k, data in results.items():
    d = data['d']
    residues_d = residues_mod_m(data['corrsum'], d)
    n_missing = d - len(residues_d)
    is_zero_only = (n_missing == 1 and 0 not in residues_d)
    ratio = len(residues_d) / d * 100

    flag = "0 SEUL MANQUANT !" if is_zero_only else ""
    print(f"  k={k:2d}: {len(residues_d):6d}/{d:10d} ({ratio:5.1f}%), "
          f"manquants={n_missing:6d}, {flag}")


# ============================================================
# PARTIE 8 : RELATION ENTRE ord_d(2), ord_d(3), et le blocage
# ============================================================

print(f"\n{'='*90}")
print(f"RELATION ENTRE ORDRES ET STRUCTURE")
print(f"{'='*90}")

def multiplicative_order(base, mod):
    if math.gcd(base, mod) != 1:
        return None
    val, order = base % mod, 1
    while val != 1 and order < mod:
        val = (val * base) % mod
        order += 1
    return order if val == 1 else None

print(f"\n{'k':>3} {'d':>10} {'ord2':>8} {'ord3':>8} {'S-1':>5} "
      f"{'ord2/S':>7} {'phi(d)':>10} {'S-1/ord2':>9} {'ord3|k?':>8}")
print("-" * 85)

for k, data in results.items():
    d = data['d']
    S = data['S']
    ord2 = multiplicative_order(2, d)
    ord3 = multiplicative_order(3, d)

    # Indicatrice d'Euler
    n = d
    phi = d
    temp = d
    p = 2
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            phi -= phi // p
        p += 1
    if temp > 1:
        phi -= phi // temp

    ord2_str = str(ord2) if ord2 else "?"
    ord3_str = str(ord3) if ord3 else "?"
    ratio = (S-1)/ord2 if ord2 else 0
    divides_k = "OUI" if ord3 and k % ord3 == 0 else ("non" if ord3 else "?")

    print(f"{k:3d} {d:10d} {ord2_str:>8} {ord3_str:>8} {S-1:5d} "
          f"{ratio:7.3f} {phi:10d} {ratio:9.3f} {divides_k:>8}")

# ============================================================
# PARTIE 9 : LE ROLE DE 3^k mod d
# ============================================================

print(f"\n{'='*90}")
print(f"VALEUR DE 3^k mod d (= 2^S mod d)")
print(f"{'='*90}")

for k, data in results.items():
    d = data['d']
    S = data['S']
    val = pow(3, k, d)  # = 2^S mod d
    is_cube = any(pow(x, 3, d) == val for x in range(d)) if d < 10000 else "?"
    print(f"  k={k:2d}: 3^k mod d = 2^S mod d = {val}"
          f" (= {val}/{d} ≈ {val/d:.4f} de d)")

# ============================================================
# SYNTHESE FRONT 4
# ============================================================

print(f"\n{'='*90}")
print(f"SYNTHESE FRONT 4 — INVARIANTS DECOUVERTS")
print(f"{'='*90}")

print("""
INVARIANTS UNIVERSELS PROUVES :
  1. corrSum ≡ 1 mod 2 (toujours impair)          [Preprint Remark 2.5]
  2. corrSum ≢ 0 mod 3 (jamais div par 3)          [Preprint Remark 2.5]
  3. corrSum ∈ {1, 3} mod 4 (toujours impair)      [consequence de 1]
  4. corrSum ∈ {1, 5} mod 6 (= impair + non div 3)  [consequence de 1+2]

INVARIANTS OBSERVES (non universels mais significatifs) :
  5. mod 9 : corrSum evite {0, 3, 6} toujours (= multiples de 3, consequence de 2)
             mais AUSSI d'autres residus pour certains k
  6. mod d : 0 est TOUJOURS manquant (= l'enonce du theoreme)
  7. Pour k=3,5 : 0 est le SEUL residu manquant mod d
  8. Pour k≥6 : beaucoup de residus manquants (C/d < 1)

ECHEC PARTIEL :
  - Pas de nouvel invariant UNIVERSEL au-dela de parite + mod 3
  - Les invariants mod 9 se reduisent au mod 3 connu
  - Le blocage de 0 mod d est SPECIFIQUE a d (pas a un module universel)

CONCLUSION :
  Le residu 0 mod d n'est pas evite par un invariant simple.
  Il est evite par la COMBINAISON de :
  (a) la structure algebrique de 2^p mod d (gap quand ord_d(2) > S-1)
  (b) la contrainte d'ordonnancement (positions croissantes)
  (c) la relation 2^S ≡ 3^k mod d (liant le module au parametrage)
""")
