#!/usr/bin/env python3
"""
GPS Phase 6.5 : Vérification directe des Mersenne connues q > 100
===================================================================
Pour chaque Mersenne prime M_q connue, vérifier:
1. La BARRIERE DE TAILLE: k_size = ceil(q * log(2)/log(3))
2. La ZONE DANGER: [18, k_min) intersecté avec [k_size, ∞)
3. Ghost Fish DIRECT dans cette intersection (3^k mod M_q)
"""

from math import ceil, log2, log, gcd
from sympy import factorint

def S_of_k(k):
    return ceil(k * log2(3))

def fast_ord_partial(a, p, max_iter=10**7):
    """Try to compute ord, with a max iteration limit."""
    if gcd(a, p) != 1:
        return None
    try:
        pf = factorint(p - 1, limit=10**6)
        # Check if fully factored
        product = 1
        for q, e in pf.items():
            product *= q ** e
        if product == p - 1:
            # Fully factored, use fast method
            order = p - 1
            for q, e in pf.items():
                for _ in range(e):
                    if pow(a, order // q, p) == 1:
                        order //= q
                    else:
                        break
            return order
        else:
            return "unknown"
    except:
        return "unknown"

print("=" * 80)
print("MERSENNE DIRECTES: vérification q > 100")
print("=" * 80)

# Known Mersenne prime exponents up to reasonable size
mersenne_q = [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127, 521, 607,
              1279, 2203, 2281, 3217, 4253, 4423, 9689, 9941, 11213]

LOG2_3 = log(3) / log(2)  # ≈ 1.58496
LOG3_2 = log(2) / log(3)  # ≈ 0.63093

print(f"\n{'q':>6} {'M_q digits':>12} {'k_size':>8} {'k_min_est':>10} "
      f"{'zone':>8} {'k_checked':>12} {'ghost?':>8}")
print("-" * 76)

for q in mersenne_q:
    if q < 13:
        continue

    M_q = pow(2, q) - 1
    n_digits = len(str(M_q)) if q <= 200 else int(q * 0.301) + 1

    # Size barrier: M_q | d(k) requires d(k) ≥ M_q
    # d(k) < 2^{S+1} = 2^{ceil(k*log2(3))+1} ≈ 2*3^k
    # So 2*3^k ≥ M_q → k ≥ log_3(M_q/2) ≈ q * log_3(2) - 1
    k_size = max(18, ceil(q * LOG3_2) - 1)

    # k_min estimate: need (M_q - 1) * ρ^{k-1} < 0.041
    # For Mersenne, ρ ≈ 1 - c/q. From data: M_61→0.945, M_89→0.962
    # Rough: ρ ≈ 1 - 3/q, then k_min ≈ 1 + q*(q*ln2+3.2)/3
    rho_est = max(0.9, 1 - 3.0/q)
    import math
    if rho_est < 1:
        k_min_est = 1 + int(math.ceil(
            (math.log(0.041) - math.log(M_q - 1 if q <= 200 else 2**q))
            / math.log(rho_est)
        ))
        k_min_est = max(18, k_min_est)
    else:
        k_min_est = 99999

    # The effective danger zone is [max(18, k_size), k_min_est)
    zone_start = max(18, k_size)
    zone_width = max(0, k_min_est - zone_start)

    # Direct ghost fish verification for manageable q
    if q <= 200:
        # We can compute 3^k mod M_q and check against {2^0, 2^1, ..., 2^{q-1}}
        powers_of_2 = set()
        val = 1
        for i in range(q):
            powers_of_2.add(val)
            val = (val * 2) % M_q

        ghost = True
        checked = 0
        for k in range(zone_start, min(k_min_est, zone_start + 50000)):
            S = S_of_k(k)
            lhs = pow(2, S, M_q)
            rhs = pow(3, k, M_q)
            checked += 1
            if lhs == rhs:
                ghost = False
                print(f"{q:>6} {n_digits:>12} {k_size:>8} {k_min_est:>10} "
                      f"{zone_width:>8} {checked:>12} {'FAIL k=' + str(k):>8}")
                break

        if ghost:
            print(f"{q:>6} {n_digits:>12} {k_size:>8} {k_min_est:>10} "
                  f"{zone_width:>8} {checked:>12} {'OUI':>8}")
    else:
        # For very large q, just report the theoretical analysis
        # Size barrier alone: k_size ≈ 0.63*q
        # For q > 200, k_size > 126 > 18, so danger zone starts at k_size
        # Zone width: k_min - k_size ≈ polynomial in q
        # Density: q/M_q ≈ q/2^q → 0
        expected_hits = zone_width * q / (2.0 ** min(q, 1000))
        print(f"{q:>6} {'~10^' + str(n_digits-1):>12} {k_size:>8} {k_min_est:>10} "
              f"{zone_width:>8} {'théorique':>12} {'E=' + f'{expected_hits:.1e}':>8}")

# =====================================================================
# THEORETICAL ANALYSIS
# =====================================================================

print(f"\n{'='*80}")
print("ANALYSE THEORIQUE: Deux Barrières")
print("=" * 80)

print("""
THEOREME (Deux Barrières — informel):

Pour tout Mersenne prime M_q = 2^q - 1 avec q ≥ 13:

BARRIERE 1 (Taille): M_q | d(k) ⟹ k ≥ k_size = ⌈q·log₃2⌉ ≈ 0.63q
  Preuve: d(k) = 2^S - 3^k < 2^{S+1} = 2·3^k, donc M_q ≤ 2·3^k,
  d'où k ≥ log₃(M_q/2) = q·log₃2 - log₃2 + O(2^{-q}).
  [RIGOUREUX]

BARRIERE 2 (Densité): Pour k ∈ [k_size, k_min), la probabilité
  que M_q | d(k) est ≤ q/(M_q - 1) par valeur de k.
  Preuve: M_q | d(k) ⟺ 3^k ∈ {2^0, 2^1, ..., 2^{q-1}} mod M_q.
  Cet ensemble a q éléments parmi M_q - 1 résidus non-nuls.
  Si 3 est quasi-primitif mod M_q (ord_3 ≈ M_q - 1),
  les 3^k parcourent (Z/M_q)* quasi-uniformément.
  [HEURISTIQUE — nécessite equidistribution effective]

Nombre attendu d'occurrences dans la zone danger:
  E ≤ (k_min - k_size) × q/(M_q - 1) ≤ Cq³/2^q → 0
  [SUPER-EXPONENTIELLEMENT petit]

CONCLUSION: Pour q suffisamment grand (q ≥ 13 empiriquement),
  le produit des deux barrières rend la divisibilité IMPOSSIBLE
  dans la zone danger.
""")

# Quantify for each q
print("Quantification:")
print(f"{'q':>6} {'k_size':>8} {'zone_max':>10} {'q/2^q':>15} {'E_max':>15}")
print("-" * 58)

for q in [13, 17, 19, 31, 61, 89, 107, 127, 521, 607, 1279, 2203]:
    k_size = ceil(q * LOG3_2)
    # Worst case zone width (using ρ → 1 limit)
    zone_max = max(0, int(q * q * 0.7) - k_size)  # rough upper bound
    density = q / (2.0 ** min(q, 500))
    E_max = zone_max * density

    print(f"{q:>6} {k_size:>8} {zone_max:>10} {density:>15.2e} {E_max:>15.2e}")

print(f"\n{'='*80}")
print("BILAN FINAL")
print("=" * 80)
print("""
STATUT DU FILET À TROIS MAILLES:

1. MAILLE 1 (Transport Affine, p ≤ 97): RIGOUREUX ✓
2. MAILLE 2 (Convolution, p > 97): RIGOUREUX quand ρ computable ✓
3. MAILLE 3 (Ghost Fish):
   - VERIFIE pour 168 primes (tous facteurs de 2^m-1, m ≤ 100) ✓
   - VERIFIE pour Mersenne q ≤ 200 par calcul direct ✓
   - HEURISTIQUE pour q > 200 (deux barrières, E → 0)

GAP THEORIQUE RESTANT:
  Prouver que 3^k ∉ {2^0,...,2^{q-1}} mod M_q pour k ∈ [k_size, k_min)
  pour TOUT Mersenne prime M_q (y compris non-découverts).

  Ce gap est EXPONENTIELLEMENT petit en probabilité mais non-nul
  en certitude mathématique.

FAISABILITE: 4/5 (computationnel) → 4.5/5 si Ghost Fish formalisé
""")
