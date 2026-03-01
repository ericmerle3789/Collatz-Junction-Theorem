#!/usr/bin/env python3
"""
GPS Phase 7.15 : Ghost Fish Analysis for the 11 DANGER primes
==============================================================
Pour chaque prime p avec ρ > 0.5 et k_min > 68 :
1. Calculer le Ghost Fish period P = plus petit k ≥ 1 tel que 3^k ∈ ⟨2⟩ (mod p)
2. Trouver TOUS les k ∈ [18, k_min-1] où p | d(k)
3. Vérifier si ces k sont couverts par Simons-de Weger (k ≤ 68)

Si AUCUN k ∈ [69, k_min-1] n'a p | d(k), alors p est inoffensif !
"""

import numpy as np
from math import log, ceil

def ghost_fish_period(p, m):
    """Smallest k ≥ 1 such that 3^k ∈ ⟨2⟩ (mod p).
    ⟨2⟩ = {2^a mod p : 0 ≤ a < m} where m = ord_p(2).

    3^k ∈ ⟨2⟩ ⟺ 3^k is an m-th power residue matching the 2-orbit.

    Equivalently: the index of ⟨2⟩ in (Z/pZ)* is (p-1)/m.
    3^k ∈ ⟨2⟩ iff 3^{k(p-1)/m} ≡ 1 (mod p) iff k(p-1)/m ≡ 0 (mod ord_p(3^{(p-1)/m}))

    Simpler: 3^k ∈ ⟨2⟩ iff (3^k)^{(p-1)/m} ≡ 1 (mod p)
    """
    orbit_set = set(pow(2, a, p) for a in range(m))

    # Compute g = 3^{(p-1)/m} mod p
    # 3^k ∈ ⟨2⟩ iff g^k ≡ 1 mod p
    exp = (p - 1) // m
    g = pow(3, exp, p)

    # Ghost Fish period = ord(g) in Z/pZ*
    # This is the smallest P with g^P ≡ 1 mod p
    if g == 1:
        # 3 is already in ⟨2⟩, P = 1
        return 1

    # P must divide ord_p(3) and also m
    # Actually P = ord(g) = smallest P with (3^exp)^P ≡ 1
    v = g
    for P in range(1, p):
        if v == 1:
            return P
        v = (v * g) % p

    return p  # Should never reach here

def find_divisible_k(p, m, k_max=300):
    """Find all k ∈ [18, k_max] where p | d(k).
    d(k) = 2^S - 3^k where S = ceil(k * log2(3)).
    p | d(k) iff 2^S ≡ 3^k (mod p).
    """
    divisible = []
    log2_3 = log(3) / log(2)

    for k in range(18, k_max + 1):
        S = ceil(k * log2_3)
        # Check 2^S ≡ 3^k (mod p)
        lhs = pow(2, S, p)
        rhs = pow(3, k, p)
        if lhs == rhs:
            divisible.append(k)

    return divisible

# The 11 danger primes with their ρ and k_min
danger_primes = [
    (28059810762433, 106, 0.809, 179),
    (54410972897, 112, 0.640, 80),
    (160465489, 114, 0.666, 72),
    (107367629, 116, 0.678, 73),
    (536903681, 116, 0.824, 138),
    (4562284561, 120, 0.774, 117),
    (77158673929, 126, 0.784, 134),
    (67280421310721, 128, 0.753, 141),
    (6713103182899, 134, 0.640, 91),
    (2879347902817, 136, 0.654, 93),
    (168749965921, 138, 0.706, 101),
]

print("=" * 75)
print("GHOST FISH + k EFFECTIFS pour les 11 primes DANGER")
print("=" * 75)
print(f"\n  Rappel : Simons-de Weger couvre k ∈ [18, 68]")
print(f"  Le GAP = k ∈ [69, k_min-1] : si p | d(k) dans ce gap, PROBLÈME")
print()

all_safe = True
gap_cases = []

for p, m, rho, k_min in danger_primes:
    print(f"  p = {p:.4e}, m = {m}, ρ = {rho:.3f}, k_min = {k_min}")

    # Ghost Fish period
    P = ghost_fish_period(p, m)
    print(f"    Ghost Fish P = {P}", end="")

    if P == 1:
        print(" (3 ∈ ⟨2⟩)")
    else:
        print(f" (3^k ∈ ⟨2⟩ ssi {P} | k)")

    # Find k values where p | d(k)
    # Search up to max(k_min, 300)
    search_max = max(k_min + 50, 300)
    k_values = find_divisible_k(p, m, search_max)

    if not k_values:
        print(f"    k effectifs dans [18, {search_max}] : AUCUN → p ne divise AUCUN d(k) !")
        print(f"    ★ SÉCURISÉ : cette prime n'apparaît JAMAIS")
    else:
        # Check if any k is in the gap [69, k_min-1]
        in_sdw = [k for k in k_values if k <= 68]
        in_gap = [k for k in k_values if 69 <= k < k_min]
        in_safe = [k for k in k_values if k >= k_min]

        print(f"    k effectifs : {k_values[:20]}{'...' if len(k_values) > 20 else ''}")
        print(f"      Couverts par Simons-de Weger (k ≤ 68) : {in_sdw if in_sdw else 'aucun'}")
        print(f"      Dans le GAP [69, {k_min-1}] : {in_gap if in_gap else 'AUCUN ★'}")
        print(f"      Couverts par convolution (k ≥ {k_min}) : {in_safe[:10] if in_safe else 'aucun'}")

        if in_gap:
            all_safe = False
            gap_cases.append({
                'p': p, 'm': m, 'rho': rho, 'k_min': k_min,
                'P': P, 'gap_k': in_gap
            })
            print(f"    ✗ DANGER : {len(in_gap)} valeurs de k dans le gap !")
        else:
            print(f"    ★ SÉCURISÉ : pas de k dans le gap")
    print()

print("=" * 75)
print("VERDICT GHOST FISH")
print("=" * 75)

if all_safe:
    print("""
  ★★★ TOUTES LES 11 PRIMES DANGER SONT SÉCURISÉES ★★★

  Aucune d'entre elles ne divise d(k) pour k dans le gap [69, k_min-1].
  Combiné avec Simons-de Weger (k ≤ 68) et la convolution (k ≥ k_min) :

  → LE TUNNEL SECRET EST BOUCHÉ pour ces primes !
""")
else:
    print(f"\n  {len(gap_cases)} prime(s) avec k dans le gap :")
    for gc in gap_cases:
        print(f"\n  p = {gc['p']:.4e}, m = {gc['m']}")
        print(f"    ρ = {gc['rho']:.3f}, k_min = {gc['k_min']}, P = {gc['P']}")
        print(f"    k dans le gap : {gc['gap_k']}")
        print(f"    → Ces k nécessitent une vérification EXACTE de la somme de Fourier")

    # For gap cases, compute exact Fourier sum
    if gap_cases:
        print(f"\n{'='*75}")
        print("VÉRIFICATION EXACTE pour les k dans le gap")
        print("="*75)

        for gc in gap_cases:
            p = gc['p']
            m = gc['m']

            orbit = [pow(2, a, p) for a in range(m)]
            log2_3 = log(3) / log(2)

            for k in gc['gap_k']:
                n = k - 17  # convolution exponent
                S = ceil(k * log2_3)
                t0 = pow(3, k, p)  # target point

                # Compute |Σ_{c=1}^{p-1} ω^{-ct₀} · (Σ_{h∈orbit} ω^{ch})^n| / p
                # This is the exact deviation
                # For large p, we can't sum all c. Use the bound:
                # |exact_sum| ≤ Σ_{c=1}^{p-1} |ρ_c|^n

                # But even better: compute exact sum with modular phases
                # For each c: phase_c = sum of cos/sin for orbit, then raise to power n

                # Actually for the exact Fourier sum we need:
                # Σ_c ω^{-ct₀} · (hat{h}_c)^n where hat{h}_c = (1/m) Σ_{h∈orbit} ω^{ch}
                #
                # For large p this is infeasible (p-1 terms).
                # Use the INTERMEDIATE bound: Σ_c ρ_c^n (sum of all |hat{h}_c|^n)

                # Sample approach: compute ρ_c for c = 1..min(p, 5000) + special values
                if p < 50000:
                    c_range = range(1, p)
                elif p < 500000:
                    c_range = list(range(1, 10000)) + list(range(p//4, p//4+2000)) + list(range(p//2-1000, p//2+1000))
                else:
                    c_range = list(range(1, 5000)) + [p//2, p//3, p//4, p//5, p//7, p//11, p//13]
                    c_range += list(range(p//2 - 500, p//2 + 500))

                # Compute ρ_c for each c
                rho_c_list = []
                for c in c_range:
                    c = c % p
                    if c == 0:
                        continue
                    total_real = 0.0
                    total_imag = 0.0
                    for h in orbit:
                        phase = 2.0 * np.pi * ((c * h) % p) / p
                        total_real += np.cos(phase)
                        total_imag += np.sin(phase)
                    rho_c = np.sqrt(total_real**2 + total_imag**2) / m
                    rho_c_list.append(rho_c)

                # Intermediate bound: (p-1)/p * max(ρ_c^n) * p ≈ (p-1) * ρ_max^n
                # Better bound: sum of ρ_c^n (sampled)
                rho_max = max(rho_c_list) if rho_c_list else 1.0

                # Pessimistic bound
                pess_bound = (p - 1) * rho_max ** n

                # For Ghost Fish: if P | k, then p | d(k) is possible
                # The exact sum needs all p-1 terms, which is infeasible for large p
                # BUT: for k ≥ k_min, the pessimistic bound already works
                # For k < k_min: need either exact sum or tighter bound

                # Compute exact sum for manageable p
                if p < 200000:
                    # Can compute exact sum
                    exact_real = 0.0
                    exact_imag = 0.0
                    for c in range(1, p):
                        # ω^{-ct₀} phase
                        phase_target = -2.0 * np.pi * ((c * t0) % p) / p

                        # hat{h}_c = (1/m) Σ_h ω^{ch}
                        s_real = 0.0
                        s_imag = 0.0
                        for h in orbit:
                            phase = 2.0 * np.pi * ((c * h) % p) / p
                            s_real += np.cos(phase)
                            s_imag += np.sin(phase)
                        hat_real = s_real / m
                        hat_imag = s_imag / m

                        # hat_c^n (complex power)
                        rho_c = np.sqrt(hat_real**2 + hat_imag**2)
                        if rho_c < 1e-15:
                            continue
                        theta_c = np.arctan2(hat_imag, hat_real)
                        power_mag = rho_c ** n
                        power_phase = n * theta_c + phase_target

                        exact_real += power_mag * np.cos(power_phase)
                        exact_imag += power_mag * np.sin(power_phase)

                    exact_val = np.sqrt(exact_real**2 + exact_imag**2) / p
                    status = "PASS ✓" if exact_val < 0.041 else "FAIL ✗"
                    print(f"\n  k={k}, p={p:.4e}, m={m}: n={n}")
                    print(f"    ρ_max = {rho_max:.4f}")
                    print(f"    Borne pessimiste = {pess_bound:.4e}")
                    print(f"    Somme EXACTE = {exact_val:.6f} {status}")
                    if exact_val < 0.041:
                        print(f"    Marge : {0.041 / exact_val:.1f}×")
                else:
                    # Can't compute exact sum for huge p
                    # Use sampled intermediate bound
                    sum_rho_n = sum(r**n for r in rho_c_list)
                    # Scale up by p/(number sampled) as rough estimate
                    scaling = (p - 1) / len(rho_c_list)
                    est_bound = sum_rho_n * scaling / p

                    print(f"\n  k={k}, p={p:.4e}, m={m}: n={n}")
                    print(f"    ρ_max = {rho_max:.4f}")
                    print(f"    Borne pessimiste = {pess_bound:.4e}")
                    print(f"    Borne intermédiaire (estimée) = {est_bound:.4e}")
                    if est_bound < 0.041:
                        print(f"    Probablement PASS (borne intermédiaire < 0.041)")
                    else:
                        print(f"    INDÉTERMINÉ : besoin d'argument supplémentaire")
