#!/usr/bin/env python3
"""
Artin Primitive Root Study — Le Pont Manquant
══════════════════════════════════════════════

Découverte CCE + Téléologique:
  - Les SEULES paires (k,p) avec N₀(p)=0 (parmi p ≤ 100) sont celles
    où 2 est racine primitive mod p (q = p-1).
  - ρ_p = 1/(p-1) pour ces primes → FCQ contraction MAXIMALE.
  - Taux d'avoidance: 13% primitives vs 0% non-primitives.

QUESTION CENTRALE:
  Pour tout k ≥ 3, est-ce que d(k) = 2^S - 3^k a au moins un
  facteur premier p avec 2 racine primitive mod p ?

  Si OUI + FCQ → N₀(p) = 0 → N₀(d) = 0 par CRT → preuve complète.

CONNEXION À ARTIN:
  La conjecture d'Artin (1927) dit que 2 est racine primitive mod p
  pour une infinité de premiers p. Hooley (1967) l'a prouvée sous GRH.
  Heath-Brown (1986) : au moins UN de {2, 3, 5} est racine primitive
  mod p pour une infinité de p (inconditionnel).

CE QUE NOUS CHERCHONS (plus fort que Artin):
  Non seulement 2 est primitive root pour infiniment beaucoup de p,
  mais CHAQUE d(k) a un tel facteur premier. C'est une propriété
  de la suite spécifique 2^S - 3^k, pas une propriété générique.
"""

import math
from collections import defaultdict
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

from syracuse_jepa.pipeline.analyst import compute_S, compute_d, factorize, multiplicative_order


@dataclass
class ArtinProfile:
    """Artin primitive root profile for d(k)."""
    k: int
    S: int
    d_bits: int
    n_prime_factors: int         # total prime factors of d
    n_small_primes: int          # primes <= 10000
    n_primitive_root: int        # primes where 2 is primitive root
    smallest_primitive: int      # smallest such prime (0 if none found)
    largest_primitive: int       # largest such prime (0 if none found)
    primitive_density: float     # fraction of primes that are primitive root
    best_rho: float              # ρ_p = 1/(p-1) for smallest primitive root prime
    best_R: float                # R(p,k) = (p-1) * (1/(p-1))^{k-1}
    fcq_sufficient: bool         # best_R < 1


def analyze_artin_profile(k: int, max_prime: int = 50000) -> ArtinProfile:
    """
    Analyze the Artin primitive root structure of d(k).
    Find all prime factors where 2 is a primitive root.
    """
    S = compute_S(k)
    d = compute_d(k)

    if d <= 1:
        return ArtinProfile(k=k, S=S, d_bits=0, n_prime_factors=0,
                           n_small_primes=0, n_primitive_root=0,
                           smallest_primitive=0, largest_primitive=0,
                           primitive_density=0, best_rho=1, best_R=float('inf'),
                           fcq_sufficient=False)

    factors = factorize(d)
    small_primes = [(p, e) for p, e in factors if p <= max_prime]
    n_prim = 0
    smallest_prim = 0
    largest_prim = 0

    for p, _ in small_primes:
        q = multiplicative_order(2, p)
        if q == p - 1:  # 2 is primitive root mod p
            n_prim += 1
            if smallest_prim == 0 or p < smallest_prim:
                smallest_prim = p
            if p > largest_prim:
                largest_prim = p

    density = n_prim / len(small_primes) if small_primes else 0

    # FCQ bound for best (smallest) primitive root prime
    if smallest_prim > 0:
        rho = 1 / (smallest_prim - 1)
        R = (smallest_prim - 1) * rho ** (k - 1)
    else:
        rho = 1
        R = float('inf')

    return ArtinProfile(
        k=k, S=S, d_bits=d.bit_length(),
        n_prime_factors=len(factors),
        n_small_primes=len(small_primes),
        n_primitive_root=n_prim,
        smallest_primitive=smallest_prim,
        largest_primitive=largest_prim,
        primitive_density=density,
        best_rho=rho,
        best_R=R,
        fcq_sufficient=R < 1,
    )


def scan_artin_profiles(k_max: int = 80, max_prime: int = 10000) -> List[ArtinProfile]:
    """Scan all k values and build Artin profiles."""
    profiles = []

    print(f"  Scanning k=3..{k_max}, factoring d(k), checking primes <= {max_prime}...")
    print()

    no_primitive = []  # k values with no primitive root prime found

    for k in range(3, k_max + 1):
        profile = analyze_artin_profile(k, max_prime)
        profiles.append(profile)

        if profile.n_primitive_root == 0:
            no_primitive.append(k)
            status = "⚠ NO PRIMITIVE ROOT PRIME"
        elif profile.fcq_sufficient:
            status = f"✓ FCQ via p={profile.smallest_primitive} (R={profile.best_R:.2e})"
        else:
            status = f"~ p={profile.smallest_primitive} but R={profile.best_R:.2e} > 1"

        if k <= 40 or k % 10 == 0 or profile.n_primitive_root == 0:
            print(f"    k={k:3d}  d={profile.d_bits:4d}bit  "
                  f"primes={profile.n_small_primes:3d}  "
                  f"prim_root={profile.n_primitive_root:2d}  "
                  f"{status}")

    print()
    if no_primitive:
        print(f"  ⚠ k values with NO primitive root prime (p ≤ {max_prime}): {no_primitive}")
    else:
        print(f"  ✓ ALL k=3..{k_max} have at least one primitive root prime (p ≤ {max_prime})")

    n_fcq = sum(1 for p in profiles if p.fcq_sufficient)
    print(f"  FCQ sufficient: {n_fcq}/{len(profiles)}")

    return profiles


def analyze_primitive_density_trend(profiles: List[ArtinProfile]) -> dict:
    """
    Analyze how the density of Artin primes among factors of d(k) evolves.

    Artin's conjecture predicts density ≈ 0.3739... (Artin's constant)
    among all primes. Does the same hold for factors of d(k)?
    """
    ARTIN_CONSTANT = 0.3739558136  # product over primes of 1 - 1/(p(p-1))

    k_vals = [p.k for p in profiles if p.n_small_primes >= 3]
    densities = [p.primitive_density for p in profiles if p.n_small_primes >= 3]

    if not densities:
        return {"status": "insufficient_data"}

    mean_density = sum(densities) / len(densities)
    trend_positive = densities[-1] > densities[0] if len(densities) >= 2 else False

    # Is density consistent with Artin's constant?
    deviation = abs(mean_density - ARTIN_CONSTANT) / ARTIN_CONSTANT

    return {
        "artin_constant": ARTIN_CONSTANT,
        "observed_mean_density": mean_density,
        "deviation_from_artin": deviation,
        "consistent_with_artin": deviation < 0.3,
        "trend": "increasing" if trend_positive else "decreasing",
        "n_datapoints": len(densities),
    }


def find_minimal_k_for_fcq(profiles: List[ArtinProfile]) -> dict:
    """
    For each k, what is the minimal prime p that makes FCQ work?
    How does this scale with k?
    """
    results = {}

    for profile in profiles:
        if profile.fcq_sufficient:
            results[profile.k] = {
                "p": profile.smallest_primitive,
                "rho": profile.best_rho,
                "R": profile.best_R,
                "k_times_log_rho": profile.k * abs(math.log(profile.best_rho)) if profile.best_rho < 1 else 0,
            }

    if results:
        # How does the required prime grow with k?
        k_vals = sorted(results.keys())
        p_vals = [results[k]["p"] for k in k_vals]

        # Fit log(p) vs k
        if len(k_vals) >= 5:
            n = len(k_vals)
            mean_k = sum(k_vals) / n
            mean_logp = sum(math.log(p) for p in p_vals) / n
            cov = sum((k - mean_k) * (math.log(p) - mean_logp) for k, p in zip(k_vals, p_vals)) / n
            var_k = sum((k - mean_k) ** 2 for k in k_vals) / n
            if var_k > 0:
                slope = cov / var_k
                return {
                    "n_fcq_proved": len(results),
                    "smallest_primes": {k: results[k]["p"] for k in k_vals[:10]},
                    "log_p_slope": slope,
                    "interpretation": f"log(p_min) grows at ~{slope:.3f} per unit k "
                                     f"→ p_min ~ exp({slope:.3f}·k)",
                }

    return {"n_fcq_proved": len(results)}


def run_artin_study(k_max: int = 60, max_prime: int = 10000) -> dict:
    """Full Artin primitive root study for d(k)."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║  ARTIN PRIMITIVE ROOT STUDY — Le Pont Manquant                   ║")
    print("║  2 est-il racine primitive mod p pour au moins un p|d(k) ?       ║")
    print("╚" + "═" * 68 + "╝")
    print()

    # Phase 1: Scan profiles
    print("┌─ PHASE 1: ARTIN PROFILES ─────────────────────────────────┐")
    profiles = scan_artin_profiles(k_max, max_prime)
    print(f"└─ {len(profiles)} profiles built ──────────────────────────┘\n")

    # Phase 2: Density trend
    print("┌─ PHASE 2: DENSITY TREND ──────────────────────────────────┐")
    density = analyze_primitive_density_trend(profiles)
    print(f"  Artin's constant: {density.get('artin_constant', 'N/A'):.6f}")
    print(f"  Observed mean:    {density.get('observed_mean_density', 'N/A'):.6f}")
    print(f"  Deviation:        {density.get('deviation_from_artin', 'N/A'):.2%}")
    print(f"  Consistent:       {density.get('consistent_with_artin', 'N/A')}")
    print(f"└─ Density analysis complete ───────────────────────────────┘\n")

    # Phase 3: FCQ scaling
    print("┌─ PHASE 3: FCQ SCALING ────────────────────────────────────┐")
    fcq_scaling = find_minimal_k_for_fcq(profiles)
    print(f"  FCQ proved: {fcq_scaling.get('n_fcq_proved', 0)} k values")
    if 'log_p_slope' in fcq_scaling:
        print(f"  p_min growth: {fcq_scaling['interpretation']}")
    if 'smallest_primes' in fcq_scaling:
        for k, p in list(fcq_scaling['smallest_primes'].items())[:10]:
            print(f"    k={k:3d}: p_min = {p}")
    print(f"└─ FCQ scaling analysis complete ───────────────────────────┘\n")

    # Synthesis
    print("╔" + "═" * 68 + "╗")
    print("║  ARTIN SYNTHESIS                                                 ║")
    print("╠" + "═" * 68 + "╣")

    all_have_prim = all(p.n_primitive_root > 0 for p in profiles)
    if all_have_prim:
        print(f"║  ✓ ALL k=3..{k_max} have primitive root primes among factors of d(k)")
        print(f"║  → This is CONSISTENT with Artin's conjecture + d(k) specifics")
        print(f"║  → But NOT a proof (need Artin-type result for 2^S-3^k factors)")
    else:
        missing = [p.k for p in profiles if p.n_primitive_root == 0]
        print(f"║  ⚠ k values without primitive root prime: {missing}")
        print(f"║  → Need larger prime search or different approach for these k")

    n_fcq = sum(1 for p in profiles if p.fcq_sufficient)
    print(f"║  FCQ sufficient for {n_fcq}/{len(profiles)} k values")

    if all_have_prim:
        print(f"║")
        print(f"║  PROOF STRATEGY:")
        print(f"║  1. Prove: d(k) always has a prime factor p with 2 prim root")
        print(f"║  2. Use FCQ: R(p,k) = (p-1) · (1/(p-1))^{{k-1}} < 1 for k ≥ k₀")
        print(f"║  3. Handle finite cases k < k₀ by direct computation")
        print(f"║  Gap: Step 1 needs Artin-type result for 2^S - 3^k")

    print("╚" + "═" * 68 + "╝")

    return {
        "all_have_primitive_root": all_have_prim,
        "n_fcq_sufficient": n_fcq,
        "density": density,
        "fcq_scaling": fcq_scaling,
        "profiles_summary": [
            {"k": p.k, "n_prim": p.n_primitive_root,
             "smallest_prim": p.smallest_primitive,
             "fcq_ok": p.fcq_sufficient}
            for p in profiles
        ],
    }


if __name__ == '__main__':
    import json
    import sys

    k_max = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    result = run_artin_study(k_max, max_prime=10000)

    with open('syracuse_jepa/pipeline/artin_results.json', 'w') as f:
        json.dump(result, f, indent=2, ensure_ascii=False, default=str)
    print(f"\nSaved to artin_results.json")
