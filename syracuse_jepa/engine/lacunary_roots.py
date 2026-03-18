#!/usr/bin/env python3
"""
LACUNARY ROOTS — Where ARE the roots of F? Why isn't ρ among them?
====================================================================

F_σ(X) = Σ_{i=0}^{k-1} 3^{δ_i} · X^{σ_i} (k-term lacunary polynomial)

For each σ: F_σ has at most k-1 roots in F_p (for p prime | d).
We KNOW ρ is not a root. But WHERE are the roots?

If the roots always fall in a specific SUBSET of F_p that excludes ρ:
that's the structural explanation.
"""

import sys, os
from math import ceil, log2, gcd
from itertools import combinations
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def find_roots_of_F(k, sigma, p):
    """Find all roots of F_σ(X) mod p."""
    deltas = [sigma[i] - i for i in range(k)]
    roots = []
    for x in range(p):
        val = sum(pow(3, deltas[i], p) * pow(x, sigma[i], p) for i in range(k)) % p
        if val == 0:
            roots.append(x)
    return roots


def analyze_root_locations(k_max=8):
    """For each (k, σ, p|d): find roots and check if ρ is ever near them."""
    print("LACUNARY ROOT ANALYSIS")
    print("=" * 65)

    for k in [3, 5, 7]:
        S = compute_S(k)
        d = compute_d(k)
        inv3 = pow(3, -1, d)
        rho = (2 * inv3) % d

        # Factor d
        factors = {}
        n = d
        for p in range(2, min(100000, n)):
            while n % p == 0:
                factors[p] = factors.get(p, 0) + 1
                n //= p
        if n > 1:
            factors[n] = 1

        print(f"\nk={k}, d={d}, ρ={rho}")

        C = count_cumulative_sequences(k, S)
        if C > 2000: continue

        for p in sorted(factors.keys()):
            if p > 5000: continue
            rho_mod_p = rho % p
            print(f"\n  mod p={p}, ρ mod p = {rho_mod_p}")

            all_roots = Counter()
            n_sigma = 0
            rho_is_root_count = 0

            for sigma in enumerate_cumulative_sequences(k, S):
                roots = find_roots_of_F(k, sigma, p)
                for r in roots:
                    all_roots[r] += 1
                n_sigma += 1
                if rho_mod_p in roots:
                    rho_is_root_count += 1

            # Distribution of roots
            print(f"  {n_sigma} sequences tested, {rho_is_root_count} have ρ as root")

            if rho_is_root_count == 0:
                print(f"  ★ ρ is NEVER a root of F_σ mod {p}")

            # Which values ARE roots most often?
            most_common = all_roots.most_common(5)
            print(f"  Most common roots: {most_common}")

            # Is 0 ever a root?
            print(f"  x=0 is root for {all_roots.get(0, 0)} sequences")
            print(f"  x=1 is root for {all_roots.get(1, 0)} sequences")
            print(f"  x=ρ={rho_mod_p} is root for {all_roots.get(rho_mod_p, 0)} sequences")

            # STRUCTURAL: are the roots always in a specific subgroup?
            root_set = set(all_roots.keys())
            # Is root_set ⊂ <2> mod p?
            gen2 = set()
            x = 1
            for _ in range(p):
                gen2.add(x)
                x = (x * 2) % p
                if x == 1: break
            roots_in_gen2 = root_set & gen2
            print(f"  Roots in <2>: {len(roots_in_gen2)}/{len(root_set)}")
            print(f"  ρ in <2>: {rho_mod_p in gen2}")

            # Is root_set ⊂ <3> mod p?
            gen3 = set()
            x = 1
            for _ in range(p):
                gen3.add(x)
                x = (x * 3) % p
                if x == 1: break
            roots_in_gen3 = root_set & gen3
            print(f"  Roots in <3>: {len(roots_in_gen3)}/{len(root_set)}")


if __name__ == '__main__':
    analyze_root_locations()
