#!/usr/bin/env python3
"""
PARITY OBSTRUCTION — Why the nearest n₀ is always EVEN
========================================================

Key finding: for most k, the near-miss n₀ = round(corrSum/d) is EVEN.
A Collatz cycle requires n₀ ODD. This creates a PARITY OBSTRUCTION.

HYPOTHESIS: corrSum(σ) mod d is always ODD (never 0, never even multiple of d).
If true, then corrSum/d is never an integer (since corrSum is odd, d is odd,
so corrSum/d would be odd/odd = integer only if d | corrSum).

Wait — corrSum is always ODD (first term 3^{k-1} is odd, rest are even).
And d is always ODD (2^S - 3^k = even - odd = odd).
So corrSum mod d ranges over {0, 1, ..., d-1}.
If corrSum ≡ 0 mod d, then n₀ = corrSum/d is odd/odd which IS odd.

So the parity of n₀ is not the obstruction per se.
But: n₀ must ALSO satisfy 3n₀+1 ≡ 0 mod 2^{e₁}, i.e., n₀ ≡ (2^{e₁}-1)/3 mod 2^{e₁}.
For e₁=1: n₀ ≡ (2-1)/3... 1/3 mod 2, but 3^{-1} mod 2 = 1, so n₀ ≡ 1 mod 2 (odd). OK.
For e₁=2: n₀ ≡ (4-1)·3^{-1} mod 4 = 3·3 mod 4 = 9 mod 4 = 1 mod 4. So n₀ ≡ 1 mod 4.
For e₁=3: n₀ ≡ (8-1)·3^{-1} mod 8 = 7·3 mod 8 = 21 mod 8 = 5 mod 8.

So the orbit constraint is: n₀ ≡ (2^{e₁}-1)·(3^{-1} mod 2^{e₁}) mod 2^{e₁}.

THIS IS HIGHLY RESTRICTIVE. Only 1 out of 2^{e₁} integers satisfy it.

Combined with n₀ = corrSum/d:
  corrSum ≡ 0 mod d AND corrSum/d ≡ c_{e₁} mod 2^{e₁}
  ⟺ corrSum ≡ 0 mod d AND corrSum ≡ c_{e₁}·d mod d·2^{e₁}

The second condition means corrSum lies in a SPECIFIC coset of d·2^{e₁}.
Since d·2^{e₁} >> d for e₁ ≥ 2, this is a much stricter condition.

KEY IDEA: The combined condition corrSum ≡ c·d mod d·2^{e₁} defines a
lattice in Z with spacing d·2^{e₁}. If the corrSum values don't hit
this lattice, no cycle exists.

For e₁ = σ₁ = first position in the cumulative sequence, e₁ ranges
from 1 to S-k+1. For each e₁, the lattice spacing is d·2^{e₁}.
If d·2^{e₁} > corrSum_max for some e₁, the lattice has no point
in the range — instant kill.

d·2^{e₁} > corrSum_max when 2^{e₁} > corrSum_max/d ≈ C.
i.e., e₁ > log₂(C) ≈ S·H(p₀) where p₀ = (k-1)/(S-1).
For k ≥ 18: C < d, so e₁ > log₂(C) < log₂(d) ≈ S.
Since e₁ < S always, this doesn't immediately kill.
But for moderate e₁ (say e₁ ≈ S/2), d·2^{e₁} > corrSum_max.
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def orbit_required_n0(e1):
    """Compute the required n₀ mod 2^{e₁} from orbit constraint."""
    mod = 2**e1
    inv3 = pow(3, -1, mod)
    return ((mod - 1) * inv3) % mod


def analyze_combined_constraint(k):
    """
    For each σ, the cycle requires:
      corrSum(σ) ≡ 0 mod d
      corrSum(σ)/d ≡ c_{e₁} mod 2^{e₁}  where e₁ = σ₁

    Combined: corrSum(σ) ≡ c_{e₁}·d mod d·2^{e₁}

    Count how many σ have corrSum within the correct coset.
    """
    S = compute_S(k)
    d = compute_d(k)
    if d <= 0: return None
    C = count_cumulative_sequences(k, S)
    if C > 500000: return None

    # For each e₁ value, count sequences in the correct coset
    by_e1 = defaultdict(lambda: {'total': 0, 'in_coset': 0, 'in_mod_d': 0})

    for sigma in enumerate_cumulative_sequences(k, S):
        cs = corrsum_cumulative(sigma, k)
        e1 = sigma[1]  # First individual exponent = σ₁
        mod = d * (2**e1)
        c_e1 = orbit_required_n0(e1)
        target = (c_e1 * d) % mod

        by_e1[e1]['total'] += 1
        if cs % d == 0:
            by_e1[e1]['in_mod_d'] += 1
        if cs % mod == target:
            by_e1[e1]['in_coset'] += 1

    return dict(by_e1)


def main():
    print("PARITY/ORBIT OBSTRUCTION ANALYSIS")
    print("=" * 70)

    for k in range(3, 15):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 500000:
            print(f"\nk={k}: C={C} too large, skipping")
            continue

        result = analyze_combined_constraint(k)
        if not result: continue

        print(f"\nk={k}, S={S}, d={d}, C={C}")
        print(f"  {'e₁':>3} {'#σ':>8} {'mod d=0':>8} {'in coset':>9} "
              f"{'lattice d·2^e₁':>15} {'vs corrSum_max':>15}")

        cs_max = max(corrsum_cumulative(sigma, k)
                     for sigma in enumerate_cumulative_sequences(k, S))

        total_in_coset = 0
        total_mod_d = 0

        for e1 in sorted(result.keys()):
            data = result[e1]
            lattice = d * (2**e1)
            ratio = cs_max / lattice
            total_in_coset += data['in_coset']
            total_mod_d += data['in_mod_d']
            marker = " ← LATTICE > corrSum_max" if lattice > cs_max else ""
            print(f"  {e1:3d} {data['total']:8d} {data['in_mod_d']:8d} "
                  f"{data['in_coset']:9d} {lattice:15d} {ratio:15.2f}{marker}")

        print(f"  TOTAL: mod d=0: {total_mod_d}, in combined coset: {total_in_coset}")
        if total_in_coset == 0 and total_mod_d == 0:
            print(f"  ✓ NO sequence satisfies either condition")
        elif total_mod_d == 0:
            print(f"  ✓ No corrSum ≡ 0 mod d (orbit check unnecessary)")
        elif total_in_coset == 0:
            print(f"  ★ corrSum ≡ 0 mod d exists but NONE in correct orbit coset!")

    # KEY QUESTION: For which e₁ is d·2^{e₁} > corrSum_max?
    print("\n═══ LATTICE KILL THRESHOLD ═══")
    print(f"{'k':>3} {'S':>3} {'d':>10} {'C':>9} {'log₂(C)':>8} {'e₁_kill':>8}")
    for k in range(3, 30):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        # e₁_kill: smallest e₁ such that d·2^{e₁} > C·d (rough upper bound on corrSum_max)
        # Since corrSum_max ≈ 3^{k-1}·2^{S-k+1} ≈ (1/3)·2^S·... hmm
        # Simpler: log₂(corrSum_max) ≈ log₂(d) + log₂(C) (very rough)
        # So e₁_kill ≈ log₂(corrSum_max/d) ≈ log₂(C)
        e1_kill = ceil(log2(C)) if C > 1 else 1
        print(f"{k:3d} {S:3d} {d:10d} {C:9d} {log2(C) if C > 0 else 0:8.1f} {e1_kill:8d}")


if __name__ == '__main__':
    main()
