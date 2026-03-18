#!/usr/bin/env python3
"""
BAKER 3-LOGARITHM APPROACH — Lower bound on |corrSum - n₀·d|
================================================================

The residual r = corrSum - n₀·d = Σ 3^{k-1-i}·2^{σ_i} - n₀·(2^S - 3^k)

Rearrange: r = (Σ 3^{k-1-i}·2^{σ_i} + n₀·3^k) - n₀·2^S

Define A = Σ 3^{k-1-i}·2^{σ_i} + n₀·3^k (a {2,3}-integer)
Then r = A - n₀·2^S.

If r = 0: A = n₀·2^S. This is a PERFECT POWER equation:
a linear combination of 2-powers and 3-powers equals a pure 2-power.

Baker's theorem (3 logarithms version, Baker-Wüstholz 1993):
|Λ| = |b₁·log α₁ + b₂·log α₂ + b₃·log α₃| > exp(-C·h₁·h₂·h₃·log B)

For our case: if r ≠ 0, then r/A ≈ non-zero, giving:
|log(A/(n₀·2^S))| > exp(-C·...) → |r| > A·exp(-C·...)

Since A ≈ n₀·2^S ≈ corrSum: |r| > corrSum · exp(-poly(log(corrSum)))
This is a POLYNOMIAL lower bound on |r|, which is always ≥ 1 (since r ∈ Z).

WAIT: |r| ≥ 1 for r ≠ 0 is TRIVIALLY true (it's an integer!).
The Baker bound gives |r| > exp(-something), but since r is an integer,
|r| ≥ 1 is automatic. Baker doesn't help for the non-vanishing.

The real question is: CAN r = 0? Baker could help if we can reformulate
the problem as a linear form in logarithms.

Actually: r = 0 means corrSum = n₀·d = n₀·(2^S - 3^k).
Equivalently: corrSum + n₀·3^k = n₀·2^S.
Since corrSum is a sum of {2,3}-terms: the LHS is a {2,3}-SMOOTH sum.
And the RHS is n₀·2^S.

If n₀ is {2,3}-smooth: then both sides are {2,3}-smooth, and we have
an equation between S-smooth numbers. Stormer's theorem limits these.

If n₀ has a prime factor p > 3: then LHS must be divisible by p.
But corrSum + n₀·3^k has n₀ as factor only through the n₀·3^k term.
corrSum = Σ 3^{k-1-i}·2^{σ_i} has no factor of n₀ in general.
So for p | n₀: p | (corrSum + n₀·3^k) iff p | corrSum.
This is a CONSTRAINT: every prime factor of n₀ must divide corrSum.

Combined with gcd(corrSum, d) < d (our fact): if n₀ = corrSum/d,
then every prime factor of n₀ divides corrSum AND d divides corrSum.
But gcd(corrSum, d) < d means d does NOT divide corrSum. Contradiction!

WAIT, THAT'S CIRCULAR: gcd(corrSum, d) < d IS the statement N₀ = 0.

OK, Baker doesn't directly help here. But the SMOOTHNESS angle might.

If n₀ is {2,3}-smooth: then n₀ = 2^a · 3^b for some a, b ≥ 0.
The cycle equation n₀·(2^S - 3^k) = corrSum then constrains a, b.
For each (a, b): this is a FINITE set of equations.

Baker's theorem on 2^c - 3^d = m (Pillai-type) gives: for each m,
there are only FINITELY many solutions. With effective bounds.

So: if we enumerate all possible n₀ = 2^a · 3^b up to some BOUND,
and check that none gives corrSum ≡ 0 mod d... this is computational.

For n₀ NOT {2,3}-smooth: n₀ has a prime factor p > 3.
Then p | corrSum (from above). But corrSum = Σ 3^{k-1-i}·2^{σ_i}.
For p > 3: p ∤ 3^{k-1-i}·2^{σ_i} for any i (since gcd(6,p)=1).
So p | corrSum iff p | Σ 3^{k-1-i}·2^{σ_i}.
This is a DIVISIBILITY condition on a weighted 2-sum.

Hmm, this doesn't immediately help. Let me check: for what fraction
of n₀ values does n₀ ACTUALLY divide corrSum for some σ?
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def analyze_smoothness(k_max=10):
    """For hypothetical n₀ = corrSum/d, check if n₀ is {2,3}-smooth."""
    print("SMOOTHNESS ANALYSIS OF n₀ = corrSum/d")
    print("=" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 50000: continue

        # For each σ, compute n₀ = round(corrSum/d) and check smoothness
        nearest_n0s = set()
        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            n0 = round(cs / d)
            if n0 > 0:
                nearest_n0s.add(n0)

        # Check smoothness of nearest n₀ values
        smooth_23 = 0
        not_smooth = 0
        for n0 in nearest_n0s:
            n = n0
            while n % 2 == 0: n //= 2
            while n % 3 == 0: n //= 3
            if n == 1:
                smooth_23 += 1
            else:
                not_smooth += 1

        print(f"  k={k}: {len(nearest_n0s)} distinct nearest n₀, "
              f"{smooth_23} {2,3}-smooth, {not_smooth} not smooth")

        # For the {2,3}-smooth n₀: check if n₀·d is achievable
        # n₀·d = corrSum for some σ?
        achievable = set(corrsum_cumulative(sigma, k)
                        for sigma in enumerate_cumulative_sequences(k, S))

        for n0 in sorted(nearest_n0s)[:10]:
            target_cs = n0 * d
            is_achievable = target_cs in achievable
            # Check smoothness
            n = n0
            while n % 2 == 0: n //= 2
            while n % 3 == 0: n //= 3
            smooth = (n == 1)
            if smooth:
                print(f"    n₀={n0} ({2**0}·{3**0}-smooth): n₀·d={target_cs}, "
                      f"achievable={is_achievable}")


def pillai_connection(k_max=12):
    """
    Pillai's conjecture (proved by Mihailescu 2004 for Catalan):
    |2^a - 3^b| = 1 has only solutions (a,b) = (1,1), (2,1), (3,2).

    More generally: 2^a - 3^b = c has finitely many solutions for each c.

    Our equation: corrSum = n₀·(2^S - 3^k).
    If n₀ = 1: corrSum = 2^S - 3^k. Is corrSum achievable?
    corrSum_min = 3^k - 2^k. And d = 2^S - 3^k.
    For corrSum = d: 3^k - 2^k < d = 2^S - 3^k → 2·3^k < 2^S + 2^k.
    Since 2^S ≈ 3^k: 2·3^k < 3^k + 2^k → 3^k < 2^k. FALSE for k ≥ 1.
    So corrSum_min > d: n₀ ≥ 2. (Reconfirms L1: corrSum > d.)

    For n₀ = 2: corrSum = 2d = 2·(2^S - 3^k) = 2^{S+1} - 2·3^k.
    Is this achievable? Need: Σ 3^{k-1-i}·2^{σ_i} = 2^{S+1} - 2·3^k.
    """
    print("\nPILLAI CONNECTION: Small n₀ analysis")
    print("=" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        achievable = set(corrsum_cumulative(sigma, k)
                        for sigma in enumerate_cumulative_sequences(k, S))

        cs_min = min(achievable)
        cs_max = max(achievable)
        n0_min = cs_min // d + (1 if cs_min % d else 0)
        n0_max = cs_max // d

        print(f"\nk={k}: d={d}, n₀ range=[{n0_min}, {n0_max}]")

        # Check small n₀ values
        for n0 in range(max(1, n0_min), min(n0_max + 1, n0_min + 20)):
            target = n0 * d
            hit = target in achievable
            # Is n₀ odd? (required for cycle)
            odd = n0 % 2 == 1
            marker = ""
            if hit:
                marker = " ★★★ HIT!"
            elif not odd:
                marker = " (even, not valid for cycle)"
            print(f"  n₀={n0:3d} ({'odd' if odd else 'even'}): target={target:10d}, "
                  f"achievable={hit}{marker}")


if __name__ == '__main__':
    analyze_smoothness()
    pillai_connection()
