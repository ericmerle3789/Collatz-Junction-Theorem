#!/usr/bin/env python3
"""
BAKER RESIDUAL ANALYSIS — Can Baker's theorem force |corrSum mod d| ≥ 1?
=========================================================================

The near-miss pattern shows |corrSum - n₀·d| ∈ {1, 2, 4} for k=3..12.
This module investigates whether Baker's theorem on linear forms in
logarithms can provide a LOWER BOUND on this residual.

THE KEY EQUATION:
  corrSum(σ) = n₀ · d  ⟺  Σ 3^{k-1-i} · 2^{σ_i} = n₀ · (2^S - 3^k)

Rewrite:  n₀·2^S - n₀·3^k = Σ 3^{k-1-i} · 2^{σ_i}
     i.e. n₀·2^S = n₀·3^k + corrSum

If n₀ exists (cycle), then:
  n₀ = corrSum / (2^S - 3^k)

Define Λ = S·ln2 - k·ln3 (the linear form). Then:
  d = 2^S - 3^k = 3^k·(e^Λ - 1) ≈ 3^k·Λ for small Λ.

Baker-LMN (1995): |Λ| > exp(-C·(log S)²) for effective C.

NOW: Can we connect the RESIDUAL |corrSum mod d| to Λ?

If corrSum = q·d + r with 0 < r < d, then:
  r = corrSum - q·(2^S - 3^k) = corrSum + q·3^k - q·2^S

This involves MULTIPLE terms. The Baker bound applies to
  |q·2^S - (q·3^k + corrSum)| = |r|

But this is a linear form in TWO exponentials (2^S and 3^k)
with COEFFICIENTS that depend on q and corrSum.

The question: can Baker bound |r| from below?
"""

import sys, os
from math import ceil, log2, log, comb, gcd, exp
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def baker_lmn_bound(k):
    """
    Baker-LMN lower bound on |S·ln2 - k·ln3|.
    From Laurent-Mignotte-Nesterenko (1995), Theorem 2:
    |b₁·ln(a₁) - b₂·ln(a₂)| > exp(-C · h₁ · h₂ · (log B)²)
    where h_i = max(|ln a_i|, 1/D), B = max(|b₁|/h₂, |b₂|/h₁),
    and C is an absolute constant ≈ 30.

    For our case: b₁ = S, a₁ = 2, b₂ = k, a₂ = 3.
    h₁ = ln 2, h₂ = ln 3, B = max(S/ln3, k/ln2).
    C = 30 (simplified from the actual constant).
    """
    S = compute_S(k)
    h1 = log(2)
    h2 = log(3)
    B = max(S / h2, k / h1)
    C = 30  # Simplified constant (actual is ~24.34 from Gouillon 2006)

    lower = exp(-C * h1 * h2 * (log(B))**2)
    actual = abs(S * log(2) - k * log(3))

    return {
        'k': k, 'S': S,
        'Lambda_actual': actual,
        'Lambda_lower_baker': lower,
        'baker_holds': actual > lower,
        'ratio': actual / lower if lower > 0 else float('inf'),
    }


def analyze_residual_vs_baker(k_max=14):
    """
    For each k, compare the actual near-miss residual with Baker-predicted bounds.

    The residual r = corrSum - n₀·d satisfies:
    r = corrSum mod d (when r > 0) or r = -(d - corrSum mod d) (when closer from above).

    We want to check: is |r| bounded below by something related to Baker?
    """
    print("BAKER RESIDUAL ANALYSIS")
    print("=" * 80)
    print(f"{'k':>3} {'d':>10} {'|Λ|':>12} {'Baker lb':>12} {'min|r|':>8} "
          f"{'min|r|/d':>10} {'n₀_near':>8}")
    print("-" * 80)

    results = []

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 500000: continue

        baker = baker_lmn_bound(k)

        # Find minimum |corrSum mod d| (distance to nearest multiple of d)
        min_r = d
        best_sigma = None
        best_n0 = None

        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            r = cs % d
            dist = min(r, d - r)
            if dist < min_r:
                min_r = dist
                best_sigma = sigma
                best_n0 = round(cs / d)

        # Baker bound on Λ gives: d > 3^k · exp(-C·(log S)²)
        # This bounds d from below but doesn't directly bound the residual r.
        #
        # HOWEVER: if we rewrite r = corrSum - n₀·d, and expand:
        # r = Σ 3^{k-1-i}·2^{σ_i} - n₀·2^S + n₀·3^k
        # = n₀·3^k + Σ 3^{k-1-i}·2^{σ_i} - n₀·2^S
        # = 3^{k-1}·(3n₀ + 1) + Σ_{i≥1} 3^{k-1-i}·2^{σ_i} - n₀·2^S
        #
        # The first orbit step gives: n₁ = (3n₀+1)/2^{e₁}
        # So 3n₀+1 = n₁·2^{e₁}
        # And the first term becomes: 3^{k-1}·n₁·2^{e₁}

        ratio_r_d = min_r / d

        print(f"{k:3d} {d:10d} {baker['Lambda_actual']:12.6e} {baker['Lambda_lower_baker']:12.6e} "
              f"{min_r:8d} {ratio_r_d:10.6f} {best_n0:8d}")

        results.append({
            'k': k, 'd': d, 'min_r': min_r, 'n0_nearest': best_n0,
            'Lambda': baker['Lambda_actual'],
            'baker_lower': baker['Lambda_lower_baker'],
            'sigma': best_sigma,
        })

    return results


def explore_residual_formula(k_max=12):
    """
    DEEP: What IS the residual r algebraically?

    r = corrSum - n₀·d where n₀ = round(corrSum/d).

    Substitute Steiner: r = corrSum - n₀·(2^S - 3^k)
    = corrSum + n₀·3^k - n₀·2^S

    Define: A = corrSum + n₀·3^k = Σ 3^{k-1-i}·2^{σ_i} + n₀·3^k
    Then: r = A - n₀·2^S

    Note: A = 3^k·(n₀ + Σ 3^{-1-i}·2^{σ_i}) = 3^k·(n₀ + corrSum/3^k)... hmm

    Actually more useful: think of r as a LINEAR FORM in 2^S and corrSum.
    r = corrSum - n₀·2^S + n₀·3^k

    Since 2^S = 3^k + d: r = corrSum - n₀·(3^k + d) + n₀·3^k = corrSum - n₀·d.
    That's circular.

    Better approach: r relates to the FRACTIONAL PART of corrSum/d.
    {corrSum/d} = r/d (if r > 0) or 1 - |r|/d (if r < 0 in signed sense).

    The fractional part of corrSum/d = {Σ 3^{k-1-i}·2^{σ_i} / (2^S - 3^k)}.

    This is a VERY specific number-theoretic quantity.
    """
    print("\n═══ RESIDUAL ALGEBRAIC STRUCTURE ═══")

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        # Compute the fractional part distribution
        frac_parts = []
        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            frac = (cs % d) / d
            frac_parts.append(frac)

        # The forbidden zone is frac = 0 (or equivalently 1).
        # How close do we get?
        min_frac = min(min(f, 1-f) for f in frac_parts)

        # Three Distance Theorem: for {n·α} on the circle, there are at most
        # 3 distinct gap lengths. Our fractions are NOT of the form {n·α},
        # but the distribution might still be structured.

        # Sort and compute gaps
        sorted_frac = sorted(set(frac_parts))
        gaps = [sorted_frac[i+1] - sorted_frac[i] for i in range(len(sorted_frac)-1)]
        if sorted_frac:
            gaps.append(1 - sorted_frac[-1] + sorted_frac[0])  # wrap-around gap

        n_distinct_gaps = len(set(round(g, 10) for g in gaps))
        min_gap = min(gaps) if gaps else 0
        max_gap = max(gaps) if gaps else 0

        # Is 0 always in the LARGEST gap?
        # The gap containing 0 is: 1 - max(sorted_frac) + min(sorted_frac)
        gap_at_0 = 1 - sorted_frac[-1] + sorted_frac[0] if sorted_frac else 0
        is_largest_gap = gap_at_0 >= max_gap - 1e-10 if gaps else False

        print(f"\n  k={k}, d={d}, C={C}")
        print(f"    min frac to 0: {min_frac:.8f}")
        print(f"    {len(sorted_frac)} distinct fractional parts")
        print(f"    gap at 0: {gap_at_0:.8f} (largest: {max_gap:.8f})")
        print(f"    0 is in largest gap: {is_largest_gap}")
        print(f"    distinct gap sizes: {n_distinct_gaps}")

        if is_largest_gap and C < d:
            print(f"    ★ 0 sits in the LARGEST gap of the fractional part distribution!")


def explore_n0_constraints(k_max=12):
    """
    For each nearest-miss, analyze what n₀ would need to be.
    Check: does n₀ satisfy the ORBIT constraints?
    """
    print("\n═══ ORBIT CONSTRAINT ON NEAREST n₀ ═══")

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 200000: continue

        # Find the σ giving corrSum closest to a multiple of d
        best_dist = d
        best_cs = None
        best_sigma = None

        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            r = cs % d
            dist = min(r, d - r)
            if dist < best_dist:
                best_dist = dist
                best_cs = cs
                best_sigma = sigma

        n0_candidate = round(best_cs / d)
        residual = best_cs - n0_candidate * d

        # Check orbit constraints for this hypothetical n₀
        individual = []
        for i in range(1, len(best_sigma)):
            individual.append(best_sigma[i] - best_sigma[i-1])
        individual.append(S - best_sigma[-1])  # last exponent

        print(f"\n  k={k}, d={d}")
        print(f"    Best σ = {best_sigma}")
        print(f"    Individual exponents: {individual}")
        print(f"    corrSum = {best_cs}, residual = {residual}")
        print(f"    Hypothetical n₀ = {n0_candidate}")

        # Check: 3·n₀ + 1 ≡ 0 mod 2^{e₁}?
        e1 = individual[0]
        check_e1 = (3 * n0_candidate + 1) % (2**e1)
        print(f"    3n₀+1 mod 2^{e1} = {check_e1} (need 0 for valid orbit)")

        if check_e1 != 0:
            print(f"    ✗ ORBIT FAILS at first step! n₀={n0_candidate} incompatible with e₁={e1}")
        else:
            n1 = (3 * n0_candidate + 1) // (2**e1)
            print(f"    n₁ = {n1} (odd: {n1 % 2 == 1})")

            # Continue orbit
            orbit = [n0_candidate, n1]
            valid = True
            for i, e in enumerate(individual[1:], 2):
                n_prev = orbit[-1]
                num = 3 * n_prev + 1
                if num % (2**e) != 0:
                    print(f"    ✗ ORBIT FAILS at step {i}: 3·{n_prev}+1 = {num} not div by 2^{e}")
                    valid = False
                    break
                n_next = num // (2**e)
                orbit.append(n_next)

            if valid:
                closes = orbit[-1] == orbit[0]
                print(f"    Orbit: {orbit}")
                print(f"    Closes: {closes}")
                if closes:
                    print(f"    ★★★ VALID CYCLE FOUND ★★★")
                else:
                    print(f"    Orbit does not close (last = {orbit[-1]} ≠ first = {orbit[0]})")


if __name__ == '__main__':
    results = analyze_residual_vs_baker()
    explore_residual_formula()
    explore_n0_constraints()

    # Save results
    print("\n═══ SUMMARY ═══")
    for r in results:
        min_r = r['min_r']
        d = r['d']
        print(f"  k={r['k']}: min|residual|={min_r}, d={d}, "
              f"min|r|/d={min_r/d:.8f}, Λ={r['Lambda']:.6e}")

    # KEY question: is min|r| always ≥ 1?
    all_positive = all(r['min_r'] >= 1 for r in results)
    print(f"\n  min|residual| ≥ 1 for ALL tested k: {all_positive}")
    if all_positive:
        print("  THIS NEEDS TO BE PROVED FOR ALL k.")
