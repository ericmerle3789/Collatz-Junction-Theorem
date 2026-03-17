#!/usr/bin/env python3
"""
Deep study of ρ_p = N₀(p)·p / C(k) — the normalized avoidance ratio.

If ρ_p < 1 for ALL (k, p) pairs, then corrSum is BIASED AWAY from 0 mod p.
If Π_{p|d} ρ_p < d/C for all k, then N₀(d) = 0 (no cycle exists).

This module computes ρ_p exactly for all feasible (k, p) pairs and studies:
1. Is ρ_p always < 1? (Would mean systematic bias)
2. How does ρ_p depend on p and k?
3. Can we bound ρ_p uniformly?
4. What is the CRT product Π ρ_p / d, and is it always < 1/C?
"""

import math
from typing import Dict, List, Tuple
from syracuse_jepa.pipeline.analyst import compute_S, compute_d, factorize
from syracuse_jepa.pipeline.spectral import count_compositions_with_residue


def study_rho(k_min: int = 3, k_max: int = 80, max_prime: int = 200) -> dict:
    """
    Compute ρ_p = N₀(p)·p/C for all feasible (k, p) pairs.
    Returns detailed analysis.
    """
    all_rho = {}       # (k, p) -> ρ_p
    by_prime = {}      # p -> [(k, ρ_p)]
    by_k = {}          # k -> [(p, ρ_p)]
    max_rho = 0.0
    max_rho_kp = (0, 0)

    print("═══ ρ_p DEEP STUDY ═══")
    print(f"Range: k={k_min}..{k_max}, primes ≤ {max_prime}")
    print()

    for k in range(k_min, k_max + 1):
        if k == 4:
            continue  # phantom
        S = compute_S(k)
        d = compute_d(k)
        factors = factorize(d)
        primes = sorted(set(p for p, _ in factors if p <= max_prime))

        if not primes:
            continue

        by_k[k] = []

        for p in primes:
            n_zero, n_total = count_compositions_with_residue(k, S, p, target_r=0)
            if n_total == 0:
                continue

            rho = n_zero * p / n_total
            all_rho[(k, p)] = rho

            by_k[k].append((p, rho, n_zero, n_total))

            if p not in by_prime:
                by_prime[p] = []
            by_prime[p].append((k, rho))

            if rho > max_rho:
                max_rho = rho
                max_rho_kp = (k, p)

        # Print progress for selected k
        if primes and (k <= 30 or k % 10 == 0):
            rhos_str = ", ".join(f"p={p}:ρ={rho:.4f}" for p, rho, _, _ in by_k[k][:4])
            print(f"  k={k:3d}  d={d.bit_length():3d}bit  {rhos_str}")

    print()
    print(f"  MAX ρ_p = {max_rho:.6f} at k={max_rho_kp[0]}, p={max_rho_kp[1]}")
    print(f"  {'ρ < 1 EVERYWHERE' if max_rho < 1.0 else '⚠ ρ ≥ 1 FOUND'}")
    print()

    # Per-prime analysis
    print("═══ Per-prime ρ statistics ═══")
    for p in sorted(by_prime.keys())[:15]:
        vals = [rho for _, rho in by_prime[p]]
        if vals:
            print(f"  p={p:5d}: n={len(vals):3d}  "
                  f"mean={sum(vals)/len(vals):.4f}  "
                  f"max={max(vals):.4f}  "
                  f"min={min(vals):.4f}  "
                  f"{'< 1 ✓' if max(vals) < 1.0 else '≥ 1 ✗'}")

    # CRT product analysis: does Π(ρ_p/p) < 1/C?
    print()
    print("═══ CRT product Π(N₀(p)/C) vs 1/d ═══")
    print("  If Π(N₀(p)/C) ≤ 1/d then N₀(d) ≤ 1 (so = 0 since no phantom for k≠4)")
    for k in sorted(by_k.keys()):
        if not by_k[k]:
            continue
        d = compute_d(k)
        S = compute_S(k)
        # Product of N₀(p)/C over all small primes
        product = 1.0
        n_total_k = by_k[k][0][3]  # C(k)
        for p, rho, n_zero, n_total in by_k[k]:
            frac = n_zero / n_total  # = N₀(p)/C = ρ/p
            product *= frac

        # Compare to 1/d (if < 1/d, then N₀(d) = 0 by heuristic)
        inv_d = 1.0 / d
        ratio = product / inv_d if inv_d > 0 else float('inf')

        if k <= 30 or k % 10 == 0:
            print(f"  k={k:3d}  Π(N₀(p)/C) = {product:.2e}  "
                  f"1/d = {inv_d:.2e}  "
                  f"ratio = {ratio:.4f}  "
                  f"{'< 1 ✓ (avoidance)' if ratio < 1.0 else '≥ 1 (need more primes)'}")

    # Study ρ_p as function of k for fixed p
    print()
    print("═══ ρ_p trend as k → ∞ (fixed p) ═══")
    for p in sorted(by_prime.keys())[:8]:
        pairs = sorted(by_prime[p])
        if len(pairs) < 4:
            continue
        ks = [k for k, _ in pairs]
        rhos = [r for _, r in pairs]
        # Linear trend
        n = len(ks)
        sx = sum(ks)
        sy = sum(rhos)
        sxx = sum(x*x for x in ks)
        sxy = sum(x*y for x, y in zip(ks, rhos))
        denom = n * sxx - sx * sx
        if denom != 0:
            slope = (n * sxy - sx * sy) / denom
            intercept = (sy - slope * sx) / n
            # Extrapolate to k=100
            rho_100 = intercept + slope * 100
            print(f"  p={p:5d}: ρ ≈ {intercept:.4f} + {slope:+.6f}·k  "
                  f"→ ρ(100) ≈ {rho_100:.4f}  "
                  f"trend={'↓ converging' if slope < -0.001 else '↑ DIVERGING' if slope > 0.001 else '≈ stable'}")

    return {
        'all_rho': all_rho,
        'by_prime': by_prime,
        'by_k': by_k,
        'max_rho': max_rho,
        'max_rho_kp': max_rho_kp,
    }


def study_exponential_sum_approach(k_max: int = 30) -> dict:
    """
    Study the exponential sum S(a,k) = Σ_{A monotone} e^{2πi·a·corrSum(A,k)/d}
    via its proxy: the distribution of corrSum mod d.

    Key quantity: for each a ∈ (Z/dZ)*, compute
      |S(a)| / C = |Σ e^{2πi·a·r/d} · count(r)| / C
    where count(r) = #{A : corrSum(A,k) ≡ r mod d}.

    If max_{a≠0} |S(a)|/C < 1 - δ, then avoidance follows.
    """
    from syracuse_jepa.pipeline.explorer import enumerate_monotone, count_compositions, corrsum
    from collections import Counter

    print()
    print("═══ EXPONENTIAL SUM STUDY ═══")
    print("  Computing |S(a)|/C = operator norm for character a")
    print()

    results = {}
    for k in range(3, min(k_max + 1, 26)):
        if k == 4:
            continue
        S = compute_S(k)
        d = compute_d(k)
        n_comp = count_compositions(k, S)
        if n_comp > 100_000:
            continue

        # Count residue distribution
        residue_counts = Counter()
        for A in enumerate_monotone(k, S):
            cs = corrsum(list(A), k)
            residue_counts[cs % d] += 1

        C = sum(residue_counts.values())

        # For each character a, compute |S(a)|/C
        max_ratio = 0.0
        max_a = 0
        for a in range(1, min(d, 500)):  # sample characters
            # S(a) = Σ_r count(r) · e^{2πi·a·r/d}
            real_part = sum(cnt * math.cos(2 * math.pi * a * r / d)
                          for r, cnt in residue_counts.items())
            imag_part = sum(cnt * math.sin(2 * math.pi * a * r / d)
                          for r, cnt in residue_counts.items())
            magnitude = math.sqrt(real_part**2 + imag_part**2)
            ratio = magnitude / C

            if ratio > max_ratio:
                max_ratio = ratio
                max_a = a

        gap = 1.0 - max_ratio
        n_distinct = len(residue_counts)

        results[k] = {
            'max_char_ratio': max_ratio,
            'max_char': max_a,
            'spectral_gap': gap,
            'n_distinct_residues': n_distinct,
            'C': C,
            'd': d,
        }

        print(f"  k={k:2d}  max|S(a)|/C = {max_ratio:.6f}  "
              f"gap = {gap:.6f}  "
              f"a*={max_a:6d}  "
              f"#residues={n_distinct}/{d}  "
              f"{'GAP > 0 ✓' if gap > 0 else 'NO GAP ✗'}")

    # Trend analysis
    ks = sorted(results.keys())
    gaps = [results[k]['spectral_gap'] for k in ks]
    if len(gaps) >= 5:
        print()
        x = list(range(len(ks)))
        y = gaps
        n = len(x)
        sx = sum(x)
        sy = sum(y)
        sxy = sum(xi*yi for xi, yi in zip(x, y))
        sxx = sum(xi*xi for xi in x)
        denom = n * sxx - sx * sx
        if denom != 0:
            slope = (n * sxy - sx * sy) / denom
            print(f"  Gap trend: slope = {slope:+.6f} per k "
                  f"({'gap shrinking' if slope < 0 else 'gap growing'})")
            print(f"  Min gap observed: {min(gaps):.6f} at k={ks[gaps.index(min(gaps))]}")

    return results


if __name__ == '__main__':
    rho_data = study_rho(3, 80, max_prime=200)
    exp_data = study_exponential_sum_approach(25)
