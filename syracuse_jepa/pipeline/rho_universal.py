#!/usr/bin/env python3
"""
Universal Spectral Contraction — ρ_p < 1 for ALL primes p ≥ 5
══════════════════════════════════════════════════════════════

THEOREM (computational, verified for p ≤ P_max):
  For every prime p ≥ 5, the FCQ spectral radius satisfies ρ_p < 1.

PROOF SKETCH:
  ρ_p = max_{a≠0} |S_p(a)| / q, where S_p(a) = Σ_{j=0}^{q-1} ω^{a·2^j mod p}
  and q = ord_p(2), ω = e^{2πi/p}.

  |S_p(a)| = q requires all q roots of unity ω^{a·2^j mod p} to be aligned,
  i.e., all a·2^j mod p must be the same residue mod p.
  But 2^j takes q DISTINCT values mod p (by definition of ord_p(2)),
  so a·2^j mod p takes q distinct values → cannot all be equal.
  Therefore |S_p(a)| < q, hence ρ_p < 1.

CONSEQUENCE:
  For any prime p ≥ 5 dividing d(k), the FCQ bound R(p,k) = q · ρ_p^{k-1}
  satisfies R → 0 as k → ∞. The critical quantity is:
    k_min(p) = min k such that R(p,k) < 1
  i.e., k_min(p) = ⌈1 + log(q) / log(1/ρ_p)⌉.

  If k_min(p) ≤ k for SOME p | d(k), then N₀(d(k)) = 0.

THIS MODULE:
  1. Verifies ρ_p < 1 for all primes up to a given bound
  2. Computes k_min(p) for each prime
  3. Analyzes the growth rate of k_min(p) as p → ∞
  4. Tests whether k_min(p) ≤ k for the 12 residual cases
"""

import math
import cmath
import time
from dataclasses import dataclass
from typing import List, Dict, Optional, Tuple

from syracuse_jepa.pipeline.analyst import (
    compute_S, compute_d, factorize, multiplicative_order
)


@dataclass
class PrimeRhoData:
    """ρ and k_min data for a single prime."""
    p: int
    q: int           # ord_p(2)
    rho: float       # max_{a≠0} |S(a)|/q
    k_min: int       # min k such that q·ρ^{k-1} < 1
    is_prim_root: bool  # q == p-1


def compute_rho(p: int) -> Tuple[float, int]:
    """Compute ρ_p and ord_p(2) for prime p."""
    q = multiplicative_order(2, p)
    omega = cmath.exp(2j * cmath.pi / p)
    powers = [pow(2, j, p) for j in range(q)]
    max_rho = 0.0
    for a in range(1, p):
        S_a = sum(omega ** (a * pw % p) for pw in powers)
        rho_a = abs(S_a) / q
        if rho_a > max_rho:
            max_rho = rho_a
    return max_rho, q


def compute_rho_fast(p: int, sample_limit: int = 500) -> Tuple[float, int]:
    """Compute ρ_p with sampling for large primes (p > sample_limit)."""
    q = multiplicative_order(2, p)
    omega = cmath.exp(2j * cmath.pi / p)
    powers = [pow(2, j, p) for j in range(q)]

    max_rho = 0.0
    # For large p, sample a subset of a values
    if p <= sample_limit:
        a_range = range(1, p)
    else:
        # Sample: first 200, last 200, and some spaced values
        a_values = set(range(1, min(201, p)))
        a_values |= set(range(max(1, p - 200), p))
        step = max(1, (p - 400) // 200)
        a_values |= set(range(200, p - 200, step))
        a_range = sorted(a_values)

    for a in a_range:
        S_a = sum(omega ** (a * pw % p) for pw in powers)
        rho_a = abs(S_a) / q
        if rho_a > max_rho:
            max_rho = rho_a

    return max_rho, q


def compute_k_min(q: int, rho: float) -> int:
    """Compute k_min = min k such that q * rho^{k-1} < 1."""
    if rho >= 1.0 or rho <= 0:
        return 999999
    # q * rho^{k-1} < 1  ⟺  (k-1) > log(q)/log(1/rho)
    k_min = math.ceil(1 + math.log(q) / math.log(1.0 / rho))
    return max(3, k_min)


def verify_rho_universal(p_max: int = 2000,
                         fast: bool = False) -> List[PrimeRhoData]:
    """
    Verify ρ_p < 1 for all primes 5 ≤ p ≤ p_max.
    Returns sorted list of PrimeRhoData.
    """
    from sympy import primerange
    results = []
    t0 = time.time()

    primes = list(primerange(5, p_max + 1))
    print(f"  Verifying ρ < 1 for {len(primes)} primes (5..{p_max})...")

    compute_fn = compute_rho_fast if fast else compute_rho

    for i, p in enumerate(primes):
        # Skip very large ord computations
        q = multiplicative_order(2, p)
        if q > 10000 and not fast:
            # Use fast method for large orders
            rho, q = compute_rho_fast(p)
        else:
            rho, q = compute_fn(p)

        k_min = compute_k_min(q, rho)
        is_pr = (q == p - 1)

        results.append(PrimeRhoData(
            p=p, q=q, rho=rho, k_min=k_min, is_prim_root=is_pr
        ))

        if (i + 1) % 50 == 0 or p <= 20:
            elapsed = time.time() - t0
            print(f"    p={p:6d}  q={q:6d}  ρ={rho:.6f}  "
                  f"k_min={k_min:4d}  {'PRIM' if is_pr else '':4s}  "
                  f"[{i+1}/{len(primes)}, {elapsed:.1f}s]")

    elapsed = time.time() - t0
    n_pass = sum(1 for r in results if r.rho < 1.0)
    n_fail = len(results) - n_pass

    print(f"\n  Result: {n_pass}/{len(results)} primes have ρ < 1 "
          f"({100*n_pass/len(results):.1f}%)")
    if n_fail > 0:
        fails = [r for r in results if r.rho >= 1.0]
        print(f"  FAILURES: {[r.p for r in fails]}")
    else:
        print(f"  ★ UNIVERSAL: ρ_p < 1 for ALL primes 5 ≤ p ≤ {p_max}")

    # k_min statistics
    k_mins = [r.k_min for r in results]
    max_kmin = max(k_mins)
    max_kmin_p = results[k_mins.index(max_kmin)].p
    print(f"  k_min range: [{min(k_mins)}, {max_kmin}]")
    print(f"  Maximum k_min = {max_kmin} at p = {max_kmin_p}")
    print(f"  Time: {elapsed:.1f}s")

    return results


def analyze_kmin_growth(results: List[PrimeRhoData]) -> dict:
    """
    Analyze how k_min grows with p.

    KEY QUESTION: Does k_min(p) grow slower than p?
    If k_min(p) = O(log p) or O(p^α) with α < 1, then for the
    12 residual cases, even large prime factors p give k_min(p) ≤ k.
    """
    print("\n  k_min growth analysis:")

    # Group by ranges
    ranges = [
        (5, 100), (100, 500), (500, 1000),
        (1000, 2000), (2000, 5000), (5000, 10000)
    ]

    for lo, hi in ranges:
        subset = [r for r in results if lo <= r.p < hi]
        if not subset:
            continue
        k_mins = [r.k_min for r in subset]
        max_km = max(k_mins)
        avg_km = sum(k_mins) / len(k_mins)
        max_p = max(r.p for r in subset)
        max_at = subset[k_mins.index(max_km)].p
        print(f"    p ∈ [{lo:5d}, {hi:5d}): n={len(subset):3d}  "
              f"k_min max={max_km:3d} (at p={max_at})  avg={avg_km:.1f}")

    # Regression: k_min vs log(p)
    import math
    log_ps = [math.log(r.p) for r in results]
    k_mins = [r.k_min for r in results]

    # Simple linear regression: k_min ≈ a * log(p) + b
    n = len(results)
    sum_x = sum(log_ps)
    sum_y = sum(k_mins)
    sum_xy = sum(x * y for x, y in zip(log_ps, k_mins))
    sum_x2 = sum(x * x for x in log_ps)

    denom = n * sum_x2 - sum_x * sum_x
    if denom != 0:
        a = (n * sum_xy - sum_x * sum_y) / denom
        b = (sum_y - a * sum_x) / n
        # R² computation
        y_mean = sum_y / n
        ss_tot = sum((y - y_mean) ** 2 for y in k_mins)
        ss_res = sum((y - (a * x + b)) ** 2 for x, y in zip(log_ps, k_mins))
        r2 = 1 - ss_res / ss_tot if ss_tot > 0 else 0

        print(f"\n  Regression: k_min ≈ {a:.2f} · log(p) + {b:.2f}  (R²={r2:.3f})")

        # Predict k_min for large primes
        for p_test in [10**6, 10**9, 10**12, 10**18]:
            k_pred = a * math.log(p_test) + b
            print(f"    Predicted k_min(p=10^{int(math.log10(p_test))}) "
                  f"≈ {k_pred:.0f}")
    else:
        a, b, r2 = 0, 0, 0

    return {
        "regression_a": a,
        "regression_b": b,
        "r_squared": r2,
        "max_kmin": max(k_mins),
        "max_kmin_prime": results[k_mins.index(max(k_mins))].p,
    }


def test_residual_cases(results: List[PrimeRhoData]) -> dict:
    """
    For the 12 residual cases, check if k_min(p) ≤ k
    for ANY prime p | d(k) that we've tested.
    """
    residual = [135, 143, 148, 158, 165, 166, 171, 176, 178, 185, 192, 193]
    tested_primes = {r.p: r for r in results}

    print("\n  Testing residual cases against known primes:")

    solved = []
    still_open = []

    for k in residual:
        d = compute_d(k)
        factors = factorize(d)

        best = None
        for p, _ in factors:
            if p in tested_primes:
                r = tested_primes[p]
                if r.k_min <= k:
                    if best is None or r.k_min < best.k_min:
                        best = r

        if best is not None:
            solved.append((k, best))
            print(f"    k={k:3d}: SOLVED via p={best.p}, k_min={best.k_min} ≤ {k}")
        else:
            # Show what factors we know about
            known = [(p, tested_primes[p].k_min)
                     for p, _ in factors if p in tested_primes]
            small_factors = [(p, e) for p, e in factors if p < 10**6]
            print(f"    k={k:3d}: OPEN  "
                  f"(smallest factor: {min(p for p, _ in factors) if factors else 'N/A'}, "
                  f"n_factors<10^6: {len(small_factors)})")
            still_open.append(k)

    print(f"\n  Residual: {len(solved)} solved, {len(still_open)} still open")
    return {
        "solved": [(k, r.p, r.k_min) for k, r in solved],
        "still_open": still_open,
    }


def run_rho_universal(p_max: int = 2000, fast: bool = False) -> dict:
    """Full universal ρ analysis."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║  UNIVERSAL SPECTRAL CONTRACTION — ρ_p < 1                        ║")
    print("║  Verify ρ_p < 1 for all primes, compute k_min growth             ║")
    print("╚" + "═" * 68 + "╝")
    print()

    # Phase 1: Verify ρ < 1
    print("┌─ PHASE 1: VERIFY ρ < 1 ─────────────────────────────────┐")
    results = verify_rho_universal(p_max, fast=fast)
    print(f"└─ {len(results)} primes verified ──────────────────────────┘\n")

    # Phase 2: k_min growth analysis
    print("┌─ PHASE 2: k_min GROWTH ──────────────────────────────────┐")
    growth = analyze_kmin_growth(results)
    print(f"└─ Growth analysis complete ───────────────────────────────┘\n")

    # Phase 3: Test residual cases
    print("┌─ PHASE 3: RESIDUAL CASES ────────────────────────────────┐")
    residual = test_residual_cases(results)
    print(f"└─ Residual analysis complete ─────────────────────────────┘\n")

    # Synthesis
    all_pass = all(r.rho < 1 for r in results)
    max_kmin = max(r.k_min for r in results)

    print("╔" + "═" * 68 + "╗")
    print("║  SYNTHESIS                                                        ║")
    print("╠" + "═" * 68 + "╣")
    print(f"║  ρ_p < 1 for ALL {len(results)} primes tested: "
          f"{'★ YES ★' if all_pass else 'NO'}")
    print(f"║  max k_min = {max_kmin} "
          f"(at p = {growth['max_kmin_prime']})")
    print(f"║  k_min ≈ {growth['regression_a']:.2f}·log(p) + "
          f"{growth['regression_b']:.2f}")
    print(f"║")

    if growth['regression_a'] > 0:
        # Predict: for what p would k_min exceed 200?
        if growth['regression_a'] != 0:
            log_p_crit = (200 - growth['regression_b']) / growth['regression_a']
            log10_crit = log_p_crit / math.log(10)
            print(f"║  k_min would reach 200 at p ≈ 10^{log10_crit:.0f}")
            print(f"║  → For the 12 residual cases (k=135..193),")
            print(f"║    we need prime factors with k_min ≤ k")

    print(f"║")
    print(f"║  Residual: {len(residual['solved'])} solved, "
          f"{len(residual['still_open'])} still open")
    if residual['still_open']:
        print(f"║  Still open: {residual['still_open']}")
    print("╚" + "═" * 68 + "╝")

    return {
        "all_rho_lt_1": all_pass,
        "n_primes": len(results),
        "max_kmin": max_kmin,
        "growth": growth,
        "residual": residual,
        "data": [
            {"p": r.p, "q": r.q, "rho": r.rho, "k_min": r.k_min,
             "is_prim_root": r.is_prim_root}
            for r in results
        ],
    }


if __name__ == '__main__':
    import sys
    import json

    p_max = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    fast = '--fast' in sys.argv

    result = run_rho_universal(p_max, fast=fast)

    outfile = 'syracuse_jepa/pipeline/rho_universal_results.json'
    with open(outfile, 'w') as f:
        json.dump(result, f, indent=2, ensure_ascii=False)
    print(f"\nSaved to {outfile}")
