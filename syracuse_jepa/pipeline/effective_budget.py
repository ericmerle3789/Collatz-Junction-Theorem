#!/usr/bin/env python3
"""
Effective Spectral Budget — CCE Cycle 2 Innovation
═══════════════════════════════════════════════════

DISCOVERY (CCE Cycle 1 + Compression Analysis):
  The "1.35x gap" in the operator framework is an ARTEFACT of assuming
  linear contraction: budget = k × rate.

  REALITY: The effective dimension of monotone compositions is
    dim_eff = log2(C_mono) ~ C_HR * sqrt(S) ~ C_HR * k/sqrt(2)
  while the "linear" model assumes dim = k-1.

  The compression ratio dim_eff/dim_total → 0 as k → ∞.

NEW QUANTITY: Effective Spectral Budget (ESB)
  ESB(k, p) = dim_eff(k) × contraction_per_step(p) - log2(d(k))

  If ESB > 0 for SOME p | d(k), then N₀(p) = 0.

  This is a REFINEMENT of the FCQ bound that accounts for
  the dimensionality reduction from monotonicity.

QUESTION: Does ESB > 0 for more k values than plain FCQ?
If so, the gap is partially or fully closed.
"""

import math
from dataclasses import dataclass
from typing import List, Dict, Optional
import cmath

from syracuse_jepa.pipeline.analyst import (
    compute_S, compute_d, factorize, multiplicative_order
)


@dataclass
class ESBResult:
    """Effective Spectral Budget for one (k, p) pair."""
    k: int
    p: int
    q: int                    # ord_p(2)
    dim_eff: float            # effective dimension under monotonicity
    dim_total: float          # k - 1 (free dimension)
    compression: float        # dim_eff / dim_total
    contraction: float        # -log2(rho) per step
    log2_d: float             # log2(d(k))
    log2_q: float             # log2(q)
    esb: float                # dim_eff * contraction - (log2_d - log2_q)
    fcq_bound: float          # q * rho^{k-1} (standard FCQ)
    esb_positive: bool        # ESB > 0 ⟹ avoidance
    fcq_proves: bool          # standard FCQ proves


def partitions_at_most_k(n: int, k: int) -> int:
    """Count partitions of n into at most k parts."""
    dp = [[0] * (k + 1) for _ in range(n + 1)]
    for j in range(k + 1):
        dp[0][j] = 1
    for i in range(1, n + 1):
        for j in range(1, k + 1):
            dp[i][j] = dp[i][j - 1]
            if i >= j:
                dp[i][j] += dp[i - j][j]
    return dp[n][k]


def compute_rho(p: int) -> float:
    """Compute FCQ spectral radius for prime p."""
    q = multiplicative_order(2, p)
    omega = cmath.exp(2j * cmath.pi / p)
    powers = [pow(2, j, p) for j in range(q)]
    max_rho = 0
    for a in range(1, min(p, 500)):
        S_a = sum(omega ** (a * pw % p) for pw in powers)
        rho_a = abs(S_a) / q
        max_rho = max(max_rho, rho_a)
    return max_rho


def compute_esb(k: int, p: int) -> ESBResult:
    """Compute the Effective Spectral Budget for (k, p)."""
    S = compute_S(k)
    d = compute_d(k)
    q = multiplicative_order(2, p)

    # Dimension calculations
    C_mono = partitions_at_most_k(S, k)
    C_free = math.comb(S + k - 1, k - 1)

    dim_eff = math.log2(C_mono) if C_mono > 1 else 0
    dim_total = math.log2(C_free) if C_free > 1 else k - 1
    compression = dim_eff / dim_total if dim_total > 0 else 1.0

    # Spectral contraction
    rho = compute_rho(p)
    contraction = -math.log2(rho) if 0 < rho < 1 else 0

    # Budget calculation
    log2_d = math.log2(d) if d > 0 else 0
    log2_q = math.log2(q) if q > 0 else 0

    # ESB = effective_contraction_total - target
    # Standard: (k-1) * contraction - (log2_d - log2_q)
    # Effective: dim_eff * (contraction / dim_total * (k-1)) - (log2_d - log2_q)
    # Simplified: the key insight is that the contraction applies to the
    # EFFECTIVE dimension, not the full dimension.

    # Actually, let's think more carefully:
    # Standard FCQ: R = q * rho^{k-1}. Need R < 1, i.e., (k-1)*|log rho| > log q
    # This assumes each of the k-1 steps contributes independently.
    # With monotonicity, the effective number of "free" steps is dim_eff,
    # not k-1. So the effective bound is:
    # R_eff = q * rho^{dim_eff}
    # But this is NOT rigorous — monotonicity constrains the steps, not reduces them.

    # More precise model: The contraction per step varies.
    # Under monotonicity, the FIRST steps have less freedom (small B values),
    # so their contraction is weaker. The LATER steps have more freedom,
    # so their contraction is stronger. The NET effect depends on the
    # distribution of step sizes.

    # For now, compute both models:
    # Model A (standard): R = q * rho^{k-1}
    # Model B (effective): R = q * rho^{dim_eff}  (OPTIMISTIC)
    # Model C (geometric mean): R = q * rho^{sqrt(dim_eff * (k-1))}  (INTERMEDIATE)

    R_standard = q * rho ** (k - 1) if rho < 1 else float('inf')
    R_effective = q * rho ** dim_eff if rho < 1 and dim_eff > 0 else float('inf')
    R_geometric = q * rho ** math.sqrt(dim_eff * (k - 1)) if rho < 1 and dim_eff > 0 else float('inf')

    esb = dim_eff * contraction - (log2_d - log2_q)

    return ESBResult(
        k=k, p=p, q=q,
        dim_eff=dim_eff,
        dim_total=dim_total,
        compression=compression,
        contraction=contraction,
        log2_d=log2_d,
        log2_q=log2_q,
        esb=esb,
        fcq_bound=R_standard,
        esb_positive=(esb > 0),
        fcq_proves=(R_standard < 1),
    )


def scan_esb(k_max: int = 50, max_prime: int = 200) -> dict:
    """Scan ESB for all k, comparing standard FCQ vs effective model."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║  EFFECTIVE SPECTRAL BUDGET — CCE Cycle 2                         ║")
    print("║  Does dimensionality reduction help close the gap?               ║")
    print("╚" + "═" * 68 + "╝")
    print()

    results = []
    n_standard_proves = 0
    n_esb_proves = 0
    n_esb_extra = 0  # cases where ESB proves but standard doesn't

    rho_cache = {}

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue

        factors = factorize(d)
        small_primes = sorted(set(p for p, _ in factors if p <= max_prime))

        best_esb = None
        for p in small_primes:
            if S > 300:  # partitions_at_most_k too slow
                continue
            result = compute_esb(k, p)
            if best_esb is None or result.esb > best_esb.esb:
                best_esb = result

        if best_esb is None:
            if k <= 40 or k % 10 == 0:
                print(f"  k={k:3d}  NO SMALL PRIMES")
            continue

        results.append(best_esb)

        if best_esb.fcq_proves:
            n_standard_proves += 1
        if best_esb.esb_positive:
            n_esb_proves += 1
        if best_esb.esb_positive and not best_esb.fcq_proves:
            n_esb_extra += 1

        if k <= 30 or k % 5 == 0:
            std = "FCQ✓" if best_esb.fcq_proves else "FCQ✗"
            esb = "ESB✓" if best_esb.esb_positive else "ESB✗"
            extra = " ★NEW" if best_esb.esb_positive and not best_esb.fcq_proves else ""
            print(f"  k={k:3d}  p={best_esb.p:5d}  compress={best_esb.compression:.3f}  "
                  f"ESB={best_esb.esb:+8.1f}  {std} {esb}{extra}")

    print()
    print("╔" + "═" * 68 + "╗")
    print("║  ESB SYNTHESIS                                                   ║")
    print("╠" + "═" * 68 + "╣")
    print(f"║  Standard FCQ proves:  {n_standard_proves}/{len(results)}")
    print(f"║  ESB (effective) proves: {n_esb_proves}/{len(results)}")
    print(f"║  NEW cases (ESB only):   {n_esb_extra}")
    print(f"║")

    if n_esb_extra > 0:
        print(f"║  ★ ESB proves {n_esb_extra} ADDITIONAL cases beyond standard FCQ!")
        print(f"║  → Dimensionality reduction IS quantitatively useful")
    else:
        print(f"║  ESB does NOT prove additional cases beyond standard FCQ")
        print(f"║  → The effective dimension model is too OPTIMISTIC")
        print(f"║  → Need a rigorous version that accounts for step correlation")

    # Analyze the compression trend
    if results:
        compressions = [(r.k, r.compression) for r in results]
        if len(compressions) >= 5:
            last_5 = [c for _, c in compressions[-5:]]
            mean_c = sum(last_5) / 5
            print(f"║")
            print(f"║  Compression trend: → {mean_c:.4f} (last 5 k values)")
            print(f"║  Hardy-Ramanujan predicts: C/(2√2·log₂k) → 0")

    print("╚" + "═" * 68 + "╝")

    return {
        "n_standard": n_standard_proves,
        "n_esb": n_esb_proves,
        "n_extra": n_esb_extra,
        "n_total": len(results),
    }


if __name__ == '__main__':
    import sys
    k_max = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    result = scan_esb(k_max, max_prime=200)
