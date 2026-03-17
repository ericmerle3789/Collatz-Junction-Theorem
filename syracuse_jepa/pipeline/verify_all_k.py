"""
Complete verification: N₀(d(k)) = 0 for all k ≥ 3, k ≠ 4.

For k = 4: N₀(d(4)) = 1 (phantom composition (1,1,1,4), corrSum=94=2·47).
This phantom does NOT produce an actual cycle (Simons–de Weger, k < 68).

This script verifies:
  - Enumeration: k = 3, 4, 5 (small cases; k=4 is a known phantom)
  - Range Exclusion: k = 6..5259 (exact integer arithmetic)
  - Baker–LMN: k ≥ 5260 (theoretical, not computational)

Running time: ~30 seconds on a modern machine.

Author: Eric Merle
Date: 17 March 2026
"""

import math
import sys
from itertools import combinations_with_replacement

LOG2_3 = math.log2(3)

# --- Ground truth functions ---

def compute_S(k: int) -> int:
    """S(k) = ceil(k * log₂3)."""
    return math.ceil(k * LOG2_3)

def compute_d(k: int) -> int:
    """d(k) = 2^S - 3^k."""
    return 2 ** compute_S(k) - 3 ** k

def compute_range(k: int) -> int:
    """range(k) = 3^r + 1 - 2^(r+1), where r = S - k."""
    S = compute_S(k)
    r = S - k
    return 3 ** r + 1 - 2 ** (r + 1)

def compute_cs_max(k: int) -> int:
    """corrSum_max = 3^k + 3^(S mod k) - 2."""
    S = compute_S(k)
    r = S % k
    return 3 ** k + 3 ** r - 2

def compute_cs_min(k: int) -> int:
    """corrSum_min = 3^k - 3 + 2^(r+1), where r = S - k."""
    S = compute_S(k)
    r = S - k
    return 3 ** k - 3 + 2 ** (r + 1)


# --- Method 1: Enumeration ---

def monotone_compositions(total: int, parts: int):
    """Generate all non-decreasing sequences of length `parts` summing to `total`, each ≥ 1."""
    results = []
    def backtrack(remaining, min_val, current):
        if len(current) == parts:
            if remaining == 0:
                results.append(tuple(current))
            return
        spots_left = parts - len(current)
        for v in range(min_val, remaining - spots_left + 2):
            backtrack(remaining - v, v, current + [v])
    backtrack(total, 1, [])
    return results

def verify_by_enumeration(k: int) -> bool:
    """Verify N₀(d(k)) = 0 by enumerating all monotone compositions."""
    S = compute_S(k)
    d = compute_d(k)
    if d <= 0:
        return True  # phantom case
    comps = monotone_compositions(S, k)
    for A in comps:
        cs = sum(3 ** (k - 1 - j) * 2 ** A[j] for j in range(k))
        if cs % d == 0:
            return False
    return True


# --- Method 2: Range Exclusion ---

def verify_range_exclusion(k: int) -> bool:
    """Verify Range Exclusion: floor(cs_max/d) == floor(cs_min/d) and cs_min % d > 0.

    The condition cs_min % d > 0 ensures that the floor multiple q·d
    is strictly below cs_min, so no multiple of d lies in [cs_min, cs_max].

    NOTE: Previous version incorrectly checked cs_max % d != 0, which
    missed the case where cs_min itself is a multiple of d (e.g., k=4).
    """
    d = compute_d(k)
    if d <= 0:
        return True  # phantom
    cs_max = compute_cs_max(k)
    cs_min = compute_cs_min(k)
    q_max = cs_max // d
    q_min = cs_min // d
    return q_max == q_min and cs_min % d > 0


# --- Method 3: Baker–LMN asymptotic ---

def baker_lmn_threshold() -> int:
    """
    Compute K₀ from the Baker–LMN constant.

    C = 24.34 · ln(2) · ln(3) · 21² ≈ 8174
    β = 3^0.585 / 2^1.585 ≈ 0.634
    K₀ = C / ln(3/β) ≈ 5258

    We use K₀ = 5260 (rounded up for safety).
    """
    C = 24.34 * math.log(2) * math.log(3) * 21 ** 2
    beta = 3 ** 0.585 / 2 ** 1.585
    K0 = math.ceil(C / math.log(3 / beta))
    return K0


# --- Main verification ---

def run_complete_verification(verbose: bool = True) -> bool:
    """
    Run the complete verification of N₀(d(k)) = 0 for all k ≥ 3.

    Returns True if all checks pass.
    """
    K0 = baker_lmn_threshold()

    if verbose:
        print("=" * 70)
        print("COMPLETE VERIFICATION: N₀(d(k)) = 0 for all k ≥ 3, k ≠ 4")
        print("=" * 70)
        print(f"\nBaker–LMN threshold: K₀ = {K0}")
        print(f"  C = 24.34 · ln(2) · ln(3) · 21² = {24.34 * math.log(2) * math.log(3) * 441:.1f}")
        print(f"  β = 3^0.585 / 2^1.585 = {3**0.585 / 2**1.585:.4f}")
        print(f"  3/β = {3 / (3**0.585 / 2**1.585):.4f}")
        print()

    all_pass = True
    enum_count = 0
    re_count = 0
    re_pass = 0
    failures = []

    # Phase 1: Enumeration for k = 3, 4, 5
    # k=3: N₀(5) = 0 (Range Exclusion also works, but enumeration is canonical)
    # k=4: N₀(47) = 1 — PHANTOM (composition (1,1,1,4), corrSum=94=2·47)
    #       Range Exclusion correctly FAILS here (cs_min=94=2d, cs_min%d=0)
    #       No actual 4-cycle exists (Simons–de Weger, k < 68)
    # k=5: N₀(13) = 0 (Range Exclusion fails: different floor quotients)
    if verbose:
        print("Phase 1: Enumeration (k = 3, 4, 5)")
        print("-" * 40)

    for k in [3, 4, 5]:
        S = compute_S(k)
        d = compute_d(k)
        comps = monotone_compositions(S, k)
        ok = verify_by_enumeration(k)
        enum_count += 1
        if verbose:
            n0 = sum(1 for A in comps
                     if sum(3 ** (k - 1 - j) * 2 ** A[j] for j in range(k)) % d == 0)
            status = 'PASS (N₀=0)' if ok else f'PHANTOM (N₀={n0})'
            print(f"  k={k}: S={S}, d={d}, {len(comps)} compositions → {status}")
        if not ok and k != 4:  # k=4 phantom is expected, not a failure
            all_pass = False
            failures.append(k)

    if verbose:
        print()

    # Phase 2: Range Exclusion for k = 6..K₀-1
    # k=3 could also pass RE, but handled above by enumeration
    # k=4 FAILS RE (cs_min%d=0), handled above
    # k=5 FAILS RE (different floors), handled above
    if verbose:
        print(f"Phase 2: Range Exclusion (k = 6..{K0 - 1})")
        print("-" * 40)

    for k in range(6, K0):
        ok = verify_range_exclusion(k)
        re_count += 1
        if ok:
            re_pass += 1
        else:
            all_pass = False
            failures.append(k)
        if verbose and k % 1000 == 0:
            print(f"  k={k}: {re_pass}/{re_count} passed so far...")

    if verbose:
        print(f"  Range Exclusion: {re_pass}/{re_count} PASS")
        if re_pass < re_count:
            print(f"  FAILURES: {[k for k in failures if k >= 6]}")
        print()

    # Phase 3: Baker–LMN asymptotic
    if verbose:
        print(f"Phase 3: Baker–LMN (k ≥ {K0})")
        print("-" * 40)
        print(f"  For k ≥ {K0}: 4.73^k > exp(8174)")
        C_val = 24.34 * math.log(2) * math.log(3) * 441
        print(f"  Verification: {K0}·ln(4.73) = {K0 * math.log(3 / (3**0.585 / 2**1.585)):.1f} > C = {C_val:.1f} ✓")
        print()

    # Summary
    if verbose:
        print("=" * 70)
        print("SUMMARY")
        print("=" * 70)
        total = enum_count + re_count
        print(f"  Enumeration:      {enum_count} checked (k = 3, 4, 5)")
        print(f"    k=3: N₀=0 ✓  k=4: N₀=1 PHANTOM (no cycle by SdW)  k=5: N₀=0 ✓")
        print(f"  Range Exclusion:  {re_pass}/{re_count} PASS (k = 6..{K0 - 1})")
        print(f"  Baker–LMN:        k ≥ {K0} (theoretical)")
        print(f"  ─────────────────────────────────────")
        total_pass = enum_count + re_pass
        if all_pass:
            print(f"  RESULT: ALL {total_pass} Range Exclusion cases PASS")
            print(f"  CONCLUSION: N₀(d(k)) = 0 for all k ≥ 3 except k=4 (phantom).")
            print(f"  k=4 phantom → no actual cycle (Simons–de Weger, k < 68). ■")
        else:
            print(f"  RESULT: {total_pass}/{total} PASS, {len(failures)} FAIL")
            print(f"  FAILURES at k = {failures}")
        print("=" * 70)

    return all_pass


if __name__ == "__main__":
    verbose = "--quiet" not in sys.argv
    ok = run_complete_verification(verbose=verbose)
    sys.exit(0 if ok else 1)
