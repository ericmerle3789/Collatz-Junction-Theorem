#!/usr/bin/env python3
"""
R84 — CRT Final Computation for k=21
=====================================
d(21) = 5 × 43 × 3221 × 34511 = 23,899,385,165
S(21) = 35

Strategy:
- Compute N_0(7419865) where 7419865 = 5 × 43 × 34511
- If N_0(7419865) = 0 → N_0(d) = 0 PROVEN (k=21 blocked)
- If N_0(7419865) > 0 → need backtracking to check mod 3221

Also compute N_0(3221 × 5) = N_0(16105) and N_0(3221 × 43) = N_0(138503)
as cross-checks.
"""

import numpy as np
import time
import sys
from math import comb

def compute_N0(k, S, p, verbose=True):
    """Compute N_0(p) = #{compositions A of S into k parts ≥1 with corrSum(A) ≡ 0 mod p}"""
    if verbose:
        mem_mb = 2 * (S + 1) * p * 8 / 1e6
        print(f"  DP mod {p}: memory estimate = {mem_mb:.0f} MB")

    # Precompute coefficients
    coeff = [pow(3, k - 1 - i, p) for i in range(k)]
    pow2 = [pow(2, a, p) for a in range(S + 1)]

    # DP: dp[remaining][residue] = count
    dp_curr = np.zeros((S + 1, p), dtype=np.int64)
    dp_curr[S, 0] = 1  # Start: remaining=S, residue=0

    for i in range(k):
        dp_next = np.zeros((S + 1, p), dtype=np.int64)
        remaining_needed = k - 1 - i  # parts still needed after this one

        for rem in range(remaining_needed + 1, S + 1):
            max_a = rem - remaining_needed
            row = dp_curr[rem]
            if not np.any(row):
                continue
            for a in range(1, max_a + 1):
                contrib = (coeff[i] * pow2[a]) % p
                new_rem = rem - a
                # Roll the row by contrib positions (equivalent to adding contrib to residue)
                dp_next[new_rem] = dp_next[new_rem] + np.roll(row, contrib)

        dp_curr = dp_next
        if verbose:
            total_this_step = int(np.sum(dp_curr))
            print(f"  Step {i+1}/{k}: {total_this_step} compositions so far")

    N0 = int(dp_curr[0, 0])
    total = int(np.sum(dp_curr[0]))
    return N0, total

def main():
    k = 21
    S = 35
    C_total = comb(S - 1, k - 1)  # = C(34, 20)

    print(f"=" * 70)
    print(f"R84 — CRT Final Computation for k={k}")
    print(f"S = {S}, C({S-1},{k-1}) = {C_total:,}")
    print(f"d({k}) = 5 × 43 × 3221 × 34511 = 23,899,385,165")
    print(f"=" * 70)

    # Verify S: 2^35 - 3^21 = 34359738368 - 10460353203 = 23899385165
    d = 2**35 - 3**21
    assert d == 23899385165, f"d = {d}"
    assert d == 5 * 43 * 3221 * 34511, "Factorization mismatch"
    print(f"✓ d({k}) = {d:,} verified")
    print()

    # Phase 1: Compute N_0 for individual primes (quick verification)
    primes = [5, 43, 3221, 34511]

    print("Phase 1: Individual primes (verification)")
    print("-" * 50)
    for p in primes:
        t0 = time.time()
        N0, total = compute_N0(k, S, p, verbose=False)
        dt = time.time() - t0
        print(f"  N_0({p}) = {N0:,} / {total:,} (ratio {N0/total:.6f}, expected 1/{p}={1/p:.6f}) [{dt:.1f}s]")
        assert total == C_total, f"Total mismatch: {total} vs {C_total}"
    print()

    # Phase 2: Compute N_0(5 × 43) = N_0(215) as sanity check
    print("Phase 2: Two-prime composites")
    print("-" * 50)

    for (p1, p2) in [(5, 43), (5, 3221), (5, 34511), (43, 3221), (43, 34511)]:
        m = p1 * p2
        mem_mb = 2 * 36 * m * 8 / 1e6
        if mem_mb > 4000:
            print(f"  N_0({m}) = SKIP (memory {mem_mb:.0f} MB)")
            continue
        t0 = time.time()
        N0, total = compute_N0(k, S, m, verbose=False)
        dt = time.time() - t0
        ratio = N0 / total if total > 0 else 0
        print(f"  N_0({p1}×{p2} = {m}) = {N0:,} (ratio {ratio:.8f}, expected {1/m:.8f}) [{dt:.1f}s]")
    print()

    # Phase 3: THE CRITICAL COMPUTATION
    # N_0(5 × 43 × 34511) = N_0(7,419,865)
    print("=" * 70)
    print("Phase 3: CRITICAL — N_0(5 × 43 × 34511) = N_0(7,419,865)")
    print("=" * 70)
    m_critical = 5 * 43 * 34511
    assert m_critical == 7419865

    mem_mb = 2 * 36 * m_critical * 8 / 1e6
    print(f"Memory estimate: {mem_mb:.0f} MB")
    print(f"If N_0(7,419,865) = 0 → N_0(d) = 0 PROVEN")
    print()

    t0 = time.time()
    N0_critical, total = compute_N0(k, S, m_critical, verbose=True)
    dt = time.time() - t0

    print()
    print(f"★★★ N_0(7,419,865) = {N0_critical} ★★★")
    print(f"Total: {total:,}")
    print(f"Time: {dt:.1f}s")
    print()

    if N0_critical == 0:
        print("=" * 70)
        print("🏆 RESULT: N_0(d(21)) = 0 PROVEN")
        print("   (since N_0(5×43×34511) = 0, no composition can satisfy")
        print("    corrSum ≡ 0 mod 5, mod 43, AND mod 34511 simultaneously)")
        print("   → k=21 is BLOCKED: no non-trivial 21-cycle exists")
        print("=" * 70)
    else:
        print(f"N_0(7,419,865) = {N0_critical} > 0")
        print(f"Need to check these {N0_critical} compositions against mod 3221")
        print(f"Will need backtracking enumeration...")

    # Phase 4: Also compute N_0(5 × 43 × 3221) = N_0(692,515) as cross-check
    print()
    print("Phase 4: Cross-check N_0(692,515) = N_0(5×43×3221)")
    print("-" * 50)
    t0 = time.time()
    N0_692515, total = compute_N0(k, S, 692515, verbose=False)
    dt = time.time() - t0
    print(f"  N_0(692,515) = {N0_692515:,} [{dt:.1f}s]")
    print(f"  (Expected from previous session: 1,738)")

    print()
    print("Summary of all N_0 values:")
    print(f"  N_0(5) = computed above")
    print(f"  N_0(43) = computed above")
    print(f"  N_0(3221) = computed above")
    print(f"  N_0(34511) = computed above")
    print(f"  N_0(692515) = {N0_692515:,}")
    print(f"  N_0(7419865) = {N0_critical}")
    print(f"  Heuristic N_0(d) ≈ {C_total}/{d} ≈ {C_total/d:.4f}")

if __name__ == "__main__":
    main()
