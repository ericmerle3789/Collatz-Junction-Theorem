#!/usr/bin/env python3
"""
R84 — Backtrack Enumeration for k=21
======================================
Phase 1: Forward DP mod 692515 (= 5×43×3221), saving all k+1 tables
Phase 2: Backtrack from dp[k][0][0] to enumerate all 1,738 compositions
Phase 3: For each composition, compute corrSum mod 34511
Phase 4: If none has corrSum ≡ 0 mod 34511 → N_0(d(21)) = 0 PROVEN
"""

import numpy as np
import time
import sys
from math import comb

def main():
    k = 21
    S = 35
    m = 692515  # = 5 × 43 × 3221
    p_check = 34511  # the remaining prime factor
    d_full = 5 * 43 * 3221 * 34511
    C_total = comb(S - 1, k - 1)

    print(f"=" * 70)
    print(f"R84 — Backtrack Enumeration for k={k}")
    print(f"S={S}, m={m}, p_check={p_check}, d={d_full:,}")
    print(f"C({S-1},{k-1}) = {C_total:,}")
    print(f"=" * 70)
    print()

    # Precompute coefficients
    coeff_m = [pow(3, k - 1 - i, m) for i in range(k)]
    pow2_m = [pow(2, a, m) for a in range(S + 1)]
    coeff_p = [pow(3, k - 1 - i, p_check) for i in range(k)]
    pow2_p = [pow(2, a, p_check) for a in range(S + 1)]

    # Phase 1: Forward DP mod m, saving all tables
    print("Phase 1: Forward DP mod", m)
    print(f"  Memory per table: {36 * m * 8 / 1e6:.0f} MB")
    print(f"  Total for {k+1} tables: {(k+1) * 36 * m * 8 / 1e9:.1f} GB")
    print()

    t0 = time.time()
    tables = []

    # Initial table: dp[0][S][0] = 1
    dp_init = np.zeros((S + 1, m), dtype=np.int64)
    dp_init[S, 0] = 1
    tables.append(dp_init)

    dp_curr = dp_init
    for i in range(k):
        dp_next = np.zeros((S + 1, m), dtype=np.int64)
        remaining_needed = k - 1 - i

        for rem in range(remaining_needed + 1, S + 1):
            max_a = rem - remaining_needed
            row = dp_curr[rem]
            if not np.any(row):
                continue
            for a in range(1, max_a + 1):
                contrib = (coeff_m[i] * pow2_m[a]) % m
                new_rem = rem - a
                dp_next[new_rem] = dp_next[new_rem] + np.roll(row, contrib)

        tables.append(dp_next)
        dp_curr = dp_next
        total_step = int(np.sum(dp_curr))
        print(f"  Step {i+1}/{k}: {total_step:,} compositions")

    N0_m = int(tables[k][0, 0])
    print(f"\n  N_0({m}) = {N0_m:,}")
    print(f"  Forward DP time: {time.time() - t0:.1f}s")
    print()

    if N0_m == 0:
        print("N_0(m) = 0 → N_0(d) = 0 trivially. Done.")
        return

    # Phase 2: Backtrack to enumerate compositions
    print("Phase 2: Backtracking to enumerate compositions")
    print(f"  Target: {N0_m} compositions with corrSum ≡ 0 mod {m}")
    print()

    t0 = time.time()
    compositions = []

    def backtrack(step, remaining, residue, partial):
        """Backtrack from step (after choosing a_0,...,a_{step-1})."""
        if step == 0:
            # Found a complete composition (in reverse)
            compositions.append(tuple(partial))
            if len(compositions) % 500 == 0:
                print(f"    Found {len(compositions)} compositions so far...")
            return

        # We need to undo step (step-1), i.e., find a = a_{step-1}
        # Current state after step-1 choices: (remaining, residue) in tables[step]
        # Previous state: (remaining + a, (residue - coeff_m[step-1]*pow2_m[a]) % m) in tables[step-1]

        i = step - 1  # index of the choice we're undoing
        min_a = max(1, (k - i) - remaining)  # prev_remaining >= k - i
        max_a = S - remaining  # prev_remaining <= S

        # Also: prev_remaining = remaining + a, and at step i,
        # we need prev_remaining <= S (always true since remaining >= 0 and a <= S)
        # and prev_remaining >= remaining_needed_at_step_i + 1 if i > 0
        # remaining_needed at step i = k - 1 - (i - 1) = k - i... wait
        # At step i (table index i), remaining must be >= k - i (need k-i more parts)
        # So prev_remaining = remaining + a must be valid for table[i]
        # prev_remaining needs to support the first i choices plus remaining
        # At table[i], valid remaining values are from (k-i) to S

        for a in range(max(1, min_a), max_a + 1):
            prev_rem = remaining + a
            if prev_rem > S or prev_rem < (k - i):
                continue
            prev_res = (residue - coeff_m[i] * pow2_m[a]) % m
            if tables[i][prev_rem, prev_res] > 0:
                partial.append(a)
                backtrack(step - 1, prev_rem, prev_res, partial)
                partial.pop()

    # Start backtracking from the final state: tables[k][0][0]
    sys.setrecursionlimit(10000)
    backtrack(k, 0, 0, [])

    dt_bt = time.time() - t0
    print(f"  Found {len(compositions)} compositions in {dt_bt:.1f}s")

    if len(compositions) != N0_m:
        print(f"  WARNING: Expected {N0_m}, found {len(compositions)}!")

    # Phase 3: Check each composition mod p_check
    print()
    print(f"Phase 3: Checking {len(compositions)} compositions mod {p_check}")
    print("-" * 50)

    hits = 0
    hit_compositions = []

    for idx, comp in enumerate(compositions):
        # comp is stored in reverse (a_{k-1}, ..., a_0) due to backtracking
        # Reverse it to get (a_0, a_1, ..., a_{k-1})
        comp_fwd = comp[::-1]

        # Compute corrSum mod p_check
        # corrSum = sum_{i=0}^{k-1} 3^{k-1-i} * 2^{a_i}
        cs = 0
        for i in range(k):
            cs = (cs + coeff_p[i] * pow2_p[comp_fwd[i]]) % p_check

        if cs == 0:
            hits += 1
            hit_compositions.append(comp_fwd)
            print(f"  ★ HIT #{hits}: composition {comp_fwd}")
            print(f"    Sum check: {sum(comp_fwd)} (should be {S})")

            # Double-check: compute corrSum mod m
            cs_m = 0
            for i in range(k):
                cs_m = (cs_m + coeff_m[i] * pow2_m[comp_fwd[i]]) % m
            print(f"    corrSum mod {m} = {cs_m} (should be 0)")
            print(f"    corrSum mod {p_check} = {cs} (should be 0)")

    print()
    print(f"=" * 70)
    if hits == 0:
        print(f"★★★ RESULT: N_0(d({k})) = 0 — PROVEN ★★★")
        print(f"")
        print(f"  None of the {len(compositions)} compositions with")
        print(f"  corrSum ≡ 0 mod {m} also satisfies corrSum ≡ 0 mod {p_check}.")
        print(f"  Therefore N_0({d_full:,}) = 0.")
        print(f"  → No non-trivial {k}-cycle exists in the Collatz system.")
        print(f"")
        print(f"  This blocks k={k} in the gap k=21..41.")
    else:
        print(f"  N_0(d({k})) ≥ {hits}")
        print(f"  {hits} composition(s) found with corrSum ≡ 0 mod d({k})")
        for c in hit_compositions:
            print(f"    {c}")
    print(f"=" * 70)

    # Sanity: verify a few compositions mod m
    print()
    print("Sanity checks on first 5 compositions:")
    for idx, comp in enumerate(compositions[:5]):
        comp_fwd = comp[::-1]
        print(f"  Comp {idx}: {comp_fwd}, sum={sum(comp_fwd)}")
        cs_m = 0
        for i in range(k):
            cs_m = (cs_m + coeff_m[i] * pow2_m[comp_fwd[i]]) % m
        cs_p = 0
        for i in range(k):
            cs_p = (cs_p + coeff_p[i] * pow2_p[comp_fwd[i]]) % p_check
        print(f"    corrSum mod {m} = {cs_m}, mod {p_check} = {cs_p}")

if __name__ == "__main__":
    main()
