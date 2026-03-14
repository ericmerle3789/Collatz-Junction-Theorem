#!/usr/bin/env python3
"""
R84-R88 — Systematic Gap Attack for k=21..41
=============================================
For each k, check S = S_min and S_min+1 (the two most constrained values).
S_min = ceil(k * log2(3)).

Strategy per (k,S):
1. Factor d(k,S) = 2^S - 3^k
2. If all prime factors < threshold → DP feasible
3. Hierarchical CRT: combine primes step by step
4. If intermediate N_0 is small → backtrack + cross-check
"""

import numpy as np
import time
import sys
from math import comb, ceil, log2, log
from sympy import factorint

def compute_N0(k, S, p, verbose=False):
    """Compute N_0(p) for compositions of S into k parts >= 1."""
    coeff = [pow(3, k - 1 - i, p) for i in range(k)]
    pow2 = [pow(2, a, p) for a in range(S + 1)]

    dp_curr = np.zeros((S + 1, p), dtype=np.int64)
    dp_curr[S, 0] = 1

    for i in range(k):
        dp_next = np.zeros((S + 1, p), dtype=np.int64)
        remaining_needed = k - 1 - i
        for rem in range(remaining_needed + 1, S + 1):
            max_a = rem - remaining_needed
            row = dp_curr[rem]
            if not np.any(row):
                continue
            for a in range(1, max_a + 1):
                contrib = (coeff[i] * pow2[a]) % p
                new_rem = rem - a
                dp_next[new_rem] = dp_next[new_rem] + np.roll(row, contrib)
        dp_curr = dp_next

    N0 = int(dp_curr[0, 0])
    total = int(np.sum(dp_curr[0]))
    return N0, total

def compute_N0_with_tables(k, S, m):
    """Forward DP mod m, returning all tables for backtracking."""
    coeff = [pow(3, k - 1 - i, m) for i in range(k)]
    pow2 = [pow(2, a, m) for a in range(S + 1)]

    tables = []
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
                contrib = (coeff[i] * pow2[a]) % m
                new_rem = rem - a
                dp_next[new_rem] = dp_next[new_rem] + np.roll(row, contrib)
        tables.append(dp_next)
        dp_curr = dp_next

    return tables

def backtrack_enumerate(tables, k, S, m):
    """Enumerate all compositions with corrSum ≡ 0 mod m by backtracking."""
    coeff = [pow(3, k - 1 - i, m) for i in range(k)]
    pow2 = [pow(2, a, m) for a in range(S + 1)]

    compositions = []

    def recurse(step, remaining, residue, partial):
        if step == 0:
            compositions.append(tuple(partial))
            return
        i = step - 1
        for a in range(1, S - remaining + 1):
            prev_rem = remaining + a
            if prev_rem > S or prev_rem < (k - i):
                continue
            prev_res = (residue - coeff[i] * pow2[a]) % m
            if tables[i][prev_rem, prev_res] > 0:
                partial.append(a)
                recurse(step - 1, prev_rem, prev_res, partial)
                partial.pop()

    sys.setrecursionlimit(50000)
    recurse(k, 0, 0, [])
    return compositions

def check_compositions_mod_p(compositions, k, S, m_orig, p_check):
    """Check enumerated compositions against additional prime."""
    coeff_p = [pow(3, k - 1 - i, p_check) for i in range(k)]
    pow2_p = [pow(2, a, p_check) for a in range(S + 1)]

    hits = 0
    for comp in compositions:
        comp_fwd = comp[::-1]
        cs = 0
        for i in range(k):
            cs = (cs + coeff_p[i] * pow2_p[comp_fwd[i]]) % p_check
        if cs == 0:
            hits += 1
    return hits

def attack_single(k, S, max_prime=2_000_000, max_composite_dp=10_000_000, max_backtrack_count=50000):
    """
    Try to prove N_0(d(k,S)) = 0.
    Returns: (status, N0_or_bound, details)
    status: "BLOCKED", "OPEN", "INFEASIBLE"
    """
    d = 2**S - 3**k
    if d <= 0:
        return ("INVALID", 0, f"d = {d} <= 0")

    C_total = comb(S - 1, k - 1)
    heuristic = C_total / d

    print(f"\n  Attack k={k}, S={S}: d = {d:,}")
    print(f"    C({S-1},{k-1}) = {C_total:,}, heuristic N_0/C = {heuristic:.6f}")

    # Factor d
    t0 = time.time()
    factors = factorint(d)
    dt = time.time() - t0
    primes = sorted(factors.keys())
    factor_str = " × ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(factors.items()))
    print(f"    d = {factor_str} [factored in {dt:.1f}s]")

    # Check feasibility: all prime factors (with multiplicity) must be manageable
    # For DP, we need array of size p per remaining value
    max_p = max(primes)
    if max_p > max_prime:
        print(f"    INFEASIBLE: largest prime {max_p:,} > {max_prime:,}")
        return ("INFEASIBLE", -1, f"largest prime {max_p:,}")

    # Compute N_0 for each prime individually
    print(f"    Individual primes:")
    prime_N0 = {}
    for p in primes:
        e = factors[p]
        if e > 1:
            # Need to handle prime powers
            pp = p ** e
        else:
            pp = p
        t0 = time.time()
        N0, total = compute_N0(k, S, pp)
        dt = time.time() - t0
        prime_N0[pp] = N0
        print(f"      N_0({pp}) = {N0:,} / {total:,} [{dt:.1f}s]")
        if N0 == 0:
            print(f"    ★ BLOCKED at prime power {pp}!")
            return ("BLOCKED", 0, f"N_0({pp}) = 0")

    # Hierarchical CRT: combine primes greedily (smallest first)
    prime_powers = sorted(prime_N0.keys())
    current_m = 1
    current_N0 = C_total

    for pp in prime_powers:
        new_m = current_m * pp
        mem_mb = 2 * (S + 1) * new_m * 8 / 1e6
        print(f"    Trying composite m = {new_m:,} (memory ~{mem_mb:.0f} MB)...")

        if new_m > max_composite_dp:
            # Too large for direct DP — try backtracking from current_m
            if current_N0 <= max_backtrack_count and current_N0 > 0:
                print(f"    Backtracking: enumerate {current_N0} compositions mod {current_m}, check mod {pp}")
                t0 = time.time()
                tables = compute_N0_with_tables(k, S, current_m)
                comps = backtrack_enumerate(tables, k, S, current_m)
                del tables  # free memory
                hits = check_compositions_mod_p(comps, k, S, current_m, pp)
                dt = time.time() - t0
                print(f"    Result: {hits} / {len(comps)} survive mod {pp} [{dt:.1f}s]")

                if hits == 0:
                    print(f"    ★ BLOCKED by CRT!")
                    return ("BLOCKED", 0, f"CRT: 0/{len(comps)} survive mod {pp}")
                else:
                    current_N0 = hits
                    # Can't easily continue CRT from here without the full composite DP
                    # But if hits is small, we could enumerate again...
                    # For now, mark as needing further work
                    remaining_primes = [q for q in prime_powers if q != pp and q * current_m > max_composite_dp]
                    if remaining_primes:
                        print(f"    {hits} compositions survive, need to check mod {remaining_primes}")
                        # Try to backtrack from new composite
                        # Actually we need a different approach here
                        # Let's try direct DP with the next two primes combined
                        pass
                    current_m = new_m  # conceptual update
            else:
                print(f"    INFEASIBLE: m={new_m:,} too large and N_0({current_m})={current_N0} too many for backtracking")
                return ("INFEASIBLE", current_N0, f"N_0({current_m}) = {current_N0}")
        else:
            # Direct DP feasible
            t0 = time.time()
            N0, total = compute_N0(k, S, new_m)
            dt = time.time() - t0
            current_m = new_m
            current_N0 = N0
            print(f"    N_0({new_m:,}) = {N0:,} [{dt:.1f}s]")

            if N0 == 0:
                print(f"    ★ BLOCKED at composite {new_m}!")
                return ("BLOCKED", 0, f"N_0({new_m}) = 0")

    # If we get here, we've combined all primes
    if current_m == d and current_N0 == 0:
        return ("BLOCKED", 0, "Full CRT")
    elif current_N0 > 0:
        return ("OPEN", current_N0, f"N_0({current_m}) = {current_N0}")
    else:
        return ("BLOCKED", 0, f"CRT composite")

def main():
    print("=" * 70)
    print("R84-R88 — SYSTEMATIC GAP ATTACK k=21..41")
    print("=" * 70)

    results = {}

    for k in range(21, 42):
        S_min = ceil(k * log2(3))
        # Verify: 2^S_min > 3^k
        assert 2**S_min > 3**k, f"S_min wrong for k={k}"
        assert 2**(S_min - 1) <= 3**k, f"S_min not minimal for k={k}"

        print(f"\n{'='*70}")
        print(f"k = {k}, S_min = {S_min}")
        print(f"{'='*70}")

        for S in [S_min, S_min + 1]:
            status, N0, detail = attack_single(k, S)
            results[(k, S)] = (status, N0, detail)

            if status == "BLOCKED":
                print(f"  → k={k}, S={S}: ✅ BLOCKED ({detail})")
            elif status == "OPEN":
                print(f"  → k={k}, S={S}: ❌ OPEN (N_0 ≥ {N0})")
            else:
                print(f"  → k={k}, S={S}: ⚠️ {status} ({detail})")

    # Summary
    print(f"\n{'='*70}")
    print("SUMMARY")
    print(f"{'='*70}")

    for k in range(21, 42):
        S_min = ceil(k * log2(3))
        s1 = results.get((k, S_min), ("?", -1, ""))
        s2 = results.get((k, S_min + 1), ("?", -1, ""))

        status1 = "✅" if s1[0] == "BLOCKED" else ("❌" if s1[0] == "OPEN" else "⚠️")
        status2 = "✅" if s2[0] == "BLOCKED" else ("❌" if s2[0] == "OPEN" else "⚠️")
        both = "✅ FULLY BLOCKED" if s1[0] == "BLOCKED" and s2[0] == "BLOCKED" else ""

        print(f"  k={k:2d}: S={S_min} {status1} {s1[0]:12s} | S={S_min+1} {status2} {s2[0]:12s} {both}")

if __name__ == "__main__":
    main()
