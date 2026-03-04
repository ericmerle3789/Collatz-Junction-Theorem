#!/usr/bin/env python3
"""
Phase F Extension: N₀(d) for k=19..21
======================================

Extends the Phase F computation to larger k.
Uses direct enumeration with Horner mod d.

k=19: C = 86,493,225 (~5.4 min at 265K/s)
k=20: C = 141,120,525 (~8.9 min)
k=21: C = 573,166,440 (~36 min)

Author: Eric Merle (assisted by Claude)
Date:   3 mars 2026
"""

import math
import time
import itertools
import sys

def ceil_log2_3_exact(k):
    three_k = 3 ** k
    S = k
    while (1 << S) < three_k:
        S += 1
    return S

def crystal_module(k):
    S = ceil_log2_3_exact(k)
    return (1 << S) - 3**k, S

def prime_factorization(n):
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            exp = 0
            while n % d == 0:
                n //= d
                exp += 1
            factors.append((d, exp))
        d += (1 if d == 2 else 2)
    if n > 1:
        factors.append((n, 1))
    return factors


def compute_N0_d(k):
    """Compute N₀(d) by enumerating all C compositions."""
    d, S = crystal_module(k)
    C = math.comb(S - 1, k - 1)
    factors = prime_factorization(d)
    primes = [p for p, _ in factors]

    print(f"  k={k}: S={S}, C={C:,}, d={d:,}, C/d={C/d:.6f}")
    print(f"    d = {' × '.join(str(p) for p, _ in factors)}")
    sys.stdout.flush()

    # Precompute 2^s mod d
    pow2_d = [pow(2, s, d) for s in range(S)]

    N0_d = 0
    total = 0
    t0 = time.time()
    batch = 2_000_000

    for combo in itertools.combinations(range(1, S), k - 1):
        # Horner: c_0 = 1 (for A[0]=0, 2^0=1), then c_j = 3*c_{j-1} + 2^{A_j}
        c = 1
        for j in range(k - 1):
            c = (3 * c + pow2_d[combo[j]]) % d
        if c == 0:
            N0_d += 1

        total += 1
        if total % batch == 0:
            elapsed = time.time() - t0
            rate = total / elapsed
            eta = (C - total) / rate
            print(f"    [{total:>12,}/{C:,}] N₀(d)={N0_d}, "
                  f"rate={rate:,.0f}/s, ETA={eta:.0f}s")
            sys.stdout.flush()

    elapsed = time.time() - t0
    print(f"    DONE: N₀(d={d:,}) = {N0_d} / {total:,}  ({elapsed:.1f}s)")
    print(f"    ★ {'H('+str(k)+') PROVED' if N0_d == 0 else 'H('+str(k)+') NOT PROVED'}")
    print()
    sys.stdout.flush()

    return {'k': k, 'S': S, 'd': d, 'C': C, 'N0_d': N0_d, 'time': elapsed}


def main():
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║   PHASE F EXTENSION: N₀(d) FOR k=19..21                  ║")
    print("╚══════════════════════════════════════════════════════════════╝")
    print()

    results = []
    t_global = time.time()

    for k in [19, 20, 21]:
        r = compute_N0_d(k)
        results.append(r)

    print("=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print()
    print(f"  {'k':>3} {'C':>15} {'d':>18} {'C/d':>10} {'N₀(d)':>8} {'Time':>8} {'Status':>12}")
    print("  " + "-" * 80)

    # Include prior results for context
    prior = [
        (3, 6, 5, 0), (4, 20, 47, 0), (5, 35, 13, 0),
        (6, 126, 295, 0), (7, 462, 1909, 0), (8, 792, 1631, 0),
        (9, 3003, 13085, 0), (10, 5005, 6487, 0),
        (11, 19448, 84997, 0), (12, 75582, 517135, 0),
        (13, 125970, 502829, 0), (14, 497420, 3605639, 0),
        (15, 817190, 2428309, 0), (16, 3268760, 24062143, 0),
        (17, 5311735, 5077565, 0), (18, 21474180, 149450423, 0),
    ]

    for k, C, d, N0 in prior:
        print(f"  {k:>3} {C:>15,} {d:>18,} {C/d:>10.6f} {N0:>8} {'prior':>8} "
              f"{'✓ PROVED':>12}")

    for r in results:
        status = '✓ PROVED' if r['N0_d'] == 0 else '✗ FAIL'
        print(f"  {r['k']:>3} {r['C']:>15,} {r['d']:>18,} {r['C']/r['d']:>10.6f} "
              f"{r['N0_d']:>8} {r['time']:>7.1f}s {status:>12}")

    print()
    total_time = time.time() - t_global
    print(f"  Total computation time: {total_time:.1f}s ({total_time/60:.1f}min)")
    print()

    all_proved = all(r['N0_d'] == 0 for r in results)
    if all_proved:
        print("  ╔══════════════════════════════════════════════════════════╗")
        print("  ║  N₀(d) = 0 VERIFIED FOR ALL k = 3..21                 ║")
        print("  ║  19 consecutive values: H(k) proved exhaustively       ║")
        print("  ╚══════════════════════════════════════════════════════════╝")
    else:
        failed = [r['k'] for r in results if r['N0_d'] > 0]
        print(f"  ⚠ N₀(d) > 0 for k = {failed}")

    print()


if __name__ == '__main__':
    main()
