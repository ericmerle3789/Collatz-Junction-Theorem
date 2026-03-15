#!/usr/bin/env python3
"""
R159 — EXTENSION DP : Prouver 13 valeurs de k (gap 20 → 7)
============================================================

Agent 4 de R159 a identifié 13 valeurs k ∈ {22..41} faisables sur M1 Pro 16GB.
Ce script exécute les preuves DP pour chacune.

STRATÉGIE :
  Pour chaque k, d(k) = 2^S - 3^k a une factorisation connue.
  Il suffit de trouver UN facteur premier p tel que N₀(p) = 0.
  On attaque le plus petit facteur premier d'abord.

TIER 1 (6 valeurs, plus faciles que k=21) :
  k=25, 34, 24, 30, 23, 26

TIER 1b (7 valeurs, mém < 4 GB) :
  k=37, 40, 29, 36, 38, 22, 27

TIER 3 (7 valeurs, INFAISABLE 16GB) :
  k=28, 31, 32, 33, 35, 39, 41 — NON TENTÉ

Author: Claude Opus 4.6 (R159 pour Eric Merle — Collatz Junction Theorem)
Date:   2026-03-15
"""

import sys
import time
import json
from math import comb, gcd, log2, ceil
from collections import OrderedDict

# ============================================================================
# MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """Minimal S such that 2^S > 3^k."""
    S = ceil(k * log2(3))
    while (1 << S) <= 3**k:
        S += 1
    while S > 0 and (1 << (S - 1)) > 3**k:
        S -= 1
    return S

def compute_d(k):
    return (1 << compute_S(k)) - 3**k

def compute_C(k):
    S = compute_S(k)
    return comb(S - 1, k - 1)

def modinv(a, m):
    if m == 1:
        return 0
    old_r, r = a % m, m
    old_s, s = 1, 0
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
    return old_s % m if old_r == 1 else None

def compute_g(k, mod):
    """g = 2 * 3^{-1} mod p (Steiner coefficient)."""
    inv3 = modinv(3, mod)
    return (2 * inv3) % mod if inv3 is not None else None

def is_prime(n):
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    d_val = n - 1
    r = 0
    while d_val % 2 == 0:
        d_val //= 2
        r += 1
    for a in witnesses:
        if a >= n:
            continue
        x = pow(a, d_val, n)
        if x == 1 or x == n - 1:
            continue
        found = False
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                found = True
                break
        if not found:
            return False
    return True

def factorize(n, limit=10**8):
    """Trial division up to limit, then Miller-Rabin for remainder."""
    if n <= 1:
        return []
    factors = []
    for p in [2, 3]:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e > 0:
            factors.append((p, e))
    p = 5
    step = 2
    while p * p <= n and p <= limit:
        e = 0
        while n % p == 0:
            n //= p
            e += 1
        if e > 0:
            factors.append((p, e))
        p += step
        step = 6 - step
    if n > 1:
        if is_prime(n):
            factors.append((n, 1))
        else:
            # n is composite but we can't factor it with trial division
            factors.append((n, 1))  # Mark as single factor
    return factors

# ============================================================================
# DENSE 2D DP (from R29-C, adapted)
# ============================================================================

def dp_N0_dense(k, p, max_time=120.0, progress=True):
    """
    Dense flat-array DP for computing N₀(p).

    State: dp[r * stride + b_last] = count of B-vectors
           with corrSum ≡ r mod p and last coordinate = b_last.

    CRITICAL: B_{k-1} = S-k is FIXED (Steiner constraint).

    Memory: p * (max_B+1) * 8 bytes.

    Returns (N0, C_total, time_s, steps_completed).
    """
    t0 = time.time()
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    if g is None:
        return None, None, 0, 0

    g_powers = [pow(g, j, p) for j in range(k)]

    # Precompute coeff_j * 2^b mod p for each (j, b)
    coeff_table = []
    for j in range(k):
        row = [0] * (max_B + 1)
        for b in range(max_B + 1):
            row[b] = (g_powers[j] * pow(2, b, p)) % p
        coeff_table.append(row)

    stride = max_B + 1

    # Memory estimate
    mem_bytes = p * stride * 8
    mem_mb = mem_bytes / (1024**2)
    if progress:
        print(f"    Mémoire DP: {mem_mb:.1f} MB ({p:,} × {stride})")

    if mem_mb > 4500:  # Safety limit: 4.5 GB
        print(f"    [SKIP] Mémoire {mem_mb:.0f} MB dépasse 4.5 GB")
        return None, None, 0, 0

    # Initialize: j=0, B_0 ∈ {0, ..., max_B}
    dp = [0] * (p * stride)
    for b in range(max_B + 1):
        r = coeff_table[0][b]
        dp[r * stride + b] += 1

    steps_done = 1

    # Transitions: j=1..k-1
    for j in range(1, k):
        if time.time() - t0 > max_time:
            print(f"    [TIMEOUT] étape {j}/{k-1} après {time.time()-t0:.1f}s")
            return None, None, time.time() - t0, steps_done

        coeff_row = coeff_table[j]
        dp_next = [0] * (p * stride)

        if j == k - 1:
            # B_{k-1} = max_B FIXÉ (Steiner)
            b_new = max_B
            delta_r = coeff_row[b_new]
            for r in range(p):
                base = r * stride
                for bp in range(b_new + 1):
                    cnt = dp[base + bp]
                    if cnt == 0:
                        continue
                    r_new = r + delta_r
                    if r_new >= p:
                        r_new -= p
                    dp_next[r_new * stride + b_new] += cnt
        else:
            for r in range(p):
                base = r * stride
                for bp in range(max_B + 1):
                    cnt = dp[base + bp]
                    if cnt == 0:
                        continue
                    for bn in range(bp, max_B + 1):
                        r_new = r + coeff_row[bn]
                        if r_new >= p:
                            r_new -= p
                        dp_next[r_new * stride + bn] += cnt

        dp = dp_next
        steps_done = j + 1

        if progress:
            active = sum(1 for x in dp if x > 0)
            t_step = time.time() - t0
            print(f"    Étape {j}/{k-1}: active={active:,}, temps={t_step:.2f}s")

    # Count N₀ and C
    N0 = 0
    C_total = 0
    for b in range(stride):
        N0 += dp[b]  # r=0 row
    for idx in range(len(dp)):
        C_total += dp[idx]

    return N0, C_total, time.time() - t0, steps_done


# ============================================================================
# SPARSE DP (for very large p, slower but lower memory)
# ============================================================================

def dp_N0_sparse(k, p, max_time=120.0, progress=True):
    """Sparse dict DP for large p where dense array would exceed memory."""
    t0 = time.time()
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    if g is None:
        return None, None, 0, 0

    g_powers = [pow(g, j, p) for j in range(k)]
    two_powers = [pow(2, b, p) for b in range(max_B + 1)]
    stride = max_B + 1

    dp = {}
    for b in range(max_B + 1):
        r = (g_powers[0] * two_powers[b]) % p
        key = r * stride + b
        dp[key] = dp.get(key, 0) + 1

    for j in range(1, k):
        if time.time() - t0 > max_time:
            return None, None, time.time() - t0, j
        coeff = g_powers[j]
        dp_next = {}
        for key, cnt in dp.items():
            r = key // stride
            b_prev = key % stride
            if j == k - 1:
                b_new = max_B
                if b_new >= b_prev:
                    r_new = (r + coeff * two_powers[b_new]) % p
                    new_key = r_new * stride + b_new
                    dp_next[new_key] = dp_next.get(new_key, 0) + cnt
            else:
                for b_new in range(b_prev, max_B + 1):
                    r_new = (r + coeff * two_powers[b_new]) % p
                    new_key = r_new * stride + b_new
                    dp_next[new_key] = dp_next.get(new_key, 0) + cnt
        dp = dp_next

        if progress:
            print(f"    Étape {j}/{k-1}: states={len(dp):,}, temps={time.time()-t0:.2f}s")

    N0 = sum(cnt for key, cnt in dp.items() if key // stride == 0)
    C_total = sum(dp.values())
    return N0, C_total, time.time() - t0, k


# ============================================================================
# TARGET k VALUES AND FACTORIZATIONS
# ============================================================================

def get_attack_plan():
    """
    Returns the 13 feasible k values with their factorizations and attack primes.
    Ordered by difficulty (easiest first).
    """
    targets = OrderedDict()

    # Tier 1: Trivialement faisable (plus petit premier < 600K)
    tier1_ks = [25, 34, 24, 30, 23, 26]

    # Tier 1b: Faisable avec ressources modestes (plus grand premier < 600M)
    tier1b_ks = [37, 40, 29, 36, 38, 22, 27]

    all_ks = tier1_ks + tier1b_ks

    for k in all_ks:
        d = compute_d(k)
        S = compute_S(k)
        C = compute_C(k)
        factors = factorize(d)

        # Find smallest prime factor
        primes = []
        for p, e in factors:
            if is_prime(p):
                primes.append(p)
        primes.sort()

        tier = "1" if k in tier1_ks else "1b"

        # Estimate memory for smallest prime
        max_B = S - k
        if primes:
            smallest_p = primes[0]
            mem_mb = smallest_p * (max_B + 1) * 8 / (1024**2)
        else:
            smallest_p = None
            mem_mb = float('inf')

        targets[k] = {
            'd': d,
            'S': S,
            'C': C,
            'factors': factors,
            'primes': primes,
            'tier': tier,
            'attack_prime': smallest_p,
            'mem_mb': mem_mb,
        }

    return targets


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    print("=" * 90)
    print("R159 — EXTENSION DP : PREUVE DE 13 VALEURS DE k")
    print("=" * 90)
    print(f"Objectif : réduire le gap de 20 valeurs (k=22..41) à 7")
    print(f"Machine : M1 Pro 16GB, limite mémoire 4.5 GB")
    print()

    targets = get_attack_plan()

    # Display attack plan
    print("PLAN D'ATTAQUE :")
    print(f"{'k':>4} {'Tier':>5} {'d(k)':>16} {'Plus petit p':>14} {'Mém (MB)':>10} {'max_B':>6}")
    print("-" * 70)
    for k, info in targets.items():
        print(f"{k:>4} {info['tier']:>5} {info['d']:>16,} {info['attack_prime']:>14,} "
              f"{info['mem_mb']:>10.1f} {info['S']-k:>6}")
    print()

    # Execute proofs
    results = {}
    proved = []
    failed = []

    t_global = time.time()

    for k, info in targets.items():
        print(f"\n{'='*70}")
        print(f"ATTAQUE k={k} (Tier {info['tier']})")
        print(f"{'='*70}")
        print(f"  d({k}) = {info['d']:,}")
        print(f"  S = {info['S']}, max_B = {info['S']-k}")
        print(f"  C({k}) = {info['C']:,}")
        print(f"  Facteurs : {info['factors']}")

        k_proved = False
        blocking_prime = None

        for p in info['primes']:
            if k_proved:
                break

            max_B = info['S'] - k
            mem_mb = p * (max_B + 1) * 8 / (1024**2)

            print(f"\n  → Attaque p = {p:,} (mém: {mem_mb:.1f} MB)")

            # Choose algorithm
            if mem_mb > 4500:
                print(f"    [SKIP] Mémoire {mem_mb:.0f} MB > 4500 MB")
                continue

            if mem_mb < 2000:
                # Dense DP
                N0, C_total, t_s, steps = dp_N0_dense(k, p, max_time=300.0)
            else:
                # For larger primes, try dense but with longer timeout
                N0, C_total, t_s, steps = dp_N0_dense(k, p, max_time=600.0)

            if N0 is None:
                print(f"    [TIMEOUT/ERROR] après {t_s:.1f}s ({steps} étapes)")
                continue

            ratio = N0 / C_total if C_total > 0 else float('nan')
            expected = C_total / p if p > 0 else float('nan')

            print(f"    N₀({p:,}) = {N0:,}")
            print(f"    C_total = {C_total:,}")
            print(f"    Ratio N₀/C = {ratio:.6f}")
            print(f"    Attendu (uniforme) = {expected:.1f}")
            print(f"    Temps = {t_s:.3f}s")

            if N0 == 0:
                print(f"    ╔══════════════════════════════════════════╗")
                print(f"    ║  ✓ N₀({p:,}) = 0 → k={k} PROUVÉ !       ║")
                print(f"    ╚══════════════════════════════════════════╝")
                k_proved = True
                blocking_prime = p
            else:
                print(f"    ✗ N₀ > 0, p={p:,} n'est PAS bloquant")

        results[k] = {
            'proved': k_proved,
            'blocking_prime': blocking_prime,
            'time_s': time.time() - t_global,
        }

        if k_proved:
            proved.append(k)
        else:
            failed.append(k)

    # ============================================================================
    # SUMMARY
    # ============================================================================

    total_time = time.time() - t_global

    print("\n" + "=" * 90)
    print("RÉSUMÉ FINAL — R159 EXTENSION DP")
    print("=" * 90)

    print(f"\nProuvés ({len(proved)}/13) : {sorted(proved)}")
    print(f"Échoués ({len(failed)}/13) : {sorted(failed)}")
    print(f"Temps total : {total_time:.1f}s")

    if proved:
        print(f"\n✅ Nouvelles valeurs de k prouvées impossible comme longueur de cycle :")
        for k in sorted(proved):
            info = targets[k]
            bp = results[k]['blocking_prime']
            print(f"   k={k} : N₀({bp:,}) = 0, d({k}) = {info['d']:,}")

    # Gap analysis
    previously_proved = list(range(3, 22))  # k=3..21 all proved
    all_proved = sorted(set(previously_proved + proved))
    remaining_gap = sorted(set(range(22, 42)) - set(proved))

    print(f"\nÉtat du gap :")
    print(f"  Avant R159 : k=3..21 prouvés, gap = 20 valeurs (k=22..41)")
    print(f"  Après R159 : gap = {len(remaining_gap)} valeurs → {remaining_gap}")

    # Save results
    output = {
        'date': '2026-03-15',
        'round': 'R159',
        'proved': proved,
        'failed': failed,
        'remaining_gap': remaining_gap,
        'total_time_s': total_time,
        'details': {str(k): v for k, v in results.items()},
    }

    output_path = '/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/R159_dp_results.json'
    with open(output_path, 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print(f"\nRésultats sauvegardés : {output_path}")

    return proved, failed


if __name__ == '__main__':
    proved, failed = main()
