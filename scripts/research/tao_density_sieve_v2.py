#!/usr/bin/env python3
"""
tao_density_sieve_v2.py — CORRECTED Density Sieve with S = ceil(k * log2(3))

CRITICAL CORRECTION: The previous version used S = 2k+1 (wrong).
The correct formula is S = ceil(k * log2(3)), which gives the MINIMAL
number of even steps needed for 2^S > 3^k (necessary for d > 0).

For k=22: S = 35 (not 45)
For k=41: S = 65 (not 83)

Also corrected: the DP counts C(S, k) compositions (not C(S-1, k-1))
because B_j ranges over k-element subsets of {0, ..., S-1}.
The actual number of valid compositions depends on the convention.

We use the project's convention: C(S-1, k-1) monotone compositions.

Also incorporates the finding that survival ≈ (S/k)/p ≈ (2+1/k)/p
(empirically, the total over all residues = C(S,k) = (S/k)*C(S-1,k-1)).

Author: Eric Merle (with Claude)
Date: 2026-03-15
"""

import math
import time
from collections import Counter


def compute_S(k):
    """S = ceil(k * log2(3)) — minimal S such that 2^S > 3^k."""
    return math.ceil(k * math.log2(3))


def compute_d(k):
    """d(k) = 2^S - 3^k with S = ceil(k * log2(3))."""
    S = compute_S(k)
    return (1 << S) - 3**k


def compute_C(k):
    """Number of monotone compositions = C(S-1, k-1)."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1)


def naive_ratio(k):
    """C(S-1, k-1) / d(k)."""
    d = compute_d(k)
    C = compute_C(k)
    return C / d if d > 0 else float('inf')


# ============================================================
# Factorization
# ============================================================

def trial_factor(n, limit=10**7):
    factors = []
    if n <= 0:
        return factors
    d = 2
    while d * d <= n and d <= limit:
        if n % d == 0:
            exp = 0
            while n % d == 0:
                n //= d
                exp += 1
            factors.append((d, exp))
        d += 1 if d == 2 else 2
    if n > 1:
        factors.append((n, 1))
    return factors


def is_probable_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0: return False
    r, d = 0, n - 1
    while d % 2 == 0: r += 1; d //= 2
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if a >= n: continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(r - 1):
            x = pow(x, x, n)
            if x == n - 1: break
        else:
            return False
    return True


def pollard_rho(n, max_iter=10**6):
    if is_probable_prime(n): return [(n, 1)]
    if n % 2 == 0:
        e = 0
        while n % 2 == 0: n //= 2; e += 1
        result = [(2, e)]
        if n > 1: result.extend(pollard_rho(n))
        return result
    import random
    for c in range(1, 200):
        x = random.randint(2, n - 1)
        y = x; d = 1
        f = lambda x: (x * x + c) % n
        iters = 0
        while d == 1 and iters < max_iter:
            x = f(x); y = f(f(y))
            d = math.gcd(abs(x - y), n)
            iters += 1
        if d != n and d != 1:
            result = []
            for part in [d, n // d]:
                if is_probable_prime(part): result.append((part, 1))
                else: result.extend(pollard_rho(part))
            return result
    return [(n, 1)]


def factor_dk(k):
    d = compute_d(k)
    if d <= 0: return [], d
    factors = trial_factor(d, limit=10**7)
    product = 1
    for p, e in factors: product *= p ** e
    remaining = d // product
    if remaining > 1:
        if is_probable_prime(remaining): factors.append((remaining, 1))
        else: factors.extend(pollard_rho(remaining))
    return factors, d


# ============================================================
# Exact DP for survival fraction mod p
# ============================================================

def exact_N0_mod_p(k, p):
    """
    Exact count of monotone compositions with corrSum = 0 mod p.
    Uses the project convention: B_j in {0,...,S-1}, strictly increasing.
    """
    S = compute_S(k)

    coeff = [[0] * S for _ in range(k)]
    for j in range(k):
        pow3 = pow(3, k - 1 - j, p)
        pow2 = 1
        for b in range(S):
            coeff[j][b] = (pow3 * pow2) % p
            pow2 = (pow2 * 2) % p

    max_b0 = S - k
    prefix = [[0] * p for _ in range(S)]
    for b in range(max_b0 + 1):
        r = coeff[0][b]
        prefix[b][r] += 1
    for b in range(1, S):
        for r in range(p):
            prefix[b][r] += prefix[b - 1][r]

    for j in range(1, k):
        min_bj = j
        max_bj = S - (k - j)
        new_prefix = [[0] * p for _ in range(S)]
        for b in range(min_bj, max_bj + 1):
            c = coeff[j][b]
            for r_new in range(p):
                r_old = (r_new - c) % p
                new_prefix[b][r_new] = prefix[b - 1][r_old]
        for b in range(1, S):
            for r in range(p):
                new_prefix[b][r] += new_prefix[b - 1][r]
        prefix = new_prefix

    return prefix[S - 1][0]


def exact_total_compositions(k, p):
    """Total compositions counted by DP (sum over all residues = C(S, k))."""
    S = compute_S(k)
    # C(S, k) = number of k-subsets of {0,...,S-1}
    return math.comb(S, k)


# ============================================================
# Main Analysis
# ============================================================

def tao_drift_analysis():
    print("=" * 80)
    print("TAO'S DRIFT ANALYSIS (corrected S = ceil(k*log2(3)))")
    print("=" * 80)
    print()
    print(f"{'k':>3s} | {'S':>3s} | {'3^k/2^S':>12s} | {'log(3^k/2^S)':>14s} | {'drift/step':>12s}")
    print("-" * 60)

    for k in range(22, 42):
        S = compute_S(k)
        log_factor = k * math.log(3) - S * math.log(2)
        drift = log_factor / k
        factor = math.exp(log_factor)
        print(f"{k:3d} | {S:3d} | {factor:12.6e} | {log_factor:14.6f} | {drift:12.6f}")

    print()
    print("Note: 3^k/2^S is close to 1 (not << 1) because S = ceil(k*log2(3)).")
    print("This is the TIGHTEST possible S, making cycles hardest to exclude.")


def density_sieve_v2():
    print()
    print("=" * 80)
    print("DENSITY SIEVE v2 (S = ceil(k*log2(3)))")
    print("=" * 80)
    print()

    results = []

    for k in range(22, 42):
        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        ratio = C / d if d > 0 else float('inf')

        factors, _ = factor_dk(k)
        factor_str = " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in factors)

        print(f"k={k:2d}, S={S:2d}, d={d}, C={C}")
        print(f"  C/d = {ratio:.6f}")
        print(f"  Factors: {factor_str}")

        # Compute exact survival for small primes
        survival_details = []
        for p, e in factors:
            if p <= 500:
                t0 = time.time()
                n0 = exact_N0_mod_p(k, p)
                elapsed = time.time() - t0
                # The DP counts from C(S,k) total, not C(S-1,k-1)
                # So survival fraction relative to C(S,k) is n0/C(S,k)
                # But we want relative to C(S-1,k-1)
                total_dp = math.comb(S, k)
                frac_dp = n0 / total_dp  # fraction of DP compositions
                frac_c = n0 / C          # fraction of "our" compositions
                survival_details.append((p, e, n0, frac_dp, frac_c, True, elapsed))
                print(f"  p={p}: N0={n0}, frac(C(S,k))={frac_dp:.6e}, "
                      f"frac(C)={frac_c:.6e}, 1/p={1/p:.6e}, "
                      f"ratio_dp={frac_dp*p:.4f}, ratio_C={frac_c*p:.4f} [{elapsed:.2f}s]")
            else:
                survival_details.append((p, e, None, 1/p, 1/p, False, 0))
                print(f"  p={p}: heuristic 1/p={1/p:.6e}")

        # CRT effective count using the CORRECT survival fractions
        # The true survival relative to C is n0/C ≈ (S/k)/p
        # So effective count ≈ (S/k)^omega * C / prod(p_i)
        # = (S/k)^omega * C / d (if d = prod p_i^e_i)

        # Actually, for the CRT approach:
        # N_0(d) = 0 iff there are NO compositions with corrSum = 0 mod d
        # The DP counts n0 = #{B : corrSum(B) = 0 mod p} out of C(S,k) total
        # The actual count we need is from C(S-1,k-1), not C(S,k)
        #
        # KEY INSIGHT: The DP over-counts by factor S/k because it considers
        # B_j in {0,...,S-1} with |B|=k (giving C(S,k) subsets)
        # but the actual monotone compositions only use C(S-1,k-1)
        #
        # Wait - let me verify what the project ACTUALLY counts.
        # The r128 script uses a_j >= 1 with sum = S, giving compositions of S into k parts.
        # C(S-1, k-1) is compositions of S into k positive parts.
        # Our DP counts k-subsets of {0,...,S-1}, which is C(S,k).
        # These are DIFFERENT objects but related by a bijection shift.
        #
        # Subsets {B_0 < B_1 < ... < B_{k-1}} of {0,...,S-1}
        # vs compositions a_j = B_j - B_{j-1} (with B_{-1} = -1) ...
        #
        # Actually: k-subsets of {0,...,S-1} biject to strictly increasing sequences
        # There are C(S,k) such subsets.
        # Compositions of S into k positive parts biject via a_j = B_j - B_{j-1} - 1 + 1
        # Hmm, this is getting confusing. Let me just check numerically.

        print(f"  C(S-1,k-1) = {C}, C(S,k) = {math.comb(S,k)}, ratio = {math.comb(S,k)/C:.6f} = S/k = {S/k:.6f}")
        print()

        results.append({
            'k': k, 'S': S, 'd': d, 'C': C, 'ratio': ratio,
            'factors': factors, 'details': survival_details
        })

    # Summary
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    print()
    print(f"{'k':>3s} | {'S':>3s} | {'C/d':>10s} | {'d':>20s} | {'#factors':>8s} | {'Note':>15s}")
    print("-" * 75)

    for r in results:
        k, S, d, C = r['k'], r['S'], r['d'], r['C']
        ratio = r['ratio']
        nf = len(r['factors'])
        note = "HARD" if ratio > 0.5 else ("moderate" if ratio > 0.1 else "easier")
        print(f"{k:3d} | {S:3d} | {ratio:10.6f} | {d:20d} | {nf:8d} | {note:>15s}")

    print()
    print("KEY FINDINGS:")
    print(f"  Maximum C/d = {max(r['ratio'] for r in results):.6f} at k={max(results, key=lambda r: r['ratio'])['k']}")
    print(f"  All C/d < 1 for k=22..41: {'YES' if all(r['ratio'] < 1 for r in results) else 'NO'}")
    print()

    # The CRT sieve needs exact survival fractions
    # From validation: survival*p ≈ S/k (not 1)
    # So for CRT: effective_count ≈ (S/k) * C / d (since we use 1/p heuristic and correct by S/k)
    # But with exact computation, we get the true survival fraction directly.

    print("CRT SIEVE ANALYSIS (with exact survival where available):")
    print()

    for r in results:
        k, S, d, C = r['k'], r['S'], r['d'], r['C']

        # For exact primes: use true N0/C(S,k) as survival
        # For heuristic primes: use 1/p
        # The question is: for CRT product, multiply survival fractions
        # and multiply by C(S,k) (total DP compositions)

        total_dp = math.comb(S, k)
        crt_product = 1.0
        all_exact = True

        for p, e, n0, frac_dp, frac_c, is_exact, elapsed in r['details']:
            if is_exact:
                crt_product *= frac_dp  # exact survival relative to C(S,k)
            else:
                crt_product *= 1.0 / p  # heuristic
                all_exact = False

        # The DP total is C(S,k), and we multiply survival fractions
        # to get expected N_0 among C(S,k) compositions
        effective_dp = crt_product * total_dp

        # But we need N_0 among the C(S-1,k-1) compositions
        # If the factor S/k applies uniformly, then effective_C = effective_dp * (k/S)
        # Hmm, this is not obvious. Let's just report both.

        tag = "exact" if all_exact else "mixed"
        print(f"  k={k:2d}: CRT effective (C(S,k) base) = {effective_dp:.6e}, "
              f"C/d = {r['ratio']:.6f} [{tag}]")


def exact_validation():
    """Validate with full exact computation for small moduli."""
    print()
    print("=" * 80)
    print("EXACT VALIDATION: survival*p for correct S")
    print("=" * 80)
    print()

    for k in [22, 23, 25, 30, 35, 41]:
        S = compute_S(k)
        C = compute_C(k)
        total_dp = math.comb(S, k)

        print(f"k={k}, S={S}, C(S-1,k-1)={C}, C(S,k)={total_dp}")

        for p in [5, 7, 11, 13, 17]:
            n0 = exact_N0_mod_p(k, p)
            frac_dp = n0 / total_dp
            print(f"  p={p:3d}: N0={n0:15d}, N0/C(S,k)={frac_dp:.8e}, "
                  f"ratio*p={frac_dp*p:.6f}, 1/p={1/p:.8e}")

        print()


def corrected_effective_counts():
    """
    The KEY question: what is the correct effective count?

    The DP counts subsets of {0,...,S-1} of size k, totaling C(S,k).
    Each subset maps to a corrSum value.
    N_0(p) = #{subsets with corrSum = 0 mod p}.

    Empirically: N_0(p)/C(S,k) ≈ 1/p (equidistribution over C(S,k) subsets).
    So survival fraction ≈ 1/p relative to C(S,k).

    But we previously saw N_0(p)/C(S-1,k-1) ≈ (S/k)/p, which is consistent
    since C(S,k)/C(S-1,k-1) = S/k.

    The correct effective count for CRT is:
    N_0(d) ≈ C(S,k) * prod(1/p_i) = C(S,k) / d

    Let's check if C(S,k)/d < 1 for all k=22..41.
    """
    print()
    print("=" * 80)
    print("CORRECTED EFFECTIVE COUNTS: C(S,k)/d")
    print("=" * 80)
    print()
    print("Under equidistribution (survival = 1/p relative to C(S,k)):")
    print("  effective N_0 ≈ C(S,k) / d")
    print()
    print(f"{'k':>3s} | {'S':>3s} | {'C(S,k)':>20s} | {'d':>20s} | {'C(S,k)/d':>12s} | {'Status':>8s}")
    print("-" * 80)

    for k in range(22, 42):
        S = compute_S(k)
        d = compute_d(k)
        csk = math.comb(S, k)
        ratio = csk / d
        status = "< 1" if ratio < 1 else ">= 1"
        print(f"{k:3d} | {S:3d} | {csk:20d} | {d:20d} | {ratio:12.6f} | {status:>8s}")

    print()
    max_k = max(range(22, 42), key=lambda k: math.comb(compute_S(k), k) / compute_d(k))
    max_ratio = math.comb(compute_S(max_k), max_k) / compute_d(max_k)
    print(f"Maximum C(S,k)/d = {max_ratio:.6f} at k={max_k}")

    if max_ratio < 1:
        print("ALL effective counts < 1 under equidistribution!")
    else:
        hard = [k for k in range(22, 42) if math.comb(compute_S(k), k) / compute_d(k) >= 1]
        print(f"HARD cases (C(S,k)/d >= 1): k = {hard}")


def main():
    tao_drift_analysis()
    exact_validation()
    corrected_effective_counts()
    density_sieve_v2()


if __name__ == "__main__":
    main()
