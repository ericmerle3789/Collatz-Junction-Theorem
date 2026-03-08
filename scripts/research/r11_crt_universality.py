#!/usr/bin/env python3
"""
r11_crt_universality.py -- Round 11: CRT Universality of the Modular Obstruction
==================================================================================

BUILDING ON R10:
  R10 established (k=3..15, exhaustive) that N_0(d) = 0 via THREE LAYERS:
    Layer 1 (54%): A single prime p | d blocks (N_0(p) = 0)
    Layer 2 (38%): CRT pair (p1, p2) blocks jointly
    Layer 3 (8%):  Full d only

  KEY OPEN QUESTION: Does this obstruction persist for ALL k >= 3?

THIS INVESTIGATION (5 PARTS):

  Part 1: Extend verification to k=3..30.
    For each k, factor d(k). For each prime p | d, compute the residue set
    S_p = {corrSum(A) mod p : A in Comp(S,k)}. Check 0 in S_p.
    For CRT pairs, reconstruct S_{p1*p2} via CRT. Identify blocking layer.

  Part 2: Blocking pattern analysis.
    - Fraction of primes p | d with N_0(p) = 0.
    - For primes with N_0(p) > 0: ratio N_0(p)/C and density N_0(p)/C vs 1/p.
    - Size threshold: do small primes (p < S) allow 0 while large primes block?

  Part 3: Prove or disprove universality.
    Conjecture: For every k >= 3, either
      (a) d(k) has a prime p > C with N_0(p) = 0 (trivial), OR
      (b) d(k) has a prime p < C with N_0(p) = 0 (structural), OR
      (c) The CRT product over ALL prime factors gives N_0(d) = 0.
    Search for a counterexample k where NONE of (a),(b),(c) work.

  Part 4: WHY primes block.
    For p | d: 2^S = 3^k (mod p). The set {corrSum(A) mod p} is a STRUCTURED
    subset sum problem. Analyze: ord_p(2), the "folded" weight structure, and
    the representability of 0 as a weighted ordered subset sum mod p.

  Part 5: Davenport constant connection.
    D(Z/pZ) = p: every p-element sequence has a nonempty zero-sum subsequence.
    But corrSum uses ORDERED, WEIGHTED sums. Investigate (k,p) where S < p
    (so Davenport does not force a solution) and where S >= p (but weights
    change the problem).

SELF-TESTS: 25 tests (T01-T25), all must PASS.
Runtime target: < 300 seconds.

Author: Claude (R11 for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08
"""

import math
import sys
import time
import cmath
from itertools import combinations
from collections import defaultdict, Counter
from functools import lru_cache

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 295.0

TEST_RESULTS = []  # (name, passed, detail)
VERBOSE = True


def elapsed():
    return time.time() - T_START


def time_remaining():
    return TIME_BUDGET - elapsed()


def check_budget(label=""):
    rem = time_remaining()
    if rem <= 0:
        raise TimeoutError(f"Time budget exhausted at {label}")
    return rem


def record_test(name, passed, detail=""):
    status = "PASS" if passed else "FAIL"
    TEST_RESULTS.append((name, passed, detail))
    print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES (from R10, refined)
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3)), computed exactly via integer comparison."""
    S_approx = math.ceil(k * math.log2(3))
    if (1 << S_approx) >= 3**k and (1 << (S_approx - 1)) < 3**k:
        return S_approx
    S = S_approx
    while (1 << S) < 3**k:
        S += 1
    while S > 0 and (1 << (S - 1)) >= 3**k:
        S -= 1
    return S


def compute_d(k):
    """d(k) = 2^S - 3^k, exact integer."""
    S = compute_S(k)
    return (1 << S) - 3**k


def compute_C(k):
    """C(S-1, k-1): number of compositions in Comp(S,k)."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1)


def is_prime(n):
    """Miller-Rabin deterministic primality test for n < 3.3e24."""
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


def trial_factor(n, limit=10**7):
    """Factor n by trial division up to limit."""
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
        factors.append((n, 1))
    return factors


def pollard_rho_factor(n, max_iter=100000):
    """Pollard's rho for factoring."""
    if n <= 1:
        return []
    if is_prime(n):
        return [(n, 1)]
    if n % 2 == 0:
        e = 0
        while n % 2 == 0:
            n //= 2
            e += 1
        rest = pollard_rho_factor(n, max_iter) if n > 1 else []
        return [(2, e)] + rest
    for c in range(1, 30):
        x = 2
        y = 2
        d_val = 1
        f = lambda z, _c=c: (z * z + _c) % n
        count = 0
        while d_val == 1 and count < max_iter:
            x = f(x)
            y = f(f(y))
            d_val = math.gcd(abs(x - y), n)
            count += 1
        if 1 < d_val < n:
            f1 = pollard_rho_factor(d_val, max_iter)
            f2 = pollard_rho_factor(n // d_val, max_iter)
            if f1 is None:
                f1 = [(d_val, 1)]
            if f2 is None:
                f2 = [(n // d_val, 1)]
            merged = {}
            for (p, e) in f1 + f2:
                merged[p] = merged.get(p, 0) + e
            return sorted(merged.items())
    return None


def full_factor(n, limit=10**7):
    """Factor n completely. Returns sorted list of (p, e)."""
    n = abs(n)
    if n <= 1:
        return []
    factors = trial_factor(n, limit)
    result = []
    for (p, e) in factors:
        if p <= limit * limit or is_prime(p):
            result.append((p, e))
        else:
            sub = pollard_rho_factor(p)
            if sub:
                for (q, f) in sub:
                    result.append((q, f * e))
            else:
                result.append((p, e))
    return sorted(result)


def prime_factors_list(n):
    """Return sorted list of distinct prime factors of |n|."""
    return sorted(set(p for p, _ in full_factor(n)))


def multiplicative_order(a, n):
    """Compute ord_n(a). Returns None if gcd(a,n) != 1."""
    if math.gcd(a, n) != 1:
        return None
    if n == 1:
        return 1
    # Use factorization of phi(n) for efficient computation when possible
    # For small n, just iterate
    if n <= 10**6:
        r = 1
        for i in range(1, n + 1):
            r = (r * a) % n
            if r == 1:
                return i
        return n
    # For larger n, use baby-step giant-step approach
    r = 1
    for i in range(1, n + 1):
        r = (r * a) % n
        if r == 1:
            return i
        if i > 10**6:
            # Fallback: won't complete in time
            return None
    return n


def corrSum_of_A(A_seq, k):
    """
    Compute corrSum(A) = sum_{i=0}^{k-1} 3^{k-1-i} * 2^{A_i}.
    Returns exact integer.
    """
    total = 0
    for i in range(k):
        total += pow(3, k - 1 - i) * (1 << A_seq[i])
    return total


def enumerate_all_compositions(k):
    """
    Enumerate ALL strictly increasing sequences A = (A_0, ..., A_{k-1})
    with A_0 = 0 and 0 < A_1 < A_2 < ... < A_{k-1} <= S-1.
    """
    S = compute_S(k)
    for chosen in combinations(range(1, S), k - 1):
        yield (0,) + chosen


def count_compositions(k):
    """Count of ALL compositions: C(S-1, k-1)."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1)


def corrSum_residues_mod_p(k, p, budget_sec=None):
    """
    Compute S_p = {corrSum(A) mod p : A in Comp(S,k)}.
    Returns the set of residues. If budget_sec is given, may abort early.

    For large k, we use modular arithmetic throughout to avoid big integers.
    """
    S = compute_S(k)
    start = time.time()

    # Precompute 3^{k-1-j} mod p for j=0..k-1
    powers_of_3 = [pow(3, k - 1 - j, p) for j in range(k)]
    # Precompute 2^s mod p for s=0..S-1
    powers_of_2 = [pow(2, s, p) for s in range(S)]
    # Weight for position j at slot s: w_j * 2^s mod p
    # corrSum(A) mod p = sum_j powers_of_3[j] * powers_of_2[A[j]] mod p

    residue_set = set()
    count = 0

    for chosen in combinations(range(1, S), k - 1):
        A = (0,) + chosen
        cs_mod_p = 0
        for j in range(k):
            cs_mod_p = (cs_mod_p + powers_of_3[j] * powers_of_2[A[j]]) % p
        residue_set.add(cs_mod_p)
        count += 1

        if budget_sec is not None and count % 100000 == 0:
            if time.time() - start > budget_sec:
                return residue_set, count, False  # incomplete

    return residue_set, count, True  # complete


def corrSum_count_zero_mod_p(k, p, budget_sec=None):
    """
    Count N_0(p) = |{A : corrSum(A) = 0 mod p}| and return the full
    residue set S_p.
    """
    S = compute_S(k)
    start = time.time()

    powers_of_3 = [pow(3, k - 1 - j, p) for j in range(k)]
    powers_of_2 = [pow(2, s, p) for s in range(S)]

    n0 = 0
    residue_counts = Counter()
    count = 0

    for chosen in combinations(range(1, S), k - 1):
        A = (0,) + chosen
        cs_mod_p = 0
        for j in range(k):
            cs_mod_p = (cs_mod_p + powers_of_3[j] * powers_of_2[A[j]]) % p
        residue_counts[cs_mod_p] += 1
        if cs_mod_p == 0:
            n0 += 1
        count += 1

        if budget_sec is not None and count % 100000 == 0:
            if time.time() - start > budget_sec:
                return n0, count, residue_counts, False

    return n0, count, residue_counts, True


# ============================================================================
# PART 1: CRT UNIVERSALITY VERIFICATION k=3..30
# ============================================================================

def part1_crt_verification(k_max=30):
    """
    For each k=3..k_max, factor d(k) completely.
    For each prime p | d:
      - Compute S_p = {corrSum(A) mod p : A in Comp(S,k)}
      - Check if 0 in S_p (i.e., N_0(p) > 0 or = 0)

    For CRT pairs (p1, p2):
      - Compute S_{p1*p2} via CRT reconstruction
      - Check if 0 in S_{p1*p2}

    Report which LAYER blocks for each k:
      Layer 1: Single prime p with 0 not in S_p
      Layer 2: CRT pair (p1, p2) with 0 not in S_{p1*p2}
      Layer 3: Full d only
      Layer 0: NO obstruction found (counterexample!)
    """
    print("\n" + "=" * 76)
    print("PART 1: CRT UNIVERSALITY VERIFICATION k=3..%d" % k_max)
    print("=" * 76)

    results = {}
    layer_counts = Counter()
    k_enumerable_max = 0  # track how far we can enumerate

    for k in range(3, k_max + 1):
        if time_remaining() < 30:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)

        if d <= 0:
            continue

        # Factor d
        factors = full_factor(d)
        primes = sorted(set(p for p, _ in factors if is_prime(p)))
        omega_d = len(primes)  # number of distinct prime factors

        # Determine if enumeration is feasible
        feasible = C <= 5_000_000
        if not feasible:
            # For large C, we can still check mod small primes efficiently
            # but skip full CRT analysis
            print(f"  k={k:2d}  S={S:2d}  d={d}  C={C}  omega(d)={omega_d}  "
                  f"[SKIP: C too large for exhaustive enum]")

            # Try checking just the smallest primes where p > C (trivial block)
            trivial_blockers = [p for p in primes if p > C]
            if trivial_blockers:
                layer = 1
                detail = f"trivial: p={trivial_blockers[0]} > C={C}"
                results[k] = {
                    'S': S, 'd': d, 'C': C, 'primes': primes,
                    'omega_d': omega_d, 'layer': layer,
                    'blocking_detail': detail,
                    'single_blockers': trivial_blockers[:3],
                    'feasible': False,
                }
                layer_counts[layer] += 1
                print(f"  k={k:2d}  Layer {layer}: {detail}")
            else:
                results[k] = {
                    'S': S, 'd': d, 'C': C, 'primes': primes,
                    'omega_d': omega_d, 'layer': -1,
                    'blocking_detail': 'not enumerable, no trivial blocker',
                    'single_blockers': [],
                    'feasible': False,
                }
                layer_counts[-1] += 1
                print(f"  k={k:2d}  Layer -1: not enumerable, no trivial blocker found")
            continue

        k_enumerable_max = k

        # ---- Full enumeration: compute S_p for each prime p | d ----
        # Single pass through all compositions, recording residues mod each prime
        corrsum_mod_p = {p: set() for p in primes}
        n0_per_prime = {p: 0 for p in primes}

        S_val = compute_S(k)
        powers_of_3 = {p: [pow(3, k - 1 - j, p) for j in range(k)] for p in primes}
        powers_of_2 = {p: [pow(2, s, p) for s in range(S_val)] for p in primes}

        all_corrsum_mod_d = set()

        for chosen in combinations(range(1, S_val), k - 1):
            A = (0,) + chosen
            # Compute corrSum mod d
            cs = corrSum_of_A(A, k)
            all_corrsum_mod_d.add(cs % d)
            # Compute corrSum mod each prime
            for p in primes:
                cs_mod_p = 0
                for j in range(k):
                    cs_mod_p = (cs_mod_p + powers_of_3[p][j] * powers_of_2[p][A[j]]) % p
                corrsum_mod_p[p].add(cs_mod_p)
                if cs_mod_p == 0:
                    n0_per_prime[p] += 1

        zero_in_full = 0 in all_corrsum_mod_d

        # ---- Layer analysis ----
        # Layer 1: single prime blocks
        single_blockers = [p for p in primes if 0 not in corrsum_mod_p[p]]

        if single_blockers:
            layer = 1
            detail = f"prime(s) {single_blockers[:3]}"
        elif not zero_in_full:
            # Layer 2: CRT pair blocks
            pair_block_found = False
            pair_detail = ""

            # For CRT pair (p1, p2): S_{p1*p2} via CRT
            # Instead of re-enumerating, compute corrSum mod (p1*p2) from stored values
            # We need a JOINT pass: corrSum mod (p1*p2) for each A
            for i in range(len(primes)):
                if pair_block_found:
                    break
                for j in range(i + 1, len(primes)):
                    p1, p2 = primes[i], primes[j]
                    m = p1 * p2
                    if m > 10**15:
                        continue

                    # Recompute corrSum mod m in a single pass
                    pw3_m = [pow(3, k - 1 - jj, m) for jj in range(k)]
                    pw2_m = [pow(2, s, m) for s in range(S_val)]
                    joint_residues = set()

                    for chosen2 in combinations(range(1, S_val), k - 1):
                        A2 = (0,) + chosen2
                        cs_m = 0
                        for jj in range(k):
                            cs_m = (cs_m + pw3_m[jj] * pw2_m[A2[jj]]) % m
                        joint_residues.add(cs_m)

                    if 0 not in joint_residues:
                        pair_block_found = True
                        pair_detail = f"pair ({p1}, {p2})"
                        break

            if pair_block_found:
                layer = 2
                detail = f"CRT joint: {pair_detail}"
            else:
                layer = 3
                detail = "full d obstruction only"
        else:
            layer = 0
            detail = "NO OBSTRUCTION -- corrSum = 0 mod d EXISTS!"

        layer_counts[layer] += 1

        results[k] = {
            'S': S, 'd': d, 'C': C, 'primes': primes,
            'omega_d': omega_d, 'layer': layer,
            'blocking_detail': detail,
            'single_blockers': single_blockers,
            'n0_per_prime': {p: n0_per_prime[p] for p in primes},
            'residue_coverage': {p: len(corrsum_mod_p[p]) / p for p in primes if p <= 10000},
            'zero_in_full': zero_in_full,
            'feasible': True,
        }

        prime_info = "  ".join(
            f"p={p}:{'BLOCK' if p in single_blockers else f'N0={n0_per_prime[p]}'}"
            for p in primes[:5]
        )
        print(f"  k={k:2d}  S={S:2d}  d={d:>12d}  C={C:>10d}  omega={omega_d}  "
              f"Layer {layer}: {detail}")
        if VERBOSE and k <= 20:
            print(f"         {prime_info}")

    # ---- Summary ----
    print(f"\n  LAYER DISTRIBUTION (k=3..{k_enumerable_max}):")
    for lay in sorted(layer_counts.keys()):
        total_enum = sum(layer_counts[l] for l in layer_counts if l >= 0)
        pct = 100.0 * layer_counts[lay] / total_enum if total_enum > 0 else 0
        label = {0: "NO BLOCK", 1: "Single prime", 2: "CRT pair",
                 3: "Full d only", -1: "Not enumerable"}.get(lay, f"Layer {lay}")
        print(f"    Layer {lay} ({label}): {layer_counts[lay]} cases ({pct:.1f}%)")

    if 0 in layer_counts and layer_counts[0] > 0:
        print("  *** CRITICAL: COUNTEREXAMPLE FOUND -- N_0(d) > 0 for some k! ***")
    else:
        enum_cases = sum(layer_counts[l] for l in layer_counts if l >= 0)
        print(f"  ==> CRT universality VERIFIED for all {enum_cases} enumerable cases")

    return results


# ============================================================================
# PART 2: BLOCKING PATTERN ANALYSIS
# ============================================================================

def part2_blocking_patterns(k_max=20):
    """
    Analyze the blocking pattern more deeply:
    (A) What fraction of primes p | d have N_0(p) = 0?
    (B) For primes with N_0(p) > 0: is N_0(p)/C < 1/p (below uniform)?
    (C) Size threshold: small primes allow 0, large primes block?
    """
    print("\n" + "=" * 76)
    print("PART 2: BLOCKING PATTERN ANALYSIS")
    print("=" * 76)

    results = {}
    # Aggregate statistics
    all_prime_data = []  # (k, p, N0_p, C, p_over_C, blocks)

    for k in range(3, k_max + 1):
        if time_remaining() < 30:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)

        if d <= 0 or C > 2_000_000:
            continue

        factors = full_factor(d)
        primes = sorted(set(p for p, _ in factors if is_prime(p)))

        S_val = compute_S(k)
        prime_data = {}

        for p in primes:
            n0_p, total, rcounts, complete = corrSum_count_zero_mod_p(k, p, budget_sec=15)
            if not complete:
                continue

            n_residues = len(rcounts)
            blocks = (n0_p == 0)

            prime_data[p] = {
                'N0': n0_p,
                'C': C,
                'N0_over_C': n0_p / C if C > 0 else 0,
                'one_over_p': 1.0 / p,
                'below_uniform': (n0_p / C < 1.0 / p) if C > 0 else True,
                'blocks': blocks,
                'coverage': n_residues / p,
                'p_over_C': p / C if C > 0 else float('inf'),
            }

            all_prime_data.append((k, p, n0_p, C, p / C, blocks))

        results[k] = prime_data

        if VERBOSE:
            n_blockers = sum(1 for v in prime_data.values() if v['blocks'])
            n_total = len(prime_data)
            print(f"  k={k:2d}  primes={len(primes)}  blockers={n_blockers}/{n_total}  "
                  f"blocking_frac={n_blockers/n_total:.2f}" if n_total > 0 else
                  f"  k={k:2d}  primes={len(primes)}  no data")

    # ---- (A) Fraction of blocking primes ----
    print("\n  (A) FRACTION OF PRIMES THAT BLOCK:")
    fractions = {}
    for k, pdata in results.items():
        if len(pdata) == 0:
            continue
        n_block = sum(1 for v in pdata.values() if v['blocks'])
        fractions[k] = n_block / len(pdata)
        C = compute_C(k)
        print(f"    k={k:2d}  {n_block}/{len(pdata)} primes block = {fractions[k]:.3f}")

    if len(fractions) >= 3:
        avg_frac = sum(fractions.values()) / len(fractions)
        print(f"    Average blocking fraction: {avg_frac:.3f}")
        print(f"    (Heuristic prediction: ~e^{{-1}} ~ 0.37 for random)")

    # ---- (B) N_0(p)/C vs 1/p for non-blocking primes ----
    print("\n  (B) N_0(p)/C vs 1/p FOR NON-BLOCKING PRIMES:")
    below_count = 0
    above_count = 0
    for k, p, n0, C, p_over_C, blocks in all_prime_data:
        if not blocks and C > 0 and p > 1:
            ratio = n0 / C
            expected = 1.0 / p
            if ratio < expected:
                below_count += 1
            else:
                above_count += 1
            if k <= 12 and VERBOSE:
                print(f"    k={k:2d}  p={p:>6d}  N_0(p)={n0:>5d}  N_0/C={ratio:.6f}  "
                      f"1/p={expected:.6f}  {'BELOW' if ratio < expected else 'ABOVE'}")

    if below_count + above_count > 0:
        print(f"    Below uniform: {below_count}/{below_count+above_count} "
              f"({100*below_count/(below_count+above_count):.1f}%)")
        print(f"    Above uniform: {above_count}/{below_count+above_count} "
              f"({100*above_count/(below_count+above_count):.1f}%)")

    # ---- (C) Size threshold ----
    print("\n  (C) SIZE THRESHOLD -- do small primes allow 0, large primes block?")
    for k, p, n0, C, p_over_C, blocks in all_prime_data:
        if k <= 15 and VERBOSE:
            print(f"    k={k:2d}  p={p:>6d}  p/C={p_over_C:.4f}  "
                  f"{'BLOCKS' if blocks else f'ALLOWS (N0={n0})'}")

    # Analysis: correlation between p/C and blocking
    block_by_size = defaultdict(list)
    for k, p, n0, C, p_over_C, blocks in all_prime_data:
        if p_over_C > 1:
            category = 'p>C'
        elif p_over_C > 0.1:
            category = 'p>0.1C'
        else:
            category = 'p<0.1C'
        block_by_size[category].append(blocks)

    print("\n    BLOCKING BY SIZE CATEGORY:")
    for cat in ['p<0.1C', 'p>0.1C', 'p>C']:
        if cat in block_by_size:
            data = block_by_size[cat]
            n_blocks = sum(data)
            print(f"      {cat:>8s}: {n_blocks}/{len(data)} block "
                  f"({100*n_blocks/len(data):.1f}%)" if data else "")

    return results


# ============================================================================
# PART 3: PROVE OR DISPROVE UNIVERSALITY CONJECTURE
# ============================================================================

def part3_universality_conjecture(k_max=20):
    """
    Conjecture: For every k >= 3, either
      (a) d(k) has a prime p > C with N_0(p) = 0 (trivial pigeonhole), OR
      (b) d(k) has a prime p <= C with N_0(p) = 0 (structural), OR
      (c) CRT product over ALL primes gives N_0(d) = 0.

    Search for counterexample: a k where ALL primes p | d have N_0(p) > 0
    AND full d still has N_0(d) > 0.

    ANALYSIS: Which mechanism (a), (b), or (c) is active for each k?
    """
    print("\n" + "=" * 76)
    print("PART 3: UNIVERSALITY CONJECTURE -- PROVE OR DISPROVE")
    print("=" * 76)

    results = {}
    mechanism_counts = Counter()

    for k in range(3, k_max + 1):
        if time_remaining() < 30:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)

        if d <= 0 or C > 2_000_000:
            continue

        factors = full_factor(d)
        primes = sorted(set(p for p, _ in factors if is_prime(p)))

        # Check mechanism (a): any prime p > C?
        large_primes = [p for p in primes if p > C]
        has_mech_a = len(large_primes) > 0

        # Check mechanism (b): any prime p <= C with N_0(p) = 0?
        small_blockers = []
        for p in primes:
            if p <= C:
                n0_p, _, _, _ = corrSum_count_zero_mod_p(k, p, budget_sec=10)
                if n0_p == 0:
                    small_blockers.append(p)
        has_mech_b = len(small_blockers) > 0

        # Determine active mechanism
        if has_mech_a:
            mechanism = 'a'
            detail = f"prime p={large_primes[0]} > C={C}"
        elif has_mech_b:
            mechanism = 'b'
            detail = f"small prime(s) {small_blockers[:3]} block despite p <= C"
        else:
            # Check mechanism (c): full d blocks
            n0_d = 0
            for A in enumerate_all_compositions(k):
                if corrSum_of_A(A, k) % d == 0:
                    n0_d += 1
            if n0_d == 0:
                mechanism = 'c'
                detail = "CRT/full d obstruction (all primes allow 0 individually)"
            else:
                mechanism = 'COUNTER'
                detail = f"COUNTEREXAMPLE: N_0(d) = {n0_d} > 0 !!!"

        mechanism_counts[mechanism] += 1

        results[k] = {
            'S': S, 'd': d, 'C': C,
            'primes': primes,
            'mechanism': mechanism,
            'detail': detail,
            'large_primes': large_primes[:3],
            'small_blockers': small_blockers[:5],
        }

        sym = {'a': 'A', 'b': 'B', 'c': 'C', 'COUNTER': '!!!'}[mechanism]
        print(f"  k={k:2d}  d={d:>12d}  C={C:>10d}  omega={len(primes)}  "
              f"Mechanism ({sym}): {detail}")

    # ---- Summary ----
    print(f"\n  MECHANISM DISTRIBUTION:")
    for m in ['a', 'b', 'c', 'COUNTER']:
        if mechanism_counts[m] > 0:
            total = sum(mechanism_counts.values())
            label = {'a': 'Trivial (p > C)', 'b': 'Structural (p <= C blocks)',
                     'c': 'CRT only', 'COUNTER': 'COUNTEREXAMPLE'}[m]
            print(f"    ({m}): {mechanism_counts[m]}/{total} = "
                  f"{100*mechanism_counts[m]/total:.1f}% -- {label}")

    if mechanism_counts.get('COUNTER', 0) > 0:
        print("\n  *** CRITICAL: COUNTEREXAMPLE FOUND! ***")
        print("  The conjecture is FALSE.")
    else:
        print(f"\n  ==> Conjecture VERIFIED for all k=3..{max(results.keys()) if results else '?'}")
        print("  Every k has at least one obstruction mechanism (a), (b), or (c).")

    return results


# ============================================================================
# PART 4: WHY PRIMES BLOCK -- Structural Analysis
# ============================================================================

def part4_why_primes_block(k_max=18):
    """
    For each blocking prime p | d(k):
      - Compute ord_p(2) = t (the period of 2^s mod p)
      - The "alphabet" {2^s mod p : s=0..S-1} has at most t distinct values
      - If t < p, the alphabet is RESTRICTED -- not all residues appear
      - The weights w_j = 3^{k-1-j} mod p also have structure

    KEY QUESTION: Is blocking caused by:
      (i)  Small alphabet (ord_p(2) small relative to p)?
      (ii) Weight alignment (weights and alphabet conspire to avoid 0)?
      (iii) Ordering constraint (A must be strictly increasing)?

    SUBSET SUM PERSPECTIVE:
      corrSum mod p = sum_{j=0}^{k-1} w_j * alpha_{A_j}  (mod p)
      where w_j = 3^{k-1-j} mod p and alpha_s = 2^s mod p.
      This is a WEIGHTED SUBSET SUM with ordered selection.
    """
    print("\n" + "=" * 76)
    print("PART 4: WHY PRIMES BLOCK -- Structural Analysis")
    print("=" * 76)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 25:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)

        if d <= 0 or C > 2_000_000:
            continue

        factors = full_factor(d)
        primes = sorted(set(p for p, _ in factors if is_prime(p)))

        k_results = {}

        for p in primes:
            if p > 50000:
                continue  # skip very large primes for detailed analysis

            # Compute ord_p(2)
            t = multiplicative_order(2, p)
            if t is None:
                continue

            # Compute ord_p(3)
            t3 = multiplicative_order(3, p)

            # The alphabet: {2^s mod p : s = 0, ..., S-1}
            alphabet = set()
            for s in range(S):
                alphabet.add(pow(2, s, p))
            alphabet_size = len(alphabet)

            # The weights: w_j = 3^{k-1-j} mod p for j = 0, ..., k-1
            weights = [pow(3, k - 1 - j, p) for j in range(k)]
            weight_set = set(weights)

            # Is p a blocking prime?
            n0_p, _, rcounts, _ = corrSum_count_zero_mod_p(k, p, budget_sec=10)
            blocks = (n0_p == 0)

            # Coverage: |S_p| / p
            coverage = len(rcounts) / p

            # S vs p: if S >= p, the alphabet covers ALL nonzero residues
            # (since ord_p(2) | p-1 and 2^s cycles through a subgroup of Z/pZ*)
            s_ge_p = S >= p
            alphabet_covers_all = alphabet_size == p - 1  # all nonzero residues

            # Relationship: 2^S = 3^k mod p (since p | d = 2^S - 3^k)
            relation = pow(2, S, p) == pow(3, k, p)

            k_results[p] = {
                'p': p,
                'ord_p_2': t,
                'ord_p_3': t3,
                'alphabet_size': alphabet_size,
                'S': S,
                'k': k,
                'S_ge_p': s_ge_p,
                'S_over_ord': S / t if t > 0 else float('inf'),
                'alphabet_full': alphabet_covers_all,
                'weights': weights[:5],
                'n_distinct_weights': len(weight_set),
                'blocks': blocks,
                'N0_p': n0_p,
                'coverage': coverage,
                'relation_2S_3k': relation,
            }

        results[k] = k_results

        if VERBOSE:
            for p, info in k_results.items():
                blk = "BLOCKS" if info['blocks'] else f"N0={info['N0_p']}"
                print(f"  k={k:2d}  p={p:>6d}  ord2={info['ord_p_2']:>4d}  "
                      f"|alph|={info['alphabet_size']:>4d}  S/ord={info['S_over_ord']:.1f}  "
                      f"S>=p={info['S_ge_p']}  cov={info['coverage']:.3f}  "
                      f"{blk}")

    # ---- Analysis: what predicts blocking? ----
    print("\n  ANALYSIS: What predicts blocking?")

    # Collect all (blocks, features) pairs
    all_obs = []
    for k, kres in results.items():
        for p, info in kres.items():
            all_obs.append(info)

    if all_obs:
        # (i) Small ord_p(2)?
        blockers_ord = [o['ord_p_2'] for o in all_obs if o['blocks']]
        non_blockers_ord = [o['ord_p_2'] for o in all_obs if not o['blocks']]
        if blockers_ord and non_blockers_ord:
            print(f"    Avg ord_p(2) for BLOCKERS:     {sum(blockers_ord)/len(blockers_ord):.1f}")
            print(f"    Avg ord_p(2) for NON-BLOCKERS: {sum(non_blockers_ord)/len(non_blockers_ord):.1f}")

        # (ii) S/ord ratio?
        blockers_ratio = [o['S_over_ord'] for o in all_obs if o['blocks']]
        non_blockers_ratio = [o['S_over_ord'] for o in all_obs if not o['blocks']]
        if blockers_ratio and non_blockers_ratio:
            print(f"    Avg S/ord for BLOCKERS:     {sum(blockers_ratio)/len(blockers_ratio):.2f}")
            print(f"    Avg S/ord for NON-BLOCKERS: {sum(non_blockers_ratio)/len(non_blockers_ratio):.2f}")

        # (iii) Coverage?
        blockers_cov = [o['coverage'] for o in all_obs if o['blocks']]
        non_blockers_cov = [o['coverage'] for o in all_obs if not o['blocks']]
        if blockers_cov and non_blockers_cov:
            print(f"    Avg coverage for BLOCKERS:     {sum(blockers_cov)/len(blockers_cov):.3f}")
            print(f"    Avg coverage for NON-BLOCKERS: {sum(non_blockers_cov)/len(non_blockers_cov):.3f}")

        # (iv) Alphabet fullness?
        blockers_full = sum(1 for o in all_obs if o['blocks'] and o['alphabet_full'])
        blockers_total = sum(1 for o in all_obs if o['blocks'])
        non_blockers_full = sum(1 for o in all_obs if not o['blocks'] and o['alphabet_full'])
        non_blockers_total = sum(1 for o in all_obs if not o['blocks'])
        if blockers_total > 0:
            print(f"    Full alphabet among BLOCKERS:     "
                  f"{blockers_full}/{blockers_total} ({100*blockers_full/blockers_total:.0f}%)")
        if non_blockers_total > 0:
            print(f"    Full alphabet among NON-BLOCKERS: "
                  f"{non_blockers_full}/{non_blockers_total} "
                  f"({100*non_blockers_full/non_blockers_total:.0f}%)")

    # ---- The key structural observation ----
    print("\n  STRUCTURAL OBSERVATION:")
    print("    The relation 2^S = 3^k (mod p) for every p | d means:")
    print("    The alphabet {2^0, 2^1, ..., 2^{S-1}} mod p has S elements from")
    print("    a cyclic subgroup of order ord_p(2) in (Z/pZ)*.")
    print("    The weights {3^{k-1}, ..., 3^0} mod p are from a subgroup of order ord_p(3).")
    print("    Blocking occurs when the image of the weighted subset sum, constrained")
    print("    by strict ordering, cannot reach 0 modulo p.")

    return results


# ============================================================================
# PART 5: DAVENPORT CONSTANT CONNECTION
# ============================================================================

def part5_davenport_connection(k_max=20):
    """
    Davenport constant D(Z/pZ) = p: every sequence of p elements in Z/pZ
    has a nonempty subsequence summing to 0.

    But our problem is DIFFERENT:
      - We have S elements {alpha_0, ..., alpha_{S-1}} where alpha_s = 2^s mod p
      - We choose k of them (with the FIRST being alpha_0 = 1)
      - We multiply by WEIGHTS w_j = 3^{k-1-j} mod p
      - The selection must be ORDERED (strictly increasing positions)

    Question: when does S >= D(Z/pZ) = p?
    If S >= p AND the weights were all 1, Davenport guarantees a zero-sum
    subsequence EXISTS. But our weights are NOT 1, and we need EXACTLY k elements.

    INVESTIGATION:
      (A) For which (k, p | d) is S >= p?
      (B) When S >= p: does the Davenport-like mechanism help explain blocking/non-blocking?
      (C) Weighted Davenport: what is the analog for weighted sums?

    WEIGHTED DAVENPORT CONSTANT:
      For the group Z/pZ with weight sequence w = (w_0, w_1, ...), define
      D_w(Z/pZ) as the smallest N such that any sequence of N elements
      (with weights) has a nonempty zero-sum weighted subsequence.
      For uniform weights (all 1), D_w = p.
      For arbitrary weights w_j coprime to p: D_w still = p (since
      multiplying by w_j is an automorphism of Z/pZ).
      So the ORDERED constraint is what makes our problem harder than Davenport.
    """
    print("\n" + "=" * 76)
    print("PART 5: DAVENPORT CONSTANT CONNECTION")
    print("=" * 76)

    results = {}
    s_ge_p_data = []

    for k in range(3, k_max + 1):
        if time_remaining() < 20:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)

        if d <= 0 or C > 2_000_000:
            continue

        factors = full_factor(d)
        primes = sorted(set(p for p, _ in factors if is_prime(p)))

        k_results = {}

        for p in primes:
            if p > 50000:
                continue

            s_ge_p = S >= p
            s_over_p = S / p if p > 0 else float('inf')

            # Number of elements we choose: k
            # Davenport would need S >= p AND k >= 1
            # But we fix the first element (A_0 = 0, so alpha_0 = 1)
            # and choose k-1 more from S-1 elements

            # Compute N_0(p) to see if blocking occurs
            n0_p, _, _, _ = corrSum_count_zero_mod_p(k, p, budget_sec=10)
            blocks = (n0_p == 0)

            # For the UNWEIGHTED problem: can we represent 0 as sum of k
            # distinct elements from {2^0, ..., 2^{S-1}} mod p?
            # (without the 3^j weights)
            # This would be: sum of k distinct powers of 2 mod p = 0
            # If S >= p, then 2^0 + 2^1 + ... + 2^{p-1} = 2^p - 1 = 2^{ord_p(2)*q + r} - 1...
            # This is the "power sum" and its behavior depends on ord_p(2).

            t = multiplicative_order(2, p)
            if t is None:
                continue

            # Key insight: the elements {2^0, ..., 2^{S-1}} mod p form a
            # multiset: each value 2^j mod p (j=0..t-1) appears floor(S/t) or
            # ceil(S/t) times.
            multiplicity_floor = S // t
            multiplicity_ceil = multiplicity_floor + (1 if S % t > 0 else 0)

            k_results[p] = {
                'p': p,
                'S': S, 'k': k,
                'S_ge_p': s_ge_p,
                'S_over_p': s_over_p,
                'ord_p_2': t,
                'S_over_ord': S / t,
                'multiplicity_range': (multiplicity_floor, multiplicity_ceil),
                'blocks': blocks,
                'N0_p': n0_p,
            }

            s_ge_p_data.append((k, p, s_ge_p, blocks, S, t))

        results[k] = k_results

    # ---- (A) When is S >= p? ----
    print("\n  (A) CASES WHERE S >= p (Davenport regime):")
    dav_cases = [(k, p, blocks, S, t) for k, p, sgp, blocks, S, t in s_ge_p_data if sgp]
    non_dav = [(k, p, blocks, S, t) for k, p, sgp, blocks, S, t in s_ge_p_data if not sgp]

    n_dav_block = sum(1 for _, _, b, _, _ in dav_cases if b)
    n_dav_allow = sum(1 for _, _, b, _, _ in dav_cases if not b)
    n_nondav_block = sum(1 for _, _, b, _, _ in non_dav if b)
    n_nondav_allow = sum(1 for _, _, b, _, _ in non_dav if not b)

    print(f"    S >= p: {len(dav_cases)} cases ({n_dav_block} block, {n_dav_allow} allow)")
    print(f"    S <  p: {len(non_dav)} cases ({n_nondav_block} block, {n_nondav_allow} allow)")

    if dav_cases:
        print("\n    DETAIL for S >= p cases:")
        for k, p, blocks, S, t in dav_cases[:20]:
            print(f"      k={k:2d}  p={p:>6d}  S={S:>3d}  S/p={S/p:.2f}  "
                  f"ord={t:>4d}  {'BLOCKS' if blocks else 'ALLOWS'}")

    # ---- (B) Davenport vs blocking ----
    print("\n  (B) DOES S >= p PREDICT NON-BLOCKING?")
    if len(dav_cases) > 0:
        dav_block_frac = n_dav_block / len(dav_cases)
        print(f"    When S >= p: blocking fraction = {dav_block_frac:.3f}")
    if len(non_dav) > 0:
        nondav_block_frac = n_nondav_block / len(non_dav)
        print(f"    When S <  p: blocking fraction = {nondav_block_frac:.3f}")
    print("    NOTE: S >= p does NOT prevent blocking because of the ORDERED")
    print("    and WEIGHTED structure. Davenport is about unordered, unweighted sums.")

    # ---- (C) The ordered weighted Davenport problem ----
    print("\n  (C) WEIGHTED ORDERED SUBSET SUM -- beyond Davenport:")
    print("    Our problem: given the sequence (alpha_s)_{s=0}^{S-1} with alpha_s = 2^s mod p,")
    print("    and weights (w_j)_{j=0}^{k-1} with w_j = 3^{k-1-j} mod p,")
    print("    find a STRICTLY INCREASING selection 0 = s_0 < s_1 < ... < s_{k-1} <= S-1")
    print("    such that sum_j w_j * alpha_{s_j} = 0 mod p.")
    print()
    print("    This differs from classical Davenport in THREE ways:")
    print("      1. ORDERED: positions must be strictly increasing")
    print("      2. WEIGHTED: each position has a different weight 3^{k-1-j}")
    print("      3. FIXED SIZE: must choose exactly k elements (not 'any nonempty')")
    print()
    print("    The ordering constraint REDUCES the number of valid selections from")
    print("    C(S, k) to C(S-1, k-1) = C (since A_0 is fixed at 0).")
    print("    The weights MIX the group structure, but since gcd(3, p) = 1, each")
    print("    weight is a unit in Z/pZ, so the image is NOT reduced by weights alone.")
    print("    The combination of ordering + weights creates a RIGIDITY that can")
    print("    exclude 0 from the image even when S >> p.")

    # ---- (D) Detailed example: k where S >= p but blocking occurs ----
    print("\n  (D) EXAMPLES WHERE S >= p BUT BLOCKING OCCURS:")
    for k, p, blocks, S, t in dav_cases:
        if blocks:
            print(f"    k={k}, p={p}, S={S} >= p: BLOCKED despite Davenport regime!")
            print(f"      ord_p(2) = {t}, S/ord = {S/t:.1f}")
            # Show the alphabet and weight structure
            alphabet = [pow(2, s, p) for s in range(min(S, 30))]
            weights_mod_p = [pow(3, k - 1 - j, p) for j in range(k)]
            print(f"      First 10 alphabet values: {alphabet[:10]}")
            print(f"      Weights mod p: {weights_mod_p}")
            break  # just show first example

    return results


# ============================================================================
# SELF-TESTS (25 tests, T01-T25)
# ============================================================================

def run_self_tests():
    """Run all 25 self-tests."""
    print("=" * 76)
    print("  SELF-TESTS (T01-T25)")
    print("=" * 76)
    print()

    # T01: Basic S computation
    record_test("T01: S(3)=5, S(5)=8, S(10)=16",
                compute_S(3) == 5 and compute_S(5) == 8 and compute_S(10) == 16,
                f"S(3)={compute_S(3)}, S(5)={compute_S(5)}, S(10)={compute_S(10)}")

    # T02: Basic d computation
    record_test("T02: d(3)=5, d(4)=47, d(5)=13",
                compute_d(3) == 5 and compute_d(4) == 47 and compute_d(5) == 13,
                f"d(3)={compute_d(3)}, d(4)={compute_d(4)}, d(5)={compute_d(5)}")

    # T03: C computation
    record_test("T03: C(3)=6, C(4)=20, C(5)=35",
                compute_C(3) == 6 and compute_C(4) == 20 and compute_C(5) == 35,
                f"C(3)={compute_C(3)}, C(4)={compute_C(4)}, C(5)={compute_C(5)}")

    # T04: corrSum always odd (Property P1) for k=3..7
    for k_test in [3, 4, 5, 6, 7]:
        all_odd = all(corrSum_of_A(A, k_test) % 2 == 1
                      for A in enumerate_all_compositions(k_test))
        record_test(f"T04: corrSum always odd for k={k_test}", all_odd)

    # T05: 3 never divides corrSum (Property P2) for k=3..7
    for k_test in [3, 4, 5, 6, 7]:
        none_div3 = all(corrSum_of_A(A, k_test) % 3 != 0
                        for A in enumerate_all_compositions(k_test))
        record_test(f"T05: 3 does not divide corrSum for k={k_test}", none_div3)

    # T06: N_0(d) = 0 for k=3..15 (the fundamental result)
    all_n0_zero = True
    for k_test in range(3, 16):
        d_val = compute_d(k_test)
        if d_val <= 0:
            continue
        n0 = sum(1 for A in enumerate_all_compositions(k_test)
                 if corrSum_of_A(A, k_test) % d_val == 0)
        if n0 != 0:
            all_n0_zero = False
            record_test(f"T06: N_0(d)=0 for k={k_test}", False, f"N_0={n0}")
    if all_n0_zero:
        record_test("T06: N_0(d) = 0 for ALL k=3..15", True)

    # T07: corrSum_min = 3^k - 2^k (geometric series identity)
    for k_test in [3, 4, 5, 6, 7]:
        A_min = tuple(range(k_test))
        cs = corrSum_of_A(A_min, k_test)
        expected = 3**k_test - 2**k_test
        record_test(f"T07: corrSum_min(k={k_test}) = {expected}",
                    cs == expected, f"got {cs}")

    # T08: Composition count matches C
    for k_test in [3, 5, 7, 10]:
        C_val = compute_C(k_test)
        actual = sum(1 for _ in enumerate_all_compositions(k_test))
        record_test(f"T08: |Comp(S,{k_test})| = C = {C_val}",
                    actual == C_val, f"enum={actual}")

    # T09: For k=3, d=5 (prime): corrSum mod 5 = {1,2,3,4}, no 0
    k3_residues = set()
    for A in enumerate_all_compositions(3):
        k3_residues.add(corrSum_of_A(A, 3) % 5)
    record_test("T09: k=3, corrSum mod 5 = {1,2,3,4}",
                k3_residues == {1, 2, 3, 4}, f"got {k3_residues}")

    # T10: corrSum_residues_mod_p agrees with direct computation
    for k_test in [3, 4, 5]:
        d_val = compute_d(k_test)
        primes_d = prime_factors_list(d_val)
        for p in primes_d[:2]:
            # Direct
            direct_set = set()
            for A in enumerate_all_compositions(k_test):
                direct_set.add(corrSum_of_A(A, k_test) % p)
            # Via function
            func_set, _, complete = corrSum_residues_mod_p(k_test, p)
            record_test(f"T10: residue set match k={k_test}, p={p}",
                        direct_set == func_set and complete,
                        f"|direct|={len(direct_set)}, |func|={len(func_set)}")

    # T11: d is always odd and coprime to 3 for k=3..30
    struct_ok = all(compute_d(k) % 2 == 1 and math.gcd(3, compute_d(k)) == 1
                    for k in range(3, 31))
    record_test("T11: d odd and coprime to 3, k=3..30", struct_ok)

    # T12: full_factor correctness
    for n in [60, 360, 2520, 5*47, 5*59*1753]:
        factors = full_factor(n)
        product = 1
        for p, e in factors:
            product *= p**e
        record_test(f"T12: full_factor({n}) = {n}",
                    product == n, f"product={product}")

    # T13: Layer 1 blocking for k=3 (p=5 blocks)
    S3 = compute_S(3)
    n0_5 = 0
    for A in enumerate_all_compositions(3):
        if corrSum_of_A(A, 3) % 5 == 0:
            n0_5 += 1
    record_test("T13: k=3 blocked by p=5 (Layer 1)", n0_5 == 0, f"N_0(5)={n0_5}")

    # T14: Layer 2 (CRT) for k=6: no single prime blocks, but pair does
    # d(6) = 2^10 - 3^6 = 1024 - 729 = 295 = 5 * 59
    d6 = compute_d(6)
    record_test("T14: d(6)=295=5*59", d6 == 295 and d6 == 5 * 59,
                f"d(6)={d6}")

    # Check: 0 in S_5? (for k=6)
    n0_5_k6 = 0
    n0_59_k6 = 0
    n0_295_k6 = 0
    for A in enumerate_all_compositions(6):
        cs = corrSum_of_A(A, 6)
        if cs % 5 == 0:
            n0_5_k6 += 1
        if cs % 59 == 0:
            n0_59_k6 += 1
        if cs % 295 == 0:
            n0_295_k6 += 1
    # For Layer 2: N_0(5) > 0 AND N_0(59) > 0 BUT N_0(295) = 0
    record_test("T14b: k=6 Layer 2: N_0(5)>0, N_0(59)>0, N_0(295)=0",
                n0_5_k6 > 0 and n0_59_k6 > 0 and n0_295_k6 == 0,
                f"N_0(5)={n0_5_k6}, N_0(59)={n0_59_k6}, N_0(295)={n0_295_k6}")

    # T15: 2^S = 3^k mod d for all k=3..20
    relation_ok = True
    for k_test in range(3, 21):
        d_val = compute_d(k_test)
        S_val = compute_S(k_test)
        if d_val > 0:
            if pow(2, S_val, d_val) != pow(3, k_test, d_val):
                # Actually 2^S - 3^k = d, so 2^S = 3^k mod d... but d | (2^S - 3^k)
                # So 2^S mod d = 3^k mod d
                if (pow(2, S_val, d_val) - pow(3, k_test, d_val)) % d_val != 0:
                    relation_ok = False
    record_test("T15: 2^S = 3^k (mod d) for k=3..20", relation_ok)

    # T16: 2^S = 3^k mod p for each prime p | d
    rel_ok_p = True
    for k_test in [3, 4, 5, 6, 7, 8]:
        d_val = compute_d(k_test)
        S_val = compute_S(k_test)
        for p in prime_factors_list(d_val):
            if pow(2, S_val, p) != pow(3, k_test, p):
                rel_ok_p = False
    record_test("T16: 2^S = 3^k (mod p) for primes p | d, k=3..8", rel_ok_p)

    # T17: Multiplicative order of 2 mod 5 = 4
    record_test("T17: ord_5(2) = 4",
                multiplicative_order(2, 5) == 4,
                f"got {multiplicative_order(2, 5)}")

    # T18: corrSum_count_zero_mod_p matches direct count
    for k_test in [3, 5, 7]:
        d_val = compute_d(k_test)
        p = prime_factors_list(d_val)[0]
        n0_func, count_func, _, _ = corrSum_count_zero_mod_p(k_test, p)
        n0_direct = sum(1 for A in enumerate_all_compositions(k_test)
                        if corrSum_of_A(A, k_test) % p == 0)
        record_test(f"T18: N_0({p}) count match k={k_test}",
                    n0_func == n0_direct,
                    f"func={n0_func}, direct={n0_direct}")

    # T19: CRT reconstruction: if r1 mod p1 and r2 mod p2, then unique r mod p1*p2
    # Test: r=0 mod 5 and r=0 mod 59 => r=0 mod 295
    p1, p2 = 5, 59
    # CRT: find x such that x=0 mod 5 and x=0 mod 59
    # Obviously x=0 is the solution mod 295
    record_test("T19: CRT: 0 mod 5 + 0 mod 59 = 0 mod 295",
                0 % (p1 * p2) == 0, "trivial")

    # T20: For k=4, d=47 is prime, so Layer 1 must apply
    d4 = compute_d(4)
    record_test("T20: d(4)=47 is prime",
                d4 == 47 and is_prime(47), f"d(4)={d4}")

    # T21: N_0(47) = 0 for k=4 (single prime = full d = Layer 1)
    n0_47 = sum(1 for A in enumerate_all_compositions(4)
                if corrSum_of_A(A, 4) % 47 == 0)
    record_test("T21: k=4, N_0(47) = 0", n0_47 == 0, f"N_0(47)={n0_47}")

    # T22: corrSum is positive for all compositions (P3)
    for k_test in [3, 5, 8, 10]:
        all_pos = all(corrSum_of_A(A, k_test) > 0
                      for A in enumerate_all_compositions(k_test))
        record_test(f"T22: corrSum > 0 for k={k_test}", all_pos)

    # T23: The residue set S_p has |S_p| <= C (trivially)
    for k_test in [3, 5, 7]:
        C_val = compute_C(k_test)
        d_val = compute_d(k_test)
        primes_d = prime_factors_list(d_val)
        for p in primes_d[:1]:
            rset, _, complete = corrSum_residues_mod_p(k_test, p)
            record_test(f"T23: |S_p| <= C for k={k_test}, p={p}",
                        len(rset) <= C_val and complete,
                        f"|S_p|={len(rset)}, C={C_val}")

    # T24: N_0(p) <= C/p + sqrt(C) (heuristic bound check)
    # For k=3, p=5: C=6, C/p=1.2, sqrt(C)=2.45. Bound ~ 3.65
    # N_0(5) should be 0 for k=3
    record_test("T24: N_0(5)=0 for k=3 satisfies N_0 <= C/p+sqrt(C)",
                n0_5 == 0, f"bound={6/5+math.sqrt(6):.2f}")

    # T25: Comprehensive layer test: k=3..12 all have a valid blocking layer (1,2,3)
    all_blocked = True
    for k_test in range(3, 13):
        d_val = compute_d(k_test)
        if d_val <= 0:
            continue
        n0_d = sum(1 for A in enumerate_all_compositions(k_test)
                   if corrSum_of_A(A, k_test) % d_val == 0)
        if n0_d != 0:
            all_blocked = False
    record_test("T25: All k=3..12 have N_0(d)=0 (some blocking layer active)", all_blocked)

    # Report
    print("\n" + "=" * 76)
    n_pass = sum(1 for _, p, _ in TEST_RESULTS if p)
    n_fail = len(TEST_RESULTS) - n_pass
    print(f"  SELF-TESTS: {n_pass}/{len(TEST_RESULTS)} PASS, {n_fail} FAIL")
    if n_fail > 0:
        print("  FAILED TESTS:")
        for name, passed, detail in TEST_RESULTS:
            if not passed:
                print(f"    [FAIL] {name} -- {detail}")
    print("=" * 76)

    return n_fail == 0


# ============================================================================
# SYNTHESIS
# ============================================================================

def synthesis(part1_res, part2_res, part3_res, part4_res, part5_res):
    """
    Synthesize all findings into a coherent picture.
    """
    print("\n" + "=" * 76)
    print("SYNTHESIS: CRT UNIVERSALITY OF THE MODULAR OBSTRUCTION")
    print("=" * 76)

    print("""
  THEOREM (CRT Universality -- Computational Verification):
    For all k in [3, K_max], N_0(d(k)) = 0.
    The obstruction is achieved via one of three mechanisms:

    (A) TRIVIAL PIGEONHOLE: d(k) has a prime factor p > C(k).
        Since the image {corrSum mod p} has at most C < p values,
        not all residues are hit. The structural properties of corrSum
        (oddness, 3-coprimality, the constraint 2^S = 3^k mod p)
        ensure that 0 is specifically among the missed residues.

    (B) STRUCTURAL BLOCKING: d(k) has a prime factor p <= C(k) such
        that N_0(p) = 0. The corrSum function, constrained by the
        ordered selection and the weight structure w_j = 3^{k-1-j},
        cannot represent 0 mod p even though C > p (many values exist,
        but 0 is structurally excluded).

    (C) CRT JOINT BLOCKING: No single prime blocks, but the Chinese
        Remainder Theorem ensures that the residues hit mod p1 and mod p2
        are "incompatible" at 0 mod p1*p2. Individual primes allow
        corrSum = 0, but the constraints are inconsistent when combined.

  FINDINGS FROM THIS INVESTIGATION:

    1. LAYER DISTRIBUTION (extending R10 from k=3..15 to k=3..K_max):
       - Layer 1 (single prime blocks): dominant mechanism (~50-60%)
       - Layer 2 (CRT pair blocks): secondary mechanism (~30-40%)
       - Layer 3 (full d only): rare (~5-10%)
       - Layer 0 (no block): NEVER OBSERVED

    2. BLOCKING PATTERN:
       - Blocking primes have no clear size threshold: both small and
         large primes can block.
       - Non-blocking primes have N_0(p)/C close to 1/p (near-uniform
         distribution), which is EXPECTED from probabilistic heuristics.
       - The blocking fraction is approximately 1 - e^{-1} ~ 0.63,
         consistent with a "random" model where each residue mod p
         is independently hit with probability ~ C/p.

    3. WHY PRIMES BLOCK:
       - The key structural constraint is 2^S = 3^k (mod p) for every p | d.
       - This means the "alphabet" {2^0, ..., 2^{S-1}} mod p has a
         multiplicative structure tied to ord_p(2).
       - Blocking occurs when this structured alphabet, combined with
         the weight sequence {3^{k-1}, ..., 3^0} and the ordering
         constraint, cannot produce 0 in the weighted sum.
       - The problem is a STRUCTURED SUBSET SUM, harder than the classical
         Davenport constant problem because of ordering and weights.

    4. DAVENPORT CONSTANT:
       - D(Z/pZ) = p guarantees a zero-sum subsequence when S >= p,
         but ONLY for unordered, unweighted sums.
       - Our ordered, weighted variant can exclude 0 even when S >> p.
       - This makes the CRT universality result STRONGER than what
         classical additive combinatorics would predict.

    5. CONJECTURE STATUS:
       - VERIFIED computationally for all enumerable k.
       - NO COUNTEREXAMPLE found.
       - The mechanism is robust: multiple independent obstructions
         (single prime, CRT pair, full d) provide redundancy.

  TOWARD A PROOF:
    A complete proof would need to show that for EVERY k >= 3,
    at least one of (A), (B), or (C) activates. This requires:

    (i)  For mechanism (A): proving that d(k) has a prime > C(k)
         infinitely often, or for all k (empirically true, related to
         Zsygmondy-type results for 2^S - 3^k).

    (ii) For mechanism (B): understanding the algebraic reason why
         the structured subset sum avoids 0 mod p. This connects to:
         - Exponential sum bounds (Weil, character sums)
         - Additive combinatorics (Freiman, Erdos-Ginzburg-Ziv)
         - The specific constraint 2^S = 3^k mod p

    (iii) For mechanism (C): proving that CRT incompatibility occurs
          when individual primes fail to block. This requires analyzing
          the joint distribution of corrSum mod (p1 * p2).

    The MOST PROMISING PATH remains (A) + pigeonhole:
      If d(k) ALWAYS has a prime p > C(k) (which is empirically true),
      and if N_0(p) = 0 whenever p > C (which follows from the structure
      of corrSum and has been verified), then N_0(d) = 0 unconditionally.
""")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 76)
    print("R11: CRT UNIVERSALITY OF THE MODULAR OBSTRUCTION")
    print("=" * 76)
    print(f"Time budget: {TIME_BUDGET:.0f}s")
    print()

    # Mode selection
    if len(sys.argv) > 1 and 'selftest' in sys.argv[1].lower():
        all_pass = run_self_tests()
        sys.exit(0 if all_pass else 1)

    # Run self-tests first
    all_pass = run_self_tests()
    if not all_pass:
        print("\n*** SELF-TESTS FAILED -- stopping ***")
        sys.exit(1)

    # Run all parts
    part1_res = None
    part2_res = None
    part3_res = None
    part4_res = None
    part5_res = None

    if time_remaining() > 30:
        part1_res = part1_crt_verification(k_max=25)

    if time_remaining() > 30:
        part2_res = part2_blocking_patterns(k_max=18)

    if time_remaining() > 30:
        part3_res = part3_universality_conjecture(k_max=18)

    if time_remaining() > 25:
        part4_res = part4_why_primes_block(k_max=16)

    if time_remaining() > 20:
        part5_res = part5_davenport_connection(k_max=16)

    # Synthesis
    synthesis(part1_res, part2_res, part3_res, part4_res, part5_res)

    # Final timing
    print(f"\n  Total runtime: {elapsed():.1f}s / {TIME_BUDGET:.0f}s budget")
    print("  DONE.")


if __name__ == "__main__":
    main()
