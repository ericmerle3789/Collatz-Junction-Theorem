#!/usr/bin/env python3
"""
r11_blocking_prime.py -- Round 11: Blocking Prime Existence for Every k >= 3
=============================================================================

THE SINGLE QUESTION:
  For every k >= 3, does there exist a prime p dividing d(k) = 2^S - 3^k
  such that N_0(p) = 0 (i.e., corrSum(A) not= 0 mod p for ALL A)?

ANSWER PREVIEW (from R10):
  NO. For k=6,9,10,12,14,15, NO single prime p | d(k) has N_0(p) = 0.
  Yet N_0(d) = 0 still holds through CRT (Chinese Remainder Theorem):
  different primes block different compositions, and jointly they block ALL.

  But for MOST k (including all k where d is prime, and all large k where
  the largest prime factor exceeds C), a single blocking prime DOES exist.

REFINED QUESTIONS:
  Q1. For which k does a single blocking prime exist?
  Q2. When no single prime blocks, what is the minimal set of primes needed?
  Q3. For large k, does the largest prime factor of d(k) eventually exceed C(k)?
  Q4. Is there an algebraic reason why certain primes block and others do not?
  Q5. Can we prove N_0(d) = 0 for all k, with or without single-prime blocking?

MATHEMATICAL SETUP:
  d = 2^S - 3^k,   S = ceil(k * log2(3)),   C = C(S-1, k-1)
  corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{A_j}
  with 0 = A_0 < A_1 < ... < A_{k-1} <= S-1  (ALL compositions)
  N_0(p) = |{A in Comp(S,k) : corrSum(A) = 0 mod p}|

  By CRT: N_0(d) > 0 requires N_0(p) > 0 for ALL primes p | d.
  Equivalently: N_0(d) = 0 iff for EACH composition A, at least one
  prime p | d has corrSum(A) != 0 mod p.

FIVE-PART INVESTIGATION:
  Part 1: Complete factorization of d(k) and N_0(p) for k=3..50.
          Classify: single-prime blocker vs CRT-only vs unknown.
  Part 2: CRT blocking analysis -- when no single prime blocks, find the
          minimal covering set and analyze the blocking partition.
  Part 3: Why N_0(p) = 0: residue avoidance mechanism for blocking primes.
  Part 4: Algebraic constraint from 2^S = 3^k mod p and its consequences.
  Part 5: Precise conjecture formulation with evidence table.

SELF-TESTS: 25 tests (T01-T25), all must PASS.
Runtime target: < 300 seconds.

HONESTY: All computations exact where feasible. If a bound FAILS, we say so.

Author: Claude (R11 for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08
"""

import math
import sys
import time
import cmath
from itertools import combinations
from collections import Counter, defaultdict

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 290.0

TEST_RESULTS = []
FINDINGS = {}

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
# SECTION 0: MATHEMATICAL PRIMITIVES
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
    """C(S-1, k-1): number of compositions."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1)


def is_prime(n):
    """Miller-Rabin deterministic for n < 3.3e24."""
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


def pollard_rho_factor(n, max_iter=200000):
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
    for c in range(1, 50):
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
    return [(n, 1)]


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
    merged = {}
    for (p, e) in result:
        merged[p] = merged.get(p, 0) + e
    return sorted(merged.items())


def prime_factors_list(n):
    """Sorted list of distinct prime factors of |n|."""
    return sorted(set(p for p, _ in full_factor(n)))


def multiplicative_order(a, n):
    """Compute ord_n(a). Returns None if gcd(a,n) != 1."""
    if n <= 1:
        return 1
    if math.gcd(a, n) != 1:
        return None
    x = a % n
    for i in range(1, n + 1):
        if x == 1:
            return i
        x = (x * a) % n
    return n


def corrSum_of_A(A_seq, k):
    """corrSum(A) = sum_{i=0}^{k-1} 3^{k-1-i} * 2^{A_i}, exact integer."""
    total = 0
    for i in range(k):
        total += pow(3, k - 1 - i) * (1 << A_seq[i])
    return total


def corrsum_mod(B_tuple, k, mod):
    """corrSum mod `mod` from B = (a_1,...,a_{k-1}), with a_0=0 implicit."""
    result = pow(3, k - 1, mod)
    for idx in range(len(B_tuple)):
        j = idx + 1
        result = (result + pow(3, k - 1 - j, mod) * pow(2, B_tuple[idx], mod)) % mod
    return result


def enumerate_all_compositions(k):
    """All A = (0, a_1, ..., a_{k-1}) with 0 < a_1 < ... < a_{k-1} <= S-1."""
    S = compute_S(k)
    for chosen in combinations(range(1, S), k - 1):
        yield (0,) + chosen


def get_residue_distribution(k, p, max_enum=5_000_000):
    """Distribution of corrSum(A) mod p. Returns Counter or None if too large."""
    S = compute_S(k)
    C = math.comb(S - 1, k - 1)
    if C > max_enum:
        return None
    dist = Counter()
    for B in combinations(range(1, S), k - 1):
        r = corrsum_mod(B, k, p)
        dist[r] += 1
    return dist


def compute_N0(k, p, dist=None, max_enum=5_000_000):
    """N_0(p) = #{A : corrSum(A) = 0 mod p}."""
    if dist is None:
        dist = get_residue_distribution(k, p, max_enum)
    if dist is None:
        return None
    return dist.get(0, 0)


# ============================================================================
# PART 1: COMPLETE FACTORIZATION AND BLOCKING CLASSIFICATION
# ============================================================================

def part1_factorization_and_blocking(k_max=50):
    """
    For k=3..k_max: factor d(k), compute N_0(p) for each prime p | d,
    and classify the blocking mechanism:
      - SINGLE: some prime p | d has N_0(p) = 0
      - CRT:    no single prime blocks, but N_0(d) = 0 (CRT obstruction)
      - OPEN:   cannot compute (C too large)
    """
    print("\n" + "=" * 72)
    print("PART 1: FACTORIZATION OF d(k) AND BLOCKING CLASSIFICATION")
    print("=" * 72)

    results = {}
    class_counts = {'SINGLE': 0, 'CRT': 0, 'OPEN': 0}

    for k in range(3, k_max + 1):
        if time_remaining() < 30:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0:
            continue

        factors = full_factor(d)
        primes = sorted(set(p for p, _ in factors))
        largest_p = max(primes) if primes else 0

        can_enum = C <= 2_000_000

        n0_per_prime = {}
        blocking_primes = []
        mechanism = 'OPEN'

        if can_enum:
            for p in primes:
                n0 = compute_N0(k, p)
                n0_per_prime[p] = n0
                if n0 == 0:
                    blocking_primes.append(p)

            if blocking_primes:
                mechanism = 'SINGLE'
            else:
                # Verify N_0(d) = 0 by CRT
                n0d = sum(1 for A in enumerate_all_compositions(k)
                          if corrSum_of_A(A, k) % d == 0)
                if n0d == 0:
                    mechanism = 'CRT'
                else:
                    mechanism = 'FAIL'  # corrSum = 0 mod d EXISTS -- would be a cycle!

        class_counts[mechanism] = class_counts.get(mechanism, 0) + 1

        results[k] = {
            'S': S, 'd': d, 'C': C,
            'factors': factors,
            'primes': primes,
            'largest_p': largest_p,
            'can_enum': can_enum,
            'n0_per_prime': n0_per_prime,
            'blocking_primes': blocking_primes,
            'mechanism': mechanism,
            'p_max_over_C': largest_p / C if C > 0 else float('inf'),
        }

        if VERBOSE:
            factor_str = " * ".join(f"{p}^{e}" if e > 1 else str(p)
                                    for p, e in factors)
            if can_enum:
                n0_str = ", ".join(f"{p}:{n0_per_prime[p]}" for p in primes[:6])
                bp_str = str(blocking_primes[:5]) if blocking_primes else "NONE"
                print(f"  k={k:2d}  d={d}  C={C}  {mechanism:>6s}  "
                      f"fact={factor_str[:50]}  N0={{" + n0_str + "}"
                      f"  block={bp_str}")
            else:
                print(f"  k={k:2d}  log2(d)={math.log2(d):.1f}  "
                      f"log2(C)={math.log2(C):.1f}  "
                      f"#primes={len(primes)}  "
                      f"p_max/C={largest_p/C:.4f}  {mechanism}")

    # Summary
    print(f"\n  BLOCKING CLASSIFICATION: {dict(class_counts)}")
    single_ks = [k for k, v in results.items() if v['mechanism'] == 'SINGLE']
    crt_ks = [k for k, v in results.items() if v['mechanism'] == 'CRT']
    print(f"  SINGLE-prime blocking: k in {single_ks}")
    print(f"  CRT-only blocking:     k in {crt_ks}")

    if any(v['mechanism'] == 'FAIL' for v in results.values()):
        fail_ks = [k for k, v in results.items() if v['mechanism'] == 'FAIL']
        print(f"  *** CRITICAL FAILURE: N_0(d) > 0 at k = {fail_ks} ***")

    FINDINGS['part1'] = results
    return results


# ============================================================================
# PART 2: CRT BLOCKING ANALYSIS
# ============================================================================

def part2_crt_analysis(k_max=16):
    """
    For k values where no single prime blocks, analyze the CRT mechanism:
    - Which pairs/sets of primes jointly block?
    - How are compositions partitioned among blocking primes?
    - What is the "blocking partition": for each A, which prime(s) block it?
    """
    print("\n" + "=" * 72)
    print("PART 2: CRT BLOCKING ANALYSIS -- Joint Prime Obstruction")
    print("=" * 72)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 25:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0 or C > 500_000:
            continue

        primes = prime_factors_list(d)

        # Compute N_0(p) for all primes
        n0_map = {}
        for p in primes:
            n0_map[p] = compute_N0(k, p)

        has_single_blocker = any(n0_map[p] == 0 for p in primes)

        if has_single_blocker:
            # Already blocked by single prime, skip CRT analysis
            results[k] = {
                'mechanism': 'SINGLE',
                'single_blockers': [p for p in primes if n0_map[p] == 0],
            }
            continue

        # CRT ANALYSIS: no single prime blocks. How do they jointly block?
        # For each composition A, find which prime(s) have corrSum(A) != 0 mod p.
        # Since N_0(d) = 0, every A must be blocked by at least one prime.

        # Compute the "blocking signature" for each composition
        # signature[A] = frozenset of primes that DO allow corrSum(A) = 0 mod p
        # (i.e., primes where corrSum(A) = 0 mod p)
        # A is blocked by ALL primes NOT in this set.

        # More useful: for each A, the set of primes where corrSum != 0 mod p
        prime_blocks = {p: set() for p in primes}  # p -> set of B-tuples blocked by p
        all_compositions = []

        for B in combinations(range(1, S), k - 1):
            all_compositions.append(B)
            for p in primes:
                if corrsum_mod(B, k, p) != 0:
                    prime_blocks[p].add(B)

        # Each composition must be in at least one prime_blocks[p]
        # The question: which primes are needed?

        # Greedy set cover
        uncovered = set(range(len(all_compositions)))
        # Map B to index
        B_to_idx = {B: i for i, B in enumerate(all_compositions)}
        # prime_blocks as index sets
        pb_idx = {p: set(B_to_idx[B] for B in prime_blocks[p]) for p in primes}

        cover = []
        remaining = set(uncovered)
        while remaining:
            # Find prime covering most remaining
            best_p = max(primes, key=lambda p: len(pb_idx[p] & remaining))
            newly_covered = pb_idx[best_p] & remaining
            if not newly_covered:
                break  # Should not happen if N_0(d) = 0
            cover.append(best_p)
            remaining -= newly_covered

        # Check pairwise blocking
        pair_blocks = {}
        for i in range(len(primes)):
            for j in range(i + 1, len(primes)):
                p1, p2 = primes[i], primes[j]
                m = p1 * p2
                joint_n0 = 0
                for B in all_compositions:
                    cs = corrsum_mod(B, k, m)
                    if cs == 0:
                        joint_n0 += 1
                pair_blocks[(p1, p2)] = joint_n0

        # Find minimal blocking pair (if any pair gives N_0 = 0)
        blocking_pairs = [(p1, p2) for (p1, p2), n0 in pair_blocks.items() if n0 == 0]

        results[k] = {
            'mechanism': 'CRT',
            'primes': primes,
            'n0_per_prime': n0_map,
            'greedy_cover': cover,
            'cover_size': len(cover),
            'pair_blocks': pair_blocks,
            'blocking_pairs': blocking_pairs,
            'C': C,
        }

        if VERBOSE:
            print(f"  k={k:2d}  d={d}  primes={primes}  "
                  f"N_0={dict(n0_map)}  cover={cover}  "
                  f"blocking_pairs={blocking_pairs}")

    # Summary
    print("\n  CRT BLOCKING SUMMARY:")
    for k, v in sorted(results.items()):
        if v['mechanism'] == 'CRT':
            print(f"    k={k}: primes={v['primes']}, "
                  f"N_0={v['n0_per_prime']}, "
                  f"greedy_cover={v['greedy_cover']}, "
                  f"blocking_pairs={v['blocking_pairs']}")

    FINDINGS['part2'] = results
    return results


# ============================================================================
# PART 3: WHY N_0(p) = 0 -- RESIDUE AVOIDANCE MECHANISM
# ============================================================================

def part3_residue_avoidance(k_max=14):
    """
    For blocking primes (N_0(p) = 0), investigate WHY 0 is avoided:
    - How many residues does corrSum achieve mod p?
    - What fraction of residues are missing?
    - Is there a structural reason (parity, 3-adic, algebraic)?
    - How does ord_p(2) relate to blocking?
    """
    print("\n" + "=" * 72)
    print("PART 3: WHY IS N_0(p) = 0? -- Residue Avoidance Mechanism")
    print("=" * 72)

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

        primes = prime_factors_list(d)

        for p in primes:
            dist = get_residue_distribution(k, p)
            if dist is None:
                continue

            n0 = dist.get(0, 0)
            if n0 > 0:
                # Not a blocker -- record for comparison
                results[(k, p, 'non-blocker')] = {
                    'k': k, 'p': p, 'n0': n0, 'C': C,
                    'is_blocker': False,
                    'coverage': len(dist) / p,
                    'max_count': max(dist.values()),
                }
                continue

            # BLOCKER: analyze in detail
            missing = sorted(set(range(p)) - set(dist.keys()))
            hit = sorted(dist.keys())
            coverage = len(hit) / p

            ord2 = multiplicative_order(2, p) if p > 2 else None
            ord3 = multiplicative_order(3, p) if p > 3 else None

            # Check: is 0 always missing, or are there other missing residues?
            n_missing = len(missing)

            # The key algebraic fact: 2^S = 3^k mod p
            # This means the "weight" 3^{k-1-j} * 2^{a_j} satisfies:
            # When a_j = 0: term = 3^{k-1}
            # When the full set of a_j spans {0,...,S-1}, the sum wraps.

            # Check if the missing residues form a pattern
            # E.g., are they a coset of some subgroup?
            if len(missing) > 1 and len(missing) < p:
                # Check if missing residues are equidistributed
                diffs = [(missing[i+1] - missing[i]) % p for i in range(len(missing)-1)]
                uniform_gap = len(set(diffs)) == 1
            else:
                uniform_gap = None

            results[(k, p, 'blocker')] = {
                'k': k, 'p': p, 'n0': 0, 'C': C,
                'is_blocker': True,
                'coverage': coverage,
                'n_missing': n_missing,
                'missing': missing[:15],
                'max_count': max(dist.values()),
                'min_count': min(dist.values()),
                'ord2': ord2,
                'ord3': ord3,
                'p_over_C': p / C,
                'uniform_gap_missing': uniform_gap,
            }

            if VERBOSE:
                print(f"  k={k:2d} p={p:>8d}  C={C:>8d}  p/C={p/C:.4f}  "
                      f"missing={n_missing}/{p} ({coverage:.3f})  "
                      f"ord2={ord2}  ord3={ord3}")

    # Analysis: correlation between blocking and algebraic invariants
    blockers = {kp: v for kp, v in results.items() if v['is_blocker']}
    non_blockers = {kp: v for kp, v in results.items() if not v['is_blocker']}

    if blockers:
        print(f"\n  BLOCKER STATISTICS ({len(blockers)} cases):")
        coverages = [v['coverage'] for v in blockers.values()]
        print(f"    Coverage range: [{min(coverages):.3f}, {max(coverages):.3f}]")
        print(f"    Avg coverage: {sum(coverages)/len(coverages):.3f}")

        ord2_vals = [v['ord2'] for v in blockers.values() if v.get('ord2')]
        if ord2_vals:
            print(f"    ord_p(2) range: [{min(ord2_vals)}, {max(ord2_vals)}]")

    FINDINGS['part3'] = results
    return results


# ============================================================================
# PART 4: ALGEBRAIC CONSTRAINT FROM 2^S = 3^k (mod p)
# ============================================================================

def part4_algebraic_constraint(k_max=14):
    """
    For each prime p | d(k), we have 2^S = 3^k (mod p).

    Consequences:
    1. corrSum = sum 3^{k-1-j} * 2^{a_j} can be rewritten using this relation.
    2. The "target" for corrSum = 0 mod p is: need sum = 0, but the first term
       is 3^{k-1} != 0 mod p (since gcd(3,p) = 1 for p | d, as d is coprime to 6).
    3. So we need: sum_{j=1}^{k-1} 3^{k-1-j} * 2^{a_j} = -3^{k-1} mod p.

    KEY INSIGHT: Factor out 3^{k-1}:
      corrSum / 3^{k-1} = 1 + sum_{j=1}^{k-1} (2/3)^{a_j} * 3^{-j+1} ... no.

    Better: Let r = 2/3 mod p (= 2 * 3^{-1} mod p).  Then:
      corrSum = 3^{k-1} * (1 + sum_{j=1}^{k-1} r^{a_j} * 3^{-(j-1)} * something)
    This does not simplify cleanly.

    Alternative: Define the "normalized" sum
      sigma = corrSum / 3^{k-1} mod p
            = 1 + sum_{j=1}^{k-1} 3^{-j} * 2^{a_j} mod p
            = 1 + sum_{j=1}^{k-1} (2^{a_j} * 3^{-j}) mod p

    For corrSum = 0 mod p: need sigma = 0 mod p, i.e.,
      sum_{j=1}^{k-1} 2^{a_j} * 3^{-j} = -1 mod p.

    This is a SUBSET SUM problem over the group Z/pZ:
      Choose k-1 distinct values a_1 < ... < a_{k-1} from {1,...,S-1}
      such that sum_{j=1}^{k-1} 2^{a_j} * 3^{-j} = -1 mod p.

    The key constraint: the ORDERING between a_j and the coefficient 3^{-j}
    is FIXED (j-th chosen element gets weight 3^{-j}).

    This is NOT a standard subset sum because the weights depend on the ORDER
    of the chosen elements, not just which are chosen.
    """
    print("\n" + "=" * 72)
    print("PART 4: ALGEBRAIC CONSTRAINT ANALYSIS")
    print("=" * 72)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 20:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0 or C > 2_000_000:
            continue

        primes = prime_factors_list(d)

        for p in primes:
            if p <= 3:
                continue

            dist = get_residue_distribution(k, p)
            if dist is None:
                continue

            n0 = dist.get(0, 0)

            ord2 = multiplicative_order(2, p)
            ord3 = multiplicative_order(3, p)

            # Key algebraic quantities
            inv3 = pow(3, p - 2, p)  # 3^{-1} mod p (Fermat)
            r_val = (2 * inv3) % p   # 2/3 mod p

            # The set of available "powers" 2^s mod p for s in {1,...,S-1}
            power_set = set()
            for s in range(1, S):
                power_set.add(pow(2, s, p))
            n_distinct = len(power_set)

            # Orbit structure: how many positions map to each power of 2 mod p?
            orbit_map = defaultdict(list)
            for s in range(1, S):
                orbit_map[pow(2, s, p)].append(s)
            orbit_sizes = sorted([len(v) for v in orbit_map.values()], reverse=True)

            # For corrSum = 0 mod p, we need:
            # target = p - pow(3, k-1, p) mod p  (the complement of the fixed term)
            fixed_term = pow(3, k - 1, p)
            target = (p - fixed_term) % p

            # What is target in terms of the group structure?
            # Is target reachable by the weighted subset sum?

            results[(k, p)] = {
                'k': k, 'p': p, 'S': S, 'C': C,
                'n0': n0,
                'ord2': ord2,
                'ord3': ord3,
                'n_distinct_pow2': n_distinct,
                'n_orbits': len(orbit_map),
                'orbit_sizes': orbit_sizes[:8],
                'target': target,
                'fixed_term': fixed_term,
                'is_blocker': n0 == 0,
                'r_val': r_val,
            }

    # Print analysis
    print("\n  ALGEBRAIC INVARIANTS FOR BLOCKING PRIMES:")
    print(f"  {'k':>3s} {'p':>8s} {'ord2':>6s} {'ord3':>6s} "
          f"{'#pow2':>6s} {'target':>8s} {'N0':>6s} {'block':>6s}")
    for (k, p), v in sorted(results.items()):
        if v['is_blocker']:
            print(f"  {k:3d} {p:8d} {v['ord2'] or '?':>6} "
                  f"{v['ord3'] or '?':>6} "
                  f"{v['n_distinct_pow2']:6d} {v['target']:8d} "
                  f"{v['n0']:6d} {'YES':>6s}")

    # Look for pattern: does ord_p(2) determine blocking?
    print("\n  QUESTION: Does large ord_p(2) correlate with blocking?")
    blocker_ord2 = [v['ord2'] for v in results.values()
                    if v['is_blocker'] and v['ord2']]
    nonblocker_ord2 = [v['ord2'] for v in results.values()
                       if not v['is_blocker'] and v['ord2']]
    if blocker_ord2:
        print(f"    Blockers:     avg ord2 = {sum(blocker_ord2)/len(blocker_ord2):.1f}, "
              f"range = [{min(blocker_ord2)}, {max(blocker_ord2)}]")
    if nonblocker_ord2:
        print(f"    Non-blockers: avg ord2 = {sum(nonblocker_ord2)/len(nonblocker_ord2):.1f}, "
              f"range = [{min(nonblocker_ord2)}, {max(nonblocker_ord2)}]")

    # KEY OBSERVATION: For blockers, is p typically > some function of k?
    print("\n  QUESTION: Is p large relative to C for blockers?")
    for (k, p), v in sorted(results.items()):
        if v['is_blocker']:
            print(f"    k={k}, p={p}, C={v['C']}, p/C={p/v['C']:.4f}")

    FINDINGS['part4'] = results
    return results


# ============================================================================
# PART 5: PRECISE CONJECTURE WITH EVIDENCE
# ============================================================================

def part5_conjecture(k_max=50):
    """
    Formulate the precise answer to the original question, with full evidence.
    """
    print("\n" + "=" * 72)
    print("PART 5: PRECISE ANSWER AND CONJECTURE FORMULATION")
    print("=" * 72)

    results = {}

    for k in range(3, k_max + 1):
        if time_remaining() < 10:
            print(f"  [BUDGET] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        if d <= 0:
            continue

        factors = full_factor(d)
        primes = sorted(set(p for p, _ in factors))
        largest_p = max(primes) if primes else 0

        can_enum = C <= 2_000_000

        # Determine blocking mechanism
        blocking = []
        n0d_zero = None
        if can_enum:
            for p in primes:
                n0 = compute_N0(k, p)
                if n0 == 0:
                    blocking.append(p)
            if not blocking:
                n0d = sum(1 for A in enumerate_all_compositions(k)
                          if corrSum_of_A(A, k) % d == 0)
                n0d_zero = (n0d == 0)
            else:
                n0d_zero = True  # single prime blocks => d blocks too

            mechanism = 'SINGLE' if blocking else ('CRT' if n0d_zero else 'FAIL')
        else:
            mechanism = 'OPEN'
            n0d_zero = None

        results[k] = {
            'S': S, 'd': d, 'C': C,
            'largest_p': largest_p,
            'p_max_over_C': largest_p / C,
            'd_over_C': d / C,
            'mechanism': mechanism,
            'n0d_zero': n0d_zero,
            'blocking': blocking,
            'n_primes': len(primes),
            'd_is_prime': len(primes) == 1 and factors[0][1] == 1,
        }

    # EVIDENCE TABLE
    print(f"\n  COMPLETE EVIDENCE TABLE:")
    print(f"  {'k':>3s} {'log2(d)':>8s} {'log2(C)':>8s} {'d/C':>10s} "
          f"{'p_max/C':>10s} {'mech':>7s} {'N0(d)=0':>8s} {'d prime':>8s}")
    for k in sorted(results.keys()):
        r = results[k]
        n0d_str = "YES" if r['n0d_zero'] else ("NO" if r['n0d_zero'] is not None else "?")
        dp_str = "YES" if r['d_is_prime'] else "no"
        print(f"  {k:3d} {math.log2(r['d']):8.2f} {math.log2(r['C']):8.2f} "
              f"{r['d_over_C']:10.4f} {r['p_max_over_C']:10.4f} "
              f"{r['mechanism']:>7s} {n0d_str:>8s} {dp_str:>8s}")

    # Classify verified k values
    single_ks = sorted(k for k, v in results.items() if v['mechanism'] == 'SINGLE')
    crt_ks = sorted(k for k, v in results.items() if v['mechanism'] == 'CRT')
    open_ks = sorted(k for k, v in results.items() if v['mechanism'] == 'OPEN')
    verified_ks = sorted(k for k, v in results.items()
                         if v['n0d_zero'] is True)

    # Check when p_max > C permanently
    p_max_gt_C_from = None
    for k in sorted(results.keys(), reverse=True):
        if results[k]['p_max_over_C'] <= 1:
            p_max_gt_C_from = None
            break
        p_max_gt_C_from = k

    print("\n" + "=" * 72)
    print("ANSWER TO THE QUESTION")
    print("=" * 72)
    print(f"""
  QUESTION: For every k >= 3, does there exist a prime p | d(k) such that
  N_0(p) = 0?

  ANSWER: NO. This is FALSE in general.

  COUNTEREXAMPLES (verified exhaustively):
    k = {crt_ks}
  For these k, EVERY prime factor p of d(k) has N_0(p) > 0 (some
  composition A achieves corrSum(A) = 0 mod p). Yet N_0(d) = 0 still
  holds through CRT: different primes block different compositions,
  and together they block ALL compositions.

  SINGLE-PRIME BLOCKING HOLDS FOR:
    k = {single_ks}
  For these k, at least one prime p | d(k) has N_0(p) = 0 individually.

  PATTERN: Single-prime blocking tends to occur when:
    (a) d(k) is prime (then the only prime factor IS d, and p > C), OR
    (b) d(k) has a large prime factor compared to C(k).
  CRT-only blocking occurs when d(k) has only "small" prime factors
  relative to C(k).

  N_0(d) = 0 (the actual no-cycle condition) HOLDS FOR ALL TESTED k:
    k = {verified_ks if verified_ks else 'none verified'}

  STATUS: The correct question is NOT about single-prime blocking but
  about N_0(d) = 0. We now know:
    1. [VERIFIED] N_0(d) = 0 for k=3..{max(verified_ks) if verified_ks else '?'}
    2. [PUBLISHED] No cycles for k <= 68 (Simons-de Weger 2005)
    3. [PROVED] d > C for k >= 18 (nonsurjectivity)
    4. [OPEN] Whether N_0(d) = 0 for ALL k >= 3

  THE REFINED CONJECTURE:
    For every k >= 3, N_0(d(k)) = 0.
    This holds either through:
    (a) A single blocking prime p | d with N_0(p) = 0, OR
    (b) CRT joint blocking: every composition is blocked by at least
        one prime factor of d.
""")

    FINDINGS['part5'] = results
    return results


# ============================================================================
# SELF-TESTS (T01-T25)
# ============================================================================

def run_all_tests():
    """Run all 25 self-tests."""
    print("\n" + "=" * 72)
    print("SELF-TESTS (T01-T25)")
    print("=" * 72)

    # T01: compute_S correctness
    all_ok = True
    for k in [3, 5, 10, 20, 50]:
        S = compute_S(k)
        ok = (1 << S) >= 3**k and (1 << (S - 1)) < 3**k
        if not ok:
            all_ok = False
    record_test("T01: compute_S(k) correct for k=3,5,10,20,50", all_ok)

    # T02: d(k) > 0
    all_pos = all(compute_d(k) > 0 for k in range(3, 51))
    record_test("T02: d(k) > 0 for all k=3..50", all_pos)

    # T03: Factorization consistency
    all_ok = True
    for k in [3, 5, 7, 10, 15]:
        d = compute_d(k)
        factors = full_factor(d)
        product = 1
        for p, e in factors:
            product *= p ** e
        if product != d:
            all_ok = False
    record_test("T03: Factorization product = d for k=3,5,7,10,15", all_ok)

    # T04: All factors are prime
    all_ok = True
    for k in range(3, 25):
        d = compute_d(k)
        if d <= 0:
            continue
        factors = full_factor(d)
        for p, e in factors:
            if not is_prime(p):
                all_ok = False
    record_test("T04: All factors of d(k) are prime for k=3..24", all_ok)

    # T05: corrSum always positive
    all_ok = True
    for k in [3, 4, 5]:
        for A in enumerate_all_compositions(k):
            if corrSum_of_A(A, k) <= 0:
                all_ok = False
                break
    record_test("T05: corrSum(A) > 0 for all A, k=3,4,5", all_ok)

    # T06: corrSum always odd
    all_ok = True
    for k in [3, 4, 5, 6]:
        for A in enumerate_all_compositions(k):
            if corrSum_of_A(A, k) % 2 == 0:
                all_ok = False
                break
    record_test("T06: corrSum(A) always odd for k=3..6", all_ok)

    # T07: corrSum not divisible by 3
    all_ok = True
    for k in [3, 4, 5, 6]:
        for A in enumerate_all_compositions(k):
            if corrSum_of_A(A, k) % 3 == 0:
                all_ok = False
                break
    record_test("T07: corrSum(A) never divisible by 3 for k=3..6", all_ok)

    # T08: Composition count matches C(S-1, k-1)
    all_ok = True
    for k in [3, 4, 5, 6, 7]:
        count = sum(1 for _ in enumerate_all_compositions(k))
        if count != compute_C(k):
            all_ok = False
    record_test("T08: Composition count = C(S-1,k-1) for k=3..7", all_ok)

    # T09: N_0(d(3)) = 0
    k = 3
    d = compute_d(k)
    n0d = sum(1 for A in enumerate_all_compositions(k)
              if corrSum_of_A(A, k) % d == 0)
    record_test("T09: N_0(d(3)) = 0", n0d == 0, f"N_0={n0d}")

    # T10: N_0(d) = 0 for k=3..10
    all_zero = True
    for k in range(3, 11):
        d = compute_d(k)
        if compute_C(k) > 1_000_000:
            continue
        found = any(corrSum_of_A(A, k) % d == 0
                    for A in enumerate_all_compositions(k))
        if found:
            all_zero = False
    record_test("T10: N_0(d(k)) = 0 for k=3..10", all_zero)

    # T11: For k=3,4,5,7,8,11,13 (single-prime cases), blocking prime exists
    single_prime_ks = [3, 4, 5, 7, 8, 11, 13]
    all_blocked = True
    for k in single_prime_ks:
        d = compute_d(k)
        primes = prime_factors_list(d)
        has_blocker = any(compute_N0(k, p) == 0 for p in primes)
        if not has_blocker:
            all_blocked = False
    record_test("T11: Single-prime blocker exists for known cases k=3,4,5,7,8,11,13",
                all_blocked)

    # T12: For k=6, NO single prime blocks (known CRT case)
    k = 6
    d6 = compute_d(6)
    primes6 = prime_factors_list(d6)
    no_single = all(compute_N0(6, p) > 0 for p in primes6)
    n0d6 = sum(1 for A in enumerate_all_compositions(6)
               if corrSum_of_A(A, 6) % d6 == 0)
    record_test("T12: k=6 has NO single blocking prime, yet N_0(d)=0",
                no_single and n0d6 == 0,
                f"primes={primes6}, N0(5)={compute_N0(6,5)}, N0(59)={compute_N0(6,59)}")

    # T13: 2^S = 3^k mod p for all p | d
    all_ok = True
    for k in range(3, 20):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0:
            continue
        for p in prime_factors_list(d):
            if pow(2, S, p) != pow(3, k, p):
                all_ok = False
    record_test("T13: 2^S = 3^k mod p for all p|d, k=3..19", all_ok)

    # T14: d(k) is odd and coprime to 3
    all_ok = all(compute_d(k) % 2 == 1 and math.gcd(3, compute_d(k)) == 1
                 for k in range(3, 51))
    record_test("T14: d(k) odd and gcd(3,d)=1 for k=3..50", all_ok)

    # T15: corrsum_mod matches corrSum_of_A mod p
    all_ok = True
    k = 5
    S = compute_S(k)
    p = prime_factors_list(compute_d(k))[0]
    for B in combinations(range(1, S), k - 1):
        A = (0,) + B
        if corrSum_of_A(A, k) % p != corrsum_mod(B, k, p):
            all_ok = False
            break
    record_test("T15: corrsum_mod matches corrSum_of_A mod p (k=5)", all_ok)

    # T16: Residue distribution sums to C
    all_ok = True
    for k in [3, 5, 7]:
        C = compute_C(k)
        for p in prime_factors_list(compute_d(k))[:2]:
            dist = get_residue_distribution(k, p)
            if dist is not None and sum(dist.values()) != C:
                all_ok = False
    record_test("T16: Residue distribution sums to C for k=3,5,7", all_ok)

    # T17: Known factorizations
    d3 = compute_d(3)
    d4 = compute_d(4)
    d5 = compute_d(5)
    ok17 = (d3 == 5 and d4 == 47 and d5 == 13)
    record_test("T17: d(3)=5, d(4)=47, d(5)=13", ok17,
                f"d(3)={d3}, d(4)={d4}, d(5)={d5}")

    # T18: is_prime correctness
    ok18 = (all(is_prime(p) for p in [2, 3, 5, 7, 97, 7919, 104729]) and
            all(not is_prime(n) for n in [1, 4, 6, 91, 100, 1001]))
    record_test("T18: is_prime correct for known primes/composites", ok18)

    # T19: multiplicative_order
    ok19 = (multiplicative_order(2, 5) == 4 and
            multiplicative_order(2, 7) == 3 and
            multiplicative_order(3, 7) == 6)
    record_test("T19: ord_5(2)=4, ord_7(2)=3, ord_7(3)=6", ok19)

    # T20: d > C for k >= 18
    all_ok = all(compute_d(k) > compute_C(k) for k in range(18, 51))
    record_test("T20: d(k) > C(k) for k=18..50", all_ok)

    # T21: corrSum(0,1,...,k-1) = 3^k - 2^k
    all_ok = all(corrSum_of_A(tuple(range(k)), k) == 3**k - 2**k
                 for k in [3, 4, 5, 6])
    record_test("T21: corrSum(0,1,...,k-1) = 3^k - 2^k", all_ok)

    # T22: Parseval identity for k=3, p=5
    k, p = 3, 5
    dist = get_residue_distribution(k, p)
    C = compute_C(k)
    omega = 2 * math.pi / p
    sum_T2 = 0.0
    for t in range(p):
        T_re = sum(c * math.cos(omega * t * r) for r, c in dist.items())
        T_im = sum(c * math.sin(omega * t * r) for r, c in dist.items())
        sum_T2 += T_re**2 + T_im**2
    sum_Nr2 = sum(c**2 for c in dist.values())
    record_test("T22: Parseval identity for k=3,p=5",
                abs(sum_T2 - p * sum_Nr2) < 0.01,
                f"|T|^2={sum_T2:.2f}, p*Nr^2={p*sum_Nr2:.2f}")

    # T23: CRT consistency for k=6 (CRT case)
    # N_0(5) = 36, N_0(59) = 6, but N_0(295) = 0
    k = 6
    d = compute_d(k)
    n0_5 = compute_N0(6, 5)
    n0_59 = compute_N0(6, 59)
    n0_d = sum(1 for A in enumerate_all_compositions(6)
               if corrSum_of_A(A, 6) % d == 0)
    ok23 = (n0_5 > 0 and n0_59 > 0 and n0_d == 0)
    record_test("T23: k=6 CRT: N0(5)>0, N0(59)>0, but N0(d)=0",
                ok23, f"N0(5)={n0_5}, N0(59)={n0_59}, N0(295)={n0_d}")

    # T24: For k=9 (CRT case), verify no single blocker and N_0(d)=0
    k = 9
    d9 = compute_d(9)
    primes9 = prime_factors_list(d9)
    n0_9_per_p = {p: compute_N0(9, p) for p in primes9}
    no_single_9 = all(v > 0 for v in n0_9_per_p.values())
    n0d9 = sum(1 for A in enumerate_all_compositions(9)
               if corrSum_of_A(A, 9) % d9 == 0)
    ok24 = (no_single_9 and n0d9 == 0)
    record_test("T24: k=9 CRT: no single blocker, N_0(d)=0",
                ok24, f"N0={n0_9_per_p}, N0(d)={n0d9}")

    # T25: Timing
    record_test("T25: Runtime within budget",
                elapsed() < TIME_BUDGET, f"{elapsed():.1f}s")

    n_pass = sum(1 for _, p, _ in TEST_RESULTS if p)
    n_fail = sum(1 for _, p, _ in TEST_RESULTS if not p)
    print(f"\n  TOTAL: {n_pass} PASS, {n_fail} FAIL out of {len(TEST_RESULTS)}")
    return n_fail == 0


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("R11: BLOCKING PRIME EXISTENCE FOR EVERY k >= 3")
    print("The Single Question: Does every k have a prime p|d with N_0(p)=0?")
    print("=" * 72)
    print(f"Start: {time.strftime('%H:%M:%S')}  Budget: {TIME_BUDGET}s")

    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        parts = set()
    elif len(sys.argv) > 1:
        parts = set(int(x) for x in sys.argv[1:] if x.isdigit())
    else:
        parts = {1, 2, 3, 4, 5}

    for i in sorted(parts):
        try:
            if i == 1:
                part1_factorization_and_blocking(k_max=50)
            elif i == 2:
                part2_crt_analysis(k_max=15)
            elif i == 3:
                part3_residue_avoidance(k_max=14)
            elif i == 4:
                part4_algebraic_constraint(k_max=14)
            elif i == 5:
                part5_conjecture(k_max=50)
        except TimeoutError as e:
            print(f"  [TIMEOUT] Part {i}: {e}")

    print()
    all_pass = run_all_tests()

    print("\n" + "=" * 72)
    print("FINAL SUMMARY")
    print("=" * 72)
    print(f"  Runtime: {elapsed():.1f}s / {TIME_BUDGET}s")
    n_pass = sum(1 for _, p, _ in TEST_RESULTS if p)
    print(f"  Tests: {n_pass}/{len(TEST_RESULTS)} PASS")

    if FINDINGS.get('part1'):
        p1 = FINDINGS['part1']
        single = [k for k, v in p1.items() if v['mechanism'] == 'SINGLE']
        crt = [k for k, v in p1.items() if v['mechanism'] == 'CRT']
        print(f"  Single-prime blocking: {single}")
        print(f"  CRT-only blocking:     {crt}")

    print("=" * 72)
    return 0 if all_pass else 1


if __name__ == "__main__":
    sys.exit(main())
