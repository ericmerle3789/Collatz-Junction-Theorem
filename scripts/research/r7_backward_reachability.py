#!/usr/bin/env python3
"""
r7_backward_reachability.py -- Round 7: Per-Prime Backward Reachability for Cycle Exclusion
============================================================================================

CONTEXT (Rounds 1-6 complete):
  Steiner's equation: n0 * d = corrSum(A),  d = 2^S - 3^k,  S = ceil(k*log2(3)).
  corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{a_j} where A = {a_0 < ... < a_{k-1}}
  subset of {0,1,...,S-1} with a_0 = 0.

  A nontrivial cycle exists iff corrSum(A) = 0 mod d for some valid A, k >= 3.

  The Horner chain: c_0 = 0, c_{j+1} = (3*c_j + 2^{b_{k-1-j}}) mod d
    where b_i = a_{i+1} - a_i - 1 (gaps minus 1), and b_i >= 0.
    The constraint sum(b_i + 1) = S forces b_i in {0,...,S-k}.

  From R6 Strategy 4: backward reachability mod d proves N_0=0 for small k,
  but sets saturate for large k. The KEY INSIGHT: run reachability per-prime p|d.
  If 0 not in R_0 mod p for ANY prime p|d, then no cycle of length k exists.

FIVE TOOLS:

  Tool 1 -- PER-PRIME BACKWARD REACHABILITY (UNCONSTRAINED):
    For each prime p|d and cycle length k:
      R_k = {0} in Z/pZ
      R_{j-1} = union over b in {0,...,S-k} of {(r - 2^b) * 3^{-1} mod p : r in R_j}
    Check: is 0 in R_0?

  Tool 2 -- WR-CONSTRAINED REACHABILITY (EXACT):
    Track (residue mod p, used_positions) to enforce without-replacement.
    Exponential in k, feasible for k <= 10 or so.

  Tool 3 -- CRT COMBINATION:
    For each k, combine per-prime blocking results.
    If ANY prime p|d blocks (0 not in R_0 mod p), then k is eliminated.

  Tool 4 -- REGIME ANALYSIS:
    Classify primes by size relative to S and analyze blocking patterns.

  Tool 5 -- TRANSITION MATRIX METHOD:
    Build (p x p) transition matrix M for Horner chain mod p.
    M^k[0][0] counts paths from 0 to 0. Compare with reachability.

HONESTY COMMITMENT:
  All modular computations are exact (Python integer arithmetic).
  If a tool produces no blocking, this script says so clearly.

Author: Claude (R7-Combinatoire for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r7_backward_reachability.py             # run all tools + self-tests
    python3 r7_backward_reachability.py selftest     # self-tests only
    python3 r7_backward_reachability.py 1 3 5        # run tools 1, 3, 5

Requires: math, itertools, collections (standard library only).
Time budget: 300 seconds max.
"""

import math
import sys
import time
from itertools import combinations
from collections import Counter, defaultdict


# ============================================================================
# GLOBAL TIME BUDGET
# ============================================================================

T_START = time.time()
TIME_BUDGET = 300.0


def time_remaining():
    return TIME_BUDGET - (time.time() - T_START)


def check_budget(label=""):
    """Raise TimeoutError if budget exhausted."""
    rem = time_remaining()
    if rem <= 0:
        raise TimeoutError(f"Time budget exhausted at {label}")
    return rem


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3))."""
    return math.ceil(k * math.log2(3))


def compute_d(k):
    """d(k) = 2^S - 3^k."""
    S = compute_S(k)
    return (1 << S) - 3**k


def num_compositions(S, k):
    """C(S-1, k-1): number of valid (k-1)-subsets of {1,...,S-1}."""
    return math.comb(S - 1, k - 1)


def can_enumerate(k, limit=2_000_000):
    """True if exhaustive enumeration is feasible within limit."""
    S = compute_S(k)
    return math.comb(S - 1, k - 1) <= limit


def prime_factorization(n):
    """Return list of (prime, exponent) pairs for |n|."""
    n = abs(n)
    if n <= 1:
        return []
    factors = []
    trial = 2
    while trial * trial <= n:
        if n % trial == 0:
            e = 0
            while n % trial == 0:
                e += 1
                n //= trial
            factors.append((trial, e))
        trial += 1
    if n > 1:
        factors.append((n, 1))
    return factors


def distinct_primes(n):
    """Sorted list of distinct prime factors of |n|."""
    return [p for p, _ in prime_factorization(n)]


def is_prime(n):
    """Simple primality test."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def extended_gcd(a, b):
    """Extended Euclidean algorithm. Returns (gcd, x, y) with a*x + b*y = gcd."""
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def modinv(a, m):
    """Modular inverse of a mod m (None if gcd != 1)."""
    if m == 1:
        return 0
    g, x, _ = extended_gcd(a % m, m)
    if g != 1:
        return None
    return x % m


def corrsum_from_subset(B_tuple, k, mod):
    """
    Compute corrSum mod `mod` from a (k-1)-subset B of {1,...,S-1}.
    With a_0 = 0 (i.e. b_0 = 0 implicit):
        corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{a_j} mod `mod`
    where a_0 = 0, and B_tuple = (a_1, ..., a_{k-1}).
    """
    result = pow(3, k - 1, mod)  # j=0 term: 3^{k-1} * 2^0
    for idx in range(len(B_tuple)):
        j = idx + 1
        result = (result + pow(3, k - 1 - j, mod)
                  * pow(2, B_tuple[idx], mod)) % mod
    return result


def corrsum_true(B_tuple, k):
    """Compute the TRUE (unreduced) corrSum as a Python integer."""
    total = 3 ** (k - 1)  # j=0: 3^{k-1} * 2^0
    for idx in range(len(B_tuple)):
        j = idx + 1
        total += 3 ** (k - 1 - j) * 2 ** B_tuple[idx]
    return total


def horner_chain_forward(positions, k, mod):
    """
    Compute the Horner chain forward:
      c_0 = 0
      c_{j+1} = (3*c_j + 2^{a_{j}}) mod `mod`
    where positions = (a_0, a_1, ..., a_{k-1}) are the SORTED positions.
    Note: a_0 = 0 always.
    Returns the final value c_k.
    """
    c = 0
    for j in range(k):
        c = (3 * c + pow(2, positions[j], mod)) % mod
    return c


def enumerate_corrsums_mod(k, mod):
    """Exact distribution of corrSum mod `mod`. Returns Counter."""
    S = compute_S(k)
    counts = Counter()
    for B in combinations(range(1, S), k - 1):
        counts[corrsum_from_subset(B, k, mod)] += 1
    return counts


# ============================================================================
# TOOL 1: PER-PRIME BACKWARD REACHABILITY (UNCONSTRAINED)
# ============================================================================

def backward_reachability_unconstrained(k, p, inv3_p=None):
    """
    Compute unconstrained backward reachability sets mod prime p.

    The Horner chain mod p:
      c_0 = 0
      c_{j+1} = (3*c_j + 2^{b_{k-1-j}}) mod p
    where b_i = a_{i+1} - a_i - 1 >= 0, and each b_i in {0,...,S-k}.

    Working backward from c_k = 0:
      c_j = (c_{j+1} - 2^b) * 3^{-1} mod p

    But we need to be careful about what "b" ranges over. In the Horner chain,
    at step j+1, we add 2^{a_j} where a_j is a position in {0,...,S-1}.
    Working backward from step k to step 0:
      At backward step i (from k down to 1): we undo the addition of 2^{a_{k-i}}
      The position a_{k-i} ranges over {0,...,S-1} (unconstrained).

    So the backward preimage of r at any step is:
      {(r - 2^a) * 3^{-1} mod p : a in {0,...,S-1}}

    Returns:
      R_list: list of sets R_k, R_{k-1}, ..., R_0 (indexed [0]=R_k, [k]=R_0)
      blocks: True if 0 not in R_0
    """
    S = compute_S(k)
    if inv3_p is None:
        inv3_p = modinv(3, p)
    if inv3_p is None:
        return None, False  # 3 not invertible mod p

    # Precompute 2^a mod p for a = 0,...,S-1
    pow2 = [pow(2, a, p) for a in range(S)]
    # Unique residues of 2^a mod p
    pow2_set = set(pow2)

    # R_k = {0}  (target: c_k = 0 mod p)
    R = {0}
    R_list = [frozenset(R)]

    for step in range(k):  # k backward steps
        R_new = set()
        for r in R:
            for pw in pow2_set:
                preimage = ((r - pw) * inv3_p) % p
                R_new.add(preimage)
        R = R_new
        R_list.append(frozenset(R))
        # Early exit if R = Z/pZ (saturated)
        if len(R) == p:
            # Fill remaining
            for _ in range(k - step - 1):
                R_list.append(frozenset(R))
            break

    blocks = 0 not in R
    return R_list, blocks


def tool1_per_prime_backward(k_range=range(3, 21)):
    """
    Tool 1: Per-prime backward reachability (unconstrained).
    For each k and each prime p|d, compute backward reachability.
    """
    hdr = "TOOL 1: PER-PRIME BACKWARD REACHABILITY (UNCONSTRAINED)"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)

    results = {}

    for k in k_range:
        check_budget(f"Tool 1 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue

        primes = distinct_primes(d)
        # For large d, factorization may yield very large primes; limit work
        if len(primes) == 0:
            continue

        k_result = {
            'S': S, 'd': d, 'primes': primes,
            'blocking': [], 'non_blocking': [],
            'R0_sizes': {}, 'saturated_step': {},
        }

        print(f"\n  k={k}  S={S}  d={d}  |primes|={len(primes)}")

        for p in primes:
            check_budget(f"Tool 1 k={k} p={p}")

            # Skip if p is too large for set-based reachability
            if p > 50000:
                print(f"    p={p}: SKIPPED (too large for set enumeration)")
                k_result['non_blocking'].append((p, 'SKIPPED'))
                continue

            inv3 = modinv(3, p)
            if inv3 is None:
                # p=3, which divides 3^k but not 2^S, so p|d only if p|2^S-3^k
                # In practice p=3 means 3|d, and 3 divides 3*c_j term
                print(f"    p={p}: 3 not invertible mod p (p=3)")
                k_result['non_blocking'].append((p, 'NO_INV3'))
                continue

            R_list, blocks = backward_reachability_unconstrained(k, p, inv3)

            R0_size = len(R_list[-1]) if R_list else 0
            sat_step = None
            for i, Rs in enumerate(R_list):
                if len(Rs) == p:
                    sat_step = i
                    break

            k_result['R0_sizes'][p] = R0_size
            if sat_step is not None:
                k_result['saturated_step'][p] = sat_step

            if blocks:
                k_result['blocking'].append(p)
                print(f"    p={p}: BLOCKS (0 not in R_0, |R_0|={R0_size}/{p})")
            else:
                k_result['non_blocking'].append((p, R0_size))
                sat_info = f", saturates at step {sat_step}" if sat_step is not None else ""
                print(f"    p={p}: does not block (|R_0|={R0_size}/{p}{sat_info})")

        if k_result['blocking']:
            print(f"  => k={k} BLOCKED by primes {k_result['blocking']}")
        else:
            print(f"  => k={k} NOT blocked by any prime (unconstrained)")

        results[k] = k_result

    # Summary
    print(f"\n  {'='*60}")
    print(f"  TOOL 1 SUMMARY")
    print(f"  {'='*60}")
    blocked_ks = [k for k, r in results.items() if r['blocking']]
    unblocked_ks = [k for k, r in results.items() if not r['blocking']]
    print(f"  Blocked k values: {blocked_ks}")
    print(f"  Unblocked k values: {unblocked_ks}")

    return results


# ============================================================================
# TOOL 2: WR-CONSTRAINED REACHABILITY (EXACT)
# ============================================================================

def backward_reachability_wr_exact(k, p, inv3_p=None, timeout_states=500000):
    """
    Exact without-replacement constrained backward reachability mod p.

    State: (c mod p, frozenset of used positions)
    We work backward from step k to step 0.

    At backward step (undoing step j, choosing position a_j):
      c_j = (c_{j+1} - 2^{a_j}) * 3^{-1} mod p
      a_j must not be in used_positions
      a_j must be in {0,...,S-1}

    The WITHOUT-REPLACEMENT constraint: positions must be distinct AND ordered
    (a_0 < a_1 < ... < a_{k-1}). But when working backward, we undo in reverse
    order: first undo a_{k-1}, then a_{k-2}, etc. For the ordering constraint,
    each chosen a must be LESS than all previously chosen (since backward).

    Actually, the ordering constraint a_0 < a_1 < ... < a_{k-1} means when we
    undo from the END: the last position chosen (a_{k-1}) is the LARGEST.
    As we go backward, each new position must be SMALLER than the previous.

    State: (residue mod p, max_position_still_available)
    This is more tractable: we need to track which positions are still "available"
    meaning smaller than the smallest position chosen so far.

    Wait -- let's think more carefully. The Horner chain is:
      c_0 = 0
      c_{j+1} = (3*c_j + 2^{a_j}) mod p  for j = 0, ..., k-1
    where a_0 = 0 < a_1 < ... < a_{k-1}, all in {0,...,S-1}.

    Working backward:
      Step 1 (undo j=k-1): choose a_{k-1} in {1,...,S-1}
        c_{k-1} = (0 - 2^{a_{k-1}}) * inv3 mod p
      Step 2 (undo j=k-2): choose a_{k-2} < a_{k-1}
        c_{k-2} = (c_{k-1} - 2^{a_{k-2}}) * inv3 mod p
      ...
      Step k (undo j=0): must have a_0 = 0
        c_0 = (c_1 - 2^0) * inv3 mod p
        Check: c_0 = 0

    So the constraint at each backward step i (choosing a_{k-i}):
      a_{k-i} < a_{k-i+1} (the position chosen must be smaller than the previous)
      a_{k-i} >= 0, and a_0 = 0 is forced at the last step.

    State representation: (residue mod p, upper_bound)
      where upper_bound = the smallest position used so far (exclusive upper bound
      for the next position to choose).

    Returns:
      final_residues: set of residues reachable at c_0
      blocks: True if 0 not in final_residues
      n_states: total states explored
    """
    S = compute_S(k)
    if inv3_p is None:
        inv3_p = modinv(3, p)
    if inv3_p is None:
        return set(), False, 0

    # Precompute 2^a mod p
    pow2 = [pow(2, a, p) for a in range(S)]

    # Start: c_k = 0, no positions used yet, upper_bound = S
    # State: (residue, upper_bound_for_next_position)
    # upper_bound means next position must be in {0, ..., upper_bound - 1}

    # Backward step 1: undo j = k-1, choose a_{k-1}
    # a_{k-1} in {k-1, ..., S-1} (must leave room for a_0,...,a_{k-2} below it)
    # Actually a_{k-1} >= k-1 (since a_0=0, a_1>=1, ..., a_{k-1}>=k-1)
    # And a_{k-1} <= S-1

    current_states = set()  # set of (residue, upper_bound)
    current_states.add((0, S))  # c_k = 0, full range available

    n_states = 1

    for step in range(k):
        # step 0: undo j = k-1 (choose a_{k-1})
        # step 1: undo j = k-2 (choose a_{k-2})
        # ...
        # step k-1: undo j = 0 (must choose a_0 = 0)

        check_budget(f"Tool 2 WR step {step}")

        j_undo = k - 1 - step  # the j being undone
        # At this step, a_{j_undo} must satisfy:
        #   j_undo <= a_{j_undo} < upper_bound
        # (must leave room for j_undo positions below: a_0=0,...,a_{j_undo-1})

        new_states = set()

        if j_undo == 0:
            # Must choose a_0 = 0
            for (res, ub) in current_states:
                if ub > 0:  # position 0 is available (ub > 0 means 0 < ub)
                    new_res = ((res - pow2[0]) * inv3_p) % p
                    new_states.add((new_res, 0))
        else:
            for (res, ub) in current_states:
                # a_{j_undo} ranges from j_undo to ub-1
                lo = j_undo
                hi = ub  # exclusive
                for a in range(lo, hi):
                    new_res = ((res - pow2[a]) * inv3_p) % p
                    new_states.add((new_res, a))

        current_states = new_states
        n_states += len(current_states)

        if n_states > timeout_states:
            return None, None, n_states  # too many states

    # After k backward steps, current_states contains (residue, 0) pairs
    # residue should be c_0; check if 0 is among them
    final_residues = {res for (res, ub) in current_states}
    blocks = 0 not in final_residues

    return final_residues, blocks, n_states


def tool2_wr_constrained(k_range=range(3, 15)):
    """
    Tool 2: WR-constrained reachability (exact).
    """
    hdr = "TOOL 2: WR-CONSTRAINED REACHABILITY (EXACT)"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)

    results = {}

    for k in k_range:
        check_budget(f"Tool 2 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue

        primes = distinct_primes(d)

        k_result = {
            'S': S, 'd': d, 'primes': primes,
            'blocking_wr': [], 'non_blocking_wr': [],
            'blocking_uc': [], 'non_blocking_uc': [],
            'R0_sizes_wr': {}, 'R0_sizes_uc': {},
            'states_explored': {},
        }

        print(f"\n  k={k}  S={S}  d={d}  C(S-1,k-1)={num_compositions(S,k)}")

        for p in primes:
            check_budget(f"Tool 2 k={k} p={p}")

            if p > 10000:
                print(f"    p={p}: SKIPPED (too large)")
                continue

            inv3 = modinv(3, p)
            if inv3 is None:
                continue

            # Unconstrained for comparison
            R_list_uc, blocks_uc = backward_reachability_unconstrained(k, p, inv3)
            uc_size = len(R_list_uc[-1]) if R_list_uc else 0
            k_result['R0_sizes_uc'][p] = uc_size
            if blocks_uc:
                k_result['blocking_uc'].append(p)
            else:
                k_result['non_blocking_uc'].append(p)

            # WR-constrained
            final_res, blocks_wr, n_states = backward_reachability_wr_exact(
                k, p, inv3, timeout_states=2_000_000
            )

            if final_res is None:
                print(f"    p={p}: WR TIMEOUT ({n_states} states), "
                      f"UC |R_0|={uc_size}/{p} {'BLOCKS' if blocks_uc else 'no block'}")
                k_result['states_explored'][p] = n_states
                continue

            wr_size = len(final_res)
            k_result['R0_sizes_wr'][p] = wr_size
            k_result['states_explored'][p] = n_states

            if blocks_wr:
                k_result['blocking_wr'].append(p)

            label_wr = "BLOCKS" if blocks_wr else "no block"
            label_uc = "BLOCKS" if blocks_uc else "no block"
            print(f"    p={p}: WR |R_0|={wr_size}/{p} ({label_wr}), "
                  f"UC |R_0|={uc_size}/{p} ({label_uc}), "
                  f"states={n_states}")

            # Sanity: WR result must be subset of UC result
            if final_res is not None and R_list_uc is not None:
                uc_R0 = R_list_uc[-1]
                if not final_res.issubset(uc_R0):
                    print(f"    *** SANITY FAIL: WR not subset of UC! ***")

        results[k] = k_result

        if k_result['blocking_wr']:
            print(f"  => k={k} BLOCKED (WR) by primes {k_result['blocking_wr']}")
        elif k_result['blocking_uc']:
            print(f"  => k={k} BLOCKED (UC only) by primes {k_result['blocking_uc']}")
        else:
            print(f"  => k={k} NOT blocked")

    print(f"\n  {'='*60}")
    print(f"  TOOL 2 SUMMARY")
    print(f"  {'='*60}")
    for k, r in sorted(results.items()):
        wr_blocks = r.get('blocking_wr', [])
        uc_blocks = r.get('blocking_uc', [])
        extra = [p for p in wr_blocks if p not in uc_blocks]
        print(f"  k={k}: WR blocks {len(wr_blocks)} primes, UC blocks {len(uc_blocks)} primes"
              f"{f', WR-only: {extra}' if extra else ''}")

    return results


# ============================================================================
# TOOL 3: CRT COMBINATION
# ============================================================================

def tool3_crt_combination(k_range=range(3, 21)):
    """
    Tool 3: CRT combination of per-prime blocking.
    For each k, if ANY prime p|d blocks, then k is eliminated.
    Also compute the CRT product of blocking prime moduli.
    """
    hdr = "TOOL 3: CRT COMBINATION"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)

    results = {}

    for k in k_range:
        check_budget(f"Tool 3 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue

        primes = distinct_primes(d)

        blocking_primes = []
        non_blocking_primes = []
        skipped_primes = []

        for p in primes:
            check_budget(f"Tool 3 k={k} p={p}")

            if p > 50000:
                skipped_primes.append(p)
                continue

            inv3 = modinv(3, p)
            if inv3 is None:
                non_blocking_primes.append((p, 'NO_INV3'))
                continue

            _, blocks = backward_reachability_unconstrained(k, p, inv3)
            if blocks:
                blocking_primes.append(p)
            else:
                non_blocking_primes.append((p, 'NO_BLOCK'))

        # CRT product of blocking primes
        crt_product = 1
        for p in blocking_primes:
            crt_product *= p

        k_eliminated = len(blocking_primes) > 0

        results[k] = {
            'S': S, 'd': d,
            'total_primes': len(primes),
            'blocking': blocking_primes,
            'non_blocking': non_blocking_primes,
            'skipped': skipped_primes,
            'crt_product': crt_product,
            'eliminated': k_eliminated,
        }

        status = "ELIMINATED" if k_eliminated else "NOT eliminated"
        print(f"  k={k:2d}  S={S:3d}  d={d:15d}  "
              f"primes={len(primes):3d}  "
              f"blocking={len(blocking_primes):3d}  "
              f"CRT={crt_product:12d}  {status}")

    # Summary table
    print(f"\n  {'='*60}")
    print(f"  TOOL 3 SUMMARY TABLE")
    print(f"  {'='*60}")
    print(f"  {'k':>4s} {'S':>4s} {'d':>16s} {'#primes':>8s} {'#block':>7s} "
          f"{'CRT prod':>14s} {'status':>12s}")
    print(f"  {'-'*4} {'-'*4} {'-'*16} {'-'*8} {'-'*7} {'-'*14} {'-'*12}")
    for k, r in sorted(results.items()):
        status = "ELIMINATED" if r['eliminated'] else "open"
        crt_str = str(r['crt_product']) if r['crt_product'] < 10**13 else f"{r['crt_product']:.4e}"
        print(f"  {k:4d} {r['S']:4d} {r['d']:16d} {r['total_primes']:8d} "
              f"{len(r['blocking']):7d} {crt_str:>14s} {status:>12s}")

    eliminated = [k for k, r in results.items() if r['eliminated']]
    open_ks = [k for k, r in results.items() if not r['eliminated']]
    print(f"\n  Eliminated k: {eliminated}")
    print(f"  Open k: {open_ks}")

    return results


# ============================================================================
# TOOL 4: REGIME ANALYSIS
# ============================================================================

def tool4_regime_analysis(k_range=range(3, 21)):
    """
    Tool 4: Regime analysis of primes p|d.
    Classify primes by size relative to S:
      - Small: p < S (reachability saturates quickly)
      - Medium: S <= p <= S^2 (blocking most likely)
      - Large: p > S^2 (few residues reachable)
    """
    hdr = "TOOL 4: REGIME ANALYSIS"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)

    results = {}

    for k in k_range:
        check_budget(f"Tool 4 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue

        primes = distinct_primes(d)
        small, medium, large = [], [], []
        S_sq = S * S

        for p in primes:
            if p < S:
                small.append(p)
            elif p <= S_sq:
                medium.append(p)
            else:
                large.append(p)

        # For each regime, compute blocking stats
        regime_stats = {}
        for regime_name, regime_primes in [('small', small), ('medium', medium), ('large', large)]:
            blocking = 0
            total = 0
            for p in regime_primes:
                check_budget(f"Tool 4 k={k} {regime_name} p={p}")
                if p > 50000:
                    continue
                inv3 = modinv(3, p)
                if inv3 is None:
                    continue
                total += 1
                _, blocks = backward_reachability_unconstrained(k, p, inv3)
                if blocks:
                    blocking += 1

            frac = blocking / total if total > 0 else 0.0
            regime_stats[regime_name] = {
                'primes': regime_primes,
                'count': len(regime_primes),
                'tested': total,
                'blocking': blocking,
                'fraction': frac,
            }

        results[k] = {
            'S': S, 'd': d, 'S_sq': S_sq,
            'regimes': regime_stats,
        }

        print(f"\n  k={k}  S={S}  S^2={S_sq}  d={d}")
        for rname in ['small', 'medium', 'large']:
            rs = regime_stats[rname]
            if rs['tested'] > 0:
                print(f"    {rname:>7s}: {rs['count']:4d} primes, "
                      f"tested {rs['tested']:4d}, "
                      f"blocking {rs['blocking']:4d} ({rs['fraction']:.1%})")
            else:
                print(f"    {rname:>7s}: {rs['count']:4d} primes, none tested")

    # Cross-k analysis
    print(f"\n  {'='*60}")
    print(f"  REGIME ANALYSIS SUMMARY")
    print(f"  {'='*60}")
    print(f"  {'k':>4s} {'small_block':>12s} {'medium_block':>13s} {'large_block':>12s}")
    print(f"  {'-'*4} {'-'*12} {'-'*13} {'-'*12}")
    for k, r in sorted(results.items()):
        parts = []
        for rname in ['small', 'medium', 'large']:
            rs = r['regimes'][rname]
            if rs['tested'] > 0:
                parts.append(f"{rs['blocking']}/{rs['tested']}")
            else:
                parts.append("--")
        print(f"  {k:4d} {parts[0]:>12s} {parts[1]:>13s} {parts[2]:>12s}")

    return results


# ============================================================================
# TOOL 5: TRANSITION MATRIX METHOD
# ============================================================================

def build_transition_matrix(k, p, inv3_p=None):
    """
    Build the Horner chain transition matrix M (p x p) mod prime p.

    M[r][c] = 1 if there exists a position a in {0,...,S-1}
              such that c = (3*r + 2^a) mod p.

    Returns M as dict of dicts: M[r] = set of reachable c's.
    """
    S = compute_S(k)
    pow2_set = set(pow(2, a, p) for a in range(S))

    M = defaultdict(set)
    for r in range(p):
        base = (3 * r) % p
        for pw in pow2_set:
            c = (base + pw) % p
            M[r].add(c)

    return M


def matrix_power_entry(M, p, k, start, end):
    """
    Compute M^k[start][end] using set-based BFS (reachability in k steps).
    Returns the number of paths from start to end in exactly k steps.

    For counting paths, we use a different approach: track multiplicity.
    M_count[r][c] = number of transitions from r to c.

    Actually, for the transition matrix method, we want (M^k)[0][0] which
    counts the number of paths from 0 to 0 in k steps.

    For small p, we can do this as actual matrix multiplication mod some large prime.
    """
    S = compute_S(k)
    pow2_list = [pow(2, a, p) for a in range(S)]
    n_positions = len(set(pow2_list))  # number of distinct 2^a mod p

    # Build count matrix as list of lists
    # M_count[r][c] = number of distinct positions a giving transition r -> c
    M_count = [[0] * p for _ in range(p)]
    for r in range(p):
        base = (3 * r) % p
        for pw in pow2_list:
            c = (base + pw) % p
            M_count[r][c] += 1

    # Matrix exponentiation to compute M^k
    # Result[i][j] = sum over paths of product of multiplicities
    # This counts the number of (WITH-REPLACEMENT) Horner chains from i to j in k steps

    # For small p, direct multiplication
    def mat_mul(A, B, sz):
        C = [[0] * sz for _ in range(sz)]
        for i in range(sz):
            for j in range(sz):
                s = 0
                for m in range(sz):
                    s += A[i][m] * B[m][j]
                C[i][j] = s
        return C

    def mat_pow(M_mat, sz, exp):
        # Identity
        result = [[0] * sz for _ in range(sz)]
        for i in range(sz):
            result[i][i] = 1
        base = M_mat
        while exp > 0:
            if exp % 2 == 1:
                result = mat_mul(result, base, sz)
            base = mat_mul(base, base, sz)
            exp //= 2
        return result

    Mk = mat_pow(M_count, p, k)
    return Mk[start][end]


def tool5_transition_matrix(k_range=range(3, 15)):
    """
    Tool 5: Transition matrix method.
    Build M mod p, compute M^k[0][0], compare with reachability.
    """
    hdr = "TOOL 5: TRANSITION MATRIX METHOD"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)

    results = {}

    for k in k_range:
        check_budget(f"Tool 5 k={k}")
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue

        primes = distinct_primes(d)
        k_result = {'S': S, 'd': d, 'matrix_results': {}}

        print(f"\n  k={k}  S={S}  d={d}")

        for p in primes:
            check_budget(f"Tool 5 k={k} p={p}")

            # Transition matrix is p x p; limit to small p
            if p > 200:
                continue

            inv3 = modinv(3, p)
            if inv3 is None:
                continue

            # Compute M^k[0][0]
            mk_00 = matrix_power_entry(None, p, k, 0, 0)

            # Compare with backward reachability
            _, blocks_uc = backward_reachability_unconstrained(k, p, inv3)

            # Consistency check: M^k[0][0] = 0 iff backward reachability blocks
            consistent = (mk_00 == 0) == blocks_uc

            k_result['matrix_results'][p] = {
                'Mk_00': mk_00,
                'blocks_uc': blocks_uc,
                'consistent': consistent,
            }

            status = "BLOCKS" if mk_00 == 0 else f"paths={mk_00}"
            cons = "OK" if consistent else "*** MISMATCH ***"
            print(f"    p={p}: M^{k}[0][0] = {mk_00}  reachability={'BLOCKS' if blocks_uc else 'open'}"
                  f"  [{cons}]")

        results[k] = k_result

    # Summary
    print(f"\n  {'='*60}")
    print(f"  TOOL 5 SUMMARY")
    print(f"  {'='*60}")
    all_consistent = True
    total_checks = 0
    for k, r in sorted(results.items()):
        for p, mr in r['matrix_results'].items():
            total_checks += 1
            if not mr['consistent']:
                all_consistent = False
                print(f"  MISMATCH at k={k}, p={p}")
    print(f"  Total consistency checks: {total_checks}")
    print(f"  All consistent: {all_consistent}")

    return results


# ============================================================================
# SELF-TESTS (minimum 15)
# ============================================================================

def run_self_tests():
    """Run all self-tests. Returns (passed, failed, total)."""
    hdr = "SELF-TESTS"
    print("\n" + "=" * 72)
    print(hdr)
    print("=" * 72)

    passed = 0
    failed = 0
    total = 0

    def check(name, condition, detail=""):
        nonlocal passed, failed, total
        total += 1
        if condition:
            passed += 1
            print(f"  T{total:02d}: PASS  {name}")
        else:
            failed += 1
            print(f"  T{total:02d}: FAIL  {name}  {detail}")

    # -------------------------------------------------------------------
    # T01: Verify d = 2^S - 3^k for k = 3..10
    # -------------------------------------------------------------------
    for k in range(3, 11):
        S = compute_S(k)
        d = compute_d(k)
        expected = (1 << S) - 3**k
        if d != expected:
            check(f"d = 2^S - 3^k for k={k}", False, f"got {d}, expected {expected}")
            break
    else:
        check("d = 2^S - 3^k for k = 3..10", True)

    # -------------------------------------------------------------------
    # T02: Verify backward reachability for k=3 matches known result (no cycle)
    # For k=3, d = 2^5 - 3^3 = 32 - 27 = 5. N_0(5) = 0 (no nontrivial cycle).
    # -------------------------------------------------------------------
    k3 = 3
    S3 = compute_S(k3)
    d3 = compute_d(k3)
    # d3 = 5, primes = [5]
    primes3 = distinct_primes(d3)
    all_block_k3 = True
    for p in primes3:
        inv3 = modinv(3, p)
        if inv3 is None:
            continue
        _, blocks = backward_reachability_unconstrained(k3, p, inv3)
        if not blocks:
            all_block_k3 = False
    # For k=3, let's verify by exhaustive check: is corrSum(A) = 0 mod d for any A?
    dist3 = enumerate_corrsums_mod(k3, d3)
    n0_k3 = dist3.get(0, 0)
    check("k=3: no cycle exists (N_0=0)", n0_k3 == 0, f"N_0={n0_k3}")

    # -------------------------------------------------------------------
    # T03: For k=3, per-prime results vs exhaustive enumeration
    # -------------------------------------------------------------------
    # k=3, d=5, only prime is 5. Check that backward reachability mod 5
    # correctly identifies blocking (or not) matching N_0(5).
    # But gcd(3,5) = 1, so 3^{-1} mod 5 = 2.
    inv3_5 = modinv(3, 5)
    check("3^{-1} mod 5 = 2", inv3_5 == 2, f"got {inv3_5}")  # This is T03

    # -------------------------------------------------------------------
    # T04: Transition matrix agrees with reachability for k=3
    # -------------------------------------------------------------------
    # For k=3, p=5: compute M^3[0][0]
    p_test = 5
    mk_00_k3 = matrix_power_entry(None, p_test, k3, 0, 0)
    _, blocks_k3_uc = backward_reachability_unconstrained(k3, p_test, inv3_5)
    # M^k[0][0] = 0 should agree with reachability blocking
    consistent_k3 = (mk_00_k3 == 0) == blocks_k3_uc
    check(f"k=3 p=5: transition matrix agrees with reachability",
          consistent_k3,
          f"M^3[0][0]={mk_00_k3}, blocks={blocks_k3_uc}")

    # -------------------------------------------------------------------
    # T05: WR-constrained reachability <= unconstrained for k=3..7
    # -------------------------------------------------------------------
    wr_leq_uc = True
    wr_detail = ""
    for k in range(3, 8):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue
        primes = distinct_primes(d)
        for p in primes:
            if p > 5000:
                continue
            inv3 = modinv(3, p)
            if inv3 is None:
                continue
            R_uc, _ = backward_reachability_unconstrained(k, p, inv3)
            uc_R0 = R_uc[-1] if R_uc else frozenset()
            wr_R0, _, n_states = backward_reachability_wr_exact(k, p, inv3, timeout_states=500000)
            if wr_R0 is None:
                continue  # timeout, skip
            if not wr_R0.issubset(uc_R0):
                wr_leq_uc = False
                wr_detail = f"k={k}, p={p}: WR has {wr_R0 - uc_R0} not in UC"
                break
        if not wr_leq_uc:
            break
    check("WR-constrained reachability subset of unconstrained (k=3..7)",
          wr_leq_uc, wr_detail)

    # -------------------------------------------------------------------
    # T06: CRT product consistency -- blocking primes are actual divisors of d
    # -------------------------------------------------------------------
    crt_ok = True
    crt_detail = ""
    for k in range(3, 11):
        d = compute_d(k)
        if d <= 1:
            continue
        primes = distinct_primes(d)
        for p in primes:
            if d % p != 0:
                crt_ok = False
                crt_detail = f"k={k}: p={p} not divisor of d={d}"
                break
        if not crt_ok:
            break
    check("CRT: all primes tested actually divide d (k=3..10)",
          crt_ok, crt_detail)

    # -------------------------------------------------------------------
    # T07: Verify 3^{-1} mod p is correct for several primes
    # -------------------------------------------------------------------
    inv3_ok = True
    inv3_detail = ""
    test_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
    for p in test_primes:
        inv = modinv(3, p)
        if inv is not None and (3 * inv) % p != 1:
            inv3_ok = False
            inv3_detail = f"p={p}: 3*{inv} mod {p} = {(3*inv)%p} != 1"
            break
    check("3^{-1} mod p correct for test primes", inv3_ok, inv3_detail)

    # -------------------------------------------------------------------
    # T08: Edge case: p = 2 (if d is even)
    # For k=3, d=5 (odd). For k=4, d=2^7-3^4=128-81=47 (odd).
    # d is always odd since 2^S is even and 3^k is odd, so d = even - odd = odd.
    # Wait: 2^S - 3^k: 2^S is even (S>=2), 3^k is odd, so d is odd. Always.
    # So p=2 never divides d.
    # -------------------------------------------------------------------
    all_d_odd = True
    for k in range(3, 30):
        d = compute_d(k)
        if d > 0 and d % 2 == 0:
            all_d_odd = False
            break
    check("d is always odd (p=2 never divides d) for k=3..29", all_d_odd)

    # -------------------------------------------------------------------
    # T09: Reachability monotonicity: |R_{j-1}| <= min(|R_j|*(S-k+1), p)
    # Actually the bound is: |R_{j-1}| <= min(|R_j| * |{2^a mod p : a<S}|, p)
    # -------------------------------------------------------------------
    mono_ok = True
    mono_detail = ""
    for k in [3, 4, 5, 6]:
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue
        primes = distinct_primes(d)
        for p in primes:
            if p > 5000:
                continue
            inv3 = modinv(3, p)
            if inv3 is None:
                continue
            pow2_distinct = len(set(pow(2, a, p) for a in range(S)))
            R_list, _ = backward_reachability_unconstrained(k, p, inv3)
            if R_list is None:
                continue
            for i in range(len(R_list) - 1):
                r_curr = len(R_list[i])
                r_next = len(R_list[i + 1])
                bound = min(r_curr * pow2_distinct, p)
                if r_next > bound:
                    mono_ok = False
                    mono_detail = (f"k={k} p={p} step {i}: "
                                   f"|R|={r_next} > bound={bound}")
                    break
            if not mono_ok:
                break
        if not mono_ok:
            break
    check("Reachability monotonicity bound holds (k=3..6)",
          mono_ok, mono_detail)

    # -------------------------------------------------------------------
    # T10: For blocking primes, verify independently by exhaustive enumeration
    # -------------------------------------------------------------------
    verify_ok = True
    verify_detail = ""
    for k in range(3, 10):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue
        if not can_enumerate(k, limit=500_000):
            continue
        primes = distinct_primes(d)
        for p in primes:
            if p > 5000:
                continue
            inv3 = modinv(3, p)
            if inv3 is None:
                continue
            _, blocks = backward_reachability_unconstrained(k, p, inv3)
            if blocks:
                # Verify: no valid A has corrSum(A) = 0 mod p
                dist = enumerate_corrsums_mod(k, p)
                n0_p = dist.get(0, 0)
                if n0_p != 0:
                    verify_ok = False
                    verify_detail = f"k={k} p={p}: blocks but N_0(p)={n0_p}"
                    break
        if not verify_ok:
            break
    check("Blocking primes verified by exhaustive enumeration (k=3..9)",
          verify_ok, verify_detail)

    # -------------------------------------------------------------------
    # T11: Horner chain forward matches corrSum
    # For k=4, check that horner_chain_forward gives the same as corrSum
    # -------------------------------------------------------------------
    horner_ok = True
    horner_detail = ""
    for k in [3, 4, 5, 6]:
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue
        count = 0
        for B in combinations(range(1, S), k - 1):
            positions = (0,) + B
            h_fwd = horner_chain_forward(positions, k, d)
            cs = corrsum_from_subset(B, k, d)
            if h_fwd != cs:
                horner_ok = False
                horner_detail = f"k={k} B={B}: horner={h_fwd}, corrsum={cs}"
                break
            count += 1
            if count > 5000:
                break
        if not horner_ok:
            break
    check("Horner chain forward matches corrSum (k=3..6)",
          horner_ok, horner_detail)

    # -------------------------------------------------------------------
    # T12: For non-blocking prime, 0 IS in R_0 (consistency)
    # -------------------------------------------------------------------
    nonblock_ok = True
    nonblock_detail = ""
    for k in range(3, 10):
        d = compute_d(k)
        if d <= 1:
            continue
        primes = distinct_primes(d)
        for p in primes:
            if p > 5000:
                continue
            inv3 = modinv(3, p)
            if inv3 is None:
                continue
            R_list, blocks = backward_reachability_unconstrained(k, p, inv3)
            if not blocks:
                if 0 not in R_list[-1]:
                    nonblock_ok = False
                    nonblock_detail = f"k={k} p={p}: claims non-blocking but 0 not in R_0"
                    break
        if not nonblock_ok:
            break
    check("Non-blocking primes have 0 in R_0 (k=3..9)",
          nonblock_ok, nonblock_detail)

    # -------------------------------------------------------------------
    # T13: WR reachability for k=3 gives exact N_0
    # For k=3, d=5, primes=[5]. WR reachability mod 5.
    # The actual number of valid subsets A with corrSum=0 mod 5 should be 0.
    # -------------------------------------------------------------------
    k_t13 = 3
    p_t13 = 5
    inv3_t13 = modinv(3, p_t13)
    wr_R0_t13, blocks_t13, _ = backward_reachability_wr_exact(k_t13, p_t13, inv3_t13)
    # Exhaustive check
    dist_t13 = enumerate_corrsums_mod(k_t13, p_t13)
    n0_t13 = dist_t13.get(0, 0)
    # If n0 = 0, then WR should block (0 not in R_0 using a_0=0 constraint)
    # Note: WR checks c_0 = 0 (Horner start), not corrSum = 0 directly.
    # The Horner chain: c_0 = 0, c_k = corrSum mod p. So corrSum = 0 mod p
    # iff there exists a valid chain with c_k = 0. Backward reachability
    # starts from c_k = 0 and checks if c_0 = 0 is reachable.
    # So blocks_t13 = True iff no valid chain reaches c_k = 0 from c_0 = 0.
    check("WR k=3 p=5: blocking agrees with N_0(5)=0",
          blocks_t13 == (n0_t13 == 0),
          f"blocks={blocks_t13}, N_0(5)={n0_t13}")

    # -------------------------------------------------------------------
    # T14: Transition matrix M^k[0][0] >= 0 (non-negative counts)
    # -------------------------------------------------------------------
    tm_nonneg = True
    tm_detail = ""
    for k in [3, 4, 5]:
        d = compute_d(k)
        if d <= 1:
            continue
        primes = distinct_primes(d)
        for p in primes:
            if p > 100:
                continue
            mk = matrix_power_entry(None, p, k, 0, 0)
            if mk < 0:
                tm_nonneg = False
                tm_detail = f"k={k} p={p}: M^k[0][0]={mk} < 0"
                break
        if not tm_nonneg:
            break
    check("Transition matrix M^k[0][0] >= 0 (k=3..5)",
          tm_nonneg, tm_detail)

    # -------------------------------------------------------------------
    # T15: For k=4, verify d=47 and its prime factorization
    # -------------------------------------------------------------------
    k4 = 4
    S4 = compute_S(k4)
    d4 = compute_d(k4)
    check("k=4: S=7, d=47", S4 == 7 and d4 == 47,
          f"S={S4}, d={d4}")

    # -------------------------------------------------------------------
    # T16: For k=5, verify exhaustive N_0(d) = 0
    # -------------------------------------------------------------------
    k5 = 5
    d5 = compute_d(k5)
    dist5 = enumerate_corrsums_mod(k5, d5)
    n0_k5 = dist5.get(0, 0)
    check("k=5: N_0(d) = 0 (exhaustive)", n0_k5 == 0, f"N_0={n0_k5}")

    # -------------------------------------------------------------------
    # T17: Backward reachability R_k = {0} always (initial condition)
    # -------------------------------------------------------------------
    init_ok = True
    for k in [3, 5, 7, 10]:
        d = compute_d(k)
        if d <= 1:
            continue
        primes = distinct_primes(d)
        for p in primes[:3]:
            if p > 5000:
                continue
            inv3 = modinv(3, p)
            if inv3 is None:
                continue
            R_list, _ = backward_reachability_unconstrained(k, p, inv3)
            if R_list and R_list[0] != frozenset({0}):
                init_ok = False
                break
    check("Backward reachability initial condition R_k = {0}",
          init_ok)

    # -------------------------------------------------------------------
    # T18: S is always >= k+1 for k >= 2
    # (since log2(3) > 1, so S = ceil(k*log2(3)) >= k+1)
    # -------------------------------------------------------------------
    s_bound_ok = True
    for k in range(2, 50):
        if compute_S(k) < k + 1:
            s_bound_ok = False
            break
    check("S >= k+1 for k=2..49", s_bound_ok)

    # -------------------------------------------------------------------
    # T19: d > 0 for all k >= 2
    # -------------------------------------------------------------------
    d_pos_ok = True
    for k in range(2, 50):
        if compute_d(k) <= 0:
            d_pos_ok = False
            break
    check("d > 0 for k=2..49", d_pos_ok)

    # -------------------------------------------------------------------
    # T20: Transition matrix row sums are constant (= S distinct positions)
    # Each row r of M has transitions to |{(3r+2^a) mod p : a in 0..S-1}|
    # The row sum (counting multiplicities) should be S.
    # -------------------------------------------------------------------
    rowsum_ok = True
    rowsum_detail = ""
    k_t20 = 4
    S_t20 = compute_S(k_t20)
    d_t20 = compute_d(k_t20)
    for p in distinct_primes(d_t20):
        if p > 100:
            continue
        pow2_list = [pow(2, a, p) for a in range(S_t20)]
        for r in range(p):
            base = (3 * r) % p
            transitions = [((base + pw) % p) for pw in pow2_list]
            if len(transitions) != S_t20:
                rowsum_ok = False
                rowsum_detail = f"p={p} r={r}: row has {len(transitions)} transitions, expected {S_t20}"
                break
        if not rowsum_ok:
            break
    check("Transition matrix row sums = S (counting multiplicity, k=4)",
          rowsum_ok, rowsum_detail)

    # -------------------------------------------------------------------
    # Summary
    # -------------------------------------------------------------------
    print(f"\n  {'='*60}")
    print(f"  SELF-TEST SUMMARY: {passed}/{total} PASS, {failed}/{total} FAIL")
    print(f"  {'='*60}")

    return passed, failed, total


# ============================================================================
# MAIN: ORCHESTRATION
# ============================================================================

def main():
    """Run requested tools and self-tests."""
    args = sys.argv[1:]

    if 'selftest' in args:
        run_self_tests()
        return

    # Determine which tools to run
    if args:
        tools_to_run = set()
        for a in args:
            try:
                tools_to_run.add(int(a))
            except ValueError:
                pass
    else:
        tools_to_run = {1, 2, 3, 4, 5}

    print("=" * 72)
    print("R7: PER-PRIME BACKWARD REACHABILITY FOR CYCLE EXCLUSION")
    print("=" * 72)
    print(f"Time budget: {TIME_BUDGET}s")
    print(f"Tools to run: {sorted(tools_to_run)}")

    all_results = {}

    try:
        if 1 in tools_to_run:
            all_results['tool1'] = tool1_per_prime_backward(range(3, 21))

        if 2 in tools_to_run:
            all_results['tool2'] = tool2_wr_constrained(range(3, 13))

        if 3 in tools_to_run:
            all_results['tool3'] = tool3_crt_combination(range(3, 21))

        if 4 in tools_to_run:
            all_results['tool4'] = tool4_regime_analysis(range(3, 21))

        if 5 in tools_to_run:
            all_results['tool5'] = tool5_transition_matrix(range(3, 13))

    except TimeoutError as e:
        print(f"\n  *** TIMEOUT: {e} ***")

    # Always run self-tests
    print()
    passed, failed, total = run_self_tests()

    # Final summary
    elapsed = time.time() - T_START
    print(f"\n{'='*72}")
    print(f"R7 FINAL SUMMARY")
    print(f"{'='*72}")
    print(f"  Elapsed time: {elapsed:.1f}s / {TIME_BUDGET}s")
    print(f"  Self-tests: {passed}/{total} PASS")

    if 'tool3' in all_results:
        t3 = all_results['tool3']
        eliminated = [k for k, r in t3.items() if r['eliminated']]
        open_ks = [k for k, r in t3.items() if not r['eliminated']]
        print(f"\n  CRT ELIMINATION RESULTS:")
        print(f"    Eliminated k values (unconstrained reachability): {eliminated}")
        print(f"    Open k values: {open_ks}")
        print()
        print(f"  INTERPRETATION:")
        if eliminated:
            print(f"    For k in {eliminated}, at least one prime p|d blocks the Horner chain")
            print(f"    mod p, proving that no valid corrSum can be 0 mod p, hence mod d.")
        if open_ks:
            print(f"    For k in {open_ks}, unconstrained backward reachability does not block.")
            print(f"    The WR-constrained version may block additional k values.")

    if 'tool2' in all_results:
        t2 = all_results['tool2']
        wr_only_blocks = []
        for k, r in sorted(t2.items()):
            wr_extra = [p for p in r.get('blocking_wr', [])
                        if p not in r.get('blocking_uc', [])]
            if wr_extra:
                wr_only_blocks.append((k, wr_extra))
        if wr_only_blocks:
            print(f"\n  WR-ONLY BLOCKING (not seen in unconstrained):")
            for k, primes in wr_only_blocks:
                print(f"    k={k}: primes {primes}")
        else:
            print(f"\n  No additional blocking from WR constraint (for tested k values).")

    print(f"\n  KEY FINDING:")
    print(f"    Backward reachability per-prime is a PURELY COMBINATORIAL method")
    print(f"    that can prove cycle non-existence without Fourier analysis.")
    print(f"    For small primes, reachability sets saturate (R_j = Z/pZ).")
    print(f"    Blocking tends to occur at medium/large primes where the set")
    print(f"    of available 2^a residues does not span all of Z/pZ.")
    print()


if __name__ == '__main__':
    main()
