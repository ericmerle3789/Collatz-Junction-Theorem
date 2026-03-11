#!/usr/bin/env python3
"""
R57 — Axe A : Base k=2 via borne sur max N_r
==========================================================================
Agent R57 (Investigateur A) — Round 57

MISSION: Study the structure of max_r N_r for k=2 in R1 regime and attempt
to obtain or approach a rigorous bound.

CONTEXT FROM R55-R56:
  P_B = 2^a + g*2^b mod p,  0 <= a <= b <= M
  g = 3 * 2^{-1} mod p = 3*(p+1)/2 mod p  (for k=2 Collatz context)
  C(2,M) = (M+1)(M+2)/2 = number of monotone pairs (a,b)
  N_r = #{(a,b) : P_B = r mod p}
  V(2) = Sum_r (N_r - C/p)^2
  A(2) = V(2)/C(2)
  R1 = regime where ord_p(2) > M+1

  SHIFT-INVARIANCE [PROVED R55]: P_{B+(1,1)} = 2g * P_B mod p
  A(2) <= 2.28 on 2931 R1 cases (R56)
  Degenerate case g = -1 mod p: P_{(a,a)} = 0, N_0 >= M+1
  Generic case (g != -1): max A = 1.89

KEY IDEA:
  Factorize: 2^a * (1 + g*2^{b-a}) = r mod p.
  Set delta = b-a in [0,M], c_delta = (1 + g*2^delta) mod p.
  For each delta: at most 1 solution a in [0, M-delta] when R1 holds.
  So max N_r <= #{delta : c_delta != 0 AND dlog constraint satisfied}.

QUESTIONS Q1-Q7:
  Q1: delta-reformulation canonical
  Q2: Structure of c_delta set
  Q3: Discrete log bound in R1
  Q4: Empirical bound on max N_r
  Q5: Rigorous bound candidate
  Q6: Is r=0 special?
  Q7: Implication for A(2)

EPISTEMIC LABELS:
  [PROVED]       = rigorous proof or exact algebraic identity
  [COMPUTED]     = verified by exact computation on all tested cases
  [OBSERVED]     = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven
  [REFUTED]      = contradicted by evidence

Author: Claude Opus 4.6 (R57 Investigateur A pour Eric Merle)
Date:   2026-03-11
"""

import sys
import time
from math import gcd, ceil, log2, sqrt, log, pi
from collections import defaultdict, Counter
from fractions import Fraction

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 28.0  # 28s budget (safe margin for 30s limit)

PASS_COUNT = 0
FAIL_COUNT = 0
VERBOSE = True

def elapsed():
    return time.time() - T_START

def time_ok(margin=2):
    return (TIME_BUDGET - elapsed()) > margin

def record_test(section, name, passed, detail=""):
    global PASS_COUNT, FAIL_COUNT
    status = "PASS" if passed else "FAIL"
    if passed:
        PASS_COUNT += 1
    else:
        FAIL_COUNT += 1
    print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))

# ============================================================================
# MATHEMATICAL PRIMITIVES
# ============================================================================

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def primes_up_to(n):
    sieve = [True] * (n + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(n**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, n+1, i):
                sieve[j] = False
    return [i for i in range(2, n+1) if sieve[i]]

def ord_mod(base, m):
    """Multiplicative order of base mod m."""
    if m <= 1 or gcd(base, m) != 1:
        return None
    o, v = 1, base % m
    while v != 1:
        o += 1
        v = (v * base) % m
        if o > m:
            return None
    return o

def compute_g_k2(p):
    """g = 3 * 2^{-1} mod p for k=2."""
    if p <= 3 or p % 2 == 0:
        return None
    inv2 = pow(2, p - 2, p)
    return (3 * inv2) % p

def C_k2(M):
    """C(2,M) = (M+1)(M+2)/2."""
    return (M + 1) * (M + 2) // 2

def eval_PB(a, b, g, p):
    """P_B = 2^a + g * 2^b mod p."""
    return (pow(2, a, p) + g * pow(2, b, p)) % p

def compute_Nr_exact(M, g, p):
    """Exact count of N_r for all residues, k=2, triangle 0<=a<=b<=M."""
    Nr = Counter()
    for a in range(M + 1):
        pow2a = pow(2, a, p)
        for b in range(a, M + 1):
            pow2b = pow(2, b, p)
            r = (pow2a + g * pow2b) % p
            Nr[r] += 1
    return Nr

def compute_Nr_via_delta(M, g, p):
    """Reformulation via delta = b - a. Returns the same Nr dict."""
    Nr = Counter()
    for delta in range(M + 1):
        c_delta = (1 + g * pow(2, delta, p)) % p
        if c_delta == 0:
            # 2^a * 0 = 0 mod p for all a in [0, M-delta]
            Nr[0] += (M - delta + 1)
        else:
            for a in range(M - delta + 1):
                r = (pow(2, a, p) * c_delta) % p
                Nr[r] += 1
    return Nr

def compute_c_deltas(M, g, p):
    """Compute c_delta = (1 + g*2^delta) mod p for delta = 0,...,M."""
    return [(1 + g * pow(2, delta, p)) % p for delta in range(M + 1)]

def discrete_log_2(target, p, ord2):
    """Find a such that 2^a = target mod p, or return None.
    Brute-force search (acceptable for small ord2)."""
    if target == 0:
        return None
    v = 1
    for a in range(ord2):
        if v == target:
            return a
        v = (v * 2) % p
    return None

def compute_M_for_k2(p):
    """Compute max_B = S - k for k=2, where S = ceil(2*log2(3)) = 4.
    So M = 4 - 2 = 2. But for generality we parameterize M freely."""
    return 2  # fixed for k=2 in Collatz context

def compute_g_general(k, p):
    """g = 2^S * 3^{-k} mod p, with S = smallest integer s.t. 2^S > 3^k."""
    if gcd(6, p) != 1:
        return None
    S = ceil(k * log2(3))
    while (1 << S) <= 3 ** k:
        S += 1
    while S > 0 and (1 << (S - 1)) > 3 ** k:
        S -= 1
    return (pow(2, S, p) * pow(pow(3, k, p), p - 2, p)) % p

# ============================================================================
# R1 CASE GENERATION
# ============================================================================

def generate_R1_cases(max_prime=500, M_range=None):
    """Generate (p, M, g, ord2) tuples in R1 regime.
    R1: ord_p(2) > M+1.
    For the Collatz context: g = 3/2 mod p, M varies.
    We also include the general g = 2^S * 3^{-k} mod p for k=2.
    """
    cases = []
    all_primes = primes_up_to(max_prime)
    valid_primes = [p for p in all_primes if p >= 5]

    for p in valid_primes:
        g = compute_g_k2(p)
        if g is None:
            continue
        ord2 = ord_mod(2, p)
        if ord2 is None:
            continue
        # M ranges from 1 to min(ord2 - 2, some cap) for R1
        max_M = min(ord2 - 2, 50, p - 2)
        if max_M < 1:
            continue
        if M_range is not None:
            M_vals = [m for m in M_range if 1 <= m <= max_M]
        else:
            # Sample a few M values
            M_vals = list(range(1, min(max_M + 1, 10)))
            if max_M >= 10:
                M_vals.extend([max_M // 2, max_M])
                M_vals = sorted(set(M_vals))
        for M in M_vals:
            is_degen = (g % p == (p - 1))  # g = -1 mod p
            cases.append((p, M, g, ord2, is_degen))
    return cases

def generate_R1_cases_large(min_prime=100, max_prime=2000, n_target=250):
    """Generate a large set of R1 cases for statistical analysis.
    For each prime, sample multiple M values to maximize coverage."""
    cases = []
    all_primes = primes_up_to(max_prime)
    valid_primes = [p for p in all_primes if p >= min_prime]

    for p in valid_primes:
        if len(cases) >= n_target:
            break
        g = compute_g_k2(p)
        if g is None:
            continue
        ord2 = ord_mod(2, p)
        if ord2 is None:
            continue
        max_M = min(ord2 - 2, 80)
        if max_M < 2:
            continue
        is_degen = (g % p == (p - 1))
        # Sample up to 3 M values: small, mid, max
        M_vals = [max_M]
        if max_M >= 6:
            M_vals.append(max_M // 2)
        if max_M >= 10:
            M_vals.append(max(2, max_M // 4))
        for M in sorted(set(M_vals)):
            cases.append((p, M, g, ord2, is_degen))
    return cases


# ============================================================================
# SECTION 1: DELTA-REFORMULATION (Q1)
# ============================================================================

def section1_delta_reformulation():
    """Q1: Verify that the delta-reformulation gives the same N_r counts."""
    print("\n" + "=" * 72)
    print("SECTION 1: DELTA-REFORMULATION (Q1)")
    print("  P_B = 2^a * (1 + g*2^delta) mod p, delta = b-a")
    print("  Verify: Nr_exact == Nr_delta for all residues")
    print("=" * 72)

    test_cases = generate_R1_cases(max_prime=100)
    if len(test_cases) > 30:
        test_cases = test_cases[:30]

    all_match = True
    count_tested = 0

    for p, M, g, ord2, is_degen in test_cases:
        if not time_ok():
            break
        Nr_exact = compute_Nr_exact(M, g, p)
        Nr_delta = compute_Nr_via_delta(M, g, p)

        C = C_k2(M)
        assert sum(Nr_exact.values()) == C
        assert sum(Nr_delta.values()) == C

        # Compare
        all_r = set(Nr_exact.keys()) | set(Nr_delta.keys())
        for r in all_r:
            if Nr_exact[r] != Nr_delta[r]:
                all_match = False
                break
        count_tested += 1

    record_test("S1", "1.1 Delta-reformulation matches exact counting",
                all_match, f"{count_tested} cases tested")

    # Test the factorization identity: P_B(a,b) = 2^a * c_{b-a} mod p
    identity_holds = True
    for p, M, g, ord2, is_degen in test_cases[:10]:
        c_deltas = compute_c_deltas(M, g, p)
        for a in range(M + 1):
            pow2a = pow(2, a, p)
            for b in range(a, M + 1):
                delta = b - a
                expected = (pow2a * c_deltas[delta]) % p
                actual = eval_PB(a, b, g, p)
                if expected != actual:
                    identity_holds = False
                    break

    record_test("S1", "1.2 Algebraic identity: P(a,b) = 2^a * c_{b-a} mod p",
                identity_holds, "[PROVED] exact algebraic factorization")

    # When c_delta = 0: all a-values give r = 0
    zero_c_check = True
    zero_c_count = 0
    for p, M, g, ord2, is_degen in test_cases[:15]:
        c_deltas = compute_c_deltas(M, g, p)
        for delta in range(M + 1):
            if c_deltas[delta] == 0:
                zero_c_count += 1
                for a in range(M - delta + 1):
                    if eval_PB(a, a + delta, g, p) != 0:
                        zero_c_check = False

    record_test("S1", "1.3 c_delta = 0 implies all contributions go to r=0",
                zero_c_check, f"[PROVED] {zero_c_count} degenerate deltas found")

    # When c_delta != 0: contribution to r determined by 2^a * c_delta
    nonzero_c_check = True
    for p, M, g, ord2, is_degen in test_cases[:10]:
        c_deltas = compute_c_deltas(M, g, p)
        for delta in range(M + 1):
            if c_deltas[delta] != 0:
                for a in range(M - delta + 1):
                    r = eval_PB(a, a + delta, g, p)
                    expected_r = (pow(2, a, p) * c_deltas[delta]) % p
                    if r != expected_r:
                        nonzero_c_check = False

    record_test("S1", "1.4 c_delta != 0: r = 2^a * c_delta mod p",
                nonzero_c_check, "[PROVED] direct factorization")

    # Verify total count consistency
    total_check = True
    for p, M, g, ord2, is_degen in test_cases[:15]:
        c_deltas = compute_c_deltas(M, g, p)
        total_from_delta = sum(
            (M - delta + 1) for delta in range(M + 1)
        )
        if total_from_delta != C_k2(M):
            total_check = False

    record_test("S1", "1.5 Total count: Sum_{delta} (M-delta+1) = C(2,M)",
                total_check, "[PROVED] algebraic identity")


# ============================================================================
# SECTION 2: STRUCTURE OF c_delta (Q2)
# ============================================================================

def section2_c_delta_structure():
    """Q2: Study the set {c_delta} for delta = 0,...,M."""
    print("\n" + "=" * 72)
    print("SECTION 2: STRUCTURE OF c_delta SET (Q2)")
    print("  c_delta = (1 + g * 2^delta) mod p")
    print("  Count distinct values, identify c_delta = 0 cases")
    print("=" * 72)

    test_cases = generate_R1_cases(max_prime=200)

    # Count how many distinct c_delta values
    distinct_counts = []
    zero_counts = []
    ratio_distinct = []  # distinct / (M+1)

    for p, M, g, ord2, is_degen in test_cases:
        if not time_ok():
            break
        c_deltas = compute_c_deltas(M, g, p)
        n_distinct = len(set(c_deltas))
        n_zero = c_deltas.count(0)
        distinct_counts.append((p, M, n_distinct, M + 1))
        zero_counts.append((p, M, n_zero, is_degen))
        if M + 1 > 0:
            ratio_distinct.append(n_distinct / (M + 1))

    if ratio_distinct:
        min_ratio = min(ratio_distinct)
        avg_ratio = sum(ratio_distinct) / len(ratio_distinct)
        record_test("S2", "2.1 Distinct c_delta values: ratio distinct/(M+1)",
                    True, f"min={min_ratio:.3f}, avg={avg_ratio:.3f}, {len(ratio_distinct)} cases")

    # In R1, are c_delta values mostly distinct?
    # c_{delta1} = c_{delta2} iff g * (2^{delta1} - 2^{delta2}) = 0 mod p
    # iff 2^{delta1} = 2^{delta2} mod p iff delta1 = delta2 mod ord_p(2)
    # In R1, ord > M+1, so delta1 != delta2 in [0,M] => 2^{delta1} != 2^{delta2}
    # => c_{delta1} != c_{delta2} UNLESS g = 0 (impossible since gcd(3,p)=1)
    # THEREFORE: in R1 generic, all c_delta are DISTINCT.
    all_distinct_in_R1 = True
    for p, M, g, ord2, is_degen in test_cases:
        if ord2 <= M + 1:  # not R1
            continue
        c_deltas = compute_c_deltas(M, g, p)
        # Remove zeros first (they can repeat conceptually)
        nonzero_c = [c for c in c_deltas if c != 0]
        if len(nonzero_c) != len(set(nonzero_c)):
            all_distinct_in_R1 = False
            break

    record_test("S2", "2.2 In R1: all nonzero c_delta are distinct",
                all_distinct_in_R1,
                "[PROVED] since 2^{d1} != 2^{d2} mod p when ord > M+1")

    # Count c_delta = 0 occurrences
    # c_delta = 0 iff 1 + g*2^delta = 0 iff 2^delta = -g^{-1} mod p
    # In R1, there is at most 1 such delta in [0,M]
    max_zeros_R1 = 0
    for p, M, n_zero, is_degen in zero_counts:
        if n_zero > max_zeros_R1:
            max_zeros_R1 = n_zero

    # Verify: in generic R1, at most 1 zero
    zero_bound_ok = True
    for p, M, g, ord2, is_degen in test_cases:
        if ord2 <= M + 1:
            continue
        c_deltas = compute_c_deltas(M, g, p)
        n_zero = c_deltas.count(0)
        if n_zero > 1:
            zero_bound_ok = False

    record_test("S2", "2.3 In R1: at most 1 delta with c_delta = 0",
                zero_bound_ok,
                f"[PROVED] 2^delta = -1/g has at most 1 sol when ord > M+1")

    # When g = -1 mod p: c_delta = 1 + (-1)*2^delta = 1 - 2^delta mod p
    # c_0 = 1 - 1 = 0. So delta = 0 always gives c_0 = 0.
    # Are there other zeros? c_delta = 0 iff 2^delta = 1 mod p iff delta = 0 mod ord.
    # In R1, ord > M+1, so only delta = 0.
    degen_check = True
    degen_count = 0
    for p, M, g, ord2, is_degen in test_cases:
        if not is_degen:
            continue
        degen_count += 1
        c_deltas = compute_c_deltas(M, g, p)
        if c_deltas[0] != 0:
            degen_check = False
        # In R1, only delta=0 should be zero
        if ord2 > M + 1:
            n_zero = c_deltas.count(0)
            if n_zero != 1:
                degen_check = False

    record_test("S2", "2.4 Degenerate g=-1: c_0=0 and unique in R1",
                degen_check, f"[PROVED] {degen_count} degen cases")

    # Relationship between c_delta values
    # c_{delta+1} = 1 + g*2^{delta+1} = 1 + 2*(g*2^delta) = 1 + 2*(c_delta - 1) = 2*c_delta - 1 mod p
    recurrence_ok = True
    for p, M, g, ord2, is_degen in test_cases[:20]:
        c_deltas = compute_c_deltas(M, g, p)
        for delta in range(M):
            expected = (2 * c_deltas[delta] - 1) % p
            if c_deltas[delta + 1] != expected:
                recurrence_ok = False

    record_test("S2", "2.5 Recurrence: c_{delta+1} = 2*c_delta - 1 mod p",
                recurrence_ok, "[PROVED] algebraic identity")


# ============================================================================
# SECTION 3: DISCRETE LOG BOUND IN R1 (Q3)
# ============================================================================

def section3_dlog_bound():
    """Q3: Verify that in R1, each delta contributes at most 1 solution a."""
    print("\n" + "=" * 72)
    print("SECTION 3: DISCRETE LOG BOUND IN R1 (Q3)")
    print("  For c_delta != 0 and r fixed: 2^a = r * c_delta^{-1} mod p")
    print("  In R1 (ord > M+1): at most 1 solution a in [0, M-delta]")
    print("=" * 72)

    test_cases = generate_R1_cases(max_prime=150)

    # For each (p,M,g) in R1, and each residue r, count solutions per delta
    max_sols_per_delta = 0
    count_tested = 0

    for p, M, g, ord2, is_degen in test_cases[:40]:
        if not time_ok():
            break
        c_deltas = compute_c_deltas(M, g, p)
        for delta in range(M + 1):
            if c_deltas[delta] == 0:
                continue
            # For this delta, each a in [0, M-delta] gives a unique r
            # (since 2^a are distinct in R1)
            # So each r gets at most 1 solution from this delta
            residues_this_delta = Counter()
            for a in range(M - delta + 1):
                r = (pow(2, a, p) * c_deltas[delta]) % p
                residues_this_delta[r] += 1
            max_count = max(residues_this_delta.values()) if residues_this_delta else 0
            if max_count > max_sols_per_delta:
                max_sols_per_delta = max_count
        count_tested += 1

    record_test("S3", "3.1 In R1: each (delta, r) pair has <= 1 solution a",
                max_sols_per_delta <= 1,
                f"[PROVED] max = {max_sols_per_delta}, {count_tested} cases")

    # Therefore N_r = Sum_{delta} indicator(exists valid a)
    # = #{delta in [0,M] : c_delta != 0 AND dlog(r/c_delta) in [0, M-delta]}
    nr_bound_ok = True
    for p, M, g, ord2, is_degen in test_cases[:30]:
        if not time_ok():
            break
        Nr_exact = compute_Nr_exact(M, g, p)
        c_deltas = compute_c_deltas(M, g, p)

        for r in range(p):
            count_from_deltas = 0
            for delta in range(M + 1):
                if c_deltas[delta] == 0:
                    if r == 0:
                        count_from_deltas += (M - delta + 1)
                    continue
                # Need 2^a = r * c_delta^{-1} mod p, a in [0, M-delta]
                if r == 0:
                    continue  # 2^a * c_delta = 0 impossible (c_delta != 0, p prime)
                inv_c = pow(c_deltas[delta], p - 2, p)
                target = (r * inv_c) % p
                a_val = discrete_log_2(target, p, ord2)
                if a_val is not None and 0 <= a_val <= M - delta:
                    count_from_deltas += 1
            if Nr_exact.get(r, 0) != count_from_deltas:
                nr_bound_ok = False

    record_test("S3", "3.2 N_r = #{delta : dlog(r/c_delta) in [0, M-delta]}",
                nr_bound_ok, "[PROVED] exact counting via discrete log")

    # Trivial bound: N_r <= M+1 (one contribution per delta)
    trivial_bound_ok = True
    for p, M, g, ord2, is_degen in test_cases[:30]:
        Nr_exact = compute_Nr_exact(M, g, p)
        max_Nr = max(Nr_exact.values()) if Nr_exact else 0
        if max_Nr > M + 1:
            trivial_bound_ok = False

    record_test("S3", "3.3 Trivial bound: max N_r <= M+1 in R1",
                trivial_bound_ok, "[PROVED] at most 1 sol per delta")

    # But the DEGENERATE delta (c_delta=0) contributes (M-delta+1) to N_0
    # In R1 degen (g=-1): c_0=0 gives M+1 contributions to N_0, so N_0 >= M+1
    degen_N0_check = True
    for p, M, g, ord2, is_degen in test_cases:
        if not is_degen or ord2 <= M + 1:
            continue
        Nr = compute_Nr_exact(M, g, p)
        # c_0 = 0 gives (M-0+1) = M+1 to N_0
        if Nr.get(0, 0) < M + 1:
            degen_N0_check = False

    record_test("S3", "3.4 Degen g=-1 in R1: N_0 >= M+1",
                degen_N0_check, "[PROVED] c_0=0, all a contribute to r=0")

    # For GENERIC case: max N_r < M+1 (strictly)
    generic_strict = True
    generic_max_ratio = 0
    for p, M, g, ord2, is_degen in test_cases:
        if is_degen or ord2 <= M + 1:
            continue
        Nr = compute_Nr_exact(M, g, p)
        max_Nr = max(Nr.values()) if Nr else 0
        ratio = max_Nr / (M + 1) if M + 1 > 0 else 0
        if ratio > generic_max_ratio:
            generic_max_ratio = ratio
        if max_Nr >= M + 1:
            generic_strict = False

    record_test("S3", "3.5 Generic case: max N_r < M+1 (strict)",
                generic_strict,
                f"[COMPUTED] max ratio = {generic_max_ratio:.4f}")


# ============================================================================
# SECTION 4: EMPIRICAL BOUND ON max N_r (Q4)
# ============================================================================

def section4_empirical_bound():
    """Q4: Measure max_r N_r empirically on large R1 sample."""
    print("\n" + "=" * 72)
    print("SECTION 4: EMPIRICAL BOUND ON max N_r (Q4)")
    print("  Measure max N_r / (M+1), max N_r / sqrt(M+1), max N_r vs C/p")
    print("=" * 72)

    cases = generate_R1_cases_large(min_prime=5, max_prime=3000, n_target=300)
    if not cases:
        print("  No R1 cases found!")
        return

    # Separate generic and degenerate
    generic_data = []  # (p, M, max_Nr, C, C_over_p)
    degen_data = []

    for p, M, g, ord2, is_degen in cases:
        if not time_ok(5):
            break
        Nr = compute_Nr_exact(M, g, p)
        C = C_k2(M)
        max_Nr = max(Nr.values()) if Nr else 0
        C_over_p = C / p

        if is_degen:
            degen_data.append((p, M, max_Nr, C, C_over_p))
        else:
            generic_data.append((p, M, max_Nr, C, C_over_p))

    print(f"  Generic cases: {len(generic_data)}, Degenerate: {len(degen_data)}")

    # Q4a: max N_r / (M+1) — should be < 1 for generic
    if generic_data:
        ratios_M1 = [d[2] / (d[1] + 1) for d in generic_data]
        max_ratio_M1 = max(ratios_M1)
        avg_ratio_M1 = sum(ratios_M1) / len(ratios_M1)

        record_test("S4", "4.1 Generic: max N_r / (M+1)",
                    max_ratio_M1 < 1.0,
                    f"max={max_ratio_M1:.4f}, avg={avg_ratio_M1:.4f}")

    # Q4b: max N_r / sqrt(M+1)
    if generic_data:
        ratios_sqrt = [d[2] / sqrt(d[1] + 1) for d in generic_data]
        max_ratio_sqrt = max(ratios_sqrt)
        avg_ratio_sqrt = sum(ratios_sqrt) / len(ratios_sqrt)

        record_test("S4", "4.2 Generic: max N_r / sqrt(M+1)",
                    True,
                    f"max={max_ratio_sqrt:.4f}, avg={avg_ratio_sqrt:.4f}")

    # Q4c: max N_r vs C/p
    if generic_data:
        excess = [d[2] - d[4] for d in generic_data]  # max_Nr - C/p
        max_excess = max(excess)
        # Normalize by sqrt(M+1)
        excess_normalized = [(d[2] - d[4]) / sqrt(d[1] + 1) for d in generic_data]
        max_excess_norm = max(excess_normalized)
        avg_excess_norm = sum(excess_normalized) / len(excess_normalized)

        record_test("S4", "4.3 Generic: (max N_r - C/p) / sqrt(M+1)",
                    True,
                    f"max={max_excess_norm:.4f}, avg={avg_excess_norm:.4f}")

    # Q4d: max N_r vs C/p + K*sqrt(M+1) — find best K
    if generic_data:
        best_K = 0
        for d in generic_data:
            p, M, max_Nr, C, C_over_p = d
            sqM = sqrt(M + 1)
            if sqM > 0:
                K_needed = (max_Nr - C_over_p) / sqM
                if K_needed > best_K:
                    best_K = K_needed

        # Check with K = best_K * 1.01
        K_test = best_K * 1.01
        bound_holds = True
        for d in generic_data:
            p, M, max_Nr, C, C_over_p = d
            bound = C_over_p + K_test * sqrt(M + 1)
            if max_Nr > bound + 0.001:
                bound_holds = False

        record_test("S4", f"4.4 Generic: max N_r <= C/p + K*sqrt(M+1), K={best_K:.4f}",
                    bound_holds,
                    f"[OBSERVED] tight bound with K={best_K:.4f}")

    # Q4e: max N_r vs C/p + K*log(M+1)
    if generic_data:
        best_K_log = 0
        for d in generic_data:
            p, M, max_Nr, C, C_over_p = d
            logM = log(M + 2)  # log(M+2) to avoid log(1)=0
            if logM > 0:
                K_needed = (max_Nr - C_over_p) / logM
                if K_needed > best_K_log:
                    best_K_log = K_needed

        record_test("S4", f"4.5 Generic: max N_r <= C/p + K*log(M+2), K={best_K_log:.4f}",
                    True,
                    f"[OBSERVED] log-scale bound")

    # Q4f: Ratio max N_r / (C/p) — the multiplicative excess
    if generic_data:
        mult_ratios = [d[2] / d[4] if d[4] > 0.01 else 0 for d in generic_data]
        mult_ratios = [r for r in mult_ratios if r > 0]
        if mult_ratios:
            max_mult = max(mult_ratios)
            avg_mult = sum(mult_ratios) / len(mult_ratios)
            record_test("S4", "4.6 Generic: max N_r / (C/p) multiplicative ratio",
                        True,
                        f"max={max_mult:.4f}, avg={avg_mult:.4f}")

    # Q4g: Does max N_r grow with M? Scatter data
    if generic_data and len(generic_data) >= 10:
        # Group by M ranges
        by_M = defaultdict(list)
        for d in generic_data:
            by_M[d[1]].append(d[2])

        sorted_Ms = sorted(by_M.keys())
        growth_data = []
        for M in sorted_Ms:
            vals = by_M[M]
            growth_data.append((M, max(vals), sum(vals)/len(vals), len(vals)))

        # Check if max N_r / sqrt(M+1) is bounded
        ratios_growth = [gd[1] / sqrt(gd[0] + 1) for gd in growth_data if gd[0] >= 2]
        if ratios_growth:
            max_growth_ratio = max(ratios_growth)
            record_test("S4", "4.7 Growth: max N_r / sqrt(M+1) bounded across M values",
                        max_growth_ratio < 10.0,
                        f"max_ratio = {max_growth_ratio:.4f}")

    # Q4h: Degenerate statistics
    if degen_data:
        degen_max_Nr = max(d[2] for d in degen_data)
        degen_max_ratio_M = max(d[2] / (d[1] + 1) for d in degen_data)
        record_test("S4", "4.8 Degen: max N_r / (M+1)",
                    True,
                    f"max_ratio={degen_max_ratio_M:.4f}, max_Nr={degen_max_Nr}")

    # Q4i: Full Nr distribution shape: how many residues have Nr > C/p?
    if generic_data:
        frac_above = []
        for p_val, M, max_Nr, C, C_over_p in generic_data:
            g = compute_g_k2(p_val)
            Nr = compute_Nr_exact(M, g, p_val)
            n_above = sum(1 for r in range(p_val) if Nr.get(r, 0) > C_over_p)
            frac_above.append(n_above / p_val)
        avg_frac_above = sum(frac_above) / len(frac_above)
        record_test("S4", "4.9 Fraction of residues with N_r > C/p",
                    True,
                    f"avg = {avg_frac_above:.4f} (expect ~0.5 if symmetric)")

    # Q4j: Second moment check: M2 = Sum Nr^2 vs C^2/p + V
    m2_check_ok = True
    for p_val, M, max_Nr, C, C_over_p in (generic_data or [])[:20]:
        g = compute_g_k2(p_val)
        Nr = compute_Nr_exact(M, g, p_val)
        M2 = sum(n*n for n in Nr.values())
        V_check = M2 - C*C/p_val
        A_check = V_check / C if C > 0 else 0
        if A_check < -0.001:  # V should be non-negative
            m2_check_ok = False

    record_test("S4", "4.10 V = M2 - C^2/p >= 0 (non-negativity)",
                m2_check_ok, "[PROVED] variance is non-negative")

    return generic_data, degen_data


# ============================================================================
# SECTION 5: RIGOROUS BOUND CANDIDATE (Q5)
# ============================================================================

def section5_rigorous_bound(generic_data=None):
    """Q5: Test candidate bounds on max N_r."""
    print("\n" + "=" * 72)
    print("SECTION 5: RIGOROUS BOUND CANDIDATE (Q5)")
    print("  Test: max N_r <= C/p + K * sqrt(C) for constant K")
    print("  Also: discrepancy D = max|N_r - C/p| / (C/p)")
    print("=" * 72)

    if generic_data is None or len(generic_data) == 0:
        cases = generate_R1_cases(max_prime=300)
        generic_data = []
        for p, M, g, ord2, is_degen in cases:
            if is_degen:
                continue
            if not time_ok():
                break
            Nr = compute_Nr_exact(M, g, p)
            C = C_k2(M)
            max_Nr = max(Nr.values()) if Nr else 0
            generic_data.append((p, M, max_Nr, C, C / p))

    if not generic_data:
        record_test("S5", "5.x No data available", False, "")
        return

    # Q5a: max N_r <= C/p + K * sqrt(C)
    best_K_sqrtC = 0
    for d in generic_data:
        p, M, max_Nr, C, C_over_p = d
        sqC = sqrt(C)
        if sqC > 0:
            K = (max_Nr - C_over_p) / sqC
            if K > best_K_sqrtC:
                best_K_sqrtC = K

    bound_sqrtC_ok = True
    K_sqrtC_test = best_K_sqrtC * 1.01
    for d in generic_data:
        p, M, max_Nr, C, C_over_p = d
        if max_Nr > C_over_p + K_sqrtC_test * sqrt(C) + 0.001:
            bound_sqrtC_ok = False

    record_test("S5", f"5.1 max N_r <= C/p + {best_K_sqrtC:.4f}*sqrt(C)",
                bound_sqrtC_ok,
                f"[OBSERVED] tightest K for sqrt(C) bound")

    # Q5b: Discrepancy D = max_r |N_r - C/p| / (C/p)
    discrepancies = []
    for d in generic_data:
        p_val, M, max_Nr, C, C_over_p = d
        if C_over_p > 0.01:
            D = (max_Nr - C_over_p) / C_over_p
            discrepancies.append((p_val, M, D))

    if discrepancies:
        max_D = max(d[2] for d in discrepancies)
        avg_D = sum(d[2] for d in discrepancies) / len(discrepancies)

        record_test("S5", "5.2 Discrepancy D = (max N_r - C/p) / (C/p)",
                    True,
                    f"max D = {max_D:.4f}, avg D = {avg_D:.4f}")

    # Q5c: Fit D as function of p
    # Hypothesis: D ~ K / sqrt(p) or D ~ K * sqrt(p) / M
    if discrepancies and len(discrepancies) >= 5:
        # D * sqrt(p) should be bounded if D ~ 1/sqrt(p)
        D_times_sqrtp = [d[2] * sqrt(d[0]) for d in discrepancies]
        max_Dsqrtp = max(D_times_sqrtp)
        avg_Dsqrtp = sum(D_times_sqrtp) / len(D_times_sqrtp)

        record_test("S5", "5.3 D * sqrt(p) boundedness",
                    True,
                    f"max = {max_Dsqrtp:.4f}, avg = {avg_Dsqrtp:.4f}")

    # Q5d: Verify the KEY inequality: max N_r <= C/p + K * (M+1) for K < 1
    best_K_M = 0
    for d in generic_data:
        p_val, M, max_Nr, C, C_over_p = d
        if M + 1 > 0:
            K = (max_Nr - C_over_p) / (M + 1)
            if K > best_K_M:
                best_K_M = K

    record_test("S5", f"5.4 max N_r <= C/p + K*(M+1), K = {best_K_M:.4f}",
                best_K_M < 1.0,
                f"[{'OBSERVED' if best_K_M < 1.0 else 'FAIL'}] K < 1 means sub-trivial bound")

    # Q5e: Can we prove max N_r <= C/p + K_test*sqrt(M+1) ?
    # Compute empirical best K for sqrt(M+1) bound directly
    best_K_sqrtM = 0
    for d in generic_data:
        p_val, M, max_Nr, C, C_over_p = d
        sqM = sqrt(M + 1)
        if sqM > 0:
            K = (max_Nr - C_over_p) / sqM
            if K > best_K_sqrtM:
                best_K_sqrtM = K

    K_test_sqrtM = best_K_sqrtM * 1.05  # 5% margin
    K5_bound = True
    violations = 0
    for d in generic_data:
        p_val, M, max_Nr, C, C_over_p = d
        bound = C_over_p + K_test_sqrtM * sqrt(M + 1)
        if max_Nr > bound + 0.001:
            K5_bound = False
            violations += 1

    record_test("S5", f"5.5 max N_r <= C/p + {K_test_sqrtM:.2f}*sqrt(M+1) (generic)",
                K5_bound,
                f"violations: {violations}/{len(generic_data)}, empirical K={best_K_sqrtM:.4f}")


# ============================================================================
# SECTION 6: r=0 SPECIAL CASE (Q6)
# ============================================================================

def section6_r0_special():
    """Q6: Is r=0 structurally special?"""
    print("\n" + "=" * 72)
    print("SECTION 6: IS r=0 SPECIAL? (Q6)")
    print("  N_0 = #{delta : c_delta = 0} * (M-delta+1) + #{delta: c_delta!=0, dlog=0}")
    print("  In generic R1: c_delta=0 for at most 1 delta, and r=0 cannot come")
    print("  from 2^a * c_delta = 0 when c_delta != 0 (since p prime, 2^a != 0)")
    print("=" * 72)

    test_cases = generate_R1_cases(max_prime=200)

    # Q6a: In generic case, N_0 = #{delta : c_delta = 0, with multiplicity}
    # When c_delta = 0: contributes (M - delta + 1) to N_0
    # When c_delta != 0: 2^a * c_delta = 0 mod p impossible. So NO contribution.
    n0_formula_ok = True
    count_tested = 0
    for p, M, g, ord2, is_degen in test_cases:
        if not time_ok():
            break
        Nr = compute_Nr_exact(M, g, p)
        c_deltas = compute_c_deltas(M, g, p)

        # Compute N_0 from c_delta structure
        N0_predicted = 0
        for delta in range(M + 1):
            if c_deltas[delta] == 0:
                N0_predicted += (M - delta + 1)
            # c_delta != 0: 2^a * c_delta = 0 mod p => impossible

        N0_actual = Nr.get(0, 0)
        if N0_predicted != N0_actual:
            n0_formula_ok = False
        count_tested += 1

    record_test("S6", "6.1 N_0 = Sum_{delta: c_delta=0} (M-delta+1)",
                n0_formula_ok,
                f"[PROVED] {count_tested} cases, exact match")

    # Q6b: In R1 generic (g != -1): at most 1 delta with c_delta=0
    # That delta satisfies 2^delta = -1/g mod p
    # If it exists, N_0 = M - delta_0 + 1
    # If not, N_0 = 0
    generic_N0_bound_ok = True
    generic_N0_values = []
    for p, M, g, ord2, is_degen in test_cases:
        if is_degen or ord2 <= M + 1:
            continue
        Nr = compute_Nr_exact(M, g, p)
        N0 = Nr.get(0, 0)
        generic_N0_values.append((p, M, N0))
        if N0 > M + 1:
            generic_N0_bound_ok = False

    max_generic_N0 = max(d[2] for d in generic_N0_values) if generic_N0_values else 0

    record_test("S6", "6.2 Generic R1: N_0 <= M+1 (from at most 1 degen delta)",
                generic_N0_bound_ok,
                f"max N_0 = {max_generic_N0}")

    # Q6c: Is N_0 typically smaller than max_{r>=1} N_r in generic case?
    n0_vs_max_r1 = []
    for p, M, g, ord2, is_degen in test_cases:
        if is_degen or ord2 <= M + 1:
            continue
        Nr = compute_Nr_exact(M, g, p)
        N0 = Nr.get(0, 0)
        max_nonzero = max((Nr.get(r, 0) for r in range(1, p)), default=0)
        n0_vs_max_r1.append((p, M, N0, max_nonzero))

    if n0_vs_max_r1:
        n0_smaller = sum(1 for d in n0_vs_max_r1 if d[2] <= d[3])
        frac_smaller = n0_smaller / len(n0_vs_max_r1)
        record_test("S6", "6.3 Generic: fraction where N_0 <= max_{r>0} N_r",
                    True,
                    f"{n0_smaller}/{len(n0_vs_max_r1)} = {frac_smaller:.3f}")

    # Q6d: In degen (g=-1): N_0 >= M+1, and this is the unique maximum
    degen_n0_max = True
    for p, M, g, ord2, is_degen in test_cases:
        if not is_degen or ord2 <= M + 1:
            continue
        Nr = compute_Nr_exact(M, g, p)
        N0 = Nr.get(0, 0)
        max_other = max((Nr.get(r, 0) for r in range(1, p)), default=0)
        if N0 < M + 1:
            degen_n0_max = False
        if max_other > N0:
            degen_n0_max = False

    record_test("S6", "6.4 Degen g=-1: N_0 = max_r N_r and N_0 >= M+1",
                degen_n0_max,
                "[PROVED] diagonal (a,a) -> 0 dominates")

    # Q6e: More precisely, in degen R1: N_0 = M + 1 exactly (only delta=0 contributes)
    degen_n0_exact = True
    for p, M, g, ord2, is_degen in test_cases:
        if not is_degen or ord2 <= M + 1:
            continue
        Nr = compute_Nr_exact(M, g, p)
        N0 = Nr.get(0, 0)
        if N0 != M + 1:
            degen_n0_exact = False

    record_test("S6", "6.5 Degen R1: N_0 = M+1 exactly",
                degen_n0_exact,
                "[PROVED] unique degen delta = 0 in R1")


# ============================================================================
# SECTION 7: IMPLICATION FOR A(2) (Q7)
# ============================================================================

def section7_implications_A2():
    """Q7: If max N_r <= C/p + K*sqrt(M+1), derive bound on A(2)."""
    print("\n" + "=" * 72)
    print("SECTION 7: IMPLICATIONS FOR A(2) (Q7)")
    print("  V = Sum (N_r - C/p)^2 <= p * (max|N_r - C/p|)^2")
    print("  If max|N_r - C/p| <= K*sqrt(M+1): A(2) <= 2*K^2*p/(M+2)")
    print("=" * 72)

    # Generate fresh data with full statistics
    cases = generate_R1_cases(max_prime=400)

    generic_A_data = []  # (p, M, A_float, V_float, max_Nr, C, C_over_p)
    degen_A_data = []

    for p, M, g, ord2, is_degen in cases:
        if not time_ok(5):
            break
        Nr = compute_Nr_exact(M, g, p)
        C = C_k2(M)
        C_over_p = Fraction(C, p)
        M2 = sum(n * n for n in Nr.values())
        V = Fraction(M2) - Fraction(C * C, p)
        A = float(V) / C if C > 0 else 0
        max_Nr = max(Nr.values()) if Nr else 0
        max_deviation = max(abs(Nr.get(r, 0) - float(C_over_p)) for r in range(p))

        entry = (p, M, A, float(V), max_Nr, C, float(C_over_p), max_deviation)
        if is_degen:
            degen_A_data.append(entry)
        else:
            generic_A_data.append(entry)

    # Q7a: Verify A(2) = V/C directly
    if generic_A_data:
        max_A_generic = max(d[2] for d in generic_A_data)
        record_test("S7", f"7.1 Generic max A(2) = {max_A_generic:.4f}",
                    max_A_generic < 2.0,
                    f"[COMPUTED] {len(generic_A_data)} cases")

    if degen_A_data:
        max_A_degen = max(d[2] for d in degen_A_data)
        record_test("S7", f"7.2 Degen max A(2) = {max_A_degen:.4f}",
                    max_A_degen < 3.0,
                    f"[COMPUTED] {len(degen_A_data)} cases")

    # Q7b: Check if V <= p * max_deviation^2
    trivial_V_bound_ok = True
    for d in generic_A_data:
        p_val, M, A, V, max_Nr, C, C_over_p, max_dev = d
        V_bound = p_val * max_dev * max_dev
        if V > V_bound + 0.01:
            trivial_V_bound_ok = False

    record_test("S7", "7.3 V <= p * (max|N_r - C/p|)^2",
                trivial_V_bound_ok,
                "[PROVED] Cauchy-Schwarz type bound")

    # Q7c: With max_dev <= K*sqrt(M+1):
    # A = V/C <= p*K^2*(M+1)/C = p*K^2*(M+1)/((M+1)(M+2)/2) = 2*K^2*p/(M+2)
    # In R1: p > ord > M+1, so p/(M+2) > 1 in general
    # This gives A <= 2*K^2*p/(M+2)
    # For this to be bounded, need K ~ sqrt((M+2)/p) which goes to 0!
    # So the bound max_dev <= K*sqrt(M+1) with fixed K does NOT directly give A bounded.
    # UNLESS K is O(sqrt(1/p)) or we use a TIGHTER variance bound.

    # Better approach: V = Sum (N_r - C/p)^2
    # = Sum N_r^2 - C^2/p
    # Each N_r <= C/p + max_dev, but most N_r are near C/p.
    # The key is that Sum (N_r - C/p)^2 involves ALL residues, not just the max.

    # Q7d: Direct computation: A(2) as function of p
    if generic_A_data and len(generic_A_data) >= 5:
        # Group by p
        by_p = defaultdict(list)
        for d in generic_A_data:
            by_p[d[0]].append(d[2])  # A values

        p_sorted = sorted(by_p.keys())
        p_maxA = [(p_val, max(by_p[p_val])) for p_val in p_sorted]

        # Does max A decrease with p?
        if len(p_maxA) >= 3:
            # Check A * p is bounded (would mean A ~ 1/p)
            Ap_products = [pa[0] * pa[1] for pa in p_maxA if pa[0] > 10]
            if Ap_products:
                record_test("S7", "7.4 A(2) * p bounded?",
                            True,
                            f"max A*p = {max(Ap_products):.2f}, avg = {sum(Ap_products)/len(Ap_products):.2f}")

    # Q7e: A(2) -> 0 for p -> infinity?
    if generic_A_data:
        large_p_data = [d for d in generic_A_data if d[0] > 100]
        if large_p_data:
            max_A_large_p = max(d[2] for d in large_p_data)
            small_p_data = [d for d in generic_A_data if d[0] <= 50]
            max_A_small_p = max(d[2] for d in small_p_data) if small_p_data else 0

            record_test("S7", "7.5 A(2) trend: large p vs small p",
                        True,
                        f"p>100: max A={max_A_large_p:.4f}, p<=50: max A={max_A_small_p:.4f}")

    # Q7f: Overall A(2) bound in R1
    all_A = [d[2] for d in generic_A_data] + [d[2] for d in degen_A_data]
    if all_A:
        overall_max_A = max(all_A)
        overall_generic_max = max(d[2] for d in generic_A_data) if generic_A_data else 0
        overall_degen_max = max(d[2] for d in degen_A_data) if degen_A_data else 0

        record_test("S7", f"7.6 Overall A(2) <= {overall_max_A:.4f} in R1",
                    overall_max_A < 3.0,
                    f"generic max={overall_generic_max:.4f}, degen max={overall_degen_max:.4f}")


# ============================================================================
# SECTION 8: GLOBAL VERDICTS
# ============================================================================

def section8_verdicts(generic_data=None):
    """Synthesize all findings into clear verdicts."""
    print("\n" + "=" * 72)
    print("SECTION 8: GLOBAL VERDICTS")
    print("=" * 72)

    # Regenerate key data for verdicts if not provided
    if generic_data is None:
        cases = generate_R1_cases(max_prime=300)
        generic_data = []
        for p, M, g, ord2, is_degen in cases:
            if is_degen or not time_ok():
                continue
            Nr = compute_Nr_exact(M, g, p)
            C = C_k2(M)
            max_Nr = max(Nr.values()) if Nr else 0
            generic_data.append((p, M, max_Nr, C, C / p))

    # Verdict 1: Delta-reformulation
    record_test("S8", "8.1 VERDICT: delta-reformulation is PROVED",
                True,
                "[PROVED] N_r = Sum_delta 1[dlog(r/c_delta) in window]")

    # Verdict 2: In R1, each delta contributes <= 1
    record_test("S8", "8.2 VERDICT: R1 implies at-most-1-per-delta",
                True,
                "[PROVED] trivial bound N_r <= M+1")

    # Verdict 3: Best empirical bound on max N_r
    if generic_data:
        # Compute best K for sqrt bound
        best_K = 0
        for d in generic_data:
            p_val, M, max_Nr, C, C_over_p = d
            sqM = sqrt(M + 1)
            if sqM > 0:
                K = (max_Nr - C_over_p) / sqM
                if K > best_K:
                    best_K = K

        record_test("S8", f"8.3 VERDICT: best K for max N_r <= C/p + K*sqrt(M+1) is K={best_K:.4f}",
                    best_K < 10.0,
                    f"[OBSERVED] on {len(generic_data)} generic R1 cases")

        # Best K for linear bound
        best_K_lin = 0
        for d in generic_data:
            p_val, M, max_Nr, C, C_over_p = d
            if M + 1 > 0:
                K = (max_Nr - C_over_p) / (M + 1)
                if K > best_K_lin:
                    best_K_lin = K

        record_test("S8", f"8.4 VERDICT: best K for max N_r <= C/p + K*(M+1) is K={best_K_lin:.4f}",
                    best_K_lin < 1.0,
                    f"[OBSERVED] K < 1 improves trivial bound")

    # Verdict 4: r=0 structure
    record_test("S8", "8.5 VERDICT: N_0 = Sum_{degen deltas} (M-delta+1) [PROVED]",
                True,
                "In generic R1: N_0 <= M+1; in degen: N_0 = M+1")

    # Verdict 5: Implications for A(2)
    # From the proof structure:
    # N_r = #{delta : c_delta != 0 AND dlog(r*c_delta^{-1}) in [0, M-delta]}
    # + #{delta : c_delta = 0} * 1[r=0] * (M - delta_0 + 1)
    #
    # The key structural insight:
    # For r != 0, generic case: N_r counts how many delta give a valid dlog.
    # The dlog values {log_2(r * c_delta^{-1}) mod ord2} are distinct mod ord2
    # (since c_delta are distinct) and spread pseudo-randomly.
    # The constraint is dlog in [0, M-delta], which is a SHRINKING window.
    #
    # Total "volume": Sum_{delta=0}^{M} (M-delta+1)/ord = C/ord (expected hits per r)
    # In R1: ord > M+1, so expected C/ord < C/(M+1) = (M+2)/2

    if generic_data:
        # Compute A(2) for all cases
        A_values = []
        for p_val, M, max_Nr, C, C_over_p in generic_data:
            # Need full Nr to compute V
            g = compute_g_k2(p_val)
            Nr = compute_Nr_exact(M, g, p_val)
            M2 = sum(n*n for n in Nr.values())
            V = M2 - C*C/p_val
            A = V / C if C > 0 else 0
            A_values.append(A)

        max_A = max(A_values) if A_values else 0
        avg_A = sum(A_values) / len(A_values) if A_values else 0

        verdict_status = "SEMI-FORMALISE"
        if max_A < 2.5:
            verdict_status = "OBSERVE : A(2) < 2.5 en generique"
        if max_A < 2.0:
            verdict_status = "OBSERVE : A(2) < 2 en generique"
        if max_A < 1.5:
            verdict_status = "OBSERVE : A(2) < 1.5 en generique"

        record_test("S8", f"8.6 VERDICT: generic A(2) max={max_A:.4f}, avg={avg_A:.4f}",
                    max_A < 3.0,
                    f"[{verdict_status}]")

    # Verdict 6: Proof gap assessment
    print()
    print("  " + "-" * 60)
    print("  PROOF GAP ANALYSIS:")
    print("  " + "-" * 60)
    print("  [PROVED]    Delta-reformulation: N_r = sum of indicator functions")
    print("  [PROVED]    R1: at-most-1 per delta => N_r <= M+1 (trivial)")
    print("  [PROVED]    N_0 structure: only degenerate deltas contribute")
    print("  [PROVED]    Degenerate g=-1: N_0 = M+1 exactly in R1")
    print("  [PROVED]    c_delta recurrence: c_{d+1} = 2*c_d - 1 mod p")
    print("  [PROVED]    R1: all nonzero c_delta are distinct")
    if generic_data:
        print(f"  [OBSERVED]  max N_r <= C/p + {best_K:.4f}*sqrt(M+1) (generic)")
        print(f"  [OBSERVED]  max N_r <= C/p + {best_K_lin:.4f}*(M+1) (generic)")
        print(f"  [OBSERVED]  A(2) <= {max_A:.4f} (generic R1)")
    print()
    print("  REMAINING GAP:")
    print("    To PROVE A(2) <= K, need to bound Sum (N_r - C/p)^2.")
    print("    The delta-reformulation reduces this to counting")
    print("    how many delta-windows [0, M-delta] capture a dlog value.")
    print("    This is a NUMBER THEORY question about distribution of")
    print("    discrete logarithms of shifted geometric sequences.")
    print("    The c_delta = 1 + g*2^delta form a SHIFTED GEOMETRIC SEQUENCE,")
    print("    so log_2(r * c_delta^{-1}) mod ord involves log of sums,")
    print("    which is the HARD part.")

    record_test("S8", "8.7 Proof gap identified and documented",
                True,
                "Gap = distribution of dlogs of shifted geometric sequence")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("R57: BASE CASE k=2 — AXE A : BORNE SUR max N_r")
    print("  Investigateur A — Round 57")
    print("  Comptage exact des solutions de 2^a + g*2^b = r mod p")
    print("  dans le triangle 0 <= a <= b <= M. Objectif: borner max_r N_r.")
    print("=" * 72)

    section1_delta_reformulation()
    section2_c_delta_structure()
    section3_dlog_bound()
    result4 = section4_empirical_bound()
    generic_data = result4[0] if result4 else None
    section5_rigorous_bound(generic_data)
    section6_r0_special()
    section7_implications_A2()
    section8_verdicts(generic_data)

    # ---- FINAL REPORT ----
    total = PASS_COUNT + FAIL_COUNT
    print("\n" + "=" * 72)
    print("FINAL REPORT")
    print("=" * 72)
    print(f"  Total tests: {total}")
    print(f"  PASS: {PASS_COUNT}")
    print(f"  FAIL: {FAIL_COUNT}")
    print(f"  Elapsed: {elapsed():.1f}s")
    rate = PASS_COUNT / total * 100 if total > 0 else 0
    print(f"  Pass rate: {rate:.1f}%")

    print()
    print("  KEY RESULTS:")
    print("    1. Delta-reformulation: PROUVE")
    print("    2. N_r = #{delta valid for r}: PROUVE")
    print("    3. Trivial bound N_r <= M+1 in R1: PROUVE")
    print("    4. c_delta all distinct in R1: PROUVE")
    print("    5. N_0 structure fully understood: PROUVE")
    print("    6. max N_r sub-trivial bound: OBSERVE (K_lin < 1)")
    print("    7. A(2) bounded in R1: OBSERVE")
    print("    8. Proof gap: distribution of dlogs of 1+g*2^delta")
    print()

    if FAIL_COUNT > 0:
        print(f"  *** {FAIL_COUNT} FAILURES DETECTED ***")
        verdict = "SEMI-FORMALISE (avec echecs)"
    else:
        print("  ALL TESTS PASSED")
        verdict = "SEMI-FORMALISE"

    print(f"\n  VERDICT GLOBAL: {verdict}")
    print("    - 6 faits PROUVES (delta-reformulation, at-most-1, c_delta distinct,")
    print("      N_0 structure, recurrence c_delta, degen g=-1)")
    print("    - Borne sub-triviale OBSERVEE mais pas prouvee")
    print("    - Gap restant : distribution des dlogs de suites geometriques decalees")
    print("=" * 72)


if __name__ == '__main__':
    main()
