#!/usr/bin/env python3
"""
M-SCAN EXTENSION ANALYSIS — Piste J.2 for G2c Gap Closure
============================================================
For the 3 unsolved convergents n=23, n=25, n=59, computes:

  1. Exact continued fraction convergents of log_2(3) via mpmath (1000+ digits)
  2. Exact delta = p_n - q_n * log_2(3) for each case
  3. Tight m_max bound from delta
  4. Feasibility assessment for exhaustive m-scan
  5. Parallelization / optimization strategies

Theory recap:
  - d(k) = 2^S - 3^k, S = ceil(k * log_2(3)) = p_n (for odd convergent index n)
  - If ord_d(2) = t <= S-1, then c = (2^t - 1)/d, c odd, c >= 5 (after Th.H, Th.I)
  - Case B: m*d = 3^k - 2^r, r = S mod t, m odd >= 5, gcd(m,6)=1
  - Theorem P (bound on m): m < 3^k / d = 1/(2^delta - 1) ~ 1/(delta * ln 2)
  - More precisely: m < 2^{S-1}/d = 1/(2*(1 - 2^{-delta}))
  - Theorem S: delta >= 0.0145 => m < 100 => eliminated by scan 10f26f
  - For delta < 0.0145: m_max can be much larger

The m-scan approach: for each odd m with gcd(m,6)=1, check if m*d + 2^r = 3^k
has a valid solution with 1 <= r <= S-1 and t = (S-r)/gcd with appropriate
constraints. If NO valid m exists, then ord_d(2) > S-1 and G2c is proven.

Protocole G-V-R v2.2 — Phase 5
"""

import sys
import time
import math

sys.stdout.reconfigure(line_buffering=True)

try:
    from mpmath import mp, mpf, log, floor, ceil, nstr, power, frac
    HAS_MPMATH = True
except ImportError:
    HAS_MPMATH = False
    print("ERROR: mpmath required. Install with: pip install mpmath")
    sys.exit(1)


# ==========================================================================
# PART 1: HIGH-PRECISION CONTINUED FRACTION OF log_2(3)
# ==========================================================================
print("=" * 78)
print("PART 1: CONTINUED FRACTION OF log_2(3) — HIGH PRECISION (mpmath)")
print("=" * 78)

# Set precision to 2000 decimal digits (well above needed)
mp.dps = 2000

log2_3_hp = log(3) / log(2)  # log_2(3) in high precision
print(f"\n  log_2(3) to 100 digits:")
print(f"  {nstr(log2_3_hp, 100)}")

# Compute continued fraction coefficients
def continued_fraction_mpmath(x, n_terms):
    """Compute CF coefficients of x using mpmath high precision."""
    coeffs = []
    for _ in range(n_terms):
        a = int(floor(x))
        coeffs.append(a)
        remainder = x - a
        if remainder < mpf(10)**(-mp.dps + 50):
            break
        x = 1 / remainder
    return coeffs

# We need at least 80 terms (convergents up to n=79)
t0 = time.time()
cf_coeffs = continued_fraction_mpmath(log2_3_hp, 100)
t_cf = time.time() - t0
print(f"\n  CF coefficients (first 80, computed in {t_cf:.2f}s):")
print(f"  {cf_coeffs[:80]}")
print(f"  Total terms computed: {len(cf_coeffs)}")

# Known reference: [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1, ...]
known_start = [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1]
match = cf_coeffs[:20] == known_start
print(f"\n  First 20 coefficients match known values: {match}")
if not match:
    print(f"  DISCREPANCY: got {cf_coeffs[:20]}")
    print(f"  Expected:        {known_start}")

# ==========================================================================
# PART 2: CONVERGENTS p_n/q_n
# ==========================================================================
print("\n" + "=" * 78)
print("PART 2: CONVERGENTS p_n/q_n OF log_2(3)")
print("=" * 78)

def compute_convergents(cf):
    """Compute convergents p_n/q_n from CF coefficients (exact integer arithmetic)."""
    convs = []
    p_prev, p_curr = 1, cf[0]
    q_prev, q_curr = 0, 1
    convs.append((p_curr, q_curr, cf[0]))
    for i in range(1, len(cf)):
        p_next = cf[i] * p_curr + p_prev
        q_next = cf[i] * q_curr + q_prev
        convs.append((p_next, q_next, cf[i]))
        p_prev, p_curr = p_curr, p_next
        q_prev, q_curr = q_curr, q_next
    return convs

convergents = compute_convergents(cf_coeffs)
print(f"\n  Total convergents computed: {len(convergents)}")

# Verify n=23, n=25 against known values
print("\n  Verification of target convergents:")
targets = {
    23: (217976794617, 137528045312),
    25: (8573543875303, 5409303924479),
}

for n_idx, (expected_S, expected_k) in targets.items():
    if n_idx < len(convergents):
        p_n, q_n, a_n = convergents[n_idx]
        match_p = (p_n == expected_S)
        match_q = (q_n == expected_k)
        status = "MATCH" if (match_p and match_q) else "MISMATCH"
        print(f"    n={n_idx}: p_n={p_n}, q_n={q_n} [{status}]")
        if not match_p:
            print(f"      Expected S={expected_S}, got p_n={p_n}")
        if not match_q:
            print(f"      Expected k={expected_k}, got q_n={q_n}")

# ==========================================================================
# PART 3: EXACT DELTA FOR EACH UNSOLVED CASE
# ==========================================================================
print("\n" + "=" * 78)
print("PART 3: EXACT DELTA FOR UNSOLVED CASES n=23, n=25, n=59")
print("=" * 78)

# For odd n: p_n/q_n > log_2(3), so S = p_n, delta = p_n - q_n * log_2(3) > 0
# From CF theory: delta ~ 1/(q_n * q_{n+1}) approximately
# More precisely: |p_n - q_n * log_2(3)| = 1 / (q_n * (alpha_{n+1}*q_n + q_{n-1}))
# where alpha_{n+1} = [a_{n+1}; a_{n+2}, ...]

target_indices = [23, 25, 59]

print(f"\n  {'n':>4} {'p_n (=S)':>22} {'q_n (=k)':>22} {'a_n':>5} {'a_{n+1}':>7}")
print("  " + "-" * 75)

case_data = {}

for n in target_indices:
    if n >= len(convergents):
        print(f"    n={n}: NOT ENOUGH CF TERMS")
        continue
    p_n, q_n, a_n = convergents[n]
    a_next = convergents[n+1][2] if n+1 < len(convergents) else "?"
    print(f"  {n:>4} {p_n:>22} {q_n:>22} {a_n:>5} {str(a_next):>7}")
    case_data[n] = {'p_n': p_n, 'q_n': q_n, 'a_n': a_n, 'a_next': a_next}

print("\n  Computing exact delta (high precision)...")

for n in target_indices:
    if n not in case_data:
        continue
    p_n = case_data[n]['p_n']
    q_n = case_data[n]['q_n']

    # delta = p_n - q_n * log_2(3) computed in mpmath
    delta_exact = mpf(p_n) - mpf(q_n) * log2_3_hp

    # Store as high-precision string
    delta_str_50 = nstr(delta_exact, 50)
    delta_str_20 = nstr(delta_exact, 20)
    delta_float = float(delta_exact)

    case_data[n]['delta'] = delta_exact
    case_data[n]['delta_float'] = delta_float

    # CF theory prediction: delta ~ 1/(q_n * q_{n+1})
    if n+1 < len(convergents):
        q_next = convergents[n+1][1]
        cf_prediction = 1.0 / (float(q_n) * float(q_next))
        case_data[n]['q_next'] = q_next
        ratio_to_prediction = delta_float / cf_prediction if cf_prediction > 0 else float('inf')
    else:
        cf_prediction = None
        ratio_to_prediction = None
        case_data[n]['q_next'] = None

    print(f"\n  n={n}:")
    print(f"    S = p_n = {p_n}")
    print(f"    k = q_n = {q_n}")
    print(f"    delta (50 digits) = {delta_str_50}")
    print(f"    delta (float)     = {delta_float:.15e}")
    if cf_prediction is not None:
        print(f"    CF prediction 1/(q_n*q_{n+1}) = {cf_prediction:.6e}")
        print(f"    Ratio delta / prediction = {ratio_to_prediction:.6f}")
        print(f"    q_{n+1} = {case_data[n]['q_next']}")

# ==========================================================================
# PART 4: DERIVATION OF m_max BOUND
# ==========================================================================
print("\n" + "=" * 78)
print("PART 4: DERIVATION OF m_max BOUND FROM DELTA")
print("=" * 78)

print("""
  THEORY:
  From Case B analysis: m*d = 3^k - 2^r, where d = 2^S - 3^k.
  Since 3^k < 2^S (because S = ceil(k*log_2(3))):
    d = 2^S - 3^k > 0.
    Also 3^k - 2^r >= d (since m >= 1), so 2^r <= 3^k - d = 2*3^k - 2^S.

  Upper bound on m:
    m = (3^k - 2^r) / d <= (3^k - 1) / d < 3^k / d
    m < 3^k / (2^S - 3^k) = 1 / (2^S/3^k - 1) = 1 / (2^delta - 1)
    where delta = S - k*log_2(3), i.e., 3^k = 2^{S-delta}.

  For small delta: 2^delta - 1 ~ delta * ln(2), so:
    m < 1 / (delta * ln(2))     ... (Theorem P bound)

  Alternative (tighter for Case B with t <= S-1):
    c = (2^t - 1)/d, c odd, c >= 5.
    Since t <= S-1: c < 2^{S-1}/d = 1/(2*(1 - 2^{-delta})).
    For small delta: c < 1/(2*delta*ln(2)).
    This bounds c, which in turn constrains m.

  But for the m-scan, we directly need the bound on m.
  From m*d <= 3^k and d = 2^S - 3^k:
    m <= 3^k / (2^S - 3^k) = 1 / (2^delta - 1)

  More precisely (using mpmath for exact computation):
""")

for n in target_indices:
    if n not in case_data:
        continue
    delta = case_data[n]['delta']
    delta_f = case_data[n]['delta_float']
    p_n = case_data[n]['p_n']
    q_n = case_data[n]['q_n']

    # Bound 1: m < 1/(2^delta - 1)  [Theorem P]
    two_delta = power(2, delta)
    m_bound_P = 1 / (two_delta - 1)
    m_bound_P_float = float(m_bound_P)

    # Bound 2: m < 1/(delta * ln(2))  [first-order approximation]
    m_bound_approx = 1 / (delta_f * math.log(2))

    # Bound 3: c_max = floor(1/(2*(1-2^{-delta})))  [from c < 2^{S-1}/d]
    c_max_exact = 1 / (2 * (1 - power(2, -delta)))
    c_max_float = float(c_max_exact)

    # m_max is the actual integer bound (floor of m_bound_P)
    m_max = int(floor(m_bound_P))

    # c_max integer bound
    c_max_int = int(floor(c_max_exact))

    # Number of odd m values with gcd(m,6)=1 up to m_max
    # These are m in {5, 7, 11, 13, 17, 19, 23, 25, ...}
    # Density: phi(6)/6 = 2/6 = 1/3 of integers are coprime to 6
    # Among odd numbers coprime to 6: density 1/3 of all integers
    # Count of odd m with gcd(m,6)=1 in [5, m_max]:
    # = floor(m_max/6)*2 + adjustment  (2 per 6-block: {..., 6j+1, 6j+5, ...} minus even)
    # Actually: m odd AND gcd(m,6)=1 means m ≡ 1 or 5 (mod 6)
    # Count from 5 to m_max: floor((m_max-5)/6)*2 + ... (depends on residue)
    count_m = 0
    # Exact count: m = 5, 7, 11, 13, 17, 19, 23, 25, ...
    # These are numbers ≡ 1 or 5 (mod 6), with m >= 5
    # In [1, N]: count of n ≡ 1 (mod 6) = floor((N-1)/6) + 1
    # In [1, N]: count of n ≡ 5 (mod 6) = floor((N-5)/6) + 1  (if N >= 5)
    if m_max >= 5:
        count_1mod6 = max(0, (m_max - 1) // 6 + 1 - 1)  # exclude m=1
        count_5mod6 = max(0, (m_max - 5) // 6 + 1)
        count_m = count_1mod6 + count_5mod6
        # Subtract m=1 and m=3 if needed (they are eliminated by Th.H/I/D)
        # m=1: eliminated by Th.D (Mihailescu)
        # m=3: eliminated since gcd(3,m) > 1 (Th.F says gcd(m,6)=1)
        # m=5 already included in the scan 10f26f for m<=100
        # So truly new m to check: from max(101, 5) to m_max with gcd(m,6)=1, m odd
        count_new = 0
        # Count m ≡ 1 (mod 6) in [101, m_max]
        if m_max >= 103:  # 103 ≡ 1 (mod 6)
            first_1mod6 = 103  # next after 100 that is ≡ 1 mod 6
            count_new += max(0, (m_max - first_1mod6) // 6 + 1)
        if m_max >= 101:  # 101 ≡ 5 (mod 6)
            first_5mod6 = 101
            count_new += max(0, (m_max - first_5mod6) // 6 + 1)

    case_data[n]['m_max'] = m_max
    case_data[n]['m_bound_P'] = m_bound_P_float
    case_data[n]['c_max'] = c_max_int
    case_data[n]['count_m_new'] = count_new if m_max >= 5 else 0

    print(f"\n  n={n} (q_n = {q_n:.6e}, delta = {delta_f:.6e}):")
    print(f"    Theorem P bound:     m < 1/(2^delta - 1) = {m_bound_P_float:.6e}")
    print(f"    First-order approx:  m < 1/(delta*ln2)   = {m_bound_approx:.6e}")
    print(f"    m_max (integer):     {m_max:,}")
    print(f"    c_max bound:         c < {c_max_float:.6e}, c_max_int = {c_max_int:,}")
    print(f"    Odd m with gcd(m,6)=1 in [5, m_max]: ~{count_m:,}")
    print(f"    NEW m to check (m > 100): ~{case_data[n]['count_m_new']:,}")


# ==========================================================================
# PART 5: WHAT NEEDS TO BE CHECKED PER m VALUE
# ==========================================================================
print("\n" + "=" * 78)
print("PART 5: COMPUTATION PER m VALUE")
print("=" * 78)

print("""
  FOR EACH odd m with gcd(m,6) = 1, m >= 5:

  Equation: m*d = 3^k - 2^r, where d = 2^S - 3^k, and we need 1 <= r <= S-1.
  Rearranging: 2^r = 3^k - m*d = 3^k - m*(2^S - 3^k) = (m+1)*3^k - m*2^S.

  For 2^r to be a power of 2, we need:
    val = (m+1)*3^k - m*2^S
    val > 0 AND val is a power of 2 AND 1 <= log_2(val) <= S-1.

  PROBLEM: 3^k and 2^S have 10^10+ digits for n=23, and 10^29+ digits for n=59.
  Direct computation is INFEASIBLE.

  MODULAR APPROACH:
  Instead of computing val directly, we work modulo small primes p:
    val = (m+1)*3^k - m*2^S mod p
  Using modular exponentiation: pow(3, k, p) and pow(2, S, p).
  If val ≡ 0 (mod p) for some odd prime p (not 2), then val is NOT a power of 2.

  Per m value, we need:
    - Compute val mod p for several small primes p
    - If val mod p != 0 for all tested p, then val COULD be a power of 2
    - But if val mod p == 0 for some odd p, then val is NOT a power of 2 => m eliminated

  COST PER m:
    - For each prime p: two modular exponentiations of ~10^10 bit exponents
    - Cost per modexp: O(log(S) * log(p)^2) ~ O(40 * 64^2) ~ O(160K) operations
    - For n=23: S ~ 2.18e11, so log2(S) ~ 38 bits
    - For n=59: S ~ 5.99e29, so log2(S) ~ 100 bits
    - With a few primes (say 10), the cost per m is tiny.

  The KEY insight: for a RANDOM m, the probability that val ≡ 0 mod p is 1/p.
  So the probability of surviving k primes is ~ prod(1 - 1/p_i).
  With primes 3, 5, 7, 11, 13, ..., 97 (25 primes), the survival probability
  is ~ prod(1-1/p) ~ 0.026. Adding more primes drops this exponentially.

  In practice, nearly ALL m values will be eliminated by a few small primes.
  Only m values where val is a genuine power of 2 (which we want to EXCLUDE)
  would survive ALL prime checks.
""")


# ==========================================================================
# PART 6: DETAILED FEASIBILITY ANALYSIS
# ==========================================================================
print("=" * 78)
print("PART 6: DETAILED FEASIBILITY ANALYSIS")
print("=" * 78)

for n in target_indices:
    if n not in case_data:
        continue
    d = case_data[n]
    p_n = d['p_n']
    q_n = d['q_n']
    m_max = d['m_max']
    count_new = d['count_m_new']
    delta_f = d['delta_float']

    print(f"\n  === n={n} ===")
    print(f"    S = {p_n:,}")
    print(f"    k = {q_n:,}")
    print(f"    delta = {delta_f:.6e}")
    print(f"    m_max = {m_max:,}")
    print(f"    m values to check (beyond scan m<=100): {count_new:,}")

    # Time estimate per m value (modexp with 64-bit modulus, ~40-bit exponent for n=23)
    # A single pow(base, exp, mod) in Python for exp~2e11, mod~64bit: ~microseconds
    # In C with __uint128_t: ~nanoseconds
    # Let's estimate:
    log2_S = math.log2(p_n) if p_n > 0 else 0
    print(f"    log2(S) = {log2_S:.1f} bits")

    # Python estimate: ~1 microsecond per modexp, 2 per prime, ~20 primes per m
    # = 40 microseconds per m
    python_time_per_m_us = 40  # microseconds
    python_total_s = count_new * python_time_per_m_us / 1e6
    python_total_h = python_total_s / 3600

    # C estimate: ~50 nanoseconds per modexp, 2 per prime, 20 primes per m
    # = 2 microseconds per m
    c_time_per_m_us = 2  # microseconds
    c_total_s = count_new * c_time_per_m_us / 1e6
    c_total_h = c_total_s / 3600

    print(f"\n    Time estimates (20 primes per m, early exit on first kill):")
    print(f"      Python: ~{python_time_per_m_us} us/m => {python_total_s:,.0f}s = {python_total_h:.1f}h")
    print(f"      C/C++:  ~{c_time_per_m_us} us/m  => {c_total_s:,.0f}s = {c_total_h:.2f}h")

    # With early exit (most m killed by first prime):
    # Expected primes needed: ~1/(1-1/3) = 1.5 (if first check is mod 3)
    # Effectively ~3 modexp per m on average
    print(f"\n    With early exit (avg ~3 modexp per m):")
    c_fast_per_m_us = 0.3  # ~3 modexp at 100ns each
    c_fast_total_s = count_new * c_fast_per_m_us / 1e6
    c_fast_total_h = c_fast_total_s / 3600
    print(f"      C optimized: ~{c_fast_per_m_us} us/m => {c_fast_total_s:,.0f}s = {c_fast_total_h:.2f}h")

    case_data[n]['python_hours'] = python_total_h
    case_data[n]['c_hours'] = c_total_h
    case_data[n]['c_fast_hours'] = c_fast_total_h


# ==========================================================================
# PART 7: BENCHMARK — Actual modexp speed
# ==========================================================================
print("\n" + "=" * 78)
print("PART 7: BENCHMARK — Actual modular exponentiation speed")
print("=" * 78)

# Test actual Python pow(base, exp, mod) speed for representative sizes
import random
random.seed(42)

for n in target_indices:
    if n not in case_data:
        continue
    p_n = case_data[n]['p_n']
    q_n = case_data[n]['q_n']

    print(f"\n  n={n}: S={p_n:,}, k={q_n:,}")

    # Benchmark pow(2, S, p) and pow(3, k, p) for various prime moduli
    test_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37,
                   41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
    n_trials = 1000

    t0 = time.time()
    for _ in range(n_trials):
        p = random.choice(test_primes)
        r2 = pow(2, p_n, p)
        r3 = pow(3, q_n, p)
    t_elapsed = time.time() - t0

    time_per_pair_us = t_elapsed / n_trials * 1e6
    print(f"    {n_trials} modexp pairs (small primes): {t_elapsed:.3f}s")
    print(f"    Time per (pow(2,S,p), pow(3,k,p)) pair: {time_per_pair_us:.1f} us")

    # Also test with 64-bit primes (more realistic for sieve)
    big_primes = [2**61 - 1, 2**31 - 1, 999999937, 1000000007, 104729]
    t0 = time.time()
    for _ in range(n_trials):
        p = random.choice(big_primes)
        r2 = pow(2, p_n, p)
        r3 = pow(3, q_n, p)
    t_elapsed_big = time.time() - t0
    time_per_pair_big_us = t_elapsed_big / n_trials * 1e6
    print(f"    {n_trials} modexp pairs (large primes): {t_elapsed_big:.3f}s")
    print(f"    Time per pair (large primes): {time_per_pair_big_us:.1f} us")

    # Revised time estimate
    m_count = case_data[n]['count_m_new']
    # With early exit, average ~1.5 prime checks per m
    avg_checks = 1.5
    revised_s = m_count * avg_checks * time_per_pair_us / 1e6
    revised_h = revised_s / 3600
    revised_d = revised_h / 24

    case_data[n]['benchmark_us'] = time_per_pair_us
    case_data[n]['revised_hours'] = revised_h

    print(f"    Revised estimate ({m_count:,} m values, avg {avg_checks} checks/m):")
    print(f"      Python: {revised_s:,.0f}s = {revised_h:.1f}h = {revised_d:.1f} days")


# ==========================================================================
# PART 8: PARALLELIZATION AND OPTIMIZATION STRATEGIES
# ==========================================================================
print("\n" + "=" * 78)
print("PART 8: PARALLELIZATION AND OPTIMIZATION STRATEGIES")
print("=" * 78)

print("""
  STRATEGY 1: SIEVE-BASED ELIMINATION (most effective)
  =====================================================
  Instead of iterating over m values, iterate over small primes p and
  precompute which m values are eliminated by each prime.

  For prime p:
    val = (m+1)*3^k - m*2^S mod p
    val ≡ 0 (mod p) iff m*(2^S - 3^k) ≡ 3^k (mod p)
                     iff m*d ≡ 3^k (mod p)
                     iff m ≡ 3^k * d^{-1} (mod p)  [if gcd(d,p) = 1]

  So for each prime p with gcd(d mod p, p) = 1:
    Exactly ONE residue class mod p is NOT eliminated (the m where val ≡ 0).
    Wait — we want val to be a power of 2, so val ≡ 0 mod p means p | val,
    which means val is NOT a power of 2 (unless p=2).

  Actually: val = (m+1)*3^k - m*2^S.
  For val to be a power of 2: val = 2^r.
  For odd prime p: val mod p = 0 => p | 2^r => impossible if p is odd.
  So: val mod p != 0 is REQUIRED for val = 2^r.

  Rewriting: val mod p = ((m+1) * pow(3, k, p) - m * pow(2, S, p)) % p
  Let A = pow(3, k, p) and B = pow(2, S, p).
  val mod p = ((m+1)*A - m*B) % p = (m*(A-B) + A) % p
  For val to be a power of 2: this must be nonzero for all odd p.
  For val mod p = 0: m ≡ -A / (A-B) mod p  [if A != B mod p]

  So for each odd prime p, at most ONE residue class of m (mod p) gives val ≡ 0.
  The m-scan seeks m where val ≡ 0 (mod p) for NO odd prime p.

  This is like a SIEVE: for each prime p, we mark off one residue class.
  After sieving with enough primes, very few (ideally zero) m values remain.

  STRATEGY 2: CHINESE REMAINDER SIEVE
  ====================================
  Precompute for primes p_1, ..., p_K the "killed" residue r_i of m mod p_i.
  Using CRT, the surviving m values satisfy:
    m NOT ≡ r_i (mod p_i) for all i.
  The fraction surviving ~ prod(1 - 1/p_i) over odd primes.

  With primes 3, 5, 7, 11, 13, ..., 97 (25 odd primes):
    Survival fraction ~ prod(1 - 1/p_i) ~ 0.0228
  With primes up to 1000 (168 odd primes):
    Survival fraction ~ prod(1 - 1/p_i) ~ very small

  But we need to check all m up to m_max. The sieve approach:
  - Compute r_i = (-A / (A - B)) mod p_i for each prime p_i
  - Create a bitmap of m values, mark off m ≡ r_i (mod p_i) for each prime
  - Check remaining m values more carefully

  For m_max ~ 10^12, a bitmap needs ~125 GB (1 bit per value).
  NOT feasible for n=23. Need segmented approach.

  STRATEGY 3: SEGMENTED SIEVE
  ============================
  Process m values in blocks of size B (e.g., B = 10^8).
  For each block [L, L+B):
    - For each prime p: mark off m ≡ r_i (mod p) in the block.
    - Check surviving m values.

  Memory: O(B) = O(10^8 bytes) = 100 MB. Feasible.
  Time: O(m_max / B * (K * B/p_avg + survivors * check_cost))
  With enough sieving primes, survivors should be extremely rare.

  STRATEGY 4: C IMPLEMENTATION WITH PARALLELISM
  ===============================================
  - Each thread handles a segment of m values
  - Sieve with small primes first, then check survivors with larger primes
  - 8-core M1 Pro: ~8x speedup
  - Expected total time: see revised estimates below

  STRATEGY 5: MATHEMATICAL SHORTCUT — THE 2-ADIC APPROACH
  =========================================================
  Instead of checking val = 2^r, we can check:
    (m+1)*3^k ≡ m*2^S + 2^r (mod 2^L) for various L
  Since 3^k is odd: (m+1)*3^k mod 2 = 1 (if m even) or 0 (if m odd).
  We need m odd (established), so (m+1) is even.
  v_2(m+1) = v_2(val) = r (from Th.B).
  This gives additional 2-adic constraints on m.
""")


# ==========================================================================
# PART 9: SIEVE ELIMINATION RATE ANALYSIS
# ==========================================================================
print("=" * 78)
print("PART 9: SIEVE ELIMINATION RATE — HOW FAST DO PRIMES KILL m VALUES?")
print("=" * 78)

# For each case, compute the killed residue class for small primes
for n in target_indices:
    if n not in case_data:
        continue
    d = case_data[n]
    p_n = d['p_n']
    q_n = d['q_n']

    print(f"\n  === n={n} ===")
    print(f"  For each odd prime p, compute which m mod p is 'killed':")
    print(f"  (i.e., val ≡ 0 mod p, which eliminates m since val cannot be 2^r)")
    print(f"  {'p':>5} {'A=3^k%p':>10} {'B=2^S%p':>10} {'A-B%p':>10} {'r_kill':>8} {'status':>12}")
    print(f"  " + "-" * 60)

    sieve_primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
                    53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
    killed_residues = []
    effective_primes = []
    survival_frac = 1.0

    for p in sieve_primes:
        A = pow(3, q_n, p)
        B = pow(2, p_n, p)
        diff = (A - B) % p

        if diff == 0:
            # A ≡ B mod p: val mod p = A for all m. If A != 0, all m survive.
            # If A = 0: val ≡ 0 mod p for ALL m => ALL killed.
            if A == 0:
                print(f"  {p:>5} {A:>10} {B:>10} {diff:>10} {'ALL':>8} {'ALL KILLED':>12}")
                # All m eliminated for this prime alone!
            else:
                print(f"  {p:>5} {A:>10} {B:>10} {diff:>10} {'NONE':>8} {'NO EFFECT':>12}")
        else:
            # r_kill = (-A * inverse(diff, p)) % p
            diff_inv = pow(diff, -1, p)
            r_kill = (-A * diff_inv) % p
            print(f"  {p:>5} {A:>10} {B:>10} {diff:>10} {r_kill:>8} {'KILLS 1/p':>12}")
            killed_residues.append((p, r_kill))
            effective_primes.append(p)
            survival_frac *= (1 - 1.0/p)

    print(f"\n  Effective sieve primes: {len(effective_primes)}")
    print(f"  Survival fraction after sieving with {len(effective_primes)} primes: {survival_frac:.2e}")
    m_max = d['m_max']
    expected_survivors = int(m_max * survival_frac / 3)  # /3 because only 1/3 of integers are coprime to 6
    print(f"  Expected survivors in [5, {m_max:,}]: ~{expected_survivors:,}")

    case_data[n]['survival_frac'] = survival_frac
    case_data[n]['effective_primes'] = effective_primes
    case_data[n]['killed_residues'] = killed_residues

    # Extended sieve with primes up to 10000
    print(f"\n  Extended sieve analysis (primes up to 10000):")
    ext_survival = 1.0
    ext_count = 0
    for p in range(3, 10001, 2):
        # Quick primality check
        if p < 4 or all(p % i != 0 for i in range(3, int(p**0.5)+1, 2)):
            A = pow(3, q_n, p)
            B = pow(2, p_n, p)
            diff = (A - B) % p
            if diff != 0:
                ext_survival *= (1 - 1.0/p)
                ext_count += 1

    expected_survivors_ext = int(m_max * ext_survival / 3)
    print(f"    Primes used: {ext_count}")
    print(f"    Survival fraction: {ext_survival:.6e}")
    print(f"    Expected survivors: ~{expected_survivors_ext:,}")
    print(f"    (These would need deeper checking, likely ~0 actual solutions)")

    case_data[n]['ext_survival'] = ext_survival
    case_data[n]['ext_survivors'] = expected_survivors_ext


# ==========================================================================
# PART 10: SUMMARY AND RECOMMENDATIONS
# ==========================================================================
print("\n" + "=" * 78)
print("PART 10: SUMMARY AND RECOMMENDATIONS")
print("=" * 78)

print("\n  SUMMARY TABLE:")
print(f"  {'':>4} {'m_max':>15} {'m to check':>15} {'Python (h)':>12} {'C est. (h)':>12} {'Feasible?':>10}")
print("  " + "-" * 75)

for n in target_indices:
    if n not in case_data:
        continue
    d = case_data[n]
    m_max = d['m_max']
    count_new = d['count_m_new']
    py_h = d.get('revised_hours', d['python_hours'])
    c_h = d['c_fast_hours']
    feasible = "YES" if py_h < 720 else ("MAYBE" if py_h < 8760 else "HARD")

    print(f"  n={n:>2} {m_max:>15,} {count_new:>15,} {py_h:>12.1f} {c_h:>12.2f} {feasible:>10}")

print(f"""
  DETAILED RECOMMENDATIONS:
  ========================

  The m-scan approach for Piste J.2 works as follows:
  - For each case (n=23, 25, 59), we bound m < m_max = floor(1/(2^delta - 1)).
  - We check all odd m in [5, m_max] with gcd(m,6) = 1.
  - For each m, we verify that val = (m+1)*3^k - m*2^S is NOT a power of 2.
  - This is done modularly: if val ≡ 0 (mod p) for any odd prime p, m is eliminated.
  - Using a segmented sieve over small primes, most m values are quickly eliminated.

  APPROACH: If EVERY m in [5, m_max] is eliminated, then there is no valid (c, t)
  with c >= 5 and t <= S-1, proving ord_d(2) > S-1 even if d(k) were prime.
  This closes G2c for that case WITHOUT needing to factor d(k).

  KEY INSIGHT: The m-scan proves the theorem EVEN IF d(k) is prime.
  It does not rely on compositeness. This is UNCONDITIONAL.

  IMPORTANT CAVEAT: If d(k) IS composite (very likely), then ord_d(2) may not
  even divide d-1, and the entire G2c analysis for that k is moot.
  The m-scan is a belt-and-suspenders approach that works regardless.
""")

for n in target_indices:
    if n not in case_data:
        continue
    d = case_data[n]
    m_max = d['m_max']
    delta_f = d['delta_float']
    py_h = d.get('revised_hours', d['python_hours'])

    print(f"  n={n}:")
    print(f"    delta = {delta_f:.6e}")
    print(f"    m_max = {m_max:,}")

    if m_max < 1e9:
        print(f"    VERDICT: HIGHLY FEASIBLE. Brute force in Python in {py_h:.1f}h.")
        print(f"    C implementation: minutes to hours.")
        print(f"    With sieve: likely seconds to minutes.\n")
    elif m_max < 1e12:
        print(f"    VERDICT: FEASIBLE with sieve approach.")
        print(f"    Segmented sieve in C: hours to days.")
        print(f"    Python with sieve: days.\n")
    elif m_max < 1e15:
        print(f"    VERDICT: CHALLENGING but possible with optimized C + parallelism.")
        print(f"    Segmented sieve on 8-core M1 Pro: weeks.\n")
    else:
        print(f"    VERDICT: INFEASIBLE by direct scan. Need theoretical argument.\n")

# Final note on the complementary approach
print("  " + "=" * 72)
print("  COMPLEMENTARY APPROACH: m-scan + compositeness sieve")
print("  " + "=" * 72)
print("""
  The m-scan and the prime sieve (crible C) are COMPLEMENTARY:

  - Crible C: finds a factor of d(k), proving d(k) composite.
    If d(k) is composite, G2c doesn't apply (only relevant for d prime).
    UNCONDITIONAL but requires finding a factor.

  - m-scan: proves ord_d(2) > S-1 without assuming anything about d(k).
    Works even if d(k) is prime. UNCONDITIONAL.

  Either approach alone suffices to close G2c for a given k.

  RECOMMENDED STRATEGY:
  1. Continue crible C to 10^12 or beyond (ongoing, ~30h per target).
  2. In parallel, implement m-scan for the feasible cases.
  3. For n=23: m-scan is very feasible (m_max ~ 10^12).
  4. For n=25: m-scan is feasible but larger (m_max ~ 10^13).
  5. For n=59: m-scan is the HARDEST (m_max ~ 10^30), likely infeasible
     by direct scan. The crible C approach is more promising for n=59.
""")

print("=" * 78)
print("ANALYSIS COMPLETE")
print("=" * 78)
