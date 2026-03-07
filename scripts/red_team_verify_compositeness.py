"""
RED TEAM VERIFICATION: Compositeness of d(q_n) for convergents of log_2(3)
==========================================================================

Agent: Red Team
Date: 2026-03-06
Objective: Independently verify all claimed results about d(k) = 2^S - 3^k
            where S = ceil(k * log_2(3)), for k = q_n (convergent denominators).

VERDICTS: PASS / FAIL for each verification block.
"""

import math
from mpmath import mp, mpf, log, ceil as mpceil, floor as mpfloor
import sys

# High precision
mp.dps = 100

LOG2_3 = log(3) / log(2)  # log_2(3) with 100 digits
LOG2_3_approx = float(LOG2_3)

print("=" * 80)
print("RED TEAM VERIFICATION SCRIPT")
print("=" * 80)
print(f"\nlog_2(3) = {LOG2_3}")
print(f"log_2(3) approx = {LOG2_3_approx}")
print()

# ============================================================
# CONTINUED FRACTION OF log_2(3)
# ============================================================
# CF = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, ...]
# We compute convergents from scratch to avoid trusting claimed values.

def compute_cf_coefficients(x, n_terms):
    """Compute continued fraction coefficients of x."""
    coeffs = []
    for _ in range(n_terms):
        a = int(mpfloor(x))
        coeffs.append(a)
        frac = x - a
        if frac < mpf('1e-50'):
            break
        x = 1 / frac
    return coeffs

def convergents_from_cf(coeffs):
    """Compute convergents p_n/q_n from CF coefficients."""
    convs = []
    p_prev2, p_prev1 = 0, 1
    q_prev2, q_prev1 = 1, 0
    for i, a in enumerate(coeffs):
        p = a * p_prev1 + p_prev2
        q = a * q_prev1 + q_prev2
        convs.append((p, q, i))
        p_prev2, p_prev1 = p_prev1, p
        q_prev2, q_prev1 = q_prev1, q
    return convs

print("=" * 80)
print("STEP 0: COMPUTE CF OF log_2(3) AND CONVERGENTS")
print("=" * 80)

cf_coeffs = compute_cf_coefficients(LOG2_3, 20)
print(f"CF coefficients: {cf_coeffs}")

convergents = convergents_from_cf(cf_coeffs)
print(f"\nConvergents p_n/q_n:")
for p, q, n in convergents:
    ratio = float(mpf(p) / mpf(q))
    diff = float(mpf(p) / mpf(q) - LOG2_3)
    side = "ABOVE" if diff > 0 else "BELOW"
    print(f"  n={n}: p_{n}/q_{n} = {p}/{q} = {ratio:.15f}  ({side} log_2(3), diff = {diff:+.2e})")

# Expected CF: [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, ...]
expected_cf_start = [1, 1, 1, 2, 2, 3, 1, 5, 2, 23]
cf_match = cf_coeffs[:10] == expected_cf_start
print(f"\nCF matches expected [1;1,1,2,2,3,1,5,2,23]: {'PASS' if cf_match else 'FAIL'}")

# Expected convergents
expected_convs = {
    0: (1, 1),
    1: (2, 1),
    2: (3, 2),
    3: (8, 5),
    4: (19, 12),
    5: (65, 41),
    6: (84, 53),
    7: (485, 306),
    8: (1054, 665),
    9: (24727, 15601),
}

conv_match = True
for n, (exp_p, exp_q) in expected_convs.items():
    actual_p, actual_q = convergents[n][0], convergents[n][1]
    ok = (actual_p == exp_p and actual_q == exp_q)
    if not ok:
        print(f"  MISMATCH n={n}: expected {exp_p}/{exp_q}, got {actual_p}/{actual_q}")
        conv_match = False

print(f"All convergents match expected values: {'PASS' if conv_match else 'FAIL'}")

# ============================================================
# VERIFICATION 1: PARITY CORRECTION
# ============================================================
print("\n" + "=" * 80)
print("VERIFICATION 1: PARITY CORRECTION (n=0..5)")
print("=" * 80)
print()
print("Rule: For n even, p_n/q_n < log_2(3) => S = p_n + 1, delta ~ 1")
print("      For n odd,  p_n/q_n > log_2(3) => S = p_n,     delta small")
print()

v1_pass = True
for n in range(6):
    p, q = convergents[n][0], convergents[n][1]
    ratio = mpf(p) / mpf(q)
    diff = ratio - LOG2_3
    is_above = diff > 0

    # Standard CF property: even convergents are below, odd are above
    expected_above = (n % 2 == 1)
    parity_ok = (is_above == expected_above)

    # S = ceil(q * log_2(3))
    exact_val = mpf(q) * LOG2_3  # = q * log_2(3)
    S = int(mpceil(exact_val))
    delta = float(mpf(S) - exact_val)

    if n % 2 == 0:  # Even: p/q < log_2(3), so q*log_2(3) > p, so S = p+1
        expected_S = p + 1
        expected_delta_large = True  # delta should be close to 1 - fractional part
    else:  # Odd: p/q > log_2(3), so q*log_2(3) < p, so S = p
        expected_S = p
        expected_delta_large = False  # delta should be small

    S_ok = (S == expected_S)

    status = "PASS" if (parity_ok and S_ok) else "FAIL"
    if not (parity_ok and S_ok):
        v1_pass = False

    print(f"n={n} ({'even' if n%2==0 else 'odd'}): p={p}, q={q}")
    print(f"  p/q {'>' if is_above else '<'} log_2(3) (expected {'>' if expected_above else '<'}): {'OK' if parity_ok else 'WRONG'}")
    print(f"  S = ceil({q} * log_2(3)) = {S}, expected {expected_S}: {'OK' if S_ok else 'WRONG'}")
    print(f"  delta = {delta:.10f}")
    print(f"  [{status}]")
    print()

print(f"VERIFICATION 1 VERDICT: {'PASS' if v1_pass else 'FAIL'}")

# ============================================================
# VERIFICATION 2: COMPOSITENESS OF d(q_n) FOR 5 KEY VALUES
# ============================================================
print("\n" + "=" * 80)
print("VERIFICATION 2: COMPOSITENESS OF d(q_n) FOR 5 KEY VALUES")
print("=" * 80)
print()

# For odd n: S = p_n (the numerator of the convergent)
# We verify: d(k) = 2^S - 3^k is divisible by claimed prime factor p
# Using modular arithmetic: (pow(2, S, p) - pow(3, k, p)) % p == 0

test_cases = [
    # (k=q_n, n, S=p_n, claimed_factor)
    (306,      7,  485,      929),
    (15601,    9,  24727,    5),
    (79335,    11, None,     23),    # Need to compute p_11
    (190537,   13, None,     15661), # Need to compute p_13
    (10781274, 15, None,     17),    # Need to compute p_15
]

# First, let's compute convergents up to n=15
print("Computing convergents up to n=15...")
cf_coeffs_ext = compute_cf_coefficients(LOG2_3, 20)
convergents_ext = convergents_from_cf(cf_coeffs_ext)

conv_dict = {}
for p, q, n in convergents_ext:
    conv_dict[n] = (p, q)
    if n <= 17:
        print(f"  n={n}: p={p}, q={q}")

# Fill in missing S values
for i, (k, n, S, factor) in enumerate(test_cases):
    if S is None:
        if n in conv_dict:
            p_n, q_n = conv_dict[n]
            if q_n != k:
                print(f"  WARNING: q_{n} = {q_n}, but claimed k = {k}")
            test_cases[i] = (k, n, p_n, factor)
            print(f"  Filled S for n={n}: S = p_{n} = {p_n}")
        else:
            print(f"  ERROR: Cannot find convergent n={n}")

print()

v2_pass = True
for k, n, S, factor in test_cases:
    if S is None:
        print(f"k={k}, n={n}: SKIP (missing S)")
        v2_pass = False
        continue

    # Check that q_n matches k
    if n in conv_dict:
        expected_q = conv_dict[n][1]
        q_match = (expected_q == k)
    else:
        q_match = None

    # Verify: (2^S - 3^k) mod factor == 0
    r2 = pow(2, S, factor)
    r3 = pow(3, k, factor)
    residue = (r2 - r3) % factor

    is_composite = (residue == 0)

    # Also verify n is odd (as claimed)
    n_is_odd = (n % 2 == 1)

    status = "PASS" if (is_composite and n_is_odd) else "FAIL"
    if not (is_composite and n_is_odd):
        v2_pass = False

    print(f"k={k} (n={n}, {'odd' if n_is_odd else 'EVEN!'}):")
    print(f"  S = p_{n} = {S}")
    if q_match is not None:
        print(f"  q_{n} = {expected_q}, matches k={k}: {'YES' if q_match else 'NO'}")
    print(f"  (2^{S} - 3^{k}) mod {factor} = ({r2} - {r3}) mod {factor} = {residue}")
    print(f"  d(k) divisible by {factor}: {'YES' if is_composite else 'NO'}")
    print(f"  [{status}]")
    print()

print(f"VERIFICATION 2 VERDICT: {'PASS' if v2_pass else 'FAIL'}")

# ============================================================
# VERIFICATION 3: delta > 0.0145 FOR 21 KNOWN PRIME d(k)
# ============================================================
print("\n" + "=" * 80)
print("VERIFICATION 3: delta > 0.0145 FOR 21 KNOWN PRIME d(k)")
print("=" * 80)
print()

prime_dk_list = [3, 4, 5, 13, 56, 61, 69, 73, 76, 148, 185, 655, 917,
                 2183, 3540, 3895, 4500, 6891, 7752, 10291, 13695]

# First verify that d(k) is actually prime for small cases
print("Pre-check: verifying d(k) is prime for small k...")
from sympy import isprime as sympy_isprime

small_k_check = True
for k in prime_dk_list[:6]:  # Check first 6 where d(k) is small enough
    S = int(mpceil(mpf(k) * LOG2_3))
    dk = 2**S - 3**k
    is_p = sympy_isprime(dk)
    print(f"  d({k}) = 2^{S} - 3^{k} = {dk}: prime = {is_p}")
    if not is_p:
        small_k_check = False
        print(f"    WARNING: d({k}) is NOT prime!")

print(f"  Small d(k) primality check: {'PASS' if small_k_check else 'FAIL'}")
print()

v3_pass = True
min_delta = float('inf')
min_delta_k = None

print(f"{'k':>8} {'S':>10} {'delta':>15} {'delta>0.0145':>15}")
print("-" * 55)

for k in prime_dk_list:
    exact_val = mpf(k) * LOG2_3
    S = int(mpceil(exact_val))
    delta = float(mpf(S) - exact_val)

    ok = delta > 0.0145
    if not ok:
        v3_pass = False

    if delta < min_delta:
        min_delta = delta
        min_delta_k = k

    print(f"{k:>8} {S:>10} {delta:>15.10f} {'PASS' if ok else 'FAIL':>15}")

print()
print(f"Minimum delta = {min_delta:.10f} at k = {min_delta_k}")
print(f"VERIFICATION 3 VERDICT: {'PASS' if v3_pass else 'FAIL'}")

# ============================================================
# VERIFICATION 4: ANTI-HALLUCINATION - ord_d(2) for small prime d(k)
# ============================================================
print("\n" + "=" * 80)
print("VERIFICATION 4: ANTI-HALLUCINATION - ord_d(2) for small prime d(k)")
print("=" * 80)
print()

def multiplicative_order(base, mod):
    """Compute the multiplicative order of base modulo mod."""
    if math.gcd(base, mod) != 1:
        return None
    order = 1
    current = base % mod
    while current != 1:
        current = (current * base) % mod
        order += 1
        if order > mod:
            return None  # Safety
    return order

# d(4) = 2^7 - 3^4 = 128 - 81 = 47
print("d(4) = 2^7 - 3^4 = 128 - 81 = 47")
dk4 = 2**7 - 3**4
print(f"  Computed: d(4) = {dk4}")
assert dk4 == 47, f"d(4) should be 47, got {dk4}"

ord_47 = multiplicative_order(2, 47)
print(f"  ord_47(2) = {ord_47}")
print(f"  Verification: pow(2, {ord_47}, 47) = {pow(2, ord_47, 47)}")
# Check: 47 is prime, so ord must divide 46 = 2 * 23
print(f"  47-1 = 46, divisors: 1, 2, 23, 46")
print(f"  ord_47(2) divides 46: {46 % ord_47 == 0}")
v4a_pass = (pow(2, ord_47, 47) == 1 and 46 % ord_47 == 0)
print(f"  [{'PASS' if v4a_pass else 'FAIL'}]")
print()

# d(5) = 2^8 - 3^5 = 256 - 243 = 13
print("d(5) = 2^8 - 3^5 = 256 - 243 = 13")
dk5 = 2**8 - 3**5
print(f"  Computed: d(5) = {dk5}")
assert dk5 == 13, f"d(5) should be 13, got {dk5}"

ord_13 = multiplicative_order(2, 13)
print(f"  ord_13(2) = {ord_13}")
print(f"  Verification: pow(2, {ord_13}, 13) = {pow(2, ord_13, 13)}")
# Check: 13 is prime, so ord must divide 12 = 2^2 * 3
print(f"  13-1 = 12, divisors: 1, 2, 3, 4, 6, 12")
print(f"  ord_13(2) divides 12: {12 % ord_13 == 0}")
v4b_pass = (pow(2, ord_13, 13) == 1 and 12 % ord_13 == 0)
print(f"  [{'PASS' if v4b_pass else 'FAIL'}]")
print()

# Additional: d(3) = 2^5 - 3^3 = 32 - 27 = 5
print("d(3) = 2^5 - 3^3 = 32 - 27 = 5")
dk3 = 2**5 - 3**3
print(f"  Computed: d(3) = {dk3}")

ord_5 = multiplicative_order(2, 5)
print(f"  ord_5(2) = {ord_5}")
print(f"  Verification: pow(2, {ord_5}, 5) = {pow(2, ord_5, 5)}")
print(f"  ord_5(2) divides 4: {4 % ord_5 == 0}")
v4c_pass = (pow(2, ord_5, 5) == 1 and 4 % ord_5 == 0)
print(f"  [{'PASS' if v4c_pass else 'FAIL'}]")
print()

# Check connection: does ord_d(2) divide anything special related to k?
print("Connection check: ord_d(2) vs k for small primes")
for k in [3, 4, 5, 13]:
    S = int(mpceil(mpf(k) * LOG2_3))
    dk = 2**S - 3**k
    if dk > 1 and sympy_isprime(dk):
        ord_dk = multiplicative_order(2, dk)
        print(f"  k={k}: d(k)={dk}, ord_{dk}(2)={ord_dk}, S={S}, S mod ord={S % ord_dk}, k mod ord={k % ord_dk if ord_dk else 'N/A'}")
        # Key property: 2^S = 3^k mod d(k), so 2^S ≡ 3^k (mod d(k))
        check = pow(2, S, dk) == pow(3, k, dk)
        print(f"         2^S ≡ 3^k (mod d(k)): {check}")

v4_pass = v4a_pass and v4b_pass and v4c_pass
print(f"\nVERIFICATION 4 VERDICT: {'PASS' if v4_pass else 'FAIL'}")

# ============================================================
# EXTRA VERIFICATION: Cross-check d(k) for convergent denominators
# ============================================================
print("\n" + "=" * 80)
print("EXTRA: VERIFY d(q_n) FOR n=0..9")
print("=" * 80)
print()

for n in range(min(10, len(convergents_ext))):
    p_n, q_n = convergents_ext[n][0], convergents_ext[n][1]
    k = q_n

    # S = ceil(k * log_2(3))
    exact_val = mpf(k) * LOG2_3
    S = int(mpceil(exact_val))
    delta = float(mpf(S) - exact_val)

    # For small k, compute d(k) directly
    if k <= 1000:
        dk = 2**S - 3**k
        # Try to factor small d(k)
        if dk > 0 and dk < 10**15:
            if sympy_isprime(dk):
                factor_info = f"PRIME ({dk})"
            else:
                # Find smallest factor
                for f in range(2, min(int(dk**0.5) + 1, 10**6)):
                    if dk % f == 0:
                        factor_info = f"COMPOSITE (smallest factor: {f}, d(k)/{f} = {dk//f})"
                        break
                else:
                    factor_info = f"COMPOSITE (no small factor found, d(k) = {dk})"
        else:
            factor_info = f"d(k) = {dk} (too large for direct factoring)"
    else:
        # For large k, just check modular residues
        dk_str = f"2^{S} - 3^{k} (too large to compute directly)"
        # Check divisibility by small primes
        small_factors = []
        for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
            r = (pow(2, S, p) - pow(3, k, p)) % p
            if r == 0:
                small_factors.append(p)
        if small_factors:
            factor_info = f"COMPOSITE (divisible by {small_factors})"
        else:
            factor_info = f"No small prime factor ≤ 47 found"

    print(f"n={n}: q_{n}={k}, S={S}, delta={delta:.10f}")
    if k <= 1000:
        print(f"  d({k}) = {dk}")
    print(f"  Status: {factor_info}")
    print()

# ============================================================
# FINAL SUMMARY
# ============================================================
print("=" * 80)
print("FINAL SUMMARY")
print("=" * 80)
print()
print(f"  CF coefficients match:           {'PASS' if cf_match else 'FAIL'}")
print(f"  Convergents match:               {'PASS' if conv_match else 'FAIL'}")
print(f"  V1 - Parity correction:          {'PASS' if v1_pass else 'FAIL'}")
print(f"  V2 - Compositeness (5 cases):    {'PASS' if v2_pass else 'FAIL'}")
print(f"  V3 - delta > 0.0145 (21 primes): {'PASS' if v3_pass else 'FAIL'}")
print(f"  V4 - Anti-hallucination (ord):   {'PASS' if v4_pass else 'FAIL'}")
print()
all_pass = cf_match and conv_match and v1_pass and v2_pass and v3_pass and v4_pass
print(f"  OVERALL VERDICT: {'ALL PASS' if all_pass else 'SOME FAILURES DETECTED'}")
print("=" * 80)
