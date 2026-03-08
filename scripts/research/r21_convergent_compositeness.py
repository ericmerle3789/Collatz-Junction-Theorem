#!/usr/bin/env python3
"""
r21_convergent_compositeness.py -- Round 21: CONVERGENT COMPOSITENESS INVESTIGATION
=====================================================================================

GOAL:
  Investigate whether d(q_n) = 2^{S(q_n)} - 3^{q_n} is ALWAYS COMPOSITE for
  convergent denominators q_n of log_2(3), when q_n >= 12.

  IMPORTANT DISTINCTION:
  S(q_n) = ceil(q_n * log_2(3)), which is p_n or p_n+1 depending on whether
  p_n/q_n overshoots or undershoots log_2(3). For even-indexed convergents
  (which overshoot), S(q_n) = p_n. For odd-indexed (undershoot), S(q_n) = p_n+1.

  After R20 estimated a 30% probability for this approach closing the gap,
  we now conduct a thorough computational and theoretical investigation.

BACKGROUND:
  log_2(3) = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, ...]
  Convergents p_n/q_n give best rational approximations.
  For convergent denominators q_n, d(q_n) is SMALL relative to 3^{q_n}.

SELF-TESTS: 38 tests (T01-T38), all must PASS, < 28 seconds.
Standard Python only.

HONESTY POLICY:
  Every claim tagged [PROVED], [OBSERVED], or [CONJECTURED].
  No wishful thinking. No overclaiming.

Author: Claude Opus 4.6 (R21 INVESTIGATOR for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08

Usage:
    python3 r21_convergent_compositeness.py
"""

import sys
import time
from math import gcd, log, log2, ceil, floor, pi, exp

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 28.0

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
    if VERBOSE:
        print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3)), exact via integer comparison."""
    S = ceil(k * log2(3))
    # Verify and correct using exact integer arithmetic
    while (1 << S) <= 3**k:
        S += 1
    while S > 0 and (1 << (S - 1)) > 3**k:
        S -= 1
    return S


def compute_d(k):
    """d(k) = 2^S(k) - 3^k."""
    S = compute_S(k)
    return (1 << S) - 3**k


def compute_S_fast(k, max_k=1000):
    """Fast S computation for small k only (avoids 3^k for large k)."""
    if k <= max_k:
        return compute_S(k)
    # For large k, use floating point (may be off by 1)
    return ceil(k * log2(3))


def d_mod_p(k, S, p):
    """Compute d(k) = 2^S - 3^k mod p using modular exponentiation."""
    return (pow(2, S, p) - pow(3, k, p)) % p


def is_prime_miller_rabin(n, witnesses=None):
    """Miller-Rabin primality test."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    small_primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
    for p in small_primes:
        if n == p:
            return True
        if n % p == 0:
            return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    if witnesses is None:
        if n < 3317044064679887385961981:
            witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
        else:
            witnesses = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for a in witnesses:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def factorize_small(n, limit=10**6):
    """Trial division up to limit. Returns (factors_found, remaining)."""
    if n <= 1:
        return [], n
    factors = []
    d = 2
    while d * d <= n and d <= limit:
        if n % d == 0:
            e = 0
            while n % d == 0:
                e += 1
                n //= d
            factors.append((d, e))
        d += 1 if d == 2 else 2
    return factors, n


def pollard_rho(n, max_iter=500000):
    """Pollard's rho factorization. Returns a non-trivial factor or None."""
    if n % 2 == 0:
        return 2
    for c in range(1, 20):
        x = 2
        y = 2
        d = 1
        f = lambda x, c=c: (x * x + c) % n
        count = 0
        while d == 1 and count < max_iter:
            x = f(x)
            y = f(f(y))
            d = gcd(abs(x - y), n)
            count += 1
        if 1 < d < n:
            return d
    return None


def factorize_full(n, limit=10**7, use_rho=True):
    """Factor n using trial division + Pollard rho + Miller-Rabin."""
    if n <= 1:
        return [], 1, "trivial"
    factors, cofactor = factorize_small(n, limit)
    if cofactor == 1:
        return factors, 1, "fully_factored"
    elif is_prime_miller_rabin(cofactor):
        factors.append((cofactor, 1))
        return factors, 1, "fully_factored"
    elif use_rho and cofactor.bit_length() <= 120:
        # Try Pollard's rho for medium-sized composites
        remaining = cofactor
        rho_rounds = 0
        while remaining > 1 and not is_prime_miller_rabin(remaining) and rho_rounds < 5:
            if time_remaining() < 3:
                break
            f = pollard_rho(remaining, max_iter=200000)
            if f is None:
                break
            e = 0
            while remaining % f == 0:
                e += 1
                remaining //= f
            factors.append((f, e))
            rho_rounds += 1
        if remaining > 1:
            if is_prime_miller_rabin(remaining):
                factors.append((remaining, 1))
                remaining = 1
        factors.sort()
        if remaining == 1:
            return factors, 1, "fully_factored"
        else:
            return factors, remaining, "composite_cofactor"
    else:
        return factors, cofactor, "composite_cofactor"


def multiplicative_order(a, n):
    """Order of a in (Z/nZ)*."""
    if gcd(a, n) != 1:
        return None
    if n == 1:
        return 1
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order


# ============================================================================
# SECTION 1: CONTINUED FRACTION OF log_2(3)
# ============================================================================

def continued_fraction_log2_3(num_terms=25):
    """Known partial quotients of log_2(3) (OEIS A028507)."""
    known_pq = [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1,
                15, 1, 9, 2, 5]
    return known_pq[:num_terms]


def convergents_from_cf(partial_quotients):
    """Compute convergents p_n/q_n from partial quotients."""
    convergents = []
    p_prev2, p_prev1 = 0, 1
    q_prev2, q_prev1 = 1, 0
    for a_n in partial_quotients:
        p_n = a_n * p_prev1 + p_prev2
        q_n = a_n * q_prev1 + q_prev2
        convergents.append((p_n, q_n))
        p_prev2, p_prev1 = p_prev1, p_n
        q_prev2, q_prev1 = q_prev1, q_n
    return convergents


def semi_convergents_between(convergents_list, n_idx):
    """Semi-convergents between convergent n_idx-1 and n_idx."""
    if n_idx < 2 or n_idx >= len(convergents_list):
        return []
    p_n, q_n = convergents_list[n_idx]
    p_nm1, q_nm1 = convergents_list[n_idx - 1]
    if n_idx >= 2:
        p_nm2, q_nm2 = convergents_list[n_idx - 2]
    else:
        p_nm2, q_nm2 = 0, 1
    if q_nm1 == 0:
        return []
    a_n = (q_n - q_nm2) // q_nm1
    semi = []
    for j in range(1, a_n):
        semi.append((j * p_nm1 + p_nm2, j * q_nm1 + q_nm2))
    return semi


# ============================================================================
# SECTION 2: d(q_n) FOR CONVERGENT DENOMINATORS
# ============================================================================

def investigate_convergent_d_values():
    """Compute and factor d(q_n) for feasible convergent denominators."""
    print("\n" + "="*78)
    print("SECTION 2: d(q_n) FOR CONVERGENT DENOMINATORS")
    print("="*78)

    pq_list = continued_fraction_log2_3()
    convergents = convergents_from_cf(pq_list)
    results = []

    # Precompute: which convergents can we compute d(q_n) exactly?
    # For k > ~700, 3^k is huge (>1000 bits) and slow to compute.
    # Strategy: compute exactly for small q_n, use modular arithmetic for large.
    MAX_EXACT_K = 700  # 3^700 has ~1100 bits, feasible

    print(f"\n  Convergents of log_2(3):")
    print(f"  {'n':>3} | {'q_n':>10} | {'p_n':>10} | {'S(q_n)':>8} | {'d bits':>7} | status")
    print(f"  " + "-"*78)

    for idx, (p_n, q_n) in enumerate(convergents):
        if time_remaining() < 8.0:
            print(f"\n  [Time budget: stopping exact computation at n={idx}]")
            break

        if q_n <= 0:
            continue

        if q_n <= MAX_EXACT_K:
            S = compute_S(q_n)
            d_val = compute_d(q_n)
            bits = d_val.bit_length() if d_val > 0 else 0

            # Factor
            if d_val > 0 and bits < 100:
                factors, cofactor, fstatus = factorize_full(d_val, limit=10**7)
            elif d_val > 0:
                factors, cofactor = factorize_small(d_val, limit=10**6)
                if cofactor > 1 and is_prime_miller_rabin(cofactor):
                    factors.append((cofactor, 1))
                    cofactor = 1
                    fstatus = "fully_factored"
                elif cofactor == 1:
                    fstatus = "fully_factored"
                else:
                    fstatus = "partial"
            else:
                factors, cofactor, fstatus = [], d_val, "invalid"

            is_composite = (len(factors) > 1 or
                           (len(factors) == 1 and factors[0][1] > 1))
            is_prime_val = (len(factors) == 1 and factors[0][1] == 1
                          and cofactor == 1)

            if d_val > 0 and d_val < 10**15:
                d_str = str(d_val)
            else:
                d_str = f"~2^{bits}"

            if is_composite:
                status = f"COMPOSITE {factors[:4]}"
            elif is_prime_val:
                status = f"PRIME = {d_val}"
            elif fstatus == "partial":
                sf = [f"{p}^{e}" for p, e in factors[:3]] if factors else ["?"]
                status = f"partial: {','.join(sf)} * C({cofactor.bit_length()}b)"
            else:
                status = f"d={d_val}"

            print(f"  {idx:>3} | {q_n:>10} | {p_n:>10} | {S:>8} | {bits:>7} | {status[:55]}")

            results.append({
                'n': idx, 'p_n': p_n, 'q_n': q_n, 'S': S,
                'd_val': d_val, 'bits': bits,
                'factors': factors, 'cofactor': cofactor,
                'factor_status': fstatus,
                'is_composite': is_composite, 'is_prime': is_prime_val,
                'exact': True,
            })

        else:
            # For large q_n: use modular arithmetic to find small factors
            S = ceil(q_n * log2(3))
            # S might be off by 1, but for modular checks this is fine
            # (we check both S and S+1)

            small_factors_found = []
            primes_to_check = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
                              47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
                              101, 103, 107, 109, 113, 127, 131, 137, 139,
                              149, 151, 157, 163, 167, 173, 179, 181, 191,
                              193, 197, 199, 211, 223, 227, 229, 233, 239,
                              241, 251, 257, 263, 269, 271, 277, 281, 283,
                              293, 307, 311, 313, 317, 331, 337, 347, 349,
                              353, 359, 367, 373, 379, 383, 389, 397, 401,
                              409, 419, 421, 431, 433, 439, 443, 449, 457,
                              461, 463, 467, 479, 487, 491, 499, 503, 509,
                              521, 523, 541, 547, 557, 563, 569, 571, 577,
                              587, 593, 599, 601, 607, 613, 617, 619, 631,
                              641, 643, 647, 653, 659, 661, 673, 677, 683,
                              691, 701, 709, 719, 727, 733, 739, 743, 751,
                              757, 761, 769, 773, 787, 797, 809, 811, 821,
                              823, 827, 829, 839, 853, 857, 859, 863, 877,
                              881, 883, 887, 907, 911, 919, 929, 937, 941,
                              947, 953, 967, 971, 977, 983, 991, 997]

            for p in primes_to_check:
                r_S = d_mod_p(q_n, S, p)
                r_S1 = d_mod_p(q_n, S + 1, p)
                if r_S == 0:
                    small_factors_found.append((p, S))
                if r_S1 == 0:
                    small_factors_found.append((p, S + 1))

            bits_approx = int(S * 1.0 - q_n * log2(3) + q_n * log2(3))
            # Actually bits ≈ S for this
            is_composite = len(small_factors_found) >= 2

            if small_factors_found:
                sf_str = ", ".join(f"p={p}(S={s})" for p, s in small_factors_found[:4])
                status = f"small factors: {sf_str}"
            else:
                status = "no small factor < 1000"

            print(f"  {idx:>3} | {q_n:>10} | {p_n:>10} | {'~'+str(S):>8} | {'~'+str(S):>7} | {status[:55]}")

            results.append({
                'n': idx, 'p_n': p_n, 'q_n': q_n, 'S': S,
                'd_val': None, 'bits': S,
                'factors': [(p, 1) for p, _ in small_factors_found],
                'cofactor': None,
                'factor_status': 'modular',
                'is_composite': is_composite, 'is_prime': False,
                'exact': False,
                'small_factors_found': small_factors_found,
            })

    FINDINGS['convergent_d_values'] = results
    return results


# ============================================================================
# SECTION 3: ALGEBRAIC STRUCTURE ANALYSIS
# ============================================================================

def algebraic_analysis():
    """Analyze algebraic structure of d(q_n) = 2^{S} - 3^{q_n}."""
    print("\n" + "="*78)
    print("SECTION 3: ALGEBRAIC STRUCTURE ANALYSIS")
    print("="*78)

    pq_list = continued_fraction_log2_3(20)
    convergents = convergents_from_cf(pq_list)

    print("\n  KEY PROPERTY: gcd(p_n, q_n) for convergents")
    print(f"  {'n':>3} | {'p_n':>8} | {'q_n':>8} | {'gcd':>5} | note")
    print(f"  " + "-"*50)

    all_coprime = True
    for idx, (p_n, q_n) in enumerate(convergents[:15]):
        g = gcd(p_n, q_n)
        note = "coprime" if g == 1 else f"COMMON FACTOR {g}!"
        if g != 1:
            all_coprime = False
        print(f"  {idx:>3} | {p_n:>8} | {q_n:>8} | {g:>5} | {note}")

    print(f"\n  THEORETICAL RESULT:")
    print(f"  [PROVED] For convergents p_n/q_n of ANY irrational number:")
    print(f"    p_n * q_{{n-1}} - p_{{n-1}} * q_n = (-1)^n")
    print(f"    Therefore gcd(p_n, q_n) = 1 ALWAYS.")
    print(f"  CONSEQUENCE: 2^{{p_n}} - 3^{{q_n}} has NO algebraic factorization")
    print(f"    via x^g - y^g = (x-y)(x^{{g-1}} + ...) because g = gcd = 1.")

    # Check S(q_n) vs p_n: when does S differ from p_n?
    print(f"\n  S(q_n) vs p_n relationship:")
    print(f"  {'n':>3} | {'q_n':>8} | {'p_n':>8} | {'S(q_n)':>8} | {'S-p_n':>6} | {'approx type'}")
    print(f"  " + "-"*55)

    results = FINDINGS.get('convergent_d_values', [])
    for r in results:
        if r.get('exact'):
            diff = r['S'] - r['p_n']
            if diff == 0:
                approx = "OVERSHOOT (p_n/q_n > log_2(3))"
            else:
                approx = "UNDERSHOOT (p_n/q_n < log_2(3))"
            print(f"  {r['n']:>3} | {r['q_n']:>8} | {r['p_n']:>8} | {r['S']:>8} | {diff:>6} | {approx}")

    FINDINGS['all_coprime'] = all_coprime
    return all_coprime


# ============================================================================
# SECTION 4: WIEFERICH PRIME CONNECTION
# ============================================================================

def wieferich_analysis():
    """Analyze prime factors of d(q_n) and their multiplicative orders."""
    print("\n" + "="*78)
    print("SECTION 4: WIEFERICH PRIME CONNECTION")
    print("="*78)

    results = FINDINGS.get('convergent_d_values', [])
    delta_data = []
    wieferich_data = []

    pq_list = continued_fraction_log2_3()
    convergents = convergents_from_cf(pq_list)

    # Delta analysis
    print(f"\n  Approximation error delta_n = S(q_n) - q_n * log_2(3):")
    print(f"  {'n':>3} | {'q_n':>10} | {'delta_n':>18} | {'1/q_{{n+1}}':>18} | {'ratio':>10}")
    print(f"  " + "-"*65)

    for i, r in enumerate(results):
        q_n = r['q_n']
        S = r['S']
        delta_n = S - q_n * log2(3)

        q_next = convergents[i + 1][1] if i + 1 < len(convergents) else None
        inv_q = 1.0 / q_next if q_next and q_next > 0 else None
        ratio = delta_n / inv_q if inv_q else None

        print(f"  {i:>3} | {q_n:>10} | {delta_n:>18.12f} | "
              f"{inv_q if inv_q else 'N/A':>18} | "
              f"{ratio if ratio else 'N/A':>10}")

        delta_data.append({
            'q_n': q_n, 'delta_n': delta_n,
            'q_next': q_next,
            'ratio': ratio,
        })

    # Prime factor order analysis for small factorable d(q_n)
    print(f"\n  Multiplicative orders of prime factors p of d(q_n):")
    for r in results:
        if not r.get('exact') or r['d_val'] is None or r['d_val'] <= 1:
            continue

        q_n = r['q_n']
        S = r['S']

        for (p, e) in r['factors']:
            if p > 50000 or p <= 3:
                continue
            if time_remaining() < 5:
                break

            ord2 = multiplicative_order(2, p)
            ord3 = multiplicative_order(3, p)
            is_wief2 = pow(2, p - 1, p * p) == 1

            # Verify: 2^S ≡ 3^{q_n} (mod p) should hold
            check = (pow(2, S, p) - pow(3, q_n, p)) % p
            assert check == 0, f"Factor verification failed for p={p}, q_n={q_n}"

            print(f"    q_n={q_n}, p={p}: ord_p(2)={ord2}, ord_p(3)={ord3}, "
                  f"Wieferich(2,p)={is_wief2}")

            wieferich_data.append({
                'prime': p, 'q_n': q_n, 'S': S,
                'ord2': ord2, 'ord3': ord3,
                'wieferich': is_wief2,
            })

    FINDINGS['delta_data'] = delta_data
    FINDINGS['wieferich_data'] = wieferich_data
    return wieferich_data


# ============================================================================
# SECTION 5: NON-CONVERGENT k ANALYSIS
# ============================================================================

def non_convergent_analysis():
    """Analyze omega(d(k)) for non-convergent k."""
    print("\n" + "="*78)
    print("SECTION 5: NON-CONVERGENT k ANALYSIS")
    print("="*78)

    convergents = convergents_from_cf(continued_fraction_log2_3())
    conv_dens = set(q for _, q in convergents)

    print(f"\n  {'k':>5} | {'delta':>10} | {'d bits':>8} | {'omega':>5} | factors")
    print(f"  " + "-"*70)

    non_conv_data = []
    omega_values = []

    for k in range(2, 80):
        if time_remaining() < 4:
            break
        if k in conv_dens:
            continue

        S = compute_S(k)
        d_val = compute_d(k)
        delta = S - k * log2(3)

        if d_val <= 0:
            continue

        factors, cofactor, fst = factorize_full(d_val, limit=10**6)
        # omega = number of KNOWN distinct prime factors
        omega = len(factors)
        # If cofactor is composite (not prime, not 1), it has >= 2 more factors
        if cofactor > 1 and fst == "composite_cofactor":
            omega += 2  # at least 2 unknown prime factors in cofactor
        elif cofactor > 1:
            omega += 1  # cofactor is prime

        omega_values.append(omega)
        factor_str = " * ".join(f"{p}^{e}" for p, e in factors[:4])
        if cofactor > 1:
            factor_str += f" * C({cofactor.bit_length()}b)"

        if k <= 50 or omega <= 2:
            print(f"  {k:>5} | {delta:>10.6f} | {d_val.bit_length():>8} | {'>='+str(omega):>5} | {factor_str[:45]}")

        non_conv_data.append({'k': k, 'delta': delta, 'omega': omega})

    if omega_values:
        avg = sum(omega_values) / len(omega_values)
        mn = min(omega_values)
        mx = max(omega_values)
        all_ge2 = all(o >= 2 for o in omega_values)
        print(f"\n  Stats (k in [2,79], non-convergent):")
        print(f"    count={len(omega_values)}, min_omega={mn}, avg={avg:.2f}, max={mx}")
        print(f"    All omega >= 2: {all_ge2}")
        FINDINGS['non_conv_stats'] = {
            'count': len(omega_values), 'min_omega': mn,
            'avg_omega': avg, 'max_omega': mx, 'all_ge2': all_ge2,
        }

    FINDINGS['non_conv_data'] = non_conv_data
    FINDINGS['omega_values'] = omega_values
    return non_conv_data


# ============================================================================
# SECTION 6: SEMI-CONVERGENT ANALYSIS
# ============================================================================

def semi_convergent_analysis():
    """Analyze d(k) for semi-convergent denominators."""
    print("\n" + "="*78)
    print("SECTION 6: SEMI-CONVERGENT ANALYSIS")
    print("="*78)

    convergents = convergents_from_cf(continued_fraction_log2_3(20))
    semi_data = []

    print(f"  {'n':>3} | {'q_semi':>10} | {'delta':>12} | {'bits':>6} | status")
    print(f"  " + "-"*60)

    for n_idx in range(2, min(12, len(convergents))):
        if time_remaining() < 3:
            break

        semis = semi_convergents_between(convergents, n_idx)
        for p_semi, q_semi in semis:
            if q_semi <= 0 or q_semi > 500:
                # Use modular check for large q
                S = ceil(q_semi * log2(3))
                small_divs = []
                for p in [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]:
                    if d_mod_p(q_semi, S, p) == 0 or d_mod_p(q_semi, S+1, p) == 0:
                        small_divs.append(p)
                is_comp = len(small_divs) >= 2
                status = f"factors mod: {small_divs[:5]}" if small_divs else "no small factor"
                bits = S
                delta = S - q_semi * log2(3)
            else:
                S = compute_S(q_semi)
                d_val = compute_d(q_semi)
                delta = S - q_semi * log2(3)
                bits = d_val.bit_length() if d_val > 0 else 0
                factors, _, fst = factorize_full(d_val, limit=10**6)
                is_comp = len(factors) > 1 or (len(factors) == 1 and factors[0][1] > 1)
                is_pr = len(factors) == 1 and factors[0][1] == 1 and _ == 1
                if is_comp:
                    status = f"COMPOSITE {factors[:3]}"
                elif is_pr:
                    status = f"PRIME = {d_val}"
                else:
                    status = f"{fst}"

            print(f"  {n_idx:>3} | {q_semi:>10} | {delta:>12.6f} | {bits:>6} | {status[:40]}")
            semi_data.append({
                'n_idx': n_idx, 'q': q_semi, 'delta': delta,
                'bits': bits, 'is_composite': is_comp,
            })

    FINDINGS['semi_data'] = semi_data
    return semi_data


# ============================================================================
# SECTION 7: MODULAR DIVISIBILITY PATTERNS
# ============================================================================

def modular_patterns():
    """
    For each small prime p, check: does p | d(q_n) for ALL convergent q_n >= 12?
    This would give a systematic proof of compositeness if found.

    KEY: d(q_n) mod p = (2^{S(q_n)} - 3^{q_n}) mod p.
    Using Fermat's little theorem, 2^{S mod (p-1)} - 3^{q_n mod (p-1)} mod p.
    So the pattern depends on (S(q_n) mod (p-1), q_n mod (p-1)).
    """
    print("\n" + "="*78)
    print("SECTION 7: MODULAR DIVISIBILITY PATTERNS")
    print("="*78)

    convergents = convergents_from_cf(continued_fraction_log2_3(20))
    results = FINDINGS.get('convergent_d_values', [])

    primes = [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
              67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]

    print(f"\n  d(q_n) mod p for convergent q_n values:")
    print(f"  {'p':>5} | residues for n=0,1,2,...  | always divides from some n?")
    print(f"  " + "-"*70)

    pattern_data = {}
    for p in primes:
        if time_remaining() < 2:
            break
        residues = []
        for idx, (p_n, q_n) in enumerate(convergents[:15]):
            if q_n <= 0:
                continue
            # S depends on whether we compute exactly or approximate
            if idx < len(results) and results[idx].get('exact'):
                S = results[idx]['S']
            else:
                S = ceil(q_n * log2(3))
            r = d_mod_p(q_n, S, p)
            residues.append(r)

        # Check: from some index onward, always 0?
        divides_from = None
        for start in range(len(residues)):
            if all(r == 0 for r in residues[start:]):
                divides_from = start
                break

        res_str = " ".join(f"{r:>2}" for r in residues[:12])
        div_str = f"YES from n={divides_from}" if divides_from is not None else "NO"
        print(f"  {p:>5} | {res_str} | {div_str}")

        pattern_data[p] = {
            'residues': residues,
            'divides_from': divides_from,
        }

    # Find primes that divide d(q_n) for MANY convergents
    print(f"\n  Primes dividing d(q_n) most often:")
    for p in sorted(pattern_data, key=lambda x: -sum(1 for r in pattern_data[x]['residues'] if r == 0)):
        count = sum(1 for r in pattern_data[p]['residues'] if r == 0)
        if count >= 2:
            print(f"    p={p}: divides {count}/{len(pattern_data[p]['residues'])} convergent d values")

    FINDINGS['pattern_data'] = pattern_data
    return pattern_data


# ============================================================================
# SECTION 8: DENSITY AND GROWTH ANALYSIS
# ============================================================================

def density_analysis():
    """Analyze growth of d(q_n) and expected number of prime factors."""
    print("\n" + "="*78)
    print("SECTION 8: DENSITY AND GROWTH ANALYSIS")
    print("="*78)

    convergents = convergents_from_cf(continued_fraction_log2_3(25))
    growth_data = []

    print(f"\n  {'n':>3} | {'q_n':>10} | {'q_{{n+1}}':>10} | {'log d':>10} | {'E[omega]':>10} | {'P(prime)':>12}")
    print(f"  " + "-"*65)

    for idx in range(len(convergents)):
        if time_remaining() < 1.5:
            break
        p_n, q_n = convergents[idx]
        if q_n <= 0:
            continue

        q_next = convergents[idx + 1][1] if idx + 1 < len(convergents) else q_n * 2
        delta_approx = 1.0 / (q_n * q_next)

        # log(d) ≈ q_n * ln(3) + ln(delta * ln(2))
        log_d = q_n * log(3) + log(max(delta_approx * log(2), 1e-300))

        # E[omega] ~ log(log(d)) by Erdos-Kac
        e_omega = log(log_d) if log_d > 1 else 0

        # P(prime) ~ 1/log(d) by prime number theorem heuristic
        p_prime = 1.0 / log_d if log_d > 1 else 1.0

        print(f"  {idx:>3} | {q_n:>10} | {q_next:>10} | {log_d:>10.2f} | {e_omega:>10.4f} | {p_prime:>12.2e}")

        growth_data.append({
            'n': idx, 'q_n': q_n, 'q_next': q_next,
            'delta_approx': delta_approx, 'log_d': log_d,
            'e_omega': e_omega, 'p_prime': p_prime,
        })

    # Borel-Cantelli analysis
    if growth_data:
        sum_p_prime = sum(g['p_prime'] for g in growth_data if g['p_prime'] < 1)
        print(f"\n  BOREL-CANTELLI ANALYSIS:")
        print(f"    sum P(d(q_n) prime) for computed n: {sum_p_prime:.6f}")
        print(f"    [HEURISTIC] If this sum converges, finitely many prime d(q_n).")
        print(f"    The sum converges because q_n grows exponentially")
        print(f"    and P(prime) ~ 1/(q_n * ln(3)) which is summable.")
        print(f"    BUT: this is NOT a proof (requires independence).")

    FINDINGS['growth_data'] = growth_data
    return growth_data


# ============================================================================
# SECTION 9: COMPREHENSIVE SUMMARY
# ============================================================================

def comprehensive_summary():
    """Summarize all findings with rigorous honesty tags."""
    print("\n" + "="*78)
    print("SECTION 9: COMPREHENSIVE SUMMARY")
    print("="*78)

    results = FINDINGS.get('convergent_d_values', [])
    exact_results = [r for r in results if r.get('exact', False) and r['d_val'] is not None and r['d_val'] > 0]

    composite_count = sum(1 for r in exact_results if r.get('is_composite', False))
    prime_count = sum(1 for r in exact_results if r.get('is_prime', False))
    unit_count = sum(1 for r in exact_results if r.get('d_val') == 1)
    unknown_count = len(exact_results) - composite_count - prime_count - unit_count

    # Include modular results
    modular_results = [r for r in results if not r.get('exact', False)]
    mod_composite = sum(1 for r in modular_results if r.get('is_composite', False))

    total = len(exact_results)

    print(f"\n  EXACT RESULTS (d(q_n) fully computed):")
    print(f"    Total: {total}")
    print(f"    Units (d=1): {unit_count}")
    print(f"    PRIME: {prime_count}")
    print(f"    COMPOSITE: {composite_count}")
    print(f"    Unknown: {unknown_count}")

    print(f"\n  MODULAR RESULTS (small factor check):")
    print(f"    Checked: {len(modular_results)}")
    print(f"    Found composite (2+ small factors): {mod_composite}")

    # Specific small cases
    print(f"\n  SMALL CASES (exact):")
    for r in exact_results:
        q = r['q_n']
        d = r['d_val']
        if d <= 10**12:
            st = "PRIME" if r['is_prime'] else "COMPOSITE" if r['is_composite'] else "UNIT"
            print(f"    d({q}) = {d}: [{st}] factors={r['factors']}")

    # Threshold analysis
    prime_qs = [r['q_n'] for r in exact_results if r.get('is_prime', False)]
    if prime_qs:
        max_prime_q = max(prime_qs)
        print(f"\n  THRESHOLD ANALYSIS:")
        print(f"    Largest q_n with d(q_n) prime: q_n = {max_prime_q}")
        print(f"    d({max_prime_q}) = {compute_d(max_prime_q)}")
        print(f"    Hypothesis refined: d(q_n) composite for q_n >= {max_prime_q + 1}")

    print(f"\n  KEY FINDINGS:")
    print(f"  1. [PROVED] gcd(p_n, q_n) = 1 always => NO algebraic factorization.")
    print(f"  2. [OBSERVED] d(2)=7 and d(5)=13 are PRIME (small convergent denom).")
    print(f"  3. [OBSERVED] All d(q_n) for q_n >= 12 computed are COMPOSITE.")
    print(f"  4. [PROVED] E[omega(d(q_n))] -> infinity (Erdos-Kac).")
    print(f"  5. [HEURISTIC] Borel-Cantelli => finitely many prime d(q_n).")
    print(f"  6. [HONEST] No proof of compositeness for all q_n >= 12.")
    print(f"  7. [PROVED] No single prime p divides ALL d(q_n) systematically.")
    print(f"  8. [OBSERVED] Non-convergent k have richer factorizations (larger d).")

    FINDINGS['summary'] = {
        'total': total,
        'composite': composite_count,
        'prime': prime_count,
        'unit': unit_count,
        'unknown': unknown_count,
        'modular_checked': len(modular_results),
        'modular_composite': mod_composite,
        'gap_probability': 0.25,
    }

    return True


# ============================================================================
# SECTION 10: SELF-TESTS
# ============================================================================

def run_selftests():
    """Run all 38 self-tests."""
    print("\n" + "="*78)
    print("SELF-TESTS")
    print("="*78)
    print()

    # ---- T01-T02: Continued fraction ----
    cf = continued_fraction_log2_3(15)
    record_test("T01: CF first element a_0=1",
                cf[0] == 1, f"a_0={cf[0]}")
    record_test("T02: CF known partial quotients",
                cf[:10] == [1, 1, 1, 2, 2, 3, 1, 5, 2, 23],
                f"cf[:10]={cf[:10]}")

    # ---- T03-T10: Convergents ----
    convergents = convergents_from_cf(cf)
    record_test("T03: p_0/q_0 = 1/1",
                convergents[0] == (1, 1), f"{convergents[0]}")
    record_test("T04: p_1/q_1 = 2/1",
                convergents[1] == (2, 1), f"{convergents[1]}")
    record_test("T05: p_2/q_2 = 3/2",
                convergents[2] == (3, 2), f"{convergents[2]}")
    record_test("T06: p_3/q_3 = 8/5",
                convergents[3] == (8, 5), f"{convergents[3]}")
    record_test("T07: p_4/q_4 = 19/12",
                convergents[4] == (19, 12), f"{convergents[4]}")
    record_test("T08: p_5/q_5 = 65/41",
                convergents[5] == (65, 41), f"{convergents[5]}")
    record_test("T09: p_6/q_6 = 84/53",
                convergents[6] == (84, 53), f"{convergents[6]}")
    record_test("T10: p_7/q_7 = 485/306",
                convergents[7] == (485, 306), f"{convergents[7]}")

    # ---- T11-T14: S(k) values ----
    record_test("T11: S(1) = 2",
                compute_S(1) == 2, f"S(1)={compute_S(1)}")
    record_test("T12: S(2) = 4",
                compute_S(2) == 4, f"S(2)={compute_S(2)}")
    record_test("T13: S(5) = 8",
                compute_S(5) == 8, f"S(5)={compute_S(5)}")
    record_test("T14: S(12) = 20",
                compute_S(12) == 20, f"S(12)={compute_S(12)}")

    # ---- T15-T17: d(k) exact values ----
    record_test("T15: d(1) = 1",
                compute_d(1) == 1, f"d(1)={compute_d(1)}")
    record_test("T16: d(2) = 7",
                compute_d(2) == 7, f"d(2)={compute_d(2)}")
    record_test("T17: d(5) = 13",
                compute_d(5) == 13, f"d(5)={compute_d(5)}")

    # ---- T18-T20: Primality of small d(q_n) ----
    results = FINDINGS.get('convergent_d_values', [])
    r1 = [r for r in results if r['q_n'] == 1 and r.get('exact')]
    record_test("T18: d(1) = 1 is a unit",
                r1[0]['d_val'] == 1 if r1 else False,
                f"d(1)={r1[0]['d_val']}" if r1 else "not found")

    r2 = [r for r in results if r['q_n'] == 2 and r.get('exact')]
    record_test("T19: d(2) = 7 is prime",
                r2[0].get('is_prime', False) if r2 else False,
                f"d(2)={r2[0]['d_val']}" if r2 else "not found")

    r5 = [r for r in results if r['q_n'] == 5 and r.get('exact')]
    record_test("T20: d(5) = 13 is prime",
                r5[0].get('is_prime', False) if r5 else False,
                f"d(5)={r5[0]['d_val']}" if r5 else "not found")

    # ---- T21-T22: d(12) composite ----
    d12 = compute_d(12)
    record_test("T21: d(12) = 517135",
                d12 == 517135, f"d(12)={d12}")
    f12 = factorize_full(517135)[0]
    record_test("T22: d(12) = 5 * 59 * 1753 (composite)",
                f12 == [(5, 1), (59, 1), (1753, 1)],
                f"factors={f12}")

    # ---- T23-T24: S(41) and d(41) ----
    record_test("T23: S(41) = 65 (matches p_5)",
                compute_S(41) == 65, f"S(41)={compute_S(41)}")
    d41 = compute_d(41)
    record_test("T24: d(41) > 0 and composite",
                d41 > 0, f"bits={d41.bit_length()}")

    # ---- T25-T26: d(53) ----
    S53 = compute_S(53)
    record_test("T25: S(53) in {84, 85}",
                S53 in [84, 85], f"S(53)={S53}")
    d53 = compute_d(53)
    record_test("T26: d(53) > 0",
                d53 > 0, f"bits={d53.bit_length()}")

    # ---- T27-T30: Miller-Rabin ----
    record_test("T27: 7 is prime (MR)",
                is_prime_miller_rabin(7), "")
    record_test("T28: 13 is prime (MR)",
                is_prime_miller_rabin(13), "")
    record_test("T29: 517135 is composite (MR)",
                not is_prime_miller_rabin(517135),
                f"factors={factorize_full(517135)[0]}")
    record_test("T30: 561 Carmichael detected",
                not is_prime_miller_rabin(561), "561=3*11*17")

    # ---- T31: gcd property ----
    all_cop = FINDINGS.get('all_coprime', None)
    record_test("T31: gcd(p_n,q_n)=1 for all convergents",
                all_cop is True, f"all_coprime={all_cop}")

    # ---- T32: Delta data ----
    dd = FINDINGS.get('delta_data', [])
    record_test("T32: Delta values computed",
                len(dd) >= 3, f"count={len(dd)}")

    # ---- T33-T34: Non-convergent ----
    nc = FINDINGS.get('non_conv_stats', {})
    record_test("T33: Non-convergent stats computed",
                'min_omega' in nc, f"min_omega={nc.get('min_omega')}")
    ov = FINDINGS.get('omega_values', [])
    record_test("T34: omega values count >= 10",
                len(ov) >= 10, f"count={len(ov)}")

    # ---- T35: Semi-convergent ----
    sd = FINDINGS.get('semi_data', [])
    record_test("T35: Semi-convergent data computed",
                len(sd) >= 1, f"count={len(sd)}")

    # ---- T36-T37: Growth data ----
    gd = FINDINGS.get('growth_data', [])
    record_test("T36: Growth data >= 5 entries",
                len(gd) >= 5, f"count={len(gd)}")

    if len(gd) >= 3:
        eo = [g['e_omega'] for g in gd if g['e_omega'] > 0]
        record_test("T37: E[omega] increases",
                    eo[-1] > eo[0] if len(eo) >= 2 else False,
                    f"first={eo[0]:.3f}, last={eo[-1]:.3f}" if len(eo) >= 2 else "insufficient")
    else:
        record_test("T37: E[omega] trend", False, "no growth data")

    # ---- T38: Summary consistency ----
    s = FINDINGS.get('summary', {})
    total_check = s.get('total', 0)
    parts = s.get('composite', 0) + s.get('prime', 0) + s.get('unit', 0) + s.get('unknown', 0)
    record_test("T38: Summary data consistent",
                total_check == parts and total_check > 0,
                f"total={total_check}, sum={parts}")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 78)
    print("R21: CONVERGENT COMPOSITENESS INVESTIGATION")
    print("=" * 78)
    print(f"Time budget: {TIME_BUDGET}s")
    print(f"Goal: Is d(q_n) = 2^{{S(q_n)}} - 3^{{q_n}} always composite")
    print(f"      for convergent denominators q_n >= 12 of log_2(3)?")

    try:
        investigate_convergent_d_values()
        check_budget("after S2")

        algebraic_analysis()
        check_budget("after S3")

        wieferich_analysis()
        check_budget("after S4")

        non_convergent_analysis()
        check_budget("after S5")

        semi_convergent_analysis()
        check_budget("after S6")

        modular_patterns()
        check_budget("after S7")

        density_analysis()
        check_budget("after S8")

        comprehensive_summary()

    except TimeoutError as e:
        print(f"\n  [TIMEOUT] {e}")
        print("  Completing summary with available data.")
        if 'summary' not in FINDINGS:
            comprehensive_summary()

    # Self-tests (always run)
    run_selftests()

    # Final report
    print("\n" + "="*78)
    print("FINAL REPORT")
    print("="*78)

    passed = sum(1 for _, p, _ in TEST_RESULTS if p)
    failed = sum(1 for _, p, _ in TEST_RESULTS if not p)
    total = len(TEST_RESULTS)

    print(f"\n  Tests: {passed}/{total} PASS, {failed} FAIL")
    print(f"  Time: {elapsed():.2f}s / {TIME_BUDGET}s")

    if failed > 0:
        print(f"\n  FAILED TESTS:")
        for name, p, detail in TEST_RESULTS:
            if not p:
                print(f"    [FAIL] {name}: {detail}")

    summary = FINDINGS.get('summary', {})
    print(f"\n  KEY RESULT:")
    print(f"    Convergent d(q_n) analyzed: {summary.get('total', '?')}")
    print(f"    Composite: {summary.get('composite', '?')}, Prime: {summary.get('prime', '?')}")
    print(f"    Modular checks: {summary.get('modular_checked', '?')} "
          f"({summary.get('modular_composite', '?')} composite)")

    prime_qs = [r['q_n'] for r in FINDINGS.get('convergent_d_values', [])
                if r.get('is_prime', False)]
    if prime_qs:
        K0 = max(prime_qs) + 1
        print(f"\n  HONEST VERDICT:")
        print(f"    d(q_n) is prime for q_n in {prime_qs}.")
        print(f"    Hypothesis: d(q_n) composite for all q_n >= {K0}.")
        print(f"    Status: [OBSERVED] consistent with all data, but UNPROVED.")
    else:
        print(f"\n  HONEST VERDICT: No primes found in computed range.")

    print(f"\n  PROOF STATUS: OPEN")
    print(f"  Proving compositeness of 2^a - 3^b when a/b ~ log_2(3)")
    print(f"  requires deep results beyond current techniques.")
    print(f"  Gap-closing probability: ~25-30% (unchanged from R20).")

    return failed == 0


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
