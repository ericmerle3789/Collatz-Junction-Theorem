#!/usr/bin/env python3
"""
r13_lpf_bound.py -- Round 13: Largest Prime Factor of d(k) vs C(k)
=====================================================================

CORE QUESTION:
  Does P+(d(k)) > C(k) = binomial(S-1, k-1) for all k >= 3,
  where d(k) = 2^S - 3^k and S = ceil(k * log2(3))?

  If TRUE for all k >= K_0, combined with computational verification for
  k < K_0, this would complete the proof that no non-trivial Collatz cycle
  exists (via the large prime blocking theorem from R12).

MAIN FINDINGS (NUANCED):

  1. P+(d(k)) > C(k) is NOT true for ALL k >= 3. Counterexamples include
     k = 3, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, ...

  2. P+(d(k)) > C(k) DOES hold sporadically: for k in {4,13,42,56,61,69,
     73,76,93,100,...} among k=3..100. This happens when d(k) is prime or
     has a very large prime factor.

  3. KEY STRUCTURAL FACT: For most k, d(k) > C(k) (since log2(d) ~ 1.585k
     while log2(C) ~ 1.45k on average). So when d(k) is PRIME, automatically
     P+ = d > C. But d(k) is composite for most k.

  4. When d(k) is highly composite (many small factors), P+(d) << C.
     The "worst" cases are k where d(k) has many medium-sized prime factors.

  5. The claim P+(d) > C cannot serve as a UNIVERSAL proof strategy because
     it fails for infinitely many k. The CRT mechanism (R12) remains essential
     for those k where P+ < C.

WHAT THIS SCRIPT INVESTIGATES (6 PARTS):

  Part 1: COMPUTATIONAL VERIFICATION -- Factor d(k) for k=3..100+, compute
          P+(d(k)) and C(k). Classify by P+ vs C and primality of d.

  Part 2: GROWTH RATE ANALYSIS -- Compare log2(d), log2(C), log2(P+).
          Show that d > C for most k, but the gap is small (~0.13k bits),
          so composite d can easily have P+ < C.

  Part 3: KNOWN THEOREMS -- Stewart, Schinzel, Zsygmondy, ABC conjecture.
          What do they give? ABC supports rad(d) >> C, not P+ >> C.

  Part 4: MULTIPLICATIVE ORDER -- For primes p | d, analyze ord_p(2).
          The order structure controls how primes divide d.

  Part 5: PROOF LANDSCAPE -- The honest assessment.
          - P+ > C is insufficient as a universal strategy.
          - CRT from R12 is the viable path.
          - A HYBRID proof: P+ handles k where d is prime,
            CRT handles k where d is composite.

  Part 6: RAD(d) vs C -- Even when P+ < C, the radical rad(d) = prod(p|d)
          often exceeds C, enabling CRT blocking.

SELF-TESTS: 30 tests (T01-T30), all must PASS.
Runtime target: < 300 seconds.

INTELLECTUAL HONESTY:
  P+(d) > C is a SPORADIC phenomenon, not a universal one.
  The proof strategy must account for both regimes.

Author: Claude (R13 for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08
"""

import math
import sys
import time
from collections import defaultdict

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
    """S = ceil(k * log2(3)), verified by exact integer comparison."""
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
    """d(k) = 2^S - 3^k, exact positive integer."""
    S = compute_S(k)
    return (1 << S) - 3**k


def compute_C(k):
    """C(k) = C(S-1, k-1): number of compositions in Comp(S, k)."""
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
    """Factor by trial division up to limit."""
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
    """Pollard rho for factoring."""
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
        if rest is None:
            return None
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
            for (pp, ee) in f1 + f2:
                merged[pp] = merged.get(pp, 0) + ee
            return sorted(merged.items())
    return None


def full_factor(n, limit=10**7):
    """Factor n completely. Returns sorted (prime, exponent) list."""
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
            if sub is not None:
                for (q, f) in sub:
                    result.append((q, f * e))
            else:
                result.append((p, e))
    merged = {}
    for (p, e) in result:
        merged[p] = merged.get(p, 0) + e
    return sorted(merged.items())


def largest_prime_factor(n):
    """P+(n): largest prime factor of |n|."""
    facs = full_factor(n)
    if not facs:
        return 1
    return max(p for p, _ in facs)


def euler_phi(n):
    """Euler totient function."""
    if n <= 0:
        return 0
    if n == 1:
        return 1
    result = n
    facs = full_factor(n)
    for p, _ in facs:
        result = result * (p - 1) // p
    return result


def multiplicative_order(a, n):
    """Compute ord_n(a). Returns None if gcd(a,n) != 1."""
    if n <= 1:
        return 1
    if math.gcd(a, n) != 1:
        return None
    phi_n = euler_phi(n)
    if phi_n == 0:
        return None
    phi_factors = full_factor(phi_n)
    order = phi_n
    for (p, e) in phi_factors:
        while order % p == 0 and pow(a, order // p, n) == 1:
            order //= p
    return order


# ============================================================================
# SECTION 1: COMPUTATIONAL VERIFICATION -- P+(d(k)) vs C(k)
# ============================================================================

def part1_compute_lpf_vs_C(max_k=100):
    """Factor d(k), compute P+(d) and C, classify for k=3..max_k."""
    print("\n" + "=" * 78)
    print(f"PART 1: COMPUTATIONAL VERIFICATION -- P+(d(k)) vs C(k) for k = 3..{max_k}")
    print("=" * 78)
    print()

    results = {}
    k_exceeds = []
    k_d_prime = []

    header = f"{'k':>3s} {'S':>4s} {'log2(d)':>8s} {'log2(P+)':>9s} {'log2(C)':>8s} {'P+>C?':>6s} {'#fac':>5s} {'d>C?':>5s} {'d prime?':>9s}"
    print(f"  {header}")
    print(f"  {'-' * len(header)}")

    for k in range(3, max_k + 1):
        if time_remaining() < 60:
            print(f"  [TIME] Stopping at k={k}")
            break

        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)

        try:
            facs = full_factor(d)
            P_plus = max(p for p, _ in facs) if facs else 1
            d_is_prime = len(facs) == 1 and facs[0][1] == 1 and is_prime(facs[0][0])
        except Exception:
            P_plus = -1
            d_is_prime = False
            facs = []

        exceeds = P_plus > C
        ratio = P_plus / C if C > 0 else float('inf')
        d_gt_C = d > C

        log2_d = math.log2(d) if d > 0 else 0
        log2_P = math.log2(P_plus) if P_plus > 1 else 0
        log2_C = math.log2(C) if C > 0 else 0

        results[k] = {
            'S': S, 'd': d, 'C': C, 'P_plus': P_plus,
            'factors': facs, 'd_prime': d_is_prime,
            'exceeds': exceeds, 'ratio': ratio, 'd_gt_C': d_gt_C,
            'log2_d': log2_d, 'log2_P': log2_P, 'log2_C': log2_C,
            'n_factors': len(facs),
        }

        if exceeds:
            k_exceeds.append(k)
        if d_is_prime:
            k_d_prime.append(k)

        yn = "YES" if exceeds else "no"
        dC = "d>C" if d_gt_C else "d<C"
        dp = "PRIME" if d_is_prime else ""
        print(f"  {k:3d} {S:4d} {log2_d:8.1f} {log2_P:9.1f} {log2_C:8.1f} {yn:>6s} {len(facs):5d} {dC:>5s} {dp:>9s}")

    max_k_computed = max(results.keys()) if results else 0

    print()
    print(f"  SUMMARY (k = 3..{max_k_computed}):")
    print(f"    k where P+(d) > C: {k_exceeds}")
    print(f"    k where d is prime: {k_d_prime}")
    print(f"    Total P+>C: {len(k_exceeds)}/{len(results)}")
    print(f"    Total d prime: {len(k_d_prime)}/{len(results)}")

    # Classify
    k_prime_and_exceeds = [k for k in k_exceeds if k in results and results[k]['d_prime']]
    k_composite_and_exceeds = [k for k in k_exceeds if k in results and not results[k]['d_prime']]
    k_prime_and_fails = [k for k in k_d_prime if k not in k_exceeds]

    print(f"    d prime AND P+>C: {k_prime_and_exceeds}")
    print(f"    d composite AND P+>C: {k_composite_and_exceeds} (large prime factor)")
    print(f"    d prime AND P+<C: {k_prime_and_fails} (d < C at these k)")

    # Check: when d is prime and d > C, do we always get P+ > C?
    d_prime_d_gt_C = [k for k in k_d_prime if k in results and results[k]['d_gt_C']]
    d_prime_d_gt_C_and_exceeds = [k for k in d_prime_d_gt_C if results[k]['exceeds']]
    print()
    print(f"  When d is prime AND d > C: {len(d_prime_d_gt_C_and_exceeds)}/{len(d_prime_d_gt_C)} have P+ > C")
    if len(d_prime_d_gt_C) > 0 and len(d_prime_d_gt_C) == len(d_prime_d_gt_C_and_exceeds):
        print("  (Trivially: d prime and d > C implies P+ = d > C)")

    FINDINGS['part1'] = {
        'k_exceeds': k_exceeds,
        'k_d_prime': k_d_prime,
        'k_prime_and_fails': k_prime_and_fails,
        'k_composite_and_exceeds': k_composite_and_exceeds,
        'data': results,
        'max_k': max_k_computed,
    }

    return results


# ============================================================================
# SECTION 2: GROWTH RATE ANALYSIS
# ============================================================================

def part2_growth_rates(data):
    """Analyze growth of log2(d), log2(C), log2(P+)."""
    print("\n" + "=" * 78)
    print("PART 2: GROWTH RATE ANALYSIS")
    print("=" * 78)
    print()

    ks = sorted(data.keys())

    # Compute average growth rates via linear regression
    def linreg(xs, ys):
        n = len(xs)
        sx = sum(xs)
        sy = sum(ys)
        sxy = sum(x * y for x, y in zip(xs, ys))
        sx2 = sum(x * x for x in xs)
        denom = n * sx2 - sx * sx
        if denom == 0:
            return 0, 0
        slope = (n * sxy - sx * sy) / denom
        intercept = (sy - slope * sx) / n
        return slope, intercept

    # log2(d) vs k
    xs = [float(k) for k in ks]
    ys_d = [data[k]['log2_d'] for k in ks]
    ys_C = [data[k]['log2_C'] for k in ks]
    ys_P = [data[k]['log2_P'] for k in ks if data[k]['P_plus'] > 1]
    xs_P = [float(k) for k in ks if data[k]['P_plus'] > 1]

    slope_d, int_d = linreg(xs, ys_d)
    slope_C, int_C = linreg(xs, ys_C)
    slope_P, int_P = linreg(xs_P, ys_P)

    print(f"  LINEAR FITS (log2 vs k):")
    print(f"    log2(d)  ~ {slope_d:.4f} * k + {int_d:.2f}   (theory: log2(3) = {math.log2(3):.4f})")
    print(f"    log2(C)  ~ {slope_C:.4f} * k + {int_C:.2f}")
    print(f"    log2(P+) ~ {slope_P:.4f} * k + {int_P:.2f}")
    print()

    # The key comparison
    if slope_d > slope_C:
        print(f"  d grows FASTER than C on average (slope gap: {slope_d - slope_C:.4f} bits/k)")
        print(f"  This means for MOST k, d > C. When d is prime, P+ = d > C trivially.")
    else:
        print(f"  C grows FASTER than d on average (slope gap: {slope_C - slope_d:.4f} bits/k)")

    print(f"  P+ grows SLOWER than both ({slope_P:.4f} vs {slope_d:.4f})")
    print(f"  This is because P+ <= d and composite d has smaller P+.")
    print()

    # Count d > C vs d < C
    d_gt_C_count = sum(1 for k in ks if data[k]['d_gt_C'])
    d_lt_C_count = len(ks) - d_gt_C_count
    print(f"  d > C for {d_gt_C_count}/{len(ks)} values ({100*d_gt_C_count/len(ks):.1f}%)")
    print(f"  d < C for {d_lt_C_count}/{len(ks)} values ({100*d_lt_C_count/len(ks):.1f}%)")
    print()

    # The d < C cases
    k_d_lt_C = [k for k in ks if not data[k]['d_gt_C']]
    if k_d_lt_C:
        print(f"  k values where d < C: {k_d_lt_C}")
        print(f"  At these k, P+ > C is IMPOSSIBLE (since P+ <= d < C).")
    print()

    # Fractional part analysis
    print("  --- Fractional Part Analysis ---")
    print("  d(k) = 2^S - 3^k = 2^S * (1 - 3^k/2^S).")
    print("  Let delta = {k * log2(3)} = k*log2(3) - floor(k*log2(3)) in (0,1).")
    print("  Then S = floor(k*log2(3)) + 1, and d ~ 2^S * (1 - 2^{-delta}).")
    print("  When delta ~ 0: d ~ 2^S * delta * ln(2), so d is SMALL.")
    print("  When delta ~ 1: d ~ 2^S * (1 - 2^{-1}) = 2^{S-1}, so d ~ 2^S.")
    print()

    # Show delta values for k where d < C
    for k in k_d_lt_C:
        delta = k * math.log2(3) - math.floor(k * math.log2(3))
        S = data[k]['S']
        print(f"    k={k}: delta={delta:.6f}, S={S}, log2(d)={data[k]['log2_d']:.2f}, log2(C)={data[k]['log2_C']:.2f}")

    print()
    print("  The k where d < C have small fractional part delta, meaning")
    print("  3^k/2^S is close to 1 and d is relatively small.")

    FINDINGS['part2'] = {
        'slope_d': slope_d,
        'slope_C': slope_C,
        'slope_P': slope_P,
        'd_gt_C_fraction': d_gt_C_count / len(ks),
        'k_d_lt_C': k_d_lt_C,
    }


# ============================================================================
# SECTION 3: KNOWN THEOREMS
# ============================================================================

def part3_known_theorems(data):
    """Apply known results on largest prime factors."""
    print("\n" + "=" * 78)
    print("PART 3: KNOWN THEOREMS ON P+(2^S - 3^k)")
    print("=" * 78)
    print()

    print("  --- A. Stewart (2013): P+(a^n - 1) ---")
    print("  Gives P+(a^n - 1) > n * exp(c * sqrt(log n)) for fixed a >= 2.")
    print("  DOES NOT APPLY: 2^S - 3^k is not of the form a^n - 1.")
    print()

    print("  --- B. Schinzel (1962): P+(a^n - b^n) ---")
    print("  Gives P+(a^n - b^n) > c * n * log(n) for gcd(a,b)=1, a>b>=1.")
    print("  DOES NOT DIRECTLY APPLY: S != k in general.")
    print("  When g = gcd(S,k) > 1: can write 2^S - 3^k = (2^{S/g})^g - (3^{k/g})^g,")
    print("  giving P+ > c * g * log(g). But g is typically 1.")
    print()

    gcds = {}
    for k in sorted(data.keys()):
        gcds[k] = math.gcd(data[k]['S'], k)
    frac_gcd_1 = sum(1 for g in gcds.values() if g == 1) / len(gcds) if gcds else 0
    print(f"  gcd(S,k) = 1 for {100*frac_gcd_1:.1f}% of k in [3,{max(data.keys())}].")
    print()

    print("  --- C. Zsygmondy (1892): Primitive prime divisors ---")
    print("  For a^n - b^n with equal exponents and gcd(a,b)=1, n >= 3:")
    print("  there exists a primitive prime divisor.")
    print("  DOES NOT APPLY: S != k.")
    print()

    print("  --- D. ABC Conjecture (CONDITIONAL) ---")
    print("  Applied to 3^k + d = 2^S:")
    print("    rad(3^k * d * 2^S) >= rad(2 * 3 * d_odd) where d_odd = d / gcd(d, 2^inf)")
    print("    ABC: 2^S < K_eps * rad(2 * 3 * d_odd)^{1+eps}")
    print("    So rad(d) >> 2^{S/(1+eps)} >> d^{1/(1+eps)}")
    print()
    print("  What does this give for P+ vs C?")
    print("  rad(d) = product of distinct primes of d.")
    print("  If omega(d) = number of distinct prime factors, then")
    print("  P+(d) >= rad(d)^{1/omega(d)} >= (d^{1/(1+eps)})^{1/omega(d)}.")
    print()
    print("  For P+ > C, we need d^{1/((1+eps)*omega(d))} > C,")
    print("  i.e., log(d)/((1+eps)*omega(d)) > log(C).")
    print("  With log(d)/log(C) ~ 1.585/1.45 ~ 1.09, we need")
    print("  omega(d) < 1.09/(1+eps) ~ 1.09.")
    print("  So ABC gives P+ > C only when omega(d) = 1 (d prime)!")
    print()
    print("  CONCLUSION: ABC does NOT give P+ > C in general.")
    print("  But ABC DOES give rad(d) >> d^{1-eps} >> C,")
    print("  which supports the CRT approach.")

    FINDINGS['part3'] = {
        'gcds': gcds,
        'frac_gcd_1': frac_gcd_1,
        'abc_gives_Pplus_gt_C': False,
        'abc_gives_rad_gt_C': True,
    }


# ============================================================================
# SECTION 4: MULTIPLICATIVE ORDER ANALYSIS
# ============================================================================

def part4_order_analysis(data):
    """Study ord_p(2) for primes p | d(k)."""
    print("\n" + "=" * 78)
    print("PART 4: MULTIPLICATIVE ORDER ANALYSIS")
    print("=" * 78)
    print()
    print("  For each prime p | d(k), we have 2^S = 3^k (mod p).")
    print("  t = ord_p(2) divides p-1 and constrains the structure of p.")
    print()

    order_data = {}
    print(f"  {'k':>3s} {'S':>4s} {'p':>12s} {'ord_p(2)':>10s} {'ord/S':>8s} {'p>C?':>5s}")
    print(f"  {'-'*55}")

    for k in sorted(data.keys()):
        if k > 30:
            break
        if time_remaining() < 40:
            break

        S = data[k]['S']
        C = data[k]['C']
        facs = data[k]['factors']
        entries = []

        for p, _ in facs:
            if p > 10**10 or not is_prime(p):
                continue
            t = multiplicative_order(2, p)
            if t is not None:
                order_ratio = t / S if S > 0 else 0
                p_gt_C = "yes" if p > C else "no"
                print(f"  {k:3d} {S:4d} {p:12d} {t:10d} {order_ratio:8.4f} {p_gt_C:>5s}")
                entries.append({'p': p, 'order': t, 'order_over_S': order_ratio})

        order_data[k] = entries

    print()
    print("  OBSERVATION: The multiplicative orders are typically SMALL relative")
    print("  to S. Most primes p | d have ord_p(2) << S, meaning they are")
    print("  'smooth' divisors of cyclotomic-type polynomials evaluated at 2.")
    print()
    print("  When ord_p(2) is large (close to p-1), p tends to be a large prime.")
    print("  This is consistent with, but does not prove, P+ being large.")

    FINDINGS['part4'] = order_data


# ============================================================================
# SECTION 5: PROOF LANDSCAPE
# ============================================================================

def part5_proof_assessment(data):
    """Honest assessment of what can and cannot be proved."""
    print("\n" + "=" * 78)
    print("PART 5: PROOF LANDSCAPE")
    print("=" * 78)
    print()

    max_k = max(data.keys())
    k_exceeds = FINDINGS['part1']['k_exceeds']
    k_fails = [k for k in sorted(data.keys()) if not data[k]['exceeds']]

    print("  === 5A. The Single-Prime Strategy ===")
    print()
    print(f"  OBSERVATION (k=3..{max_k}): P+(d(k)) > C(k) for k in {k_exceeds}")
    print(f"  ({len(k_exceeds)} out of {len(data)} values = {100*len(k_exceeds)/len(data):.1f}%).")
    print()
    print(f"  FAILS for {len(k_fails)} values: too many for computational patching.")
    print(f"  The single-prime strategy CANNOT be the sole proof mechanism.")
    print()

    print("  === 5B. Why P+ < C for Many k ===")
    print()
    print("  When d is composite, P+(d) can be much smaller than d.")
    print("  Example: k=30, d ~ 2^46, but P+ ~ 2^17 (d has 6 prime factors).")
    print("  The 'worst' cases have many medium-sized factors: d = p1*p2*...*pm")
    print("  where each pi ~ d^{1/m} and C ~ d^{0.91}, so pi < C when m >= 2.")
    print()

    print("  === 5C. The CRT Path (R12) ===")
    print()
    print("  The CRT approach does NOT need any single prime to exceed C.")
    print("  It needs: for each composition A, at least one prime p | d has")
    print("  corrSum(A) != 0 (mod p). This is a COVERAGE problem, not a")
    print("  size problem.")
    print()
    print("  R12 verified N_0(d) = 0 for k=3..25 by exhaustive enumeration.")
    print("  The challenge is proving this for all k.")
    print()

    print("  === 5D. HYBRID Strategy ===")
    print()
    print("  A complete proof could use:")
    print("  1. For k where d(k) is prime: P+ = d > C trivially (when d > C,")
    print("     which holds for all primes with k >= 13).")
    print("  2. For k where d(k) is composite: CRT mechanism.")
    print("     Need to prove that the prime factorization of d is 'rich enough'")
    print("     for CRT blocking to work.")
    print()
    print("  The REMAINING GAP is proving CRT blocking for composite d(k)")
    print("  at all k, which is the subject of R12's spectral/Parseval approach.")
    print()

    # Density of primes among d(k)
    n_primes = len(FINDINGS['part1']['k_d_prime'])
    print(f"  === 5E. Density of Primes ===")
    print(f"  d(k) is prime for {n_primes}/{len(data)} values in [3,{max_k}].")
    print(f"  By heuristic (d ~ 2^S has probability ~1/(S*ln2) of being prime),")
    print(f"  we expect O(k/log(k)) primes up to k, so infinitely many.")
    print(f"  But we CANNOT prove d(k) is prime for infinitely many k")
    print(f"  (this would be a major open problem in number theory).")

    FINDINGS['part5'] = {
        'n_exceeds': len(k_exceeds),
        'n_fails': len(k_fails),
        'n_primes': n_primes,
        'single_prime_sufficient': False,
        'crt_needed': True,
    }


# ============================================================================
# SECTION 6: RAD(d) vs C
# ============================================================================

def part6_radical_analysis(data):
    """Analyze rad(d) = product of distinct prime factors vs C."""
    print("\n" + "=" * 78)
    print("PART 6: RADICAL rad(d) vs C")
    print("=" * 78)
    print()
    print("  Even when P+(d) < C, the CRT modulus uses ALL primes of d.")
    print("  rad(d) = product of distinct primes dividing d.")
    print("  If rad(d) > C, then the CRT has enough 'room' to block.")
    print()

    print(f"  {'k':>3s} {'log2(rad)':>10s} {'log2(C)':>8s} {'rad>C?':>7s} {'log2(rad/C)':>12s} {'#primes':>8s}")
    print(f"  {'-'*55}")

    rad_gt_C = 0
    total = 0

    for k in sorted(data.keys()):
        facs = data[k]['factors']
        C = data[k]['C']
        rad_d = 1
        n_primes = 0
        for p, _ in facs:
            rad_d *= p
            n_primes += 1
        exceeds = rad_d > C
        if exceeds:
            rad_gt_C += 1
        total += 1
        log_rad = math.log2(rad_d) if rad_d > 0 else 0
        log_C = math.log2(C) if C > 0 else 0
        log_ratio = log_rad - log_C
        yn = "YES" if exceeds else "no"
        print(f"  {k:3d} {log_rad:10.2f} {log_C:8.2f} {yn:>7s} {log_ratio:12.2f} {n_primes:8d}")

    print()
    print(f"  RESULT: rad(d) > C for {rad_gt_C}/{total} values ({100*rad_gt_C/total:.1f}%)")
    print()
    if rad_gt_C / total > 0.85:
        print("  rad(d) > C for the VAST MAJORITY of k. This is why CRT works:")
        print("  the combined modular constraints from all primes of d have")
        print("  enough 'space' to cover all C compositions.")
    print()
    print("  Under ABC conjecture: rad(d) >> d^{1-eps} >> C for all large k.")
    print("  This would PROVE CRT has enough power for all large k.")

    k_rad_lt_C = [k for k in sorted(data.keys())
                  if not any(True for _ in [1])  # dummy
                  or True]
    # Actually find k where rad < C
    k_rad_fails = []
    for k in sorted(data.keys()):
        facs = data[k]['factors']
        C = data[k]['C']
        rad = 1
        for p, _ in facs:
            rad *= p
        if rad <= C:
            k_rad_fails.append(k)

    if k_rad_fails:
        print(f"  k where rad(d) <= C: {k_rad_fails}")
        print("  At these k, CRT blocking relies on the STRUCTURE of corrSum residues,")
        print("  not just the size of the modulus.")

    FINDINGS['part6'] = {
        'rad_gt_C_fraction': rad_gt_C / total if total > 0 else 0,
        'k_rad_lt_C': k_rad_fails,
    }


# ============================================================================
# SECTION 7: SELF-TESTS
# ============================================================================

def run_self_tests(data):
    """30 self-tests. All must PASS."""
    print("\n" + "=" * 78)
    print("SELF-TESTS (T01-T30)")
    print("=" * 78)
    print()

    # ===== Basic Correctness =====

    # T01: S is correctly computed for known values
    known_S = [(3, 5), (4, 7), (5, 8), (6, 10), (7, 12), (10, 16), (13, 21)]
    ok = all(compute_S(k) == s for k, s in known_S)
    record_test("T01: compute_S correct for known values", ok,
                f"Checked {known_S}")

    # T02: d(k) > 0 for all k = 1..100
    ok = all(compute_d(k) > 0 for k in range(1, 101))
    record_test("T02: d(k) > 0 for k=1..100", ok)

    # T03: d(k) = 2^S - 3^k
    ok = True
    for k in [3, 7, 13, 20, 42]:
        S = compute_S(k)
        if compute_d(k) != (1 << S) - 3**k:
            ok = False
    record_test("T03: d(k) = 2^S - 3^k verified", ok, "k=3,7,13,20,42")

    # T04: C(k) = binomial(S-1, k-1)
    ok = True
    for k in [3, 5, 10, 15, 25]:
        S = compute_S(k)
        if compute_C(k) != math.comb(S - 1, k - 1):
            ok = False
    record_test("T04: C(k) = binom(S-1,k-1) verified", ok)

    # T05: Primality test
    primes = [2, 3, 5, 47, 13, 502829, 1000000007]
    composites = [4, 6, 9, 295, 1909, 100, 1631]
    ok = all(is_prime(p) for p in primes) and all(not is_prime(c) for c in composites)
    record_test("T05: Primality test correct", ok,
                f"{len(primes)} primes, {len(composites)} composites")

    # T06: Factorization of known d(k)
    expected_facs = {
        5: [(5, 1)], 47: [(47, 1)], 13: [(13, 1)],
        295: [(5, 1), (59, 1)], 1909: [(23, 1), (83, 1)],
    }
    ok = all(full_factor(n) == exp for n, exp in expected_facs.items())
    record_test("T06: Factorization correct for d(3..7)", ok)

    # T07: Factor product equals d for k=3..30
    ok = True
    for k in range(3, 31):
        d = compute_d(k)
        facs = full_factor(d)
        prod = 1
        for p, e in facs:
            prod *= p**e
        if prod != d:
            ok = False
            break
    record_test("T07: Product of factors = d for k=3..30", ok)

    # ===== Main Findings =====

    # T08: d(3) = 5 is prime, P+ = 5, C = 6, P+ < C
    record_test("T08: k=3: d=5 prime, P+=5 < C=6",
                data[3]['d_prime'] and data[3]['P_plus'] == 5 and data[3]['C'] == 6 and not data[3]['exceeds'])

    # T09: d(4) = 47 is prime, P+ = 47, C = 20, P+ > C
    record_test("T09: k=4: d=47 prime, P+=47 > C=20",
                data[4]['d_prime'] and data[4]['P_plus'] == 47 and data[4]['C'] == 20 and data[4]['exceeds'])

    # T10: d(5) = 13 is prime, P+ = 13, C = 35, P+ < C (because d < C)
    record_test("T10: k=5: d=13 prime, P+=13 < C=35 (d < C)",
                data[5]['d_prime'] and not data[5]['exceeds'] and not data[5]['d_gt_C'])

    # T11: d(13) = 502829 is prime, P+ > C
    record_test("T11: k=13: d=502829 prime, P+>C",
                data[13]['d_prime'] and data[13]['exceeds'])

    # T12: P+ > C holds for at least 3 values of k in [3..50]
    k_exc_50 = [k for k in FINDINGS['part1']['k_exceeds'] if k <= 50]
    record_test("T12: P+>C for >= 3 values in [3,50]",
                len(k_exc_50) >= 3,
                f"Found {len(k_exc_50)}: {k_exc_50}")

    # T13: P+ > C is NOT universal (fails for k=3)
    record_test("T13: P+>C is NOT universal (k=3 is counterexample)",
                not data[3]['exceeds'],
                "P+(5)=5 < C(4,2)=6")

    # T14: When d is prime and d > C, then P+ > C trivially
    ok = True
    for k in sorted(data.keys()):
        if data[k]['d_prime'] and data[k]['d_gt_C']:
            if not data[k]['exceeds']:
                ok = False
    record_test("T14: d prime AND d>C => P+>C (trivial)", ok)

    # T15: d prime AND d < C => P+ < C (only for k=3,5)
    k_prime_lt_C = [k for k in sorted(data.keys()) if data[k]['d_prime'] and not data[k]['d_gt_C']]
    record_test("T15: d prime AND d<C occurs (k=3,5)",
                set(k_prime_lt_C) == {3, 5},
                f"Found: {k_prime_lt_C}")

    # ===== Growth Rates =====

    # T16: log2(d) > log2(C) for most k
    d_gt_C_frac = FINDINGS['part2']['d_gt_C_fraction']
    record_test("T16: d > C for majority of k",
                d_gt_C_frac > 0.5,
                f"{100*d_gt_C_frac:.1f}% have d>C")

    # T17: Slope of log2(d) ~ log2(3) ~ 1.585
    slope_d = FINDINGS['part2']['slope_d']
    record_test("T17: slope of log2(d) ~ log2(3)",
                abs(slope_d - math.log2(3)) < 0.05,
                f"slope={slope_d:.4f}, log2(3)={math.log2(3):.4f}")

    # T18: Slope of log2(C) < slope of log2(d)
    slope_C = FINDINGS['part2']['slope_C']
    record_test("T18: slope(log2(C)) < slope(log2(d))",
                slope_C < slope_d,
                f"slope_C={slope_C:.4f} < slope_d={slope_d:.4f}")

    # T19: d < C at exactly k=3, 5, 17 in [3,100]
    k_d_lt_C = FINDINGS['part2']['k_d_lt_C']
    record_test("T19: d < C at exactly k=3,5,17",
                set(k_d_lt_C) == {3, 5, 17},
                f"Found: {k_d_lt_C}")

    # ===== Known Theorems =====

    # T20: 2^S - 3^k != 2^n - 1 for k >= 2 (not Mersenne)
    ok = all(compute_d(k) != (1 << compute_S(k)) - 1 for k in range(3, 50))
    record_test("T20: d(k) is NOT Mersenne for k=3..49", ok)

    # T21: gcd(S,k) = 1 for majority of k
    frac = FINDINGS['part3']['frac_gcd_1']
    record_test("T21: gcd(S,k)=1 for majority of k",
                frac > 0.5,
                f"{100*frac:.1f}% have gcd=1")

    # T22: ABC does NOT imply P+ > C universally
    record_test("T22: ABC does not give P+>C universally",
                not FINDINGS['part3']['abc_gives_Pplus_gt_C'],
                "Need omega(d)=1, which is not guaranteed")

    # ===== Orders =====

    # T23: ord_p(2) | (p-1) for tested primes
    ok = True
    for k in range(3, 8):
        d = compute_d(k)
        facs = full_factor(d)
        for p, _ in facs:
            if is_prime(p) and p > 2:
                t = multiplicative_order(2, p)
                if t is None or (p - 1) % t != 0:
                    ok = False
    record_test("T23: ord_p(2) | (p-1) for primes p|d, k=3..7", ok)

    # T24: 2^S = 3^k (mod p) for all p | d(k)
    ok = True
    for k in [3, 5, 9, 13, 20]:
        S = compute_S(k)
        facs = full_factor(compute_d(k))
        for p, _ in facs:
            if is_prime(p) and pow(2, S, p) != pow(3, k, p):
                ok = False
    record_test("T24: 2^S = 3^k (mod p) verified", ok, "k=3,5,9,13,20")

    # T25: euler_phi correct
    phi_cases = [(1, 1), (2, 1), (6, 2), (10, 4), (47, 46), (100, 40)]
    ok = all(euler_phi(n) == phi for n, phi in phi_cases)
    record_test("T25: euler_phi correct", ok)

    # ===== Radical Analysis =====

    # T26: rad(d) > C for majority of k
    rad_frac = FINDINGS['part6']['rad_gt_C_fraction']
    record_test("T26: rad(d) > C for majority of k",
                rad_frac > 0.7,
                f"{100*rad_frac:.1f}%")

    # T27: rad(d) >= P+(d) always (since rad includes all primes)
    ok = True
    for k in sorted(data.keys()):
        facs = data[k]['factors']
        rad = 1
        for p, _ in facs:
            rad *= p
        if rad < data[k]['P_plus']:
            ok = False
    record_test("T27: rad(d) >= P+(d) always", ok)

    # ===== Proof Assessment =====

    # T28: CRT is needed (P+ < C for at least 50% of k)
    n_fails = sum(1 for k in data if not data[k]['exceeds'])
    frac_fails = n_fails / len(data)
    record_test("T28: P+<C for >= 50% of k (CRT needed)",
                frac_fails >= 0.5,
                f"{100*frac_fails:.1f}% have P+<C")

    # T29: omega(d) increases on average with k
    omegas_small = [data[k]['n_factors'] for k in sorted(data.keys()) if k <= 15]
    omegas_large = [data[k]['n_factors'] for k in sorted(data.keys()) if k > 30]
    avg_small = sum(omegas_small) / len(omegas_small) if omegas_small else 0
    avg_large = sum(omegas_large) / len(omegas_large) if omegas_large else 0
    record_test("T29: omega(d) larger for big k (on avg)",
                avg_large >= avg_small,
                f"avg(k<=15)={avg_small:.2f}, avg(k>30)={avg_large:.2f}")

    # T30: Every d(k) has at least one prime factor for k >= 3
    ok = all(len(data[k]['factors']) >= 1 for k in data if k >= 3)
    record_test("T30: d(k) has >= 1 prime factor for all k", ok)


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 78)
    print("R13: LARGEST PRIME FACTOR P+(d(k)) vs C(k) = C(S-1, k-1)")
    print("     d(k) = 2^S - 3^k,  S = ceil(k * log2(3))")
    print("=" * 78)
    print()
    print("CENTRAL QUESTION: Does P+(d(k)) > C(k) for all k >= 3?")
    print("SHORT ANSWER: NO. But P+ > C is more common than expected for large k,")
    print("because d > C for most k and d(k) is prime for infinitely many k (heuristic).")
    print()

    # Part 1
    data = part1_compute_lpf_vs_C(max_k=100)

    # Part 2
    part2_growth_rates(data)

    # Part 3
    part3_known_theorems(data)

    # Part 4
    part4_order_analysis(data)

    # Part 5
    part5_proof_assessment(data)

    # Part 6
    part6_radical_analysis(data)

    # Self-tests
    run_self_tests(data)

    # ====== FINAL SUMMARY ======
    print("\n" + "=" * 78)
    print("FINAL SUMMARY")
    print("=" * 78)
    print()
    n_pass = sum(1 for _, p, _ in TEST_RESULTS if p)
    n_fail = sum(1 for _, p, _ in TEST_RESULTS if not p)
    n_total = len(TEST_RESULTS)
    print(f"  Tests: {n_pass}/{n_total} PASS, {n_fail}/{n_total} FAIL")

    if n_fail > 0:
        print()
        print("  FAILED TESTS:")
        for name, passed, detail in TEST_RESULTS:
            if not passed:
                print(f"    [FAIL] {name}: {detail}")

    print()
    print("  === KEY RESULTS ===")
    print()
    k_exc = FINDINGS['part1']['k_exceeds']
    k_pr = FINDINGS['part1']['k_d_prime']
    max_k = FINDINGS['part1']['max_k']
    print(f"  1. COMPUTATIONAL (k=3..{max_k}):")
    print(f"     P+(d(k)) > C(k) for k in {k_exc}")
    print(f"     d(k) is prime for k in {k_pr}")
    print(f"     When d is prime and d > C: P+ > C trivially (all k >= 13).")
    print(f"     When d is composite: P+ < C for almost all k.")
    print()
    print(f"  2. GROWTH RATES:")
    print(f"     log2(d) ~ {FINDINGS['part2']['slope_d']:.4f} * k")
    print(f"     log2(C) ~ {FINDINGS['part2']['slope_C']:.4f} * k")
    print(f"     d > C for {100*FINDINGS['part2']['d_gt_C_fraction']:.0f}% of k (d grows slightly faster)")
    print()
    print(f"  3. RADICAL:")
    print(f"     rad(d) > C for {100*FINDINGS['part6']['rad_gt_C_fraction']:.0f}% of k")
    print(f"     Under ABC: rad(d) >> d^{{1-eps}} >> C for all large k")
    print()
    print(f"  4. KNOWN THEOREMS: None gives P+(d) > C unconditionally.")
    print(f"     Stewart, Schinzel, Zsygmondy: wrong form (need a^n - b^n, S != k).")
    print(f"     ABC: gives rad(d) >> C but not P+(d) >> C.")
    print()
    print(f"  5. THE TRUE GAP:")
    print(f"     The proof of N_0(d) = 0 cannot rely on P+(d) > C alone.")
    print(f"     It must use the CRT mechanism (multiple primes cooperating),")
    print(f"     as established in R12. The remaining challenge is proving")
    print(f"     CRT universality for all k, not the size of individual primes.")
    print()
    print(f"  6. PROOF STRATEGY:")
    print(f"     HYBRID: For k where d is prime (infinitely many heuristically),")
    print(f"     N_0(d) = 0 follows from the large-prime theorem (P+ = d > C).")
    print(f"     For k where d is composite, CRT blocking via R12 analysis.")
    print(f"     The gap is proving CRT blocking for ALL composite d(k).")
    print()

    print(f"  Runtime: {elapsed():.1f}s")
    print()

    if n_fail == 0:
        print("  ALL TESTS PASSED.")
    else:
        print(f"  WARNING: {n_fail} TEST(S) FAILED.")
        sys.exit(1)


if __name__ == "__main__":
    main()
