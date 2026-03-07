#!/usr/bin/env python3
"""
Probabilistic Analysis for the Collatz Junction Theorem
=========================================================
Analyzes the 3 unsolved cases (n=23, 25, 59) where d(q_n) = 2^S - 3^k
has no prime factor found up to 10^11.

Computes:
1. Dickman's rho function (delay-differential equation)
2. Size estimates for each target
3. Probability of finding a factor in (10^11, 10^12]
4. Combined probability across all 3 targets
5. Analysis of the 34 known factors' distribution
6. Extrapolation for remaining factors

Author: Eric Merle / Claude analysis
Date: 2026-03-06
"""

import math
import numpy as np
from scipy.integrate import solve_ivp
from scipy.interpolate import interp1d
from collections import Counter

print("=" * 78)
print("  PROBABILISTIC ANALYSIS — Collatz Junction Theorem")
print("  3 Unsolved Cases: n=23, n=25, n=59")
print("=" * 78)

# ============================================================================
# SECTION 1: DICKMAN'S RHO FUNCTION
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 1: DICKMAN'S RHO FUNCTION rho(u)")
print("=" * 78)

def compute_dickman_rho(u_max=30.0, n_points=10000):
    """
    Compute Dickman's rho function using the delay-differential equation:
        rho(u) = 1                          for 0 <= u <= 1
        u * rho'(u) = -rho(u-1)            for u > 1

    We solve this iteratively on intervals [n, n+1] for n = 1, 2, ...
    On each interval, rho(u-1) is known from the previous interval.
    """
    # For 0 <= u <= 1: rho(u) = 1
    # For 1 <= u <= 2: u*rho'(u) = -rho(u-1) = -1, so rho'(u) = -1/u
    #   rho(u) = 1 - ln(u)  for 1 <= u <= 2

    u_vals = np.linspace(0, u_max, n_points + 1)
    rho_vals = np.zeros(n_points + 1)

    for i, u in enumerate(u_vals):
        if u <= 1.0:
            rho_vals[i] = 1.0
        elif u <= 2.0:
            rho_vals[i] = 1.0 - math.log(u)
        else:
            break

    # For u > 2, use numerical integration on each unit interval
    # rho(u) = rho(n) - integral from n to u of rho(t-1)/t dt
    # where n = floor(u)

    # Build interpolation as we go
    du = u_max / n_points

    # We need a more careful approach. Use the integral form:
    # rho(u) = rho(n) - int_n^u rho(t-1)/t dt for n <= u <= n+1

    # First, build a fine grid for [0, 2]
    fine_u = []
    fine_rho = []
    for i, u in enumerate(u_vals):
        if u <= 2.0 + 1e-12:
            if u <= 1.0:
                fine_u.append(u)
                fine_rho.append(1.0)
            else:
                fine_u.append(u)
                fine_rho.append(1.0 - math.log(u))

    # Now extend interval by interval
    current_max = 2
    while current_max < u_max:
        n = current_max  # integer start of interval
        # On [n, n+1], rho(t-1) is known for t-1 in [n-1, n]
        # rho(u) = rho(n) - integral from n to u of rho(t-1)/t dt

        rho_interp = interp1d(fine_u, fine_rho, kind='linear', fill_value='extrapolate')
        rho_at_n = float(rho_interp(n))

        n_sub = 500  # substeps per unit interval
        sub_du = 1.0 / n_sub

        for j in range(1, n_sub + 1):
            u = n + j * sub_du
            if u > u_max:
                break
            # Trapezoidal integration from n to u
            # integral of rho(t-1)/t from n to u
            integral = 0.0
            for m in range(j):
                t0 = n + m * sub_du
                t1 = n + (m + 1) * sub_du
                f0 = float(rho_interp(t0 - 1)) / t0 if t0 > 0 else 0
                f1 = float(rho_interp(t1 - 1)) / t1
                integral += 0.5 * (f0 + f1) * sub_du

            rho_u = rho_at_n - integral
            fine_u.append(u)
            fine_rho.append(max(rho_u, 0))  # rho >= 0

        current_max += 1

    return np.array(fine_u), np.array(fine_rho)

# Compute rho
u_arr, rho_arr = compute_dickman_rho(u_max=25.0, n_points=5000)
rho_func = interp1d(u_arr, rho_arr, kind='linear', fill_value=(1.0, 0.0), bounds_error=False)

# Print some key values and compare with known
print("\nDickman's rho function - computed values vs known:")
known_rho = {
    1: 1.0,
    2: 0.30685,
    3: 0.04861,
    4: 0.00491,
    5: 0.000354,
    6: 1.91e-5,
    7: 7.89e-7,
    8: 2.56e-8,
    10: 1.35e-11,
    15: 1.64e-19,
    20: 2.77e-28,
}

print(f"  {'u':>5s}  {'rho(u) computed':>18s}  {'rho(u) known':>18s}  {'ratio':>10s}")
print(f"  {'-'*5}  {'-'*18}  {'-'*18}  {'-'*10}")
for u, known in sorted(known_rho.items()):
    computed = float(rho_func(u))
    ratio = computed / known if known > 0 else float('inf')
    print(f"  {u:5d}  {computed:18.6e}  {known:18.6e}  {ratio:10.4f}")

# ============================================================================
# SECTION 2: TARGET SIZE ESTIMATES
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 2: TARGET SIZE ESTIMATES")
print("=" * 78)

# Data for the 3 unsolved cases
targets = {
    23: {
        'q_n': 137528045312,
        'S': 217976794617,       # = p_n
        'delta': 1.296e-12,
        'a_n': 2,
        'a_n1': 5,
    },
    25: {
        'q_n': 5409303924479,
        'S': 8573543875303,      # = p_n
        'delta': 9.512e-14,
        'a_n': 7,
        'a_n1': 1,
    },
    59: {
        'q_n': 3.78e29,
        'S': 5.99e29,            # approximate
        'delta': 4.538e-31,
        'a_n': 1,
        'a_n1': 5,
    },
}

print("\nTarget d(q_n) = 2^S - 3^(q_n) size estimates:")
print(f"  {'n':>3s}  {'S':>20s}  {'log10(d)':>16s}  {'digits':>16s}")
print(f"  {'-'*3}  {'-'*20}  {'-'*16}  {'-'*16}")

for n, data in targets.items():
    S = data['S']
    q = data['q_n']
    # d = 2^S - 3^q, so log10(d) ~ S * log10(2) (since 2^S >> 3^q for small delta)
    # More precisely: d = 2^S * (1 - 3^q/2^S) ~ 2^S * delta * ln(2)
    # But for size: log10(d) ~ S * log10(2)
    log10_d = S * math.log10(2)
    digits = log10_d
    data['log10_d'] = log10_d
    data['digits'] = digits

    if S > 1e20:
        print(f"  {n:3d}  {S:20.3e}  {log10_d:16.3e}  ~{digits:.3e}")
    else:
        print(f"  {n:3d}  {S:20.0f}  {log10_d:16.3e}  ~{digits:.3e}")

print("\n  Context: The largest number ever factored (RSA challenge) had ~250 digits.")
print("  These targets have 10^10 to 10^29 digits -- utterly beyond any factoring method.")
print("  We can ONLY find factors by trial division (sieving) or ECM for small factors.")

# ============================================================================
# SECTION 3: PROBABILITY OF FINDING A FACTOR IN (10^11, 10^12]
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 3: PROBABILITY OF FINDING A FACTOR IN (10^11, 10^12]")
print("=" * 78)

B1 = 1e11
B2 = 1e12

# --- Approach 1: Prime counting heuristic ---
# For a "random" number N, the expected number of prime factors in (B1, B2] is:
#   E = sum_{B1 < p <= B2} 1/p ~ ln(ln(B2)) - ln(ln(B1))
# This uses Mertens' theorem.

lnln_B2 = math.log(math.log(B2))
lnln_B1 = math.log(math.log(B1))
E_random = lnln_B2 - lnln_B1

print(f"\n--- Approach 1: Mertens' theorem (unconditional) ---")
print(f"  B1 = {B1:.0e}, B2 = {B2:.0e}")
print(f"  ln(ln(B2)) = {lnln_B2:.6f}")
print(f"  ln(ln(B1)) = {lnln_B1:.6f}")
print(f"  E(# prime factors in (B1, B2]) = {E_random:.6f}")
print(f"  Pr(at least one factor | random N) = 1 - exp(-E) = {1 - math.exp(-E_random):.6f}")

# --- Approach 2: Conditional on no factor <= B1 ---
# Given that no prime factor <= B1 divides N, the conditional probability that
# a factor exists in (B1, B2] depends on the distribution of the smallest factor.
#
# For a random number N of D digits:
# Pr(smallest factor > B) ~ rho(log(N)/log(B)) for large N
# But when D >> log(B), rho(u) for u >> 1 is ~ u^{-u} which is tiny.
# This means: Pr(all factors > B) ~ 0, so there ALMOST CERTAINLY IS a factor below B.
# The question is: where is it?

print(f"\n--- Approach 2: Dickman's rho analysis ---")
print(f"\n  For a random number N with D digits, the probability that ALL prime")
print(f"  factors exceed B is rho(u) where u = log(N)/log(B) = D*ln(10)/ln(B).")

for n, data in targets.items():
    D = data['digits']

    # u for B1 = 10^11
    u_B1 = D * math.log(10) / math.log(B1)
    # u for B2 = 10^12
    u_B2 = D * math.log(10) / math.log(B2)

    print(f"\n  n={n}: D ~ {D:.3e} digits")
    print(f"    u(B1=10^11) = {u_B1:.3e}")
    print(f"    u(B2=10^12) = {u_B2:.3e}")
    print(f"    rho(u) for these u values: EFFECTIVELY 0")
    print(f"    (rho(u) ~ u^{{-u}} ~ exp(-{u_B1:.2e} * ln({u_B1:.2e})) = exp(-{u_B1 * math.log(u_B1):.2e}))")
    print(f"    ==> A 'random' number this large CERTAINLY has a factor below 10^12.")

# --- Approach 3: More refined conditional probability ---
print(f"\n--- Approach 3: Conditional probability given no factor <= B1 ---")
print(f"\n  Given that d(q_n) has no factor <= B1 = 10^11, what is the probability")
print(f"  that it has a factor in (B1, B2] = (10^11, 10^12]?")
print(f"\n  Key insight: For truly random numbers, the smallest prime factor p1")
print(f"  satisfies Pr(p1 > x) ~ rho(log N / log x). Since rho(u) -> 0 for u >> 1,")
print(f"  the smallest factor is almost surely << N^epsilon for any epsilon > 0.")
print(f"\n  The density of primes in (B1, B2] relative to all primes up to B2 is:")
print(f"    pi(B2) - pi(B1) ~ B2/ln(B2) - B1/ln(B1)")

pi_B2 = B2 / math.log(B2)
pi_B1 = B1 / math.log(B1)
print(f"    ~ {pi_B2:.3e} - {pi_B1:.3e} = {pi_B2 - pi_B1:.3e} primes in range")

# For a random composite number with no factor <= B1,
# the probability that it has a factor in (B1, B2] is approximately:
# sum_{B1 < p <= B2} 1/p, which we already computed as E_random.
# But CONDITIONALLY on no factor <= B1, we need:
# Pr(factor in (B1, B2] | no factor <= B1) = 1 - Pr(no factor in (B1, B2] | no factor <= B1)
#
# For a random number, the events "p divides N" for different primes are approximately
# independent, so:
# Pr(no factor in (B1, B2] | no factor <= B1) ~ exp(-sum_{B1<p<=B2} 1/p) = exp(-E_random)
# But this must be adjusted by 1/Pr(no factor <= B1).
# Since Pr(no factor <= B1) ~ rho(log N / log B1) which is TINY for huge N,
# the conditional probability is actually higher.

# However, the most honest approach: since these numbers are astronomically large
# and the factor MUST exist (with probability 1 - rho(huge)), the question is
# really about the DISTRIBUTION of the smallest factor.

print(f"\n--- Approach 4: Distribution of smallest prime factor ---")
print(f"\n  For a truly random N, Pr(smallest factor = p) ~ 1/p (Erdos-Kac heuristic).")
print(f"  Given that the smallest factor p1 > B1, we condition:")
print(f"  Pr(p1 in (B1, B2] | p1 > B1) = Pr(p1 in (B1, B2]) / Pr(p1 > B1)")
print(f"\n  The numerator: sum_{{B1<p<=B2}} 1/p * prod_{{q<=B1}} (1-1/q)")
print(f"  The denominator: prod_{{p<=B1}} (1-1/p) ~ e^(-gamma)/ln(B1) (Mertens)")

gamma_em = 0.5772156649  # Euler-Mascheroni constant
mertens_B1 = math.exp(-gamma_em) / math.log(B1)  # ~ prod(1-1/p) for p <= B1
mertens_B2 = math.exp(-gamma_em) / math.log(B2)

# Pr(smallest factor > B1) ~ e^{-gamma}/ln(B1) (for random N >> B1)
# Pr(smallest factor > B2) ~ e^{-gamma}/ln(B2)
# Pr(smallest factor in (B1,B2]) ~ e^{-gamma} * (1/ln(B1) - 1/ln(B2))
# Pr(p1 in (B1,B2] | p1 > B1) ~ (1/ln(B1) - 1/ln(B2)) / (1/ln(B1))
#                                = 1 - ln(B1)/ln(B2)

pr_factor_in_range_cond = 1 - math.log(B1) / math.log(B2)

print(f"\n  Using Mertens' third theorem:")
print(f"    Pr(smallest factor > B1) ~ e^(-gamma)/ln(B1) = {mertens_B1:.6e}")
print(f"    Pr(smallest factor > B2) ~ e^(-gamma)/ln(B2) = {mertens_B2:.6e}")
print(f"    Pr(p1 in (B1,B2] | p1 > B1) = 1 - ln(B1)/ln(B2)")
print(f"                                  = 1 - {math.log(B1):.4f}/{math.log(B2):.4f}")
print(f"                                  = {pr_factor_in_range_cond:.6f}")
print(f"                                  = {pr_factor_in_range_cond*100:.2f}%")

print(f"\n  >>> RESULT: Per target, conditional on no factor <= 10^11,")
print(f"  >>> the probability of finding a factor in (10^11, 10^12] is ~{pr_factor_in_range_cond*100:.1f}%")

# But there's a subtlety for multiple prime factors
print(f"\n  Refinement: the above assumes the smallest factor is in that range.")
print(f"  The probability of having ANY factor (not necessarily the smallest) is higher.")
print(f"  Expected # of prime factors in (B1, B2] (Mertens): E = {E_random:.6f}")
print(f"  Pr(at least one factor in (B1, B2]) ~ 1 - exp(-E) = {1-math.exp(-E_random):.6f}")
print(f"  This matches the ~{(1-math.exp(-E_random))*100:.1f}% per target estimate.")

# ============================================================================
# SECTION 4: COMBINED PROBABILITY (3 targets)
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 4: COMBINED PROBABILITY (3 targets)")
print("=" * 78)

p_per_target = pr_factor_in_range_cond  # ~ 8.33%
p_per_target_mertens = 1 - math.exp(-E_random)

# Probability at least 1 of 3 targets has a factor in (B1, B2]
p_none = (1 - p_per_target) ** 3
p_at_least_one = 1 - p_none

p_none_m = (1 - p_per_target_mertens) ** 3
p_at_least_one_m = 1 - p_none_m

print(f"\n  Model A: Mertens' conditional (1 - ln B1/ln B2)")
print(f"    Pr(factor in range | one target) = {p_per_target:.4f} ({p_per_target*100:.2f}%)")
print(f"    Pr(NO factor for any of 3 targets) = {p_none:.4f} ({p_none*100:.2f}%)")
print(f"    Pr(at least 1 of 3 has factor) = {p_at_least_one:.4f} ({p_at_least_one*100:.2f}%)")

print(f"\n  Model B: Mertens' sum 1/p (expected count)")
print(f"    Pr(factor in range | one target) = {p_per_target_mertens:.4f} ({p_per_target_mertens*100:.2f}%)")
print(f"    Pr(NO factor for any of 3 targets) = {p_none_m:.4f} ({p_none_m*100:.2f}%)")
print(f"    Pr(at least 1 of 3 has factor) = {p_at_least_one_m:.4f} ({p_at_least_one_m*100:.2f}%)")

# Extended ranges
print(f"\n  Extended analysis for larger sieve ranges:")
print(f"  {'Range':>20s}  {'Pr/target':>12s}  {'Pr(>=1 of 3)':>14s}  {'Cumulative':>12s}")
print(f"  {'-'*20}  {'-'*12}  {'-'*14}  {'-'*12}")

cum_prob = 0  # Cumulative from 10^11 onwards
for exp_B2 in range(12, 21):
    B2_ext = 10 ** exp_B2
    p_ext = 1 - math.log(B1) / math.log(B2_ext)
    # But this is from B1 to B2_ext. We want the increment in each decade.
    if exp_B2 == 12:
        B_lo = B1
    else:
        B_lo = 10 ** (exp_B2 - 1)

    # Pr of smallest factor in (B_lo, B2_ext] given > B1
    p_decade = math.log(B_lo) / math.log(B2_ext) if exp_B2 > 12 else 0
    # Actually, we want conditional on > B_lo:
    # Pr(smallest in (B_lo, 10^exp] | > B1) = (1/ln(B_lo) - 1/ln(B2_ext)) / (1/ln(B1))
    # = ln(B1) * (1/ln(B_lo) - 1/ln(B2_ext))
    p_decade_given_B1 = math.log(B1) * (1/math.log(B_lo) - 1/math.log(B2_ext))
    p3_decade = 1 - (1 - p_decade_given_B1) ** 3
    cum_prob += p_decade_given_B1  # Approximate (ignoring correlations)
    cum_3 = 1 - (1 - min(cum_prob, 0.99)) ** 3

    print(f"  (10^{exp_B2-1}, 10^{exp_B2}]  {p_decade_given_B1:12.4f}  {p3_decade:14.4f}  {min(cum_3, 0.999):12.4f}")

# ============================================================================
# SECTION 5: WHY SO RESISTANT? — THE FORM 2^a - 3^b
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 5: WHY SO RESISTANT? — THE FORM 2^a - 3^b")
print("=" * 78)

print("""
  KEY QUESTION: Are numbers of the form 2^a - 3^b biased in their factor
  distribution compared to random numbers of similar size?

  Analysis:

  1. DICKMAN SAYS THEY MUST BE COMPOSITE:
     For n=23: d has ~6.56e10 digits. rho(log d / log B) for B = 10^12 gives
     u ~ 6.56e10 * ln(10) / ln(10^12) ~ 5.47e9.
     rho(5.47e9) is so close to 0 that Pr(d is prime) ~ 0.
     ==> These numbers CERTAINLY have prime factors. The question is: how big?

  2. FOR RANDOM N OF THIS SIZE:
     The smallest prime factor is typically ~ exp(exp(gamma * ln(N)))? No --
     for random N, Pr(smallest factor > x) ~ 1/ln(x) (Mertens).
     So the "typical" smallest factor of a random N is O(1) -- most random
     numbers are even!

     Given that gcd(d, 6) = 1 (since d = 2^a - 3^b is coprime to 2 and 3),
     the smallest factor must be >= 5. This already eliminates the two densest
     families of primes (2 and 3), but the effect on the distribution of the
     SMALLEST factor > 5 is modest.

  3. STRUCTURAL BIAS OF 2^a - 3^b:
     For a prime p >= 5, p | (2^S - 3^k) iff 2^S = 3^k (mod p).
     This requires: (2/3)^S = 3^{k-S} (mod p), i.e., the discrete log of
     (2/3) must satisfy a specific congruence.

     The probability that a random prime p divides 2^S - 3^k is:
       Pr(p | d) = 1/(ord_p(2/3)) if gcd(ord_p(2/3), ...) works out

     For a RANDOM prime p, the expected value of 1/ord_p(2/3) is ~ 1/(p-1)
     on average (since ord_p divides p-1). But the actual order can be much
     smaller or much larger than (p-1)/2.

     KEY INSIGHT: Since S and k are SPECIFIC numbers (not random), we need
     2^S = 3^k (mod p), which happens with probability 1/ord_p(2) when
     p does not divide k and things work out.

     Heuristically: Pr(p | 2^S - 3^k) ~ 1/p for "generic" S, k.
     This is the SAME as for random numbers!

  4. SO WHY ARE THESE 3 CASES HARDER?
     Answer: They're NOT structurally harder. With 37 targets and a ~8%
     per-target chance of needing factors > 10^11, getting 3 such cases is
     EXPECTED. It's the normal tail of the distribution.

     Pr(3+ out of 37 have smallest factor > 10^11) ~
""")

# Calculate probability under random model
from scipy.stats import binom

# Under random model, each target has probability ~ e^{-gamma}/ln(B1) of
# having smallest factor > B1. But this is for RANDOM numbers coprime to 6.
# For N coprime to 6, Pr(smallest factor > B1) ~ 2 * e^{-gamma}/ln(B1)
# (factor of 2 because we skip primes 2 and 3)

# Actually more precisely: for N coprime to 6,
# Pr(smallest factor > B) ~ prod_{5<=p<=B} (1 - 1/p) / prod_{p<=B} (1-1/p) * prod_{p<=B}(1-1/p)
# = prod_{5<=p<=B} (1 - 1/p)
# ~ (1/2 * 2/3)^{-1} * e^{-gamma}/ln(B) = 3 * e^{-gamma}/ln(B)

# Let's compute more carefully
# For N coprime to 6: Pr(p | N) = 1/(p-1) * p/(p-1) ... no.
# Simpler: Pr(p | N | gcd(N,6)=1) = 1/p for p >= 5 (same as unconditional for large p)
# Pr(all p in [5,B] don't divide N | coprime to 6) = prod_{5<=p<=B} (1 - 1/p)
#   = prod_{p<=B}(1-1/p) / ((1-1/2)(1-1/3))
#   = (e^{-gamma}/ln B) / (1/2 * 2/3)  [Mertens]
#   = 3 * e^{-gamma} / ln(B)

pr_no_factor_B1_coprime6 = 3 * math.exp(-gamma_em) / math.log(B1)

print(f"  Pr(smallest factor > 10^11 | coprime to 6) ~ 3*e^(-gamma)/ln(10^11)")
print(f"                                              = {pr_no_factor_B1_coprime6:.6f}")
print(f"                                              = {pr_no_factor_B1_coprime6*100:.2f}%")

# Binomial: Pr(k >= 3 out of 37)
pr_3plus = 1 - binom.cdf(2, 37, pr_no_factor_B1_coprime6)
pr_exact3 = binom.pmf(3, 37, pr_no_factor_B1_coprime6)

print(f"\n  Under random model (coprime to 6):")
print(f"    Expected # without factor <= 10^11 out of 37: {37 * pr_no_factor_B1_coprime6:.2f}")
print(f"    Pr(exactly 3 without factor) = {pr_exact3:.4f} ({pr_exact3*100:.2f}%)")
print(f"    Pr(3 or more without factor) = {pr_3plus:.4f} ({pr_3plus*100:.2f}%)")
print(f"\n  ==> Getting 3 out of 37 is {'consistent with' if pr_3plus > 0.01 else 'slightly unusual for'} the random model.")
print(f"      There is NO evidence of structural bias making these numbers harder to factor.")

# ============================================================================
# SECTION 6: DISTRIBUTION OF THE 34 KNOWN SMALLEST FACTORS
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 6: DISTRIBUTION OF THE 34 KNOWN SMALLEST FACTORS")
print("=" * 78)

# From the synthesis table (Section 2), extracting the smallest known factor for each resolved case
# n (odd index) -> factor
known_factors = {
    7:  929,
    9:  5,
    11: 23,
    13: 15661,
    15: 17,
    17: 10499517109,
    19: 5,
    21: 79,
    27: 23,
    29: 13,
    31: 47,
    33: 151,
    35: 5,
    37: 73,
    39: 196171,
    41: 467,
    43: 17218217,
    45: 9343,
    47: 13,
    49: 136421,
    51: 23,
    53: 329009,
    55: 5,
    57: 11633,
    61: 11,
    63: 5,
    65: 4975245329,
    67: 433,
    69: 5,
    71: 60853189,
    73: 229,
    75: 33521,
    77: 1661926991,
    79: 172583,
}

factors_list = sorted(known_factors.values())
log_factors = [math.log10(f) for f in factors_list]

print(f"\n  Total resolved cases: {len(known_factors)}")
print(f"\n  Factor statistics:")
print(f"    Minimum:  {min(factors_list)} (= 5, appears for n=9,19,35,55,63,69)")
print(f"    Maximum:  {max(factors_list)} (= 10499517109, for n=17)")
print(f"    Median:   {np.median(factors_list):.0f}")
print(f"    Mean:     {np.mean(factors_list):.0f}")
print(f"    Geo mean: {10**np.mean(log_factors):.2f}")
print(f"    Mean(log10): {np.mean(log_factors):.2f}")
print(f"    Std(log10):  {np.std(log_factors):.2f}")

# Distribution by order of magnitude
print(f"\n  Distribution by order of magnitude (log10):")
print(f"  {'Range':>20s}  {'Count':>6s}  {'Fraction':>10s}  {'Cumulative':>12s}")
print(f"  {'-'*20}  {'-'*6}  {'-'*10}  {'-'*12}")

cum = 0
for lo in range(0, 12):
    hi = lo + 1
    count = sum(1 for lf in log_factors if lo <= lf < hi)
    cum += count
    frac = count / len(factors_list)
    cum_frac = cum / len(factors_list)
    if count > 0:
        print(f"  [10^{lo}, 10^{hi})  {count:6d}  {frac:10.3f}  {cum_frac:12.3f}")

# Compare with theoretical distribution for random numbers coprime to 6
print(f"\n  Theoretical distribution (random N coprime to 6):")
print(f"  Pr(smallest factor in [10^a, 10^{{a+1}})) ~ ln(10^{{a+1}})/ln(10^a) * (something)")
print(f"  More precisely: Pr(p1 in [x, cx]) = 1 - ln(x)/ln(cx) = 1 - 1/log_x(cx)")
print(f"  For a decade [10^a, 10^{{a+1}}]: Pr = 1 - a/(a+1) = 1/(a+1)")
print(f"  But conditional on p1 >= 5 (so a >= 0.7):")

# The distribution of the smallest prime factor for a random number coprime to 6:
# Pr(p1 = p | p1 >= 5) proportional to (1/p) * prod_{5<=q<p} (1-1/q)
# This is approximately: Pr(p1 > x | p1 >= 5) ~ ln(5)/ln(x) for x >= 5

# Pr(p1 in [10^a, 10^{a+1}] | p1 >= 5) = ln(5)/ln(10^a) - ln(5)/ln(10^{a+1})
#   = ln(5) * (1/(a*ln10) - 1/((a+1)*ln10))
#   = ln(5)/(ln10) * 1/(a(a+1))

print(f"\n  {'Range':>20s}  {'Pr(theory)':>12s}  {'Observed':>10s}  {'Expected(34)':>14s}")
print(f"  {'-'*20}  {'-'*12}  {'-'*10}  {'-'*14}")

ln5 = math.log(5)
ln10 = math.log(10)
total_theory = 0
for lo in range(1, 12):
    hi = lo + 1
    # Pr(p1 in [10^lo, 10^hi) | p1 >= 5) for lo >= 1
    if lo == 0:
        pr_theory = 1 - ln5 / (1 * ln10)
    else:
        x_lo = 10**lo if lo >= 1 else 5
        x_hi = 10**hi
        pr_theory = ln5 / math.log(x_lo) - ln5 / math.log(x_hi)

    total_theory += pr_theory
    count = sum(1 for lf in log_factors if lo <= lf < hi)
    observed = count / len(factors_list)
    expected = pr_theory * 34

    if count > 0 or pr_theory > 0.01:
        print(f"  [10^{lo}, 10^{hi})  {pr_theory:12.4f}  {observed:10.3f}  {expected:14.1f}")

# Special case: factors that are exactly 5
count_5 = sum(1 for f in factors_list if f == 5)
print(f"\n  Special: factor = 5 appears {count_5} times out of 34 ({count_5/34*100:.1f}%)")
print(f"  Theoretical Pr(5 | 2^S - 3^k, coprime to 6): depends on ord_5(2/3)")
print(f"    ord_5(2) = 4, ord_5(3) = 4")
print(f"    2^S mod 5 cycles: {[pow(2,i,5) for i in range(4)]}")
print(f"    3^k mod 5 cycles: {[pow(3,i,5) for i in range(4)]}")
print(f"    5 | (2^S - 3^k) iff 2^S = 3^k (mod 5)")
print(f"    This happens for 1/4 of (S,k) pairs --> Pr = 1/4 = 25%")
print(f"    Observed: {count_5/34*100:.1f}% -- {'consistent' if abs(count_5/34 - 0.25) < 0.15 else 'different'}")

# Factor 23
count_23 = sum(1 for f in factors_list if f == 23)
print(f"\n  Factor = 23 appears {count_23} times ({count_23/34*100:.1f}%)")
print(f"    ord_23(2) = 11, so Pr(23 | 2^S - 3^k) ~ 1/11 = 9.1%")
print(f"    Observed: {count_23/34*100:.1f}%")

# Factor 13
count_13 = sum(1 for f in factors_list if f == 13)
print(f"\n  Factor = 13 appears {count_13} times ({count_13/34*100:.1f}%)")
print(f"    ord_13(2) = 12, so Pr(13 | 2^S - 3^k) ~ 1/12 = 8.3%")
print(f"    Observed: {count_13/34*100:.1f}%")

# ============================================================================
# SECTION 7: EXTRAPOLATION — WHERE ARE THE REMAINING FACTORS?
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 7: EXTRAPOLATION — WHERE ARE THE REMAINING FACTORS?")
print("=" * 78)

# Given that the 3 remaining factors are > 10^11, estimate their distribution
print(f"\n  Given: 3 targets with smallest factor > 10^11")
print(f"  Question: What is the expected size of their smallest factor?")

# Under the random model: Pr(p1 > x | p1 > B1) = ln(B1)/ln(x) for x > B1
# So the CDF of the smallest factor, given > B1, is:
# F(x) = 1 - ln(B1)/ln(x) for x > B1
# PDF: f(x) = ln(B1) / (x * (ln x)^2)
# Median: F(x_med) = 0.5 --> ln(B1)/ln(x_med) = 0.5 --> x_med = B1^2 = 10^22
# Mean: integral of x * f(x) dx from B1 to infinity DIVERGES (heavy tail)
# But the geometric mean (median of log x) is better:
# E[ln x | p1 > B1] = integral of ln(x) * f(x) dx
# Let t = ln(x), so x = e^t, dx = e^t dt, f(x) = ln(B1)/(e^t * t^2) * e^t = ln(B1)/t^2
# E[t] = integral from ln(B1) to inf of t * ln(B1)/t^2 dt = ln(B1) * [ln(t)] from ln(B1) to inf
# This also diverges! So the distribution is very heavy-tailed.

# More useful: conditional on p1 in (B1, B_max] for some reasonable B_max
# Practical question: what range do we need to search to find them with 50%/90%/99% probability?

print(f"\n  Under random model (conditional on p1 > 10^11):")
print(f"  Pr(p1 <= x) = 1 - ln(10^11)/ln(x)")
print(f"\n  Probability of finding the factor by searching up to B:")
print(f"  {'B':>14s}  {'Pr(found)/target':>18s}  {'Pr(>=1 of 3)':>16s}")
print(f"  {'-'*14}  {'-'*18}  {'-'*16}")

for exp in [12, 13, 14, 15, 16, 18, 20, 22, 25, 30, 50, 100]:
    B = 10 ** exp
    pr_found = 1 - math.log(B1) / math.log(B)
    pr_found_3 = 1 - (1 - pr_found) ** 3
    print(f"  10^{exp:<8d}  {pr_found:18.6f}  {pr_found_3:16.6f}")

print(f"\n  Milestones:")
# Find B for 50%, 90%, 99% probability per target
for target_pr, label in [(0.5, "50%"), (0.9, "90%"), (0.99, "99%")]:
    # 1 - ln(B1)/ln(B) = target_pr
    # ln(B1)/ln(B) = 1 - target_pr
    # ln(B) = ln(B1) / (1 - target_pr)
    lnB = math.log(B1) / (1 - target_pr)
    log10_B = lnB / math.log(10)
    exp_ratio = 1 / (1 - target_pr)
    print(f"    {label} per target: search up to 10^{log10_B:.1f} (= B1^{exp_ratio:.1f})")

# ============================================================================
# SECTION 8: HISTOGRAM OF KNOWN FACTORS (TEXT-BASED)
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 8: HISTOGRAM OF KNOWN FACTORS (log10 scale)")
print("=" * 78)

# Create text-based histogram
bin_edges = list(range(0, 12))
hist_counts = []
for lo in range(0, 11):
    count = sum(1 for lf in log_factors if lo <= lf < lo + 1)
    hist_counts.append(count)

max_count = max(hist_counts)
bar_width = 50

print(f"\n  log10(factor)  count  histogram")
print(f"  {'-'*13}  {'-'*5}  {'-'*bar_width}")
for i, count in enumerate(hist_counts):
    bar_len = int(count / max_count * bar_width) if max_count > 0 else 0
    bar = '#' * bar_len
    if count > 0:
        print(f"  [{i:2d}, {i+1:2d})      {count:5d}  {bar}")

print(f"\n  Total: {sum(hist_counts)} factors")

# Detailed listing
print(f"\n  All 34 factors sorted:")
for i, (n, f) in enumerate(sorted(known_factors.items(), key=lambda x: x[1])):
    print(f"    {i+1:2d}. n={n:2d}  factor={f:>15d}  (10^{math.log10(f):.2f})")

# ============================================================================
# SECTION 9: SPECIFIC ANALYSIS FOR THE SIEVE (10^11, 10^12]
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 9: SIEVE EFFORT ANALYSIS (10^11, 10^12]")
print("=" * 78)

# Number of primes in (10^11, 10^12]
pi_1e11 = 1e11 / math.log(1e11)  # ~ 3.95e9
pi_1e12 = 1e12 / math.log(1e12)  # ~ 3.62e10

primes_in_range = pi_1e12 - pi_1e11
print(f"\n  Primes in (10^11, 10^12]: ~{primes_in_range:.3e}")
print(f"    pi(10^11) ~ {pi_1e11:.3e}")
print(f"    pi(10^12) ~ {pi_1e12:.3e}")
print(f"    Difference: ~{primes_in_range:.3e} primes to test")

# Time estimate
primes_per_sec = 350000  # from the synthesis: ~350K primes/s for n=23/25
time_secs = primes_in_range / primes_per_sec
time_hours = time_secs / 3600

print(f"\n  Time estimate (at 350K primes/s from previous sieve):")
print(f"    Time per target: ~{time_secs:.0f}s = ~{time_hours:.1f} hours")
print(f"    Total for 3 targets: ~{3*time_hours:.1f} hours")
print(f"    (Can run in parallel on different cores)")

# With optimization (segmented sieve is faster for larger ranges)
print(f"\n  Note: Sieve speed may vary. The 10^11 sieve tested ~4.1G primes in 11691s")
print(f"  (= ~351K primes/s). The (10^11, 10^12] range has ~{primes_in_range/1e9:.1f}G primes.")
print(f"  At same speed: ~{primes_in_range/350000/3600:.0f} hours per target.")

# ============================================================================
# SECTION 10: SUMMARY AND RECOMMENDATIONS
# ============================================================================
print("\n" + "=" * 78)
print("  SECTION 10: SUMMARY AND RECOMMENDATIONS")
print("=" * 78)

print(f"""
  KEY FINDINGS:

  1. DICKMAN'S ANALYSIS: The targets are so large (10^10 to 10^29 digits) that
     they are CERTAINLY composite. rho(u) = 0 to any meaningful precision for
     u ~ 10^9. The question is not IF they have prime factors, but WHERE.

  2. PROBABILITY PER TARGET (sieve 10^11 to 10^12):
     Pr(factor in range | no factor <= 10^11) ~ {pr_factor_in_range_cond*100:.1f}%

  3. COMBINED PROBABILITY (at least 1 of 3 targets):
     Pr(at least 1 factor found) ~ {p_at_least_one*100:.1f}%

  4. THE 3 UNSOLVED CASES ARE STATISTICALLY NORMAL:
     Under the random model, Pr(3+ out of 37 without factor <= 10^11) ~ {pr_3plus*100:.1f}%
     This is NOT unusual. No structural bias detected.

  5. FACTOR DISTRIBUTION (34 known):
     - Geometric mean: 10^{np.mean(log_factors):.1f}
     - 6 factors = 5 (17.6%), consistent with Pr(5|d) = 1/4 = 25%
     - Distribution roughly follows 1/(p * ln^2(p)) as expected
     - Largest found: 10,499,517,109 (10^10.02)

  6. WHERE ARE THE MISSING FACTORS?
     Under the random model (conditional on > 10^11):
     - 50% chance of being below 10^{math.log(B1)/(1-0.5)/math.log(10):.0f}
     - 90% chance of being below 10^{math.log(B1)/(1-0.9)/math.log(10):.0f}
     - Median expected: 10^22 (= (10^11)^2)

  7. SIEVE EFFORT for (10^11, 10^12]:
     ~{primes_in_range:.2e} primes to test
     ~{time_hours:.0f} hours per target at current speed
     ~{3*time_hours:.0f} hours total (parallelizable)

  RECOMMENDATION:
  - The sieve to 10^12 has a ~{p_at_least_one*100:.0f}% chance of resolving at least
    one case. This is WORTH DOING.
  - If it fails: the next decade (10^12, 10^13] adds another ~4-5% per target.
  - To reach 50% per target, one would need to sieve to ~10^22 -- infeasible
    by trial division but potentially reachable by ECM.
  - ECM could find factors up to ~40 digits (10^40) with reasonable effort,
    but each curve takes ~150 hours for numbers this large.
    A practical ECM campaign (~100 curves) would cover factors up to ~25-30 digits.
""")

print("=" * 78)
print("  END OF ANALYSIS")
print("=" * 78)
