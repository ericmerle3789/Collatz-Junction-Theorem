#!/usr/bin/env python3
"""R181_verify_contradiction.py — Independent verification of the claimed
coefficient c = 3/(5·ln6) in the Collatz cycle contradiction argument.

CLAIM UNDER EXAMINATION:
  For a hypothetical Collatz cycle of compressed length x through odd numbers
  B_0, ..., B_{x-1}, the cumulative rotation error satisfies:
    E ≈ c · Σ(1/B_i)  with c = 3/(5·ln6)
  Combined with the product constraint Σ(1/B_i) ≈ 3d/3^x and the cycle
  equation E = log_6(1 + d/3^x), this gives 9·2^S/(5·3^x) = 1, which
  contradicts 2^S/3^x ≈ 1.

THIS SCRIPT derives everything from first principles and checks whether
the coefficient c is correct.

Author: Independent verification (Claude, from scratch)
Date: 15 March 2026
"""

import math
from typing import List, Tuple
from fractions import Fraction

# ==========================================================================
# Constants
# ==========================================================================
LN2 = math.log(2)
LN3 = math.log(3)
LN6 = math.log(6)
LOG6_2 = LN2 / LN6
LOG6_3 = LN3 / LN6
ALPHA = LOG6_3

print("=" * 80)
print("INDEPENDENT VERIFICATION: Collatz cycle contradiction coefficient")
print("=" * 80)
print(f"  α = log_6(3) = {ALPHA:.15f}")
print(f"  1-α = log_6(2) = {LOG6_2:.15f}")
print(f"  ln(6) = {LN6:.15f}")
print()

# ==========================================================================
# PART 1: Exact rotation formulas from first principles
# ==========================================================================

def phi(n):
    """φ(n) = frac(log_6(n + 1/5))"""
    return math.log(n + 0.2) / LN6 % 1.0

def phi_exact(n):
    """φ(n) = log_6(n + 1/5), WITHOUT taking fractional part."""
    return math.log(n + 0.2) / LN6


def epsilon_odd_exact(B):
    """EXACT error for odd step B → 3B+1.

    Derivation:
      φ(3B+1) - φ(B) = log_6((3B+1+1/5)/(B+1/5))
                       = log_6((15B+6)/(5B+1))
                       = log_6(3·(5B+2)/(5B+1))
                       = log_6(3) + log_6(1 + 1/(5B+1))
    So ε_odd(B) = log_6(1 + 1/(5B+1)).
    """
    return math.log1p(1.0 / (5*B + 1)) / LN6


def epsilon_even_exact(m):
    """EXACT error for even step m → m/2.

    Derivation:
      φ(m/2) - φ(m) = log_6((m/2 + 1/5)/(m + 1/5))
                     = log_6((5m+2)/(10) / ((5m+1)/5))
                     = log_6((5m+2)/(2(5m+1)))
                     = -log_6(2) + log_6((5m+2)/(5m+1))
                     = -log_6(2) + log_6(1 + 1/(5m+1))
    So ε_even(m) = log_6(1 + 1/(5m+1)).

    NOTE: This is the SAME formula as ε_odd, just with m in place of B!
    Both errors equal log_6(1 + 1/(5n+1)) where n is the input.
    """
    return math.log1p(1.0 / (5*m + 1)) / LN6


print("=" * 80)
print("PART 1: Verify exact error formulas")
print("=" * 80)
print()

# Verify odd step
print("  Odd step verification (B → 3B+1):")
print(f"  {'B':>8s}  {'φ(3B+1)-φ(B)-α':>18s}  {'formula':>18s}  {'match':>6s}")
for B in [1, 3, 5, 7, 11, 27, 97, 999, 9999]:
    direct = (phi_exact(3*B+1) - phi_exact(B)) % 1.0
    if direct > 0.5: direct -= 1.0
    rotation_part = ALPHA
    err = direct - rotation_part
    formula = epsilon_odd_exact(B)
    match = abs(err - formula) < 1e-12
    print(f"  {B:>8d}  {err:>18.14f}  {formula:>18.14f}  {'OK' if match else 'FAIL':>6s}")

print()

# Verify even step
print("  Even step verification (m → m/2, m even):")
print(f"  {'m':>8s}  {'φ(m/2)-φ(m)+log6(2)':>20s}  {'formula':>18s}  {'match':>6s}")
for m in [2, 4, 6, 10, 28, 82, 100, 998, 10000]:
    direct = (phi_exact(m//2) - phi_exact(m)) % 1.0
    if direct > 0.5: direct -= 1.0
    rotation_part = -LOG6_2
    err = direct - rotation_part
    formula = epsilon_even_exact(m)
    match = abs(err - formula) < 1e-12
    print(f"  {m:>8d}  {err:>20.14f}  {formula:>18.14f}  {'OK' if match else 'FAIL':>6s}")

print()

# KEY CHECK: Is ε_even = log_6(1+1/(5m+1)) or log_6(1+2/(5m+2))?
print("  CRITICAL CHECK: ε_even formula")
print("  R181 claims: ε_even(m) = log_6(1 + 2/(5m+2))")
print("  Our derivation: ε_even(m) = log_6(1 + 1/(5m+1))")
print()
print(f"  {'m':>8s}  {'direct':>18s}  {'1/(5m+1)':>18s}  {'2/(5m+2)':>18s}  {'correct':>10s}")
for m in [4, 10, 28, 100, 1000, 10000]:
    direct = (phi_exact(m//2) - phi_exact(m) + LOG6_2)
    f1 = math.log1p(1.0/(5*m+1)) / LN6  # our formula
    f2 = math.log1p(2.0/(5*m+2)) / LN6  # R181 formula
    which = "1/(5m+1)" if abs(direct - f1) < abs(direct - f2) else "2/(5m+2)"
    print(f"  {m:>8d}  {direct:>18.14f}  {f1:>18.14f}  {f2:>18.14f}  {which:>10s}")

print()

# ==========================================================================
# PART 2: Compressed Collatz orbit and EXACT cumulative error
# ==========================================================================

def compressed_orbit(n, max_steps=5000):
    """Compute compressed Collatz orbit starting from odd n.
    Returns list of (B_i, v_i) pairs."""
    B = n
    if B % 2 == 0:
        while B % 2 == 0:
            B //= 2
    orbit = []
    for _ in range(max_steps):
        m = 3*B + 1
        v = 0
        while m % 2 == 0:
            m //= 2
            v += 1
        orbit.append((B, v))
        B = m
        if B == 1:
            break
    return orbit


def exact_cumulative_error(orbit):
    """Compute EXACT cumulative error E for a compressed orbit.

    For each compressed step B_i → B_{i+1}:
      1. Odd step: B_i → 3B_i+1, error = log_6(1 + 1/(5B_i+1))
      2. Even steps: m → m/2 for each of v_i halvings
         Intermediate values: m_j = (3B_i+1)/2^j for j=0,...,v_i-1
         Each gives error log_6(1 + 1/(5m_j+1))

    Total error = sum of all these terms.
    """
    E = 0.0
    for B_i, v_i in orbit:
        # Odd step error
        E += math.log1p(1.0 / (5*B_i + 1)) / LN6

        # Even step errors
        m = 3*B_i + 1  # first intermediate (even) value
        for j in range(v_i):
            E += math.log1p(1.0 / (5*m + 1)) / LN6
            m //= 2  # next intermediate value

    return E


def exact_cumulative_error_R181(orbit):
    """Compute cumulative error using the R181 WRONG even formula.
    Uses log_6(1 + 2/(5m+2)) for even steps instead of log_6(1 + 1/(5m+1)).
    """
    E = 0.0
    for B_i, v_i in orbit:
        # Odd step error (same)
        E += math.log1p(1.0 / (5*B_i + 1)) / LN6

        # Even step errors (R181 formula)
        m = 3*B_i + 1
        for j in range(v_i):
            E += math.log1p(2.0 / (5*m + 2)) / LN6
            m //= 2

    return E


print("=" * 80)
print("PART 2: Exact cumulative error on orbits")
print("=" * 80)
print()

# Verify against direct phi computation
print("  Cross-check: exact E vs direct φ computation")
print(f"  {'B_0':>8s}  {'steps':>6s}  {'E_exact':>16s}  {'E_direct':>16s}  {'match':>6s}")

for B0 in [3, 7, 27, 97, 871, 6171]:
    orbit = compressed_orbit(B0)
    E_exact = exact_cumulative_error(orbit)

    # Direct: φ(B_final) - φ(B_0) - x·α + S·(1-α) where x=odd steps, S=total even steps
    x = len(orbit)
    S = sum(v for _, v in orbit)
    B_final = 1  # all orbits reach 1

    # The total rotation should be:
    # φ(1) - φ(B0) = x·α - S·(1-α) + E  (mod integers)
    # So E = φ(1) - φ(B0) - x·α + S·log_6(2) (mod integers)
    E_direct_raw = phi_exact(1) - phi_exact(B0) - x * ALPHA + S * LOG6_2
    # This should differ from E_exact by an integer
    diff = E_exact - E_direct_raw
    # Round to nearest integer
    n_int = round(diff)
    residual = abs(diff - n_int)

    match = residual < 1e-8
    print(f"  {B0:>8d}  {x:>6d}  {E_exact:>16.10f}  {E_direct_raw:>16.10f}  "
          f"{'OK' if match else 'FAIL':>6s}  (diff={diff:.4f}, int={n_int})")

print()

# ==========================================================================
# PART 3: Fit coefficient c in E ≈ c · Σ(1/B_i)
# ==========================================================================

print("=" * 80)
print("PART 3: Determine the TRUE coefficient c")
print("=" * 80)
print()

# For orbits (not cycles), compute E and Σ(1/B_i) and fit c
print("  For orbits: E_exact, Σ(1/B_i), ratio c = E/Σ(1/B_i)")
print()

# Also compute the decomposition: odd part and even part separately
print(f"  {'B_0':>8s}  {'x':>5s}  {'E_exact':>14s}  {'E_odd':>14s}  {'E_even':>14s}  "
      f"{'Σ1/B':>14s}  {'c=E/Σ':>10s}  {'c_odd':>10s}  {'c_even':>10s}")

c_values = []
c_odd_values = []
c_even_values = []

for B0 in [27, 97, 231, 871, 4591, 6171, 77031, 837799, 1723519]:
    orbit = compressed_orbit(B0)

    E_odd = 0.0
    E_even = 0.0
    sum_inv_B = 0.0
    sum_inv_Bnext = 0.0

    for i, (B_i, v_i) in enumerate(orbit):
        sum_inv_B += 1.0 / B_i

        # Odd part
        E_odd += math.log1p(1.0 / (5*B_i + 1)) / LN6

        # Even part
        m = 3*B_i + 1
        for j in range(v_i):
            E_even += math.log1p(1.0 / (5*m + 1)) / LN6
            m //= 2

        # Track B_{i+1}
        B_next = (3*B_i + 1) >> v_i  # = B_{i+1}
        sum_inv_Bnext += 1.0 / B_next

    E_total = E_odd + E_even
    x = len(orbit)

    if sum_inv_B > 0:
        c_total = E_total / sum_inv_B
        c_o = E_odd / sum_inv_B
        c_e = E_even / sum_inv_B

        c_values.append(c_total)
        c_odd_values.append(c_o)
        c_even_values.append(c_e)

        print(f"  {B0:>8d}  {x:>5d}  {E_total:>14.8f}  {E_odd:>14.8f}  {E_even:>14.8f}  "
              f"{sum_inv_B:>14.8f}  {c_total:>10.6f}  {c_o:>10.6f}  {c_e:>10.6f}")

print()
print(f"  Mean c = {sum(c_values)/len(c_values):.6f}")
print(f"  Mean c_odd = {sum(c_odd_values)/len(c_odd_values):.6f}")
print(f"  Mean c_even = {sum(c_even_values)/len(c_even_values):.6f}")
print()

c_claimed = 3.0 / (5 * LN6)
c_alt1 = 1.0 / (3 * LN6)
c_alt2 = 2.0 / (5 * LN6)
c_odd_theory = 1.0 / (5 * LN6)

print("  COMPARISON WITH CLAIMED VALUES:")
print(f"    c_claimed  = 3/(5·ln6) = {c_claimed:.6f}")
print(f"    c_alt1     = 1/(3·ln6) = {c_alt1:.6f}")
print(f"    c_alt2     = 2/(5·ln6) = {c_alt2:.6f}")
print(f"    c_odd_th   = 1/(5·ln6) = {c_odd_theory:.6f}")
print()
print("  NOTE: c depends on the orbit! It is NOT a universal constant for")
print("  general orbits because Σ(1/B_{i+1}) ≠ Σ(1/B_i) for non-cycles.")
print("  The coefficient c has meaning only in the cycle context.")
print()

# ==========================================================================
# PART 4: Cycle-specific analysis with the EXACT formulas
# ==========================================================================

print("=" * 80)
print("PART 4: Cycle-specific coefficient derivation")
print("=" * 80)
print()

print("  For a CYCLE B_0 → B_1 → ... → B_{x-1} → B_0:")
print()
print("  E = Σ_i ε_odd(B_i) + Σ_i Σ_{j=0}^{v_i-1} ε_even(m_{i,j})")
print()
print("  Odd part:  Σ log_6(1 + 1/(5B_i+1))")
print("           ≈ Σ 1/((5B_i+1)·ln6)")
print("           ≈ (1/(5·ln6)) · Σ 1/B_i")
print()
print("  Even part: For step i, intermediates m_{i,j} = (3B_i+1)/2^j")
print("    Σ_{j=0}^{v_i-1} log_6(1+1/(5m_{i,j}+1))")
print("    ≈ Σ_{j=0}^{v_i-1} 1/((5·(3B_i+1)/2^j+1)·ln6)")
print("    ≈ Σ_{j=0}^{v_i-1} 2^j/((5·(3B_i+1))·ln6)")
print("    = (2^{v_i}-1)/(5·(3B_i+1)·ln6)")
print()
print("  Since B_{i+1} = (3B_i+1)/2^{v_i}, we have 3B_i+1 = B_{i+1}·2^{v_i}.")
print("  So: (2^{v_i}-1)/(5·B_{i+1}·2^{v_i}·ln6)")
print("     = (1 - 2^{-v_i})/(5·B_{i+1}·ln6)")
print()
print("  Summing over all steps:")
print("    E_even ≈ (1/(5·ln6)) · Σ_i (1-2^{-v_i})/B_{i+1}")
print()
print("  For a CYCLE, Σ f(B_{i+1}) = Σ f(B_i) (cyclic relabeling).")
print("  BUT (1-2^{-v_i}) depends on i, so we CANNOT simply replace!")
print()
print("  More precisely:")
print("    E_even ≈ (1/(5·ln6)) · [Σ 1/B_{i+1} - Σ 2^{-v_i}/B_{i+1}]")
print("           = (1/(5·ln6)) · [Σ 1/B_i - Σ 2^{-v_i}/B_{i+1}]")
print()
print("  The correction term Σ 2^{-v_i}/B_{i+1} is NOT zero in general.")
print("  For v_i ≥ 2, each term is ≤ 1/(4·B_{i+1}), but for v_i = 1,")
print("  the term is 1/(2·B_{i+1}) which can be significant.")
print()
print("  THEREFORE the true coefficient for cycles is:")
print("    E ≈ (1/(5·ln6))[Σ 1/B_i + Σ 1/B_i - Σ 2^{-v_i}/B_{i+1}]")
print("      = (2/(5·ln6)) · Σ 1/B_i - (1/(5·ln6)) · Σ 2^{-v_i}/B_{i+1}")
print()
print("  The R181 derivation claims c = 3/(5·ln6) which would require:")
print("    E_even ≈ (2/(5·ln6)) · Σ 1/B_i")
print("  i.e., the even-step error contributes TWICE the odd-step error.")
print("  This is ONLY true if ε_even has a factor of 2 (which it doesn't).")
print()

# ==========================================================================
# PART 5: The trivial cycle k=1 as ground truth
# ==========================================================================

print("=" * 80)
print("PART 5: Ground truth — the trivial cycle k=1")
print("=" * 80)
print()

print("  The trivial cycle: 1 → 4 → 2 → 1")
print("  Compressed: B_0 = 1, v_0 = 2, x = 1, S = 2")
print("  d = 2^2 - 3^1 = 4 - 3 = 1")
print()

# EXACT computation for trivial cycle
B0, v0 = 1, 2
x, S = 1, 2
d = (1 << S) - 3**x

# Cycle equation: E = log_6(2^S/3^x) = log_6(4/3)
E_required = math.log(2**S / 3**x) / LN6
print(f"  E_required = log_6(2^S/3^x) = log_6(4/3) = {E_required:.15f}")

# Exact computation of E
# Odd step: 1 → 4, ε = log_6(1 + 1/6) = log_6(7/6)
eps_odd = math.log(7/6) / LN6
print(f"  ε_odd(1)  = log_6(7/6) = {eps_odd:.15f}")

# Even step 1: 4 → 2, ε = log_6(1 + 1/21) = log_6(22/21)
m1 = 4
eps_even1 = math.log1p(1.0/(5*m1+1)) / LN6
print(f"  ε_even(4) = log_6(1+1/21) = log_6(22/21) = {eps_even1:.15f}")

# Even step 2: 2 → 1, ε = log_6(1 + 1/11) = log_6(12/11)
m2 = 2
eps_even2 = math.log1p(1.0/(5*m2+1)) / LN6
print(f"  ε_even(2) = log_6(1+1/11) = log_6(12/11) = {eps_even2:.15f}")

E_computed = eps_odd + eps_even1 + eps_even2
print(f"  E_computed = {E_computed:.15f}")
print(f"  E_required = {E_required:.15f}")
print(f"  Match: {abs(E_computed - E_required) < 1e-12}")
print()

# Verify with exact fractions
print("  EXACT fraction check:")
print("  E = log_6(7/6) + log_6(22/21) + log_6(12/11)")
print(f"    = log_6(7·22·12 / (6·21·11))")
prod_num = 7 * 22 * 12
prod_den = 6 * 21 * 11
print(f"    = log_6({prod_num}/{prod_den})")
print(f"    = log_6({Fraction(prod_num, prod_den)})")
from math import gcd
g = gcd(prod_num, prod_den)
print(f"    = log_6({prod_num//g}/{prod_den//g})")
print(f"    = log_6(4/3)")
print(f"  4/3 = {4/3}, {prod_num//g}/{prod_den//g} = {prod_num/prod_den}")
print(f"  EXACT MATCH: {prod_num * 3 == prod_den * 4}")
print()

# Now check if the leading-order formula works for k=1
sum_inv_B = 1.0  # Σ 1/B_i = 1/1 = 1
print(f"  Σ(1/B_i) = {sum_inv_B}")
print(f"  c_claimed · Σ(1/B_i) = {c_claimed * sum_inv_B:.6f}")
print(f"  c_alt2 · Σ(1/B_i)   = {c_alt2 * sum_inv_B:.6f}")
print(f"  E_required           = {E_required:.6f}")
print()
c_true_k1 = E_required / sum_inv_B
print(f"  TRUE c for k=1 cycle = E/Σ(1/B) = {c_true_k1:.10f}")
print(f"  = log_6(4/3) = {math.log(4/3)/LN6:.10f}")
print()
print(f"  Compare:")
print(f"    3/(5·ln6) = {c_claimed:.10f}  (R181 claim)")
print(f"    2/(5·ln6) = {c_alt2:.10f}")
print(f"    1/(3·ln6) = {c_alt1:.10f}")
print(f"    true (k=1) = {c_true_k1:.10f}")
print()

# For k=1: check what ratio the contradiction argument gives
print("  What ratio does the contradiction argument give for k=1?")
print(f"  If c = 3/(5·ln6): c · Σ(1/B) · 3^x · ln6 / d = {c_claimed * sum_inv_B * 3**x * LN6 / d:.6f}")
print(f"  Required: 1.0 (for a valid cycle)")
print(f"  Using c_true: {c_true_k1 * sum_inv_B * 3**x * LN6 / d:.6f}")
print()

# More detailed: the contradiction chain for k=1
print("  CONTRADICTION CHAIN for k=1:")
print(f"    Product constraint: Σ 1/(3B_i) = ln(1+d/3^x)/1 ... wait")
print()

# The product constraint is:
# Σ ln(1 + 1/(3B_i)) = ln(2^S/3^x)
# For k=1: ln(1 + 1/3) = ln(4/3)
prod_lhs = math.log(1 + 1.0/(3*1))
prod_rhs = math.log(2**S / 3**x)
print(f"    Σ ln(1+1/(3B_i)) = ln(1+1/3) = {prod_lhs:.15f}")
print(f"    ln(2^S/3^x) = ln(4/3) = {prod_rhs:.15f}")
print(f"    Match: {abs(prod_lhs - prod_rhs) < 1e-14}")
print()
print(f"    So the 'first-order' Σ 1/(3B_i) ≈ d/3^x is:")
print(f"    1/3 ≈ {d / 3**x:.6f}  ({1/3:.6f} vs {1/3:.6f})")
print(f"    This is EXACT for k=1 because d/3^x = 1/3 and 1/(3·1) = 1/3.")
print()
print(f"    So Σ 1/B_i = 3·d/3^x = {3*d/3**x:.6f} = {3*1/3:.6f} = 1. CORRECT.")
print()

# ==========================================================================
# PART 6: Numerical determination of the cycle-specific coefficient
# ==========================================================================

print("=" * 80)
print("PART 6: What coefficient would make cycles consistent?")
print("=" * 80)
print()

print("  For a cycle with parameters (S, x, d):")
print("    E = log_6(2^S/3^x) = log_6(1 + d/3^x)")
print("    Product constraint: Σ 1/B_i ≈ 3d/3^x  (first order)")
print()
print("  So the effective c = E / Σ(1/B_i) = log_6(1+d/3^x) / (3d/3^x)")
print("  For small d/3^x: ≈ (d/(3^x·ln6)) / (3d/3^x) = 1/(3·ln6)")
print()
print(f"  c_asymptotic = 1/(3·ln6) = {1/(3*LN6):.10f}")
print()

# Check this for convergents of log_2(3)
convergents_S_x = [
    (2, 1), (5, 3), (8, 5), (19, 12), (46, 29), (65, 41),
    (84, 53), (485, 306), (1054, 665), (24727, 15601)
]

print("  Checking c_needed = E / (3d/3^x) for convergents of log_2(3):")
print(f"  {'S':>6s}  {'x':>6s}  {'d/3^x':>14s}  {'c_needed':>14s}  {'1/(3ln6)':>14s}")

for S, x in convergents_S_x:
    d = (1 << S) - 3**x
    if d <= 0:
        continue
    # Use Fraction or log arithmetic for large values
    from decimal import Decimal, getcontext
    getcontext().prec = 50
    d_over_3x = float(Decimal(d) / Decimal(3)**x)
    if d_over_3x > 0:
        E = math.log1p(d_over_3x) / LN6
        sum_inv_approx = 3.0 * d_over_3x
        c_needed = E / sum_inv_approx
        print(f"  {S:>6d}  {x:>6d}  {d_over_3x:>14.6e}  "
              f"{c_needed:>14.10f}  {1/(3*LN6):>14.10f}")

print()
print(f"  As d/3^x → 0, c_needed → 1/(3·ln6) = {1/(3*LN6):.10f}")
print(f"  NOT 3/(5·ln6) = {3/(5*LN6):.10f}")
print()

# ==========================================================================
# PART 7: Where exactly does the R181 derivation go wrong?
# ==========================================================================

print("=" * 80)
print("PART 7: Identifying the error in R181")
print("=" * 80)
print()

print("  R181 claims ε_even(m) = log_6(1 + 2/(5m+2)).")
print("  The CORRECT formula is ε_even(m) = log_6(1 + 1/(5m+1)).")
print()
print("  For large m: 2/(5m+2) ≈ 2/(5m), while 1/(5m+1) ≈ 1/(5m).")
print("  So R181 overestimates the even-step error by a factor of ~2.")
print()
print("  This factor of 2 propagates as follows:")
print("    R181: E_even ≈ (2/(5·ln6)) · Σ 1/B_{i+1}")
print("    TRUE: E_even ≈ (1/(5·ln6)) · Σ (1-2^{-v_i})/B_{i+1}")
print()
print("  For a cycle (Σ 1/B_{i+1} = Σ 1/B_i):")
print("    R181: E ≈ (1/(5·ln6) + 2/(5·ln6)) · Σ 1/B_i = 3/(5·ln6) · Σ 1/B_i")
print("    TRUE: E ≈ (1/(5·ln6) + (1-<2^{-v}>)/(5·ln6)) · Σ 1/B_i")
print("          ≈ (2-<2^{-v}>)/(5·ln6) · Σ 1/B_i")
print()
print("  where <2^{-v}> is a weighted average of 2^{-v_i}/B_{i+1} over 1/B_{i+1}.")
print()
print("  But even with the TRUE coefficient, we need to check whether")
print("  a contradiction still arises.")
print()

# Compute actual E_even/Σ(1/B_{i+1}) for orbits
print("  Numerical check: E_even / Σ(1/B_{i+1}) for various orbits")
print(f"  {'B_0':>8s}  {'E_even/Σ(1/B_next)':>20s}  {'1/(5ln6)':>14s}  {'2/(5ln6)':>14s}  {'ratio to 1/5ln6':>16s}")

for B0 in [27, 97, 871, 6171, 77031, 837799]:
    orbit = compressed_orbit(B0)
    E_even = 0.0
    sum_inv_Bnext = 0.0

    for B_i, v_i in orbit:
        m = 3*B_i + 1
        for j in range(v_i):
            E_even += math.log1p(1.0 / (5*m + 1)) / LN6
            m //= 2
        B_next = (3*B_i + 1) >> v_i
        sum_inv_Bnext += 1.0 / B_next

    if sum_inv_Bnext > 0:
        ratio = E_even / sum_inv_Bnext
        print(f"  {B0:>8d}  {ratio:>20.10f}  {1/(5*LN6):>14.10f}  {2/(5*LN6):>14.10f}  {ratio * 5 * LN6:>16.10f}")

print()
print(f"  Theory: E_even/Σ(1/B_next) should approach 1/(5·ln6) = {1/(5*LN6):.10f}")
print(f"  (not 2/(5·ln6) = {2/(5*LN6):.10f} as R181 claims)")
print()

# ==========================================================================
# PART 8: Does a contradiction still exist with the correct coefficient?
# ==========================================================================

print("=" * 80)
print("PART 8: Does a contradiction still exist with c = 1/(3·ln6)?")
print("=" * 80)
print()

print("  With the CORRECT asymptotic coefficient c = 1/(3·ln6):")
print("    E ≈ (1/(3·ln6)) · Σ 1/B_i")
print("    Σ 1/B_i ≈ 3d/3^x")
print("    E ≈ (1/(3·ln6)) · 3d/3^x = d/(3^x·ln6)")
print()
print("  The cycle equation requires:")
print("    E = log_6(2^S/3^x) ≈ d/(3^x·ln6)  (for small d/3^x)")
print()
print("  So: d/(3^x·ln6) ≈ d/(3^x·ln6)")
print()
print("  THIS IS AUTOMATICALLY SATISFIED! There is NO contradiction!")
print()
print("  The ratio is:")
print("    E_from_product / E_required = (d/(3^x·ln6)) / (d/(3^x·ln6)) = 1")
print()
print("  Equivalently:")
print("    c · 3/3^x · ln6 · 2^S = (1/(3·ln6)) · 3 · ln6 · 2^S/3^x")
print("    = (1/3) · 3 · (2^S/3^x) = 2^S/3^x ≈ 1")
print()
print("  So the 'ratio' is just 2^S/3^x ≈ 1. No contradiction.")
print()

# Now let's see what happens with the exact (not asymptotic) coefficient
print("  MORE CAREFUL ANALYSIS:")
print("  The exact odd part is Σ log_6(1+1/(5B_i+1)), not Σ 1/(5B_i·ln6).")
print("  The exact product constraint is Σ ln(1+1/(3B_i)) = ln(2^S/3^x).")
print()
print("  Combining EXACTLY:")
print("    E = Σ [log_6(1+1/(5B_i+1)) + Σ_j log_6(1+1/(5m_{i,j}+1))]")
print("    ln(2^S/3^x) = Σ ln(1+1/(3B_i))")
print()
print("  These are related by:")
print("    1/(5n+1) vs 1/(3n): asymptotically ratio = 3/5")
print("    log_6(1+x)/ln(1+y) = (1/ln6) · x/y to leading order")
print()
print("  So E/ln(2^S/3^x) ≈ (1/ln6) · [Σ 1/(5B_i) + Σ_i Σ_j 1/(5m_{i,j})] / [Σ 1/(3B_i)]")
print()

# Let's compute this ratio exactly for convergents
print("  Computing EXACT ratio E_exact / E_required for the trivial cycle k=1:")
print(f"    E_exact = log_6(4/3) = {math.log(4/3)/LN6:.15f}")
print(f"    E_required = log_6(4/3) = {math.log(4/3)/LN6:.15f}")
print(f"    Ratio = 1.000000000000000 (trivially, since it's a real cycle)")
print()
print("  The issue is: for a HYPOTHETICAL cycle with k > 1, would the ratio be 1?")
print()
print("  The rotation equation E = log_6(2^S/3^x) is EXACT for any cycle.")
print("  The product constraint Σ ln(1+1/(3B_i)) = ln(2^S/3^x) is also EXACT.")
print("  Both hold simultaneously by construction. There is no contradiction")
print("  at the level of these identities.")
print()
print("  The R181 'contradiction' arose from using the WRONG even-step coefficient")
print("  (factor of 2 error), which made the two constraints inconsistent.")
print("  With the correct coefficient, they are automatically consistent.")
print()

# ==========================================================================
# PART 9: Verify the even-step formula algebraically
# ==========================================================================

print("=" * 80)
print("PART 9: Algebraic verification of even-step formula")
print("=" * 80)
print()

print("  Computing φ(m/2) - φ(m) + log_6(2) for various even m:")
print("  This should equal ε_even(m).")
print()
print(f"  {'m':>8s}  {'log6(1+1/(5m+1))':>20s}  {'log6(1+2/(5m+2))':>20s}  {'direct':>20s}")

for m in [2, 4, 6, 10, 20, 50, 100, 1000, 10000]:
    f_correct = math.log1p(1.0/(5*m+1)) / LN6
    f_r181 = math.log1p(2.0/(5*m+2)) / LN6
    direct = phi_exact(m//2) - phi_exact(m) + LOG6_2
    # Adjust for mod 1
    while direct < -0.5: direct += 1
    while direct > 0.5: direct -= 1
    print(f"  {m:>8d}  {f_correct:>20.15f}  {f_r181:>20.15f}  {direct:>20.15f}")

print()
print("  Observation: the CORRECT formula log_6(1+1/(5m+1)) matches 'direct' exactly.")
print("  The R181 formula log_6(1+2/(5m+2)) does NOT match.")
print()

# Show the algebra error in R181
print("  WHERE R181 WENT WRONG:")
print("  R181 line 175 claims: φ(n/2) - φ(n) = log_6((5n+4)/(2(5n+2)))")
print()
print("  Let's check: n/2 + 1/5 = (5n+2)/10")
print("               n + 1/5   = (5n+1)/5")
print("  Ratio = (5n+2)/10 / ((5n+1)/5) = (5n+2)/(2(5n+1))")
print("  This gives: log_6((5n+2)/(2(5n+1))) = -log_6(2) + log_6((5n+2)/(5n+1))")
print("            = -log_6(2) + log_6(1 + 1/(5n+1))")
print()
print("  R181 wrote (5n+4)/(2(5n+2)) instead of (5n+2)/(2(5n+1)).")
print("  This looks like a substitution error: perhaps confusing")
print("  n + 2/5 with n/2 + 2/5, or 5(n/2)+2 with 5n+4.")
print()
print("  Specifically: (5n+4)/(2(5n+2)) - (5n+2)/(2(5n+1))")
print("  For n=4: (24)/(2·22) = 24/44 = 6/11 ≈ 0.5455")
print(f"           vs (22)/(2·21) = 22/42 = 11/21 ≈ {11/21:.4f}")
print()

# ==========================================================================
# PART 10: Attempting alternative contradiction arguments
# ==========================================================================

print("=" * 80)
print("PART 10: Can any contradiction be salvaged?")
print("=" * 80)
print()

print("  The leading-order analysis gives no contradiction.")
print("  Could HIGHER-ORDER terms create one?")
print()
print("  Exact cycle equations (no approximation):")
print("  (a) E = log_6(2^S/3^x)  [rotation return]")
print("  (b) Σ ln(1+1/(3B_i)) = ln(2^S/3^x)  [product return]")
print()
print("  From (a): E = ln(2^S/3^x) / ln6")
print("  From (b): E = Σ ln(1+1/(3B_i)) / ln6")
print()
print("  Wait -- these are NOT the same! (a) and (b) don't directly")
print("  equate because E involves errors at 1/(5B+1) not 1/(3B).")
print()
print("  Let's be precise about what E equals in terms of the B_i.")
print()

# The exact E for a cycle
print("  For a hypothetical cycle:")
print("  E = Σ_i [log_6(1+1/(5B_i+1)) + Σ_{j=0}^{v_i-1} log_6(1+1/(5m_{i,j}+1))]")
print("  where m_{i,j} = (3B_i+1)/2^j")
print()
print("  And E = log_6(2^S/3^x)  ... (cycle equation)")
print()
print("  Also: Σ ln(1+1/(3B_i)) = ln(2^S/3^x) ... (product equation)")
print()
print("  So: E · ln6 = Σ ln(1+1/(3B_i))")
print("  And: E = Σ [log_6(1+1/(5B_i+1)) + even parts]")
print("  I.e.: Σ ln(1+1/(3B_i)) = Σ [ln(1+1/(5B_i+1)) + even parts]")
print()
print("  This is a NONTRIVIAL identity that must be satisfied by cycle B_i.")
print("  Let's check whether it's automatically true or imposes constraints.")
print()

# For the trivial cycle k=1:
print("  Trivial cycle (B=1, v=2):")
lhs = math.log(1 + 1/3)  # ln(1 + 1/(3·1))
odd_part = math.log(1 + 1/6)  # ln(1 + 1/(5·1+1))
even1 = math.log(1 + 1/21)  # ln(1 + 1/(5·4+1))
even2 = math.log(1 + 1/11)  # ln(1 + 1/(5·2+1))
rhs = odd_part + even1 + even2
print(f"  LHS = ln(4/3) = {lhs:.15f}")
print(f"  RHS = ln(7/6) + ln(22/21) + ln(12/11) = {rhs:.15f}")
print(f"  = ln(7·22·12/(6·21·11)) = ln(1848/1386) = ln({Fraction(1848,1386)}) = ln(4/3)")
print(f"  Match: {abs(lhs - rhs) < 1e-14}")
print()
print("  For k=1 it works. But this is FORCED by the rotation framework --")
print("  BOTH sides equal ln(2^S/3^x). For any valid cycle, both sides")
print("  independently equal ln(2^S/3^x), so the identity is trivially satisfied.")
print()
print("  CONCLUSION: The rotation framework identity")
print("    Σ ln(1+1/(3B_i)) = E · ln6")
print("  where E = Σ_i [ε_odd(B_i) + Σ_j ε_even(m_{i,j})]")
print("  is AUTOMATICALLY TRUE for any cycle. No contradiction arises.")
print()

# ==========================================================================
# FINAL SUMMARY
# ==========================================================================

print("=" * 80)
print("FINAL SUMMARY")
print("=" * 80)
print()
print("  THE CLAIM IS FALSE.")
print()
print("  The claimed contradiction 9·2^S/(5·3^x) = 1 is based on an")
print("  ALGEBRAIC ERROR in the even-step error formula.")
print()
print("  SPECIFICALLY:")
print("  1. R181 claims ε_even(m) = log_6(1 + 2/(5m+2))")
print("     CORRECT:    ε_even(m) = log_6(1 + 1/(5m+1))")
print("     The R181 formula overestimates by approximately a factor of 2.")
print()
print("  2. This factor-of-2 error inflates the even-step contribution,")
print("     yielding c = 3/(5·ln6) instead of the correct")
print(f"     c ≈ 2/(5·ln6) (ignoring 2^{{-v}} corrections).")
print()
print("  3. With the correct coefficient, the leading-order analysis gives:")
print("     E ≈ c · Σ(1/B_i) and E = log_6(2^S/3^x)")
print("     with c → 1/(3·ln6) for cycles (matching both constraints),")
print("     so the ratio becomes 1, not 9/5.")
print()
print("  4. More fundamentally, the two constraints")
print("     (rotation return and product return) are BOTH exact consequences")
print("     of the cycle definition. They cannot contradict each other.")
print("     Any apparent contradiction signals an error in the approximation.")
print()
print("  5. The trivial cycle k=1 confirms: E_exact = log_6(4/3) and")
print("     c_true = log_6(4/3) ≈ 0.1606, which equals neither 3/(5·ln6)")
print("     nor 1/(3·ln6) exactly, but approaches 1/(3·ln6) asymptotically")
print("     for large cycles (where the first-order approximation holds).")
print()
print("  VERIFICATION STATUS: The contradiction is INVALID.")
print("  The rotation framework is correct and elegant, but it does not")
print("  yield a proof that non-trivial cycles are impossible.")
print()
