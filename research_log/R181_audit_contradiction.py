#!/usr/bin/env python3
"""R181_audit_contradiction.py — RUTHLESS AUDIT of the claimed 9/5 contradiction.

This script audits each step of the claimed proof that no non-trivial Collatz
cycles exist, via a "9/5 ≈ 1" contradiction derived from the circle rotation
near-conjugacy.

CLAIMED ARGUMENT:
  Step 1: E_cycle = d/(2^S · ln6) from rotation return
  Step 2: E_cycle ≈ c · Σ(1/B_i) with c = 3/(5·ln6)
  Step 3: Σ(1/B_i) ≈ 3d/3^x from cycle product identity
  Step 4: Combining gives 9/5 = 1, contradiction.

THIS AUDIT:
  A. Derives Step 1 from scratch
  B. Checks error formulas at intermediate (even) values
  C. Verifies the product identity
  D. Checks whether error terms can absorb the 9/5 discrepancy
  E. Tests against the trivial cycle k=1
  F. Provides a definitive verdict

Author: Eric Merle (assisted by Claude, RED TEAM mode)
Date:   15 March 2026
"""

import math
from typing import List, Tuple
from fractions import Fraction

# ============================================================================
# Constants
# ============================================================================
LN2 = math.log(2)
LN3 = math.log(3)
LN6 = math.log(6)
ALPHA = LN3 / LN6  # log_6(3) ≈ 0.61315
LOG6_2 = LN2 / LN6

print("=" * 80)
print("R181 — RUTHLESS AUDIT OF THE 9/5 CONTRADICTION CLAIM")
print("=" * 80)
print(f"  alpha = log_6(3) = {ALPHA:.15f}")
print(f"  ln6 = {LN6:.15f}")
print(f"  3/(5*ln6) = {3.0/(5*LN6):.15f}")
print()


# ============================================================================
# UTILITY FUNCTIONS
# ============================================================================

def phi(n):
    """phi(n) = {log_6(n + 1/5)} — fractional part."""
    return math.log(n + 0.2) / LN6 % 1.0

def eps_odd_exact(B):
    """Exact error for odd step B -> 3B+1.
    eps_odd(B) = log_6(1 + 1/(5B+1))
    """
    return math.log1p(1.0 / (5*B + 1)) / LN6

def eps_even_exact(m):
    """Exact error for even step m -> m/2.
    eps_even(m) = log_6(1 + 2/(5m+2))
    where m is even.
    """
    return math.log1p(2.0 / (5*m + 2)) / LN6

def compressed_orbit(B0, max_steps=200):
    """Compressed Collatz orbit: odd -> odd.
    Returns list of (B_i, v_i) pairs.
    """
    orbit = []
    B = B0
    for _ in range(max_steps):
        val = 3*B + 1
        v = 0
        while val % 2 == 0:
            val //= 2
            v += 1
        orbit.append((B, v))
        B = val
        if B == 1:
            break
    return orbit

def exact_cumulative_error_compressed_step(B, v):
    """Compute EXACT cumulative error for one compressed step B -> B'.

    The compressed step is:
      B (odd) -> 3B+1 (even) -> (3B+1)/2 -> ... -> (3B+1)/2^v = B' (odd)

    Elementary steps:
      1 odd step:  B -> 3B+1, error = eps_odd(B) = log_6(1 + 1/(5B+1))
      v even steps: m_j -> m_j/2 for j=1..v
        where m_1 = 3B+1, m_2 = (3B+1)/2, ..., m_v = (3B+1)/2^{v-1}
        error_j = eps_even(m_j) = log_6(1 + 2/(5*m_j + 2))

    Returns: total error for this compressed step, and breakdown.
    """
    e_odd = eps_odd_exact(B)

    e_evens = []
    m = 3*B + 1  # This is even
    for j in range(v):
        e_ev = eps_even_exact(m)
        e_evens.append((m, e_ev))
        m = m // 2

    total = e_odd + sum(e for _, e in e_evens)
    return total, e_odd, e_evens


def exact_cumulative_error_orbit(orbit):
    """Compute EXACT total cumulative error for a compressed orbit.
    Sum over all compressed steps.
    """
    total = 0.0
    details = []
    for B, v in orbit:
        step_total, e_odd, e_evens = exact_cumulative_error_compressed_step(B, v)
        details.append((B, v, step_total, e_odd, e_evens))
        total += step_total
    return total, details


# ============================================================================
# AUDIT A: IS STEP 1 CORRECT?
# ============================================================================

def audit_step1():
    """Verify the rotation return equation E_cycle = d/(2^S * ln6)."""
    print("=" * 80)
    print("AUDIT A: STEP 1 — ROTATION RETURN EQUATION")
    print("=" * 80)
    print()

    print("  DERIVATION FROM SCRATCH:")
    print("  ─" * 40)
    print()
    print("  The near-conjugacy says: phi(C(n)) = phi(n) + alpha + eps(n) mod 1")
    print("  where alpha = log_6(3), and C is the elementary Collatz map.")
    print()
    print("  For a cycle of TOTAL length L (elementary steps):")
    print("    phi(n) + L*alpha + E_total = phi(n) + m  (for some integer m)")
    print("    => L*alpha + E_total = m")
    print("    => E_total = m - L*alpha")
    print()
    print("  Now L = S (total elementary steps = x odd + (S-x) even... ")
    print("  WAIT. Let me be precise.")
    print()
    print("  For a compressed cycle through x odd numbers B_0,...,B_{x-1}:")
    print("    - x odd steps (each B_i -> 3B_i+1)")
    print("    - Total even steps = sum(v_i) = S")
    print("    - Total elementary steps = x + S")
    print()
    print("  Each elementary step advances phi by alpha + eps_step (mod 1).")
    print("  Total rotation for the cycle:")
    print("    (x + S) * alpha + E_total = m  (integer)")
    print()
    print("  WAIT — THIS IS WRONG in the claim!")
    print("  The claim says E_cycle = d/(2^S * ln6), where d = 2^S - 3^x.")
    print("  But the total number of elementary steps is x + S, not S.")
    print()
    print("  Let me re-derive. For the cycle:")
    print("    (x + S)*alpha + E_total = m")
    print("    E_total = m - (x + S)*alpha")
    print("            = m - (x + S)*ln3/ln6")
    print()
    print("  Now what is m? From the cycle, we need 2^S = 3^x * prod(1 + 1/(3B_i)).")
    print("  For a 'pure' cycle (cycle equation): prod((3B_i+1)/2^{v_i}) = 1 (cyclic return)")
    print("  => prod(3B_i+1) = 2^S * prod(B_i)")
    print("  Wait, let me use: since B_{i+1} = (3B_i+1)/2^{v_i}, and it's a cycle,")
    print("  prod(B_{i+1}/B_i) = 1 => prod((3B_i+1)/(B_i * 2^{v_i})) = 1")
    print("  => prod(3B_i+1) / (prod(B_i) * 2^S) = 1")
    print("  => prod(3B_i+1) = 2^S * prod(B_i)")
    print("  => prod(3 + 1/B_i) = 2^S / prod(B_i) * prod(B_i) ... no.")
    print("  Actually: prod(3B_i+1) = prod(B_i) * prod(3 + 1/B_i) = prod(B_i) * 2^S")
    print("  NO: prod(3B_i+1) / prod(B_i) = prod((3B_i+1)/B_i) = prod(3 + 1/B_i).")
    print("  And prod(3B_i+1) = 2^S * prod(B_i).")
    print("  So prod(3 + 1/B_i) = 2^S. CORRECT.")
    print()
    print("  Taking log: sum ln(3 + 1/B_i) = S*ln2")
    print("  => x*ln3 + sum ln(1 + 1/(3B_i)) = S*ln2")
    print("  => sum ln(1 + 1/(3B_i)) = S*ln2 - x*ln3 = ln(2^S/3^x) = ln(1 + d/3^x)")
    print()
    print("  Now, the total rotation (x+S)*alpha = (x+S)*ln3/ln6.")
    print("  For this to be near an integer m:")
    print("    m ≈ (x+S)*ln3/ln6")
    print()
    print("  Let me compute (x+S)*ln3/ln6 using S*ln2 = x*ln3 + ln(1+d/3^x):")
    print("    S = (x*ln3 + ln(1+d/3^x))/ln2")
    print("    x + S = x + x*ln3/ln2 + ln(1+d/3^x)/ln2")
    print("          = x*(1 + ln3/ln2) + ln(1+d/3^x)/ln2")
    print("          = x*ln6/ln2 + ln(1+d/3^x)/ln2")
    print("    (x+S)*ln3/ln6 = x*ln3/ln2 + ln(1+d/3^x)*ln3/(ln2*ln6)")
    print()
    print("  Now x*ln3/ln2 is generally NOT an integer.")
    print("  The fractional part {x*ln3/ln2} = {x*log_2(3)} measures the gap.")
    print()
    print("  Let me try a DIFFERENT approach. The integer m must satisfy:")
    print("    m*ln6 ≈ (x+S)*ln3")
    print("    m*(ln2+ln3) ≈ x*ln3 + S*ln3")
    print("    m*ln2 + m*ln3 ≈ x*ln3 + S*ln3")
    print("    m*ln2 ≈ (x + S - m)*ln3")
    print("  So 2^m ≈ 3^{x+S-m}. Setting r = x+S-m:")
    print("    2^m = 3^r approximately, i.e., m*ln2 ≈ r*ln3.")
    print()
    print("  The EXACT rotation return for the cycle:")
    print("    E_total = m - (x+S)*alpha = m - (x+S)*ln3/ln6")
    print("  Multiply by ln6:")
    print("    E_total * ln6 = m*ln6 - (x+S)*ln3")
    print("                  = m*(ln2+ln3) - (x+S)*ln3")
    print("                  = m*ln2 - (x+S-m)*ln3")
    print("                  = m*ln2 - r*ln3  where r = x+S-m")
    print()
    print("  So E_total = (m*ln2 - r*ln3) / ln6.")
    print()
    print("  For d = 2^S - 3^x, we have S*ln2 = x*ln3 + ln(1+d/3^x).")
    print("  The E_total involves DIFFERENT exponents (m, r) than (S, x).")
    print()
    print("  *** CRITICAL FINDING ***")
    print("  The claim says E_cycle = d/(2^S * ln6).")
    print("  But E_total = (m*ln2 - r*ln3)/ln6 where m, r are the nearest")
    print("  integer approximation from the rotation, NOT directly S and x!")
    print()
    print("  Let me check: IS there a simpler expression?")
    print("  From the cycle product identity: 3^x * prod(1 + 1/(3B_i)) = 2^S")
    print("  => ln(2^S) = ln(3^x) + sum ln(1 + 1/(3B_i))")
    print("  => S*ln2 - x*ln3 = sum ln(1 + 1/(3B_i))")
    print()
    print("  And E_total = m - (x+S)*ln3/ln6. We need to express m.")
    print("  For the phi map: phi(B_0) = log_6(B_0 + 1/5) mod 1.")
    print("  The cycle returns to B_0, so phi returns to the same value mod 1.")
    print("  Hence (x+S)*alpha + E_total ≡ 0 mod 1, i.e., E_total = -fractional part.")
    print()
    print()

    # NUMERICAL TEST: compute E_total for the trivial cycle k=1
    print("  NUMERICAL TEST: Trivial cycle k=1 (1 -> 4 -> 2 -> 1)")
    print("  ─" * 40)
    B_values = [1]
    v_values = [2]  # 3*1+1 = 4 = 2^2, so v=2
    x = 1
    S = 2
    d = 2**S - 3**x  # = 4 - 3 = 1

    # Total elementary steps = x + S = 1 + 2 = 3
    # Steps: 1 (odd) -> 4 (even) -> 2 (even) -> 1
    total_steps = x + S

    # Exact cumulative error
    orbit = [(1, 2)]
    E_exact, details = exact_cumulative_error_orbit(orbit)

    # Rotation return: (x+S)*alpha + E_total = m
    rotation = total_steps * ALPHA + E_exact
    m_nearest = round(rotation)
    E_total_from_rotation = m_nearest - total_steps * ALPHA

    print(f"    x = {x}, S = {S}, d = {d}")
    print(f"    Total elementary steps = {total_steps}")
    print(f"    (x+S)*alpha = {total_steps * ALPHA:.15f}")
    print(f"    E_exact (sum of eps) = {E_exact:.15f}")
    print(f"    Rotation total = {rotation:.15f}")
    print(f"    Nearest integer m = {m_nearest}")
    print(f"    E_total = m - (x+S)*alpha = {E_total_from_rotation:.15f}")
    print(f"    E_exact (from eps sum) = {E_exact:.15f}")
    print(f"    Discrepancy = {abs(E_exact - E_total_from_rotation):.2e}")
    print()

    # Now check the claim: E_cycle = d/(2^S * ln6)
    E_claimed = d / (2**S * LN6)
    print(f"    Claimed E_cycle = d/(2^S * ln6) = {E_claimed:.15f}")
    print(f"    Actual E_exact = {E_exact:.15f}")
    print(f"    Ratio E_exact / E_claimed = {E_exact / E_claimed:.10f}")
    print()

    # Also check: ln(1 + d/3^x) / ln6
    E_log = math.log1p(d / 3**x) / LN6
    print(f"    ln(1 + d/3^x) / ln6 = {E_log:.15f}")
    print(f"    This is NOT the same as d/(2^S * ln6) = {E_claimed:.15f}")
    print(f"    Ratio = {E_log / E_claimed:.10f}")
    print()
    print(f"    NOTE: ln(1+d/3^x) = {math.log1p(d/3**x):.15f}")
    print(f"          d/3^x = {d/3**x:.15f}")
    print(f"          d/2^S = {d/2**S:.15f}")
    print(f"    These differ significantly when d/3^x is not tiny!")
    print()

    # *** THE KEY QUESTION: What is E_total exactly for a cycle? ***
    print("  THE CORRECT DERIVATION OF E_total FOR A CYCLE:")
    print("  ─" * 40)
    print()
    print("  From the product identity: prod(3 + 1/B_i) = 2^S")
    print("  => sum ln(3 + 1/B_i) = S*ln2")
    print("  => x*ln3 + sum ln(1 + 1/(3B_i)) = S*ln2  ... (I)")
    print()
    print("  The cumulative error E_total is the sum of all eps for each")
    print("  elementary step. For one compressed step (B_i, v_i):")
    print("    e_i = eps_odd(B_i) + sum_{j=1}^{v_i} eps_even(m_{i,j})")
    print("  where m_{i,j} = (3B_i+1)/2^{j-1}.")
    print()
    print("  The rotation for the full compressed step:")
    print("    phi(B_{i+1}) - phi(B_i) = (1 + v_i)*alpha + e_i  (mod 1)")
    print("  Wait -- let me reconsider. Each elementary step adds alpha.")
    print("  Compressed step = 1 odd + v_i even = (1 + v_i) elementary steps.")
    print("  So: phi(B_{i+1}) - phi(B_i) = (1 + v_i)*alpha + e_i  (mod 1)")
    print()
    print("  For the full cycle (x compressed steps):")
    print("    sum [phi(B_{i+1}) - phi(B_i)] = 0  (mod 1, since it's a cycle)")
    print("    sum [(1 + v_i)*alpha + e_i] = 0  (mod 1)")
    print("    (x + S)*alpha + E_total = 0  (mod 1)")
    print("  where E_total = sum e_i.")
    print()
    print("  So: E_total = m - (x+S)*alpha for some integer m,")
    print("  i.e., E_total = m - (x+S)*ln3/ln6.")
    print()
    print("  Multiply by ln6: E_total*ln6 = m*ln6 - (x+S)*ln3")
    print("                              = m*ln2 + m*ln3 - x*ln3 - S*ln3")
    print("                              = m*ln2 - (x+S-m)*ln3")
    print()
    print("  From (I): S*ln2 = x*ln3 + sum ln(1 + 1/(3B_i))")
    print("  This does NOT directly give us E_total*ln6 = m*ln2 - r*ln3.")
    print()
    print("  The claim 'E_cycle = d/(2^S*ln6)' CANNOT be correct in general.")
    print("  d/(2^S*ln6) ~ d/(3^x*ln6) for large x, while the actual E_total")
    print("  depends on which integer m the rotation lands near.")
    print()

    # Let me compute what E_total SHOULD be from the cycle equation
    print("  ALTERNATIVE: Express E_total via the cumulative errors directly.")
    print("  E_total = sum_i [eps_odd(B_i) + sum_j eps_even(m_{i,j})]")
    print()
    print("  For the trivial cycle B_0=1, v_0=2:")
    for B, v, step_total, e_odd, e_evens in details:
        print(f"    B={B}, v={v}")
        print(f"    eps_odd({B}) = {e_odd:.15f}")
        for m_val, e_ev in e_evens:
            print(f"    eps_even({m_val}) = {e_ev:.15f}")
        print(f"    Step total = {step_total:.15f}")
    print(f"    E_total = {E_exact:.15f}")
    print()

    return E_exact, E_claimed


# ============================================================================
# AUDIT B: IS STEP 2 CORRECT?
# ============================================================================

def audit_step2():
    """Check E_cycle ≈ c * sum(1/B_i) with c = 3/(5*ln6)."""
    print("=" * 80)
    print("AUDIT B: STEP 2 — ERROR APPROXIMATION E ≈ c*Σ(1/B_i)")
    print("=" * 80)
    print()

    c = 3.0 / (5 * LN6)
    print(f"  Claimed: E_cycle ≈ c * Σ(1/B_i) with c = 3/(5*ln6) = {c:.15f}")
    print()

    print("  DERIVATION CHECK:")
    print("  For each compressed step, the error is:")
    print("    e_i = eps_odd(B_i) + sum_{j=1}^{v_i} eps_even(m_{i,j})")
    print()
    print("    eps_odd(B_i) = log_6(1 + 1/(5B_i+1)) ≈ 1/((5B_i+1)*ln6) ≈ 1/(5B_i*ln6)")
    print()
    print("    eps_even(m_{i,j}) = log_6(1 + 2/(5m_{i,j}+2))")
    print("    where m_{i,j} = (3B_i+1)/2^{j-1}")
    print()
    print("  The even errors involve the INTERMEDIATE values, not B_i!")
    print("  m_{i,1} = 3B_i+1 ≈ 3B_i")
    print("  m_{i,2} = (3B_i+1)/2 ≈ 3B_i/2")
    print("  ...")
    print("  m_{i,v_i} = (3B_i+1)/2^{v_i-1} ≈ 3B_i/2^{v_i-1}")
    print()
    print("  So eps_even(m_{i,j}) ≈ 2/(5*m_{i,j}*ln6) = 2/(5*(3B_i+1)/2^{j-1}*ln6)")
    print("                       ≈ 2^j / (5*3B_i*ln6)")
    print()
    print("  Sum over j=1..v_i:")
    print("    sum eps_even ≈ (2 + 4 + ... + 2^{v_i}) / (15*B_i*ln6)")
    print("                 = (2^{v_i+1} - 2) / (15*B_i*ln6)")
    print()
    print("  Total for step i:")
    print("    e_i ≈ 1/(5B_i*ln6) + (2^{v_i+1} - 2)/(15*B_i*ln6)")
    print("        = [3 + (2^{v_i+1} - 2)] / (15*B_i*ln6)")
    print("        = (2^{v_i+1} + 1) / (15*B_i*ln6)")
    print()
    print("  *** THIS IS NOT c/B_i = 3/(5*B_i*ln6) = 9/(15*B_i*ln6)! ***")
    print("  It's (2^{v_i+1}+1)/(15*B_i*ln6), which depends on v_i.")
    print()
    print("  For the 'average' v_i ≈ S/x ≈ log_2(3) ≈ 1.585:")
    print(f"    2^(v_avg+1) + 1 ≈ 2^{1 + LN3/LN2:.3f} + 1 ≈ {2**(1+LN3/LN2) + 1:.4f}")
    print(f"    Expected coefficient per 1/B_i: {(2**(1+LN3/LN2)+1)/15:.6f} / ln6")
    print(f"    Claimed coefficient: 9/15 = {9/15:.6f} / ln6")
    print(f"    Ratio: {(2**(1+LN3/LN2)+1)/9:.6f}")
    print()
    print("  BUT WAIT: v_i is NOT a constant. It varies. And 2^{v_i} is convex,")
    print("  so E[2^{v_i}] > 2^{E[v_i]}. The correct sum is:")
    print("    E_total ≈ (1/15*ln6) * sum_i (2^{v_i+1}+1)/B_i")
    print("  This is NOT simply proportional to sum(1/B_i) unless all v_i are equal.")
    print()

    # NUMERICAL VERIFICATION
    print("  NUMERICAL VERIFICATION on pseudo-cycles:")
    print("  ─" * 40)

    # Test on long trajectory segments
    test_starts = [3, 7, 27, 97, 871, 6171, 77031]

    for B0 in test_starts:
        orbit = compressed_orbit(B0, max_steps=50)
        if len(orbit) < 5:
            continue

        # Take first 10 compressed steps
        sub = orbit[:min(10, len(orbit))]
        E_exact, details = exact_cumulative_error_orbit(sub)

        # Compute the claimed approximation
        sum_inv_B = sum(1.0/B for B, v in sub)
        E_approx_claimed = c * sum_inv_B

        # Compute the CORRECT approximation
        sum_weighted = sum((2**(v+1) + 1) / (15.0 * B * LN6) for B, v in sub)

        # Also compute the exact breakdown
        x_local = len(sub)
        S_local = sum(v for _, v in sub)

        ratio_claimed = E_exact / E_approx_claimed if abs(E_approx_claimed) > 1e-20 else float('inf')
        ratio_correct = E_exact / sum_weighted if abs(sum_weighted) > 1e-20 else float('inf')

        print(f"  B0={B0:>6d}, x={x_local}, S={S_local}")
        print(f"    E_exact    = {E_exact:.10f}")
        print(f"    E_claimed  = c*Σ(1/B) = {E_approx_claimed:.10f}  (ratio: {ratio_claimed:.6f})")
        print(f"    E_correct  = Sigma(2^(v+1)+1)/(15B*ln6) = {sum_weighted:.10f}  (ratio: {ratio_correct:.6f})")
        print()

    print("  *** VERDICT ON STEP 2 ***")
    print("  The coefficient c = 3/(5*ln6) is WRONG. The correct error depends on")
    print("  the individual v_i values, not just on Σ(1/B_i).")
    print("  The correct leading-order expression is:")
    print("    E ≈ Σ_i (2^{v_i+1}+1) / (15*B_i*ln6)")
    print("  which equals (sum of 2^{v_i+1}+1 weighted by 1/B_i) / (15*ln6).")
    print()
    return


# ============================================================================
# AUDIT C: IS STEP 3 CORRECT?
# ============================================================================

def audit_step3():
    """Verify the product identity and Σ(1/B_i) ≈ 3d/3^x."""
    print("=" * 80)
    print("AUDIT C: STEP 3 — PRODUCT IDENTITY AND Σ(1/B_i)")
    print("=" * 80)
    print()

    print("  The product identity for a cycle:")
    print("  prod(3 + 1/B_i) = 2^S  =>  sum ln(1 + 1/(3B_i)) = S*ln2 - x*ln3 = ln(1+d/3^x)")
    print()
    print("  Expanding: ln(1 + 1/(3B_i)) ≈ 1/(3B_i) - 1/(18B_i^2) + ...")
    print("  So: Σ 1/(3B_i) ≈ ln(1 + d/3^x) ≈ d/3^x - d^2/(2*9^x) + ...")
    print("  Hence: Σ 1/B_i ≈ 3d/3^x - 3d^2/(2*9^x) + 3*Σ 1/(18B_i^2) + ...")
    print()
    print("  THIS STEP IS CORRECT to leading order in d/3^x.")
    print("  The error is O(Σ 1/B_i^2) + O(d^2/9^x).")
    print()

    # Verify for trivial cycle
    print("  Verification for trivial cycle k=1:")
    B_vals = [1]
    S, x = 2, 1
    d = 2**S - 3**x  # = 1

    sum_inv_B = sum(1.0/B for B in B_vals)
    sum_ln = sum(math.log(1 + 1.0/(3*B)) for B in B_vals)
    rhs = math.log(1 + d / 3.0**x)

    print(f"    Σ 1/(3B_i) = {sum(1.0/(3*B) for B in B_vals):.10f}")
    print(f"    d/3^x = {d/3.0**x:.10f}")
    print(f"    Σ ln(1+1/(3B_i)) = {sum_ln:.10f}")
    print(f"    ln(1+d/3^x) = {rhs:.10f}")
    print(f"    Match: {abs(sum_ln - rhs) < 1e-10}")
    print()
    print(f"    Σ 1/B_i = {sum_inv_B:.10f}")
    print(f"    3d/3^x = {3*d/3.0**x:.10f}")
    print(f"    Ratio = {sum_inv_B / (3*d/3.0**x):.10f}")
    print(f"    NOTE: For k=1, d/3^x = 1/3 is NOT small, so the")
    print(f"    approximation ln(1+u) ≈ u is poor (u = 0.333).")
    print(f"    ln(1+0.333) = {math.log(4/3):.6f} vs 0.333, ratio = {math.log(4/3)/0.333:.6f}")
    print()

    print("  For large cycles, d/3^x is exponentially small (for convergents).")
    print("  So Step 3 is CORRECT for large cycles. It fails for k=1 because")
    print("  d/3^x = 1/3 is not small.")
    print()

    # How small is d/3^x for convergents?
    print("  d/3^x for convergents of log_2(3):")
    convergents = [(2,1), (5,3), (8,5), (19,12), (27,17), (46,29), (65,41), (84,53)]
    for S_val, x_val in convergents:
        d_val = 2**S_val - 3**x_val
        ratio = d_val / 3.0**x_val
        print(f"    (S={S_val:>3d}, x={x_val:>3d}): d={d_val:>12d}, d/3^x={ratio:.6e}")
    print()
    return


# ============================================================================
# AUDIT D: COMBINATION AND 9/5 DISCREPANCY
# ============================================================================

def audit_step4():
    """Check whether combining the approximations correctly gives 9/5 or not."""
    print("=" * 80)
    print("AUDIT D: STEP 4 — THE 9/5 COMBINATION")
    print("=" * 80)
    print()

    print("  The claim combines:")
    print("    (i)   E_cycle = d/(2^S * ln6)          [from Step 1]")
    print("    (ii)  E_cycle ≈ c * Σ(1/B_i)           [from Step 2]")
    print("    (iii) Σ(1/B_i) ≈ 3d/3^x                [from Step 3]")
    print()
    print("  => d/(2^S*ln6) ≈ (3/(5*ln6)) * 3d/3^x = 9d/(5*3^x*ln6)")
    print("  => 1/2^S ≈ 9/(5*3^x)")
    print("  => 5*3^x ≈ 9*2^S")
    print("  => 5 ≈ 9 * 2^S/3^x")
    print("  Since 2^S/3^x = 1 + d/3^x ≈ 1:")
    print("  => 5 ≈ 9. CONTRADICTION.")
    print()
    print("  BUT — MULTIPLE ERRORS IN THIS CHAIN:")
    print()

    print("  ERROR 1: Step 1 is WRONG.")
    print("  The actual E_total = m - (x+S)*alpha, not d/(2^S*ln6).")
    print("  The 'derivation' of d/(2^S*ln6) conflates the rotation integer m")
    print("  with the Diophantine quantity 2^S - 3^x.")
    print()
    print("  Let me check: what IS m - (x+S)*alpha?")
    print("  We need: (x+S)*alpha = (x+S)*ln3/ln6.")
    print("  From S*ln2 = x*ln3 + ln(1+d/3^x):")
    print("    S = x*ln3/ln2 + ln(1+d/3^x)/ln2")
    print("    x + S = x(1 + ln3/ln2) + ln(1+d/3^x)/ln2")
    print("          = x*ln6/ln2 + ln(1+d/3^x)/ln2")
    print("    (x+S)*ln3/ln6 = x*ln3/ln2 + ln(1+d/3^x)*ln3/(ln2*ln6)")
    print()
    print("  Now x*ln3/ln2 = x*log_2(3). For the nearest integer m:")
    print("    m = round(x*ln6/ln2 * ln3/ln6 + ...) = round(x*ln3/ln2 + ...)")
    print()
    print("  The key: x*ln3/ln2 is NOT near an integer in general.")
    print("  {x*log_2(3)} can be any value in [0,1).")
    print()
    print("  For convergents of log_2(3), {x*log_2(3)} IS small:")
    print("  |x*log_2(3) - S| ≈ d/(3^x * ln2) (for large x).")
    print()
    print("  So for convergents:")
    print("    (x+S)*alpha = (x*ln6/ln2)*alpha + (d/(3^x*ln2))*(...)...")
    print("  This is getting circular. Let me just compute numerically.")
    print()

    print("  NUMERICAL TEST: Compute all quantities for convergents")
    print("  ─" * 40)
    print()

    convergents = [(2,1), (5,3), (8,5), (19,12), (27,17), (46,29), (65,41)]

    for S_val, x_val in convergents:
        d_val = 2**S_val - 3**x_val

        # Total elementary steps
        L = x_val + S_val

        # Rotation: L * alpha
        L_alpha = L * ALPHA
        m = round(L_alpha)
        E_rotation = m - L_alpha  # This is what E_total must equal for a cycle

        # Claimed E = d/(2^S * ln6)
        E_claimed = d_val / (2**S_val * LN6)

        # ln(1+d/3^x) / ln6 — another candidate
        if d_val > 0:
            E_log = math.log1p(d_val / 3.0**x_val) / LN6
        else:
            E_log = math.log(1 + d_val / 3.0**x_val) / LN6

        # The "correct" E_total from Step 2+3 (using the CORRECT formula)
        # E ≈ Σ_i (2^{v_i+1}+1)/(15*B_i*ln6)
        # For a hypothetical cycle with x equal B_i = k, v_i = S/x:
        # E ≈ x*(2^{S/x+1}+1)/(15*k*ln6)
        # Since the cycle has x elements all equal to k (uniform approximation):
        # Σ(1/B_i) = x/k
        # And from Step 3: x/k ≈ 3d/3^x, so k ≈ x*3^x/(3d)

        print(f"  (S={S_val}, x={x_val}): d={d_val}")
        print(f"    L=x+S = {L}")
        print(f"    L*alpha = {L_alpha:.10f}, m={m}")
        print(f"    E_rotation = m - L*alpha = {E_rotation:.10f}")
        print(f"    E_claimed  = d/(2^S*ln6) = {E_claimed:.10f}")
        print(f"    ln(1+d/3^x)/ln6 = {E_log:.10f}")
        print(f"    Ratio E_rotation/E_claimed = {E_rotation/E_claimed if abs(E_claimed) > 1e-20 else 'N/A'}")
        print(f"    Ratio E_rotation/E_log = {E_rotation/E_log if abs(E_log) > 1e-20 else 'N/A'}")
        print()

    print()
    print("  ERROR 2: Step 2 coefficient c = 3/(5*ln6) is WRONG.")
    print("  The correct coefficient depends on v_i (see Audit B).")
    print("  The actual leading-order error for each compressed step is")
    print("  (2^{v_i+1}+1)/(15*B_i*ln6), not 3/(5*B_i*ln6) = 9/(15*B_i*ln6).")
    print()
    print("  For v_i = 1 (the most common case): (2^2+1)/15 = 5/15 = 1/3")
    print("  For v_i = 2: (2^3+1)/15 = 9/15 = 3/5")
    print("  For v_i = 3: (2^4+1)/15 = 17/15")
    print("  The claim uses 9/15 which corresponds to v_i=2, but the 'average'")
    print("  v_i ≈ log_2(3) ≈ 1.585 does NOT give 9/15.")
    print()

    print("  ERROR 3: Even if Steps 1 and 2 were correct, the combination")
    print("  of TWO approximations (each with O(1/k) errors) and comparing")
    print("  them at leading order is INVALID when the main terms are also O(1/k).")
    print()
    print("  Specifically:")
    print("    E_total ≈ A + O(1/k^2)  where A = O(d/3^x) = O(1/k)")
    print("    E_total ≈ B + O(1/k^2)  where B = O(d/3^x) = O(1/k)")
    print("  Then A/B = 9/5 + O(error/k). But error/k could be O(1),")
    print("  making the ratio meaningless!")
    print()
    print("  Actually: d/3^x = O(1/k) (since k ≈ g(v)/d and g(v) < 3^x).")
    print("  The correction terms in Step 3 are O(d^2/9^x) = O(1/k^2 * 3^x)...")
    print("  Wait, this needs more care.")
    print()

    return


# ============================================================================
# AUDIT E: TRIVIAL CYCLE k=1
# ============================================================================

def audit_trivial_cycle():
    """The claimed argument must FAIL for k=1 since the trivial cycle exists."""
    print("=" * 80)
    print("AUDIT E: TRIVIAL CYCLE k=1")
    print("=" * 80)
    print()

    print("  The trivial cycle: 1 -> 4 -> 2 -> 1")
    print("  x = 1 (one odd number: B_0 = 1)")
    print("  v_0 = 2 (since 3*1+1 = 4 = 2^2)")
    print("  S = v_0 = 2")
    print("  d = 2^2 - 3^1 = 1")
    print()

    # Step 1: E_total for the trivial cycle
    orbit = [(1, 2)]
    E_exact, details = exact_cumulative_error_orbit(orbit)

    L = 3  # x + S = 1 + 2
    m = round(L * ALPHA)
    E_rotation = m - L * ALPHA

    print(f"  EXACT E_total = {E_exact:.15f}")
    print(f"  Rotation check: L*alpha = {L*ALPHA:.15f}, m = {m}")
    print(f"  E_from_rotation = {E_rotation:.15f}")
    print(f"  Match: {abs(E_exact - E_rotation) < 1e-10}")
    print()

    # Step 2: Does E ≈ c * Σ(1/B_i) work?
    c = 3.0 / (5 * LN6)
    sum_inv_B = 1.0  # 1/B_0 = 1/1
    E_step2 = c * sum_inv_B
    print(f"  Step 2 (claimed): E ≈ c/B_0 = {c:.10f} * 1 = {E_step2:.10f}")
    print(f"  Actual E_exact = {E_exact:.10f}")
    print(f"  Ratio: {E_exact / E_step2:.10f}")
    print()

    # Correct Step 2:
    B, v = 1, 2
    E_correct_coeff = (2**(v+1) + 1) / (15.0 * LN6)
    print(f"  Step 2 (corrected): (2^(v+1)+1)/(15*B*ln6) = {E_correct_coeff:.10f}")
    print(f"  Actual E_exact = {E_exact:.10f}")
    print(f"  Ratio: {E_exact / E_correct_coeff:.10f}")
    print(f"  (Still not exact because of higher-order terms in the Taylor expansion)")
    print()

    # Step 3: Σ(1/B_i) vs 3d/3^x
    sum_inv = 1.0
    approx = 3 * 1 / 3.0  # 3d/3^x = 3*1/3 = 1
    print(f"  Step 3: Σ(1/B_i) = {sum_inv:.10f}")
    print(f"          3d/3^x = {approx:.10f}")
    print(f"          Match: YES (exactly in this case)")
    print()

    # Step 4: The 9/5 ratio
    E_step1 = 1.0 / (4 * LN6)  # d/(2^S*ln6) = 1/(4*ln6)
    E_step23 = 9.0 / (5 * 3 * LN6)  # 9d/(5*3^x*ln6) = 9/(5*3*ln6)
    print(f"  Step 1 claimed: d/(2^S*ln6) = {E_step1:.10f}")
    print(f"  Step 2+3 combined: 9d/(5*3^x*ln6) = {E_step23:.10f}")
    print(f"  Ratio: {E_step1 / E_step23:.10f}  (should be 9/5 = 1.8 per the claim)")
    print(f"  Actual ratio: {E_step1 / E_step23:.10f}")
    print()
    print(f"  But the ACTUAL E_exact = {E_exact:.10f}")
    print(f"  Neither {E_step1:.10f} nor {E_step23:.10f} equals the actual error!")
    print()

    print("  CRITICAL: For k=1, the actual E_exact = {:.10f}".format(E_exact))
    print(f"  This is the sum of:")
    print(f"    eps_odd(1) = log_6(1 + 1/6) = {math.log1p(1/6)/LN6:.10f}")
    print(f"    eps_even(4) = log_6(1 + 2/22) = {math.log1p(2/22)/LN6:.10f}")
    print(f"    eps_even(2) = log_6(1 + 2/12) = {math.log1p(2/12)/LN6:.10f}")
    print()

    print("  The argument claims to get a contradiction for ALL k >= 3.")
    print("  But the derivation is equally 'valid' for k=1.")
    print("  The fact that no contradiction arises for k=1 (cycle EXISTS)")
    print("  means the argument must have a flaw.")
    print()
    print("  The flaw is: the approximations in Steps 1 and 2 have errors")
    print("  that are comparable to the main terms for small k.")
    print("  For k >= 3, the errors might be smaller, but Step 2's coefficient")
    print("  is WRONG regardless of k.")
    print()

    return


# ============================================================================
# AUDIT F: QUANTITATIVE ERROR ANALYSIS
# ============================================================================

def audit_error_magnitudes():
    """Determine if the 9/5 discrepancy survives when all corrections are included."""
    print("=" * 80)
    print("AUDIT F: QUANTITATIVE ERROR ANALYSIS")
    print("=" * 80)
    print()

    print("  We need to check: for a hypothetical cycle with large k, do the")
    print("  correction terms potentially absorb the factor 9/5?")
    print()

    print("  Consider a hypothetical cycle with x odd numbers, all ≈ k,")
    print("  with v_i ≈ S/x ≈ log_2(3) ≈ 1.585.")
    print()

    # The correct E_total (leading order, with v_i dependence)
    # E ≈ Σ_i (2^{v_i+1}+1) / (15*B_i*ln6)
    # If all B_i ≈ k and all v_i = v:
    # E ≈ x*(2^{v+1}+1) / (15*k*ln6)

    # From Step 3: x/k ≈ 3d/3^x (assuming d/3^x small)
    # So E ≈ 3d*(2^{v+1}+1) / (3^x * 15 * ln6)
    #       = d*(2^{v+1}+1) / (5 * 3^x * ln6)

    # The "Step 1" E_rotation = m - (x+S)*alpha.
    # We showed this is NOT simply d/(2^S*ln6).
    # Let's figure out what it actually is.

    # (x+S)*alpha = (x+S)*ln3/ln6
    # From S*ln2 = x*ln3 + ln(1+d/3^x):
    #   x + S = x + (x*ln3 + ln(1+d/3^x))/ln2
    #         = x*(1 + ln3/ln2) + ln(1+d/3^x)/ln2
    #         = x*ln6/ln2 + ln(1+d/3^x)/ln2
    #   (x+S)*ln3/ln6 = x*ln3/ln2 + ln(1+d/3^x)*ln3/(ln2*ln6)

    # Now: S*ln2 - x*ln3 = ln(1+d/3^x) ≈ d/3^x
    # So: x*ln3/ln2 ≈ S - d/(3^x*ln2)
    # And: x*ln3/ln2 is near integer iff S is near x*log_2(3)

    # Let p = round(x*ln3/ln2) = round(x*log_2(3))
    # Then: x*ln3/ln2 = p + {x*log_2(3)} where {.} is distance to nearest int

    # For convergents: |{x*log_2(3)} - (S - x*log_2(3))| depends...
    # Actually for convergent (S,x): S = round(x*log_2(3)), so:
    # x*log_2(3) = S - delta where delta = S - x*log_2(3) = (S*ln2 - x*ln3)/ln2
    #            = ln(1+d/3^x)/ln2 ≈ d/(3^x*ln2)

    # So: (x+S)*alpha = (S - d/(3^x*ln2) + d/(3^x*ln2)/...
    # Let me just compute this cleanly:
    # (x+S)*alpha = x*ln3/ln2 * ln3/ln6 + ln(1+d/3^x)*ln3/(ln2*ln6)
    # Hmm no: (x+S)*ln3/ln6 = (x*ln6/ln2 + ln(1+d/3^x)/ln2) * ln3/ln6
    #                        = x*ln3/ln2 + ln(1+d/3^x)*ln3/(ln2*ln6)

    # x*ln3/ln2 = S - ln(1+d/3^x)/ln2
    # So: (x+S)*alpha = S - ln(1+d/3^x)/ln2 + ln(1+d/3^x)*ln3/(ln2*ln6)
    #                 = S + ln(1+d/3^x)/ln2 * (ln3/ln6 - 1)
    #                 = S + ln(1+d/3^x)/ln2 * (ln3 - ln6)/ln6
    #                 = S + ln(1+d/3^x)/ln2 * (-ln2/ln6)
    #                 = S - ln(1+d/3^x)/ln6

    # So: (x+S)*alpha = S - ln(1+d/3^x)/ln6
    # And: E_total = m - (x+S)*alpha = m - S + ln(1+d/3^x)/ln6

    # For the cycle, m must be an integer. And S is already an integer.
    # So m - S is an integer. Let's call it p: E_total = p + ln(1+d/3^x)/ln6.
    # For E_total to be the actual cumulative error (which is O(1/k)):
    # p + ln(1+d/3^x)/ln6 = E_total ≈ small
    # => p ≈ -ln(1+d/3^x)/ln6 ≈ -d/(3^x*ln6)
    # Since p is an integer and d/(3^x*ln6) is small, p = 0.
    # => E_total = ln(1+d/3^x)/ln6 ≈ d/(3^x*ln6)

    print("  KEY DERIVATION:")
    print("  (x+S)*alpha = S - ln(1+d/3^x)/ln6")
    print("  [Derived by substituting S = (x*ln3 + ln(1+d/3^x))/ln2]")
    print()
    print("  So: E_total = m - S + ln(1+d/3^x)/ln6")
    print("  Since m-S is integer and E_total is small, m = S.")
    print("  Therefore: E_total = ln(1+d/3^x)/ln6 ≈ d/(3^x * ln6)")
    print()
    print("  *** THIS IS d/(3^x * ln6), NOT d/(2^S * ln6) as claimed! ***")
    print()
    print("  Since 2^S = 3^x + d, we have 2^S > 3^x, so:")
    print("  d/(2^S * ln6) < d/(3^x * ln6)")
    print("  The ratio is d/2^S vs d/3^x, i.e., 3^x/2^S = 1/(1+d/3^x) < 1.")
    print("  For convergents, d/3^x is small, so the ratio ≈ 1 - d/3^x ≈ 1.")
    print()

    # NUMERICAL VERIFICATION
    print("  NUMERICAL VERIFICATION:")
    convergents = [(2,1), (5,3), (8,5), (19,12), (27,17), (46,29), (65,41), (84,53)]

    print(f"  {'S':>4s}  {'x':>3s}  {'d':>12s}  {'(x+S)*alpha':>14s}  "
          f"{'S - ln(.)/ln6':>14s}  {'match?':>8s}  {'ln(1+d/3^x)/ln6':>16s}  {'d/(3^x*ln6)':>14s}  {'d/(2^S*ln6)':>14s}")

    for S_val, x_val in convergents:
        d_val = 2**S_val - 3**x_val
        L = x_val + S_val
        L_alpha = L * ALPHA

        rhs = S_val - math.log1p(d_val / 3.0**x_val) / LN6
        match = abs(L_alpha - rhs) < 1e-10

        E_correct = math.log1p(d_val / 3.0**x_val) / LN6
        E_approx = d_val / (3.0**x_val * LN6)
        E_claimed = d_val / (2.0**S_val * LN6)

        print(f"  {S_val:>4d}  {x_val:>3d}  {d_val:>12d}  {L_alpha:>14.10f}  "
              f"{rhs:>14.10f}  {'YES' if match else 'NO':>8s}  {E_correct:>16.10f}  {E_approx:>14.10f}  {E_claimed:>14.10f}")

    print()
    print("  CONFIRMED: (x+S)*alpha = S - ln(1+d/3^x)/ln6 holds to machine precision.")
    print("  E_total = ln(1+d/3^x)/ln6, NOT d/(2^S*ln6).")
    print()

    # Now redo the "contradiction" with the CORRECT Step 1
    print("  REDO THE COMBINATION WITH CORRECT STEP 1:")
    print("  ─" * 40)
    print()
    print("  Correct Step 1: E_total = ln(1+d/3^x)/ln6")
    print("  For small d/3^x: E_total ≈ d/(3^x * ln6)")
    print()
    print("  Correct Step 2: E_total ≈ Σ_i (2^{v_i+1}+1)/(15*B_i*ln6)")
    print("  For uniform cycle (all B_i ≈ k, all v_i ≈ v):")
    print("    E_total ≈ x*(2^{v+1}+1)/(15*k*ln6)")
    print()
    print("  Step 3 (correct): Σ(1/B_i) ≈ 3d/3^x")
    print("  So x/k ≈ 3d/3^x, meaning x*(1/k) ≈ 3d/3^x.")
    print()
    print("  Combining corrected Steps 2 and 3:")
    print("    E_total ≈ (2^{v+1}+1)/15 * (3d/3^x) / ln6")
    print("            = (2^{v+1}+1) * d / (5 * 3^x * ln6)")
    print()
    print("  Equating with correct Step 1:")
    print("    d/(3^x*ln6) ≈ (2^{v+1}+1)*d/(5*3^x*ln6)")
    print("  Cancel d/(3^x*ln6):")
    print("    1 ≈ (2^{v+1}+1)/5")
    print("    5 ≈ 2^{v+1}+1")
    print("    2^{v+1} ≈ 4")
    print("    v ≈ 1")
    print()
    print("  But v = S/x ≈ log_2(3) ≈ 1.585, so 2^{v+1} ≈ 2^2.585 ≈ 6.0.")
    print(f"  2^{{v+1}} + 1 ≈ {2**(1+LN3/LN2)+1:.4f}")
    print(f"  (2^{{v+1}}+1)/5 ≈ {(2**(1+LN3/LN2)+1)/5:.4f}")
    print()
    print("  So the ratio is ≈ 1.40, not 1. Still a discrepancy!")
    print()
    print("  BUT WAIT: the 'v' in the approximation is wrong because")
    print("  we used v_i = S/x as if it were an integer. Let's be more careful.")
    print()

    # The correct analysis for v_i variable
    print("  CORRECT ANALYSIS WITH VARIABLE v_i:")
    print("  The exact sum is:")
    print("    Σ_i (2^{v_i+1}+1)/(15*B_i) = (1/15)*[Σ_i (2^{v_i+1})/B_i + Σ_i 1/B_i]")
    print()
    print("  Now: B_{i+1} = (3B_i+1)/2^{v_i}, so 2^{v_i} = (3B_i+1)/B_{i+1}")
    print("    2^{v_i+1} = 2*(3B_i+1)/B_{i+1}")
    print()
    print("  So: Σ (2^{v_i+1})/B_i = 2*Σ (3B_i+1)/(B_i*B_{i+1})")
    print("                        = 2*Σ (3 + 1/B_i)/B_{i+1}")
    print("                        = 6*Σ 1/B_{i+1} + 2*Σ 1/(B_i*B_{i+1})")
    print()
    print("  For a cycle: Σ 1/B_{i+1} = Σ 1/B_i (just shifted index)")
    print("  So: Σ (2^{v_i+1})/B_i = 6*Σ 1/B_i + 2*Σ 1/(B_i*B_{i+1})")
    print()
    print("  Therefore:")
    print("    E_total ≈ [6*Σ(1/B_i) + 2*Σ(1/(B_i*B_{i+1})) + Σ(1/B_i)] / (15*ln6)")
    print("            = [7*Σ(1/B_i) + 2*Σ(1/(B_i*B_{i+1}))] / (15*ln6)")
    print()
    print("  Using Σ(1/B_i) ≈ 3d/3^x and Σ(1/(B_i*B_{i+1})) = O(1/k^2):")
    print("    E_total ≈ 7*3d/(3^x*15*ln6) + O(1/k^2)")
    print("            = 7d/(5*3^x*ln6) + O(1/k^2)")
    print()
    print("  Equating with E_total = d/(3^x*ln6):")
    print("    d/(3^x*ln6) = 7d/(5*3^x*ln6) + O(1/k^2)")
    print("    1 = 7/5 + O(k/d^2·3^x·...)")
    print()
    print("  7/5 = 1.4. Still NOT 1. Discrepancy of 2/5.")
    print()
    print("  *** WHERE IS THE MISSING FACTOR? ***")
    print()
    print("  The issue: our leading-order approximation for eps_even(m) = 2/(5m*ln6)")
    print("  is only the first term. The EXACT formula is")
    print("    eps_even(m) = log_6(1 + 2/(5m+2))")
    print("  and the correction from log(1+u) ≈ u - u^2/2 + ... contributes")
    print("  at the NEXT order. For the sum of geometric series in the even errors,")
    print("  the leading-order approximation overestimates systematically.")
    print()
    print("  But more fundamentally: the discrepancy 7/5 ≠ 1 or 9/5 ≠ 1 means")
    print("  the two expressions for E_total (from rotation vs from error sum)")
    print("  give DIFFERENT leading-order terms. This is not a contradiction!")
    print("  It means the leading-order approximations are INCONSISTENT,")
    print("  i.e., we are comparing two WRONG approximations to the same quantity.")
    print()

    return


# ============================================================================
# AUDIT G: DEFINITIVE RESOLUTION
# ============================================================================

def audit_definitive():
    """Resolve the apparent contradiction definitively."""
    print("=" * 80)
    print("AUDIT G: DEFINITIVE RESOLUTION")
    print("=" * 80)
    print()

    print("  THE RESOLUTION: The two expressions are approximations to")
    print("  the SAME quantity E_total, but at different orders of accuracy.")
    print()
    print("  Expression 1 (from rotation):  E_total = ln(1+d/3^x)/ln6  [EXACT for cycles]")
    print("  Expression 2 (from error sum): E_total = Σ_i e_i            [EXACT by definition]")
    print()
    print("  When we approximate Expression 2 in terms of 1/B_i, we lose")
    print("  information because the error terms eps_odd and eps_even have")
    print("  sub-leading contributions that are NOT captured by the 1/B_i")
    print("  approximation.")
    print()
    print("  The claimed 'contradiction' arises from:")
    print("  1. WRONG formula for E_total from rotation (d/(2^S*ln6) vs d/(3^x*ln6))")
    print("  2. WRONG coefficient in the error sum (ignoring v_i dependence)")
    print("  3. Equating two DIFFERENT approximations as if both were exact")
    print()

    print("  PROOF THAT NO CONTRADICTION EXISTS:")
    print("  ─" * 40)
    print()
    print("  For the trivial cycle k=1:")

    # Exact computation for k=1
    orbit = [(1, 2)]
    E_exact, _ = exact_cumulative_error_orbit(orbit)
    E_from_rotation = math.log1p(1/3.0) / LN6  # ln(1 + d/3^x)/ln6 with d=1,x=1

    print(f"    E_exact (eps sum) = {E_exact:.15f}")
    print(f"    E_from_rotation   = {E_from_rotation:.15f}")
    print(f"    Match: {abs(E_exact - E_from_rotation) < 1e-10}")
    print()
    print("  Both expressions give the SAME answer for the actual cycle.")
    print("  The discrepancy only appears when we APPROXIMATE both sides")
    print("  and compare the approximate forms.")
    print()

    # Now verify numerically for the k=1 cycle that all pieces are consistent
    print("  DETAILED CONSISTENCY CHECK for k=1:")
    print()

    B, v = 1, 2
    x, S = 1, 2
    d = 1

    # Exact error breakdown
    e_odd = eps_odd_exact(1)  # B=1: log_6(1+1/6)
    m1 = 4  # 3*1+1
    e_even1 = eps_even_exact(4)  # m=4: log_6(1+2/22)
    m2 = 2  # 4/2
    e_even2 = eps_even_exact(2)  # m=2: log_6(1+2/12)

    E_sum = e_odd + e_even1 + e_even2

    # From product identity
    prod_check = (3*1+1)  # = 4
    # prod(3 + 1/B_i) = 3 + 1 = 4 = 2^2 = 2^S. CHECK.

    # sum ln(1+1/(3B_i)) = ln(1+1/3) = ln(4/3)
    sum_ln = math.log(4/3)
    rhs = S * LN2 - x * LN3  # = 2*ln2 - ln3 = ln4 - ln3 = ln(4/3)

    print(f"    Product identity: 3 + 1/B_0 = {3 + 1} = 4 = 2^{S} ✓")
    print(f"    sum ln(1+1/(3B)) = ln(4/3) = {sum_ln:.10f}")
    print(f"    S*ln2 - x*ln3 = {rhs:.10f}")
    print(f"    Match: {abs(sum_ln - rhs) < 1e-10} ✓")
    print()

    print(f"    eps_odd(1) = {e_odd:.10f}")
    print(f"    eps_even(4) = {e_even1:.10f}")
    print(f"    eps_even(2) = {e_even2:.10f}")
    print(f"    Sum = {E_sum:.10f}")
    print(f"    ln(1+d/3^x)/ln6 = ln(4/3)/ln6 = {math.log(4/3)/LN6:.10f}")
    print(f"    Match: {abs(E_sum - math.log(4/3)/LN6) < 1e-10}")
    print()

    # KEY: let's DERIVE why E_sum = ln(1+d/3^x)/ln6 exactly (for ANY cycle)
    print("  WHY E_sum = ln(1+d/3^x)/ln6 EXACTLY (for any cycle):")
    print("  ─" * 40)
    print()
    print("  Each compressed step B -> B' = (3B+1)/2^v in the phi-space:")
    print("    phi(B') - phi(B) = log_6((B'+1/5)/(B+1/5))  (mod 1)")
    print("                    = log_6((3B+1)/2^v + 1/5) - log_6(B + 1/5) (mod 1)")
    print()
    print("  For the FULL cycle:")
    print("    Σ [phi(B_{i+1}) - phi(B_i)] = 0  (mod 1)")
    print("    => Σ log_6((B_{i+1}+1/5)/(B_i+1/5)) = integer  (mod 1)")
    print("    => log_6(Π (B_{i+1}+1/5)/(B_i+1/5)) = integer")
    print("    => Π (B_{i+1}+1/5)/(B_i+1/5) = 6^m")
    print()
    print("  But for a cycle, Π B_{i+1}/B_i = 1 (telescoping).")
    print("  So Π (B_{i+1}+1/5)/(B_i+1/5) = 1 as well (same telescoping)!")
    print("  => 6^m = 1, so m = 0.")
    print()
    print("  Wait — this says E_total = 0 - (x+S)*alpha?? That can't be right.")
    print("  Let me reconsider. The phi function has fractional part {.}.")
    print("  The log_6 of the product could be a non-zero integer due to the")
    print("  fractional part wrapping.")
    print()
    print("  Actually NO: Π (B_{i+1}+1/5)/(B_i+1/5) is a TELESCOPING product.")
    print("  For a cycle (B_x = B_0): the product equals 1 EXACTLY.")
    print("  So log_6(product) = 0.")
    print("  But this is the SUM of log_6 ratios WITHOUT the mod 1.")
    print()
    print("  In the near-conjugacy decomposition:")
    print("    phi(B') - phi(B) = (v+1)*alpha + e_compressed_step  (mod 1)")
    print("  where e_compressed_step is the TOTAL error for that compressed step.")
    print()
    print("  The SUM (without mod 1) of log_6 ratios = 0.")
    print("  The SUM of (v_i+1)*alpha = (x+S)*alpha.")
    print("  So: 0 = (x+S)*alpha + E_total - m*1  (where m accounts for wrapping)")
    print("  => E_total = m - (x+S)*alpha")
    print()
    print("  But ALSO the exact sum is:")
    print("    Σ log_6((B_{i+1}+1/5)/(B_i+1/5)) = 0")
    print()
    print("  And this equals Σ [(v_i+1)*alpha + e_i] only mod 1.")
    print("  WITHOUT mod 1:")
    print("    log_6((B'+1/5)/(B+1/5)) = log_6((3B+1+1/5)/(2^v*(B+1/5)))")
    print("                             = log_6(3B+6/5) - v*log_6(2) - log_6(B+1/5)")
    print("                             = log_6(3(B+2/5)) - v*(1-alpha) - log_6(B+1/5)")
    print("                             = log_6(3) + log_6(B+2/5) - log_6(B+1/5) - v + v*alpha")
    print("                             = alpha + log_6(1+1/(5B+1)) - v(1-alpha)")
    print("                             = alpha + eps_odd(B) - v + v*alpha")
    print("                             = (1+v)*alpha - v + eps_odd(B)")
    print()
    print("  Wait — WHERE did the even errors go?")
    print("  The compressed step directly gives:")
    print("    log_6((B'+1/5)/(B+1/5)) = (1+v)*alpha - v + eps_odd(B)")
    print()
    print("  But earlier we said the error is eps_odd(B) + Σ eps_even(m_j).")
    print("  The resolution: in the compressed view, going directly from B to B',")
    print("  the 'rotation' includes (1+v)*alpha but the integer part is different.")
    print()
    print("  Let me separate integer and fractional parts more carefully.")
    print("  (1+v)*alpha - v = alpha + v*(alpha - 1) = alpha - v*(1-alpha)")
    print("                  = alpha - v*log_6(2)")
    print("  This is the 'expected' advance: one multiplication by 3 (adds alpha)")
    print("  and v divisions by 2 (each subtracts log_6(2) = 1-alpha).")
    print()
    print("  The full advance per compressed step:")
    print("    Delta_i = alpha - v_i*(1-alpha) + eps_odd(B_i)")
    print("            = alpha - v_i*log_6(2) + eps_odd(B_i)")
    print()
    print("  *** CRITICAL: The compressed error per step is JUST eps_odd(B_i). ***")
    print("  *** The even steps DON'T contribute additional errors! ***")
    print()
    print("  This is because in the DIRECT compressed computation")
    print("  B -> B' = (3B+1)/2^v, we compute phi(B') - phi(B) in one shot,")
    print("  and the only error beyond the rotation is eps_odd(B).")
    print()
    print("  The even errors ONLY appear when we decompose the compressed step")
    print("  into elementary steps. In the direct compressed view, they are")
    print("  ABSORBED into the integer count (the -v term).")
    print()

    # VERIFICATION
    print("  VERIFICATION: compressed error = just eps_odd")
    print()

    for B_test in [1, 3, 5, 7, 11, 27, 97, 871]:
        if B_test % 2 == 0:
            continue
        val = 3*B_test + 1
        v = 0
        while val % 2 == 0:
            val //= 2
            v += 1
        B_next = val

        # Direct: phi(B_next) - phi(B_test)
        direct = math.log(B_next + 0.2) / LN6 - math.log(B_test + 0.2) / LN6

        # Expected: alpha - v*(1-alpha) + eps_odd(B_test) = (1+v)*alpha - v + eps_odd
        expected = (1+v)*ALPHA - v + eps_odd_exact(B_test)

        # The difference should be an integer (from mod 1)
        diff = direct - expected
        diff_rounded = round(diff)
        residual = abs(diff - diff_rounded)

        # eps_odd only
        e_odd_only = eps_odd_exact(B_test)

        # Sum of elementary errors
        total_step, e_odd, e_evens = exact_cumulative_error_compressed_step(B_test, v)

        print(f"  B={B_test:>4d}, v={v}, B'={B_next:>6d}")
        print(f"    Direct phi diff = {direct:.10f}")
        print(f"    (1+v)*alpha - v + eps_odd = {expected:.10f}")
        print(f"    Difference = {diff:.10f} (nearest int: {diff_rounded}, residual: {residual:.2e})")
        print(f"    eps_odd(B) = {e_odd_only:.10f}")
        print(f"    eps_odd + Σ eps_even = {total_step:.10f}")
        print()

    print()
    print("  *** THE COMPRESSED-STEP ERROR IS eps_odd(B_i) ONLY. ***")
    print("  *** The even errors are NOT additional — they are an artifact ***")
    print("  *** of decomposing the compressed step into elementary steps. ***")
    print()

    # FINAL: redo the combination correctly
    print("  FINAL CORRECT COMBINATION:")
    print("  ═" * 40)
    print()
    print("  For a cycle:")
    print("    Σ Delta_i = 0  (mod integers, since phi returns)")
    print("    Σ [(1+v_i)*alpha - v_i + eps_odd(B_i)] = integer")
    print("    (x+S)*alpha - S + Σ eps_odd(B_i) = integer")
    print("    E_total = Σ eps_odd(B_i) = integer + S - (x+S)*alpha")
    print()
    print("  We showed (x+S)*alpha = S - ln(1+d/3^x)/ln6")
    print("  So: E_total = integer + S - S + ln(1+d/3^x)/ln6")
    print("              = integer + ln(1+d/3^x)/ln6")
    print("  And since E_total is small: integer = 0.")
    print("  => E_total = ln(1+d/3^x)/ln6  [EXACT]")
    print()
    print("  And E_total = Σ eps_odd(B_i) = Σ log_6(1 + 1/(5B_i+1))")
    print()
    print("  Now: eps_odd(B_i) ≈ 1/((5B_i+1)*ln6) ≈ 1/(5B_i*ln6)")
    print("  So: E_total ≈ Σ 1/(5B_i*ln6) = (1/5*ln6) * Σ(1/B_i)")
    print()
    print("  And from Step 3: Σ 1/B_i ≈ 3d/3^x")
    print()
    print("  Combining: E_total ≈ 3d/(5*3^x*ln6)")
    print("  But also: E_total ≈ d/(3^x*ln6)")
    print()
    print("  Ratio: (d/(3^x*ln6)) / (3d/(5*3^x*ln6)) = 5/3")
    print()
    print(f"  So we get 5/3 ≈ {5/3:.6f}, not 9/5.")
    print()
    print("  Is THIS a contradiction? 5/3 ≠ 1.")
    print()
    print("  NO. The discrepancy comes from the approximations:")
    print("    ln(1+d/3^x) ≈ d/3^x  (error: -d^2/(2*9^x))")
    print("    ln(1+1/(5B+1)) ≈ 1/(5B+1)  (error: -1/(2(5B+1)^2))")
    print("    ln(1+1/(3B)) ≈ 1/(3B)  (error: -1/(18B^2))")
    print()
    print("  The EXACT identity (no approximation needed) is:")
    print("    Σ log_6(1 + 1/(5B_i+1)) = ln(1+d/3^x)/ln6")
    print()
    print("  These are DIFFERENT functions of B_i, and equating their")
    print("  Taylor expansions at different orders gives apparent contradictions.")
    print("  But the exact forms are EQUAL by construction (both equal E_total).")
    print()

    # Final numerical proof
    print("  DEFINITIVE NUMERICAL PROOF for k=1:")
    print(f"    LHS = log_6(1 + 1/(5*1+1)) = log_6(7/6) = {math.log(7/6)/LN6:.15f}")
    print(f"    RHS = ln(1+d/3^x)/ln6 = ln(4/3)/ln6 = {math.log(4/3)/LN6:.15f}")
    print(f"    Equal? {abs(math.log(7/6)/LN6 - math.log(4/3)/LN6) < 1e-10}")
    print()
    print(f"    LHS = {math.log(7/6)/LN6:.15f}")
    print(f"    RHS = {math.log(4/3)/LN6:.15f}")
    print(f"    These are NOT equal! Difference = {math.log(7/6)/LN6 - math.log(4/3)/LN6:.15f}")
    print()
    print("  WAIT — they should be equal if the compressed error is just eps_odd.")
    print("  But they're NOT equal for k=1! Let me recheck.")
    print()
    print("  For k=1, the cycle has x=1 compressed step, with B_0=1, v_0=2.")
    print("  E_total from rotation = ln(1+d/3^x)/ln6 = ln(4/3)/ln6")
    print(f"           = {math.log(4/3)/LN6:.15f}")
    print()
    print("  E_total from eps sum:")
    print("  In COMPRESSED view: eps_odd(1) = log_6(1+1/6) = log_6(7/6)")
    print(f"           = {math.log(7/6)/LN6:.15f}")
    print()
    print("  These DIFFER. Why?")
    print()
    print("  Because the 'integer' in E_total = integer + ln(1+d/3^x)/ln6 might NOT be 0!")
    print("  Let me recompute:")
    L = 3  # x+S = 1+2
    La = L * ALPHA
    print(f"  (x+S)*alpha = 3*alpha = {La:.15f}")
    print(f"  S - ln(1+d/3^x)/ln6 = 2 - {math.log(4/3)/LN6:.10f} = {2 - math.log(4/3)/LN6:.15f}")
    print(f"  Match: {abs(La - (2 - math.log(4/3)/LN6)) < 1e-10}")
    print()
    print(f"  m = round(La) = {round(La)}")
    print(f"  E_total from rotation = m - La = {round(La) - La:.15f}")
    print(f"  E_from_eps (compressed: just eps_odd) = log_6(7/6) = {math.log(7/6)/LN6:.15f}")
    print()

    # Check: in compressed view, Delta_i = (1+v)*alpha - v + eps_odd
    delta = (1+2)*ALPHA - 2 + math.log(7/6)/LN6
    print(f"  Delta_0 = 3*alpha - 2 + eps_odd(1) = {delta:.15f}")
    print(f"  This should be an integer: nearest = {round(delta)}, residual = {abs(delta - round(delta)):.2e}")
    print()
    print("  For the cycle: Σ Delta_i = 0 (mod 1)")
    print(f"  Delta_0 = {delta:.15f}")
    print(f"  {delta:.15f} mod 1 = {delta % 1:.15f}")
    print(f"  Distance to 0 mod 1: {min(delta % 1, 1 - delta % 1):.2e}")
    print()

    # It should be 0 mod 1 for a genuine cycle!
    # Let me check with exact arithmetic
    # phi(1) = log_6(1.2) mod 1
    # phi(B') where B' = (3+1)/4 = 1 (cycle returns)
    # phi(1) = phi(1) so the cycle is consistent

    phi_1 = math.log(1.2) / LN6
    phi_1_mod1 = phi_1 % 1
    print(f"  phi(1) = log_6(1.2) = {phi_1:.15f}")
    print(f"  phi(1) mod 1 = {phi_1_mod1:.15f}")
    print()

    # Through elementary steps: 1 -> 4 -> 2 -> 1
    phi_4 = math.log(4.2) / LN6 % 1
    phi_2 = math.log(2.2) / LN6 % 1
    phi_1b = math.log(1.2) / LN6 % 1

    print(f"  Elementary orbit: phi(1)={phi_1_mod1:.10f}, phi(4)={phi_4:.10f}, phi(2)={phi_2:.10f}, phi(1)={phi_1b:.10f}")

    # Advances
    adv1 = (phi_4 - phi_1_mod1) % 1  # odd step 1->4
    adv2 = (phi_2 - phi_4) % 1        # even step 4->2
    adv3 = (phi_1b - phi_2) % 1       # even step 2->1
    total = (adv1 + adv2 + adv3)

    # Map advances to signed
    def signed_mod1(x):
        x = x % 1
        return x if x <= 0.5 else x - 1

    print(f"  Advance 1->4: {signed_mod1(adv1):.10f} (expected alpha = {ALPHA:.10f})")
    print(f"  Advance 4->2: {signed_mod1(adv2):.10f} (expected alpha = {ALPHA:.10f})")
    print(f"  Advance 2->1: {signed_mod1(adv3):.10f} (expected alpha = {ALPHA:.10f})")
    print(f"  Sum of advances: {signed_mod1(adv1) + signed_mod1(adv2) + signed_mod1(adv3):.10f}")
    print(f"  Total (raw): {total:.10f}")
    print(f"  floor(total): {int(total)}")
    print()

    # The sum of signed errors
    e1 = signed_mod1(adv1) - ALPHA
    e2 = signed_mod1(adv2) - ALPHA
    e3 = signed_mod1(adv3) - ALPHA
    print(f"  Error 1 (odd, n=1):  {e1:.10f}  vs eps_odd(1)={eps_odd_exact(1):.10f}")
    print(f"  Error 2 (even, n=4): {e2:.10f}  vs eps_even(4)={eps_even_exact(4):.10f}")
    print(f"  Error 3 (even, n=2): {e3:.10f}  vs eps_even(2)={eps_even_exact(2):.10f}")
    print(f"  Sum of errors: {e1+e2+e3:.10f}")
    print()

    # So the total E from elementary is e1+e2+e3
    E_elem = e1 + e2 + e3
    print(f"  E_total (elementary): {E_elem:.15f}")
    print(f"  ln(4/3)/ln6:         {math.log(4/3)/LN6:.15f}")
    print(f"  Match: {abs(E_elem - math.log(4/3)/LN6) < 1e-10}")
    print()

    # And the compressed E_total
    # In compressed view: one step B=1 -> B'=1
    # phi(B') - phi(B) = 0 (since B'=B for a cycle)
    # = (1+v)*alpha - v + eps_compressed (not mod 1, but the EXACT advance)
    # Direct: log_6((1+0.2)/(1+0.2)) = 0
    # So: 0 = (1+2)*alpha - 2 + eps_compressed - (integer wrapping)
    # 0 = 3*alpha - 2 + eps_compressed mod 1

    # In terms of the NON-mod-1 computation:
    # log_6(B'+0.2) - log_6(B+0.2) = 0 (since B'=B)
    # But going through elementary steps:
    # log_6(B'+0.2) - log_6(B+0.2) = sum of log_6 ratios at each step
    # = log_6(4.2/1.2) + log_6(2.2/4.2) + log_6(1.2/2.2)
    # = log_6(4.2/1.2 * 2.2/4.2 * 1.2/2.2) = log_6(1) = 0. ✓

    print("  CONCLUSION ON THE COMPRESSED vs ELEMENTARY VIEW:")
    print()
    print("  The TOTAL error E_total is computed from ELEMENTARY steps.")
    print("  It includes eps_odd + sum(eps_even) for each compressed step.")
    print("  E_total = ln(1+d/3^x)/ln6 = e1+e2+e3 for k=1.")
    print()
    print("  The COMPRESSED view error (just eps_odd) does NOT equal E_total.")
    print("  The compressed view absorbs even errors into integer wrapping,")
    print("  but the TOTAL rotation error includes all elementary contributions.")
    print()

    return


# ============================================================================
# FINAL VERDICT
# ============================================================================

def final_verdict():
    print("=" * 80)
    print("FINAL VERDICT: THE 9/5 'CONTRADICTION' IS INVALID")
    print("=" * 80)
    print()
    print("  ERRORS FOUND IN THE CLAIMED PROOF:")
    print()
    print("  1. STEP 1 IS WRONG (Critical)")
    print("     The correct expression is E_total = ln(1+d/3^x)/ln6,")
    print("     NOT d/(2^S*ln6). The ratio is:")
    print("       ln(1+d/3^x) / (d/2^S) = (2^S/3^x) * ln(1+d/3^x)/(d/3^x)")
    print("     For small d/3^x: ≈ (1+d/3^x) * 1 ≈ 1. So the error is small")
    print("     but the derivation in the claim is incorrectly attributed.")
    print("     The claim writes d/(2^S*ln6) but means d/(3^x*ln6). With 2^S,")
    print("     there is an extra factor 3^x/2^S = 1/(1+d/3^x) ≈ 1.")
    print("     This error alone does NOT invalidate the argument significantly,")
    print("     but it shows sloppy reasoning.")
    print()
    print("  2. STEP 2 IS WRONG (Critical)")
    print("     The coefficient c = 3/(5*ln6) is INCORRECT.")
    print("     The correct leading-order error per compressed step involves")
    print("     BOTH the odd error and the even errors at intermediate values.")
    print("     The even errors contribute an additional factor that depends on v_i.")
    print("     The correct leading-order sum is:")
    print("       E_total ≈ (1/(5*ln6)) * Σ(1/B_i)  [from eps_odd alone]")
    print("     The coefficient is 1/(5*ln6), NOT 3/(5*ln6).")
    print("     But this is incomplete: the even errors contribute additionally:")
    print("       E_total ≈ (1/(5*ln6)) * Σ(1/B_i)")
    print("              + (2/(5*ln6)) * Σ [sum_{j=1}^{v_i} 2^{j-1}/(3B_i+1)] / ln6")
    print("     which makes the total depend on v_i in a complex way.")
    print()
    print("  3. THE COMBINATION IS INVALID (Fatal)")
    print("     Even with corrected Steps 1 and 2, the argument equates two")
    print("     different APPROXIMATIONS to the same quantity E_total.")
    print("     Both sides are approximations with O(1/k^2) errors.")
    print("     The leading-order terms don't match because the Taylor expansions")
    print("     of log_6(1+1/(5B+1)) and 1/(5B+1) and log(1+1/(3B)) and 1/(3B)")
    print("     involve DIFFERENT functions evaluated at DIFFERENT points.")
    print("     There is no contradiction: the exact expressions are EQUAL")
    print("     (both equal E_total), and the apparent ratio ≠ 1 is an artifact")
    print("     of comparing incompatible approximations.")
    print()
    print("  4. THE TRIVIAL CYCLE k=1 IS A COUNTEREXAMPLE (Fatal)")
    print("     The argument, if valid, would also exclude k=1.")
    print("     But the cycle 1->4->2->1 exists. The argument must therefore")
    print("     fail somewhere, and we have identified exactly where:")
    print("     the approximations are too coarse to distinguish k=1 from k≥3.")
    print()
    print("  5. NO CIRCULAR REASONING FOUND")
    print("     The argument is not circular — it's simply wrong.")
    print("     The individual steps contain genuine mathematical content")
    print("     (near-conjugacy, product identity, error bounds) but the")
    print("     combination of approximations is mathematically invalid.")
    print()
    print("  SEVERITY: The claimed contradiction is COMPLETELY INVALID.")
    print("  It does NOT prove the absence of non-trivial Collatz cycles.")
    print()
    print("  The underlying mathematical framework (near-conjugacy, error")
    print("  structure, product identity) is CORRECT and potentially useful,")
    print("  but the specific argument as presented contains multiple fatal")
    print("  errors that render its conclusion unsupported.")
    print()
    print("=" * 80)
    print("END OF AUDIT")
    print("=" * 80)


# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    print()
    audit_step1()
    print()
    audit_step2()
    print()
    audit_step3()
    print()
    audit_step4()
    print()
    audit_trivial_cycle()
    print()
    audit_error_magnitudes()
    print()
    audit_definitive()
    print()
    final_verdict()
