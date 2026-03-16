#!/usr/bin/env python3
"""
R199 Refined Arc Analysis

The arc argument from the preprint: for a cycle of length k with step sum S,
the cycle equation sum_{j=0}^{k-1} 2^{a_j} 3^{k-1-j} * n_0 = (2^S - 3^k) * n_0 / d
requires n_0 to be a positive integer.

The KEY bound: the maximum possible value g_max of the cycle polynomial
over all admissible step sequences is bounded by:
  g_max ≤ (3^k / d) * (something involving {k*theta})

More precisely, from Steiner's / Simons-de Weger's analysis:
For a cycle of length k, any element n satisfies:
  n ≥ 1 implies d(k) > 0 and n ≤ 3^k / d(k) * max_coefficient

The condition {k*theta} > log2(5/3) is SUFFICIENT but not NECESSARY.

Let me check the ACTUAL condition: can n_0 ≥ 1 exist?

For a hypothetical k-cycle, the smallest element n_0 satisfies:
  n_0 = d(k) * N_0 / (sum of weighted terms)

Actually, the precise Steiner bound is:
  n_min(k) ≥ 2^k / d(k) for cycles where all steps are "up"

Let me use the ACTUAL lower bound from the literature:
Steiner (1977): If (n_0, n_1, ..., n_{k-1}) is a k-cycle, then
  n_0 ≥ 2^k / (3 * d(k)) when d(k) > 0

And the upper bound: n_0 < 3^k / d(k) (from the cycle equation)

But the REAL question is N_0(d) = 0, which requires showing the cycle
polynomial has no positive integer solutions.

Let me reconsider. The arc argument works when:
For ALL compositions (s_1,...,s_k) with s_i ≥ 1 and sum = S,
the polynomial P(s_1,...,s_k) = sum_{j=0}^{k-1} 2^{s_1+...+s_j} * 3^{k-1-j}
satisfies P / d(k) is not a positive integer.

A STRONGER sufficient condition than {k*theta} > log2(5/3):
  g_max = max over compositions of P(s_1,...,s_k)
  If g_max < 2*d(k), then n_0 = P/d ∈ (0, 2), so n_0 = 1 only possible.
  Then check n_0 = 1 directly.

Actually, the standard result (Bohm & Sontacchi 1978, also Crandall 1978):
A nontrivial k-cycle exists iff there exist integers 1 ≤ s_1, ..., s_k with
s_1 + ... + s_k = S such that
  n_0 = (sum_{j=1}^{k} 3^{k-j} * 2^{s_1+...+s_j}) / d(k)
is a POSITIVE INTEGER.

The maximum of the numerator over all compositions:
  When all power of 2 is concentrated at the end: s_k = S-k+1, s_i=1 for i<k
  numerator_max ≈ 2^S * (1 + 3/2 + 9/4 + ...) / 3 ≈ 2^S * 3^{k-1} / (3-2) = 2^S * 3^{k-1}
  But more carefully: numerator = sum_{j=1}^k 3^{k-j} * 2^{a_j} where a_j = s_1+...+s_j

The MINIMUM of the numerator (over compositions):
  When power is spread evenly: s_i = S/k for each i
  numerator_min ≈ 3^{k-1} * 2^{S/k} * (1 - (2/3)^k * 2^{(k-1)S/k}) / ... complicated

Let me just compute directly. For each OPEN k, compute:
1. The minimum and maximum of the numerator over all compositions
   (by optimization, not exhaustive enumeration)
2. Check if min_numerator / d(k) > 1 (would mean n_0 ≥ 2)
3. Check if max_numerator / d(k) < 1 (would mean no solution, i.e., arc works)
"""

from math import comb
from mpmath import mp, mpf, log as mplog, ceil as mpceil, floor as mpfloor

mp.dps = 50
theta = mplog(3) / mplog(2)

print("="*80)
print("REFINED ARC: Computing g_max and g_min bounds")
print("="*80)
print()

# For a composition (s_1,...,s_k) with s_i ≥ 1, sum = S:
# numerator = sum_{j=1}^{k} 3^{k-j} * 2^{s_1+...+s_j}
# = sum_{j=1}^{k} 3^{k-j} * 2^{a_j}  where a_1 < a_2 < ... < a_k = S

# g_max is achieved when we MAXIMIZE the numerator.
# Since 3^{k-j} decreases with j but 2^{a_j} increases,
# to maximize: we want large 2^{a_j} paired with large 3^{k-j}.
# This means: make a_1 as large as possible = give big steps early.
# Optimal: s_1 = S-k+1, s_2 = s_3 = ... = s_k = 1
# Then a_j = S-k+1 + (j-1) for j ≥ 1, so a_1 = S-k+1, a_k = S.

# g_min is achieved when we MINIMIZE.
# Optimal: s_1 = s_2 = ... = s_{k-1} = 1, s_k = S-k+1
# Then a_j = j for j < k, a_k = S.

open_ks = [18,19,20,21,23,24,25,26,28,30,31,32,33,35,36,37,38,40]

print(f"{'k':>3} {'S':>4} {'d(k)':>20} {'g_min':>25} {'g_max':>25} {'g_min/d':>15} {'g_max/d':>15} {'status'}")
print("-"*130)

for k in open_ks:
    S = int(mpceil(k * theta))
    d = 2**S - 3**k

    if d <= 0:
        print(f"{k:>3} {S:>4}: d <= 0, SKIP")
        continue

    # g_max: s_1 = S-k+1, rest = 1
    # a_j for j=1..k: a_1 = S-k+1, a_2 = S-k+2, ..., a_k = S
    g_max = 0
    for j in range(1, k+1):
        a_j = S - k + j  # = (S-k+1) + (j-1)
        g_max += 3**(k-j) * 2**a_j

    # g_min: s_k = S-k+1, rest = 1
    # a_j for j=1..k: a_1 = 1, a_2 = 2, ..., a_{k-1} = k-1, a_k = S
    g_min = 0
    for j in range(1, k):
        g_min += 3**(k-j) * 2**j
    g_min += 3**0 * 2**S  # j = k term

    ratio_min = g_min / d
    ratio_max = g_max / d

    # n_0 must be an integer in [g_min/d, g_max/d]? No!
    # n_0 = numerator/d for SOME specific composition
    # But g_max/d gives an UPPER bound on n_0 for the max-numerator composition
    # The point is: if g_max < d, then n_0 < 1 for ALL compositions, so no cycle exists.

    if g_max < d:
        status = "RESOLVED (g_max < d)"
    elif g_min > d:
        # All n_0 ≥ 2, cycles must have large elements
        status = f"n_0 ≥ {g_min // d} for all comps"
    else:
        n_max = g_max // d
        status = f"OPEN (n_0 ≤ {n_max})"

    print(f"{k:>3} {S:>4} {d:>20} {g_min:>25} {g_max:>25} {float(ratio_min):>15.4f} {float(ratio_max):>15.4f} {status}")

print()
print("="*80)
print("KEY INSIGHT: g_max < d is equivalent to the arc argument")
print("="*80)
print()
print("For reference, the RESOLVED (arc) cases from Part 1:")
for k in [22, 27, 29, 34, 39, 41]:
    S = int(mpceil(k * theta))
    d = 2**S - 3**k
    g_max = sum(3**(k-j) * 2**(S-k+j) for j in range(1, k+1))
    print(f"  k={k}: g_max/d = {g_max/d:.6f}, g_max < d? {g_max < d}")

print()
print("="*80)
print("CONCLUSION: Which k in 18..41 are truly OPEN?")
print("="*80)
print()

# Recheck all with both criteria
all_resolved = []
all_open = []

for k in range(18, 42):
    S = int(mpceil(k * theta))
    d = 2**S - 3**k
    frac = float(k * theta - mpfloor(k * theta))

    g_max = sum(3**(k-j) * 2**(S-k+j) for j in range(1, k+1))
    g_min = sum(3**(k-j) * 2**j for j in range(1, k)) + 2**S

    arc_frac = frac > float(mplog(mpf(5)/3) / mplog(2))
    arc_gmax = g_max < d

    if arc_frac or arc_gmax:
        all_resolved.append(k)
        method = "arc({k*theta})" if arc_frac else "arc(g_max<d)"
        print(f"  k={k}: RESOLVED by {method}")
    else:
        n_upper = g_max // d
        all_open.append((k, n_upper))
        print(f"  k={k}: OPEN, n_0 ≤ {n_upper}")

print()
print(f"RESOLVED: {len(all_resolved)} values: {all_resolved}")
print(f"OPEN: {len(all_open)} values: {[x[0] for x in all_open]}")

# For OPEN cases, compute tighter bounds
print()
print("="*80)
print("OPEN CASES: Hercher/Barina lower bounds")
print("="*80)
print()
print("Hercher (2023): No non-trivial cycle with min element < 2^68")
print("Barina (2020): Verified up to ~2^68")
print()

for k, n_upper in all_open:
    S = int(mpceil(k * theta))
    d = 2**S - 3**k
    hercher_bound = 2**68

    g_max = sum(3**(k-j) * 2**(S-k+j) for j in range(1, k+1))
    n_max = g_max // d

    if n_max < hercher_bound:
        print(f"  k={k}: n_0 ≤ {n_max:.3e}, Hercher bound = {hercher_bound:.3e} -> ", end="")
        if n_max < hercher_bound:
            print("RESOLVED by Hercher/Barina!")
        else:
            print("still OPEN")
    else:
        print(f"  k={k}: n_0 ≤ {n_max:.3e}, exceeds Hercher bound {hercher_bound:.3e} -> OPEN")
