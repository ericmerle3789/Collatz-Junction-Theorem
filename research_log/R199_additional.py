#!/usr/bin/env python3
"""
R199 Additional analysis:
1. For k=32, {k*theta} = 0.7188 is very close to threshold 0.73697. Can we tighten?
2. For k=33, the large prime 118901334075361 has p/C(k) = 0.9437 -- nearly exceeds C(k)
3. Divisibility patterns: d(k) | d(mk) for certain m?
4. Relationship between d(18) factors and d(36) factors (k and 2k)
"""

from math import comb, gcd
from mpmath import mp, mpf, log as mplog, ceil as mpceil, floor as mpfloor
from sympy import factorint
from sympy.ntheory import n_order

mp.dps = 50
theta = mplog(3) / mplog(2)
LOG2_5_3 = float(mplog(mpf(5)/mpf(3)) / mplog(2))

print("="*80)
print("PART 1: Near-miss arc cases")
print("="*80)
print()
print(f"Arc threshold: {{k*theta}} > log2(5/3) = {LOG2_5_3:.15f}")
print()

# k values sorted by how close {k*theta} is to the threshold
near_misses = []
for k in range(18, 42):
    frac = float(k * theta - mpfloor(k * theta))
    gap = frac - LOG2_5_3
    near_misses.append((abs(gap), gap, k, frac))

near_misses.sort()
print("Closest to arc threshold (sorted by |gap|):")
for absgap, gap, k, frac in near_misses[:10]:
    status = "ARC OK" if gap > 0 else "NO ARC"
    print(f"  k={k:2d}: {{k*theta}} = {frac:.12f}, gap = {gap:+.12f}  [{status}]")

print()
print("="*80)
print("PART 2: k=32 deep analysis (closest miss, gap = -0.018)")
print("="*80)
# k=32: {32*theta} = 0.7188, threshold = 0.7370
# d(32) = 73 * 5462734586759
# Can we use a refined arc argument? The arc argument says g_max < d.
# g_max = C(S-1, k-1) * (2^S/d - 1) when {k*theta} is large
# Actually the key condition is 2^{S} < (5/3) * 3^k, i.e., d < (2/3)*3^k

k = 32
S = int(mpceil(k * theta))
d = 2**S - 3**k
three_k = 3**k
ratio = float(mpf(d) / (mpf(2)/3 * mpf(three_k)))
print(f"k=32: d = {d}")
print(f"  3^k = {three_k}")
print(f"  (2/3)*3^k = {2*three_k//3}")
print(f"  d / ((2/3)*3^k) = {ratio:.10f}")
print(f"  Arc needs d < (2/3)*3^k, ratio = {ratio:.10f}")
if ratio < 1:
    print(f"  Arc WOULD work! ratio < 1")
else:
    print(f"  Arc fails: ratio = {ratio:.6f} >= 1")

print()
print("="*80)
print("PART 3: Divisibility relations d(k) | d(mk)")
print("="*80)
print()
# Check if d(k) | d(2k) or other relations
for k1 in range(18, 22):
    S1 = int(mpceil(k1 * theta))
    d1 = 2**S1 - 3**k1
    for m in [2, 3]:
        k2 = m * k1
        if k2 > 41:
            continue
        S2 = int(mpceil(k2 * theta))
        d2 = 2**S2 - 3**k2
        if d2 % d1 == 0:
            print(f"  d({k1}) | d({k2}): {d1} divides {d2}, quotient = {d2 // d1}")
        else:
            r = d2 % d1
            g = gcd(d1, d2)
            print(f"  d({k1}) does NOT divide d({k2}), gcd = {g}")

# Check d(18) and d(36) share factors
print()
print("Shared prime factors between d(k) and d(2k):")
for k1 in [18, 19, 20]:
    k2 = 2 * k1
    if k2 > 41:
        continue
    S1 = int(mpceil(k1 * theta))
    d1 = 2**S1 - 3**k1
    S2 = int(mpceil(k2 * theta))
    d2 = 2**S2 - 3**k2
    f1 = set(factorint(d1).keys())
    f2 = set(factorint(d2).keys())
    shared = f1 & f2
    print(f"  d({k1}) primes: {sorted(f1)}")
    print(f"  d({k2}) primes: {sorted(f2)}")
    print(f"  Shared: {sorted(shared)}")
    print()

print("="*80)
print("PART 4: Structural observations on multiplicative orders")
print("="*80)
print()
# For p | d(k) = 2^S - 3^k, we have 2^S ≡ 3^k (mod p)
# So ord_p(2) divides gcd of {n : 2^n ≡ 3^k mod p}
# In particular, 2^S ≡ 3^k mod p means 2^S * 3^{-k} ≡ 1 mod p
# If we let alpha = ord_p(2) and beta = ord_p(3), then
# S*alpha_inv ≡ k*beta_inv (mod something)...
# Actually: ord_p(2) | S iff 2^S ≡ 1 mod p, which means 3^k ≡ 1 mod p too

print("For p | d(k): checking 2^S mod p and 3^k mod p")
test_cases = {
    18: {137: 68, 1090879: 181813},
    32: {73: 9, 5462734586759: 2731367293379},
    33: {29: 28, 118901334075361: 19816889012560},
}

for k, primes in test_cases.items():
    S = int(mpceil(k * theta))
    d = 2**S - 3**k
    print(f"\nk={k}, S={S}, d={d}:")
    for p, ord2 in primes.items():
        r2 = pow(2, S, p)
        r3 = pow(3, k, p)
        print(f"  p={p}: 2^{S} mod p = {r2}, 3^{k} mod p = {r3}, 2^S - 3^k mod p = {(r2 - r3) % p}")
        print(f"    ord_p(2) = {ord2}, S mod ord = {S % ord2}")
        # ord_p(3)
        try:
            ord3 = n_order(3, p)
            print(f"    ord_p(3) = {ord3}, k mod ord = {k % ord3}")
        except:
            print(f"    ord_p(3): computation skipped")

print()
print("="*80)
print("PART 5: k=33 — largest prime nearly exceeds C(k)")
print("="*80)
k = 33
S = int(mpceil(k * theta))
d = 2**S - 3**k
C_k = comb(S-1, k-1)
p_large = 118901334075361
ratio_pC = p_large / C_k
print(f"k=33: p_large = {p_large}")
print(f"  C(k) = C({S-1},{k-1}) = {C_k}")
print(f"  p/C(k) = {ratio_pC:.10f}")
print(f"  C(k) - p = {C_k - p_large}")
print(f"  Deficit: {(C_k - p_large) / C_k * 100:.2f}% of C(k)")
print()
# For pigeonhole, we need p > C(k). The deficit is small.
# Is there a tighter bound than C(S-1,k-1)?

# The cycle equation: sum_{i=0}^{k-1} 2^{s_i} * 3^{k-1-i} * n_0 ≡ 0 mod d
# where 0 ≤ s_0 < s_1 < ... < s_{k-1} = S
# The number of ways to choose s_0,...,s_{k-2} from {0,...,S-1}
# with s_{k-1}=S fixed is C(S-1, k-1) but actually it's C(S, k-1)
# Wait, let's be precise. We need 0 ≤ s_0 < s_1 < ... < s_{k-1}
# with s_{k-1} = S-1 (or similar). Let me recheck.

# Actually for the Collatz cycle, S = s_0 + s_1 + ... + s_{k-1} where s_i ≥ 1
# and the number of compositions is not C(S-1,k-1).
# C(S-1,k-1) counts the number of ways to write S as an ordered sum of k positive integers.

print("Clarification on C(k):")
print(f"  C(S-1, k-1) counts compositions of S into k positive parts")
print(f"  This equals the number of admissible step sequences (s_1,...,s_k) with s_i >= 1, sum = S")
print(f"  = C({S-1}, {k-1}) = {C_k}")

print()
print("="*80)
print("PART 6: Summary of strategies per OPEN k")
print("="*80)
print()

open_ks = [18,19,20,21,23,24,25,26,28,30,31,32,33,35,36,37,38,40]
for k in open_ks:
    S = int(mpceil(k * theta))
    d = 2**S - 3**k
    frac = float(k * theta - mpfloor(k * theta))
    gap = frac - LOG2_5_3
    factors = factorint(d)
    C_k = comb(S-1, k-1)
    max_p = max(factors.keys())
    ratio = max_p / C_k

    strategies = []
    if abs(gap) < 0.1:
        strategies.append(f"near-arc (gap={gap:+.4f})")
    if ratio > 0.5:
        strategies.append(f"near-pigeonhole (p/C={ratio:.4f})")
    if max_p > C_k:
        strategies.append("PIGEONHOLE")

    strat_str = ", ".join(strategies) if strategies else "no obvious shortcut"
    print(f"  k={k:2d}: max_p/C(k)={ratio:.6e}, arc_gap={gap:+.6f} -> {strat_str}")
