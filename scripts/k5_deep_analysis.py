#!/usr/bin/env python3
"""
Deep algebraic analysis of k=5 case.
d=13 (prime), S=8, C(7,4)=35 sequences, only 12/13 residues hit, 0 missed.
WHY is 0 the specifically missed residue?
"""

from itertools import combinations
from math import gcd

k, S, d = 5, 8, 13
print(f"k={k}, S={S}, d={d} (prime)")
print(f"2^S = {2**S}, 3^k = {3**k}, d = {2**S - 3**k} = {d}")
print()

# Arithmetic mod 13
print("=== Arithmetic mod 13 ===")
ord2 = next(j for j in range(1, 14) if pow(2, j, 13) == 1)
ord3 = next(j for j in range(1, 14) if pow(3, j, 13) == 1)
print(f"ord_13(2) = {ord2}")
print(f"ord_13(3) = {ord3}")
print(f"2 is primitive root mod 13: {ord2 == 12}")
print()

# Powers of 2 mod 13
pow2_mod = [pow(2, i, 13) for i in range(S)]
print(f"2^i mod 13 for i=0..{S-1}: {pow2_mod}")
# Powers of 3 mod 13
pow3_mod = [pow(3, i, 13) for i in range(k)]
print(f"3^i mod 13 for i=0..{k-1}: {pow3_mod}")
print()

# Weights: w_i = 3^{k-1-i} mod 13
weights = [pow(3, k-1-i, 13) for i in range(k)]
print(f"Weights w_i = 3^(k-1-i) mod 13: {weights}")
print()

# Enumerate all cumulative sequences and their corrSum mod 13
print("=== All 35 cumulative sequences ===")
print(f"{'sigma':>20} {'corrSum':>10} {'mod 13':>7} {'corrSum/d':>10}")
print("-" * 55)

residue_count = [0] * d
residue_seqs = {r: [] for r in range(d)}

for combo in combinations(range(1, S), k-1):
    sigma = (0,) + combo
    cs = sum(3**(k-1-i) * 2**sigma[i] for i in range(k))
    r = cs % d
    residue_count[r] += 1
    residue_seqs[r].append(sigma)
    q = cs // d
    print(f"{str(sigma):>20} {cs:>10} {r:>7} {q:>10}")

print()
print("=== Residue distribution mod 13 ===")
for r in range(d):
    count = residue_count[r]
    bar = "█" * count
    marker = " *** MISSED ***" if count == 0 else ""
    print(f"  r={r:2d}: {count:2d} {bar}{marker}")

print()
print("=== Which residue is missed? ===")
missed = [r for r in range(d) if residue_count[r] == 0]
print(f"Missed residues: {missed}")

# Algebraic analysis: corrSum mod 13 = Σ w_i · 2^{σ_i} mod 13
print()
print("=== Algebraic structure ===")
# In Z/13Z, the corrSum is: Σ_{i=0}^{4} w_i · α^{σ_i}
# where α = 2, w = (81, 27, 9, 3, 1) mod 13 = (3, 1, 9, 3, 1)
# and σ_0 = 0 (fixed).
print(f"In Z/13Z: corrSum = Σ w_i · 2^(σ_i)")
print(f"Weights mod 13: {weights}")
print(f"Base contribution (σ_0=0): w_0 · 2^0 = {weights[0]} · 1 = {weights[0]} mod 13")
print(f"For corrSum ≡ 0: remaining sum must be ≡ {(-weights[0]) % d} mod 13")
target = (-weights[0]) % d
print(f"Target: {target}")
print()

# Express as: w_1·2^σ_1 + w_2·2^σ_2 + w_3·2^σ_3 + w_4·2^σ_4 ≡ target mod 13
# where 0 < σ_1 < σ_2 < σ_3 < σ_4 ≤ 7
print("=== Reduced problem: 4 values from {2^1,...,2^7} mod 13 ===")
print(f"w_1·2^σ_1 + w_2·2^σ_2 + w_3·2^σ_3 + w_4·2^σ_4 ≡ {target} mod 13")
print(f"w = ({weights[1]}, {weights[2]}, {weights[3]}, {weights[4]})")
available = [(i, pow(2, i, 13)) for i in range(1, S)]
print(f"Available 2^i mod 13: {[(i, v) for i, v in available]}")
print()

# Check ALL sums
print("=== Check all 4-subsets of positions {1..7} ===")
count_at_target = 0
for combo in combinations(range(1, S), 4):
    vals = [pow(2, s, 13) for s in combo]
    wsum = sum(weights[j+1] * vals[j] for j in range(4)) % d
    if wsum == target:
        count_at_target += 1
        print(f"  {combo}: weighted sum = {wsum} ≡ {target} mod 13 *** HIT ***")

print(f"\nCount hitting target {target}: {count_at_target}")
if count_at_target == 0:
    print("CONFIRMED: No 4-subset gives the target. 0 is structurally avoided.")

# WHY? Analyze the algebraic constraints
print()
print("=== Deeper: Weighted sum values for all 35 subsets ===")
all_wsums = []
for combo in combinations(range(1, S), 4):
    vals = [pow(2, s, 13) for s in combo]
    wsum = sum(weights[j+1] * vals[j] for j in range(4)) % d
    all_wsums.append(wsum)

from collections import Counter
wsum_dist = Counter(all_wsums)
print(f"Distribution of weighted sums mod 13:")
for r in range(d):
    c = wsum_dist.get(r, 0)
    marker = " *** TARGET (not hit) ***" if r == target and c == 0 else ""
    print(f"  {r:2d}: {c:2d} {'█'*c}{marker}")

# Key question: is the avoidance of 'target' related to 2^S ≡ 3^k mod 13?
print()
print("=== Algebraic connection to 2^S = 3^k mod d ===")
print(f"2^{S} mod 13 = {pow(2, S, 13)}")
print(f"3^{k} mod 13 = {pow(3, k, 13)}")
print(f"They are equal: {pow(2, S, 13) == pow(3, k, 13)}")

# Note: 2^8 = 256, 3^5 = 243. 256-243 = 13. So 2^8 ≡ 3^5 ≡ 9 mod 13.
# The relation α^S = β^k means there's a deep connection.

# Let's see what happens if we replace the target with other values
print()
print("=== What if we tested OTHER residues as 'forbidden'? ===")
print("For each r, count 4-subsets with weighted sum ≡ (13-3-r) mod 13:")
# corrSum ≡ r mod 13 means 3 + weighted_remainder ≡ r
# so weighted_remainder ≡ r - 3 mod 13
for target_r in range(d):
    adjusted_target = (target_r - weights[0]) % d
    count = sum(1 for combo in combinations(range(1, S), 4)
                for vals in [[pow(2, s, 13) for s in combo]]
                if sum(weights[j+1] * vals[j] for j in range(4)) % d == adjusted_target)
    marker = " ← actual (N0 for cycles)" if target_r == 0 else ""
    print(f"  corrSum ≡ {target_r:2d}: {count:2d} sequences{marker}")

print()
print("=== KEY INSIGHT ===")
print("The corrSum ≡ 0 case corresponds to Collatz cycles.")
print("This is the ONLY value in Z/13Z not achieved by the evaluation map.")
print("The algebraic coupling α^S = β^k (equivalently d = 2^S - 3^k)")
print("creates exactly this exclusion.")
