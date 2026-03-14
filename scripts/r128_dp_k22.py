#!/usr/bin/env python3
"""
R128 — DP verification for k=22: N_0(d(22)) = 0 ?

d(22) = 2978678759 ≈ 3×10^9. C/d ≈ 0.31.
Approach: sparse DP tracking reachable corrSum residues mod d.

Uses dict of sets: for each partial_sum s, store set of corrSum mod d.
"""
import math
import time
from collections import defaultdict

k = 22
S = 35
d = 2**S - 3**k  # = 2978678759

print(f"k={k}, S={S}, d={d}")
print(f"C(S-1,k-1) = {math.comb(S-1,k-1)}")
print(f"C/d = {math.comb(S-1,k-1)/d:.4f}")
print()

# Precompute 3^i mod d and 2^i mod d
pow3 = [1] * k
for i in range(1, k):
    pow3[i] = (pow3[i-1] * 3) % d

pow2 = [1] * (S + 1)
for i in range(1, S + 1):
    pow2[i] = (pow2[i-1] * 2) % d

# DP: current[s] = set of reachable corrSum mod d values at step j
# j goes from 0 to k-1 (choosing a_0 through a_{k-1})

current = defaultdict(set)
current[0].add(0)  # initial: s=0, c=0

start_time = time.time()

for j in range(k):
    next_states = defaultdict(set)
    coeff = pow3[k - 1 - j]  # 3^{k-1-j} mod d

    # s ranges from j to S - (k - j) = S - k + j
    total_new = 0
    for s in range(j, S - k + j + 1):
        if s not in current:
            continue
        c_set = current[s]
        if not c_set:
            continue

        # a_j ranges from 1 to S - s - (k - 1 - j)
        max_a = S - s - (k - 1 - j)

        for a_j in range(1, max_a + 1):
            new_s = s + a_j
            exponent = S - new_s
            # contribution = 3^{k-1-j} * 2^{S - new_s} mod d
            contrib = (coeff * pow2[exponent]) % d

            # Batch add: shift all c values by contrib
            new_set = {(c + contrib) % d for c in c_set}
            next_states[new_s].update(new_set)
            total_new += len(new_set)

    current = next_states

    # Stats
    total_states = sum(len(v) for v in current.values())
    elapsed = time.time() - start_time
    print(f"Step {j+1}/{k}: {total_states:,} reachable states, "
          f"time={elapsed:.1f}s, "
          f"s_range=[{min(current.keys()) if current else '?'}, {max(current.keys()) if current else '?'}]")

    # Safety check: abort if too many states
    if total_states > 500_000_000:  # 500M limit
        print(f"ABORT: too many states ({total_states:,}). DP infeasible in Python.")
        break

# Check result
if S in current:
    if 0 in current[S]:
        print(f"\n*** N_0({d}) > 0 : corrSum ≡ 0 mod d IS reachable ***")
        print(f"*** This would mean a {k}-cycle EXISTS! ***")
    else:
        print(f"\n*** N_0({d}) = 0 : corrSum ≡ 0 mod d is NOT reachable ***")
        print(f"*** k={k} is CLOSED: no {k}-cycle exists! ***")
else:
    print(f"\nDP did not reach s=S={S}. Something went wrong.")

total_time = time.time() - start_time
print(f"\nTotal time: {total_time:.1f}s")
