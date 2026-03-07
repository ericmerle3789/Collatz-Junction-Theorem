#!/usr/bin/env python3
"""
Compute gcd(C, d-1) for all 19 prime d cases.
C = binom(S-1, k-1), d = 2^S - 3^k.
Output: table of values for Lean4 formalization.
"""
import math
import sys
sys.stdout.reconfigure(line_buffering=True)

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

KNOWN_K = [3, 4, 5, 13, 56, 61, 69, 73, 76, 148, 185, 655, 917, 2183, 3540, 3895, 4500, 6891, 7752]

print(f"{'k':>5s} | {'S':>5s} | {'bits(d)':>8s} | {'bits(C)':>8s} | {'gcd':>12s} | {'bits(gcd)':>9s} | {'2^gcd mod d':>12s} | {'pass':>5s}")
print("-" * 90)

for k in KNOWN_K:
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    C = math.comb(S - 1, k - 1)
    g = math.gcd(C, d - 1)
    test = pow(2, g, d)
    passed = test != 1
    test_str = str(test) if test < 10**6 else '(big)'
    print(f"{k:5d} | {S:5d} | {d.bit_length():8d} | {C.bit_length():8d} | {g:12d} | {g.bit_length():9d} | {test_str:>12s} | {'YES' if passed else 'NO'}")

print()
print("# Lean4 theorem statements:")
print()
for k in KNOWN_K:
    S = ceil_log2_3(k)
    d = pow(2, S) - pow(3, k)
    C = math.comb(S - 1, k - 1)
    g = math.gcd(C, d - 1)
    test = pow(2, g, d)
    assert test != 1, f"FAIL for k={k}!"
    print(f"-- k={k}, S={S}, d={d.bit_length()}b, C={C.bit_length()}b, gcd={g}, 2^gcd mod d = {test if test < 100 else '...'} ≠ 1")
    print(f"theorem g2c_k{k} : modPow 2 (Nat.gcd (binom {S-1} {k-1}) (2^{S} - 3^{k} - 1)) (2^{S} - 3^{k}) ≠ 1 := by native_decide")
    print()
