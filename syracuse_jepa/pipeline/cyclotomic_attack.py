#!/usr/bin/env python3
"""
CYCLOTOMIC ATTACK — Exploit factorization of X^S - 3^k
"""

import sys, os
from math import ceil, log2, comb, gcd
from itertools import combinations
from functools import reduce

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def mobius(k):
    if k == 1: return 1
    n = k
    factors = set()
    d = 2
    while d * d <= n:
        if n % d == 0:
            if n // d % d == 0:
                return 0
            factors.add(d)
            n //= d
        else:
            d += 1
    if n > 1:
        factors.add(n)
    return (-1)**len(factors)


def cyclotomic_homogeneous(n, x, y):
    """Phi_n(x, y) via Mobius inversion."""
    divisors = [d for d in range(1, n+1) if n % d == 0]
    num, den = 1, 1
    for d in divisors:
        val = x**d - y**d
        mu = mobius(n // d)
        if mu == 1:
            num *= val
        elif mu == -1:
            den *= val
    if den == 0 or num % den != 0:
        return None
    return num // den


def analyze_cyclotomic(k_max=20):
    print("CYCLOTOMIC FACTORIZATION")
    print("=" * 70)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        g = gcd(S, k)
        a, b = S // g, k // g

        if g == 1:
            print(f"k={k:2d}, S={S:2d}: d={d} (irreducible, single Phi)")
            continue

        divisors = [m for m in range(1, g+1) if g % m == 0]
        factors = {}
        for m in divisors:
            val = cyclotomic_homogeneous(m, 2**a, 3**b)
            if val is not None and val != 0:
                factors[m] = val

        product = reduce(lambda x, y: x * y, factors.values(), 1)
        ok = abs(product) == abs(d)

        C = count_cumulative_sequences(k, S)
        print(f"k={k:2d}, S={S:2d}, g={g}: factors = ", end="")
        print(" · ".join(f"Phi_{m}={v}" for m, v in factors.items()), end="")
        print(f" {'✓' if ok else '✗'}")

        if C <= 200000:
            for m, factor_val in factors.items():
                fv = abs(factor_val)
                if fv <= 1: continue
                n_div = 0
                for sigma in enumerate_cumulative_sequences(k, S):
                    cs = corrsum_cumulative(sigma, k)
                    if cs % fv == 0:
                        n_div += 1
                marker = "★ BLOCKS!" if n_div == 0 else ""
                print(f"    Phi_{m}={fv}: N0={n_div}/{C} {marker}")


if __name__ == '__main__':
    analyze_cyclotomic()
