#!/usr/bin/env python3
"""
R86 — Modular Decoupling: verify ord_p(2) > sqrt(p) for primes of d(k)
========================================================================
If ord_p(2) > sqrt(p) for ALL primes p | d(k), then the Gauss sum bound
gives exponential cancellation in character sums, proving N_0(p) ~ C/p.

Check this condition for k = 21..41.
"""

import math
from sympy import factorint
from collections import defaultdict

def ord_mod(a, n):
    """Compute multiplicative order of a modulo n."""
    if math.gcd(a, n) > 1:
        return -1
    r = 1
    x = a % n
    while x != 1:
        x = (x * a) % n
        r += 1
        if r > n:
            return -1  # shouldn't happen
    return r

def main():
    print("=" * 80)
    print("R86 — Modular Decoupling Condition: ord_p(2) > sqrt(p) for all p | d(k)")
    print("=" * 80)
    print()

    results = {}

    for k in range(21, 42):
        S = math.ceil(k * math.log2(3))
        d = 2**S - 3**k
        C = math.comb(S - 1, k - 1)

        # Factor d
        factors = factorint(d)
        primes = sorted(factors.keys())

        all_satisfy = True
        prime_data = []

        for p in primes:
            e = factors[p]
            r = ord_mod(2, p)
            sp = math.isqrt(p) + 1  # ceil(sqrt(p))
            satisfies = r > math.sqrt(p)
            ratio = r / math.sqrt(p)
            prime_data.append((p, e, r, sp, satisfies, ratio))
            if not satisfies:
                all_satisfy = False

        results[k] = {
            'S': S, 'd': d, 'C': C, 'factors': factors,
            'primes': prime_data, 'all_satisfy': all_satisfy
        }

        status = "✅" if all_satisfy else "❌"
        print(f"k={k:2d}, S={S:2d}, d={d:>20,}")
        print(f"  C/d = {C/d:.4f}, factors = {' × '.join(str(p) + ('^'+str(e) if e>1 else '') for p,e in sorted(factors.items()))}")
        for p, e, r, sp, sat, ratio in prime_data:
            mark = "✓" if sat else "✗"
            print(f"  p={p:>12,}: ord_p(2)={r:>8,}, √p≈{math.sqrt(p):>8.1f}, ratio={ratio:>6.2f} {mark}")

        # Compute cancellation rate if all satisfy
        if all_satisfy:
            max_ratio = max(math.sqrt(p) / r for p, _, r, _, _, _ in prime_data)
            decay = max_ratio ** k
            print(f"  Cancellation: max(√p/r) = {max_ratio:.4f}, decay^k = {decay:.2e}")
            print(f"  → Bound: |N_0 - C/d| ≤ C × K × {decay:.2e}")
            print(f"  {status} ALL PRIMES SATISFY ord > √p — Lemma APPLIES")
        else:
            bad = [(p, r, ratio) for p, _, r, _, sat, ratio in prime_data if not sat]
            print(f"  {status} FAILS for: {', '.join(f'p={p} (ratio={ratio:.2f})' for p,r,ratio in bad)}")
        print()

    # Summary
    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    passing = [k for k in range(21, 42) if results[k]['all_satisfy']]
    failing = [k for k in range(21, 42) if not results[k]['all_satisfy']]
    print(f"  PASS (ord > √p for all p): {len(passing)}/21 — k = {passing}")
    print(f"  FAIL: {len(failing)}/21 — k = {failing}")
    print()

    if failing:
        print("Analysis of failures:")
        for k in failing:
            data = results[k]
            bad = [(p, r, ratio) for p, _, r, _, sat, ratio in data['primes'] if not sat]
            for p, r, ratio in bad:
                print(f"  k={k}: p={p}, ord={r}, √p={math.sqrt(p):.1f}, ratio={ratio:.3f}")
                # Check if ord > p^(1/3) at least
                if r > p**(1./3):
                    print(f"         ord > p^(1/3)={p**(1./3):.1f} ✓ (cube root regime)")
                else:
                    print(f"         ord < p^(1/3)={p**(1./3):.1f} ✗ (small order)")

    # Additional analysis: check ALL S values for passing k
    print()
    print("=" * 80)
    print("Checking S = S_min AND S_min + 1 for k with PASS at S_min")
    print("=" * 80)
    for k in passing[:5]:  # Just check first 5
        S_min = math.ceil(k * math.log2(3))
        for S in [S_min, S_min + 1]:
            d = 2**S - 3**k
            C = math.comb(S - 1, k - 1)
            factors = factorint(d)
            all_ok = True
            for p in factors:
                r = ord_mod(2, p)
                if r <= math.sqrt(p):
                    all_ok = False
                    break
            status = "✅" if all_ok else "❌"
            print(f"  k={k}, S={S}: d={d:,}, C/d={C/d:.4f} {status}")

if __name__ == "__main__":
    main()
