#!/usr/bin/env python3
"""
R199 - Finite Verification for k = 18..41
Agent A1: Investigateur Computationnel

For each k, compute:
- S = ceil(k * log2(3))
- d(k) = 2^S - 3^k
- {k * theta} where theta = log2(3)
- Complete factorization of d(k)
- C(k) = C(S-1, k-1) (binomial coefficient)
- For each prime p | d(k): ord_p(2), check if p > C(k)
- Classification: RESOLVED / PARTIALLY RESOLVED / OPEN
"""

import math
from math import comb, gcd, log2
from sympy import factorint, isprime, nextprime, Rational
from sympy.ntheory import n_order
from mpmath import mp, mpf, log as mplog, ceil as mpceil, floor as mpfloor, frac as mpfrac

# High precision for fractional parts
mp.dps = 50

# theta = log2(3) with high precision
theta = mplog(3) / mplog(2)
LOG2_5_3 = mplog(mpf(5)/mpf(3)) / mplog(2)  # log2(5/3) ~ 0.73697...

print(f"theta = log2(3) = {theta}")
print(f"log2(5/3) = {LOG2_5_3}")
print(f"Arc threshold: {{k*theta}} > {float(LOG2_5_3):.6f}")
print()

# Mersenne primes for reference
mersenne_exponents = [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127]
mersenne_primes = set(2**p - 1 for p in mersenne_exponents)

results = []

for k in range(18, 42):
    print(f"{'='*80}")
    print(f"k = {k}")
    print(f"{'='*80}")

    # S = ceil(k * log2(3))
    k_theta = k * theta
    S = int(mpceil(k_theta))
    frac_part = float(k_theta - mpfloor(k_theta))

    print(f"  S = ceil({k} * log2(3)) = {S}")
    print(f"  {{k*theta}} = {frac_part:.10f}")
    print(f"  Arc threshold = {float(LOG2_5_3):.10f}")

    arc_works = frac_part > float(LOG2_5_3)
    print(f"  Arc argument applies: {arc_works}")

    # d(k) = 2^S - 3^k
    d = 2**S - 3**k
    print(f"  d({k}) = 2^{S} - 3^{k} = {d}")
    print(f"  d({k}) has {len(str(abs(d)))} digits")

    if d <= 0:
        print(f"  WARNING: d(k) <= 0, this means 2^S < 3^k")
        results.append({
            'k': k, 'S': S, 'd': d, 'frac': frac_part,
            'arc': arc_works, 'status': 'INVALID (d<=0)',
            'factors': {}, 'C_k': 0
        })
        continue

    # Factorize d(k)
    print(f"  Factorizing d({k})...")
    factors = factorint(d)
    print(f"  d({k}) = ", end="")
    factor_strs = []
    for p, e in sorted(factors.items()):
        if e == 1:
            factor_strs.append(f"{p}")
        else:
            factor_strs.append(f"{p}^{e}")
    print(" * ".join(factor_strs))

    # Check Mersenne primes
    for p in factors:
        if p in mersenne_primes:
            exp = [e for e in mersenne_exponents if 2**e - 1 == p][0]
            print(f"  *** Mersenne prime M_{exp} = {p} divides d({k})! ***")

    # C(k) = C(S-1, k-1)
    C_k = comb(S - 1, k - 1)
    print(f"  C({k}) = C({S-1}, {k-1}) = {C_k}")
    print(f"  C({k}) has {len(str(C_k))} digits")

    # For each prime factor, compute ord_p(2) and check p > C(k)
    print(f"\n  Prime factor analysis:")
    prime_analysis = {}
    any_prime_exceeds_C = False

    for p in sorted(factors.keys()):
        e = factors[p]
        exceeds_C = p > C_k

        # Compute ord_p(2)
        if p == 2:
            ord_p = None
            print(f"    p = 2 (e={e}): ord_p(2) = N/A (p=2)")
            prime_analysis[p] = {'e': e, 'ord': None, 'exceeds_C': exceeds_C}
            continue

        try:
            ord_p = n_order(2, p)
        except Exception as ex:
            ord_p = -1
            print(f"    p = {p}: ord computation failed: {ex}")

        # Check if S | ord_p(2) — relevant because 2^S ≡ 3^k (mod p)
        divides_S = (ord_p > 0 and S % ord_p == 0)

        print(f"    p = {p} (e={e}): ord_p(2) = {ord_p}, p > C(k)? {exceeds_C}", end="")
        if exceeds_C:
            print(" [PIGEONHOLE WORKS]", end="")
            any_prime_exceeds_C = True
        if divides_S:
            print(f" [ord | S]", end="")
        print()

        prime_analysis[p] = {
            'e': e, 'ord': ord_p, 'exceeds_C': exceeds_C,
            'divides_S': divides_S
        }

    # Classification
    if arc_works:
        status = "RESOLVED (arc argument)"
    elif any_prime_exceeds_C:
        # Find which prime(s) exceed C(k)
        big_primes = [p for p, info in prime_analysis.items() if info.get('exceeds_C')]
        status = f"RESOLVED (CRT pigeonhole via p={big_primes})"
    else:
        # Check: can we still resolve via CRT with structural arguments?
        max_prime = max(factors.keys()) if factors else 0
        status = f"OPEN (max prime {max_prime} < C(k)={C_k})"

    print(f"\n  STATUS: {status}")

    results.append({
        'k': k, 'S': S, 'd': d, 'frac': frac_part,
        'arc': arc_works, 'status': status,
        'factors': factors, 'C_k': C_k,
        'prime_analysis': prime_analysis
    })
    print()

# Summary
print("\n" + "="*80)
print("SUMMARY TABLE")
print("="*80)
print(f"{'k':>3} {'S':>4} {'frac':>12} {'arc':>5} {'#digits(d)':>10} {'#primes':>8} {'max_p':>15} {'C(k)':>20} {'status'}")
print("-"*120)

resolved_count = 0
open_count = 0
arc_count = 0
crt_count = 0

for r in results:
    k = r['k']
    S = r['S']
    frac = r['frac']
    arc = r['arc']
    d = r['d']
    ndigits = len(str(abs(d)))
    nprimes = len(r['factors'])
    max_p = max(r['factors'].keys()) if r['factors'] else 0
    C_k = r['C_k']
    status = r['status']

    if 'RESOLVED' in status:
        resolved_count += 1
        if 'arc' in status:
            arc_count += 1
        else:
            crt_count += 1
    else:
        open_count += 1

    print(f"{k:>3} {S:>4} {frac:>12.8f} {str(arc):>5} {ndigits:>10} {nprimes:>8} {max_p:>15} {str(C_k)[:20]:>20} {status}")

print()
print(f"RESOLVED: {resolved_count} (arc: {arc_count}, CRT: {crt_count})")
print(f"OPEN: {open_count}")
print()

# Detailed analysis of OPEN cases
print("="*80)
print("DETAILED ANALYSIS OF OPEN CASES")
print("="*80)
for r in results:
    if 'OPEN' in r['status']:
        k = r['k']
        print(f"\nk = {k}: d = {r['d']}")
        print(f"  Factorization: ", end="")
        for p, e in sorted(r['factors'].items()):
            print(f"{p}^{e} " if e > 1 else f"{p} ", end="")
        print()
        print(f"  C(k) = {r['C_k']}")
        print(f"  {{k*theta}} = {r['frac']:.10f} (need > {float(LOG2_5_3):.10f} for arc)")
        print(f"  Gap to arc threshold: {r['frac'] - float(LOG2_5_3):.10f}")

        # For each prime, show ratio p/C(k)
        for p, info in sorted(r.get('prime_analysis', {}).items()):
            if p == 2:
                continue
            ratio = p / r['C_k'] if r['C_k'] > 0 else float('inf')
            print(f"  p={p}: ord_2={info.get('ord', '?')}, p/C(k)={ratio:.6e}")

# Additional: rho_p analysis
print("\n" + "="*80)
print("rho_p ANALYSIS (for reference, NOT sufficient alone)")
print("="*80)
print("Note: rho_p = #{x in Z/pZ : sum of C(S-1,k-1) terms = 0} / p")
print("rho_p < 1 does NOT imply N_0(p) = 0 when p < C(k)")
print()

for r in results:
    if 'OPEN' in r['status']:
        k = r['k']
        S = r['S']
        print(f"k={k}, S={S}:")
        for p, info in sorted(r.get('prime_analysis', {}).items()):
            if p == 2:
                continue
            ord_p = info.get('ord', 0)
            if ord_p and ord_p > 0:
                # rho_p depends on structure of the polynomial mod p
                # Simple bound: if ord_p(2) = o, then the polynomial has degree <= C(k)
                # and at most C(k) roots mod p
                # So rho_p <= min(1, C(k)/p)
                rho_bound = min(1.0, r['C_k'] / p)
                print(f"  p={p}: ord={ord_p}, rho_p <= min(1, C(k)/p) = {rho_bound:.6f}")

# Generate the full data for the report
print("\n" + "="*80)
print("COMPLETE FACTORIZATIONS")
print("="*80)
for r in results:
    k = r['k']
    S = r['S']
    d = r['d']
    factors = r['factors']
    factor_str = " * ".join(
        f"{p}^{e}" if e > 1 else str(p)
        for p, e in sorted(factors.items())
    )
    print(f"k={k}: d = 2^{S} - 3^{k} = {factor_str}")
