#!/usr/bin/env python3
"""
PARADIGM 5: Self-Referential System — Deep Exploration
========================================================

Key insight: A k-cycle gives not 1 but k Steiner equations (one per starting element).
The cyclic shifts create an OVERDETERMINED system.
Combined with C < d, this might be enough to prove no solution exists.

The system:
  n_0 · d = corrSum(σ^{(0)})     starting from n_0
  n_1 · d = corrSum(σ^{(1)})     starting from n_1
  ...
  n_{k-1} · d = corrSum(σ^{(k-1)})  starting from n_{k-1}

where σ^{(i)} is the cyclic shift of the cumulative exponent sequence.
"""

from itertools import combinations
from math import ceil, log2, comb
from collections import defaultdict
import json

def S_of_k(k): return ceil(k * log2(3))
def d_of_k(k): return 2**S_of_k(k) - 3**k

def corrsum_cum(sigma, k):
    return sum(pow(3, k-1-i) * pow(2, sigma[i]) for i in range(k))


def cyclic_shift_cumulative(sigma, S):
    """
    Given cumulative exponents σ = (0, σ_1, ..., σ_{k-1}) with individual
    exponents e_i = σ_i - σ_{i-1} (and e_k = S - σ_{k-1}),
    compute the cumulative sequence starting from n_1 instead of n_0.

    If individual exponents are (e_1, e_2, ..., e_k), cycling gives
    (e_2, e_3, ..., e_k, e_1). The new cumulative sequence is
    (0, e_2, e_2+e_3, ..., e_2+...+e_k, S) but we need σ_{k-1} < S,
    so the new σ' = (0, e_2, e_2+e_3, ..., e_2+...+e_k).
    """
    k = len(sigma)
    # Individual exponents
    indiv = [sigma[i] - sigma[i-1] for i in range(1, k)]
    indiv.append(S - sigma[-1])  # last individual exponent e_k

    # Cyclic shift: (e_2, e_3, ..., e_k, e_1)
    shifted_indiv = indiv[1:] + [indiv[0]]

    # New cumulative sequence
    new_sigma = [0]
    cumsum = 0
    for e in shifted_indiv[:-1]:  # k-1 cumulative positions
        cumsum += e
        new_sigma.append(cumsum)

    return tuple(new_sigma)


def all_cyclic_shifts(sigma, S):
    """Generate all k cyclic shifts of a cumulative sequence."""
    shifts = [sigma]
    current = sigma
    k = len(sigma)
    for _ in range(k - 1):
        current = cyclic_shift_cumulative(current, S)
        shifts.append(current)
    return shifts


def analyze_self_referential(k):
    """
    For each cumulative sequence σ, compute the k cyclic shifts and
    check if ALL give corrSum ≡ 0 mod d simultaneously.

    This is the FULL cycle constraint, not just one equation.
    """
    S = S_of_k(k)
    d = d_of_k(k)
    if d <= 0:
        return None

    C = count_cumulative(k, S)
    if C > 200000:
        return {'k': k, 'status': 'too_large', 'C': C}

    results = {
        'k': k, 'S': S, 'd': d, 'C': C,
        'single_hits': 0,       # corrSum ≡ 0 mod d (single equation)
        'all_shifts_hit': 0,    # ALL k shifts give ≡ 0 mod d
        'partial_hits': defaultdict(int),  # how many shifts give ≡ 0
    }

    for sigma in enumerate_cum(k, S):
        # Single equation check
        cs0 = corrsum_cum(sigma, k) % d
        if cs0 == 0:
            results['single_hits'] += 1

            # Check all cyclic shifts
            shifts = all_cyclic_shifts(sigma, S)
            n_zero = sum(1 for s in shifts if corrsum_cum(s, k) % d == 0)
            results['partial_hits'][n_zero] += 1

            if n_zero == k:
                results['all_shifts_hit'] += 1
                results['cycle_sigma'] = list(sigma)

    return results


def count_cumulative(k, S):
    return comb(S-1, k-1)

def enumerate_cum(k, S):
    for combo in combinations(range(1, S), k-1):
        yield (0,) + combo


def main():
    print("SELF-REFERENTIAL SYSTEM ANALYSIS")
    print("=" * 60)
    print("Question: If we require ALL k cyclic shifts to give corrSum ≡ 0,")
    print("how many candidates survive?")
    print()

    print(f"{'k':>3} {'C':>9} {'single_hits':>12} {'all_k_shifts':>13}")
    print("-" * 45)

    for k in range(3, 15):
        S = S_of_k(k)
        d = d_of_k(k)
        if d <= 0: continue
        C = count_cumulative(k, S)
        if C > 200000:
            print(f"{k:3d} {C:9d}  (too large)")
            continue

        r = analyze_self_referential(k)
        if r and 'single_hits' in r:
            print(f"{k:3d} {C:9d} {r['single_hits']:12d} {r['all_shifts_hit']:13d}")
            if r['partial_hits']:
                for n_hits, count in sorted(r['partial_hits'].items()):
                    print(f"     {count} sequences have {n_hits}/{k} shifts hitting 0")
        else:
            print(f"{k:3d} {C:9d}  (skipped)")

    print()
    print("KEY: For a real cycle, ALL k shifts must give corrSum ≡ 0 mod d.")
    print("If single_hits = 0, the self-referential check is moot.")
    print("If single_hits > 0 but all_k_shifts = 0, the OVERDETERMINED")
    print("system eliminates all candidates — this is the paradigm's power.")


if __name__ == '__main__':
    main()
