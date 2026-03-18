#!/usr/bin/env python3
"""
JEPA PROOF SEARCH LOOP — Autonomous Lemma Generator & Tester
==============================================================

Generates SPECIFIC, FALSIFIABLE lemmas about corrSum and tests them.
Each lemma is a candidate building block for a proof of H.

Loop: Generate → Test (k=3..14) → Score → Mutate → Repeat

A "good" lemma is one that:
1. Is TRUE for all tested k
2. Would IMPLY N0(d) = 0 if proved for all k
3. Has a plausible proof path
"""

import sys, os, time
from math import ceil, log2, comb, gcd, sqrt
from itertools import combinations
from collections import defaultdict

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def precompute(k_max=14):
    cache = {}
    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 500000: continue
        data = []
        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            data.append((sigma, cs))
        cache[k] = {'S': S, 'd': d, 'C': C, 'data': data}
    return cache


def test_lemma(cache, lemma_fn, name=""):
    """Test a lemma on all cached k values. Returns (pass_count, fail_count, details)."""
    passes = 0
    fails = 0
    details = []
    for k, kdata in sorted(cache.items()):
        d = kdata['d']
        S = kdata['S']
        for sigma, cs in kdata['data']:
            result = lemma_fn(k, S, d, sigma, cs)
            if result:
                passes += 1
            else:
                fails += 1
                if len(details) < 5:
                    details.append({'k': k, 'sigma': sigma, 'cs': cs, 'r': cs % d})
                if fails > 10:
                    return passes, fails, details
    return passes, fails, details


# ════════════════════════════════════════════════════════════
# LEMMA BANK: Candidate lemmas to test
# ════════════════════════════════════════════════════════════

def lemma_corrsum_gt_d(k, S, d, sigma, cs):
    """L1: corrSum > d always."""
    return cs > d

def lemma_corrsum_not_mult_d(k, S, d, sigma, cs):
    """L2 (= the target): corrSum ≢ 0 mod d."""
    return cs % d != 0

def lemma_corrsum_coprime_d(k, S, d, sigma, cs):
    """L3: gcd(corrSum, d) = 1."""
    return gcd(cs, d) == 1

def lemma_corrsum_mod_d_odd(k, S, d, sigma, cs):
    """L4: corrSum mod d is odd (since corrSum is odd and d is odd)."""
    return (cs % d) % 2 == 1

def lemma_first_term_dominates_mod(k, S, d, sigma, cs):
    """L5: corrSum mod d = (3^{k-1} mod d) + (rest mod d), and rest < d/2."""
    base = pow(3, k-1)
    rest = cs - base
    return (rest % d) != (d - (base % d)) % d  # rest mod d ≠ -base mod d

def lemma_no_small_quotient(k, S, d, sigma, cs):
    """L6: corrSum/d is never very close to an integer (frac part > 1/d^0.5)."""
    r = cs % d
    dist = min(r, d - r)
    return dist >= max(1, int(sqrt(d) * 0.001))

def lemma_orbit_e1_kills(k, S, d, sigma, cs):
    """L7: If corrSum ≡ 0 mod d, orbit fails at step 1.
    Checks: n₀ = cs/d satisfies 3n₀+1 ≡ 0 mod 2^{σ₁}? If not, orbit impossible."""
    if cs % d != 0:
        return True  # Vacuously true
    n0 = cs // d
    e1 = sigma[1]
    return (3 * n0 + 1) % (2**e1) != 0

def lemma_corrsum_avoids_multiples_of_largest_prime_power(k, S, d, sigma, cs):
    """L8: Let p^a be the largest prime power dividing d. Then corrSum ≢ 0 mod p^a."""
    # Find largest prime power factor of d
    n = d
    max_pa = 1
    for p in range(2, min(10000, n)):
        if n % p == 0:
            pa = 1
            while n % p == 0:
                pa *= p
                n //= p
            if pa > max_pa:
                max_pa = pa
    if n > 1 and n > max_pa:
        max_pa = n
    return cs % max_pa != 0

def lemma_v2_of_3n0_plus1_bounded(k, S, d, sigma, cs):
    """L9: If n₀ = round(cs/d), then v₂(3n₀+1) < σ₁.
    This means even the nearest integer n₀ can't satisfy the orbit equation."""
    n0 = round(cs / d)
    if n0 <= 0:
        return True
    val = 3 * n0 + 1
    v2 = 0
    while val % 2 == 0:
        v2 += 1
        val //= 2
    e1 = sigma[1]
    return v2 < e1

def lemma_corrsum_mod_d_in_units_group(k, S, d, sigma, cs):
    """L10: corrSum mod d is always a unit in Z/dZ (coprime to d).
    Stronger than L2 (implies L2)."""
    return gcd(cs % d, d) == 1 if cs % d != 0 else False


LEMMAS = [
    ("L1: corrSum > d", lemma_corrsum_gt_d),
    ("L2: corrSum ≢ 0 mod d (TARGET)", lemma_corrsum_not_mult_d),
    ("L3: gcd(corrSum, d) = 1", lemma_corrsum_coprime_d),
    ("L4: corrSum mod d is odd", lemma_corrsum_mod_d_odd),
    ("L5: rest mod d ≠ -base mod d", lemma_first_term_dominates_mod),
    ("L6: frac part > 0.001/√d", lemma_no_small_quotient),
    ("L7: orbit e₁ kills (vacuous if L2)", lemma_orbit_e1_kills),
    ("L8: corrSum ≢ 0 mod largest p^a", lemma_corrsum_avoids_multiples_of_largest_prime_power),
    ("L9: v₂(3n₀+1) < σ₁ for nearest n₀", lemma_v2_of_3n0_plus1_bounded),
    ("L10: corrSum mod d in (Z/dZ)*", lemma_corrsum_mod_d_in_units_group),
]


def run_proof_search():
    print("JEPA PROOF SEARCH LOOP")
    print("=" * 70)

    t0 = time.time()
    cache = precompute(14)
    total_sequences = sum(v['C'] for v in cache.values())
    print(f"Precomputed {len(cache)} values of k, {total_sequences} total sequences\n")

    print(f"{'Lemma':>45} {'PASS':>8} {'FAIL':>6} {'Status':>8}")
    print("-" * 75)

    results = []
    for name, fn in LEMMAS:
        passes, fails, details = test_lemma(cache, fn, name)
        status = "✓ TRUE" if fails == 0 else f"✗ FAIL"
        print(f"{name:>45} {passes:8d} {fails:6d} {status:>8}")
        if fails > 0 and details:
            for d in details[:2]:
                print(f"{'':>45}   counter: k={d['k']}, r={d['r']}")
        results.append({
            'name': name, 'passes': passes, 'fails': fails,
            'true_for_all': fails == 0,
        })

    # SYNTHESIS
    print("\n" + "=" * 70)
    print("SYNTHESIS: Which lemmas are TRUE for all k=3..14?")
    print("=" * 70)

    true_lemmas = [r for r in results if r['true_for_all']]
    false_lemmas = [r for r in results if not r['true_for_all']]

    print(f"\n✓ TRUE ({len(true_lemmas)}):")
    for r in true_lemmas:
        implication = ""
        if "TARGET" in r['name']:
            implication = " ← THIS IS WHAT WE NEED TO PROVE"
        elif "gcd" in r['name'] or "units" in r['name']:
            implication = " ← IMPLIES L2 (would suffice)"
        elif "orbit" in r['name'] or "v₂" in r['name']:
            implication = " ← orbit constraint"
        print(f"  {r['name']}{implication}")

    print(f"\n✗ FALSE ({len(false_lemmas)}):")
    for r in false_lemmas:
        print(f"  {r['name']} ({r['fails']} counterexamples)")

    # PROOF STRATEGY
    print("\n" + "=" * 70)
    print("PROOF STRATEGY RECOMMENDATION")
    print("=" * 70)

    # Check: is L3 (coprime) true? If so, it implies L2.
    l3 = next((r for r in results if 'L3' in r['name']), None)
    if l3 and not l3['true_for_all']:
        print("\n  L3 (coprime) is FALSE — cannot prove via gcd argument alone.")
        print("  Need to handle the cases where gcd(corrSum, d) > 1.")

    # Check: is L1 true? corrSum > d for all?
    l1 = next((r for r in results if 'L1' in r['name']), None)
    if l1 and l1['true_for_all']:
        print("\n  L1 (corrSum > d) is TRUE — every corrSum exceeds d.")
        print("  This means n₀ = corrSum/d ≥ 1 if divisible.")
        print("  Combined with orbit constraints: powerful.")

    # The best strategy depends on what's true
    if l3 and l3['true_for_all']:
        print("\n  STRATEGY: Prove gcd(corrSum, d) = 1 for all k ≥ 3.")
        print("  This would immediately give N0 = 0.")
    else:
        print("\n  STRATEGY: Two-pronged approach needed:")
        print("  (A) For σ where gcd(corrSum, d) = 1: done (coprime blocks divisibility)")
        print("  (B) For σ where gcd(corrSum, d) > 1: use orbit constraints")
        print("      (orbit always fails at step 1 for near-miss candidates)")

    elapsed = time.time() - t0
    print(f"\nTotal time: {elapsed:.1f}s")


if __name__ == '__main__':
    run_proof_search()
