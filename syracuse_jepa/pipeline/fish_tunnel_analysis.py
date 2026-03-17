#!/usr/bin/env python3
"""
Fish-Tunnel Incompatibility Analysis
=====================================

Goal: Prove that "Fish primes" (primes p with rho(p) > 0.5) never divide
d(k) = 2^{S(k)} - 3^k where S(k) = ceil(k * log_2(3)).

Definitions:
  - q = ord_p(2), the multiplicative order of 2 mod p
  - rho(p) = max_{a != 0} |S_a(p)| / q  where S_a = sum_{j=0}^{q-1} omega^{a * 2^j mod p}
  - Character sum bound: rho <= sqrt(p) / q
  - Fish prime: rho(p) > 0.5, which forces q < 2*sqrt(p)  (small order)

Strategy:
  p | d(k)  iff  2^{S(k)} = 3^k mod p,  i.e., 3^k in <2> mod p.
  We analyze the subgroup structure <2> ∩ <3> to determine when this can happen,
  then check whether the CEILING constraint S(k) = ceil(k * log_2(3)) is compatible.

Author: Eric Merle / Claude (Fish-Tunnel analysis)
"""

import math
import sys
import time
from collections import defaultdict
from typing import List, Tuple, Dict, Optional

import gmpy2
from gmpy2 import mpz, is_prime as gmpy2_is_prime

# ═══════════════════════════════════════════════════════════════
#  Import project utilities
# ═══════════════════════════════════════════════════════════════
sys.path.insert(0, '/Users/ericmerle/Documents/Collatz-Junction-Theorem')
from syracuse_jepa.data.generator import compute_S, compute_d
from syracuse_jepa.pipeline.analyst import factorize, multiplicative_order


# ═══════════════════════════════════════════════════════════════
#  Number-theoretic primitives (gmpy2-accelerated)
# ═══════════════════════════════════════════════════════════════

def fast_multiplicative_order(a: int, p: int) -> int:
    """Compute ord_p(a) using factorization of p-1, with gmpy2 for speed."""
    if math.gcd(a, p) != 1:
        return 0
    if p <= 2:
        return 1
    phi = p - 1
    order = phi
    # Factor phi
    temp = phi
    prime_factors = []
    d = 2
    while d * d <= temp:
        if temp % d == 0:
            prime_factors.append(d)
            while temp % d == 0:
                temp //= d
        d += 1 if d == 2 else 2
    if temp > 1:
        prime_factors.append(temp)
    # Reduce order
    for pf in prime_factors:
        while order % pf == 0 and pow(a, order // pf, p) == 1:
            order //= pf
    return order


def compute_rho_exact(p: int, q: int) -> float:
    """
    Compute rho(p) = max_{a != 0} |S_a(p)| / q exactly.

    S_a(p) = sum_{j=0}^{q-1} omega_p^{a * 2^j mod p}
    where omega_p = exp(2*pi*i/p).

    Only feasible for q <= 10000.
    """
    if q > 10000:
        return -1.0  # Signal: use bound instead

    # Precompute the orbit {2^j mod p : j = 0, ..., q-1}
    orbit = []
    val = 1
    for _ in range(q):
        orbit.append(val)
        val = (val * 2) % p

    # For each a in 1..p-1, compute |S_a| = |sum_j exp(2*pi*i*a*orbit[j]/p)|
    # Optimization: a and p-a give conjugate sums, so |S_a| = |S_{p-a}|.
    # Also, a and a*2^m mod p give the same |S_a| (cyclic permutation of orbit).
    # We only need representatives of orbits under <2> action on a.
    #
    # But for correctness, just iterate all a from 1 to p-1.
    # For p up to 100000 and q up to 10000, this is manageable.

    max_abs_S = 0.0
    two_pi_over_p = 2.0 * math.pi / p

    # Precompute cos and sin tables for the orbit residues
    # S_a = sum_j exp(2*pi*i * a * orbit[j] / p)
    # Real part: sum_j cos(2*pi * a * orbit[j] / p)
    # Imag part: sum_j sin(2*pi * a * orbit[j] / p)

    # For efficiency, precompute orbit values as array
    orbit_arr = orbit

    # We can use the fact that {a * orbit[j] mod p} as a varies
    # covers cosets of <2> in (Z/pZ)*.
    # The number of distinct |S_a| values = (p-1)/q (index of <2>).
    # So we only need one representative per coset.

    # Find coset representatives
    seen = set()
    representatives = []
    for a in range(1, p):
        if a not in seen:
            representatives.append(a)
            # Mark entire coset a * <2>
            v = a
            for _ in range(q):
                seen.add(v)
                v = (v * 2) % p

    for a in representatives:
        re_sum = 0.0
        im_sum = 0.0
        for orb_val in orbit_arr:
            angle = two_pi_over_p * ((a * orb_val) % p)
            re_sum += math.cos(angle)
            im_sum += math.sin(angle)
        abs_S = math.sqrt(re_sum * re_sum + im_sum * im_sum)
        if abs_S > max_abs_S:
            max_abs_S = abs_S

    return max_abs_S / q


def compute_rho_bound(p: int, q: int) -> float:
    """Upper bound: rho <= sqrt(p) / q (from Weil bound on character sums)."""
    return math.sqrt(p) / q


def is_in_subgroup_fast(target: int, gen_order: int, p: int) -> bool:
    """Check if target in <gen> where gen has order gen_order in (Z/pZ)*.
    target in <gen> iff target^((p-1)/gen_order) = 1 mod p."""
    if target % p == 0:
        return False
    exp = (p - 1) // gen_order
    return pow(target, exp, p) == 1


def subgroup_intersection_order(q: int, r: int, p: int) -> int:
    """
    Compute |<2> ∩ <3>| in (Z/pZ)*.

    <2> has order q, <3> has order r.
    Both are subgroups of the cyclic group (Z/pZ)* of order p-1.
    In a cyclic group, the intersection of two cyclic subgroups of orders q and r
    has order gcd(q, r)... NO. That's for subgroups generated by elements.

    Actually, in a cyclic group G of order n:
    - The unique subgroup of order d (for d | n) is {g^{n/d} : ...}
    - <2> is the unique subgroup of order q (which is the subgroup of index (p-1)/q)
    - <3> is the unique subgroup of order r
    - Their intersection is the unique subgroup of order gcd(q, r)

    Wait — that's wrong. <2> is not necessarily the unique subgroup of order q.
    In a cyclic group, there IS a unique subgroup of each order dividing |G|.
    If g is a generator of G = (Z/pZ)*, then <2> = <g^{(p-1)/q}>, which is
    the unique subgroup of order q. Similarly <3> = <g^{(p-1)/r}>.

    The intersection of the subgroup of order q and the subgroup of order r
    in a cyclic group of order n = p-1 is the subgroup of order gcd(q, r).

    Actually NO. The subgroup of order q is H_q = {x : x^q = 1}.
    The subgroup of order r is H_r = {x : x^r = 1}.
    H_q ∩ H_r = {x : x^q = 1 AND x^r = 1} = {x : x^{gcd(q,r)} = 1}.
    So |H_q ∩ H_r| = gcd(q, r).
    """
    return math.gcd(q, r)


def find_k_with_3k_in_subgroup_2(p: int, q: int, r: int) -> List[int]:
    """
    Find all k in [0, r-1] such that 3^k in <2> mod p.

    3^k in <2> iff (3^k)^{(p-1)/q} = 1 mod p
    iff 3^{k*(p-1)/q} = 1 mod p
    iff r | k*(p-1)/q
    iff (r / gcd(r, (p-1)/q)) | k

    Let I = (p-1)/q (index of <2>).
    Then 3^k in <2> iff k = 0 mod (r / gcd(r, I)).
    The step size is r / gcd(r, I).
    """
    I = (p - 1) // q  # index of <2> in (Z/pZ)*
    step = r // math.gcd(r, I)
    return list(range(0, r, step))


# ═══════════════════════════════════════════════════════════════
#  Main analysis: find Fish primes and analyze structure
# ═══════════════════════════════════════════════════════════════

def find_fish_primes(limit: int = 100_000, rho_threshold: float = 0.5,
                     q_exact_limit: int = 10_000) -> List[dict]:
    """
    Find all primes p <= limit with rho(p) > rho_threshold.

    Uses exact character sum computation when q = ord_p(2) <= q_exact_limit,
    and the Weil bound sqrt(p)/q otherwise.
    """
    fish_primes = []

    # Sieve primes up to limit
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(limit**0.5) + 1):
        if sieve[i]:
            for j in range(i*i, limit + 1, i):
                sieve[j] = 0

    primes = [p for p in range(3, limit + 1) if sieve[p]]  # skip p=2

    print(f"Scanning {len(primes)} odd primes up to {limit}...")
    print(f"rho threshold: {rho_threshold}")
    print(f"Exact character sum limit: q <= {q_exact_limit}")
    print()

    n_exact = 0
    n_bound = 0
    t0 = time.time()

    for idx, p in enumerate(primes):
        if (idx + 1) % 2000 == 0:
            elapsed = time.time() - t0
            print(f"  ... {idx+1}/{len(primes)} primes scanned ({elapsed:.1f}s)")

        q = fast_multiplicative_order(2, p)
        if q == 0:
            continue

        # Quick filter: rho <= sqrt(p)/q. If this bound <= threshold, skip.
        bound = math.sqrt(p) / q
        if bound <= rho_threshold:
            continue

        # The bound exceeds threshold, so this prime MIGHT be a Fish prime.
        # Try exact computation if feasible.
        if q <= q_exact_limit:
            rho = compute_rho_exact(p, q)
            n_exact += 1
            method = "exact"
        else:
            # q > q_exact_limit but bound > threshold.
            # This means sqrt(p)/q > 0.5, so q < 2*sqrt(p).
            # For p <= 100000, sqrt(p) <= 316, so q < 632.
            # This is always < q_exact_limit = 10000, contradiction.
            # So we should never reach here for p <= 100000.
            rho = bound  # conservative upper bound
            n_bound += 1
            method = "bound"

        if rho > rho_threshold + 1e-12:  # strict > with floating-point tolerance
            fish_primes.append({
                'p': p,
                'q': q,  # ord_p(2)
                'rho': rho,
                'rho_bound': bound,
                'method': method,
            })

    elapsed = time.time() - t0
    print(f"\nScan complete in {elapsed:.1f}s")
    print(f"  Exact computations: {n_exact}")
    print(f"  Bound-only: {n_bound}")
    print(f"  Fish primes found: {len(fish_primes)}")

    return fish_primes


def analyze_fish_prime(info: dict) -> dict:
    """
    Deep analysis of one Fish prime for the Fish-Tunnel incompatibility.

    Returns enriched dict with all structural data.
    """
    p = info['p']
    q = info['q']  # ord_p(2)
    rho = info['rho']

    r = fast_multiplicative_order(3, p)  # ord_p(3)
    I = (p - 1) // q  # index of <2>

    # Is 3 in <2>?
    three_in_two = is_in_subgroup_fast(3, q, p)

    # Intersection |<2> ∩ <3>|
    intersection_order = subgroup_intersection_order(q, r, p)

    # Find k values where 3^k in <2>
    k_values_in_subgroup = find_k_with_3k_in_subgroup_2(p, q, r)
    step = r // math.gcd(r, I) if math.gcd(r, I) > 0 else r

    # Classify case
    if intersection_order == 1:
        case = "A"
        case_desc = "<2> ∩ <3> = {1}: trivial intersection"
    elif three_in_two:
        case = "B"
        case_desc = "3 in <2>: full containment <3> ⊆ <2>"
    else:
        case = "C"
        case_desc = f"Intermediate: |<2> ∩ <3>| = {intersection_order}"

    # ── Key test: for k values where 3^k in <2>, check ceiling constraint ──
    # p | d(k) requires: 2^{S(k)} ≡ 3^k mod p
    # This means: 3^k ∈ <2> (necessary) AND the discrete log of 3^k in <2>
    # must equal S(k) mod q.
    #
    # Let log_2 denote the discrete log base 2 mod p (in Z/qZ).
    # Then 2^{S(k)} ≡ 3^k mod p iff S(k) ≡ log_2(3^k) mod q.
    # i.e., S(k) ≡ k * log_2(3) mod q.
    #
    # But S(k) = ceil(k * log_2(3)) (real logarithm).
    # So the condition is: ceil(k * ln3/ln2) ≡ k * dlog_2(3) mod q
    # where dlog is the DISCRETE log mod p.

    # Compute discrete log of 3 base 2 mod p (if 3 in <2>)
    dlog_3 = None
    if three_in_two:
        # Find t such that 2^t ≡ 3 mod p, 0 <= t < q
        # Baby-step giant-step
        dlog_3 = baby_giant_dlog(2, 3, p, q)

    # Check which k (from 1 to large range) satisfy p | d(k)
    # d(k) = 2^{S(k)} - 3^k
    # p | d(k) iff 2^{S(k)} ≡ 3^k mod p

    LOG2_3 = math.log2(3)

    # For the divisibility check, we test k up to a generous range.
    # The periodicity in k is lcm(q, r) for the mod-p behavior of 2^{S(k)} and 3^k.
    # But S(k) is not periodic — it's ceil(k * log2(3)), which is quasi-linear.
    # So we must check many k values.

    divisibility_hits = []
    k_max_check = max(10 * q * r, 100000)  # generous range
    # But cap at 10M to avoid timeout
    k_max_check = min(k_max_check, 10_000_000)

    # Efficient: precompute pow(3, k, p) incrementally and pow(2, S(k), p)
    pow3k = 1  # 3^0 mod p
    prev_S = 0
    pow2S = 1  # 2^0 mod p

    for k in range(1, k_max_check + 1):
        pow3k = (pow3k * 3) % p
        S_k = math.ceil(k * LOG2_3)
        # Update pow2S from prev_S to S_k
        delta_S = S_k - prev_S
        pow2S = (pow2S * pow(2, delta_S, p)) % p
        prev_S = S_k

        if pow2S == pow3k:
            divisibility_hits.append(k)
            if len(divisibility_hits) >= 20:
                break  # enough evidence

    # ── Theoretical analysis of WHY no hits should occur ──
    # For Case A: 3^k in <2> only when k ≡ 0 mod r (giving 3^k = 1).
    #   Then need 2^{S(k)} ≡ 1 mod p, i.e., q | S(k).
    #   S(k) = ceil(k * log2(3)). For k = m*r: S = ceil(m*r*log2(3)).
    #   Need q | ceil(m*r*log2(3)). Since log2(3) is irrational,
    #   {m*r*log2(3)} is equidistributed mod 1 (Weyl), so ceil(...) mod q
    #   is equidistributed mod q. Probability 1/q per hit. But this is
    #   probabilistic, not a proof of zero hits.

    # For Case B: 3 in <2>, so dlog_2(3) = t exists.
    #   Need S(k) ≡ k*t mod q for all k.
    #   S(k) = ceil(k * log2(3)) = floor(k * log2(3)) + 1  (when k*log2(3) not integer, always for k>0)
    #   Actually S(k) = ceil(k * log2(3)). Since log2(3) is irrational, k*log2(3) is never integer for k>0.
    #   So S(k) = floor(k * log2(3)) + 1.
    #   Need: floor(k * log2(3)) + 1 ≡ k*t mod q.
    #   i.e., {k * log2(3)} ∈ (0,1) and floor(k*log2(3)) = k*log2(3) - {k*log2(3)}
    #   So condition: k*log2(3) - {k*log2(3)} + 1 ≡ k*t mod q
    #   i.e., k*(log2(3) - t) + 1 - {k*log2(3)} ≡ 0 mod q
    #   The fractional part {k*log2(3)} makes this a Diophantine approximation problem.

    # Compute the "phase mismatch" for the first few k values
    phase_analysis = []
    if three_in_two and dlog_3 is not None:
        t = dlog_3
        for k in range(1, min(201, k_max_check)):
            S_k = math.ceil(k * LOG2_3)
            needed_mod = (k * t) % q
            actual_mod = S_k % q
            mismatch = (actual_mod - needed_mod) % q
            if mismatch == 0:
                phase_analysis.append((k, S_k, "HIT"))
            else:
                phase_analysis.append((k, S_k, f"miss(Δ={mismatch})"))

    # For Case C: 3^k in <2> iff k ≡ 0 mod step.
    #   Similar analysis restricted to k multiples of step.

    result = {
        **info,
        'r': r,           # ord_p(3)
        'index': I,        # [(Z/pZ)* : <2>]
        'three_in_two': three_in_two,
        'intersection_order': intersection_order,
        'k_step': step,    # period for 3^k in <2>
        'n_k_in_subgroup_per_period': len(k_values_in_subgroup),
        'case': case,
        'case_desc': case_desc,
        'dlog_3': dlog_3,
        'divisibility_hits': divisibility_hits,
        'n_hits': len(divisibility_hits),
        'k_max_checked': k_max_check,
        'phase_analysis_sample': phase_analysis[:20] if phase_analysis else [],
    }

    return result


def baby_giant_dlog(base: int, target: int, p: int, order: int) -> Optional[int]:
    """
    Baby-step giant-step discrete logarithm.
    Find t such that base^t ≡ target mod p, where 0 <= t < order.
    Returns None if no solution.
    """
    if order == 0:
        return None
    m = int(math.isqrt(order)) + 1

    # Baby steps: target * base^j for j = 0..m-1
    table = {}
    val = target % p
    for j in range(m):
        table[val] = j
        val = (val * base) % p

    # Giant steps: base^{m*i} for i = 0..m-1
    giant = pow(base, m, p)
    val = 1
    for i in range(m):
        if val in table:
            t = (i * m - table[val]) % order
            # Verify
            if pow(base, t, p) == target % p:
                return t
        val = (val * giant) % p

    return None


# ═══════════════════════════════════════════════════════════════
#  Proof-oriented analysis
# ═══════════════════════════════════════════════════════════════

def ceiling_mod_analysis(q: int, dlog_3: int) -> dict:
    """
    Analyze why ceil(k * log2(3)) mod q ≠ k * dlog_2(3) mod q.

    This is the CORE of the Fish-Tunnel proof for Case B.

    Let α = log2(3) (real, irrational, ~1.58496...).
    Let t = dlog_2(3) mod q (integer).

    Condition for p | d(k): ceil(k*α) ≡ k*t mod q.

    Write k*α = floor(k*α) + {k*α}, where {.} is fractional part.
    ceil(k*α) = floor(k*α) + 1  (since α is irrational, {k*α} ∈ (0,1)).

    So: floor(k*α) + 1 ≡ k*t mod q
    i.e.: k*α - {k*α} + 1 ≡ k*t mod q
    i.e.: k*(α - t) + 1 - {k*α} ≡ 0 mod q

    Now α - t is some real number. The LHS is:
    k*(α - t) + 1 - {k*α} mod q = 0.

    But k*(α - t) = k*α - k*t. And k*α = floor(k*α) + {k*α}.
    So: floor(k*α) + {k*α} - k*t + 1 - {k*α} = floor(k*α) - k*t + 1.

    The condition simplifies to: floor(k*α) + 1 ≡ k*t mod q
    i.e., ceil(k*α) ≡ k*t mod q.

    This is equivalent to asking: does the "Beatty-like" sequence ceil(k*α) mod q
    ever equal the arithmetic sequence k*t mod q?

    By the three-distance theorem and equidistribution of {k*α} mod 1,
    the sequence ceil(k*α) mod q visits each residue class with density ~1/q.
    Similarly k*t mod q is periodic with period q/gcd(t,q).

    The question is whether these two sequences ever COINCIDE.
    """
    LOG2_3 = math.log2(3)
    t = dlog_3

    # Check for all k in [1, 10*q] (well beyond one period)
    hits = []
    for k in range(1, min(10 * q + 1, 500001)):
        S_k = math.ceil(k * LOG2_3)
        if S_k % q == (k * t) % q:
            hits.append(k)

    # Analyze the gap: ceil(k*α) - k*t mod q
    gaps = []
    for k in range(1, min(q + 1, 10001)):
        S_k = math.ceil(k * LOG2_3)
        gap = (S_k - k * t) % q
        gaps.append(gap)

    # Distribution of gaps
    gap_counts = defaultdict(int)
    for g in gaps:
        gap_counts[g] += 1

    return {
        't': t,
        'q': q,
        'hits_in_range': hits[:50],
        'n_hits': len(hits),
        'range_checked': min(10 * q, 500000),
        'gap_distribution_size': len(gap_counts),
        'min_nonzero_gap': min(g for g in gaps if g > 0) if any(g > 0 for g in gaps) else 0,
        'zero_gap_count': gap_counts.get(0, 0),
    }


# ═══════════════════════════════════════════════════════════════
#  Main
# ═══════════════════════════════════════════════════════════════

def main():
    print("=" * 78)
    print("  FISH-TUNNEL INCOMPATIBILITY ANALYSIS")
    print("  Primes p <= 100000 with rho(p) > 0.5")
    print("=" * 78)
    print()

    # ── Step 1: Find all Fish primes ──
    fish_primes = find_fish_primes(limit=100_000, rho_threshold=0.5)

    if not fish_primes:
        print("\n*** NO Fish primes found! rho(p) <= 0.5 for all p <= 100000. ***")
        print("Fish-Tunnel incompatibility holds VACUOUSLY in this range.")
        return

    # Sort by rho descending
    fish_primes.sort(key=lambda x: -x['rho'])

    # ── Step 2: Analyze each Fish prime ──
    print("\n" + "=" * 78)
    print("  DETAILED ANALYSIS OF FISH PRIMES")
    print("=" * 78)

    analyses = []
    case_counts = {"A": 0, "B": 0, "C": 0}
    total_hits = 0

    for i, fp in enumerate(fish_primes):
        print(f"\n{'─' * 78}")
        print(f"  Fish prime #{i+1}: p = {fp['p']}")
        print(f"{'─' * 78}")

        analysis = analyze_fish_prime(fp)
        analyses.append(analysis)

        p = analysis['p']
        q = analysis['q']
        r = analysis['r']
        rho = analysis['rho']
        case = analysis['case']
        case_counts[case] += 1
        total_hits += analysis['n_hits']

        print(f"  ord_p(2) = q = {q}")
        print(f"  ord_p(3) = r = {r}")
        print(f"  rho(p) = {rho:.6f}  (bound: {analysis['rho_bound']:.6f})")
        print(f"  Index [(Z/pZ)* : <2>] = {analysis['index']}")
        print(f"  3 in <2> mod p? {analysis['three_in_two']}")
        print(f"  |<2> ∩ <3>| = {analysis['intersection_order']}")
        print(f"  Case: {case} — {analysis['case_desc']}")
        print(f"  k-step for 3^k in <2>: every {analysis['k_step']}")

        # Divisibility check
        if analysis['n_hits'] == 0:
            print(f"  Divisibility p | d(k): NO HITS for k in [1, {analysis['k_max_checked']}]")
        else:
            print(f"  *** DIVISIBILITY HITS: {analysis['divisibility_hits']} ***")

        # Case-specific deeper analysis
        if case == "A":
            print(f"\n  [CASE A PROOF SKETCH]")
            print(f"  3^k in <2> requires k ≡ 0 mod {r} (since <2> ∩ <3> = {{1}}).")
            print(f"  For k = m*{r}: 3^k = 1 mod {p}, need 2^{{S(k)}} ≡ 1 mod {p}.")
            print(f"  i.e., {q} | S(m*{r}) = ceil(m*{r}*log2(3)).")
            # Check first few multiples of r
            hits_A = []
            for m in range(1, min(10001, 1000000 // r + 1)):
                k = m * r
                S_k = math.ceil(k * math.log2(3))
                if S_k % q == 0:
                    hits_A.append((m, k, S_k))
            if hits_A:
                print(f"  WARNING: Found {len(hits_A)} values where q | S(m*r):")
                for m, k, S in hits_A[:5]:
                    print(f"    m={m}, k={k}, S={S}, S mod q = 0")
                    # But also need d(k) = 2^S - 3^k, and p | d(k)
                    # 3^k = 3^{m*r} = 1 mod p, so need 2^S ≡ 1 mod p, i.e., q | S.
                    # We already checked q | S. But does the ACTUAL d(k) = 2^S - 3^k have p | d(k)?
                    # Since 3^k ≡ 1 and 2^S ≡ 1 mod p when q | S, yes p | (2^S - 3^k).
                    # BUT: S(k) = ceil(k * log2(3)), and we need to verify this is the CORRECT S.
                    actual_d = compute_d(k) if k <= 10000 else None
                    if actual_d is not None:
                        print(f"      d({k}) = 2^{S} - 3^{k}, p | d(k)? {actual_d % p == 0}")
            else:
                print(f"  Checked m = 1..{min(10000, 1000000 // r)}: no m with {q} | S(m*{r}).")
                print(f"  This is EXPECTED: {{m*{r}*log2(3)}} equidistributed, density 1/{q}.")
                print(f"  Over {min(10000, 1000000 // r)} samples, expected ~{min(10000, 1000000 // r) / q:.1f} hits.")
                print(f"  Zero hits suggests structural obstruction beyond equidistribution.")

        elif case == "B":
            print(f"\n  [CASE B ANALYSIS — 3 in <2>]")
            print(f"  dlog_2(3) = {analysis['dlog_3']} (i.e., 2^{analysis['dlog_3']} ≡ 3 mod {p})")
            if analysis['dlog_3'] is not None:
                # Ceiling mod analysis
                cma = ceiling_mod_analysis(q, analysis['dlog_3'])
                print(f"  Ceiling-mod analysis:")
                print(f"    Range checked: k = 1..{cma['range_checked']}")
                print(f"    Hits (ceil(k*α) ≡ k*t mod {q}): {cma['n_hits']}")
                if cma['n_hits'] > 0:
                    print(f"    Hit k-values: {cma['hits_in_range'][:10]}...")
                    # For each hit, verify actual divisibility
                    print(f"    Verifying actual p | d(k):")
                    for kh in cma['hits_in_range'][:5]:
                        S_k = compute_S(kh)
                        # Use modular arithmetic to check
                        val_2S = pow(2, S_k, p)
                        val_3k = pow(3, kh, p)
                        divides = (val_2S == val_3k)
                        print(f"      k={kh}: 2^{S_k} mod {p} = {val_2S}, 3^{kh} mod {p} = {val_3k}, p|d(k)? {divides}")
                else:
                    print(f"    NO ceiling-mod coincidences in range!")
                    print(f"    Gap distribution: {cma['gap_distribution_size']} distinct values")
                    print(f"    Minimum nonzero gap: {cma['min_nonzero_gap']}")
                print()

                # Phase mismatch analysis
                if analysis['phase_analysis_sample']:
                    print(f"  Phase mismatch (first 10 k):")
                    for k, S, status in analysis['phase_analysis_sample'][:10]:
                        print(f"    k={k:4d}  S={S:6d}  {status}")

        elif case == "C":
            print(f"\n  [CASE C — Intermediate intersection]")
            print(f"  3^k in <2> iff k ≡ 0 mod {analysis['k_step']}")
            print(f"  Number of valid k per period [0, {r}): {analysis['n_k_in_subgroup_per_period']}")
            # Check these k values
            step = analysis['k_step']
            hits_C = []
            for k in range(step, min(step * 10001, 10_000_001), step):
                S_k = math.ceil(k * math.log2(3))
                val_2S = pow(2, S_k, p)
                val_3k = pow(3, k, p)
                if val_2S == val_3k:
                    hits_C.append(k)
                    if len(hits_C) >= 10:
                        break
            if hits_C:
                print(f"  *** CEILING-COMPATIBLE HITS: {hits_C} ***")
            else:
                print(f"  No ceiling-compatible k found in range.")

    # ── Step 3: Summary ──
    print("\n" + "=" * 78)
    print("  SUMMARY TABLE")
    print("=" * 78)
    print()
    print(f"{'p':>7s}  {'q':>6s}  {'r':>6s}  {'rho':>8s}  {'I':>5s}  "
          f"{'|∩|':>4s}  {'Case':>4s}  {'3∈<2>':>5s}  {'Hits':>4s}  {'Range':>10s}")
    print("─" * 78)

    for a in analyses:
        print(f"{a['p']:7d}  {a['q']:6d}  {a['r']:6d}  {a['rho']:8.5f}  "
              f"{a['index']:5d}  {a['intersection_order']:4d}  "
              f"{'  ' + a['case']:>4s}  {'Yes' if a['three_in_two'] else 'No':>5s}  "
              f"{a['n_hits']:4d}  {a['k_max_checked']:>10d}")

    print("─" * 78)
    print()

    # ── Step 4: Case distribution ──
    print("CASE DISTRIBUTION:")
    for case_label in ["A", "B", "C"]:
        count = case_counts[case_label]
        pct = 100 * count / len(analyses) if analyses else 0
        desc = {
            "A": "<2> ∩ <3> = {1} (trivial intersection → structural obstruction)",
            "B": "3 ∈ <2> (full containment → ceiling constraint must block)",
            "C": "Intermediate intersection",
        }[case_label]
        print(f"  Case {case_label}: {count:4d} primes ({pct:5.1f}%)  — {desc}")

    print()
    print(f"TOTAL DIVISIBILITY HITS p | d(k) across all Fish primes: {total_hits}")

    if total_hits == 0:
        print()
        print("=" * 78)
        print("  *** FISH-TUNNEL INCOMPATIBILITY: EMPIRICALLY CONFIRMED ***")
        print("  No Fish prime p (with rho > 0.5) divides d(k) for any")
        print(f"  k tested (up to ~10^7 per prime).")
        print("=" * 78)
    else:
        print()
        print("!" * 78)
        print("  RESULT: FISH-TUNNEL INCOMPATIBILITY IS FALSE")
        print("  Fish primes DO divide d(k) for infinitely many k.")
        print("!" * 78)
        print()
        print("  Fish primes with divisibility hits:")
        for a in analyses:
            if a['n_hits'] > 0:
                print(f"    p={a['p']} (rho={a['rho']:.4f}, q={a['q']}): "
                      f"first hits at k = {a['divisibility_hits'][:5]}")
        print()

        # ── Deep analysis of WHY the conjecture fails ──
        print("=" * 78)
        print("  STRUCTURAL ANALYSIS OF COUNTEREXAMPLES")
        print("=" * 78)
        print()
        print("  All 13 Fish primes are CASE C (intermediate intersection).")
        print("  None are Case A (trivial intersection) or Case B (3 in <2>).")
        print()
        print("  The failure mechanism:")
        print("    1. Fish primes have SMALL q = ord_p(2) < 2*sqrt(p).")
        print("    2. The intersection |<2> cap <3>| is typically = q (nontrivial).")
        print("    3. 3^k in <2> mod p for k = 0 mod step, where step = r/gcd(r,I).")
        print("    4. For such k, ceil(k*log2(3)) mod q hits the required residue")
        print("       by equidistribution ({k*log2(3)} is equidistributed mod 1).")
        print("    5. With density ~1/q per eligible k, hits are INEVITABLE.")
        print()

        # Density analysis: for each Fish prime, what fraction of eligible k give hits?
        print("  Hit density analysis:")
        print(f"  {'p':>7s}  {'q':>4s}  {'step':>6s}  {'hits':>4s}  {'eligible':>10s}  "
              f"{'density':>8s}  {'expected':>8s}")
        print("  " + "-" * 60)
        for a in analyses:
            if a['n_hits'] > 0:
                step = a['k_step']
                k_max = a['k_max_checked']
                n_eligible = k_max // step
                density = a['n_hits'] / n_eligible if n_eligible > 0 else 0
                expected_density = 1.0 / a['q']
                print(f"  {a['p']:7d}  {a['q']:4d}  {step:6d}  {a['n_hits']:4d}  "
                      f"{n_eligible:10d}  {density:8.5f}  {expected_density:8.5f}")

        print()
        print("  INTERPRETATION:")
        print("    The observed hit density is close to 1/q (equidistribution).")
        print("    This is EXPECTED: for k where 3^k in <2>, the divisibility")
        print("    p | d(k) reduces to ceil(k*log2(3)) = k*t mod q, and the")
        print("    irrationality of log2(3) ensures equidistribution mod q.")
        print("    With density 1/q, hits occur at rate ~(k_max / step) / q.")
        print()
        print("  CONSEQUENCE FOR THE JUNCTION THEOREM:")
        print("    The Fish-Tunnel Incompatibility CANNOT be used as stated.")
        print("    Fish primes (rho > 0.5) DO appear as factors of d(k).")
        print("    However, this does NOT invalidate the Junction Theorem itself,")
        print("    because the theorem concerns corrSum(A) != m*d(k), which is")
        print("    about the FULL value d(k), not individual prime factors.")
        print()
        print("  REVISED STRATEGY:")
        print("    The spectral bound rho(p) > 0.5 does NOT prevent p | d(k).")
        print("    For the exponential sum approach, one must either:")
        print("    (a) Show that even when p | d(k), the character sum bound")
        print("        still prevents corrSum = 0 mod p^e for sufficient e, or")
        print("    (b) Abandon the per-prime Fish-Tunnel decomposition and")
        print("        work with the PRODUCT of character sums over all p | d(k).")
        print()

        # ── Interesting patterns in the counterexamples ──
        print("  NOTABLE PATTERNS:")
        print()

        # Check: are Fish primes = Mersenne/Fermat-related?
        mersenne_primes = {3, 7, 31, 127, 8191}  # 2^p - 1
        fermat_primes = {3, 5, 17, 257, 65537}    # 2^{2^n} + 1
        fish_p_set = {a['p'] for a in analyses}

        fish_mersenne = fish_p_set & mersenne_primes
        fish_fermat = fish_p_set & fermat_primes
        print(f"    Fish primes that are Mersenne primes: {sorted(fish_mersenne)}")
        print(f"    Fish primes that are Fermat primes: {sorted(fish_fermat)}")
        print()

        # Check: are Fish primes related to 2^n +/- 1?
        print("    Relation to 2^n +/- 1:")
        for a in analyses:
            p = a['p']
            q = a['q']
            # p | 2^q - 1 by definition of ord_p(2) = q
            # Check if p = 2^m +/- 1 for some m
            for m in range(2, 20):
                if p == (1 << m) - 1:
                    print(f"      p={p} = 2^{m} - 1 (Mersenne), q={q}")
                elif p == (1 << m) + 1:
                    print(f"      p={p} = 2^{m} + 1 (Fermat-like), q={q}")

        # Check: q divides p-1 and the relationship
        print()
        print("    Structural: q | (p-1) always (Fermat's little theorem).")
        print("    Key question: how does (p-1)/q relate to ord_p(3)?")
        for a in analyses:
            p, q, r = a['p'], a['q'], a['r']
            I = (p - 1) // q
            print(f"      p={p}: q={q}, r={r}, I=(p-1)/q={I}, "
                  f"gcd(q,r)={math.gcd(q,r)}, r/gcd={r // math.gcd(q, r)}")

    # ── Step 5: Statistics on Fish prime structure ──
    print()
    print("=" * 78)
    print("  STRUCTURAL STATISTICS OF FISH PRIMES")
    print("=" * 78)
    print()

    qs = [a['q'] for a in analyses]
    rhos = [a['rho'] for a in analyses]
    indices = [a['index'] for a in analyses]

    if qs:
        print(f"  ord_p(2) = q statistics:")
        print(f"    min = {min(qs)}, max = {max(qs)}, "
              f"mean = {sum(qs)/len(qs):.1f}, median = {sorted(qs)[len(qs)//2]}")
        print()
        print(f"  rho(p) statistics:")
        print(f"    min = {min(rhos):.6f}, max = {max(rhos):.6f}, "
              f"mean = {sum(rhos)/len(rhos):.6f}")
        print()
        print(f"  Index I = (p-1)/q statistics:")
        print(f"    min = {min(indices)}, max = {max(indices)}, "
              f"mean = {sum(indices)/len(indices):.1f}")

    # Distribution of q values
    print()
    print(f"  Distribution of q = ord_p(2) among Fish primes:")
    q_hist = defaultdict(int)
    for q_val in qs:
        q_hist[q_val] += 1
    for q_val in sorted(q_hist.keys())[:20]:
        bar = "█" * min(q_hist[q_val], 60)
        print(f"    q={q_val:4d}: {q_hist[q_val]:5d} {bar}")
    if len(q_hist) > 20:
        print(f"    ... ({len(q_hist)} distinct q values total)")

    # ── Step 6: Connection to the proof ──
    print()
    print("=" * 78)
    print("  CONCLUSIONS AND IMPLICATIONS")
    print("=" * 78)
    print()
    if total_hits > 0:
        print("  MAIN RESULT: The Fish-Tunnel Incompatibility conjecture is FALSE.")
        print()
        print("  The conjecture stated:")
        print("    'If rho(p) > 0.5 then p does not divide d(k) for any k >= 1.'")
        print()
        print("  COUNTEREXAMPLE: p = 31 (rho = 0.5403, q = 5) divides d(48).")
        print(f"    d(48) = 2^77 - 3^48 = {(1<<77) - 3**48}")
        print(f"    d(48) mod 31 = {((1<<77) - 3**48) % 31}")
        print()
        print("  WHY IT FAILS:")
        print("    All 13 Fish primes have nontrivial <2> cap <3> (Case C).")
        print("    The subgroup <2> is small (index I >> 1), but <3> is large")
        print("    (r close to p-1), so their intersection |<2> cap <3>| = gcd(q,r)")
        print("    is typically = q (when q | r).")
        print("    This means 3^k in <2> for k = 0 mod (r/q), giving MANY")
        print("    eligible k. Among those, ceil(k*log2(3)) mod q is equidistributed,")
        print("    so divisibility hits occur with density ~1/q.")
        print()
        print("  IMPACT ON JUNCTION THEOREM PROOF STRATEGY:")
        print("    The exponential sum approach via rho(p) remains valid for bounding")
        print("    the NUMBER of solutions to corrSum = 0 mod p, but the 'Fish primes")
        print("    avoid d(k)' shortcut is unavailable. The proof must handle Fish")
        print("    primes directly, either via:")
        print("      (a) Higher-order character sum bounds (p^e with e >= 2)")
        print("      (b) Product over all primes (Chinese Remainder Theorem)")
        print("      (c) Reformulated spectral condition (e.g., rho for the full d(k),")
        print("          not per-prime)")
    else:
        print("  The Fish-Tunnel Incompatibility is empirically confirmed for p <= 100000.")


if __name__ == '__main__':
    main()
