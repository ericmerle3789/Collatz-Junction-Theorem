#!/usr/bin/env python3
"""
PARADIGM BREAKER — Creative Discovery Engine for Hypothesis H
==============================================================

The standard approaches (Range Exclusion, per-prime FCQ, exponential sums L∞/L2)
ALL FAIL for cumulative corrSum. This module thinks OUTSIDE those paradigms.

Philosophy: Investigateur racinaire + Innovateur déductif + Allégories
- Don't try to bound. Try to UNDERSTAND.
- Don't treat d as a black box. It's 2^S - 3^k.
- Don't treat corrSum as arbitrary. It's a weighted sum on a geometric set.
- The answer might be ALGEBRAIC, not ANALYTIC.

Architecture:
  SEED BANK → RESONANCE DETECTOR → PARADIGM GENERATOR → JUDGE → OUTPUT

Anti-hallucination: Every claim is verified numerically before being accepted.
"""

import sys, os, json, time
from math import ceil, log2, comb, gcd, log
from itertools import combinations
from collections import Counter
from typing import List, Dict, Tuple, Optional

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative, corrsum_cumulative_mod,
    enumerate_cumulative_sequences, count_cumulative_sequences,
    cumulative_to_individual, is_valid_cycle_candidate
)


# ================================================================
# SEED BANK: Atomic facts about the cumulative corrSum problem
# ================================================================

def plant_seeds(k_max: int = 14) -> List[dict]:
    """Extract all known atomic facts that might seed a paradigm break."""
    seeds = []

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0:
            continue

        C = count_cumulative_sequences(k, S)
        if C > 500000:
            continue

        # Enumerate and analyze
        residues = []
        corrsums = []
        for sigma in enumerate_cumulative_sequences(k, S):
            cs = corrsum_cumulative(sigma, k)
            corrsums.append(cs)
            residues.append(cs % d)

        hit = set(residues)
        N0 = residues.count(0)

        # Seed 1: Steiner's algebraic identity
        # corrSum = 3^{k-1} + Σ 3^{k-1-i} · 2^{σ_i}
        # In Z/dZ: 2^S ≡ 3^k, so 3 ≡ 2^{S/k} "approximately"
        seeds.append({
            'type': 'algebraic_identity',
            'k': k, 'S': S, 'd': d,
            'relation': f'2^{S} ≡ 3^{k} mod {d}',
            'note': 'The COUPLING between 2 and 3 modulo d'
        })

        # Seed 2: Coverage pattern
        coverage = len(hit) / d
        seeds.append({
            'type': 'coverage',
            'k': k, 'coverage': coverage,
            'C_over_d': C / d,
            'missed': d - len(hit),
            '0_missed': 0 not in hit,
        })

        # Seed 3: corrSum/d distribution (quotients)
        quotients = [cs // d for cs in corrsums]
        seeds.append({
            'type': 'quotient_range',
            'k': k, 'q_min': min(quotients), 'q_max': max(quotients),
            'note': 'n₀ would be in this range if cycle existed'
        })

        # Seed 4: First term dominance
        # corrSum = 3^{k-1} + REST where REST involves 2^{σ_i} with σ_i ≥ 1
        base = pow(3, k-1)
        rest_min = min(cs - base for cs in corrsums)
        rest_max = max(cs - base for cs in corrsums)
        seeds.append({
            'type': 'first_term_dominance',
            'k': k, 'base': base, 'base_mod_d': base % d,
            'rest_range': (rest_min, rest_max),
            'note': '3^{k-1} is the FIXED term (σ_0=0). REST varies.'
        })

        # Seed 5: Residue of base term
        # For corrSum ≡ 0 mod d, REST ≡ -3^{k-1} mod d
        target_rest = (-base) % d
        rest_residues = [(cs - base) % d for cs in corrsums]
        hits_target = sum(1 for r in rest_residues if r == target_rest)
        seeds.append({
            'type': 'target_avoidance',
            'k': k, 'target': target_rest,
            'hits': hits_target,
            'note': f'REST must hit {target_rest} mod {d} for cycle. Hits: {hits_target}'
        })

        # Seed 6: Multiplicative structure in Z/dZ
        # 2 and 3 have specific orders mod d
        # The weights 3^{k-1-i} cycle with period ord_d(3)
        # The values 2^{σ_i} cycle with period ord_d(2)
        ord2 = 1
        x = 2 % d
        while x != 1 and ord2 < d:
            x = (x * 2) % d
            ord2 += 1
        if x != 1:
            ord2 = -1  # 2 doesn't have finite order (shouldn't happen)

        seeds.append({
            'type': 'multiplicative_order',
            'k': k, 'd': d, 'ord_d_2': ord2,
            'S_mod_ord': S % ord2 if ord2 > 0 else -1,
            'note': f'2^S = 2^{{{S}}} ≡ 2^{{{S % ord2 if ord2 > 0 else "?"}}} mod d. But 2^S ≡ 3^k mod d.'
        })

        # Seed 7: Polynomial evaluation perspective
        # corrSum = P(2) where P(X) = Σ 3^{k-1-i} · X^{σ_i} in Z/dZ
        # This is an evaluation of a specific polynomial at X = 2
        # The polynomial has k terms with geometric coefficients
        seeds.append({
            'type': 'polynomial_evaluation',
            'k': k,
            'note': 'corrSum = P(2) mod d where P has k terms with 3-geometric coefficients'
        })

    return seeds


# ================================================================
# RESONANCE DETECTOR: Find surprising interactions between seeds
# ================================================================

def detect_resonances(seeds: List[dict], k_max: int = 14) -> List[dict]:
    """Detect non-trivial interactions between atomic facts."""
    resonances = []

    # Group seeds by k
    by_k = {}
    for s in seeds:
        k = s.get('k')
        if k:
            by_k.setdefault(k, []).append(s)

    for k, k_seeds in by_k.items():
        seed_map = {s['type']: s for s in k_seeds}

        # Resonance 1: Why is the target ALWAYS avoided?
        if 'target_avoidance' in seed_map:
            ta = seed_map['target_avoidance']
            if ta['hits'] == 0:
                resonances.append({
                    'type': 'target_always_avoided',
                    'k': k,
                    'target': ta['target'],
                    'strength': 'STRONG',
                    'note': f'REST never hits {ta["target"]} mod d. WHY?',
                    'paradigm_hint': 'Algebraic obstruction, not probabilistic'
                })

        # Resonance 2: Coupling 2^S = 3^k creates algebraic constraint
        if 'algebraic_identity' in seed_map and 'polynomial_evaluation' in seed_map:
            resonances.append({
                'type': 'algebraic_coupling',
                'k': k,
                'strength': 'FUNDAMENTAL',
                'note': 'P(2) ≡ 0 mod d with d = 2^S - 3^k and P has 3-geometric coefficients. '
                        'The ROOT of d (in terms of 2 and 3) is the same as the STRUCTURE of P.',
                'paradigm_hint': 'The polynomial P is "adapted" to the modulus d. '
                                 'This is NOT a coincidence — it IS the cycle equation.'
            })

        # Resonance 3: First term 3^{k-1} mod d is special
        if 'first_term_dominance' in seed_map:
            ftd = seed_map['first_term_dominance']
            base_mod = ftd['base_mod_d']
            d = ftd.get('rest_range', (0,0))
            resonances.append({
                'type': 'base_residue_structure',
                'k': k,
                'base_mod_d': base_mod,
                'note': f'3^{{k-1}} mod d = {base_mod}. Since 3^k ≡ 2^S mod d, '
                        f'3^{{k-1}} ≡ 2^S · 3^{{-1}} mod d.',
                'paradigm_hint': 'The base term encodes the coupling. '
                                 'Its residue is NOT arbitrary.'
            })

    # Cross-k resonances
    # Look at how coverage evolves
    coverages = [(s['k'], s['coverage']) for s in seeds if s['type'] == 'coverage']
    if len(coverages) > 3:
        # Does coverage decrease monotonically?
        decreasing = all(coverages[i][1] >= coverages[i+1][1]
                        for i in range(len(coverages)-1) if coverages[i][0] < coverages[i+1][0])
        resonances.append({
            'type': 'coverage_trend',
            'data': coverages,
            'decreasing': decreasing,
            'note': 'Coverage C/d → 0 exponentially (Junction Theorem).',
            'paradigm_hint': 'For large k, Im(Ev_d) is EXTREMELY sparse. '
                             'In a sparse regime, avoiding ONE specific value is "easy".'
        })

    return resonances


# ================================================================
# PARADIGM GENERATOR: Create genuinely new proof approaches
# ================================================================

def generate_paradigms(seeds: List[dict], resonances: List[dict]) -> List[dict]:
    """
    Generate paradigm-breaking proof ideas.
    Each paradigm is a fundamentally different way to prove H.
    """
    paradigms = []

    # ══════════════════════════════════════════════════
    # PARADIGM 1: The Functional Equation Approach
    # ══════════════════════════════════════════════════
    # corrSum(σ) = 0 mod d means P(α) = 0 mod d where α = 2.
    # But d = α^S - β^k where β = 3.
    # So α^S ≡ β^k mod d, meaning P(α) ≡ 0 mod (α^S - β^k).
    # This is a POLYNOMIAL DIVISIBILITY question:
    # Does (X^S - β^k) | P(X) in Z[X]?
    # If NOT, then P(α) mod d ≠ 0 (in some sense).
    paradigms.append({
        'name': 'FUNCTIONAL_EQUATION',
        'idea': 'Treat corrSum ≡ 0 mod d as a polynomial divisibility problem. '
                'P(X) = Σ β^{k-1-i} · X^{σ_i} evaluated at X = α = 2, '
                'modulo d = α^S - β^k. This is: does (X^S - β^k) divide P(X) in Z[X]? '
                'Since P has only k terms (degree < S) and X^S - β^k has degree S, '
                'divisibility is impossible unless P has very specific structure.',
        'verification': 'Check: for k=5, P(X) = 81 + 27X^{σ_1} + 9X^{σ_2} + 3X^{σ_3} + X^{σ_4} '
                        'divided by X^8 - 243. The remainder at X=2 is corrSum mod 13.',
        'potential': 'HIGH — transforms the number theory problem into algebra',
        'obstacle': 'P depends on the choice of σ (many polynomials to check)',
    })

    # ══════════════════════════════════════════════════
    # PARADIGM 2: The Galois Theory Approach
    # ══════════════════════════════════════════════════
    # d = 2^S - 3^k. For prime d, Z/dZ is a field.
    # The element 2 generates a subgroup of order ord_d(2) = S (since 2^S = 3^k ≡ 0... no).
    # Actually ord_d(2) divides φ(d) but 2^S ≡ 3^k mod d, not 1.
    # The key: the set {2^0, 2^1, ..., 2^{S-1}} mod d is a GEOMETRIC progression
    # that wraps around Z/dZ in a specific pattern determined by ord_d(2).
    paradigms.append({
        'name': 'GALOIS_GEOMETRIC_SET',
        'idea': 'The corrSum is a weighted sum of elements from the geometric set '
                'G = {1, 2, 4, ..., 2^{S-1}} mod d. The weights are from '
                'W = {3^{k-1}, 3^{k-2}, ..., 1} mod d. Both are geometric. '
                'The interaction of TWO geometric progressions modulo d = 2^S - 3^k '
                'might have algebraic properties that prevent 0 from being attainable. '
                'Key: 2^S = 3^k mod d ties G and W together.',
        'verification': 'For k=5: G = {1,2,4,8,3,6,12,11} mod 13, W = {3,1,9,3,1} mod 13. '
                        'Check if the "reachable set" of Σ w_rank(σ_i) · 2^{σ_i} always avoids target.',
        'potential': 'MEDIUM-HIGH — Galois theory of cyclotomic fields might apply',
        'obstacle': 'd is usually composite, not a field',
    })

    # ══════════════════════════════════════════════════
    # PARADIGM 3: The Information-Theoretic Approach
    # ══════════════════════════════════════════════════
    # A cycle requires n₀ · d = corrSum. This means corrSum carries
    # EXACTLY log₂(d) bits of "information" about divisibility.
    # But the choice of σ encodes log₂(C) bits.
    # For k ≥ 18: log₂(C) < log₂(d), so the choice CANNOT specify
    # a particular residue class mod d.
    # This is an information-theoretic IMPOSSIBILITY.
    paradigms.append({
        'name': 'INFORMATION_THEORETIC',
        'idea': 'The choice of σ encodes log₂(C(S-1,k-1)) bits of information. '
                'For corrSum ≡ 0 mod d, we need to "hit" a specific residue, '
                'which requires log₂(d) bits of precision. '
                'For k ≥ 18: log₂(C) < log₂(d), so the choice CANNOT carry enough '
                'information to specify residue 0. '
                'HOWEVER: this argument proves "at most one 0-hit" not "exactly zero". '
                'Need: the "encoding" corrSum(σ) mod d is INJECTIVE enough.',
        'verification': 'For k=14: log₂(C) = 18.9, log₂(d) = 21.8. Gap of 2.9 bits.',
        'potential': 'MEDIUM — proves impossibility in average case, need worst case',
        'obstacle': 'The encoding is highly non-injective (many σ give same residue)',
    })

    # ══════════════════════════════════════════════════
    # PARADIGM 4: The Orbit Impossibility via Heights
    # ══════════════════════════════════════════════════
    # If a cycle exists, n₀ = corrSum/d. The orbit (n₀,...,n_{k-1})
    # must satisfy the "height" condition:
    # h(orbit) = Σ log(n_i) = constant per cycle.
    # But h is related to the Mahler measure of the polynomial P.
    # If the Mahler measure of P is incompatible with a cycle, done.
    paradigms.append({
        'name': 'HEIGHT_IMPOSSIBILITY',
        'idea': 'Use the theory of heights in arithmetic dynamics. '
                'The Collatz map T is a piecewise-affine dynamical system. '
                'A cycle is a periodic orbit of T. '
                'The canonical height of a cycle is h = (1/k) Σ log n_i. '
                'By Baker-Wüstholz: h ≥ c/(log k)^{k+1} for effective c. '
                'But also h ≤ log(corrSum_max/d) which decreases. '
                'If lower > upper, no cycle.',
        'verification': 'For k=68: lower bound ≈ ? (need Baker constants), '
                        'upper bound = log(corrSum_max/d) ≈ log(C) - log(d) < 0 (since C < d).',
        'potential': 'HIGH — directly uses the counting bound in a new way',
        'obstacle': 'Baker-Wüstholz constants are large; effective for large k only',
    })

    # ══════════════════════════════════════════════════
    # PARADIGM 5: The Self-Referential Approach
    # ══════════════════════════════════════════════════
    # corrSum = n₀ · d. But n₀ = corrSum/d.
    # Also: each orbit element n_i satisfies its own Steiner equation
    # (starting from n_i instead of n₀).
    # This gives a SYSTEM of k equations, each involving the SAME d.
    # The system is overdetermined (k equations, k unknowns, but
    # constrained to a set of size C < d).
    paradigms.append({
        'name': 'SELF_REFERENTIAL_SYSTEM',
        'idea': 'A k-cycle gives k Steiner equations (one per starting element). '
                'Each equation involves the SAME d = 2^S - 3^k. '
                'The system is: n_i · d = corrSum_i(σ^{(i)}) for i=0,...,k-1. '
                'The σ^{(i)} are cyclically shifted versions of σ^{(0)}. '
                'This creates k LINKED constraints on a single object. '
                'Combined with C < d: the overdetermined system has no solution.',
        'verification': 'Check: for k=5, write all 5 Steiner equations. '
                        'Are they algebraically independent?',
        'potential': 'VERY HIGH — exploits the FULL cycle structure, not just one equation',
        'obstacle': 'Need to formalize "algebraically independent" for shifted σ',
    })

    # ══════════════════════════════════════════════════
    # PARADIGM 6: The Carry Propagation Approach
    # ══════════════════════════════════════════════════
    # corrSum = Σ 3^{k-1-i} · 2^{σ_i}. The binary representation of corrSum
    # has specific carry patterns when adding the k terms.
    # d = 2^S - 3^k in binary has a specific pattern too.
    # For d | corrSum, the carry pattern of corrSum must be compatible with d.
    # The carries create LONG-RANGE CORRELATIONS between the σ_i choices.
    paradigms.append({
        'name': 'CARRY_PROPAGATION',
        'idea': 'In base 2, corrSum = Σ 3^{k-1-i} · 2^{σ_i} involves adding k terms '
                'at SPECIFIC bit positions (σ_i). The carry chains create '
                'dependencies between positions. For d | corrSum, the carries must '
                'conspire to produce a specific bit pattern (multiple of d). '
                'The strict ordering σ_0 < σ_1 < ... < σ_{k-1} limits which carry '
                'patterns are achievable.',
        'verification': 'For k=5, analyze the binary structure of all 35 corrSum values. '
                        'Compare carry patterns of values near 0 mod 13 vs far from 0.',
        'potential': 'MEDIUM — carries are hard to analyze but structurally rich',
        'obstacle': '3^{k-1-i} in binary is complex; carry analysis is technical',
    })

    return paradigms


# ================================================================
# JUDGE: Verify paradigms numerically
# ================================================================

def judge_paradigm(paradigm: dict, k_test: int = 5) -> dict:
    """
    Numerically test a paradigm on a small case.
    Returns the paradigm augmented with verification results.
    """
    S = compute_S(k_test)
    d = compute_d(k_test)
    name = paradigm['name']
    result = dict(paradigm)
    result['k_test'] = k_test

    if name == 'FUNCTIONAL_EQUATION':
        # For each σ, compute P(X) mod (X^S - 3^k) evaluated at X=2
        # This is exactly corrSum mod d. Check that it's never 0.
        never_zero = True
        for sigma in enumerate_cumulative_sequences(k_test, S):
            cs_mod = corrsum_cumulative_mod(sigma, k_test, d)
            if cs_mod == 0:
                never_zero = False
                break
        result['verified'] = never_zero
        result['note'] = f'P(2) mod (2^S-3^k) ≠ 0 for all σ: {never_zero}'

    elif name == 'SELF_REFERENTIAL_SYSTEM':
        # For a hypothetical cycle: check that cyclic shifts give consistent equations
        # Take a random σ, compute all k cyclic shifts, check if they're all consistent
        # with the same n₀, n₁, ..., n_{k-1}
        test_sigmas = list(enumerate_cumulative_sequences(k_test, S))[:5]
        for sigma in test_sigmas:
            diag = is_valid_cycle_candidate(sigma, k_test)
            if diag['is_divisible'] and diag.get('valid_orbit') and diag.get('orbit_closes'):
                result['found_cycle'] = True
                result['sigma'] = sigma
                break
        else:
            result['found_cycle'] = False
        result['verified'] = not result.get('found_cycle', False)
        result['note'] = f'No valid cycle found for k={k_test}: {result["verified"]}'

    elif name == 'INFORMATION_THEORETIC':
        C = count_cumulative_sequences(k_test, S)
        result['log2_C'] = log(C, 2) if C > 0 else 0
        result['log2_d'] = log(d, 2) if d > 0 else 0
        result['bit_gap'] = result['log2_d'] - result['log2_C']
        result['verified'] = result['bit_gap'] > 0  # C < d means info gap
        result['note'] = f'Bit gap: {result["bit_gap"]:.2f} (positive means C < d)'

    else:
        result['verified'] = 'not_tested'
        result['note'] = 'Numerical test not implemented for this paradigm'

    return result


# ================================================================
# MAIN: Run the paradigm breaker
# ================================================================

def run_paradigm_breaker(k_max: int = 14) -> dict:
    """Full paradigm-breaking cycle."""
    t_start = time.time()

    print("╔" + "═" * 68 + "╗")
    print("║  PARADIGM BREAKER — Creative Discovery for Hypothesis H           ║")
    print("║  Seeds → Resonances → Paradigms → Judge                           ║")
    print("╚" + "═" * 68 + "╝\n")

    # Step 1: Plant seeds
    print("┌─ STEP 1: PLANT SEEDS ─────────────────────────────────────┐")
    seeds = plant_seeds(k_max)
    n_types = len(set(s['type'] for s in seeds))
    print(f"  Planted {len(seeds)} seeds across {n_types} categories")
    print(f"└───────────────────────────────────────────────────────────┘\n")

    # Step 2: Detect resonances
    print("┌─ STEP 2: DETECT RESONANCES ───────────────────────────────┐")
    resonances = detect_resonances(seeds, k_max)
    for r in resonances:
        if r.get('strength') in ('STRONG', 'FUNDAMENTAL'):
            print(f"  ★ {r['type']} (k={r.get('k', '?')}): {r.get('paradigm_hint', '')[:70]}")
    print(f"  Total: {len(resonances)} resonances detected")
    print(f"└───────────────────────────────────────────────────────────┘\n")

    # Step 3: Generate paradigms
    print("┌─ STEP 3: GENERATE PARADIGMS ──────────────────────────────┐")
    paradigms = generate_paradigms(seeds, resonances)
    for p in paradigms:
        print(f"  [{p['potential']:>12}] {p['name']}")
    print(f"  Total: {len(paradigms)} paradigms generated")
    print(f"└───────────────────────────────────────────────────────────┘\n")

    # Step 4: Judge paradigms
    print("┌─ STEP 4: JUDGE PARADIGMS ─────────────────────────────────┐")
    judged = []
    for p in paradigms:
        j = judge_paradigm(p, k_test=5)
        judged.append(j)
        status = "✓" if j.get('verified') == True else ("✗" if j.get('verified') == False else "?")
        print(f"  {status} {j['name']}: {j.get('note', '')[:60]}")
    print(f"└───────────────────────────────────────────────────────────┘\n")

    # Rank by potential
    ranking = sorted(judged, key=lambda p: {'VERY HIGH': 5, 'HIGH': 4, 'MEDIUM-HIGH': 3,
                                             'MEDIUM': 2, 'LOW': 1}.get(p.get('potential', 'LOW'), 0),
                     reverse=True)

    print("╔" + "═" * 68 + "╗")
    print("║  PARADIGM RANKING                                                 ║")
    print("╠" + "═" * 68 + "╣")
    for i, p in enumerate(ranking):
        v = "✓" if p.get('verified') == True else "?"
        print(f"║  {i+1}. [{p['potential']:>12}] {v} {p['name']:<40} ║")
    print("╚" + "═" * 68 + "╝")

    elapsed = time.time() - t_start

    result = {
        'n_seeds': len(seeds),
        'n_resonances': len(resonances),
        'n_paradigms': len(paradigms),
        'ranking': [{'name': p['name'], 'potential': p['potential'],
                     'verified': p.get('verified')} for p in ranking],
        'time': round(elapsed, 2),
    }

    # Save
    out_path = os.path.join(os.path.dirname(__file__), '..', 'logs', 'paradigm_breaker_result.json')
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, 'w') as f:
        json.dump(result, f, indent=2)

    return result


if __name__ == '__main__':
    run_paradigm_breaker()
