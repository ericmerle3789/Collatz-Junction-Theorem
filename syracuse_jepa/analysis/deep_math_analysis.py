"""
Syracuse-JEPA v2 — Deep Mathematical Analysis

Goes beyond ML to extract MATHEMATICAL PATTERNS from the data.
The JEPA showed us WHERE to look (R2=0.85 on fractional ratios).
Now we formalize what it found.

Key questions:
1. What is the distribution of corrSum/d (fractional part)?
2. Is there a lower bound on min|corrSum - m*d| / d?
3. How does this lower bound scale with k?
4. Can we find a FORMULA for the minimum distance?
"""

import sys
import os
import math
import json
import numpy as np
from collections import defaultdict
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from syracuse_jepa.data.generator import (
    compute_S, compute_d, corrsum, corrsum_mod, corrsum_terms,
    enumerate_monotone_compositions, count_compositions,
)


def analyze_corrsum_distribution(k: int) -> dict:
    """Detailed analysis of corrSum distribution for a given k."""
    S = compute_S(k)
    d = compute_d(k)

    all_cs = []
    all_ratios = []
    all_residues = []
    all_compositions = []

    for A in enumerate_monotone_compositions(k, S):
        cs = corrsum(list(A), k)
        all_cs.append(cs)
        all_ratios.append(cs / d)
        all_residues.append(cs % d)
        all_compositions.append(A)

    ratios = np.array(all_ratios)
    residues = np.array(all_residues)
    frac = ratios - np.floor(ratios)

    # Closest to integer
    dist_to_int = np.minimum(frac, 1 - frac)
    closest_idx = np.argmin(dist_to_int)

    # Distribution of residues
    residue_counts = defaultdict(int)
    for r in all_residues:
        residue_counts[r] += 1

    # Which residues are MISSING?
    missing_residues = [r for r in range(d) if r not in residue_counts]

    # g_min and g_max (corrSum/d bounds)
    g_min = min(all_ratios)
    g_max = max(all_ratios)

    return {
        'k': k, 'S': S, 'd': d,
        'n_compositions': len(all_cs),
        'g_min': g_min, 'g_max': g_max,
        'g_min_floor': int(np.floor(g_min)),
        'g_max_floor': int(np.floor(g_max)),
        'n_possible_m': int(np.floor(g_max)) - int(np.ceil(g_min)) + 1,
        'closest_frac': float(dist_to_int[closest_idx]),
        'closest_composition': all_compositions[closest_idx],
        'closest_corrsum': all_cs[closest_idx],
        'closest_ratio': all_ratios[closest_idx],
        'n_distinct_residues': len(residue_counts),
        'n_missing_residues': len(missing_residues),
        'zero_in_range': 0 in residue_counts,
        'residue_coverage': len(residue_counts) / d,
    }


def find_gap_lower_bound(max_k: int = 25) -> list:
    """
    For each k, find the minimum |corrSum - m*d| / d over all compositions A
    and all integers m. This is the GAP — if we can bound it away from 0,
    we prove N0(d) = 0.
    """
    results = []

    for k in range(3, max_k + 1):
        S = compute_S(k)
        d = compute_d(k)
        n_comp = count_compositions(k, S)

        if n_comp > 200000:
            print(f"k={k}: skipping ({n_comp} compositions)")
            continue

        min_gap = float('inf')
        min_gap_comp = None
        min_gap_m = None
        n_zero = 0

        for A in enumerate_monotone_compositions(k, S):
            cs = corrsum(list(A), k)
            r = cs % d

            if r == 0:
                n_zero += 1
                min_gap = 0
                min_gap_comp = A
                min_gap_m = cs // d
            else:
                gap = min(r, d - r) / d
                if gap < min_gap:
                    min_gap = gap
                    min_gap_comp = A
                    # Which m is closest?
                    m_low = cs // d
                    if r <= d - r:
                        min_gap_m = m_low
                    else:
                        min_gap_m = m_low + 1

        result = {
            'k': k, 'S': S, 'd': d,
            'n_compositions': n_comp,
            'min_gap': min_gap,
            'min_gap_composition': min_gap_comp,
            'min_gap_m': min_gap_m,
            'n_zero': n_zero,
        }
        results.append(result)

        if min_gap > 0:
            # Express gap as fraction for exact representation
            cs = corrsum(list(min_gap_comp), k)
            r = cs % d
            exact_gap = Fraction(min(r, d - r), d)
            result['exact_gap'] = str(exact_gap)
            result['gap_numerator'] = exact_gap.numerator
            result['gap_denominator'] = exact_gap.denominator

        marker = "N0>0!" if n_zero > 0 else ""
        print(
            f"k={k:2d}  d={d:>12d}  gap={min_gap:.8f}  "
            f"comp={min_gap_comp}  N0={n_zero}  {marker}"
        )

    return results


def analyze_gap_scaling(results: list) -> dict:
    """
    Analyze how the gap scales with k.
    If gap ~ C * f(k) for some function f, this gives us a LEMMA candidate.
    """
    # Filter out k=4 (has N0=1)
    filtered = [r for r in results if r['n_zero'] == 0 and r['min_gap'] > 0]

    if len(filtered) < 3:
        return {'status': 'insufficient_data'}

    k_vals = np.array([r['k'] for r in filtered])
    gaps = np.array([r['min_gap'] for r in filtered])
    log_gaps = np.log(gaps)
    d_vals = np.array([r['d'] for r in filtered])
    log_d = np.log(d_vals)

    # Try gap ~ C * k^alpha
    from numpy.polynomial import polynomial as P
    # log(gap) = alpha * log(k) + log(C)
    log_k = np.log(k_vals)
    coeffs = np.polyfit(log_k, log_gaps, 1)
    alpha = coeffs[0]
    log_C = coeffs[1]
    r2_power = 1 - np.sum((log_gaps - (alpha * log_k + log_C))**2) / np.sum((log_gaps - np.mean(log_gaps))**2)

    # Try gap ~ C * exp(-beta * k)
    coeffs_exp = np.polyfit(k_vals, log_gaps, 1)
    beta = -coeffs_exp[0]
    log_C_exp = coeffs_exp[1]
    r2_exp = 1 - np.sum((log_gaps - (coeffs_exp[0] * k_vals + log_C_exp))**2) / np.sum((log_gaps - np.mean(log_gaps))**2)

    # Try gap ~ C / d^gamma
    coeffs_d = np.polyfit(log_d, log_gaps, 1)
    gamma = -coeffs_d[0]
    r2_d = 1 - np.sum((log_gaps - (coeffs_d[0] * log_d + coeffs_d[1]))**2) / np.sum((log_gaps - np.mean(log_gaps))**2)

    return {
        'power_law': {
            'alpha': float(alpha),
            'C': float(np.exp(log_C)),
            'r2': float(r2_power),
            'formula': f'gap ~ {np.exp(log_C):.4f} * k^{alpha:.4f}',
        },
        'exponential': {
            'beta': float(beta),
            'C': float(np.exp(log_C_exp)),
            'r2': float(r2_exp),
            'formula': f'gap ~ {np.exp(log_C_exp):.4f} * exp(-{beta:.4f} * k)',
        },
        'd_scaling': {
            'gamma': float(gamma),
            'r2': float(r2_d),
            'formula': f'gap ~ C * d^{-gamma:.4f}',
        },
        'best_fit': max(
            [('power_law', r2_power), ('exponential', r2_exp), ('d_scaling', r2_d)],
            key=lambda x: x[1]
        )[0],
    }


def extract_corrsum_mod_structure(k: int) -> dict:
    """
    Analyze the GROUP STRUCTURE of corrSum values mod d.
    Which cosets of Z/dZ are hit? Which are avoided?
    Is there an algebraic pattern?
    """
    S = compute_S(k)
    d = compute_d(k)

    residues = set()
    for A in enumerate_monotone_compositions(k, S):
        cs = corrsum_mod(list(A), k, d)
        residues.add(cs)

    # Check if residues form a subgroup or coset
    residues_list = sorted(residues)

    # Check closure under addition mod d
    is_closed_under_add = True
    for a in residues_list[:50]:  # check first 50 for efficiency
        for b in residues_list[:50]:
            if (a + b) % d not in residues:
                is_closed_under_add = False
                break
        if not is_closed_under_add:
            break

    # Check if residues are a coset of some subgroup
    # If residues = g + H for some subgroup H, then residues - residues = H
    diffs = set()
    for a in residues_list[:100]:
        for b in residues_list[:100]:
            diffs.add((a - b) % d)

    return {
        'k': k, 'd': d,
        'n_residues': len(residues),
        'd_total': d,
        'coverage': len(residues) / d,
        'zero_in_residues': 0 in residues,
        'is_closed_under_addition': is_closed_under_add,
        'n_differences': len(diffs),
        'diffs_coverage': len(diffs) / d,
        'residues_sample': residues_list[:20],
    }


def find_forbidden_zone(k: int) -> dict:
    """
    For a given k, identify the 'forbidden zone' around 0 in the residue space.
    What is the minimum and maximum residue? Is there a gap around 0?
    """
    S = compute_S(k)
    d = compute_d(k)

    residues = []
    for A in enumerate_monotone_compositions(k, S):
        cs = corrsum_mod(list(A), k, d)
        residues.append(cs)

    residues = sorted(set(residues))

    if not residues:
        return {'k': k, 'status': 'no_data'}

    # Find gap around 0
    # Residues close to 0 (from below): max r such that r < d/2 and close to 0
    # Residues close to 0 (from above): min r such that r > d/2, measuring d-r
    close_to_zero = []
    for r in residues:
        dist = min(r, d - r)
        close_to_zero.append((dist, r))
    close_to_zero.sort()

    # The "forbidden zone" is [0, min_pos_residue) union (d - min_neg_residue, d)
    min_positive = min(r for r in residues if r > 0) if any(r > 0 for r in residues) else d
    max_below_d = max(r for r in residues if r < d) if any(r < d for r in residues) else 0
    gap_from_above = d - max_below_d

    return {
        'k': k, 'd': d,
        'min_positive_residue': min_positive,
        'gap_from_above': gap_from_above,
        'forbidden_zone_size': min(min_positive, gap_from_above),
        'forbidden_zone_fraction': min(min_positive, gap_from_above) / d,
        'closest_5_to_zero': close_to_zero[:5],
        'n_distinct_residues': len(residues),
    }


if __name__ == '__main__':
    print("=" * 70)
    print("  DEEP MATHEMATICAL ANALYSIS — Syracuse-JEPA v2")
    print("=" * 70)

    print("\n--- 1. Gap Lower Bound ---")
    gap_results = find_gap_lower_bound(max_k=23)

    print("\n--- 2. Gap Scaling Analysis ---")
    scaling = analyze_gap_scaling(gap_results)
    print(f"\nBest fit: {scaling.get('best_fit', 'N/A')}")
    for model_name in ['power_law', 'exponential', 'd_scaling']:
        if model_name in scaling:
            m = scaling[model_name]
            print(f"  {model_name}: {m['formula']}  (R2={m['r2']:.4f})")

    print("\n--- 3. Residue Structure ---")
    for k in [3, 5, 7, 10, 15, 20]:
        S = compute_S(k)
        d = compute_d(k)
        n_comp = count_compositions(k, S)
        if n_comp > 100000:
            continue
        struct = extract_corrsum_mod_structure(k)
        print(
            f"  k={k:2d}  d={struct['d']:>10d}  "
            f"coverage={struct['coverage']:.4f}  "
            f"zero={struct['zero_in_residues']}  "
            f"closed_add={struct['is_closed_under_addition']}"
        )

    print("\n--- 4. Forbidden Zone Analysis ---")
    for k in range(3, 21):
        S = compute_S(k)
        d = compute_d(k)
        n_comp = count_compositions(k, S)
        if n_comp > 100000:
            continue
        fz = find_forbidden_zone(k)
        print(
            f"  k={k:2d}  d={fz['d']:>10d}  "
            f"forbidden_zone={fz['forbidden_zone_size']:>6d}  "
            f"fraction={fz['forbidden_zone_fraction']:.6f}  "
            f"closest={fz['closest_5_to_zero'][:2]}"
        )

    # Save results
    output = {
        'gap_results': [{k: v for k, v in r.items() if k != 'min_gap_composition'}
                       for r in gap_results],
        'scaling': scaling,
    }
    os.makedirs('syracuse_jepa/logs', exist_ok=True)
    with open('syracuse_jepa/logs/deep_math_results.json', 'w') as f:
        json.dump(output, f, indent=2, default=str)
    print("\nResults saved to syracuse_jepa/logs/deep_math_results.json")
