#!/usr/bin/env python3
"""
Cumulative Sequence Generator — CORRECT Steiner Formula
========================================================

Replaces monotone compositions with cumulative position sequences.
This is the CORRECT mathematical object for Steiner's equation (1977).

Steiner: n₀ · (2^S - 3^k) = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{σ_i}
where σ = (0 = σ_0 < σ_1 < ... < σ_{k-1} < S) are cumulative exponents.

The set of valid sequences is Comp_cum(S, k) = {(k-1)-subsets of {1,...,S-1}}
prepended with 0. Count: C(S-1, k-1).
"""

from itertools import combinations
from math import ceil, log2, comb
from typing import Generator, Tuple, List, Dict, Optional
import numpy as np


def compute_S(k: int) -> int:
    """S(k) = ⌈k · log₂(3)⌉"""
    return ceil(k * log2(3))


def compute_d(k: int) -> int:
    """d(k) = 2^S - 3^k"""
    S = compute_S(k)
    return (1 << S) - 3**k


def corrsum_cumulative(sigma: Tuple[int, ...], k: int) -> int:
    """
    Correct Steiner corrSum with CUMULATIVE exponents.
    corrSum(σ) = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{σ_i}
    where σ_0 = 0 and σ is strictly increasing.
    """
    return sum(pow(3, k - 1 - i) * pow(2, sigma[i]) for i in range(k))


def corrsum_cumulative_mod(sigma: Tuple[int, ...], k: int, m: int) -> int:
    """corrSum mod m using modular exponentiation."""
    return sum(pow(3, k - 1 - i, m) * pow(2, sigma[i], m) for i in range(k)) % m


def enumerate_cumulative_sequences(k: int, S: int) -> Generator[Tuple[int, ...], None, None]:
    """
    Enumerate ALL valid cumulative sequences.
    σ = (0, σ_1, ..., σ_{k-1}) with 0 < σ_1 < ... < σ_{k-1} < S.
    Count: C(S-1, k-1).

    WARNING: Exponential in k. Use only for k ≤ ~20.
    """
    for combo in combinations(range(1, S), k - 1):
        yield (0,) + combo


def count_cumulative_sequences(k: int, S: int) -> int:
    """Count cumulative sequences = C(S-1, k-1)."""
    return comb(S - 1, k - 1)


def cumulative_to_individual(sigma: Tuple[int, ...]) -> Tuple[int, ...]:
    """Convert cumulative sequence to individual exponents.
    e_i = σ_i - σ_{i-1} for i ≥ 1, with e_0 undefined (σ_0 = 0).
    Returns (e_1, e_2, ..., e_{k-1}, S - σ_{k-1}).
    """
    k = len(sigma)
    return tuple(sigma[i] - sigma[i-1] for i in range(1, k))


def sample_cumulative_sequence(k: int, S: int, rng=None) -> Tuple[int, ...]:
    """Sample a random cumulative sequence uniformly."""
    if rng is None:
        rng = np.random.default_rng()
    # Choose k-1 values from {1,...,S-1} without replacement
    chosen = sorted(rng.choice(range(1, S), size=k-1, replace=False))
    return (0,) + tuple(int(x) for x in chosen)


def compute_n0(sigma: Tuple[int, ...], k: int) -> float:
    """Compute n₀ = corrSum/d. Returns float (exact if integer)."""
    d = compute_d(k)
    cs = corrsum_cumulative(sigma, k)
    if d == 0:
        return float('inf')
    return cs / d


def is_valid_cycle_candidate(sigma: Tuple[int, ...], k: int) -> dict:
    """
    Check if a cumulative sequence could correspond to a Collatz cycle.
    Returns diagnostic dict.
    """
    S = compute_S(k)
    d = compute_d(k)
    cs = corrsum_cumulative(sigma, k)

    n0_exact = cs / d
    n0_int = cs // d
    remainder = cs % d

    result = {
        'sigma': sigma,
        'k': k, 'S': S, 'd': d,
        'corrSum': cs,
        'corrSum_mod_d': remainder,
        'is_divisible': remainder == 0,
        'n0_float': n0_exact,
    }

    if remainder == 0:
        result['n0'] = n0_int
        result['n0_is_odd'] = n0_int % 2 == 1
        result['n0_positive'] = n0_int > 0

        # Orbit analysis
        individual = cumulative_to_individual(sigma)
        orbit = [n0_int]
        valid_orbit = True
        for e in individual:
            n = orbit[-1]
            numerator = 3 * n + 1
            if numerator % (1 << e) != 0:
                valid_orbit = False
                break
            next_n = numerator // (1 << e)
            orbit.append(next_n)

        result['individual_exponents'] = individual
        result['orbit'] = orbit
        result['valid_orbit'] = valid_orbit
        if valid_orbit and len(orbit) > 1:
            result['orbit_closes'] = orbit[-1] == orbit[0]

    return result


def generate_exploration_data(k: int, max_sequences: int = 100000) -> dict:
    """
    Generate complete exploration data for a given k using cumulative sequences.
    """
    S = compute_S(k)
    d = compute_d(k)
    C = count_cumulative_sequences(k, S)

    data = {
        'k': k, 'S': S, 'd': d, 'C': C, 'C_over_d': C / d if d > 0 else float('inf'),
        'formula': 'cumulative',
    }

    if C > max_sequences:
        data['enumerated'] = False
        data['note'] = f'Too many sequences ({C}), sampling'
        # Sample
        rng = np.random.default_rng(42)
        n_samples = min(max_sequences, C)
        residues = []
        for _ in range(n_samples):
            sigma = sample_cumulative_sequence(k, S, rng)
            r = corrsum_cumulative_mod(sigma, k, d)
            residues.append(r)
        data['n_sampled'] = n_samples
        data['n_zero_residue'] = sum(1 for r in residues if r == 0)
        data['n_distinct_residues'] = len(set(residues))
    else:
        data['enumerated'] = True
        residues = []
        zero_sequences = []
        for sigma in enumerate_cumulative_sequences(k, S):
            r = corrsum_cumulative_mod(sigma, k, d) if d > 0 else -1
            residues.append(r)
            if r == 0:
                zero_sequences.append(sigma)

        data['n_zero_residue'] = len(zero_sequences)
        data['zero_sequences'] = [list(s) for s in zero_sequences]
        data['n_distinct_residues'] = len(set(residues))
        data['coverage'] = len(set(residues)) / d if d > 0 else 0

        # Min distance to 0
        if residues:
            min_dist = min(min(r, d - r) for r in residues if d > 0)
            data['min_distance_to_0'] = min_dist

    return data


if __name__ == '__main__':
    print("CUMULATIVE SEQUENCE GENERATOR — Verification")
    print("=" * 60)

    for k in range(3, 16):
        data = generate_exploration_data(k)
        status = "N₀=0 ✓" if data['n_zero_residue'] == 0 else f"N₀={data['n_zero_residue']} !!!"
        cov = data.get('coverage', '?')
        cov_str = f"{cov:.3f}" if isinstance(cov, float) else str(cov)
        print(f"k={k:2d}  C={data['C']:>10d}  d={data['d']:>12d}  "
              f"C/d={data['C_over_d']:.4f}  coverage={cov_str}  {status}")
