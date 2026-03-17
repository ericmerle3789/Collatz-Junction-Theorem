"""
Syracuse-JEPA v2 — Data Generator for Collatz Junction Theorem

Generates monotone compositions and their corrSum values for JEPA training.

Mathematical objects:
- Monotone composition A = (a₀ ≤ a₁ ≤ ... ≤ a_{k-1}), Σ aᵢ = S
- S(k) = ⌈k · log₂(3)⌉ (unique S such that d(k) = 2^S - 3^k > 0 minimal)
- corrSum(A) = Σᵢ 3^{k-1-i} · 2^{aᵢ}
- d(k) = 2^S - 3^k
- g_max(k) = max_A corrSum(A)
- Junction Theorem: corrSum(A) ≠ m·d for any m ≥ 1 and any monotone A

Reference: Merle, "Collatz Junction Theorem" (preprint)
"""

import math
import numpy as np
from typing import List, Tuple, Optional, Generator
from functools import lru_cache


def compute_S(k: int) -> int:
    """Compute S(k) = ⌈k · log₂(3)⌉, the unique S such that d = 2^S - 3^k > 0 is minimal."""
    return math.ceil(k * math.log2(3))


def compute_d(k: int) -> int:
    """Compute d(k) = 2^S - 3^k."""
    S = compute_S(k)
    return (1 << S) - 3**k


def corrsum(A: List[int], k: int) -> int:
    """
    Compute corrSum(A) = Σᵢ 3^{k-1-i} · 2^{aᵢ} for a composition A of length k.
    Uses Python arbitrary precision integers.
    """
    total = 0
    for i, a in enumerate(A):
        total += 3**(k - 1 - i) * (1 << a)
    return total


def corrsum_terms(A: List[int], k: int) -> List[int]:
    """Return individual terms 3^{k-1-i} · 2^{aᵢ} as a list."""
    return [3**(k - 1 - i) * (1 << a) for i, a in enumerate(A)]


def corrsum_mod(A: List[int], k: int, m: int) -> int:
    """Compute corrSum(A) mod m efficiently using modular arithmetic."""
    total = 0
    for i, a in enumerate(A):
        total = (total + pow(3, k - 1 - i, m) * pow(2, a, m)) % m
    return total


def enumerate_monotone_compositions(k: int, S: int) -> Generator[Tuple[int, ...], None, None]:
    """
    Enumerate ALL monotone compositions of S into k parts.
    A monotone composition: 0 ≤ a₀ ≤ a₁ ≤ ... ≤ a_{k-1}, Σ aᵢ = S.

    Yields tuples (a₀, a₁, ..., a_{k-1}).

    WARNING: Exponential in k. Only use for small k (≤ ~25).
    """
    def _recurse(pos: int, remaining: int, min_val: int, current: List[int]):
        if pos == k:
            if remaining == 0:
                yield tuple(current)
            return
        # max value for this position: remaining (if all subsequent are same)
        max_val = remaining // (k - pos) if pos < k - 1 else remaining
        # Actually, remaining sum with (k-pos) parts each >= min_val
        # The last part takes whatever is left
        if pos == k - 1:
            if remaining >= min_val:
                yield tuple(current + [remaining])
            return
        for v in range(min_val, remaining + 1):
            # Check if remaining - v can be distributed among k-pos-1 parts each >= v
            rest = remaining - v
            parts_left = k - pos - 1
            if rest >= v * parts_left:  # minimum possible with parts >= v
                yield from _recurse(pos + 1, rest, v, current + [v])

    yield from _recurse(0, S, 0, [])


def count_compositions(k: int, S: int) -> int:
    """Count monotone compositions without enumerating (dynamic programming)."""
    # p(S, k) = number of partitions of S into exactly k non-negative parts (weakly increasing)
    # = number of partitions of S into at most k parts (by conjugation)
    # Use DP: dp[s][j] = # ways to partition s into at most j parts
    dp = [[0] * (k + 1) for _ in range(S + 1)]
    for j in range(k + 1):
        dp[0][j] = 1  # empty partition
    for s in range(1, S + 1):
        for j in range(1, k + 1):
            # Either don't use a part of size s, or use one
            dp[s][j] = dp[s][j - 1]
            if s >= j:
                dp[s][j] += dp[s - j][j]
    return dp[S][k]


def sample_monotone_composition(k: int, S: int, rng: np.random.Generator) -> Tuple[int, ...]:
    """
    Sample a uniformly random monotone composition of S into k non-negative parts.
    Uses the "stars and bars" + sorting approach for uniform sampling.
    """
    # Method: sample k non-negative integers summing to S, then sort
    # Uniform on compositions (not partitions) then sort → biased toward partitions
    # with more distinct orderings. For JEPA this is acceptable as we want coverage.
    #
    # Better method: Nijenhuis-Wilf for uniform partitions, but complex.
    # Compromise: use Dirichlet-based continuous relaxation then round.

    # Simple approach: random breakpoints
    if k == 1:
        return (S,)

    breakpoints = sorted(rng.choice(S + k - 1, size=k - 1, replace=False))
    parts = []
    prev = 0
    for bp in breakpoints:
        parts.append(bp - prev)
        prev = bp + 1
    parts.append(S + k - 1 - prev)
    # This gives a uniform composition; sort for monotone
    parts.sort()
    return tuple(parts)


def generate_dataset_exact(k: int) -> dict:
    """
    Generate EXACT dataset for a given k: enumerate all compositions and compute corrSum.
    Returns dict with arrays.
    """
    S = compute_S(k)
    d = compute_d(k)

    compositions = []
    corrsums = []
    residues = []  # corrSum mod d
    ratios = []    # corrSum / d (float)

    for A in enumerate_monotone_compositions(k, S):
        cs = corrsum(list(A), k)
        compositions.append(A)
        corrsums.append(cs)
        residues.append(cs % d)
        ratios.append(float(cs) / float(d))

    return {
        'k': k,
        'S': S,
        'd': d,
        'compositions': compositions,
        'corrsums': corrsums,
        'residues': residues,
        'ratios': ratios,
        'n_total': len(compositions),
        'n_zero_residue': sum(1 for r in residues if r == 0),
    }


def generate_dataset_sampled(k: int, n_samples: int, seed: int = 42) -> dict:
    """Generate sampled dataset for larger k values."""
    S = compute_S(k)
    d = compute_d(k)
    rng = np.random.default_rng(seed)

    compositions = []
    corrsums = []
    residues = []
    ratios = []

    for _ in range(n_samples):
        A = sample_monotone_composition(k, S, rng)
        cs = corrsum(list(A), k)
        compositions.append(A)
        corrsums.append(cs)
        residues.append(cs % d)
        ratios.append(float(cs) / float(d))

    return {
        'k': k,
        'S': S,
        'd': d,
        'compositions': compositions,
        'corrsums': corrsums,
        'residues': residues,
        'ratios': ratios,
        'n_total': len(compositions),
        'n_zero_residue': sum(1 for r in residues if r == 0),
    }


def generate_multi_view_features(A: Tuple[int, ...], k: int, S: int, d: int) -> dict:
    """
    Generate multiple views/features for a single composition.
    These are the inputs to the JEPA encoder.

    View 1 (structural): The composition itself, normalized
    View 2 (arithmetic): corrSum terms and their residues
    View 3 (spectral): Fourier-like features of the composition
    """
    A_list = list(A)

    # View 1: Structural
    A_normalized = np.array(A_list, dtype=np.float32) / max(S, 1)
    gaps = np.diff(A_list).astype(np.float32) / max(S, 1)  # gaps between consecutive elements

    # View 2: Arithmetic
    terms = corrsum_terms(A_list, k)
    log_terms = np.array([math.log2(t) if t > 0 else 0 for t in terms], dtype=np.float32)
    cs = sum(terms)
    residue = cs % d
    ratio = float(cs) / float(d)
    fractional_ratio = ratio - int(ratio)  # how close to a multiple of d

    # Residues mod small primes
    small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    prime_residues = np.array([cs % p for p in small_primes], dtype=np.float32)
    prime_residues_normalized = prime_residues / np.array(small_primes, dtype=np.float32)

    # View 3: Spectral
    # DFT of the composition sequence
    A_complex = np.array(A_list, dtype=np.complex128)
    fft = np.fft.fft(A_complex)
    fft_magnitude = np.abs(fft).astype(np.float32) / max(S, 1)
    fft_phase = np.angle(fft).astype(np.float32) / np.pi  # normalized to [-1, 1]

    return {
        'view1_composition': A_normalized,
        'view1_gaps': gaps,
        'view2_log_terms': log_terms,
        'view2_fractional_ratio': np.float32(fractional_ratio),
        'view2_prime_residues': prime_residues_normalized,
        'view3_fft_magnitude': fft_magnitude,
        'view3_fft_phase': fft_phase,
        # Labels (for probing, not training)
        'residue_mod_d': residue,
        'ratio': ratio,
        'corrsum': cs,
    }


def prepare_jepa_batch(dataset: dict, pad_k: int = 50) -> dict:
    """
    Prepare a batch of multi-view features for JEPA training.
    Pads all sequences to pad_k for batching.
    """
    k = dataset['k']
    S = dataset['S']
    d = dataset['d']

    all_v1_comp = []
    all_v1_gaps = []
    all_v2_log = []
    all_v2_frac = []
    all_v2_primes = []
    all_v3_mag = []
    all_v3_phase = []
    all_residues = []
    all_ratios = []

    for A in dataset['compositions']:
        features = generate_multi_view_features(A, k, S, d)

        # Pad to pad_k
        def pad(arr, target_len):
            if len(arr) >= target_len:
                return arr[:target_len]
            return np.pad(arr, (0, target_len - len(arr)), mode='constant')

        all_v1_comp.append(pad(features['view1_composition'], pad_k))
        all_v1_gaps.append(pad(features['view1_gaps'], pad_k - 1))
        all_v2_log.append(pad(features['view2_log_terms'], pad_k))
        all_v2_frac.append(features['view2_fractional_ratio'])
        all_v2_primes.append(features['view2_prime_residues'])
        all_v3_mag.append(pad(features['view3_fft_magnitude'], pad_k))
        all_v3_phase.append(pad(features['view3_fft_phase'], pad_k))
        all_residues.append(features['residue_mod_d'])
        all_ratios.append(features['ratio'])

    return {
        'v1_composition': np.stack(all_v1_comp),
        'v1_gaps': np.stack(all_v1_gaps),
        'v2_log_terms': np.stack(all_v2_log),
        'v2_fractional_ratio': np.array(all_v2_frac),
        'v2_prime_residues': np.stack(all_v2_primes),
        'v3_fft_magnitude': np.stack(all_v3_mag),
        'v3_fft_phase': np.stack(all_v3_phase),
        'residues': np.array(all_residues),
        'ratios': np.array(all_ratios),
        'k': k,
        'S': S,
        'd': d,
    }


# Quick validation
if __name__ == '__main__':
    for k in range(3, 12):
        S = compute_S(k)
        d = compute_d(k)
        n_comp = count_compositions(k, S)
        print(f"k={k:2d}  S={S:2d}  d={d:10d}  #compositions={n_comp:>10d}")

    # Verify for k=3
    print("\n--- k=3 exact enumeration ---")
    ds = generate_dataset_exact(3)
    print(f"Total compositions: {ds['n_total']}")
    print(f"Zero residues (corrSum ≡ 0 mod d): {ds['n_zero_residue']}")
    print(f"Min ratio: {min(ds['ratios']):.4f}, Max ratio: {max(ds['ratios']):.4f}")

    # Show first few
    for i in range(min(5, ds['n_total'])):
        A = ds['compositions'][i]
        cs = ds['corrsums'][i]
        r = ds['residues'][i]
        print(f"  A={A}  corrSum={cs}  mod d={r}  ratio={ds['ratios'][i]:.4f}")
