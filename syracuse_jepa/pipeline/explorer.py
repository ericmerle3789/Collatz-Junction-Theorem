"""
Explorer — Mathematical Data Generation

Generates exhaustive or sampled data for compositions, corrSum, and
related quantities. Feeds structured data to the Conjecturer.
"""

import math
import json
from dataclasses import dataclass, field, asdict
from typing import List, Tuple, Optional, Iterator
from functools import lru_cache


def compute_S(k: int) -> int:
    """S(k) = ceil(k * log2(3))"""
    return math.ceil(k * math.log2(3))


def compute_d(k: int) -> int:
    """d(k) = 2^S(k) - 3^k"""
    return (1 << compute_S(k)) - 3**k


def corrsum(A: list, k: int) -> int:
    """corrSum(A, k) = sum_i 3^(k-1-i) * 2^(A_i)"""
    return sum(3**(k - 1 - i) * (1 << a) for i, a in enumerate(A))


def enumerate_monotone(k: int, S: int, min_val: int = 0) -> Iterator[tuple]:
    """Enumerate all monotone (non-decreasing) compositions of S into k parts."""
    if k == 0:
        if S == 0:
            yield ()
        return
    if k == 1:
        if S >= min_val:
            yield (S,)
        return
    max_first = S // k
    for v in range(min_val, max_first + 1):
        for rest in enumerate_monotone(k - 1, S - v, v):
            yield (v,) + rest


@lru_cache(maxsize=None)
def count_compositions(k: int, S: int, min_val: int = 0) -> int:
    """Count monotone compositions (cached DP)."""
    if k == 0:
        return 1 if S == 0 else 0
    if k == 1:
        return 1 if S >= min_val else 0
    return sum(
        count_compositions(k - 1, S - v, v)
        for v in range(min_val, S // k + 1)
    )


@dataclass
class ExplorationResult:
    """Complete exploration data for one value of k."""
    k: int
    S: int
    d: int
    n_compositions: int
    n_zero_residue: int  # N_0: compositions with corrSum ≡ 0 mod d
    min_gap_abs: int     # min |corrSum mod d| over non-zero residues
    min_gap_rel: float   # min_gap_abs / d
    closest_composition: Optional[list] = None
    closest_corrsum: int = 0
    closest_residue: int = 0
    # Pattern data for conjecturer
    residue_distribution: dict = field(default_factory=dict)
    zero_compositions: list = field(default_factory=list)
    # Almost-flat analysis
    almost_flat_residue: int = 0
    almost_flat_v: int = 0
    almost_flat_r: int = 0

    def to_dict(self):
        return asdict(self)


def explore_k(k: int, max_compositions: int = 2_000_000) -> ExplorationResult:
    """Full exploration for a single k value."""
    S = compute_S(k)
    d = compute_d(k)
    n_comp = count_compositions(k, S)

    if n_comp > max_compositions:
        return ExplorationResult(
            k=k, S=S, d=d, n_compositions=n_comp,
            n_zero_residue=-1,  # -1 = not computed (too many)
            min_gap_abs=-1, min_gap_rel=-1.0,
        )

    n_zero = 0
    min_gap = d
    closest_comp = None
    closest_cs = 0
    closest_res = 0
    zero_comps = []

    for A in enumerate_monotone(k, S):
        cs = corrsum(list(A), k)
        r = cs % d
        if r == 0:
            n_zero += 1
            zero_comps.append(list(A))
        else:
            gap = min(r, d - r)
            if gap < min_gap:
                min_gap = gap
                closest_comp = list(A)
                closest_cs = cs
                closest_res = r

    # Almost-flat analysis
    v = S // k
    r_count = S % k
    if r_count == 0:
        af_comp = [v] * k
    else:
        af_comp = [v] * (k - r_count) + [v + 1] * r_count
    af_cs = corrsum(af_comp, k)
    af_residue = af_cs % d

    return ExplorationResult(
        k=k, S=S, d=d, n_compositions=n_comp,
        n_zero_residue=n_zero,
        min_gap_abs=min_gap if n_zero == 0 else 0,
        min_gap_rel=(min_gap / d) if n_zero == 0 and d > 0 else 0.0,
        closest_composition=closest_comp,
        closest_corrsum=closest_cs,
        closest_residue=closest_res,
        zero_compositions=zero_comps,
        almost_flat_residue=af_residue,
        almost_flat_v=v,
        almost_flat_r=r_count,
    )


def explore_range(k_min: int = 3, k_max: int = 40,
                  max_compositions: int = 2_000_000) -> List[ExplorationResult]:
    """Explore all k values in range."""
    results = []
    for k in range(k_min, k_max + 1):
        result = explore_k(k, max_compositions)
        results.append(result)
        status = "N0=0 ✓" if result.n_zero_residue == 0 else (
            f"N0={result.n_zero_residue}" if result.n_zero_residue > 0 else "SKIPPED"
        )
        print(f"  k={k:2d}  S={result.S:2d}  d={result.d:>20d}  "
              f"#comp={result.n_compositions:>8d}  {status}")
    return results


if __name__ == '__main__':
    print("=" * 70)
    print("  EXPLORER — Generating mathematical data")
    print("=" * 70)
    results = explore_range(3, 40)

    # Save
    out = [r.to_dict() for r in results]
    with open('syracuse_jepa/pipeline/exploration_data.json', 'w') as f:
        json.dump(out, f, indent=2)
    print(f"\nSaved {len(results)} exploration results.")
