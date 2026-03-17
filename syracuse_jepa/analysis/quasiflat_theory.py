"""
Syracuse-JEPA v2 — Quasi-Flat Composition Theory

The JEPA + near-miss analysis revealed that compositions closest to
corrSum = m*d are QUASI-FLAT: aᵢ ≈ S/k with small deviations.

This module develops the THEORY of quasi-flat compositions:
1. For a flat composition A = (v, v, ..., v, v+1, ..., v+1), corrSum has a CLOSED FORM
2. This closed form allows us to prove corrSum mod d ≠ 0 ANALYTICALLY
3. If we can show that ALL near-misses are quasi-flat, this gives a proof strategy

KEY INSIGHT:
  For a perfectly flat composition A = (v, v, ..., v) with k·v = S:
    corrSum = 2^v · Σᵢ 3^{k-1-i} = 2^v · (3^k - 1) / 2

  For d = 2^S - 3^k, the condition corrSum = m·d becomes:
    2^v · (3^k - 1) / 2 = m · (2^S - 3^k)

  This is a Diophantine equation in v and m that we can analyze.
"""

import sys
import os
import math
import json
import numpy as np
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from syracuse_jepa.data.generator import (
    compute_S, compute_d, corrsum, corrsum_mod,
    enumerate_monotone_compositions, count_compositions,
)


def corrsum_flat(k: int, v: int) -> int:
    """
    corrSum for a perfectly flat composition A = (v, v, ..., v).
    corrSum = 2^v · Σᵢ 3^{k-1-i} = 2^v · (3^k - 1) / 2
    """
    # (3^k - 1) is always even (3^k is odd, minus 1 = even)
    return (1 << v) * (3**k - 1) // 2


def corrsum_almost_flat(k: int, v: int, r: int) -> int:
    """
    corrSum for an almost-flat composition:
    A = (v, v, ..., v, v+1, ..., v+1)
    where the first (k-r) entries are v and the last r entries are v+1.
    Sum = (k-r)*v + r*(v+1) = k*v + r.

    corrSum = Σᵢ₌₀^{k-r-1} 3^{k-1-i} · 2^v + Σᵢ₌k-r^{k-1} 3^{k-1-i} · 2^{v+1}
            = 2^v · Σᵢ₌₀^{k-r-1} 3^{k-1-i} + 2^{v+1} · Σᵢ₌k-r^{k-1} 3^{k-1-i}
            = 2^v · [Σ₀^{k-1} 3^{k-1-i} + Σ_{k-r}^{k-1} 3^{k-1-i}]
            = 2^v · [(3^k - 1)/2 + (3^r - 1)/2]
            = 2^v · [(3^k + 3^r - 2)/2]
            Wait, let me recompute...

    Let S_total = Σᵢ₌₀^{k-1} 3^{k-1-i} = (3^k - 1) / 2
    Let S_tail = Σᵢ₌k-r^{k-1} 3^{k-1-i} = Σⱼ₌₀^{r-1} 3^j = (3^r - 1) / 2

    corrSum = 2^v · (S_total - S_tail) + 2^{v+1} · S_tail
            = 2^v · S_total + 2^v · S_tail
            = 2^v · [(3^k - 1)/2 + (3^r - 1)/2]
    """
    S_total = (3**k - 1) // 2
    S_tail = (3**r - 1) // 2
    return (1 << v) * (S_total + S_tail)


def analyze_flat_corrsum(max_k: int = 25):
    """
    For each k, compute corrSum for flat and almost-flat compositions.
    Check if they can equal m*d.
    """
    print("=" * 80)
    print("  QUASI-FLAT COMPOSITION ANALYSIS")
    print("=" * 80)
    print()

    for k in range(3, max_k + 1):
        S = compute_S(k)
        d = compute_d(k)

        # Case 1: Perfectly flat (only possible if k | S)
        if S % k == 0:
            v = S // k
            cs = corrsum_flat(k, v)
            r = cs % d
            ratio = cs / d
            print(f"k={k:2d}  FLAT: A=({v},)*{k}  S={S}  cs={cs}  mod d={r}  ratio={ratio:.6f}")
        else:
            # Case 2: Almost flat with r = S mod k entries at v+1
            v = S // k
            r_count = S % k  # number of (v+1) entries
            cs = corrsum_almost_flat(k, v, r_count)
            residue = cs % d
            ratio = cs / d

            # Verify against direct computation
            A_flat = [v] * (k - r_count) + [v + 1] * r_count
            cs_direct = corrsum(A_flat, k)
            assert cs == cs_direct, f"Mismatch: {cs} vs {cs_direct}"

            print(
                f"k={k:2d}  ALMOST-FLAT: v={v}, r={r_count}  "
                f"A=({v},)*{k-r_count}+({v+1},)*{r_count}  "
                f"cs={cs}  mod d={residue}  ratio={ratio:.6f}  "
                f"{'*** ZERO ***' if residue == 0 else ''}"
            )


def prove_flat_avoidance():
    """
    THEORETICAL ANALYSIS: Can corrSum for a flat composition equal m*d?

    For the almost-flat case with r entries at v+1:
      corrSum = 2^v · [(3^k - 1)/2 + (3^r - 1)/2]
             = 2^v · (3^k + 3^r - 2) / 2
             = 2^{v-1} · (3^k + 3^r - 2)

    For this to equal m · d = m · (2^S - 3^k):
      2^{v-1} · (3^k + 3^r - 2) = m · (2^S - 3^k)

    where S = k·v + r.

    So: 2^{v-1} · (3^k + 3^r - 2) = m · (2^{kv+r} - 3^k)

    For the FLAT case (r=0, S = kv):
      2^{v-1} · (3^k - 1) = m · (2^{kv} - 3^k)

    This is a diophantine equation in m (for fixed k and v = S/k).

    KEY: Since 3^k - 1 is even, write 3^k - 1 = 2·T_k where T_k = (3^k-1)/2.
    Then: 2^v · T_k = m · (2^{kv} - 3^k)

    For m to be a positive integer:
      m = 2^v · T_k / (2^{kv} - 3^k)

    Since d = 2^{kv} - 3^k > 0, we need 2^v · T_k to be divisible by d.

    Let's check: gcd(2^v · T_k, d) = gcd(2^v · T_k, 2^{kv} - 3^k)
    Since d = 2^{kv} - 3^k is odd (2^{kv} is even iff kv > 0, 3^k is odd → d is odd).
    Wait: 2^{kv} is even (kv >= 3), 3^k is odd, so d is odd.
    Therefore gcd(2^v, d) = 1 (d is odd, 2^v has only factor 2).
    So: m = 2^v · T_k / d is integer iff d | T_k.
    """
    print("\n" + "=" * 80)
    print("  THEORETICAL: Can flat corrSum = m*d?")
    print("  For flat case: m = 2^v · T_k / d where T_k = (3^k-1)/2")
    print("  Since d is ODD: need d | T_k")
    print("=" * 80)
    print()

    for k in range(3, 30):
        S = compute_S(k)
        d = compute_d(k)

        if S % k == 0:
            v = S // k
            T_k = (3**k - 1) // 2
            divides = (T_k % d == 0)
            if divides:
                m = (1 << v) * T_k // d
                print(f"k={k:2d}  d={d:>14d}  T_k mod d = 0  *** FLAT corrSum = {m}*d ***")
            else:
                residue_T = T_k % d
                print(f"k={k:2d}  d={d:>14d}  T_k mod d = {residue_T:>14d}  (NOT zero)")
        else:
            v = S // k
            r = S % k
            # Almost-flat: need d | (T_k + T_r) where T_r = (3^r - 1)/2
            T_k = (3**k - 1) // 2
            T_r = (3**r - 1) // 2
            combined = T_k + T_r
            divides = (combined % d == 0)
            residue = combined % d
            print(
                f"k={k:2d}  d={d:>14d}  "
                f"(T_k+T_r) mod d = {residue:>14d}  "
                f"{'*** DIVIDES ***' if divides else ''}"
                f"  [v={v}, r={r}]"
            )


def search_quasi_flat_avoidance(max_k: int = 25, max_span: int = 5):
    """
    For each k, enumerate compositions with span <= max_span.
    These are the "quasi-flat" compositions.
    Check if ANY of them gives corrSum = m*d.

    If no quasi-flat composition hits m*d, and we can bound the gap for
    non-quasi-flat compositions, we have a proof strategy.
    """
    print("\n" + "=" * 80)
    print(f"  QUASI-FLAT SEARCH (span <= {max_span})")
    print("=" * 80)
    print()

    for k in range(3, max_k + 1):
        S = compute_S(k)
        d = compute_d(k)
        n_comp = count_compositions(k, S)

        if n_comp > 300000:
            print(f"k={k:2d}: skipping ({n_comp} total)")
            continue

        n_qf = 0  # quasi-flat count
        n_qf_zero = 0
        min_qf_gap = d
        min_qf_comp = None

        n_nqf = 0  # non-quasi-flat count
        min_nqf_gap = d

        for A in enumerate_monotone_compositions(k, S):
            cs = corrsum(list(A), k)
            r = cs % d
            gap = min(r, d - r) if r > 0 else 0
            span = A[-1] - A[0]

            if span <= max_span:
                n_qf += 1
                if r == 0:
                    n_qf_zero += 1
                if gap < min_qf_gap and r > 0:
                    min_qf_gap = gap
                    min_qf_comp = A
            else:
                n_nqf += 1
                if gap < min_nqf_gap and r > 0:
                    min_nqf_gap = gap

        print(
            f"k={k:2d}  QF(span<={max_span}): {n_qf:>6d}/{n_comp}  "
            f"N0_QF={n_qf_zero}  min_gap_QF={min_qf_gap:>10d}  "
            f"NQF: {n_nqf:>6d}  min_gap_NQF={min_nqf_gap if n_nqf > 0 else 'N/A':>10}  "
            f"comp={min_qf_comp}"
        )


if __name__ == '__main__':
    analyze_flat_corrsum(max_k=30)
    prove_flat_avoidance()
    search_quasi_flat_avoidance(max_k=25, max_span=3)
