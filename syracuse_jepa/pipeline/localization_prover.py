#!/usr/bin/env python3
"""
LOCALIZATION PROVER — Where does d appear in N(P_σ)?
=====================================================

For k=5: d=13 divides N(P_σ) for 10/35 sequences. But P_σ(2) ≡ 0 mod 13
for 0/35. So the factor 13 in the norm comes from OTHER conjugates.

N(P_σ(α)) = Π_{j=0}^{S-1} P_σ(α·ζ^j)

The j=0 factor is P_σ(α) evaluated at the real root α = 3^{k/S}.
But we evaluate at α = 2 (since 2^S = 3^k mod d).

d | Π P_σ(α·ζ^j) but d ∤ P_σ(2) means the prime factor d appears
in some P_σ(α·ζ^j) with j ≠ 0.

QUESTION: Which conjugate j absorbs the factor d?

If we can show that the j=0 conjugate NEVER absorbs d,
while some j ≠ 0 conjugate always does, that gives a proof.

This is an ANALYTIC approach in the number field: the j=0 evaluation
(at the real root ≈ 2) gives a large positive number, while other
evaluations (at complex roots) can be small and hit 0 mod d.
"""

import sys, os, cmath
from math import ceil, log2, comb, gcd, pi
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def analyze_conjugate_evaluations(k):
    """
    For each σ, compute |P_σ(α·ζ^j)| for all j=0,...,S-1.
    Find which conjugate is closest to 0 (absorbs the prime factors).
    """
    S = compute_S(k)
    d = compute_d(k)
    if d <= 0: return

    C = count_cumulative_sequences(k, S)
    if C > 5000: return

    alpha_real = 3**(k/S)  # Real S-th root
    print(f"\nk={k}, S={S}, d={d}, α = 3^({k}/{S}) = {alpha_real:.6f}")

    # For each j, α·ζ^j where ζ = e^{2πi/S}
    # The j=0 root: α_0 = α_real ≈ 2.00... (close to 2!)
    # |α_0 - 2| is related to d: d = 2^S - 3^k ≈ 3^k·Λ where Λ = S·ln2 - k·ln3.
    delta = abs(alpha_real - 2)
    print(f"  |α - 2| = {delta:.8f}")
    print(f"  α^S = {alpha_real**S:.1f} (should be {3**k})")

    # For each σ, find which conjugate gives min |P_σ(root)|
    j0_never_min = True
    j0_count = 0

    for sigma in enumerate_cumulative_sequences(k, S):
        # Evaluate P_σ at each conjugate root
        evals = []
        for j in range(S):
            angle = 2 * pi * j / S
            root = alpha_real * cmath.exp(1j * angle)
            val = sum(3**(k-1-i) * root**sigma[i] for i in range(len(sigma)))
            evals.append(abs(val))

        min_j = min(range(S), key=lambda j: evals[j])
        if min_j == 0:
            j0_never_min = False
            j0_count += 1

    print(f"  j=0 (real root) is MINIMUM for {j0_count}/{C} sequences")
    print(f"  j=0 NEVER minimum: {j0_never_min}")

    if j0_never_min:
        print(f"  ★ The real conjugate P_σ(α) is NEVER the smallest!")
        print(f"  This means: if d | N(P_σ), the factor comes from j ≠ 0.")
        print(f"  Proof approach: bound |P_σ(α)| > d from below → P_σ(2) ≢ 0 mod d.")

    # Actually compute P_σ(α_real) and compare with d
    min_pval = float('inf')
    for sigma in enumerate_cumulative_sequences(k, S):
        val = sum(3**(k-1-i) * alpha_real**sigma[i] for i in range(len(sigma)))
        if val < min_pval:
            min_pval = val

    print(f"  min P_σ(α_real) = {min_pval:.2f} vs d = {d}")
    print(f"  min P_σ(α_real) / d = {min_pval/d:.4f}")

    # THE KEY INSIGHT: P_σ(α_real) = corrSum(σ) evaluated at α instead of 2.
    # Since α ≈ 2 (because 3^{k/S} ≈ 2 when S ≈ k·log₂3):
    # P_σ(α) ≈ P_σ(2) = corrSum(σ).
    # And corrSum > d (verified as L1 in proof search).
    # So |P_σ(α)| > d approximately.

    # More precisely: P_σ(α) = P_σ(2) + P_σ'(ξ)·(α - 2) for some ξ ∈ (2, α).
    # |P_σ(α) - P_σ(2)| ≤ |P_σ'(max)|·|α-2|.
    # If this is small enough, P_σ(α) ≈ P_σ(2) > d, so |P_σ(α)| > d.
    # Then d cannot divide P_σ(α) (as a real number d doesn't divide something > d
    # unless it equals d or 2d etc. — but we need d | P_σ(2) in Z, not |P_σ(α)|).

    # Actually, the connection is:
    # P_σ(2) mod d = P_σ(α) mod (α-2) in Z[α].
    # And |P_σ(α)| is the absolute value in the REAL embedding.
    # We can't directly use |P_σ(α)| > d to conclude P_σ(2) ≢ 0 mod d.

    # BUT: if d is PRIME and P_σ(α) ∉ (α-2), then P_σ(2) ≢ 0 mod d.
    # And P_σ(α) ∉ (α-2) iff the NORM N(P_σ) is not in (d).
    # For k=3,4: N(P_σ) is coprime to d → QED.
    # For k=5: N(P_σ) can be divisible by d. Need to check WHICH ideal factor of d
    #          divides P_σ(α) in Z[α].

    print(f"  (End of conjugate analysis for k={k})")


def main():
    print("LOCALIZATION OF d IN THE NORM")
    print("=" * 60)
    for k in [3, 4, 5, 7, 8]:
        analyze_conjugate_evaluations(k)


if __name__ == '__main__':
    main()
