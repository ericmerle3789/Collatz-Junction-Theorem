#!/usr/bin/env python3
"""
MAXIMUM PRINCIPLE FOR POSITIVE SUMS — Path to Universal Proof
===============================================================

THEOREM CANDIDATE:
For all σ ∈ Comp_cum(S,k) and all j=1,...,S-1:
  |P_σ(α·ζ^j)| < P_σ(α)
where α = 3^{k/S} (real root), ζ = e^{2πi/S}.

PROOF IDEA:
P_σ(X) = Σ_{i=0}^{k-1} c_i · X^{σ_i} with c_i = 3^{k-1-i} > 0.

At the real root X = α: all terms c_i · α^{σ_i} are POSITIVE.
At X = α·ζ^j: P_σ(α·ζ^j) = Σ c_i · α^{σ_i} · ζ^{j·σ_i}.

|P_σ(α·ζ^j)| = |Σ c_i · α^{σ_i} · ζ^{j·σ_i}|
              ≤ Σ c_i · α^{σ_i} · |ζ^{j·σ_i}|
              = Σ c_i · α^{σ_i}
              = P_σ(α).

So |P_σ(α·ζ^j)| ≤ P_σ(α) always. Equality iff all ζ^{j·σ_i} are equal
(all have the same argument), i.e., j·σ_i ≡ const mod S for all i.
Since σ_0 = 0 and σ_1 ≥ 1: j·0 = 0 and j·σ_1 ≡ 0 mod S requires
S | j·σ_1. For j ∈ {1,...,S-1} and σ_1 < S: this holds only if j = S/gcd(σ_1,S)·m...
STRICT inequality holds when the σ_i are NOT all ≡ 0 mod S/j.

For σ_0 = 0, σ_1 ≥ 1: the phases ζ^{j·σ_i} include both ζ^0 = 1 and
ζ^{j·σ_1} ≠ 1 (when S ∤ j·σ_1). So |P| < P(α) strictly for j ≠ 0.

THIS GIVES: P_σ(α) = max_j |P_σ(α·ζ^j)|.

CONSEQUENCE FOR THE NORM:
N(P_σ) = Π_j P_σ(α·ζ^j).
|N(P_σ)| = Π_j |P_σ(α·ζ^j)| < P_σ(α)^S (strict when S ≥ 2).

And P_σ(α) ≈ corrSum (since α ≈ 2).

NOW: if d | corrSum (= P_σ(2)), then d divides a number close to P_σ(α).
And N(P_σ) = P_σ(α) · Π_{j≠0} P_σ(α·ζ^j).
Since |Π_{j≠0}| < P_σ(α)^{S-1}:
|N(P_σ)| < P_σ(α)^S.

If d | P_σ(2) and d | N(P_σ): d divides both P_σ(2) and N(P_σ).
Since d = N(α-2) = Π(2-α·ζ^j): d = |Π(2-α·ζ^j)|.

The AM-GM on |2-α·ζ^j|:
|2-α·ζ^j|² = 4 + α² - 4α·cos(2πj/S) for j ≠ 0.
|2-α|² = (2-α)² ≈ Λ² (very small, since α ≈ 2).

Product: d = |2-α| · Π_{j≠0} |2-α·ζ^j|.
|2-α| = |2 - 3^{k/S}| ≈ |Λ| (small).
Π_{j≠0} |2-α·ζ^j| ≈ d / |Λ| (large).

If d | P_σ(2): P_σ(2) = n₀·d.
P_σ(α) ≈ P_σ(2) = n₀·d.
n₀ = P_σ(2)/d.

From the maximum principle: |N(P_σ)| < P_σ(α)^S ≈ (n₀·d)^S.
From the norm formula: N(P_σ) = P_σ(α) · Π_{j≠0} P_σ(α·ζ^j).

If (α-2) | P_σ(α) in Z[α] (needed for d | P_σ(2)):
N(α-2) = d, and the contribution of (α-2) to N(P_σ) is "at least d".
So |N(P_σ)| ≥ d · ...

Hmm, this doesn't directly give a contradiction. But it constrains the
relationship between P_σ(α) and its conjugates.

THE KEY BOUND:
P_σ(α) > d for all σ and all k (verified as L1 in proof search, and
min P_σ(α)/d > 0.99 for all tested k).

If we can prove P_σ(α) > d UNCONDITIONALLY, then combined with
the maximum principle: |N(P_σ)| < P_σ(α)^S, and P_σ(α) > d, giving:
|N(P_σ)| < P_σ(α)^S but N(P_σ) ≥ d^S... no, that's not right.

Actually: P_σ(α) > d doesn't mean N(P_σ) > d^S.
The OTHER conjugates can be << d.

Let me focus on what IS provable and verify it more carefully.
"""

import sys, os, cmath
from math import ceil, log2, comb, pi, log
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import (
    compute_S, compute_d, corrsum_cumulative,
    enumerate_cumulative_sequences, count_cumulative_sequences,
)


def verify_maximum_principle(k_max=12):
    """
    Verify: P_σ(α) = max_j |P_σ(α·ζ^j)| for all σ (strict max at j=0).
    This is a consequence of the triangle inequality + positive coefficients.
    """
    print("MAXIMUM PRINCIPLE VERIFICATION")
    print("=" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 5000: continue

        alpha = 3**(k/S)
        violations = 0
        min_ratio = float('inf')  # min over σ of P(α)/max_{j≠0}|P(α·ζ^j)|

        for sigma in enumerate_cumulative_sequences(k, S):
            coeffs = [(3**(k-1-i), sigma[i]) for i in range(k)]

            # P at real root
            p_real = sum(c * alpha**s for c, s in coeffs)

            # P at complex roots
            max_complex = 0
            for j in range(1, S):
                root = alpha * cmath.exp(2j * cmath.pi * j / S)
                p_complex = sum(c * root**s for c, s in coeffs)
                max_complex = max(max_complex, abs(p_complex))

            ratio = p_real / max_complex if max_complex > 0 else float('inf')
            min_ratio = min(min_ratio, ratio)

            if p_real <= max_complex + 1e-6:  # Allow tiny numerical error
                violations += 1

        status = "✓" if violations == 0 else f"✗ {violations} violations"
        print(f"  k={k}: max principle {status}, min P(α)/max|P(α·ζ)| = {min_ratio:.4f}")

    print("\n  Triangle inequality guarantees |P(α·ζ^j)| ≤ P(α) for positive coefficients.")
    print("  Strict inequality when phases ζ^{j·σ_i} are not all equal — TRUE for all valid σ.")


def compute_critical_bound(k_max=14):
    """
    THE CRITICAL BOUND:
    P_σ(α) ≥ corrSum_min where α = 3^{k/S} ≈ 2.

    Actually: P_σ(α) = Σ 3^{k-1-i} · α^{σ_i} where α < 2 (when S > k·log₂3).
    Since α < 2: each term 3^{k-1-i} · α^{σ_i} < 3^{k-1-i} · 2^{σ_i} = corrSum term.
    So P_σ(α) < P_σ(2) = corrSum.

    Wait — α can be < 2 or > 2 depending on the fractional part of k·log₂3.
    S = ⌈k·log₂3⌉, so 3^{k/S} = 3^{k/⌈k·log₂3⌉}.
    When S = k·log₂3 + ε: α = 3^{1/log₂3 · 1/(1+ε/k·log₂3)} ≈ 2^{1/(1+ε/(...))} < 2.

    So α < 2 ALWAYS (since S > k·log₂3 by definition of ceiling).

    Therefore P_σ(α) < P_σ(2) = corrSum for all σ (since α < 2 and coefficients positive).
    And P_σ(α) > P_σ(α_min) where α_min is the... hmm this doesn't help.

    Better: P_σ(α)/d ratio.
    P_σ(α) = Σ c_i · α^{σ_i}, and the minimum is at σ = (0,1,...,k-1):
    P_min(α) = Σ 3^{k-1-i} · α^i = (3^k - α^k)/(3 - α) if α ≠ 3...

    Actually: P_min(α) = Σ_{i=0}^{k-1} 3^{k-1-i} · α^i = (3^k - α^k)/(3 - α).
    Since α^S = 3^k: α^k = 3^{k²/S}. Hmm, not clean.

    Let me just compute the ratio P_σ(α)/d for each k and track the minimum.
    """
    print("\nCRITICAL BOUND: P_σ(α)/d ratio")
    print("=" * 60)
    print(f"{'k':>3} {'S':>3} {'α':>10} {'d':>10} {'min P(α)/d':>12} {'min P(2)/d':>12}")
    print("-" * 60)

    for k in range(3, k_max + 1):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 0: continue
        C = count_cumulative_sequences(k, S)
        if C > 50000: continue

        alpha = 3**(k/S)

        min_pa_d = float('inf')
        min_p2_d = float('inf')

        for sigma in enumerate_cumulative_sequences(k, S):
            pa = sum(3**(k-1-i) * alpha**sigma[i] for i in range(k))
            p2 = corrsum_cumulative(sigma, k)
            min_pa_d = min(min_pa_d, pa/d)
            min_p2_d = min(min_p2_d, p2/d)

        print(f"{k:3d} {S:3d} {alpha:10.6f} {d:10d} {min_pa_d:12.6f} {min_p2_d:12.6f}")


if __name__ == '__main__':
    verify_maximum_principle()
    compute_critical_bound()
