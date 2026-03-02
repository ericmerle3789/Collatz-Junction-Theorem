#!/usr/bin/env python3
"""
SP10 L10.A — Effective ρ Bound: Our Own Formula
================================================

THESIS: We don't need BGK effectivity. We can build a DIRECT
effective bound on ρ(p) = max_{c≠0} |Σ_{h∈⟨2⟩} ω^{ch}| / m
for the specific subgroup H = ⟨2⟩ in F_p*.

KEY OBSERVATIONS:
1. H = ⟨2⟩ = {1, 2, 4, ..., 2^{m-1}} where m = ord_p(2)
2. The exponential sum is: S_c = Σ_{j=0}^{m-1} ω^{c·2^j}
3. This is a LACUNARY exponential sum (powers of 2)
4. The Weil bound gives |S_c| ≤ √p for general characters
5. But we need a bound relative to m, not √p

APPROACH: DIRECT COMPUTATION via the generating function
S_c = Σ_{j=0}^{m-1} exp(2πi c·2^j / p)

This is a sum of unit vectors on the circle. The cancellation
comes from the RAPID GROWTH of 2^j, which causes the phases
c·2^j/p to "spread out" over the circle.

LEMMA (Our Own):
For m ≥ 4 and p ≥ m^4, c ≠ 0 mod p:
  |S_c| ≤ m - m / (2 log₂(p))

This gives ρ ≤ 1 - 1/(2 log₂(p)) < 1 - 1/(8 log₂(m))
(using p ≥ m^4, so log₂(p) ≥ 4 log₂(m))

PROOF STRATEGY:
The sum S_c = Σ ω^{c·2^j} can be analyzed via the
distribution of {c·2^j / p} mod 1.

By the three distances theorem applied to the doubling map,
consecutive terms 2^j mod p and 2^{j+1} mod p are "spread"
such that the phases don't all align.

ANTI-HALLUCINATION:
- Verify the bound numerically for known cases
- Cross-check with Weil bound and DI_B values from L9
- Flag any case where our bound is WORSE than the Weil bound
"""

import math
import cmath
import sys
from sympy import isprime
from sympy.ntheory import n_order

sys.set_int_max_str_digits(100000)


def exact_rho(p, m):
    """Compute exact ρ(p) = max_{c≠0} |S_c| / m."""
    omega = cmath.exp(2j * cmath.pi / p)
    max_abs = 0
    for c in range(1, p):
        s = sum(omega ** (c * pow(2, j, p)) for j in range(m))
        abs_s = abs(s)
        if abs_s > max_abs:
            max_abs = abs_s
    return max_abs / m


def fast_rho_max(p, m, sample_size=None):
    """
    Compute ρ(p) by evaluating |S_c|/m for c = 1,...,p-1.
    For large p, sample random c values.
    """
    omega = cmath.exp(2j * cmath.pi / p)

    # Precompute 2^j mod p
    powers = []
    val = 1
    for j in range(m):
        powers.append(val)
        val = (val * 2) % p

    max_abs = 0
    max_c = 0

    if sample_size is None or p <= sample_size:
        candidates = range(1, p)
    else:
        import random
        random.seed(42)
        candidates = random.sample(range(1, p), min(sample_size, p - 1))

    for c in candidates:
        s = sum(cmath.exp(2j * cmath.pi * (c * h % p) / p)
                for h in powers)
        abs_s = abs(s)
        if abs_s > max_abs:
            max_abs = abs_s
            max_c = c

    return max_abs / m, max_c


def our_bound_v1(p, m):
    """
    ATTEMPT 1: Bound based on equidistribution of 2^j mod p.

    The key idea: if 2^j mod p were UNIFORMLY distributed in
    [0, p-1], then S_c ≈ 0 for c ≠ 0.

    The discrepancy of the sequence {2^j/p} is bounded by the
    Erdős–Turán inequality. For the doubling map mod p:
    D_m ≤ (1/K) + Σ_{k=1}^{K} (1/k) · |Σ_{j=0}^{m-1} e^{2πikj·2/p}| / m

    But this is circular (we're bounding the sum using the sum).

    SIMPLER APPROACH: Geometric series argument.
    S_c = Σ_{j=0}^{m-1} ω^{c·2^j}

    For consecutive terms: ω^{c·2^{j+1}} = (ω^{c·2^j})^2
    So the phases are iterates of z → z^2 on the unit circle.

    If z_0 = ω^c = e^{2πic/p}, then z_j = z_0^{2^j} = ω^{c·2^j}.

    The key: |z_j - z_{j+1}| = |z_j| · |1 - z_j| = |1 - z_j|
    (since |z_j| = 1).

    If z_j is not close to 1, then z_j and z_{j+1} are spread out.
    The number of j where z_j is "close to 1" is limited by
    the order structure.
    """
    # The bound ρ ≤ 1 - 1/(2·log₂(p)) is heuristic.
    # Let's verify it and try to prove it.
    log2_p = math.log2(p)
    bound = 1 - 1 / (2 * log2_p)
    return bound


def our_bound_v2(p, m):
    """
    ATTEMPT 2: Van der Corput-type bound.

    By Weyl differencing (van der Corput inequality):
    |S_c|^2 ≤ m + 2 Σ_{1≤h<m} |Σ_{j=0}^{m-1-h} ω^{c(2^{j+h} - 2^j)}|

    The inner sum: Σ_j ω^{c·2^j·(2^h - 1)}
    = S_{c·(2^h-1)}  (another exponential sum of same type!)

    This seems circular again, but we can extract information:
    For h such that gcd(2^h - 1, p) > 1, i.e., p | (2^h - 1),
    this means h ≥ m (since m = ord_p(2)).
    So for 1 ≤ h < m: gcd(2^h - 1, p) = 1, and the new
    "frequency" c' = c·(2^h - 1) mod p runs through nonzero
    values.

    KEY INSIGHT: The M different values c·(2^h - 1) mod p
    for h = 1, ..., m-1 are ALL DISTINCT (since 2^h are
    distinct mod p and c ≠ 0).

    By Parseval's identity:
    Σ_{c=1}^{p-1} |S_c|^2 = m·(p-1)

    So the AVERAGE |S_c|^2 = m.
    This means the average ρ_c = |S_c|/m satisfies:
    avg(ρ_c^2) = 1/m

    For the MAXIMUM ρ = max ρ_c, we need more work.
    But if ρ = 1 - ε, then:
    m·(1-ε)^2 ≤ Σ |S_c|^2 / (p-1) → contradiction for small ε

    Wait, that's not quite right. Let me think more carefully.
    """
    # Parseval gives: Σ_{c=0}^{p-1} |S_c|^2 = m·p
    # (S_0 = m, so |S_0|^2 = m^2)
    # Σ_{c=1}^{p-1} |S_c|^2 = mp - m^2 = m(p-m)
    # Average for c ≠ 0: |S_c|^2 = m(p-m)/(p-1)

    # If ρ = max |S_c|/m for c ≠ 0, then:
    # m^2·ρ^2 ≥ |S_c|^2 for ALL c ≠ 0
    # But also: m^2·ρ^2 ≤ max |S_c|^2

    # From Parseval: (p-1) · m^2 · ρ^2 ≥ Σ_{c≠0} |S_c|^2 = m(p-m)
    # ρ^2 ≥ (p-m) / (m(p-1))
    # ρ ≥ √((p-m)/(m(p-1)))

    # For p ≥ m^4:
    # ρ ≥ √((m^4 - m)/(m·(m^4-1))) = √((m^3-1)/(m^4-1))
    # ≈ √(1/m) = m^{-1/2}

    # This is a LOWER bound on ρ — so ρ ≥ m^{-1/2}
    # But we need an UPPER bound ρ ≤ 1 - ε!

    # The Weil bound gives: |S_c| ≤ (m-1)√p / (something)
    # Actually, the standard Weil bound for character sums gives:
    # |Σ_{j} χ(f(j))| ≤ (deg f - 1)√p
    # But our sum is not of this form.

    # For MULTIPLICATIVE characters over subgroups:
    # |S_c| = |Σ_{h ∈ H} ψ(h)| where ψ(h) = e^{2πich/p}
    # is an additive character evaluated on subgroup H.

    # Polya-Vinogradov for incomplete sums? No, H is a
    # multiplicative subgroup, not an interval.

    # KATZ BOUND: For the sum Σ_{x ∈ H} e^{2πi x/p}
    # where H is a multiplicative subgroup of order m:
    # If m ≥ p^{1/2+ε}, then |Σ| ≤ m · p^{-δ(ε)}
    # (Bourgain-Glibichuk-Konyagin, 2006)

    # But we're in Regime B where m ≤ p^{1/4}... so BGK
    # does NOT directly apply!

    # NEW IDEA: Use the DOUBLING MAP structure.
    # H = {1, 2, 4, ..., 2^{m-1}} mod p
    # This is not just any subgroup — it's the orbit of 1
    # under x → 2x.
    # The elements 2^j mod p for j = 0,...,m-1 are consecutive
    # iterates of the doubling map on Z/pZ.

    # For the doubling map, we have a well-known result:
    # The discrepancy D_N of {2^j/p : j=0,...,N-1} satisfies
    # D_N ≤ C·log(p)/√p  (for N = ord_p(2) = m)

    # If m = p (i.e., 2 is a primitive root), this gives
    # discrepancy O(log(p)/√p), which is excellent.

    # For m << p: the discrepancy of {2^j/p : j=0,...,m-1}
    # is bounded by Korobov (1958):
    # D_m ≤ C · (m/p + (log p)/p · Σ_{1≤k≤p/2} 1/(k · ||k·2^j/p||))
    # This is getting complicated.

    # PRAGMATIC BOUND: use Parseval lower bound + Weil
    rho_lower = math.sqrt((p - m) / (m * (p - 1)))
    rho_weil = math.sqrt(p) / m  # Weil-type upper bound
    return min(rho_weil, 1.0), rho_lower


def our_bound_v3_direct(p, m):
    """
    ATTEMPT 3: Direct bound using number of "aligned" phases.

    S_c = Σ_{j=0}^{m-1} e^{2πi c·2^j/p}

    Key insight: |S_c| = m iff all terms are equal, i.e.,
    c·2^j ≡ c·2^{j'} (mod p) for all j,j'.
    This means 2^j ≡ 2^{j'} (mod p), i.e., j = j' (for j,j' < m).
    So |S_c| = m only if c = 0 (mod p).

    For c ≠ 0: |S_c| < m.

    MORE PRECISELY: |S_c| = m - δ where δ > 0.
    The cancellation δ depends on how "spread out" the phases are.

    CLAIM: If m ≥ 4, then ρ ≤ 1 - 1/m^2.
    (This would give k_crit improvement by factor m.)

    PROOF ATTEMPT: Among m unit vectors e^{iθ_j} on the circle,
    the maximum of |Σ e^{iθ_j}|/m equals 1 iff all θ_j are equal.
    If at least two θ_j differ by at least 2π/m^2, then
    |Σ e^{iθ_j}| ≤ m - 2sin^2(π/m^2)/m ≈ m - 2π^2/m^5

    Actually this is too weak. Let me think differently.

    The phases θ_j = 2πc·2^j/p mod 2π.
    If θ_j are in arithmetic progression or geometric progression,
    the sum can be computed exactly.

    For GEOMETRIC: θ_{j+1} = 2·θ_j (mod 2π·something)
    This is the doubling map on the circle.

    ERGODIC THEORY: The doubling map x → 2x mod 1 is ergodic
    on [0,1). For an ergodic system, the Birkhoff average
    (1/m) Σ f(T^j(x)) → ∫ f dx as m → ∞
    for almost all x.

    For f(x) = e^{2πix} and T(x) = 2x mod 1:
    ∫ e^{2πix} dx = 0
    So (1/m) S_c → 0 for almost all starting points c/p.

    But "almost all" in the ergodic theorem is measure-theoretic.
    We need bounds for SPECIFIC starting points.

    QUANTITATIVE ERGODIC THEOREM: By the spectral gap of
    the doubling map (which is 1/2 on L^2), we get:
    |(1/m) S_c| ≤ C · (1/2)^{m/something}?

    NO - the spectral gap of the doubling map on Z/pZ is not
    the same as on [0,1). On Z/pZ with the doubling map
    x → 2x, the spectral gap is controlled by ord_p(2) = m.

    ACTUAL QUANTITATIVE BOUND:
    For the sum S_c = Σ_{j=0}^{m-1} e^{2πi c·2^j/p}:

    Katz (1989) showed that if gcd(c, p) = 1 and 2 has
    order m in (Z/pZ)*, then for any multiplicative character
    χ of order d dividing m:
    |Σ_{j=0}^{m-1} χ(j) e^{2πi c·2^j/p}| ≤ (d-1)√p

    For the trivial character (χ = 1):
    |S_c| ≤ (m-1)·√p / m ??? No, this doesn't help.

    Let me try a completely different approach.
    """
    # Direct computation for small cases
    if p <= 10000 and m <= 200:
        rho, _ = fast_rho_max(p, m)
        return rho
    else:
        # Weil-type bound
        return min(math.sqrt(p) / m, 1.0)


def test_effective_bounds():
    """Test various bounds against exact computations."""
    print("=" * 72)
    print("SP10 L10.A — EFFECTIVE ρ BOUNDS")
    print("=" * 72)

    # Test primes from L9 data (known cases)
    test_cases = [
        # (p, m, known_regime, description)
        (31, 5, "W", "p=31, m=5 (L9 debug case)"),
        (127, 7, "DI_B", "p=127=M7, m=7 (DI_B boundary)"),
        (8191, 13, "DI_B", "p=8191=M13, m=13 (K_MAX prime)"),
        (131071, 17, "DI_B", "p=131071=M17, m=17"),
        (524287, 19, "DI_B", "p=524287=M19, m=19"),
        (7, 3, "W", "p=7, m=3 (worst case SP5)"),
        (13, 12, "W", "p=13, m=12 (q3 example)"),
        (257, 8, "DI_B", "p=257, m=8 (L9 debug case)"),
    ]

    print(f"\n{'p':>10} {'m':>5} {'regime':>8} {'ρ_exact':>10} "
          f"{'√p/m':>10} {'1-1/m':>10} {'1-1/2logp':>10}")
    print("-" * 72)

    for p, m, regime, desc in test_cases:
        rho_exact, max_c = fast_rho_max(p, m)
        weil = math.sqrt(p) / m
        trivial = 1 - 1 / m
        our_v1 = our_bound_v1(p, m)

        print(f"{p:>10} {m:>5} {regime:>8} {rho_exact:>10.6f} "
              f"{weil:>10.6f} {trivial:>10.6f} {our_v1:>10.6f}")

    # Now test with LARGER primes to see patterns
    print(f"\n\nPATTERN SEARCH: ρ for larger m")
    print("-" * 72)
    print(f"{'m':>5} {'p':>15} {'p/m^4':>12} {'ρ':>10} "
          f"{'√p/m':>10} {'1-1/m':>10}")
    print("-" * 72)

    # Find primes with specific m values
    for target_m in [5, 7, 10, 13, 15, 20, 25, 30]:
        # Find smallest prime p with ord_p(2) = target_m
        # p ≡ 1 (mod m) is necessary
        found = False
        for candidate in range(target_m + 1, 100000):
            if candidate % target_m != 1:
                continue
            if not isprime(candidate):
                continue
            try:
                actual_m = n_order(2, candidate)
                if actual_m == target_m:
                    p = candidate
                    rho, _ = fast_rho_max(p, target_m,
                                           sample_size=2000)
                    weil = math.sqrt(p) / target_m
                    trivial = 1 - 1 / target_m
                    ratio = p / target_m ** 4
                    regime = "B" if ratio >= 1 else "A"

                    print(f"{target_m:>5} {p:>15} {ratio:>12.4f} "
                          f"{rho:>10.6f} {weil:>10.6f} "
                          f"{trivial:>10.6f}  [{regime}]")
                    found = True
                    break
            except Exception:
                continue
        if not found:
            print(f"{target_m:>5} {'(not found)':>15}")

    # KEY QUESTION: For primes in Regime B (p >= m^4),
    # is ρ actually smaller than 1 - 1/m?
    print(f"\n\nCRITICAL TEST: Regime B primes (p >= m^4)")
    print("-" * 72)
    print(f"{'m':>5} {'p':>15} {'p/m^4':>12} {'ρ':>10} "
          f"{'1-1/m':>10} {'gap':>10}")
    print("-" * 72)

    for target_m in [3, 4, 5, 6, 7, 8]:
        threshold = target_m ** 4
        # Find primes p >= m^4 with ord_p(2) = m
        for candidate in range(threshold, threshold + 50000):
            if candidate % target_m != 1:
                continue
            if not isprime(candidate):
                continue
            try:
                actual_m = n_order(2, candidate)
                if actual_m == target_m:
                    p = candidate
                    rho, max_c = fast_rho_max(p, target_m)
                    trivial = 1 - 1 / target_m
                    gap = trivial - rho
                    ratio = p / target_m ** 4

                    print(f"{target_m:>5} {p:>15} {ratio:>12.4f} "
                          f"{rho:>10.6f} {trivial:>10.6f} "
                          f"{gap:>10.6f}")
                    break
            except Exception:
                continue


def explore_our_own_bound():
    """
    ATTEMPT 4: THE FILTER CASCADE (Zeno approach).

    Instead of proving ρ < 1 - ε globally, we show that
    IF N = 1 (one candidate k₀ survives all filters),
    THEN k₀ must satisfy additional constraints that
    progressively eliminate it.

    Filter 4a: k₀ = n₃·j₀ where j₀ is the UNIQUE solution
    of the Beatty congruence. This means:
    ⌈n₃·j₀·θ⌉ ≡ L·j₀ (mod m)

    Since θ is transcendental and n₃·j₀ is bounded by k_crit,
    the fractional part {n₃·j₀·θ} is governed by the theory
    of continued fractions.

    Filter 4b: k₀ must satisfy p | d(k₀) = 2^{S₀} - 3^{k₀}.
    Since 2^{S₀} ≡ 3^{k₀} (mod p) and S₀ = ⌈k₀θ⌉:
    2^{⌈k₀θ⌉} ≡ 3^{k₀} (mod p)

    Writing k₀ = n₃·j₀:
    2^{⌈n₃·j₀·θ⌉} ≡ (3^{n₃})^{j₀} ≡ (2^L)^{j₀} = 2^{Lj₀} (mod p)

    So: ⌈n₃·j₀·θ⌉ ≡ L·j₀ (mod m)  ... which is the Beatty cond!

    This means: the Beatty condition IS the divisibility condition.
    Filter 4b adds NOTHING new.

    Filter 4c: SIZE constraint.
    If k₀ = n₃·j₀, then k₀ ≤ k_crit ≤ 3m·ln(p) (Lemma 2).
    Also k₀ ≥ 69 (by assumption).
    So n₃·j₀ ∈ [69, 3m·ln(p)].
    If n₃ is large (close to (p-1)/m), then j₀ must be small.

    Filter 4d: DIOPHANTINE constraint.
    ⌈n₃·j₀·θ⌉ ≡ L·j₀ (mod m)
    Let ε = n₃·j₀·θ - ⌊n₃·j₀·θ⌋ be the fractional part.
    Then S₀ = ⌈n₃·j₀·θ⌉ = ⌊n₃·j₀·θ⌋ + 1 (when ε > 0).
    The congruence becomes:
    ⌊n₃·j₀·θ⌋ + 1 ≡ L·j₀ (mod m)

    Since θ is transcendental, the number ⌊n₃·j₀·θ⌋ has
    specific Diophantine properties that can be exploited.

    In particular, by Baker's theorem on linear forms in logarithms:
    |n₃·j₀·θ - integer| ≥ exp(-C·log(n₃·j₀)·loglog(n₃·j₀))

    This gives a LOWER BOUND on ε = {n₃·j₀·θ}, which translates
    to a constraint on the Beatty congruence.
    """
    print("\n" + "=" * 72)
    print("SP10 L10.B — CASCADE DE FILTRES (Approche Zénon)")
    print("=" * 72)

    # The key computation: for each hypothetical Regime B prime,
    # what constraints does the unique k₀ satisfy?

    # Let's compute for small m values what k₀ would need to be
    print(f"\n  Pour chaque m, calcul des contraintes sur k₀:")
    print(f"  (Regime B: p >= m^4, unique candidat j₀)")
    print()

    theta = math.log2(3)

    for m in range(4, 20):
        p_min = m ** 4
        k_crit_max = 3 * m * math.log(p_min + 1)
        # n₃ minimal pour regime B non-generique: n₃ ≥ 2
        # j₀ minimal: j₀ ≥ ceil(69/n₃)
        # j₀ maximal: j₀ ≤ floor(k_crit/n₃) ≤ floor(k_crit/2)

        j_max = k_crit_max / 2  # worst case n₃ = 2
        n_candidates = int(j_max)

        # The Beatty congruence for each j:
        # ⌈n₃·j·θ⌉ ≡ L·j (mod m)
        # L = ⌊n₃·θ⌋ + 1 (since n₃·θ is never integer for n₃ < p)

        # For n₃ = 2: L = ⌈2θ⌉ = ⌈3.170⌉ = 4
        # Congruence: ⌈2j·θ⌉ ≡ 4j (mod m)
        # i.e., ⌈2jθ⌉ mod m = (4j) mod m

        n3 = 2
        L = math.ceil(n3 * theta)
        matches = 0
        for j in range(max(1, math.ceil(69 / n3)),
                        min(int(k_crit_max / n3) + 1, 10000)):
            k = n3 * j
            S = math.ceil(k * theta)
            if S % m == (L * j) % m:
                matches += 1

        print(f"  m={m:2d}: p_min={p_min:>8d}, k_crit≤{k_crit_max:.0f}, "
              f"n₃=2→ L={L}, j∈[{math.ceil(69/n3)}, "
              f"{int(k_crit_max/n3)}], "
              f"matches={matches}")

    # KEY FINDING: for the Beatty congruence with irrational θ,
    # the THREE DISTANCES THEOREM guarantees at most 1 match
    # when J < m. But can we get 0?

    print(f"\n  ANALYSE FINE: pourquoi le match unique est exclu")
    print(f"  (Filtre 4d: contrainte de Baker)")
    print()

    # If k₀ = n₃·j₀ is the unique solution, then
    # 2^{S₀} ≡ 3^{k₀} (mod p) where p ≥ m^4 ≥ (ord_p(2))^4
    #
    # Baker's theorem: |2^a - 3^b| ≥ exp(-C₁ · log(a)·log(b))
    # for a, b ≥ 2 (Laurent-Mignotte-Nesterenko 1995)
    #
    # But d(k₀) = 2^{S₀} - 3^{k₀} ≥ 1 (otherwise no primes to divide)
    # AND p | d(k₀), so p ≤ d(k₀)
    #
    # Baker gives: d(k₀) = |2^{S₀} - 3^{k₀}| ≥ exp(-C·log(S₀)·log(k₀))
    #
    # For k₀ ≤ k_crit ≤ 3m·ln(p):
    # d(k₀) ≥ exp(-C·log(3m·ln(p))·log(3m·ln(p)))
    #        = exp(-C·(log(m) + loglog(p) + const)^2)
    #
    # But p ≤ d(k₀), so:
    # p ≤ d(k₀)... wait, d(k₀) = 2^{S₀} - 3^{k₀} which grows
    # exponentially with k₀. So p can be very large.
    #
    # The Baker bound says d(k₀) ≥ exp(-poly(log S₀, log k₀))
    # which is ≥ 1 for S₀ ≥ 2 (since d(k₀) is a positive integer).
    # Not very useful directly.
    #
    # BUT: v_p(d(k₀)) is what matters. If p | d(k₀), what is
    # the p-adic valuation?
    #
    # By Yu (2007) p-adic Baker:
    # v_p(2^a - 3^b) ≤ C₂ · log(a)·log(b)·log(p) / (log(2)·log(3))
    #
    # For our case a = S₀, b = k₀:
    # v_p(d(k₀)) ≤ C₂ · log(S₀)·log(k₀)·log(p)
    #
    # This means: p^{v_p(d(k₀))} ≤ p^{C₂·log(S₀)·log(k₀)·log(p)}
    # which constrains how divisible d(k₀) is by p.
    #
    # In particular: v_p(d(k₀)) = 1 for "most" cases
    # (confirmed empirically in L9).

    print(f"  Baker p-adique (Yu 2007):")
    print(f"  v_p(d(k)) ≤ C₂ · log(S)·log(k)·log(p)")
    print(f"  Pour k₀ ≤ 3m·ln(p) et p ≥ m^4:")
    for m in [4, 5, 7, 10, 15, 20]:
        p = m ** 4
        k_crit = 3 * m * math.log(p)
        S_crit = k_crit * theta
        baker_bound = 50 * math.log(S_crit) * math.log(k_crit) * math.log(p)
        print(f"    m={m:2d}: v_p ≤ {baker_bound:.1f} "
              f"(k_crit={k_crit:.0f})")

    print(f"\n  CONCLUSION PARTIELLE:")
    print(f"  Baker ne donne pas v_p = 0 directement.")
    print(f"  Mais il contraint v_p ≤ O(polylog).")
    print(f"  Le filtre suivant (4e) exploite cela...")


def main():
    test_effective_bounds()
    explore_our_own_bound()

    print("\n" + "=" * 72)
    print("SYNTHESE L10.A + L10.B")
    print("=" * 72)
    print("""
  1. BOUNDS TESTEES:
     - Weil: ρ ≤ √p/m (trop faible en regime B car √p/m > 1)
     - Triviale: ρ ≤ 1 - 1/m (ce qu'on utilise actuellement)
     - Notre v1: ρ ≤ 1 - 1/(2·log₂(p)) (heuristique, à prouver)
     - Parseval: ρ ≥ √((p-m)/(m(p-1))) (borne INFERIEURE)

  2. CASCADE DE FILTRES:
     - Filtre 4a: k₀ = n₃·j₀ (structure de groupe)
     - Filtre 4b: Beatty ≡ divisibilité (pas de gain)
     - Filtre 4c: Contrainte de taille k₀ ∈ [69, k_crit]
     - Filtre 4d: Baker p-adique → v_p ≤ polylog
     - Filtre 4e: [À CONSTRUIRE] Contrainte Diophantienne
       sur {n₃·j₀·θ} via théorie des fractions continues

  3. PISTE LA PLUS PROMETTEUSE:
     Filtre 4e — la transcendance de θ = log₂(3) impose
     que |n₃·j₀·θ - entier| n'est jamais "trop petit",
     ce qui contraint le résidu S₀ mod m.
     Combiné avec la congruence de Beatty, cela pourrait
     exclure le candidat unique.
    """)


if __name__ == "__main__":
    main()
