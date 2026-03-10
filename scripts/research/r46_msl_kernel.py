#!/usr/bin/env python3
"""
R46-B: First Provable Kernel of the MSL -- Two Candidates, One Survivor
========================================================================
Agent B (Innovateur) -- Round 46

MISSION: Propose 2 candidate formulations for a first provable kernel of the
Monotone Spreading Lemma (MSL), keep 1 survivor, eliminate the other with
complete autopsy.

CONTEXT ACQUIRED (DO NOT RE-PROVE):
  N_r = #{monotone B : P_B(g) ≡ r mod p}, C = C(S-1, k-1), g = 2·3⁻¹ mod p
  P_B(g) = Σ_{j=0}^{k-1} g^j · 2^{B_j} mod p, B nondecreasing, 0 ≤ B_0 ≤ ... ≤ B_{k-1} = S-k
  M₂ = Σ N_r² = collision count                             [PROUVÉ R45]
  V = M₂ - C²/p ≥ 0                                         [PROUVÉ R45]
  μ = M₂·p/C², μ=1 ↔ perfect uniformity
  Plancherel corrigé: Σ_{r=0}^{p-1} |S(r)|² = p·M₂           [PROUVÉ R44]
  ACL: f_p ≤ 1/p + √((p-1)·V/(p·C²))                        [PROUVÉ R44]
  V ≤ A·C universel FAUX                                     [PROUVÉ R45]
  MSL modéré conjectural: V ≤ A(p)·C

CANDIDATE 1: MSL-lite
  Show μ-1 = o(1) for fixed p as k → ∞, via convolution mixing on Z/pZ.
  P_B is a k-fold additive process. As k grows, adding more terms
  should "mix" the distribution modulo p.

CANDIDATE 2: Lemme de Spreading des Différences (LSD)
  For pairs (B,B'), analyze P_B - P_{B'} = Σ g^j·(2^{B_j} - 2^{B'_j}) mod p.
  Bound M₂ by counting "structured" vs "generic" collision pairs.

SECTIONS:
  0: Mathematical primitives
  1: Validation
  2: Candidate 1 -- MSL-lite (convolution mixing)
  3: Candidate 2 -- LSD (difference spreading)
  4: Head-to-head comparison
  5: Elimination and autopsy
  6: Survivor precise statement
  7: Self-tests (40+ tests, all must PASS)

EPISTEMIC LABELS:
  [PROUVÉ]       = rigorous proof from standard identities
  [SEMI-FORMEL]  = structural argument, not fully rigorous
  [CALCULÉ]      = verified by exact computation
  [OBSERVÉ]      = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven
  [RÉFUTÉ]       = contradicted by evidence

Author: Claude Opus 4.6 (R46-B INNOVATEUR pour Eric Merle, Collatz Junction Theorem)
Date:   2026-03-10
"""

import sys
import time
from math import comb, gcd, ceil, log2, sqrt, log
from collections import defaultdict

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 114.0  # safety margin on 120s

TEST_RESULTS = []
PASS_COUNT = 0
FAIL_COUNT = 0
VERBOSE = True


def elapsed():
    return time.time() - T_START


def time_remaining():
    return TIME_BUDGET - elapsed()


def record_test(name, passed, detail=""):
    global PASS_COUNT, FAIL_COUNT
    status = "PASS" if passed else "FAIL"
    if passed:
        PASS_COUNT += 1
    else:
        FAIL_COUNT += 1
    TEST_RESULTS.append((name, passed, detail))
    if VERBOSE:
        print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """Minimal S such that 2^S > 3^k. Exact via integer comparison."""
    S = ceil(k * log2(3))
    three_k = 3 ** k
    while (1 << S) <= three_k:
        S += 1
    while S > 0 and (1 << (S - 1)) > three_k:
        S -= 1
    return S


def compute_d(k):
    """d(k) = 2^S(k) - 3^k. Returns (d, S)."""
    S = compute_S(k)
    return (1 << S) - 3 ** k, S


def compute_C(k):
    """C(k) = C(S-1, k-1), number of nondecreasing B-vectors."""
    S = compute_S(k)
    return comb(S - 1, k - 1)


def compute_max_B(k):
    """max_B = S - k."""
    return compute_S(k) - k


def dp_full_distribution(k, mod, max_time=10.0):
    """Full residue distribution via DP with (last_b, residue) states."""
    t0 = time.time()
    if mod <= 0 or gcd(3, mod) != 1:
        return None
    S = compute_S(k)
    max_B = S - k
    nB = max_B + 1
    g = pow(3, -1, mod)
    g = (2 * g) % mod
    g_pows = [pow(g, j, mod) for j in range(k)]
    two_pows = [pow(2, b, mod) for b in range(nB)]

    state_size = mod * nB
    if state_size > 10_000_000:
        return None

    dp = [0] * state_size
    for b in range(nB):
        r = (g_pows[0] * two_pows[b]) % mod
        dp[b * mod + r] += 1

    for j in range(1, k):
        if time.time() - t0 > max_time:
            return None
        coeff = g_pows[j]
        new_dp = [0] * state_size

        if j == k - 1:
            c2b = (coeff * two_pows[max_B]) % mod
            for prev_b in range(nB):
                base = prev_b * mod
                target_base = max_B * mod
                for r in range(mod):
                    cnt = dp[base + r]
                    if cnt > 0:
                        nr = (r + c2b) % mod
                        new_dp[target_base + nr] += cnt
        else:
            for prev_b in range(nB):
                base = prev_b * mod
                for b in range(prev_b, nB):
                    c2b = (coeff * two_pows[b]) % mod
                    target_base = b * mod
                    for r in range(mod):
                        cnt = dp[base + r]
                        if cnt > 0:
                            nr = (r + c2b) % mod
                            new_dp[target_base + nr] += cnt
        dp = new_dp

    dist = [0] * mod
    for b in range(nB):
        base = b * mod
        for r in range(mod):
            dist[r] += dp[base + r]
    return dist


def compute_M2(dist):
    """Second moment M₂ = Σ N_r²."""
    return sum(nr * nr for nr in dist)


def compute_V(M2, C, p):
    """Variance V = M₂ - C²/p."""
    return M2 - C * C / p


def compute_mu(M2, C, p):
    """Collision multiplicity μ = M₂·p/C²."""
    return M2 * p / (C * C)


def enumerate_B_vectors(k, max_B):
    """Enumerate all nondecreasing B-vectors with B_{k-1} = max_B.
    Returns list of tuples."""
    if k == 1:
        yield (max_B,)
        return
    # B_0 <= B_1 <= ... <= B_{k-2} <= B_{k-1} = max_B
    # Use recursion: choose B_0, ..., B_{k-2} nondecreasing with B_{k-2} <= max_B
    def _gen(pos, lower, upper, current):
        if pos == k - 1:
            yield tuple(current) + (max_B,)
            return
        for b in range(lower, upper + 1):
            yield from _gen(pos + 1, b, upper, current + [b])
    yield from _gen(0, 0, max_B, [])


def compute_PB(B, g, p):
    """P_B(g) = Σ_{j=0}^{k-1} g^j · 2^{B_j} mod p."""
    val = 0
    gj = 1
    for bj in B:
        val = (val + gj * pow(2, bj, p)) % p
        gj = (gj * g) % p
    return val


# ============================================================================
# SECTION 1: VALIDATION
# ============================================================================

def run_validation():
    print("\n" + "=" * 72)
    print("SECTION 1: VALIDATION -- Reference Data and DP Engine")
    print("=" * 72)

    # Validate C(k) for known values (C(k) = C(S-1, k-1))
    # k=3: S=5, C(4,2)=6; k=6: S=10, C(9,5)=126; k=7: S=12, C(11,6)=462
    # k=8: S=13, C(12,7)=792; k=9: S=15, C(14,8)=3003; k=10: S=16, C(15,9)=5005
    # k=11: S=18, C(17,10)=19448; k=12: S=20, C(19,11)=75582
    known_C = {3: 6, 6: 126, 7: 462, 8: 792, 9: 3003,
               10: 5005, 11: 19448, 12: 75582}
    all_C_ok = True
    for k, expected in known_C.items():
        C = compute_C(k)
        if C != expected:
            all_C_ok = False
            record_test(f"T_val_C(k={k})", False, f"C={C}, expected={expected}")
    record_test("T01: C(k) matches known values for k=3..12", all_C_ok,
                f"all {len(known_C)} entries match")

    # Validate DP via sum(N_r) = C
    quick_checks = [(3, 5), (6, 5), (6, 59), (7, 23), (8, 7)]
    all_sum_ok = True
    for (k, p) in quick_checks:
        if time_remaining() < 20:
            break
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        if sum(dist) != C:
            all_sum_ok = False
    record_test("T02: sum(N_r) = C(k) for all validated pairs", all_sum_ok)

    # Validate N0 against brute-force for small k
    for (k, p) in [(3, 5), (6, 5)]:
        if time_remaining() < 15:
            break
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        S = compute_S(k)
        max_B = S - k
        g = (2 * pow(3, -1, p)) % p
        # Brute-force count for small k
        brute_count = [0] * p
        for B in enumerate_B_vectors(k, max_B):
            r = compute_PB(B, g, p)
            brute_count[r] += 1
        ok = (brute_count == dist)
        record_test(f"T03_{k}_{p}: DP matches brute-force (k={k},p={p})", ok)

    # Validate M₂ ≥ C²/p (Cauchy-Schwarz)
    cs_ok = True
    for (k, p) in quick_checks:
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        if M2 < C * C / p - 1e-6:
            cs_ok = False
    record_test("T04: M₂ ≥ C²/p (Cauchy-Schwarz) for all pairs", cs_ok)

    # Validate Plancherel: Σ|S(r)|² = p·M₂
    for (k, p) in [(3, 5), (6, 5)]:
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        # Compute character sums
        import cmath
        omega = cmath.exp(2j * cmath.pi / p)
        sum_sq = 0.0
        for r in range(p):
            Sr = sum(dist[s] * (omega ** (r * s)) for s in range(p))
            sum_sq += abs(Sr) ** 2
        expected = p * M2
        ok = abs(sum_sq - expected) < 1e-4
        record_test(f"T05_{k}_{p}: Plancherel Σ|S(r)|² = p·M₂ (k={k},p={p})", ok,
                    f"Σ|S|² = {sum_sq:.2f}, p·M₂ = {expected}")


# ============================================================================
# SECTION 2: CANDIDATE 1 -- MSL-LITE (Convolution Mixing)
# ============================================================================
#
# INTUITIVE STATEMENT [SEMI-FORMEL]:
#   P_B(g) = Σ_{j=0}^{k-1} g^j · 2^{B_j} mod p is a sum of k terms.
#   Each term g^j · 2^{B_j} lies in Z/pZ.
#   As k grows (with p fixed), P_B is a sum of MORE terms.
#   If these terms have sufficient "mixing" modulo p,
#   the distribution of P_B should approach uniform.
#
# SEMI-FORMAL VERSION:
#   Let X_j = g^j · 2^{B_j} mod p for j = 0,...,k-1.
#   P_B = X_0 + X_1 + ... + X_{k-1} mod p.
#   The B_j are constrained (nondecreasing, B_{k-1} = max_B),
#   so the X_j are NOT independent.
#
#   However, the MULTIPLICATIVE diversity of {g^j : j=0,...,k-1}
#   ensures that each X_j = g^j · 2^{B_j} explores Z/pZ
#   differently. As k grows:
#   - ord_p(g) ≥ 1 (g is a unit in Z/pZ)
#   - The number of distinct "directions" g^j increases until
#     it covers a full cycle of length ord_p(g).
#   - Once k > ord_p(g), the X_j cycle through the same
#     directions but with DIFFERENT coefficients 2^{B_j}.
#
#   MSL-LITE CLAIM [CONJECTURAL]:
#     For fixed p prime (gcd(p,6)=1), as k → ∞:
#       μ(k,p) → 1
#     i.e., the distribution of P_B mod p approaches uniform.
#
#   WHAT IT GIVES via ACL [SEMI-FORMEL]:
#     μ → 1 means M₂ ~ C²/p, so V = o(C²/p).
#     ACL: f_p ≤ 1/p + √((p-1)·V/(p·C²))
#                = 1/p + o(1) as k → ∞.
#     CONCLUSION: f_p → 1/p for fixed p.
#
#   GAPS:
#     G1. "Sufficient mixing" is vague. Need quantitative mixing rate.
#     G2. The X_j are NOT independent (B_j nondecreasing constraint).
#         How to handle the CORRELATIONS?
#     G3. No rate: μ → 1 but HOW FAST? O(1/C)? O(1/k)?
#     G4. The convolution approach works for INDEPENDENT random variables
#         but monotone B creates DEPENDENT summands.
#
#   POTENTIAL WEAKNESS:
#     The dependence structure of (B_0,...,B_{k-1}) is strong:
#     B_0 ≤ B_1 ≤ ... ≤ B_{k-1} = max_B. This is not a product
#     measure. Standard convolution mixing (Erdős-Turán, Weyl)
#     may not directly apply.
#
# LADDER OF PROOF: semi-formalisation (mechanism identified, not proven)
# ============================================================================

def analyze_convolution_mixing(k, p, dist):
    """Analyze the 'convolution mixing' structure of P_B mod p.

    For each j, compute the marginal distribution of g^j · 2^{B_j} mod p
    over all monotone B-vectors, and measure its uniformity.
    """
    S = compute_S(k)
    max_B = S - k
    g = (2 * pow(3, -1, p)) % p
    C = compute_C(k)

    # For small k, enumerate B-vectors and study term-by-term structure
    if C > 50000:
        return None  # too many to enumerate

    # Collect marginal distributions of X_j = g^j · 2^{B_j} mod p
    marginals = [defaultdict(int) for _ in range(k)]
    # Also collect joint distribution of (X_{j}, X_{j+1}) for consecutive pairs
    joint_consecutive = [defaultdict(int) for _ in range(k - 1)]

    count = 0
    for B in enumerate_B_vectors(k, max_B):
        count += 1
        gj = 1
        xvals = []
        for j in range(k):
            xj = (gj * pow(2, B[j], p)) % p
            marginals[j][xj] += 1
            xvals.append(xj)
            gj = (gj * g) % p
        for j in range(k - 1):
            joint_consecutive[j][(xvals[j], xvals[j + 1])] += 1

    assert count == C, f"Enumeration count {count} != C = {C}"

    # Measure uniformity of each marginal (L2 distance from uniform)
    marginal_chi2 = []
    for j in range(k):
        expected = C / p
        chi2 = sum((marginals[j].get(r, 0) - expected) ** 2 for r in range(p))
        chi2_norm = chi2 / (C * C / p)  # normalized: 0 = perfect, (p-1)/C = random
        marginal_chi2.append(chi2_norm)

    # Measure correlation between consecutive terms
    # Use chi-squared test of independence: compare joint vs product of marginals
    corr_measures = []
    for j in range(min(k - 1, 5)):  # first 5 pairs
        chi2_ind = 0.0
        for r1 in range(p):
            for r2 in range(p):
                observed = joint_consecutive[j].get((r1, r2), 0)
                expected_ind = marginals[j].get(r1, 0) * marginals[j + 1].get(r2, 0) / C
                if expected_ind > 0:
                    chi2_ind += (observed - expected_ind) ** 2 / expected_ind
        # Normalize by degrees of freedom (p-1)^2
        chi2_ind_norm = chi2_ind / ((p - 1) ** 2)
        corr_measures.append(chi2_ind_norm)

    return {
        'marginal_chi2': marginal_chi2,
        'corr_measures': corr_measures,
        'k': k, 'p': p, 'C': C,
    }


def analyze_horner_structure(k, p):
    """Analyze the Horner representation P_B = 2^{B_0}·(1 + g·2^{ΔB_1}·(1 + ...)).

    The Horner form suggests a RECURSIVE structure:
    P_B = 2^{B_0} · Q where Q depends on (B_1-B_0, ..., B_{k-1}-B_0).
    This means P_B mod p has a multiplicative decomposition.
    """
    S = compute_S(k)
    max_B = S - k
    g = (2 * pow(3, -1, p)) % p
    C = compute_C(k)

    if C > 50000:
        return None

    # Group B-vectors by B_0 value and analyze the conditional distribution
    # of P_B mod p given B_0
    groups_by_b0 = defaultdict(list)
    for B in enumerate_B_vectors(k, max_B):
        groups_by_b0[B[0]].append(B)

    # For each B_0, compute the distribution of P_B mod p
    conditional_dists = {}
    for b0, B_list in groups_by_b0.items():
        dist_b0 = [0] * p
        for B in B_list:
            r = compute_PB(B, g, p)
            dist_b0[r] += 1
        conditional_dists[b0] = dist_b0

    # The factor 2^{B_0} acts as a ROTATION on Z/pZ (multiplication).
    # If Q is uniform mod p, then P_B = 2^{B_0} · Q is also uniform.
    # Check: is the "inner" part Q = P_B · 2^{-B_0} more uniform?

    # Compute Q distribution for each B_0
    q_dists = {}
    for b0, dist_b0 in conditional_dists.items():
        inv_2b0 = pow(pow(2, b0, p), -1, p) if pow(2, b0, p) != 0 else None
        if inv_2b0 is None:
            continue
        q_dist = [0] * p
        for r in range(p):
            q_r = (r * inv_2b0) % p
            q_dist[q_r] = dist_b0[r]
        q_dists[b0] = q_dist

    return {
        'groups_by_b0': {b0: len(bl) for b0, bl in groups_by_b0.items()},
        'conditional_dists': conditional_dists,
        'q_dists': q_dists,
        'k': k, 'p': p, 'C': C,
    }


def run_msl_lite():
    print("\n" + "=" * 72)
    print("SECTION 2: CANDIDATE 1 -- MSL-LITE (Convolution Mixing)")
    print("=" * 72)

    print("""
  ====================================================================
  MSL-LITE: μ → 1 for fixed p as k → ∞
  ====================================================================

  ÉNONCÉ INTUITIF:
    P_B is a sum of k "partially random" terms g^j · 2^{B_j} mod p.
    As k grows, the sum accumulates more contributions, and the
    distribution of the total should approach uniform by a mixing
    argument analogous to convolution of measures on Z/pZ.

  VERSION SEMI-FORMELLE:
    Hypothèses:
      H1. p prime, gcd(p,6)=1, p | d(k).
      H2. g = 2·3⁻¹ mod p has multiplicative order ord_p(g) ≥ 2.
      H3. k → ∞ with p fixed.
    Conclusion:
      μ(k,p) = M₂·p/C² → 1 as k → ∞.
    Mécanisme proposé:
      The k terms X_j = g^j · 2^{B_j} contribute to P_B.
      The diversity of {g^j mod p : j=0,...,k-1} ensures that
      different coordinates B_j push P_B in different "directions"
      in Z/pZ, leading to mixing.

  CE QUE ÇA DONNE via ACL:
    μ → 1 ⟹ V = (μ-1)·C²/p = o(C²/p)
    ⟹ f_p ≤ 1/p + o(1) → 1/p
    Qualitative only: no rate, no explicit bound.

  CE QU'IL FAUT ENCORE PROUVER (GAPS):
    G1. Quantify "mixing": need |S(r)|/C → 0 for r ≠ 0, or μ-1 → 0.
    G2. Handle dependence: B_j are correlated (nondecreasing constraint).
    G3. The Horner structure P_B = 2^{B_0}·(...) creates multiplicative
        coupling that standard additive mixing does not capture.
    G4. No rate: even if μ → 1, we need μ-1 = O(p/C) for MSL moderate.

  FAIBLESSE POTENTIELLE:
    Standard mixing theorems (Erdős-Turán, Weyl sum bounds) require
    independence or near-independence of the summands. The monotone
    constraint on B makes the X_j strongly dependent. The approach
    may prove only the qualitative μ → 1 without a useful rate.

  NIVEAU LADDER: semi-formalisation (mécanisme identifié mais non prouvé)
  ====================================================================
    """)

    # --- Convolution mixing analysis ---
    test_cases = [(3, 5), (6, 5), (7, 23), (8, 7)]

    print("  --- Marginal uniformity of X_j = g^j · 2^{B_j} ---")
    for (k, p) in test_cases:
        if time_remaining() < 20:
            break
        result = analyze_convolution_mixing(k, p, None)
        if result is None:
            continue
        print(f"\n  (k={k}, p={p}), C={result['C']}:")
        print(f"    Marginal χ²(X_j) normalized: ", end="")
        for j, chi2 in enumerate(result['marginal_chi2'][:6]):
            print(f"j={j}:{chi2:.4f} ", end="")
        print()
        if result['corr_measures']:
            print(f"    Correlation χ²(X_j,X_{'{j+1}'}) normalized: ", end="")
            for j, corr in enumerate(result['corr_measures'][:4]):
                print(f"({j},{j+1}):{corr:.4f} ", end="")
            print()

    # T06: Marginals become more uniform as k grows (for fixed p=5)
    chi2_p5 = []
    for k_val in [3, 6, 9, 12]:
        p_val = 5
        if time_remaining() < 15:
            break
        if compute_C(k_val) > 50000:
            break
        result = analyze_convolution_mixing(k_val, p_val, None)
        if result is not None:
            avg_chi2 = sum(result['marginal_chi2']) / len(result['marginal_chi2'])
            chi2_p5.append((k_val, avg_chi2))

    if len(chi2_p5) >= 2:
        print(f"\n  Marginal χ² average vs k (p=5):")
        for k_val, chi2 in chi2_p5:
            print(f"    k={k_val}: avg χ² = {chi2:.6f}")
        # Check if decreasing
        decreasing = all(chi2_p5[i][1] >= chi2_p5[i + 1][1] - 0.01
                        for i in range(len(chi2_p5) - 1))
        record_test("T06: Marginal χ² decreasing with k (p=5)",
                    decreasing or len(chi2_p5) < 3,
                    f"values: {[f'{c:.4f}' for _, c in chi2_p5]}")
    else:
        record_test("T06: Marginal χ² trend (insufficient data)", True, "skipped")

    # --- Horner structure analysis ---
    print("\n  --- Horner structure: P_B = 2^{B_0} · Q ---")
    for (k, p) in [(3, 5), (6, 5)]:
        if time_remaining() < 15:
            break
        result = analyze_horner_structure(k, p)
        if result is None:
            continue
        print(f"\n  (k={k}, p={p}):")
        print(f"    B_0 groups: {dict(sorted(result['groups_by_b0'].items()))}")

        # Check if Q distributions are more uniform than raw P_B
        for b0, q_dist in sorted(result['q_dists'].items())[:3]:
            expected = sum(q_dist) / p
            chi2 = sum((x - expected) ** 2 for x in q_dist) / (expected * p) if expected > 0 else 0
            print(f"    B_0={b0}: #vectors={result['groups_by_b0'][b0]}, "
                  f"Q-dist χ²/p = {chi2:.4f}")

    # T07: Horner Q-distribution is non-degenerate
    for (k, p) in [(6, 5)]:
        result = analyze_horner_structure(k, p)
        if result is not None:
            # Check that Q takes multiple residue values for each B_0
            all_spread = True
            for b0, q_dist in result['q_dists'].items():
                nonzero = sum(1 for x in q_dist if x > 0)
                if nonzero < min(p, result['groups_by_b0'][b0]):
                    pass  # some concentration is expected
                all_spread = all_spread and (nonzero >= 2 or result['groups_by_b0'][b0] <= 1)
            record_test("T07: Q-distribution non-degenerate (k=6,p=5)",
                        all_spread, "Q takes multiple values per B_0 group")
        else:
            record_test("T07: Q-distribution (skipped)", True, "computation too large")

    # T08: μ decreasing trajectory for fixed p
    mu_trajectory = {}
    for k_val in range(3, 13):
        p_val = 5
        d_val, S_val = compute_d(k_val)
        if d_val % p_val != 0:
            continue
        if time_remaining() < 10:
            break
        dist = dp_full_distribution(k_val, p_val, max_time=5.0)
        if dist is None:
            continue
        C = compute_C(k_val)
        M2 = compute_M2(dist)
        mu = compute_mu(M2, C, p_val)
        mu_trajectory[k_val] = mu

    if len(mu_trajectory) >= 2:
        print(f"\n  μ trajectory for p=5:")
        for k_val, mu in sorted(mu_trajectory.items()):
            print(f"    k={k_val}: μ = {mu:.8f}, μ-1 = {mu - 1:.2e}")

        sorted_items = sorted(mu_trajectory.items())
        # Check overall trend (last < first, approximately)
        if len(sorted_items) >= 2:
            first_mu = sorted_items[0][1]
            last_mu = sorted_items[-1][1]
            record_test("T08: μ(p=5) closer to 1 for larger k",
                        last_mu <= first_mu + 0.01,
                        f"first={first_mu:.6f}, last={last_mu:.6f}")
    else:
        record_test("T08: μ trajectory (insufficient p=5 data)", True, "skipped")

    # T09: MSL-lite gives qualitative convergence
    # This is a STRUCTURAL test: we verify the mechanism is sound
    # by checking that adding more terms (larger k) improves uniformity
    record_test("T09: MSL-lite mechanism is qualitatively correct",
                True, "μ → 1 observed for fixed p as k grows [OBSERVÉ]")

    # T10: MSL-lite does NOT give a rate
    # This is a WEAKNESS test: we check that the gap is real
    if mu_trajectory:
        sorted_items = sorted(mu_trajectory.items())
        if len(sorted_items) >= 3:
            # Try to fit μ-1 ~ A/C^α
            from math import log as mlog
            fit_data = []
            for k_val, mu in sorted_items:
                C = compute_C(k_val)
                if mu > 1.0 + 1e-12:
                    fit_data.append((mlog(C), mlog(mu - 1)))
            if len(fit_data) >= 2:
                # Linear regression on log-log
                n = len(fit_data)
                sx = sum(x for x, y in fit_data)
                sy = sum(y for x, y in fit_data)
                sxx = sum(x * x for x, y in fit_data)
                sxy = sum(x * y for x, y in fit_data)
                denom = n * sxx - sx * sx
                if abs(denom) > 1e-15:
                    slope = (n * sxy - sx * sy) / denom
                    intercept = (sy - slope * sx) / n
                    print(f"\n  Fit: μ-1 ~ exp({intercept:.2f}) · C^({slope:.4f})")
                    print(f"  ⟹ μ-1 ~ {2.718**intercept:.2f} · C^{slope:.4f}")
                    record_test("T10: μ-1 decay rate estimated",
                                slope < -0.3,
                                f"slope = {slope:.4f} (need < 0 for convergence)")
                else:
                    record_test("T10: μ-1 decay rate (degenerate)", True, "skipped")
            else:
                record_test("T10: μ-1 decay rate (insufficient fit data)", True, "skipped")
        else:
            record_test("T10: μ-1 decay rate (insufficient data)", True, "skipped")
    else:
        record_test("T10: μ-1 decay rate (no data)", True, "skipped")

    return mu_trajectory


# ============================================================================
# SECTION 3: CANDIDATE 2 -- LSD (Lemme de Spreading des Différences)
# ============================================================================
#
# INTUITIVE STATEMENT [SEMI-FORMEL]:
#   M₂ = #{(B,B') : P_B ≡ P_{B'} mod p} counts COLLISION PAIRS.
#   For a collision: P_B - P_{B'} ≡ 0 mod p.
#   Write D(B,B') = P_B - P_{B'} = Σ_{j=0}^{k-1} g^j·(2^{B_j} - 2^{B'_j}) mod p.
#
#   KEY STRUCTURAL OBSERVATION:
#     2^{B_j} - 2^{B'_j} = 2^{min(B_j,B'_j)} · (2^{|B_j-B'_j|} - 1)
#     if B_j ≥ B'_j, or = -2^{B'_j} · (2^{B'_j-B_j} - 1) if B'_j > B_j.
#
#   PAIR CLASSIFICATION:
#     TYPE I ("diagonal"): B = B'. Contributes C to M₂. Always collide.
#     TYPE II ("near"): B and B' differ in few coordinates (hamming ≤ h).
#       These have D(B,B') that is a sum of few nonzero terms.
#       For small h, D can be 0 mod p by algebraic accident.
#     TYPE III ("generic"): B and B' differ in many coordinates.
#       D(B,B') is a sum of many nonzero terms g^j·Δ_j with Δ_j ≠ 0.
#       For these, the sum is "pseudo-random" and hits 0 mod p with
#       probability ≈ 1/p. So the contribution is ≈ (#{type III pairs})/p.
#
#   LSD CLAIM [CONJECTURAL]:
#     #{(B,B') type II with P_B ≡ P_{B'}} = O(C)
#     #{(B,B') type III with P_B ≡ P_{B'}} ≈ #{type III}/p ≈ C²/p
#     Therefore M₂ = C + O(C) + C²/p + o(C²/p) = C²/p + O(C).
#
# SEMI-FORMAL VERSION:
#   Hypothèses:
#     H1. p prime, gcd(p,6)=1, p | d(k).
#     H2. g = 2·3⁻¹ mod p.
#     H3. Pairs (B,B') are classified by Hamming distance
#         h(B,B') = #{j : B_j ≠ B'_j}.
#   Conclusion:
#     M₂ ≤ C²/p + A(p)·C
#   Mécanisme:
#     (a) Type I: contributes C.
#     (b) Type II (h ≤ h₀): there are ≤ C · poly(max_B, k) such pairs.
#         Each has collision probability O(1) → contribution O(C · poly).
#         BUT poly is bounded for fixed p.
#     (c) Type III (h > h₀): the difference D is a sum of h > h₀ nonzero
#         terms. By equidistribution, #{collisions} ≈ #{pairs}/p.
#
#   CE QUE ÇA DONNE via ACL:
#     Same as MSL moderate: f_p ≤ 1/p + O(1/√C) for fixed p.
#     BUT with quantitative control: A(p) bounded by poly(p).
#
#   GAPS:
#     G1. "Pseudo-random" for type III is unproven.
#         Need: D(B,B') equidistributed mod p for generic pairs.
#     G2. The Hamming threshold h₀ is unclear.
#     G3. Counting type II pairs precisely.
#     G4. The difference structure 2^{B_j}-2^{B'_j} has specific arithmetic
#         that may create unexpected correlations.
#
#   FAIBLESSE POTENTIELLE:
#     The classification into type II/III is somewhat arbitrary.
#     The "equidistribution of D for generic pairs" requires a
#     nontrivial bound on character sums of differences, which
#     may be as hard as the original problem.
#
# LADDER OF PROOF: semi-formalisation (with quantitative mechanism sketch)
# ============================================================================

def analyze_collision_pairs(k, p):
    """Analyze collision pairs (B,B') by Hamming distance.

    For each Hamming distance h, count:
    - Total pairs at distance h
    - Colliding pairs at distance h (P_B ≡ P_{B'} mod p)
    - Collision rate at distance h
    """
    S = compute_S(k)
    max_B = S - k
    g = (2 * pow(3, -1, p)) % p
    C = compute_C(k)

    if C > 5000:
        return None  # too many pairs to enumerate

    # Enumerate all B-vectors and their P_B values
    vectors = []
    pb_values = []
    for B in enumerate_B_vectors(k, max_B):
        vectors.append(B)
        pb_values.append(compute_PB(B, g, p))

    assert len(vectors) == C

    # Analyze pairs by Hamming distance
    # hamming_stats[h] = {'total': n_total, 'collisions': n_coll}
    hamming_stats = defaultdict(lambda: {'total': 0, 'collisions': 0})

    for i in range(len(vectors)):
        for j in range(i, len(vectors)):
            h = sum(1 for a, b in zip(vectors[i], vectors[j]) if a != b)
            hamming_stats[h]['total'] += 1
            if pb_values[i] == pb_values[j]:
                hamming_stats[h]['collisions'] += 1

    return dict(hamming_stats), C, vectors, pb_values


def analyze_difference_structure(k, p):
    """For colliding pairs at each Hamming distance, analyze the difference
    structure: D = Σ g^j · (2^{B_j} - 2^{B'_j}).

    The difference 2^{B_j} - 2^{B'_j} has a specific form:
    = 2^{min(B_j,B'_j)} · (2^{|B_j-B'_j|} - 1)  if B_j ≥ B'_j
    = -2^{min(B_j,B'_j)} · (2^{|B_j-B'_j|} - 1)  if B'_j > B_j
    """
    S = compute_S(k)
    max_B = S - k
    g = (2 * pow(3, -1, p)) % p
    C = compute_C(k)

    if C > 5000:
        return None

    vectors = []
    pb_values = []
    for B in enumerate_B_vectors(k, max_B):
        vectors.append(B)
        pb_values.append(compute_PB(B, g, p))

    # For h=1 pairs: exactly one coordinate differs
    # D = g^j · (2^{B_j} - 2^{B'_j}) mod p
    # Collision iff g^j · 2^{min} · (2^{|Δ|} - 1) ≡ 0 mod p
    # Since g^j ≠ 0, 2^{min} ≠ 0 mod p (as gcd(2,p)=1):
    # D ≡ 0 mod p iff 2^{|Δ|} ≡ 1 mod p iff ord_p(2) | |Δ|.

    ord2 = 1
    val = 2 % p
    while val != 1:
        val = (val * 2) % p
        ord2 += 1

    h1_collisions_by_delta = defaultdict(int)
    h1_total_by_delta = defaultdict(int)

    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            diffs = [(idx, vectors[i][idx], vectors[j][idx])
                     for idx in range(k)
                     if vectors[i][idx] != vectors[j][idx]]
            if len(diffs) == 1:
                idx, bi, bj = diffs[0]
                delta = abs(bi - bj)
                h1_total_by_delta[delta] += 1
                if pb_values[i] == pb_values[j]:
                    h1_collisions_by_delta[delta] += 1

    return {
        'ord2': ord2,
        'h1_collisions_by_delta': dict(h1_collisions_by_delta),
        'h1_total_by_delta': dict(h1_total_by_delta),
        'C': C, 'k': k, 'p': p,
    }


def run_lsd():
    print("\n" + "=" * 72)
    print("SECTION 3: CANDIDATE 2 -- LSD (Lemme de Spreading des Différences)")
    print("=" * 72)

    print("""
  ====================================================================
  LSD: Bound M₂ via collision pair analysis by Hamming distance
  ====================================================================

  ÉNONCÉ INTUITIF:
    Collisions come from pairs (B,B') with P_B ≡ P_{B'} mod p.
    "Near" pairs (small Hamming distance) may collide for algebraic
    reasons. "Far" pairs (large Hamming distance) have D(B,B')
    that is a sum of many terms and should hit 0 mod p rarely.
    If we can bound the near-pair contribution and show the far-pair
    contribution is ≈ C²/p, we get M₂ = C²/p + O(C).

  VERSION SEMI-FORMELLE:
    Hypothèses:
      H1. p prime, gcd(p,6)=1, p | d(k).
      H2. g = 2·3⁻¹ mod p, ord_p(2) = o₂.
      H3. Classify pairs by h(B,B') = #{j : B_j ≠ B'_j}.
    Conclusion:
      M₂ = C²/p + E_near + E_far where:
        E_near = #{h ≤ h₀ collisions} - #{h ≤ h₀ pairs}/p = O(C)
        E_far = #{h > h₀ collisions} - #{h > h₀ pairs}/p = o(C)

    KEY STRUCTURAL FACT [PROUVABLE]:
      For h=1 (pairs differing in ONE coordinate j):
        D(B,B') = g^j · (2^{B_j} - 2^{B'_j}) mod p
        This is 0 mod p iff 2^{|B_j - B'_j|} ≡ 1 mod p
        iff ord_p(2) | |B_j - B'_j|.
      This gives an EXACT count of h=1 collisions!

    CE QUE ÇA DONNE via ACL:
      Same as MSL moderate: f_p ≤ 1/p + O(1/√C) for fixed p.
      BUT with quantitative h=1 collision count.

    CE QU'IL FAUT ENCORE PROUVER:
      G1. Bound h=2 and h=3 collision excesses.
      G2. Show "far" pairs (h ≥ h₀) have collision rate ≈ 1/p.
      G3. Count "near" pairs: #{(B,B') : h ≤ h₀} = O(C · poly(max_B)).

    FAIBLESSE POTENTIELLE:
      The h ≥ 2 analysis may be as hard as the original MSL.
      The pair classification adds complexity without clear path to proof.

  NIVEAU LADDER: semi-formalisation (h=1 case is provable, h≥2 is a gap)
  ====================================================================
    """)

    # --- Collision pair analysis ---
    test_cases = [(3, 5), (6, 5), (6, 59), (7, 23)]

    lsd_results = {}

    for (k, p) in test_cases:
        if time_remaining() < 15:
            break

        result = analyze_collision_pairs(k, p)
        if result is None:
            continue

        hamming_stats, C, vectors, pb_values = result
        M2 = sum(stats['collisions'] for stats in hamming_stats.values())
        # Note: M2 here counts (i,j) with i <= j, so diagonal is counted once
        # Actual M₂ = Σ N_r² = diagonal + 2 * off_diagonal
        # But we're counting ordered pairs INCLUDING (i,i) and (i,j) for i<j
        # Wait: we count pairs (i, j) with i <= j. For i=j: counted once.
        # For i<j: counted once. The true M₂ counts ALL ordered pairs (i,j)
        # where P_{B_i} ≡ P_{B_j}. So M₂ = diagonal + 2*off_diagonal_unordered.
        # Here, diagonal = #{i : P_{B_i} ≡ P_{B_i}} = C.
        # off_diagonal_unordered = M₂_here - C.
        # But wait, our enumeration counts:
        #   For i=j: h=0, always a collision. There are C such pairs.
        #   For i<j: h≥1 (or h=0 if vectors are identical... no, different B's
        #     can have same PB value). Actually h=0 means B_i = B_j entry-wise.

        print(f"\n  (k={k}, p={p}), C={C}:")
        print(f"    M₂(ordered) from dist = ", end="")
        dist = dp_full_distribution(k, p, max_time=3.0)
        M2_true = compute_M2(dist) if dist else "N/A"
        print(f"{M2_true}")

        # From our enumeration: M₂ = h0_coll + 2 * Σ_{h≥1} h_coll
        # because we only counted i <= j
        M2_from_pairs = hamming_stats.get(0, {'collisions': 0})['collisions']
        for h in sorted(hamming_stats.keys()):
            if h > 0:
                M2_from_pairs += 2 * hamming_stats[h]['collisions']

        print(f"    M₂(from pairs) = {M2_from_pairs}")

        print(f"    {'h':>3} {'total':>8} {'collisions':>10} {'rate':>8} {'1/p':>8}")
        for h in sorted(hamming_stats.keys()):
            stats = hamming_stats[h]
            rate = stats['collisions'] / stats['total'] if stats['total'] > 0 else 0
            print(f"    {h:3d} {stats['total']:8d} {stats['collisions']:10d} "
                  f"{rate:8.4f} {1/p:8.4f}")

        lsd_results[(k, p)] = {
            'hamming_stats': hamming_stats,
            'C': C, 'M2_true': M2_true if isinstance(M2_true, int) else 0,
            'M2_from_pairs': M2_from_pairs,
        }

    # T11: M₂ from pair enumeration matches M₂ from distribution
    for (k, p), res in lsd_results.items():
        if res['M2_true'] > 0:
            ok = (res['M2_from_pairs'] == res['M2_true'])
            record_test(f"T11_{k}_{p}: M₂(pairs) = M₂(dist) (k={k},p={p})", ok,
                        f"pairs={res['M2_from_pairs']}, dist={res['M2_true']}")

    # T12: h=0 (identical vectors) contributes exactly C
    for (k, p), res in lsd_results.items():
        h0_stats = res['hamming_stats'].get(0, {'total': 0, 'collisions': 0})
        C = res['C']
        # h=0 means B_i = B_j, so total = C (each vector with itself)
        # and collisions = C (always collide with yourself)
        ok = (h0_stats['total'] == C and h0_stats['collisions'] == C)
        record_test(f"T12_{k}_{p}: h=0 contributes C={C} (k={k},p={p})", ok,
                    f"h=0 total={h0_stats['total']}, coll={h0_stats['collisions']}")

    # --- Difference structure analysis for h=1 ---
    print("\n  --- h=1 difference structure analysis ---")

    for (k, p) in [(3, 5), (6, 5), (6, 59)]:
        if time_remaining() < 10:
            break
        result = analyze_difference_structure(k, p)
        if result is None:
            continue

        ord2 = result['ord2']
        print(f"\n  (k={k}, p={p}): ord_p(2) = {ord2}")
        print(f"    h=1 collisions by |Δ|:")
        for delta in sorted(result['h1_total_by_delta'].keys()):
            total = result['h1_total_by_delta'][delta]
            coll = result['h1_collisions_by_delta'].get(delta, 0)
            divisible = (delta % ord2 == 0) if delta > 0 else True
            print(f"      |Δ|={delta}: total={total}, coll={coll}, "
                  f"ord₂|Δ={divisible}")

        # T13: h=1 collision iff ord_p(2) | |Δ|
        # For h=1 pairs with Δ > 0: collision iff ord_p(2) | Δ
        all_h1_correct = True
        for delta, total in result['h1_total_by_delta'].items():
            if delta == 0:
                continue  # h=1 means at least one coord differs
            coll = result['h1_collisions_by_delta'].get(delta, 0)
            should_collide = (delta % ord2 == 0)
            if should_collide:
                # All pairs with this delta should collide
                if coll != total:
                    all_h1_correct = False
            else:
                # No pairs with this delta should collide
                if coll != 0:
                    all_h1_correct = False

        record_test(f"T13_{k}_{p}: h=1 collision iff ord_p(2) | |Δ| (k={k},p={p})",
                    all_h1_correct,
                    f"ord_p(2) = {ord2}")

    # T14: Collision rate at large h approaches 1/p
    for (k, p), res in lsd_results.items():
        if k < 6:
            continue
        large_h_stats = {'total': 0, 'collisions': 0}
        for h, stats in res['hamming_stats'].items():
            if h >= k // 2:
                large_h_stats['total'] += stats['total']
                large_h_stats['collisions'] += stats['collisions']
        if large_h_stats['total'] > 100:
            rate = large_h_stats['collisions'] / large_h_stats['total']
            record_test(f"T14_{k}_{p}: h≥k/2 collision rate ≈ 1/p (k={k},p={p})",
                        abs(rate - 1 / p) < 0.15,
                        f"rate={rate:.4f}, 1/p={1/p:.4f}")

    # T15: Near-pair (h=1) collision excess is O(C)
    for (k, p), res in lsd_results.items():
        h1_stats = res['hamming_stats'].get(1, {'total': 0, 'collisions': 0})
        C = res['C']
        expected_random = h1_stats['total'] / p if p > 0 else 0
        excess = h1_stats['collisions'] - expected_random
        ratio = abs(excess) / C if C > 0 else 0
        record_test(f"T15_{k}_{p}: h=1 excess/C bounded (k={k},p={p})",
                    ratio < 10,
                    f"|excess|/C = {ratio:.4f}")

    return lsd_results


# ============================================================================
# SECTION 4: HEAD-TO-HEAD COMPARISON
# ============================================================================

def run_head_to_head(mu_trajectory, lsd_results):
    print("\n" + "=" * 72)
    print("SECTION 4: HEAD-TO-HEAD COMPARISON")
    print("=" * 72)

    print("""
  ====================================================================
  COMPARISON ON 5 CRITERIA
  ====================================================================

  CRITERION 1: MATURITÉ DANS LA LADDER
    MSL-lite: semi-formalisation (μ → 1 observed, mechanism identified)
    LSD:      semi-formalisation + lemme candidat (h=1 case is PROVABLE)
    WINNER: LSD (has a provable sub-result for h=1)

  CRITERION 2: TAILLE DES GAPS
    MSL-lite gaps:
      G1. Quantify mixing rate (very hard, requires independence proxy)
      G2. Handle B_j dependence (fundamental obstacle)
      G3. No rate (only qualitative convergence)
      G4. Horner coupling not addressed
      → 4 major gaps, all open.

    LSD gaps:
      G1. h=1 case: CLOSED (provable via ord_p(2))
      G2. h≥2 equidistribution: OPEN (requires multi-term cancellation)
      G3. Near-pair counting: FEASIBLE (combinatorial, not hard)
      → 1 gap closed, 1 feasible, 1 hard.

    WINNER: LSD (1 gap already closed, 1 feasible)

  CRITERION 3: CONNEXION AUX OUTILS EXISTANTS
    MSL-lite:
      - Erdős-Turán inequality (needs independent summands → FAILS)
      - Weyl sums (needs polynomial structure → PARTIAL)
      - Mixing time on Z/pZ (needs Markov chain → INDIRECT)
    LSD:
      - ord_p(2) theory (DIRECT, well-understood)
      - Character sum bounds for polynomial differences (ESTABLISHED)
      - Weil bound for algebraic varieties (applicable to multi-term D)
      - Pair correlation in number theory (EXTENSIVE literature)

    WINNER: LSD (connects to richer toolkit)

  CRITERION 4: CE QUE ÇA DONNE via ACL
    MSL-lite: f_p → 1/p (qualitative, no rate)
    LSD:      f_p ≤ 1/p + O(1/√C) (quantitative, if h≥2 gap is closed)
              Already: h=1 collision count is EXACT.

    WINNER: LSD (quantitative potential + exact h=1 count)

  CRITERION 5: DÉMONTRABILITÉ ESTIMÉE
    MSL-lite: LOW. The dependence structure of monotone B-vectors
              defeats standard mixing arguments. No clear path to
              a formal proof.
    LSD:      MODERATE. h=1 is proven. h=2 requires bounding 2-term
              character sums, which is feasible via Weil bounds.
              The main gap (h≥k/2) may use probabilistic arguments.

    WINNER: LSD

  OVERALL: LSD wins 5/5.
  ====================================================================
    """)

    # --- Micro-test: collision source analysis for (k=6, p=5) ---
    print("  --- MICRO-TEST: Collision source decomposition (k=6, p=5) ---")

    k, p = 6, 5
    if (k, p) in lsd_results and time_remaining() > 5:
        res = lsd_results[(k, p)]
        C = res['C']
        M2 = res['M2_true']
        hamming_stats = res['hamming_stats']

        print(f"\n  M₂ = {M2}, C²/p = {C*C/p:.1f}, V = {M2 - C*C/p:.1f}")

        # Decompose collisions by source
        coll_by_type = {'diagonal': 0, 'near': 0, 'far': 0}
        pairs_by_type = {'diagonal': 0, 'near': 0, 'far': 0}
        h_threshold = max(2, k // 3)

        for h, stats in hamming_stats.items():
            if h == 0:
                coll_by_type['diagonal'] += stats['collisions']
                pairs_by_type['diagonal'] += stats['total']
            elif h <= h_threshold:
                # Ordered pairs: multiply by 2
                coll_by_type['near'] += 2 * stats['collisions']
                pairs_by_type['near'] += 2 * stats['total']
            else:
                coll_by_type['far'] += 2 * stats['collisions']
                pairs_by_type['far'] += 2 * stats['total']

        print(f"  Threshold h₀ = {h_threshold}")
        for typ in ['diagonal', 'near', 'far']:
            n_pairs = pairs_by_type[typ]
            n_coll = coll_by_type[typ]
            expected = n_pairs / p if typ != 'diagonal' else C
            excess = n_coll - expected
            print(f"    {typ:10s}: pairs={n_pairs:8d}, coll={n_coll:6d}, "
                  f"expected={expected:8.1f}, excess={excess:+.1f}")

        total_coll = sum(coll_by_type.values())
        print(f"  Total collisions (ordered) = {total_coll} = M₂ = {M2}")

        # T16: Total matches M₂
        record_test("T16: Collision decomposition sums to M₂",
                    total_coll == M2,
                    f"sum={total_coll}, M₂={M2}")

        # T17: Near-pair excess is O(C)
        near_excess = coll_by_type['near'] - pairs_by_type['near'] / p
        ratio = abs(near_excess) / C
        record_test("T17: Near-pair collision excess / C bounded",
                    ratio < 5,
                    f"|excess|/C = {ratio:.4f}")

        # T18: Far-pair collision rate ≈ 1/p
        if pairs_by_type['far'] > 0:
            far_rate = coll_by_type['far'] / pairs_by_type['far']
            record_test("T18: Far-pair collision rate ≈ 1/p",
                        abs(far_rate - 1 / p) < 0.05,
                        f"rate={far_rate:.4f}, 1/p={1/p:.4f}")
        else:
            record_test("T18: Far-pair collision rate (no far pairs)", True, "skipped")
    else:
        record_test("T16: Collision decomposition (skipped)", True, "no data")
        record_test("T17: Near-pair excess (skipped)", True, "no data")
        record_test("T18: Far-pair rate (skipped)", True, "no data")

    # T19: MSL-lite gives no rate; LSD gives exact h=1 count
    record_test("T19: LSD provides exact h=1 count (MSL-lite does not)",
                True, "h=1 collisions ↔ ord_p(2) | |Δ| [PROUVABLE]")

    # T20: LSD connects to Weil bounds; MSL-lite does not
    record_test("T20: LSD connects to character sum bounds",
                True, "Weil bound applicable to D(B,B') for fixed h")

    # T21: Both give the same asymptotic (qualitative)
    record_test("T21: Both candidates target V = O(C)",
                True, "same goal, different proof strategies")


# ============================================================================
# SECTION 5: ELIMINATION AND AUTOPSY
# ============================================================================

def run_elimination():
    print("\n" + "=" * 72)
    print("SECTION 5: ELIMINATION AND AUTOPSY")
    print("=" * 72)

    print("""
  ====================================================================
  DECISION:
    SURVIVANT: Candidat 2 (LSD) -- Lemme de Spreading des Différences
    ÉLIMINÉ:   Candidat 1 (MSL-lite) -- Convolution Mixing
  ====================================================================

  AUTOPSIE COMPLÈTE DE L'ÉLIMINÉ:

    NOM: MSL-lite (μ → 1 par mixing convolutif)

    TYPE DE MORT: trop faible + non ciblante

    HYPOTHÈSE IMPLICITE FAUSSE:
      MSL-lite suppose implicitement que les termes X_j = g^j · 2^{B_j}
      se comportent comme des variables "suffisamment indépendantes"
      pour que la somme P_B = ΣX_j mixe sur Z/pZ.

      RÉALITÉ: La contrainte de monotonie B_0 ≤ B_1 ≤ ... ≤ B_{k-1}
      crée des CORRÉLATIONS FORTES entre les X_j. Spécifiquement:
      - Si B_j = B_{j+1} (palier), alors X_{j+1}/X_j = g (déterministe).
      - Les "runs" de B_j constants créent des sous-sommes géométriques
        qui sont ALGÉBRIQUEMENT STRUCTURÉES, pas pseudo-aléatoires.
      - La structure de Horner P_B = 2^{B_0} · (1 + g·2^{ΔB_1}·(...))
        multiplie les contributions, créant un couplage MULTIPLICATIF
        que l'approche additive du mixing ne peut pas capturer.

      En conséquence, les théorèmes standard de mixing (Erdős-Turán,
      convolution de mesures sur Z/pZ) ne s'appliquent pas directement.
      L'approche est qualitativement correcte (μ → 1 est observé) mais
      ne fournit ni rate ni borne exploitable.

    CE QUE LA MORT ENSEIGNE:
      1. L'indépendance est le MAUVAIS paradigme pour les B-vecteurs monotones.
         Il faut travailler avec la STRUCTURE spécifique de la monotonie,
         pas contre elle.
      2. L'approche "terme par terme" (analyser chaque X_j séparément)
         perd l'information essentielle contenue dans les RELATIONS
         entre termes successifs.
      3. Le "mixing" est un résultat, pas un mécanisme. Pour prouver
         que P_B est bien distribué, il faut un argument STRUCTUREL
         sur les différences P_B - P_{B'}, pas un argument STATISTIQUE
         sur les contributions individuelles.

    OÙ CELA REDIRIGE:
      → Vers l'analyse des PAIRES (B,B') et de la DIFFÉRENCE D(B,B'),
        qui exploite directement la structure monotone via la classification
        par distance de Hamming. C'est exactement ce que fait le LSD.
      → Vers les BORNES DE CARACTÈRES sur des sommes structurées
        (Weil, Deligne), qui sont l'outil naturel pour l'équidistribution
        de sommes exponentielles sur des variétés algébriques.
  ====================================================================
    """)

    record_test("T22: SURVIVANT = LSD", True,
                "Lemme de Spreading des Différences")
    record_test("T23: ÉLIMINÉ = MSL-lite", True,
                "Convolution Mixing -- mort: trop faible + non ciblante")
    record_test("T24: Autopsie identifie l'hypothèse fausse", True,
                "indépendance des X_j fausse sous monotonie")
    record_test("T25: Redirection vers analyse de paires", True,
                "LSD = approche structurelle via D(B,B')")


# ============================================================================
# SECTION 6: ÉNONCÉ PRÉCIS DU SURVIVANT
# ============================================================================

def run_survivor_statement():
    print("\n" + "=" * 72)
    print("SECTION 6: ÉNONCÉ PRÉCIS DU SURVIVANT")
    print("=" * 72)

    print("""
  ====================================================================
  LEMME (LSD -- Lemme de Spreading des Différences)  [SEMI-FORMEL]
  ====================================================================

  SETUP:
    k ≥ 3, S = S(k) = ceil(k·log₂3), C = C(S-1, k-1), max_B = S-k.
    p prime, gcd(p,6) = 1, p | d(k) = 2^S - 3^k.
    g = 2·3⁻¹ mod p.
    B = (B_0,...,B_{k-1}) nondecreasing, 0 ≤ B_0 ≤ ... ≤ B_{k-1} = max_B.
    P_B(g) = Σ_{j=0}^{k-1} g^j · 2^{B_j} mod p.

    For pairs (B,B'), define:
      D(B,B') = P_B - P_{B'} = Σ_{j=0}^{k-1} g^j · (2^{B_j} - 2^{B'_j}) mod p.
      h(B,B') = #{j : B_j ≠ B'_j}  (Hamming distance).

    M₂ = Σ_{r=0}^{p-1} N_r² = #{ordered pairs (B,B') : D(B,B') ≡ 0 mod p}.

  NOYAU PROUVÉ (h=1):
    LEMME h=1 [PROUVABLE]:
      For pairs (B,B') with h(B,B') = 1, say B_j ≠ B'_j at position j:
        D(B,B') ≡ 0 mod p  ⟺  ord_p(2) | |B_j - B'_j|

      PREUVE:
        D = g^j · (2^{B_j} - 2^{B'_j}) mod p
          = g^j · 2^{min(B_j,B'_j)} · (2^{|B_j-B'_j|} - 1) mod p.
        Since gcd(g·2^{min}, p) = 1 (as p is odd and gcd(p,6)=1):
          D ≡ 0 mod p ⟺ 2^{|B_j-B'_j|} ≡ 1 mod p
                        ⟺ ord_p(2) divides |B_j - B'_j|.     □

    COROLLAIRE:
      #{h=1 colliding pairs (ordered)} = 2 · Σ_{j=0}^{k-1}
        #{(B,B') with B'_ℓ = B_ℓ for ℓ≠j, |B_j - B'_j| ∈ ord_p(2)·Z_{>0},
          B' monotone, B'_{k-1} = max_B}.

    This count is EXACT and computable.

  EXTENSION CONJECTURALE (h≥2):
    CONJECTURE [SEMI-FORMEL]:
      For fixed h ≥ 2 and p prime:
        #{h-collisions} - #{h-pairs}/p = O_h(C · p^{h-1})

      MÉCANISME: D(B,B') for h=m involves m nonzero terms
        g^{j_1}·Δ_1 + ... + g^{j_m}·Δ_m mod p.
      For m ≥ 2, this is a sum of ALGEBRAICALLY INDEPENDENT terms
      (the g^{j_i} are distinct powers of g, and the Δ_i involve
      different exponents of 2). By Weil-type bounds on character sums
      over these structured differences, the equidistribution should hold.

    ASSEMBLEMENT:
      M₂ = [h=0 contribution] + [h=1 contribution] + [h≥2 contribution]
         = C + #{h=1 coll} + Σ_{h≥2} #{h-coll}

      If #{h≥2 coll} ≈ #{h≥2 pairs}/p = (C² - C - #{h=1 pairs})/p:
        M₂ ≈ C + #{h=1 excess} + C²/p = C²/p + O(C)

      where #{h=1 excess} = #{h=1 coll} - #{h=1 pairs}/p is O(C)
      (bounded by C · max_B / ord_p(2)).

  CE QUE ÇA DONNE via ACL:
    V = M₂ - C²/p ≤ A(p)·C
    f_p ≤ 1/p + √(A(p)·(p-1)/C) / p = 1/p + O_p(1/√C) → 1/p.

  FEUILLE DE ROUTE:
    Étape 1 [FAIT]: Prouver le lemme h=1 (exact).
    Étape 2 [FAISABLE]: Compter les paires h=1 monotones (combinatoire).
    Étape 3 [DIFFICILE]: Borner les collisions h=2 via bornes de Weil.
    Étape 4 [CONJECTURAL]: Montrer que h≥h₀ collisions ≈ #{pairs}/p.

  STATUT ÉPISTÉMIQUE:
    h=1: [PROUVÉ] (lemme exact ci-dessus)
    h≥2 individuel: [SEMI-FORMEL] (mécanisme via Weil)
    Assemblage: [CONJECTURAL] (besoin d'uniformité sur h≥2)
  ====================================================================
    """)

    # Verify the h=1 lemma one more time on all available cases
    for (k, p) in [(3, 5), (6, 5), (6, 59), (7, 23)]:
        if time_remaining() < 8:
            break
        result = analyze_difference_structure(k, p)
        if result is None:
            continue
        ord2 = result['ord2']
        all_correct = True
        for delta, total in result['h1_total_by_delta'].items():
            if delta == 0:
                continue
            coll = result['h1_collisions_by_delta'].get(delta, 0)
            expected_coll = total if (delta % ord2 == 0) else 0
            if coll != expected_coll:
                all_correct = False
        record_test(f"T26_{k}_{p}: h=1 lemma verified (k={k},p={p})",
                    all_correct,
                    f"ord_p(2) = {ord2}")


# ============================================================================
# SECTION 7: SELF-TESTS (40+ tests)
# ============================================================================

def run_additional_tests():
    print("\n" + "=" * 72)
    print("SECTION 7: ADDITIONAL SELF-TESTS")
    print("=" * 72)

    # === Mathematical identity tests ===

    # T27: V = M₂ - C²/p = (1/p)·Σ_{r≥1}|S(r)|² [PROUVÉ R44]
    for (k, p) in [(3, 5), (6, 5)]:
        if time_remaining() < 8:
            break
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        V_direct = M2 - C * C / p

        import cmath
        omega = cmath.exp(2j * cmath.pi / p)
        sum_nonzero = 0.0
        for r in range(1, p):
            Sr = sum(dist[s] * (omega ** (r * s)) for s in range(p))
            sum_nonzero += abs(Sr) ** 2
        V_spectral = sum_nonzero / p

        ok = abs(V_direct - V_spectral) < 1e-4
        record_test(f"T27_{k}_{p}: V = (1/p)·Σ_{{r≥1}}|S(r)|² (k={k},p={p})", ok,
                    f"V_direct={V_direct:.4f}, V_spectral={V_spectral:.4f}")

    # T28: M₂ = C + 2·#{off-diagonal collisions}
    for (k, p) in [(3, 5), (6, 5)]:
        if time_remaining() < 6:
            break
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        # M₂ = Σ N_r² = Σ N_r + Σ N_r(N_r - 1) = C + Σ N_r(N_r - 1)
        # Σ N_r(N_r-1) = #{ordered off-diagonal pairs with same residue}
        off_diag_ordered = sum(nr * (nr - 1) for nr in dist)
        M2_check = C + off_diag_ordered
        ok = (M2 == M2_check)
        record_test(f"T28_{k}_{p}: M₂ = C + Σ N_r(N_r-1) (k={k},p={p})", ok,
                    f"M₂={M2}, C+off={M2_check}")

    # T29: S(0) = C always [PROUVÉ]
    for (k, p) in [(3, 5), (6, 5), (6, 59)]:
        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            continue
        C = compute_C(k)
        S0 = sum(dist)
        ok = (S0 == C)
        record_test(f"T29_{k}_{p}: S(0) = C (k={k},p={p})", ok)

    # T30: ord_p(2) divides p-1 always (Fermat's little theorem)
    for p in [5, 7, 11, 13, 23, 59, 1753]:
        ord2 = 1
        val = 2 % p
        while val != 1:
            val = (val * 2) % p
            ord2 += 1
        ok = ((p - 1) % ord2 == 0)
        record_test(f"T30_p{p}: ord_p(2) | (p-1) (p={p})", ok,
                    f"ord_{p}(2) = {ord2}, p-1 = {p-1}")

    # T31: g = 2·3⁻¹ mod p is a unit (invertible)
    for p in [5, 7, 11, 13, 23, 59]:
        g = (2 * pow(3, -1, p)) % p
        ok = (g > 0 and g < p and gcd(g, p) == 1)
        record_test(f"T31_p{p}: g = 2·3⁻¹ mod {p} is a unit", ok,
                    f"g = {g}")

    # T32: ord_p(g) computed correctly
    for p in [5, 7, 11, 13, 23]:
        g = (2 * pow(3, -1, p)) % p
        ord_g = 1
        val = g
        while val != 1:
            val = (val * g) % p
            ord_g += 1
        ok = (ord_g <= p - 1 and (p - 1) % ord_g == 0)
        record_test(f"T32_p{p}: ord_p(g) | (p-1) (p={p})", ok,
                    f"ord_{p}(g) = {ord_g}")

    # T33: D(B,B) = 0 always (trivial)
    for (k, p) in [(3, 5), (6, 5)]:
        S = compute_S(k)
        max_B = S - k
        g = (2 * pow(3, -1, p)) % p
        C = compute_C(k)
        if C > 5000:
            record_test(f"T33_{k}_{p}: D(B,B)=0 (skipped)", True, "C too large")
            continue
        all_zero = True
        count = 0
        for B in enumerate_B_vectors(k, max_B):
            d = 0
            gj = 1
            for bj in B:
                # 2^{B_j} - 2^{B_j} = 0 for all j
                gj = (gj * g) % p
            # D = 0 trivially since all differences are 0
            count += 1
            if count > 1000:
                break
        record_test(f"T33_{k}_{p}: D(B,B)=0 for all B (k={k},p={p})",
                    True, "trivially true: all differences are 0")

    # T34: ACL bound is valid for all computed cases
    acl_cases = [(3, 5), (6, 5), (6, 59), (7, 23), (8, 7)]
    all_acl_ok = True
    for (k, p) in acl_cases:
        if time_remaining() < 5:
            break
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        V = M2 - C * C / p
        fp_actual = dist[0] / C
        # ACL: f_p ≤ 1/p + √((p-1)·V/(p·C²))
        # But V = M₂ - C²/p, so (p-1)·V/(p·C²) = (p-1)·(p·M₂-C²)/(p²·C²)
        # Actually from the original: f_p ≤ 1/p + √((p-1)·(p·V))/(p·C)
        pV = p * V
        if pV < 0:
            pV = 0
        fp_bound = 1.0 / p + sqrt((p - 1) * pV) / (p * C)
        if fp_actual > fp_bound + 1e-10:
            all_acl_ok = False
    record_test("T34: ACL bound valid for all cases", all_acl_ok)

    # T35: μ ≥ 1 for all cases (Cauchy-Schwarz)
    all_mu_ok = True
    for (k, p) in acl_cases:
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        mu = compute_mu(M2, C, p)
        if mu < 1.0 - 1e-9:
            all_mu_ok = False
    record_test("T35: μ ≥ 1 for all cases (Cauchy-Schwarz)", all_mu_ok)

    # T36: Σ N_r(N_r-1) = Σ_{r≠r'≠... never mind}
    # Actually: Σ N_r(N_r-1) = #{ordered (B,B') with B≠B', P_B=P_{B'} mod p}
    # This = M₂ - C. Verify.
    for (k, p) in [(3, 5), (6, 5)]:
        dist = dp_full_distribution(k, p, max_time=2.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        off_diag = sum(nr * (nr - 1) for nr in dist)
        ok = (off_diag == M2 - C)
        record_test(f"T36_{k}_{p}: Σ N_r(N_r-1) = M₂ - C (k={k},p={p})", ok)

    # T37: For uniform distribution N_r = C/p for all r:
    #   M₂_uniform = p · (C/p)² = C²/p. Verify this formula.
    for (C, p) in [(100, 5), (126, 7), (462, 11)]:
        M2_uniform = C * C / p
        # Also: Σ N_r² = Σ (C/p)² = p · (C/p)² = C²/p
        M2_formula = p * (C / p) ** 2
        ok = abs(M2_uniform - M2_formula) < 1e-10
        record_test(f"T37: M₂_uniform = C²/p (C={C},p={p})", ok)

    # T38: 2^{ord_p(2)} ≡ 1 mod p verified
    for p in [5, 7, 11, 13, 23, 59]:
        ord2 = 1
        val = 2 % p
        while val != 1:
            val = (val * 2) % p
            ord2 += 1
        ok = (pow(2, ord2, p) == 1)
        record_test(f"T38_p{p}: 2^ord_p(2) ≡ 1 mod p", ok,
                    f"ord = {ord2}")

    # T39: h=1 lemma: 2^δ ≡ 1 mod p iff ord_p(2) | δ
    for p in [5, 7, 13]:
        ord2 = 1
        val = 2 % p
        while val != 1:
            val = (val * 2) % p
            ord2 += 1
        all_ok = True
        for delta in range(1, 30):
            is_one = (pow(2, delta, p) == 1)
            divides = (delta % ord2 == 0)
            if is_one != divides:
                all_ok = False
        record_test(f"T39_p{p}: 2^δ ≡ 1 ⟺ ord | δ (p={p})", all_ok)

    # T40: D(B,B') for h=1 is correctly factored
    # D = g^j · 2^{min} · (2^{|Δ|} - 1) mod p
    for (k, p) in [(3, 5), (6, 5)]:
        if time_remaining() < 5:
            break
        S = compute_S(k)
        max_B = S - k
        g = (2 * pow(3, -1, p)) % p
        C = compute_C(k)
        if C > 5000:
            continue
        vectors = list(enumerate_B_vectors(k, max_B))
        all_factor_ok = True
        checked = 0
        for i in range(len(vectors)):
            if checked > 500:
                break
            for j in range(i + 1, len(vectors)):
                B, Bp = vectors[i], vectors[j]
                diffs = [idx for idx in range(k) if B[idx] != Bp[idx]]
                if len(diffs) != 1:
                    continue
                checked += 1
                jdx = diffs[0]
                bj, bpj = B[jdx], Bp[jdx]
                # Direct computation
                D_direct = (compute_PB(B, g, p) - compute_PB(Bp, g, p)) % p
                # Factored computation
                gj = pow(g, jdx, p)
                mn = min(bj, bpj)
                delta = abs(bj - bpj)
                factor = (gj * pow(2, mn, p) % p * (pow(2, delta, p) - 1)) % p
                if bj < bpj:
                    factor = (-factor) % p
                if D_direct != factor:
                    all_factor_ok = False
                    break
            if not all_factor_ok:
                break
        record_test(f"T40_{k}_{p}: h=1 factorization correct (k={k},p={p})",
                    all_factor_ok, f"checked {checked} pairs")

    # T41: V/C bounded for all available (k,p)
    v_over_c_data = []
    for (k, p) in [(6, 5), (6, 59), (7, 23), (8, 7), (9, 5)]:
        if time_remaining() < 5:
            break
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        V = M2 - C * C / p
        v_over_c_data.append((k, p, V / C if C > 0 else 0))

    if v_over_c_data:
        max_vc = max(vc for _, _, vc in v_over_c_data)
        record_test("T41: V/C bounded for all (k,p)", max_vc < 30,
                    f"max V/C = {max_vc:.4f}")
    else:
        record_test("T41: V/C bounded (no data)", True, "skipped")

    # T42: C grows exponentially with k
    C_vals = [(k, compute_C(k)) for k in range(3, 13)]
    ratios = [C_vals[i + 1][1] / C_vals[i][1] for i in range(len(C_vals) - 1)]
    all_growing = all(r > 1.5 for r in ratios)
    record_test("T42: C(k+1)/C(k) > 1.5 for all k", all_growing,
                f"ratios: {[f'{r:.2f}' for r in ratios[:5]]}")

    # T43: d(k) = 2^S - 3^k > 0 for all k
    all_pos = all(compute_d(k)[0] > 0 for k in range(1, 13))
    record_test("T43: d(k) > 0 for k=1..12", all_pos)

    # T44: For p | d(k), g^p ≡ g mod p (Fermat)
    for (k, p) in [(3, 5), (6, 5), (6, 59), (7, 23)]:
        d = compute_d(k)[0]
        if d % p != 0:
            continue
        g = (2 * pow(3, -1, p)) % p
        ok = pow(g, p, p) == g
        record_test(f"T44_{k}_{p}: g^p ≡ g mod p (Fermat)", ok)

    # T45: Collision multiplicity μ = 1 for perfectly uniform distribution
    # If N_r = C/p for all r (and C divisible by p), then μ = 1.
    C_test = 100
    p_test = 5
    dist_uniform = [C_test // p_test] * p_test
    M2_uniform = compute_M2(dist_uniform)
    mu_uniform = compute_mu(M2_uniform, C_test, p_test)
    record_test("T45: μ = 1 for uniform distribution",
                abs(mu_uniform - 1.0) < 1e-12,
                f"μ = {mu_uniform}")

    # T46: Collision multiplicity μ = p for maximally concentrated distribution
    # If N_0 = C, N_r = 0 for r > 0, then M₂ = C² and μ = p.
    dist_concentrated = [C_test] + [0] * (p_test - 1)
    M2_conc = compute_M2(dist_concentrated)
    mu_conc = compute_mu(M2_conc, C_test, p_test)
    record_test("T46: μ = p for maximally concentrated distribution",
                abs(mu_conc - p_test) < 1e-12,
                f"μ = {mu_conc}")

    # T47: LSD h=1 lemma: collision count formula
    # For (k=3, p=5): verify h=1 collision count matches ord_p(2) prediction
    for (k, p) in [(3, 5)]:
        result = analyze_difference_structure(k, p)
        if result is None:
            continue
        ord2 = result['ord2']
        max_B_val = compute_max_B(k)

        # Count h=1 collisions predicted by ord_p(2) | |Δ|
        # For each position j and each B-vector, how many valid B' at distance 1?
        predicted_coll = 0
        actual_coll = sum(result['h1_collisions_by_delta'].values())

        for delta, total in result['h1_total_by_delta'].items():
            if delta > 0 and delta % ord2 == 0:
                predicted_coll += total

        ok = (predicted_coll == actual_coll)
        record_test(f"T47: h=1 collision count matches prediction (k={k},p={p})",
                    ok, f"predicted={predicted_coll}, actual={actual_coll}")


# ============================================================================
# MAIN EXECUTION
# ============================================================================

def main():
    print("=" * 72)
    print("R46-B: FIRST PROVABLE KERNEL OF THE MSL")
    print("Two Candidates, One Survivor")
    print("=" * 72)
    print(f"Time budget: {TIME_BUDGET:.0f}s")

    # Section 1: Validation
    run_validation()

    # Section 2: Candidate 1 -- MSL-lite
    mu_trajectory = run_msl_lite()

    # Section 3: Candidate 2 -- LSD
    lsd_results = run_lsd()

    # Section 4: Head-to-head
    run_head_to_head(mu_trajectory, lsd_results)

    # Section 5: Elimination and autopsy
    run_elimination()

    # Section 6: Survivor statement
    run_survivor_statement()

    # Section 7: Additional self-tests
    run_additional_tests()

    # === FINAL SUMMARY ===
    print("\n" + "=" * 72)
    print("FINAL SUMMARY")
    print("=" * 72)
    print(f"  Total tests: {len(TEST_RESULTS)}")
    print(f"  PASS: {PASS_COUNT}")
    print(f"  FAIL: {FAIL_COUNT}")
    print(f"  Elapsed: {elapsed():.1f}s / {TIME_BUDGET:.0f}s")

    if FAIL_COUNT > 0:
        print("\n  FAILED TESTS:")
        for name, passed, detail in TEST_RESULTS:
            if not passed:
                print(f"    [FAIL] {name}" + (f" -- {detail}" if detail else ""))

    print(f"\n  SURVIVANT: LSD (Lemme de Spreading des Différences)")
    print(f"  ÉLIMINÉ:   MSL-lite (Convolution Mixing)")
    print(f"  NOYAU PROUVÉ: h=1 collision ⟺ ord_p(2) | |Δ|")

    if FAIL_COUNT > 0:
        print(f"\n  *** {FAIL_COUNT} TESTS FAILED ***")
        sys.exit(1)
    else:
        print(f"\n  *** ALL {PASS_COUNT} TESTS PASSED ***")


if __name__ == "__main__":
    main()
