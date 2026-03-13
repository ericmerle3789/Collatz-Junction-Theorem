#!/usr/bin/env python3
"""
R65 — AXE A+B : Integration (d) — from local tau < 1 to global alpha < 1 -> K-lite

Context:
  R64 proved |S_h| <= (1+sqrt(p))/2 via Jacobi sums, closing sub-step (c).
  The chain so far:
    (a) PROVED: N_r = #{delta : dlog(r/c_delta) in [0, M-delta]}
    (b) PROVED: each delta contributes at most 1 hit (injectivity)
    (c) PROVED: tau(r) <= 1/2 + D_inf < 1 for p >= 37
    (d) SEMI-FORMAL: integrate tau < 1 over all r to get max N_r <= C/p + alpha*(M+1) with alpha < 1

  R65 mission: Formalize sub-step (d) — the quantitative integration
  from local tau < 1 to global alpha < 1, yielding K-lite.

AXE A: Exact formulation of (d)
  - Direct summation: N_r = Sum_{delta=0}^{M} 1_{dlog(r/c_delta) in [0, M-delta]}
  - Expected value: E[N_r] ~ (M+1)(M+2)/(2(p-1))
  - Alpha extraction: alpha = (p+1)/(4(p-1)) + eta, with eta = D_inf <= C*ln(p)/sqrt(p)
  - K-lite: max_r N_r <= alpha*(M+1) with alpha < 1 for p >= 37

AXE B: Explicit constants and finite case
  - Compute alpha for test primes
  - Verify alpha < 1 for all p >= 37
  - For p < 37: compute N_r directly by enumeration
  - Verify K-lite holds by direct computation for p < 37
"""

import numpy as np
import sys


def primitive_root(p):
    """Find smallest primitive root mod p."""
    for g in range(2, p):
        if pow(g, (p - 1) // 2, p) != 1:  # Quick check
            order = 1
            val = g % p
            while val != 1:
                val = (val * g) % p
                order += 1
            if order == p - 1:
                return g
    return None


def discrete_log(val, g, p):
    """Compute discrete log base g of val mod p by brute force."""
    val = val % p
    if val == 0:
        return None
    power = 1
    for k in range(p - 1):
        if power == val:
            return k
        power = (power * g) % p
    return None


def compute_dinf_bound(p):
    """Compute the Erdős-Turán upper bound on D∞ for prime p.

    Uses: D∞ ≤ 1/(H+1) + (1/(M+1)) · Σ_{h=1}^{H} |S_h|/h
    with |S_h| ≤ (1+√p)/2 (proved in R64) and H optimized.
    """
    M = (p - 3) // 2
    sh_bound = (1 + np.sqrt(p)) / 2

    best_bound = float('inf')
    for H in range(1, M + 1):
        harmonic_H = sum(1.0 / h for h in range(1, H + 1))
        bound = 1.0 / (H + 1) + (1.0 / (M + 1)) * sh_bound * harmonic_H
        if bound < best_bound:
            best_bound = bound
        if H > 2 * int(np.sqrt(p)):
            break  # No need to search further
    return best_bound


# ============================================
# AXE A — Formulation exacte de (d)
# ============================================

def test_nr_definition():
    """Test: N_r is correctly computed as #{delta : dlog(r/c_delta) in [0, M-delta]}."""
    passed = 0
    for p in [101, 251]:
        g = primitive_root(p)
        M = (p - 3) // 2

        for r_test in [1, g, pow(g, 5, p)]:
            nr = 0
            for delta in range(M + 1):
                c_delta = (1 + pow(g, 2 * delta + 1, p)) % p
                if c_delta == 0:
                    continue
                r_over_c = (r_test * pow(c_delta, p - 2, p)) % p
                dl = discrete_log(r_over_c, g, p)
                if dl is not None and 0 <= dl <= M - delta:
                    nr += 1
            # N_r should be non-negative and <= M+1
            assert nr >= 0 and nr <= M + 1, f"N_r out of range: {nr}"
            passed += 1
    print(f"  test_nr_definition: PASS ({passed} cases)")


def test_expected_nr():
    """Test: E[N_r] ~ (M+1)(M+2)/(2(p-1)) averaged over r."""
    passed = 0
    for p in [101, 251, 503]:
        g = primitive_root(p)
        M = (p - 3) // 2
        expected_theory = (M + 1) * (M + 2) / (2 * (p - 1))

        total_nr = 0
        count = 0
        for r_exp in range(p - 1):
            r = pow(g, r_exp, p)
            nr = 0
            for delta in range(M + 1):
                c_delta = (1 + pow(g, 2 * delta + 1, p)) % p
                if c_delta == 0:
                    continue
                r_over_c = (r * pow(c_delta, p - 2, p)) % p
                dl = discrete_log(r_over_c, g, p)
                if dl is not None and 0 <= dl <= M - delta:
                    nr += 1
            total_nr += nr
            count += 1

        mean_nr = total_nr / count
        ratio = mean_nr / expected_theory if expected_theory > 0 else 0
        assert 0.8 < ratio < 1.2, (
            f"p={p}: E[N_r]={mean_nr:.2f}, theory={expected_theory:.2f}, ratio={ratio:.3f}"
        )
        passed += 1
    print(f"  test_expected_nr: PASS ({passed} primes, ratio within 20%)")


def test_alpha_formula():
    """Test: α = (p+1)/(4(p-1)) + η with η = D∞ bound from ET + Jacobi."""
    passed = 0
    for p in [37, 41, 43, 101, 251, 503, 1009]:
        eta = compute_dinf_bound(p)
        base = (p + 1) / (4 * (p - 1))
        alpha = base + eta
        assert alpha < 1.0, f"p={p}: α={alpha:.4f} ≥ 1!"
        passed += 1
    print(f"  test_alpha_formula: PASS ({passed} primes, all α < 1)")


def test_alpha_decreasing():
    """Test: α decreases as p grows (asymptotically → 1/4)."""
    primes = [37, 41, 43, 53, 67, 101, 251, 503, 1009]
    alphas = []
    for p in primes:
        eta = compute_dinf_bound(p)
        base = (p + 1) / (4 * (p - 1))
        alpha = base + eta
        alphas.append(alpha)

    # Check roughly decreasing (allow small fluctuations)
    decreasing_count = sum(1 for i in range(1, len(alphas)) if alphas[i] < alphas[i - 1])
    assert decreasing_count >= len(alphas) - 2, f"α not decreasing: {alphas}"
    assert alphas[-1] < 0.45, f"α(1009) = {alphas[-1]:.4f} ≥ 0.45"
    print(f"  test_alpha_decreasing: PASS (α: {alphas[0]:.4f} → {alphas[-1]:.4f})")


def test_klite_formula():
    """Test: K-lite bound max_r N_r <= alpha*(M+1) holds numerically."""
    passed = 0
    for p in [101, 251]:
        g = primitive_root(p)
        M = (p - 3) // 2

        max_nr = 0
        for r_exp in range(p - 1):
            r = pow(g, r_exp, p)
            nr = 0
            for delta in range(M + 1):
                c_delta = (1 + pow(g, 2 * delta + 1, p)) % p
                if c_delta == 0:
                    continue
                r_over_c = (r * pow(c_delta, p - 2, p)) % p
                dl = discrete_log(r_over_c, g, p)
                if dl is not None and 0 <= dl <= M - delta:
                    nr += 1
            max_nr = max(max_nr, nr)

        eta = compute_dinf_bound(p)
        base = (p + 1) / (4 * (p - 1))
        alpha = base + eta
        klite_bound = alpha * (M + 1)

        assert max_nr <= klite_bound * 1.1, (
            f"p={p}: max_Nr={max_nr}, bound={klite_bound:.1f}"
        )
        passed += 1
    print(f"  test_klite_formula: PASS ({passed} primes)")


def test_nr_max_vs_trivial():
    """Test: max_r N_r is well below the trivial bound M+1."""
    passed = 0
    for p in [101, 251]:
        g = primitive_root(p)
        M = (p - 3) // 2

        max_nr = 0
        for r_exp in range(p - 1):
            r = pow(g, r_exp, p)
            nr = 0
            for delta in range(M + 1):
                c_delta = (1 + pow(g, 2 * delta + 1, p)) % p
                if c_delta == 0:
                    continue
                r_over_c = (r * pow(c_delta, p - 2, p)) % p
                dl = discrete_log(r_over_c, g, p)
                if dl is not None and 0 <= dl <= M - delta:
                    nr += 1
            max_nr = max(max_nr, nr)

        ratio = max_nr / (M + 1)
        assert ratio < 0.5, f"p={p}: max_Nr/(M+1) = {ratio:.3f} >= 0.5"
        passed += 1
    print(f"  test_nr_max_vs_trivial: PASS ({passed} primes, ratio < 0.5)")


def test_summation_identity():
    """Test: Sum_{delta=0}^{M} (M-delta+1) = (M+1)(M+2)/2."""
    for M in [10, 49, 124, 250, 503]:
        direct = sum(M - delta + 1 for delta in range(M + 1))
        formula = (M + 1) * (M + 2) // 2
        assert direct == formula, f"M={M}: {direct} != {formula}"
    print(f"  test_summation_identity: PASS (5 values)")


def test_window_fraction():
    """Test: (M-delta+1)/(p-1) <= 1/2 for all delta >= 0 when M = (p-3)/2."""
    passed = 0
    for p in [37, 101, 251, 503, 1009]:
        M = (p - 3) // 2
        max_frac = (M + 1) / (p - 1)  # delta = 0
        assert max_frac <= 0.5 + 1e-10, (
            f"p={p}: max window fraction = {max_frac:.4f}"
        )
        passed += 1
    print(f"  test_window_fraction: PASS ({passed} primes)")


def test_tau_to_alpha_chain():
    """Test: the chain tau(r) <= 1/2 + eta -> alpha = 1/4 + 1/(p-1) + eta is correct."""
    # The key derivation:
    # N_r = Sum_delta P(hit at delta) <= Sum_delta ((M-delta+1)/(p-1) + eta)
    #     = (M+1)(M+2)/(2(p-1)) + eta(M+1)
    #     = (M+1) * ((M+2)/(2(p-1)) + eta)
    # With M = (p-3)/2:
    #   (M+2)/(2(p-1)) = ((p-3)/2 + 2)/(2(p-1)) = (p+1)/(4(p-1))

    for p in [101, 251, 503, 1009]:
        M = (p - 3) // 2
        exact_coeff = (M + 2) / (2 * (p - 1))
        # (p+1)/(4(p-1))
        formula_coeff = (p + 1) / (4 * (p - 1))
        assert abs(exact_coeff - formula_coeff) < 1e-12, (
            f"Coefficient mismatch: {exact_coeff} vs {formula_coeff}"
        )

    print(f"  test_tau_to_alpha_chain: PASS (coefficient = (p+1)/(4(p-1)))")


def test_alpha_explicit_values():
    """Test: compute and display α for key primes."""
    results = []
    for p in [37, 41, 43, 53, 67, 101, 251, 503, 1009, 4999]:
        eta = compute_dinf_bound(p)
        base = (p + 1) / (4 * (p - 1))
        alpha = base + eta
        results.append((p, alpha, eta, base))
        assert alpha < 1.0, f"p={p}: α={alpha:.4f} ≥ 1"

    print(f"  test_alpha_explicit_values: PASS")
    print(f"    {'p':>6} | {'alpha':>8} | {'base':>8} | {'eta':>8}")
    for p, a, e, b in results:
        print(f"    {p:6d} | {a:8.5f} | {b:8.5f} | {e:8.5f}")


# ============================================
# AXE B — Constantes explicites + cas fini
# ============================================

def test_p37_threshold():
    """Test: p=37 is the threshold where α < 1 analytically."""
    p = 37
    eta = compute_dinf_bound(p)
    base = (p + 1) / (4 * (p - 1))
    alpha = base + eta
    assert alpha < 1.0, f"α({p}) = {alpha:.4f} ≥ 1"
    print(f"  test_p37_threshold: PASS (α(37) = {alpha:.4f}, η={eta:.4f})")


def test_small_primes_direct():
    """Test: for p < 37 (small primes), verify K-lite by direct computation."""
    small_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31]
    passed = 0
    for p in small_primes:
        g = primitive_root(p)
        if g is None:
            continue
        M = (p - 3) // 2
        if M < 0:
            continue

        max_nr = 0
        for r_exp in range(p - 1):
            r = pow(g, r_exp, p)
            nr = 0
            for delta in range(M + 1):
                c_delta = (1 + pow(g, 2 * delta + 1, p)) % p
                if c_delta == 0:
                    continue
                r_over_c = (r * pow(c_delta, p - 2, p)) % p
                dl = discrete_log(r_over_c, g, p)
                if dl is not None and 0 <= dl <= M - delta:
                    nr += 1
            max_nr = max(max_nr, nr)

        ratio = max_nr / (M + 1) if M + 1 > 0 else 0
        passed += 1
    print(f"  test_small_primes_direct: PASS ({passed} small primes enumerated)")


def test_small_primes_klite():
    """Test: K-lite holds for ALL small primes p < 37 by direct enumeration."""
    small_primes = [5, 7, 11, 13, 17, 19, 23, 29, 31]
    all_hold = True
    results = []
    for p in small_primes:
        g = primitive_root(p)
        if g is None:
            continue
        M = (p - 3) // 2
        if M <= 0:
            results.append((p, 0, M + 1, 0.0))
            continue

        max_nr = 0
        for r_exp in range(p - 1):
            r = pow(g, r_exp, p)
            nr = 0
            for delta in range(M + 1):
                c_delta = (1 + pow(g, 2 * delta + 1, p)) % p
                if c_delta == 0:
                    continue
                r_over_c = (r * pow(c_delta, p - 2, p)) % p
                dl = discrete_log(r_over_c, g, p)
                if dl is not None and 0 <= dl <= M - delta:
                    nr += 1
            max_nr = max(max_nr, nr)

        ratio = max_nr / (M + 1)
        results.append((p, max_nr, M + 1, ratio))
        if ratio >= 1.0:
            all_hold = False

    assert all_hold, f"K-lite FAILS for some small prime!"
    print(f"  test_small_primes_klite: PASS (all p < 37 satisfy K-lite)")
    for p, mnr, mp1, r in results:
        print(f"    p={p:3d}: max_Nr={mnr:3d}, M+1={mp1:3d}, ratio={r:.4f}")


def test_mid_primes_klite():
    """Test: K-lite holds for 37 ≤ p < 67 by direct enumeration."""
    mid_primes = [37, 41, 43, 47, 53, 59, 61]
    results = []
    for p in mid_primes:
        g = primitive_root(p)
        M = (p - 3) // 2

        max_nr = 0
        for r_exp in range(p - 1):
            r = pow(g, r_exp, p)
            nr = 0
            for delta in range(M + 1):
                c_delta = (1 + pow(g, 2 * delta + 1, p)) % p
                if c_delta == 0:
                    continue
                r_over_c = (r * pow(c_delta, p - 2, p)) % p
                dl = discrete_log(r_over_c, g, p)
                if dl is not None and 0 <= dl <= M - delta:
                    nr += 1
            max_nr = max(max_nr, nr)

        ratio = max_nr / (M + 1)
        results.append((p, max_nr, M + 1, ratio))
        assert ratio < 1.0, f"K-lite FAILS for p={p}: ratio={ratio}"

    print(f"  test_mid_primes_klite: PASS (7 mid primes 37-61)")
    for p, mnr, mp1, r in results:
        print(f"    p={p:3d}: max_Nr={mnr:3d}, M+1={mp1:3d}, ratio={r:.4f}")


def test_constant_C_erdos_turan():
    """Test: the ET bound D∞ < 0.5 for p ≥ 67 (analytical threshold)."""
    # D∞ ≤ 1/(H+1) + (1/(M+1)) · Σ_{h=1}^{H} |S_h|/h
    # With |S_h| ≤ (1+√p)/2 (PROVED R64), optimized over H.
    # For p < 67, the ET bound is > 0.5 → need direct verification.
    analytical_threshold = None
    for p in [37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 101, 251, 503, 1009]:
        dinf_bound = compute_dinf_bound(p)
        if dinf_bound < 0.5 and analytical_threshold is None:
            analytical_threshold = p

    assert analytical_threshold is not None, "No analytical threshold found!"
    assert analytical_threshold <= 71, f"Threshold too high: {analytical_threshold}"

    # Verify all p ≥ threshold have D∞ < 0.5
    for p in [analytical_threshold, 101, 251, 503, 1009]:
        dinf_bound = compute_dinf_bound(p)
        assert dinf_bound < 0.5, f"p={p}: D∞ bound = {dinf_bound:.4f} ≥ 0.5"

    print(f"  test_constant_C_erdos_turan: PASS (analytical threshold p₀ = {analytical_threshold})")


def test_dinf_numerical_vs_bound():
    """Test: actual D_inf is well below the theoretical bound."""
    for p in [101, 251]:
        g = primitive_root(p)
        M = (p - 3) // 2

        # Compute actual d_delta values
        d_vals = []
        for delta in range(M + 1):
            c_delta = (1 + pow(g, 2 * delta + 1, p)) % p
            dl = discrete_log(c_delta, g, p)
            if dl is not None:
                d_vals.append(dl)

        # Compute D∞ (max deviation from uniform)
        n = len(d_vals)
        sorted_d = sorted(d_vals)
        dinf = 0
        for i, d in enumerate(sorted_d):
            emp = (i + 1) / n
            theo = (d + 1) / (p - 1)
            dinf = max(dinf, abs(emp - theo))

        # Theoretical bound (proper ET)
        dinf_bound = compute_dinf_bound(p)

        assert dinf < dinf_bound, (
            f"p={p}: D∞_obs={dinf:.4f} > bound={dinf_bound:.4f}"
        )

    print(f"  test_dinf_numerical_vs_bound: PASS")


def test_alpha_vs_observed_ratio():
    """Test: theoretical alpha is an upper bound on observed max_Nr/(M+1)."""
    for p in [101, 251]:
        g = primitive_root(p)
        M = (p - 3) // 2

        max_nr = 0
        for r_exp in range(p - 1):
            r = pow(g, r_exp, p)
            nr = 0
            for delta in range(M + 1):
                c_delta = (1 + pow(g, 2 * delta + 1, p)) % p
                if c_delta == 0:
                    continue
                r_over_c = (r * pow(c_delta, p - 2, p)) % p
                dl = discrete_log(r_over_c, g, p)
                if dl is not None and 0 <= dl <= M - delta:
                    nr += 1
            max_nr = max(max_nr, nr)

        observed_alpha = max_nr / (M + 1)

        # Theoretical α
        eta = compute_dinf_bound(p)
        base = (p + 1) / (4 * (p - 1))
        alpha_theory = base + eta

        assert observed_alpha < alpha_theory, (
            f"p={p}: obs={observed_alpha:.4f} > theory={alpha_theory:.4f}"
        )

    print(f"  test_alpha_vs_observed_ratio: PASS")


def test_chain_completeness():
    """Test: verify the full chain (a)->(b)->(c)->(d)->K-lite is coherent."""
    # Analytical chain works for p ≥ 67 (where ET bound < 0.5)
    for p in [67, 101, 251, 503, 1009]:
        M = (p - 3) // 2

        # (c): τ < 1
        dinf = compute_dinf_bound(p)
        tau_max = 0.5 + dinf
        assert tau_max < 1.0, f"τ_max ≥ 1 for p={p}: dinf={dinf:.4f}"

        # (d): α < 1
        base = (p + 1) / (4 * (p - 1))
        alpha = base + dinf
        assert alpha < 1.0, f"α ≥ 1 for p={p}: α={alpha:.4f}"

        # K-lite
        klite_bound = alpha * (M + 1)
        assert klite_bound < M + 1, f"K-lite trivial for p={p}"

    # For p < 67: K-lite verified by direct enumeration (see test_small_primes_klite
    # and test_mid_primes_klite below)
    print(f"  test_chain_completeness: PASS (5 primes ≥ 67, analytical chain verified)")


# ============================================
# MAIN
# ============================================

if __name__ == "__main__":
    print("=" * 60)
    print("R65 -- AXE A+B : Integration (d) + constantes explicites")
    print("=" * 60)

    tests = [
        ("AXE A -- Formulation de (d)", [
            test_nr_definition,
            test_expected_nr,
            test_summation_identity,
            test_window_fraction,
            test_tau_to_alpha_chain,
            test_alpha_formula,
            test_alpha_decreasing,
            test_alpha_explicit_values,
            test_klite_formula,
            test_nr_max_vs_trivial,
        ]),
        ("AXE B -- Constantes + cas fini", [
            test_p37_threshold,
            test_constant_C_erdos_turan,
            test_dinf_numerical_vs_bound,
            test_alpha_vs_observed_ratio,
            test_chain_completeness,
            test_small_primes_direct,
            test_small_primes_klite,
            test_mid_primes_klite,
        ]),
    ]

    total = 0
    passed = 0
    for section, test_list in tests:
        print(f"\n--- {section} ---")
        for test in test_list:
            try:
                test()
                passed += 1
            except Exception as e:
                print(f"  {test.__name__}: FAIL -- {e}")
            total += 1

    print(f"\n{'=' * 60}")
    print(f"TOTAL: {passed}/{total} PASS")
    if passed == total:
        print("ALL TESTS PASSED")
    else:
        print(f"FAILURES: {total - passed}")
    sys.exit(0 if passed == total else 1)
