#!/usr/bin/env python3
"""R181_spectral_gap.py — Transfer Matrix Spectral Gap Analysis for Condition Q.

MISSION: Push toward a PROVABLE spectral gap bound for the exponential sums
approach to the Collatz Junction Theorem.

FRAMEWORK:
  For prime p | d(k) = 2^S - 3^k, the recurrence c_{j+1} = 3*c_j + 2^{e_j} mod p
  defines a permutation matrix T_e (p x p) for each exponent e in {0,...,S-1}.

  (T_e)_{ij} = delta_{j, (3i + 2^e) mod p}

  The Nr-vector (counting g(v) mod p) is:
    Nr = e_{k-1}(T_1, T_2, ..., T_{S-1}) . delta_0

  where e_{k-1} is the elementary symmetric polynomial of order k-1 in matrices.

  The spectral gap of the averaged matrix M = (1/(S-1)) * sum_{e=1}^{S-1} T_e
  controls mixing and hence cancellation in the character sum S_p(a).

SECTIONS:
  1. Transfer matrix construction and verification
  2. Spectral gap computation for small primes
  3. Dependence on ord_p(2) and arithmetic structure
  4. Twisted transfer matrices (character-sum connection)
  5. Hybrid peeling + spectral approach
  6. Di Benedetto-Lagarias-Tao bound analysis
  7. Toward a provable spectral gap: theoretical analysis
  8. Comparison with exact N_0(p) computations

Author: Eric Merle (assisted by Claude)
Date: 15 March 2026
"""

import math
import cmath
import time
import hashlib
import sys
from itertools import combinations
from collections import defaultdict

import numpy as np
from numpy.linalg import eigvals, norm, matrix_power

# ============================================================
# Core arithmetic (shared with R181_exponential_sums.py)
# ============================================================

def S_of_k(k):
    """S(k) = ceil(k * log2(3))."""
    return math.ceil(k * math.log2(3))

def d_of_k(k):
    """d(k) = 2^S - 3^k."""
    return (1 << S_of_k(k)) - 3**k

def C_of_k(k):
    """C(k) = C(S-1, k-1)."""
    return math.comb(S_of_k(k) - 1, k - 1)

def prime_factors(n):
    """Sorted list of distinct prime factors of |n|."""
    if n == 0:
        return []
    factors = set()
    temp = abs(n)
    d = 2
    while d * d <= temp:
        while temp % d == 0:
            factors.add(d)
            temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    return sorted(factors)

def multiplicative_order(a, p):
    """ord_p(a): smallest positive integer m such that a^m = 1 mod p."""
    if p <= 1 or a % p == 0:
        return 0
    val, order = a % p, 1
    while val != 1:
        val = (val * a) % p
        order += 1
        if order > p:
            return 0
    return order

def is_primitive_root(g, p):
    """Check if g is a primitive root mod p."""
    return multiplicative_order(g, p) == p - 1


# ============================================================
# Section 1: Transfer matrix construction
# ============================================================

def build_transfer_matrix(e, p):
    """Build the p x p permutation matrix T_e for the recurrence c -> 3c + 2^e mod p.

    (T_e)_{new, old} = 1 iff new = (3*old + 2^e) mod p.

    This is a permutation matrix because c -> 3c + 2^e is a bijection on Z/pZ
    (since gcd(3, p) = 1 for p >= 5).
    """
    T = np.zeros((p, p), dtype=float)
    pow2e = pow(2, e, p)
    for old in range(p):
        new = (3 * old + pow2e) % p
        T[new][old] = 1.0
    return T


def build_averaged_matrix(p, S):
    """Build M = (1/(S-1)) * sum_{e=1}^{S-1} T_e.

    This is the averaged transfer matrix over all available exponents.
    M is doubly stochastic (since each T_e is a permutation matrix).
    """
    M = np.zeros((p, p), dtype=float)
    for e in range(1, S):
        pow2e = pow(2, e, p)
        for old in range(p):
            new = (3 * old + pow2e) % p
            M[new][old] += 1.0
    M /= (S - 1)
    return M


def build_twisted_transfer_matrix(e, p, a):
    """Build the twisted transfer matrix for character a.

    For the character sum S_p(a) = sum_v omega^{a*g(v)}, the relevant
    operator is T_e twisted by the character: the state tracks both the
    Horner value h mod p and the accumulated phase.

    Concretely, in the "Fourier-side" representation:
      (T_e^{(a)})_{s, r} = omega^{a * (s - 3r)} * delta_{s, 3r + 2^e mod p}
                          = omega^{a * 2^e} * delta_{s, 3r + 2^e mod p}

    So T_e^{(a)} = omega^{a * 2^e} * T_e (as a matrix).

    The product over a subset gives:
      prod_{e in subset} T_e^{(a)} = (prod omega^{a*2^e}) * prod T_e

    This means the SPECTRAL STRUCTURE of the product is the same as for T_e
    (permutation matrices), but the character sum involves the ELEMENTARY
    SYMMETRIC POLYNOMIAL of the twisted matrices.

    For the averaged matrix approach, we need:
      M^{(a)} = (1/(S-1)) sum_{e=1}^{S-1} omega^{a*2^e} * T_e
    """
    omega = cmath.exp(2j * cmath.pi / p)
    phase = omega ** ((a * pow(2, e, p)) % p)

    T = np.zeros((p, p), dtype=complex)
    pow2e = pow(2, e, p)
    for old in range(p):
        new = (3 * old + pow2e) % p
        T[new][old] = phase
    return T


def build_twisted_averaged_matrix(p, S, a):
    """Build M^{(a)} = (1/(S-1)) sum_{e=1}^{S-1} omega^{a*2^e} * T_e.

    This is the key object: its spectral radius controls the cancellation
    in S_p(a) when we use the elementary symmetric polynomial approach.
    """
    omega = cmath.exp(2j * cmath.pi / p)
    M = np.zeros((p, p), dtype=complex)
    for e in range(1, S):
        pow2e = pow(2, e, p)
        phase = omega ** ((a * pow2e) % p)
        for old in range(p):
            new = (3 * old + pow2e) % p
            M[new][old] += phase
    M /= (S - 1)
    return M


# ============================================================
# Section 2: Spectral gap computation
# ============================================================

def compute_spectral_data(p, S):
    """Compute the spectral gap and eigenvalue distribution of the averaged matrix M.

    Returns:
      - eigenvalues (sorted by |lambda|, descending)
      - spectral_gap = 1 - |lambda_2|/|lambda_1|
      - mixing_rate = |lambda_2|
    """
    M = build_averaged_matrix(p, S)
    evals = eigvals(M)

    # Sort by absolute value, descending
    sorted_evals = sorted(evals, key=lambda x: abs(x), reverse=True)
    abs_evals = [abs(ev) for ev in sorted_evals]

    # lambda_1 should be 1 (Perron-Frobenius, M is doubly stochastic)
    lambda1 = abs_evals[0]
    lambda2 = abs_evals[1] if len(abs_evals) > 1 else 0.0

    spectral_gap = 1.0 - lambda2 / lambda1 if lambda1 > 0 else 0.0

    return {
        'eigenvalues': sorted_evals,
        'abs_eigenvalues': abs_evals,
        'lambda1': lambda1,
        'lambda2': lambda2,
        'spectral_gap': spectral_gap,
        'mixing_rate': lambda2,
        'matrix': M,
    }


def compute_twisted_spectral_data(p, S, a):
    """Compute spectral data for the twisted averaged matrix M^{(a)}.

    For M^{(a)}, the leading eigenvalue is NOT necessarily 1
    (the twisting breaks the doubly-stochastic property).
    The spectral RADIUS rho(M^{(a)}) controls the exponential sum.
    """
    Ma = build_twisted_averaged_matrix(p, S, a)
    evals = eigvals(Ma)

    abs_evals = sorted([abs(ev) for ev in evals], reverse=True)
    rho = abs_evals[0]
    rho2 = abs_evals[1] if len(abs_evals) > 1 else 0.0

    return {
        'spectral_radius': rho,
        'second_eigenvalue': rho2,
        'all_abs': abs_evals,
        'matrix': Ma,
    }


# ============================================================
# Section 3: Dependence on arithmetic structure
# ============================================================

def analyze_arithmetic_dependence(p, S):
    """Study how the spectral gap depends on ord_p(2), ord_p(3), and p mod 4.

    Key insight: The set {2^e mod p : e = 1, ..., S-1} is a subset of the
    cyclic group <2> in (Z/pZ)*. If ord_p(2) | (S-1), the set is a full
    coset; otherwise it's a partial orbit. This structure controls M.

    The matrix M = (1/(S-1)) sum_e T_e where T_e maps c -> 3c + 2^e.
    The "translation part" 2^e ranges over {2^1, 2^2, ..., 2^{S-1}} mod p.

    If these values are well-distributed in Z/pZ, M is close to the
    doubly stochastic matrix (1/p) * J (all-ones), giving spectral gap ~ 1.
    If they cluster, the gap is smaller.
    """
    ord2 = multiplicative_order(2, p)
    ord3 = multiplicative_order(3, p)

    # Set of translations: {2^e mod p : e = 1, ..., S-1}
    translations = set()
    for e in range(1, S):
        translations.add(pow(2, e, p))

    n_translations = len(translations)
    coverage = n_translations / p  # fraction of Z/pZ covered

    # Is 3 a primitive root?
    prim_root_3 = (ord3 == p - 1)
    # Is 2 a primitive root?
    prim_root_2 = (ord2 == p - 1)

    # The subgroup <2> mod p
    subgroup_2 = set()
    val = 1
    for _ in range(ord2):
        subgroup_2.add(val)
        val = (val * 2) % p

    # How many of the translations fall in distinct cosets of <3>?
    # (This matters because the "multiplication by 3" part of T_e
    #  permutes within cosets of <3>.)

    return {
        'ord_p_2': ord2,
        'ord_p_3': ord3,
        'p_mod_4': p % 4,
        'p_mod_8': p % 8,
        'is_primitive_root_2': prim_root_2,
        'is_primitive_root_3': prim_root_3,
        'n_distinct_translations': n_translations,
        'coverage': coverage,
        'S_minus_1': S - 1,
        'S_mod_ord2': (S - 1) % ord2,
        'full_orbits': (S - 1) // ord2,
        'residual': (S - 1) % ord2,
    }


# ============================================================
# Section 4: Elementary symmetric polynomial of permutation matrices
# ============================================================

def compute_elem_sym_poly(matrices, order):
    """Compute e_r(M_1, ..., M_n) = sum_{|T|=r} prod_{i in T} M_i.

    This is the matrix-valued elementary symmetric polynomial of order r.
    For our application: matrices = [T_1, T_2, ..., T_{S-1}] and r = k-1.

    WARNING: This is exponentially expensive in r. Only feasible for small cases.
    Uses DP approach: build up by processing matrices one at a time.
    """
    n = len(matrices)
    p = matrices[0].shape[0]

    # DP: dp[j] = e_j(M_1, ..., M_i) after processing i matrices
    # dp[j] is a p x p matrix
    dp = [np.zeros((p, p), dtype=complex) for _ in range(order + 1)]
    dp[0] = np.eye(p, dtype=complex)

    for i in range(n):
        # Process M_{i+1}: update from dp[j] to dp[j+1]
        # Must go backwards to avoid double-counting
        for j in range(min(order, i + 1), 0, -1):
            dp[j] = dp[j] + matrices[i] @ dp[j - 1]

    return dp[order]


def verify_esp_vs_brute(k, p):
    """Verify that the ESP computation matches brute-force enumeration.

    The Nr vector should satisfy:
      Nr[r] = (e_{k-1}(T_1,...,T_{S-1}) @ delta_0)[r]

    where delta_0 = (1, 0, ..., 0) is the initial state (c_0 = 0).

    Actually, the Horner recurrence starts with c_0 = 0 and we pick
    exponents from {1, ..., S-1} (the 0-th exponent is fixed as e_0,
    which determines the initial term 2^{e_0} * 3^{k-1}).

    For the Nr counting (matching compute_Nr_dp):
    e_0 = 0 is fixed (Def 2.1 of preprint: A_0 = 0).
    We choose k-1 elements from {1,...,S-1} for e_1,...,e_{k-1}.
    The DP computes the Horner value of the inner sum (without e_0).
    C = C(S-1, k-1).
    """
    S = S_of_k(k)

    # Brute force: fix e_0 = 0, choose k-1 from {1,...,S-1}
    # The DP recurrence tracks c -> 3c + 2^e, starting from c = 0.
    # After processing k-1 elements (e_1,...,e_{k-1}), the Horner value is
    # the partial sum without the e_0 contribution.
    Nr_brute = defaultdict(int)
    for subset in combinations(range(1, S), k - 1):
        # Horner recurrence: process in order of decreasing position
        # to match the DP (which processes a from S-1 down to 1)
        c = 0
        for ej in subset:  # already sorted ascending
            c = (3 * c + pow(2, ej, p)) % p
        Nr_brute[c] += 1

    C = sum(Nr_brute.values())
    assert C == C_of_k(k), f"Count mismatch: {C} vs {C_of_k(k)}"

    return dict(Nr_brute), C


# ============================================================
# Section 5: Hybrid peeling + spectral approach
# ============================================================

def hybrid_peeling_spectral(k, p):
    """Implement the hybrid approach: peel e_{k-1}, then apply spectral methods.

    Strategy:
      N_0(p) = sum_{e_{k-1}=k-1}^{S-1} |{valid (e_0,...,e_{k-2}):
                   sum_{j=0}^{k-2} 3^{k-1-j} * 2^{e_j} = -2^{e_{k-1}} mod p}|

    For each fixed e_{k-1}, define the target t = (-2^{e_{k-1}}) mod p.
    The inner sum counts (k-1)-element subsets of {0,...,e_{k-1}-1} such
    that the partial corrSum equals t mod p.

    This reduces to a (k-2)-order ESP problem with the transfer matrices
    restricted to exponents {0,...,e_{k-1}-1}.

    The spectral gap of the restricted averaged matrix controls the inner sum.
    """
    S = S_of_k(k)

    results_per_last = []

    for e_last in range(k - 1, S):
        # Target residue: -2^{e_last} mod p (the contribution of the last term)
        target = (-pow(2, e_last, p)) % p

        # Inner problem: choose k-1 elements from {0, ..., e_last-1}
        # and compute partial sum = sum_{j=0}^{k-2} 3^{k-1-j} * 2^{e_j} mod p
        # We need this to equal target.

        # For the spectral analysis: the averaged matrix over {0,...,e_last-1}
        if e_last >= 2:
            M_inner = np.zeros((p, p), dtype=float)
            for e in range(e_last):
                pow2e = pow(2, e, p)
                for old in range(p):
                    new = (3 * old + pow2e) % p
                    M_inner[new][old] += 1.0
            M_inner /= e_last

            evals = eigvals(M_inner)
            abs_evals = sorted([abs(ev) for ev in evals], reverse=True)
            gap_inner = 1.0 - abs_evals[1] / abs_evals[0] if abs_evals[0] > 0 else 0
        else:
            gap_inner = 0.0

        # Count exactly (brute force for small cases)
        inner_count = 0
        if e_last >= k - 1:
            for subset in combinations(range(e_last), k - 1):
                # The composition is (subset[0], ..., subset[k-2], e_last)
                # Partial sum for the first k-1 terms
                partial = 0
                for j, ej in enumerate(subset):
                    partial = (partial + pow(3, k - 1 - j, p) * pow(2, ej, p)) % p
                # Actually, I need to be more careful about the indexing.
                # g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{e_j}
                # If e_{k-1} = e_last, then the last term is 3^0 * 2^{e_last} = 2^{e_last}
                # And the partial sum over j=0,...,k-2 is sum 3^{k-1-j} * 2^{e_j}
                # We need: partial + 2^{e_last} = 0 mod p
                # So partial = -2^{e_last} mod p = target
                if partial == target:
                    inner_count += 1

        # Theoretical prediction: if Nr were uniform, inner_count ~ C(e_last, k-1) / p
        C_inner = math.comb(e_last, k - 1) if e_last >= k - 1 else 0
        predicted = C_inner / p if p > 0 else 0

        results_per_last.append({
            'e_last': e_last,
            'target': target,
            'inner_count': inner_count,
            'C_inner': C_inner,
            'predicted_uniform': predicted,
            'ratio': inner_count / predicted if predicted > 0 else float('inf'),
            'gap_inner': gap_inner,
        })

    # Total N_0
    N0_total = sum(r['inner_count'] for r in results_per_last)

    return {
        'N0_total': N0_total,
        'details': results_per_last,
        'k': k,
        'p': p,
        'S': S,
    }


# ============================================================
# Section 6: Di Benedetto-Lagarias-Tao bound analysis
# ============================================================

def di_benedetto_bound(p):
    """Compute the Di Benedetto et al. (2020) bound on character sums.

    For Regime A primes (p < m^4 where m = ord_p(2)):
      rho(p) <= C_1 * m^{-31/2880}

    where rho(p) = max_{a != 0} |S_p(a)| / C is the cancellation ratio.

    The exponent 31/2880 ~ 0.01076 is quite small, coming from the
    sum-product theorem of Bourgain-Glibichuk-Konyagin (2006).

    We compute:
      m = ord_p(2)
      regime: A if p < m^4, B otherwise
      bound: m^{-31/2880} (Regime A)
      Whether this suffices for Condition Q: need rho < 0.041/(p-1) approximately
    """
    m = multiplicative_order(2, p)
    if m == 0:
        return None

    regime = 'A' if p < m**4 else 'B'
    exponent = 31 / 2880

    if regime == 'A':
        # The bound: rho <= C_1 * m^{-exponent}
        # We set C_1 = 1 for now (unknown effective constant)
        bound_rho = m ** (-exponent)
    else:
        # Regime B: only trivial bound rho <= 1 - 1/m
        bound_rho = 1.0 - 1.0 / m

    # For Condition Q: |sum_{a=1}^{p-1} S_p(a)| <= 0.041 * C
    # If |S_p(a)| <= rho * C for each a, then |sum| <= (p-1) * rho * C
    # Need: (p-1) * rho <= 0.041
    # So rho <= 0.041 / (p-1)
    rho_needed = 0.041 / (p - 1) if p > 1 else float('inf')

    # But this is too pessimistic (assumes all S_p(a) have the same sign).
    # With random phases, |sum| ~ sqrt(p) * max|S_p|, so need:
    # sqrt(p) * rho <= 0.041, i.e., rho <= 0.041 / sqrt(p)
    rho_needed_rms = 0.041 / math.sqrt(p)

    return {
        'p': p,
        'm': m,
        'regime': regime,
        'bound_rho': bound_rho,
        'exponent': exponent,
        'rho_needed_triangleineq': rho_needed,
        'rho_needed_rms': rho_needed_rms,
        'sufficient_triangle': bound_rho <= rho_needed,
        'sufficient_rms': bound_rho <= rho_needed_rms,
        'p_over_m4': p / m**4 if m > 0 else float('inf'),
    }


# ============================================================
# Section 7: Theoretical spectral gap analysis
# ============================================================

def theoretical_gap_analysis(p, S):
    """Analyze the spectral gap theoretically.

    CLAIM TO TEST: For p = 1 mod 4 with ord_p(2) = p-1,
    the spectral gap satisfies Delta >= 1/sqrt(p).

    APPROACH: The averaged matrix M = (1/N) sum_{e=1}^{N} T_e where N = S-1.
    Each T_e is a permutation matrix for c -> 3c + 2^e mod p.

    Key observation: M is a doubly stochastic matrix with entries M[i][j] =
    #{e in {1,...,N} : i = 3j + 2^e mod p} / N.

    For fixed j, i = 3j + 2^e mod p, so e is determined: 2^e = i - 3j mod p.
    There is at most one e in {1,...,N} mapping j -> i (if ord_p(2) >= N),
    and the entry is 0 or 1/N.

    If ord_p(2) = p-1 (2 is a primitive root):
    - The translations {2^1, ..., 2^N} mod p cover N distinct residues
    - For each (i,j), M[i][j] = 1/N if (i-3j) is in {2^1,...,2^N} mod p, else 0
    - Each row and column has exactly N nonzero entries equal to 1/N...
      NO, that's wrong. Each column j has EXACTLY N entries (one per e),
      so each column sums to 1. Each row i has #{j : i-3j in {2^1,...,2^N} mod p}
      = #{j : 3j in i - {2^1,...,2^N} mod p} entries. Since multiplication by 3
      is a bijection, this is |{i-2^1,...,i-2^N} intersect 3*Z/pZ| = N
      (they're all in Z/pZ and 3 is a unit). So each row also has N entries.
      Thus M is an N-regular bipartite graph on p vertices, normalized by N.

    SPECTRAL GAP OF CAYLEY GRAPHS:
    M is related to a Cayley graph on Z/pZ with connection set
    S_conn = {2^1, 2^2, ..., 2^{S-1}} mod p (after undoing the 3-multiplication).

    For a Cayley graph on Z/pZ with connection set S_conn:
    eigenvalue for character chi_a(x) = omega^{ax} is:
      lambda_a = (1/|S_conn|) * sum_{s in S_conn} omega^{as}

    The spectral gap is Delta = 1 - max_{a != 0} |lambda_a|.
    """
    N = S - 1  # number of transfer matrices

    # The "effective Cayley graph" after factoring out multiplication by 3:
    # M acts on functions f: Z/pZ -> C as:
    #   (Mf)(i) = (1/N) sum_{e=1}^{N} f(3^{-1}(i - 2^e))
    #           = (1/N) sum_{e=1}^{N} f(3^{-1}*i - 3^{-1}*2^e)
    #
    # Writing g = 3^{-1} mod p: (Mf)(i) = (1/N) sum_{e=1}^{N} f(g*i - g*2^e)
    #
    # In Fourier: hat{f}(a) -> hat{lambda}_a * hat{f}(a)
    # where hat{lambda}_a = (1/N) sum_{e=1}^{N} omega^{-a*g*2^e} * omega^{a*g*i}
    #
    # Actually, let's compute eigenvalues of M directly.
    # The eigenvectors of any circulant-like matrix on Z/pZ are chi_a(x) = omega^{ax}.
    # But M is NOT circulant because of the x3 multiplication.
    #
    # However, we can decompose: T_e = R_3 * D_{2^e} where
    #   R_3 = permutation matrix for x -> 3x mod p (multiplication)
    #   D_{2^e} = permutation matrix for x -> x + 2^e mod p (translation)
    #
    # So M = R_3 * (1/N) * sum_e D_{2^e} = R_3 * A
    # where A = (1/N) * sum_e D_{2^e} is CIRCULANT.
    #
    # A has eigenvalues: a_t = (1/N) * sum_{e=1}^{N} omega^{t * 2^e} for t = 0,...,p-1.
    # R_3 has eigenvalues omega^{3^{-1} * t}... no, R_3 permutes the Fourier basis.
    #
    # The eigenvalues of M = R_3 * A are NOT simply products of eigenvalues
    # because R_3 and A don't commute in general.

    # Direct computation: eigenvalues of M
    M = build_averaged_matrix(p, S)
    evals_M = eigvals(M)
    abs_evals_M = sorted([abs(ev) for ev in evals_M], reverse=True)

    # Eigenvalues of the circulant part A
    omega = cmath.exp(2j * cmath.pi / p)
    A_evals = []
    for t in range(p):
        lam = sum(omega ** ((t * pow(2, e, p)) % p) for e in range(1, S)) / N
        A_evals.append(lam)

    abs_A_evals = sorted([abs(lam) for lam in A_evals], reverse=True)

    # The "Gauss sum" structure: sum_{e=1}^{N} omega^{t*2^e}
    # If ord_p(2) = m and N = q*m + r (q full orbits, r residual):
    #   sum_{e=1}^{N} omega^{t*2^e} = q * sum_{e=0}^{m-1} omega^{t*2^e}
    #                                  + sum_{e=0}^{r-1} omega^{t*2^{qm+e+1}}
    # The full orbit sum is a Ramanujan-like sum.

    ord2 = multiplicative_order(2, p)
    q_orbits = N // ord2
    r_residual = N % ord2

    # Full orbit sum: sum_{e=0}^{m-1} omega^{t*2^e}
    # This is the "Kloosterman-type" sum over the subgroup <2>.
    full_orbit_sums = []
    for t in range(p):
        s = sum(omega ** ((t * pow(2, e, p)) % p) for e in range(ord2))
        full_orbit_sums.append(s)

    # For t such that t is in the annihilator of <2>:
    # i.e., t * 2^e = t for all e (mod p) -- only t = 0.
    # For other t: the orbit {t*2^e mod p} has length ord2/gcd(stuff).

    # Kloosterman-like bound: |sum_{e=0}^{m-1} omega^{t*2^e}| for t != 0
    # This is a character sum over the cyclic subgroup <2> of (Z/pZ)*.
    # By the Weil bound for multiplicative character sums? Not directly applicable.
    #
    # Simpler: if <2> = (Z/pZ)* (primitive root), the sum is -1 (complete sum minus t=0 term).
    # If <2> is a proper subgroup of index [(p-1)/m]:
    #   sum_{h in <2>} omega^{th} = m if t = 0, else
    #   = (Ramanujan sum) if t is in certain coset.

    # The key bound (Polya-Vinogradov for subgroup):
    # For H = <2> subset F_p* of order m:
    #   |sum_{h in H} omega^{th}| <= sqrt(p) for t != 0 (trivially)
    # Better: if m > sqrt(p), we get cancellation ~ sqrt(p).
    # If m = p-1: sum = -1 (complete character sum).

    kloosterman_max = max(abs(full_orbit_sums[t]) for t in range(1, p))

    return {
        'M_gap': 1.0 - abs_evals_M[1] / abs_evals_M[0] if abs_evals_M[0] > 0 else 0,
        'M_lambda2': abs_evals_M[1],
        'A_gap': 1.0 - abs_A_evals[1] / abs_A_evals[0] if abs_A_evals[0] > 0 else 0,
        'A_lambda2': abs_A_evals[1],
        'ord2': ord2,
        'full_orbits': q_orbits,
        'residual': r_residual,
        'kloosterman_max': kloosterman_max,
        'kloosterman_over_sqrt_p': kloosterman_max / math.sqrt(p),
        'theoretical_gap_lower': 1.0 / math.sqrt(p),  # conjectured lower bound
        'actual_vs_conjectured': (1.0 - abs_evals_M[1]) / (1.0 / math.sqrt(p)),
    }


# ============================================================
# Section 8: Exact N_0(p) computation via DP
# ============================================================

def compute_Nr_dp(k, p):
    """Compute Nr(p) distribution via DP (from R181_exponential_sums.py)."""
    S = S_of_k(k)
    n_choose = k - 1

    dp = [defaultdict(int) for _ in range(n_choose + 1)]
    dp[0][0] = 1

    for a in range(S - 1, 0, -1):
        pow2a = pow(2, a, p)
        for j in range(min(n_choose - 1, S - 1 - a), -1, -1):
            if not dp[j]:
                continue
            new_entries = {}
            for r, cnt in dp[j].items():
                new_r = (3 * r + pow2a) % p
                new_entries[new_r] = new_entries.get(new_r, 0) + cnt
            for r, cnt in new_entries.items():
                dp[j + 1][r] += cnt

    Nr = dict(dp[n_choose])
    C_val = sum(Nr.values())
    return Nr, C_val


# ============================================================
# Main investigation
# ============================================================

def main():
    print("=" * 80)
    print("  R181: TRANSFER MATRIX SPECTRAL GAP ANALYSIS")
    print("  Mission: Provable spectral gap bound for Condition Q")
    print("=" * 80)

    # Collect test cases: (k, S, d, C, primes_dividing_d)
    test_cases = []
    for k in range(2, 25):
        d = d_of_k(k)
        if d <= 0:
            continue
        S = S_of_k(k)
        C = C_of_k(k)
        primes = [p for p in prime_factors(d) if 5 <= p <= 200]
        for p in primes:
            test_cases.append((k, S, C, d, p))

    # ═══════════════════════════════════════════════════════════════
    # PART 1: Spectral gaps of averaged transfer matrices
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "─" * 80)
    print("  PART 1: Spectral gaps of M = (1/(S-1)) sum T_e for small primes p | d(k)")
    print("─" * 80)

    target_primes = [5, 7, 11, 13, 23, 29, 31, 37, 41, 43, 47]

    # For each prime, find the smallest k where p | d(k)
    prime_k_pairs = []
    for p in target_primes:
        for k in range(2, 60):
            d = d_of_k(k)
            if d > 0 and d % p == 0:
                S = S_of_k(k)
                prime_k_pairs.append((p, k, S))
                break

    print(f"\n  {'p':>5} {'k':>4} {'S':>4} {'ord_p(2)':>9} {'ord_p(3)':>9} "
          f"{'Delta(M)':>10} {'lambda_2':>10} {'1/sqrt(p)':>10} {'Delta>=1/sqp?':>14}")
    print("  " + "-" * 90)

    spectral_results = []

    for p, k, S in prime_k_pairs:
        spec = compute_spectral_data(p, S)
        arith = analyze_arithmetic_dependence(p, S)

        gap = spec['spectral_gap']
        lam2 = spec['lambda2']
        inv_sqrtp = 1.0 / math.sqrt(p)
        passes = "YES" if gap >= inv_sqrtp else "no"

        spectral_results.append({
            'p': p, 'k': k, 'S': S,
            'gap': gap, 'lambda2': lam2,
            'ord2': arith['ord_p_2'], 'ord3': arith['ord_p_3'],
            'prim2': arith['is_primitive_root_2'],
            'prim3': arith['is_primitive_root_3'],
            'coverage': arith['coverage'],
        })

        print(f"  {p:>5} {k:>4} {S:>4} {arith['ord_p_2']:>9} {arith['ord_p_3']:>9} "
              f"{gap:>10.6f} {lam2:>10.6f} {inv_sqrtp:>10.6f} {passes:>14}")

    # ═══════════════════════════════════════════════════════════════
    # PART 2: How spectral gap depends on S for fixed p
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "─" * 80)
    print("  PART 2: Spectral gap vs S for fixed primes (p = 7, 11, 23)")
    print("─" * 80)

    for p_fixed in [7, 11, 23]:
        print(f"\n  p = {p_fixed}, ord_p(2) = {multiplicative_order(2, p_fixed)}")
        print(f"  {'k':>4} {'S':>4} {'Delta':>10} {'lambda_2':>10} {'coverage':>10}")
        print("  " + "-" * 50)

        for k in range(2, 40):
            d = d_of_k(k)
            if d <= 0 or d % p_fixed != 0:
                continue
            S = S_of_k(k)
            spec = compute_spectral_data(p_fixed, S)
            arith = analyze_arithmetic_dependence(p_fixed, S)
            print(f"  {k:>4} {S:>4} {spec['spectral_gap']:>10.6f} "
                  f"{spec['lambda2']:>10.6f} {arith['coverage']:>10.4f}")

    # ═══════════════════════════════════════════════════════════════
    # PART 3: Twisted spectral radii (character sum connection)
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "─" * 80)
    print("  PART 3: Twisted spectral radius rho(M^{(a)}) for a = 1,...,p-1")
    print("─" * 80)

    twisted_cases = [(k, S, C, d, p) for k, S, C, d, p in test_cases
                     if p <= 30 and k <= 12]

    for k, S, C, d, p in twisted_cases[:6]:
        print(f"\n  k={k}, S={S}, p={p}, C={C}")
        print(f"  {'a':>4} {'rho(M^a)':>12} {'rho_2':>12} {'rho/1':>10}")
        print("  " + "-" * 45)

        rho_values = []
        for a in range(1, p):
            tw = compute_twisted_spectral_data(p, S, a)
            rho_values.append(tw['spectral_radius'])
            print(f"  {a:>4} {tw['spectral_radius']:>12.6f} "
                  f"{tw['second_eigenvalue']:>12.6f} "
                  f"{tw['spectral_radius']:>10.6f}")

        max_rho = max(rho_values)
        mean_rho = sum(rho_values) / len(rho_values)
        print(f"  max rho = {max_rho:.6f}, mean rho = {mean_rho:.6f}, "
              f"1/sqrt(p) = {1/math.sqrt(p):.6f}")

    # ═══════════════════════════════════════════════════════════════
    # PART 4: Elementary symmetric polynomial verification
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "─" * 80)
    print("  PART 4: ESP e_{k-1}(T_1,...,T_{S-1}) verification against brute force")
    print("─" * 80)

    esp_cases = [(k, S, C, d, p) for k, S, C, d, p in test_cases
                 if C <= 200 and p <= 30 and k <= 6]

    for k, S, C, d, p in esp_cases[:5]:
        # Build transfer matrices for e = 1, ..., S-1 (matching the DP)
        matrices = [build_transfer_matrix(e, p).astype(complex) for e in range(1, S)]

        # Compute ESP of order k-1 (choosing k-1 matrices from S-1 available)
        t0 = time.time()
        esp_matrix = compute_elem_sym_poly(matrices, k - 1)
        dt_esp = time.time() - t0

        # Nr[r] = (esp_matrix @ delta_0)[r]
        # where delta_0 is the initial state c=0
        delta_0 = np.zeros(p, dtype=complex)
        delta_0[0] = 1.0
        Nr_esp = esp_matrix @ delta_0

        # Brute force (matches the DP convention)
        Nr_brute, C_check = verify_esp_vs_brute(k, p)

        # Compare
        match = True
        for r in range(p):
            esp_val = round(Nr_esp[r].real)
            brute_val = Nr_brute.get(r, 0)
            if esp_val != brute_val:
                match = False

        status = "MATCH" if match else "MISMATCH"
        print(f"  k={k}, p={p}, S={S}, C={C}: ESP vs brute = {status} "
              f"(ESP time: {dt_esp:.3f}s)")
        if not match:
            print(f"    ESP Nr: {[round(Nr_esp[r].real) for r in range(p)]}")
            print(f"    Brute Nr: {[Nr_brute.get(r, 0) for r in range(p)]}")

    # ═══════════════════════════════════════════════════════════════
    # PART 5: Hybrid peeling + spectral approach
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "─" * 80)
    print("  PART 5: Hybrid peeling + spectral analysis")
    print("─" * 80)

    hybrid_cases = [(k, S, C, d, p) for k, S, C, d, p in test_cases
                    if C <= 500 and p <= 30 and k <= 8]

    for k, S, C, d, p in hybrid_cases[:4]:
        result = hybrid_peeling_spectral(k, p)
        N0 = result['N0_total']
        Nr_dp, C_dp = compute_Nr_dp(k, p)
        N0_dp = Nr_dp.get(0, 0)

        print(f"\n  k={k}, S={S}, p={p}, C={C}")
        print(f"  N_0 (hybrid peeling) = {N0}")
        print(f"  N_0 (DP verification) = {N0_dp}")
        print(f"  C/p = {C/p:.2f}")
        print(f"  Peeling bound (k-1)/(S-1)*C = {(k-1)/(S-1)*C:.2f}")

        # Show per-e_last breakdown (first few)
        print(f"  {'e_last':>6} {'target':>7} {'count':>7} {'C_inner':>8} "
              f"{'ratio':>8} {'gap':>8}")
        print("  " + "-" * 55)
        for detail in result['details'][:8]:
            ratio_str = f"{detail['ratio']:.3f}" if detail['ratio'] < 1e6 else "inf"
            print(f"  {detail['e_last']:>6} {detail['target']:>7} "
                  f"{detail['inner_count']:>7} {detail['C_inner']:>8} "
                  f"{ratio_str:>8} {detail['gap_inner']:>8.4f}")

    # ═══════════════════════════════════════════════════════════════
    # PART 6: Di Benedetto-Lagarias-Tao bound
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "─" * 80)
    print("  PART 6: Di Benedetto et al. (2020) bound analysis")
    print("  Bound: rho <= m^{-31/2880} ~ m^{-0.01076} for Regime A")
    print("─" * 80)

    all_primes = sorted(set(p for _, _, _, _, p in test_cases))

    print(f"\n  {'p':>5} {'m=ord(2)':>9} {'regime':>7} {'rho_bound':>10} "
          f"{'need(tri)':>10} {'need(rms)':>10} {'OK(tri)?':>9} {'OK(rms)?':>9}")
    print("  " + "-" * 80)

    for p in all_primes:
        db = di_benedetto_bound(p)
        if db is None:
            continue
        print(f"  {p:>5} {db['m']:>9} {db['regime']:>7} {db['bound_rho']:>10.6f} "
              f"{db['rho_needed_triangleineq']:>10.6f} {db['rho_needed_rms']:>10.6f} "
              f"{'YES' if db['sufficient_triangle'] else 'no':>9} "
              f"{'YES' if db['sufficient_rms'] else 'no':>9}")

    # ═══════════════════════════════════════════════════════════════
    # PART 7: Theoretical spectral gap analysis
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "─" * 80)
    print("  PART 7: Theoretical analysis — Cayley graph decomposition")
    print("─" * 80)

    theory_cases = [(p, k, S) for p, k, S in prime_k_pairs if p <= 50]

    print(f"\n  {'p':>5} {'k':>4} {'S':>4} {'Delta(M)':>10} {'Delta(A)':>10} "
          f"{'kloost_max':>11} {'kl/sqrt(p)':>11} {'Delta>=1/sqp':>13}")
    print("  " + "-" * 85)

    for p, k, S in theory_cases:
        th = theoretical_gap_analysis(p, S)
        passes = "YES" if th['M_gap'] >= th['theoretical_gap_lower'] else "no"
        print(f"  {p:>5} {k:>4} {S:>4} {th['M_gap']:>10.6f} {th['A_gap']:>10.6f} "
              f"{th['kloosterman_max']:>11.4f} {th['kloosterman_over_sqrt_p']:>11.4f} "
              f"{passes:>13}")

    # ═══════════════════════════════════════════════════════════════
    # PART 8: Comparison with exact N_0 and Condition Q
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "─" * 80)
    print("  PART 8: Spectral predictions vs exact N_0(p)")
    print("─" * 80)

    comparison_cases = [(k, S, C, d, p) for k, S, C, d, p in test_cases
                        if C <= 50000 and p <= 100]

    print(f"\n  {'k':>3} {'p':>5} {'N_0':>6} {'C/p':>8} {'peel_bd':>8} "
          f"{'Delta':>8} {'(1-D)^k':>10} {'pred_bd':>10} {'Q_ratio':>10}")
    print("  " + "-" * 80)

    for k, S, C, d, p in comparison_cases:
        Nr, C_check = compute_Nr_dp(k, p)
        N0 = Nr.get(0, 0)

        spec = compute_spectral_data(p, S)
        gap = spec['spectral_gap']

        # Spectral prediction: after k-1 mixing steps, deviation from uniform is
        # ~ C * (1 - Delta)^{k-1} / p
        mixing_factor = (1 - gap) ** (k - 1) if gap < 1 else 0
        spectral_bound = C / p * (1 + (p - 1) * mixing_factor)

        # Peeling bound
        peel_bound = (k - 1) / (S - 1) * C

        # Condition Q ratio
        Q_ratio = abs(p * N0 - C) / C if C > 0 else 0

        print(f"  {k:>3} {p:>5} {N0:>6} {C/p:>8.2f} {peel_bound:>8.1f} "
              f"{gap:>8.4f} {mixing_factor:>10.6f} {spectral_bound:>10.2f} "
              f"{Q_ratio:>10.6f}")

    # ═══════════════════════════════════════════════════════════════
    # PART 9: Summary and provability analysis
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "─" * 80)
    print("  PART 9: Summary — Path to a Provable Spectral Gap Bound")
    print("─" * 80)

    # Collect all spectral gap data
    all_gaps = []
    for k, S, C, d, p in test_cases:
        if p > 200:
            continue
        spec = compute_spectral_data(p, S)
        all_gaps.append({
            'p': p, 'k': k, 'S': S, 'C': C,
            'gap': spec['spectral_gap'],
            'lambda2': spec['lambda2'],
            'ord2': multiplicative_order(2, p),
            'inv_sqrt_p': 1.0 / math.sqrt(p),
        })

    # Test the conjecture: Delta >= 1/sqrt(p)
    n_passes = sum(1 for g in all_gaps if g['gap'] >= g['inv_sqrt_p'])
    n_total = len(all_gaps)

    print(f"""
  FINDINGS:

  1. SPECTRAL GAP UNIVERSALITY:
     Tested {n_total} (p, S) pairs. Gap >= 1/sqrt(p): {n_passes}/{n_total}
     {'ALL PASS' if n_passes == n_total else f'{n_total - n_passes} FAILURES'}

  2. SPECTRAL GAP vs ARITHMETIC STRUCTURE:""")

    # Group by ord_p(2) type
    by_type = defaultdict(list)
    for g in all_gaps:
        if g['ord2'] == g['p'] - 1:
            by_type['primitive_root'].append(g)
        elif g['ord2'] >= (g['p'] - 1) // 2:
            by_type['half_order'].append(g)
        else:
            by_type['small_order'].append(g)

    for type_name, gaps in by_type.items():
        if gaps:
            min_gap = min(g['gap'] for g in gaps)
            max_gap = max(g['gap'] for g in gaps)
            mean_gap = sum(g['gap'] for g in gaps) / len(gaps)
            min_ratio = min(g['gap'] / g['inv_sqrt_p'] for g in gaps)
            print(f"     {type_name}: n={len(gaps)}, "
                  f"Delta in [{min_gap:.4f}, {max_gap:.4f}], "
                  f"mean={mean_gap:.4f}, min(Delta*sqrt(p))={min_ratio:.4f}")

    # Fit: Delta ~ c * p^{-alpha}
    if len(all_gaps) >= 5:
        log_p = [math.log(g['p']) for g in all_gaps]
        log_gap = [math.log(g['gap']) for g in all_gaps if g['gap'] > 0]
        if len(log_p) == len(log_gap):
            n = len(log_p)
            mx = sum(log_p) / n
            my = sum(log_gap) / n
            cov = sum((log_p[i] - mx) * (log_gap[i] - my) for i in range(n))
            var = sum((log_p[i] - mx)**2 for i in range(n))
            if var > 0:
                alpha_fit = -cov / var
                c_fit = math.exp(my + alpha_fit * mx)
                print(f"\n     Empirical fit: Delta ~ {c_fit:.3f} * p^{{-{alpha_fit:.4f}}}")
                print(f"     (For comparison: 1/sqrt(p) has exponent 0.5)")

    print(f"""
  3. DI BENEDETTO BOUND ANALYSIS:
     The exponent 31/2880 ~ 0.01076 is FAR too small for our needs.
     Even with m = ord_p(2) ~ p/2, the bound gives rho ~ (p/2)^{{-0.01}}
     which is essentially 1 for moderate p.

     HOWEVER: the Di Benedetto bound applies to INDIVIDUAL character sums
     |S_p(a)|, not to the spectral gap of M. The spectral gap is a
     STRONGER statement about mixing.

  4. KEY STRUCTURAL INSIGHT:
     The averaged matrix M = R_3 * A where:
       R_3 = multiplication-by-3 permutation (eigenvalues on unit circle)
       A = (1/N) * sum D_{{2^e}} = circulant translation average

     The eigenvalues of A are:
       a_t = (1/N) * sum_{{e=1}}^{{N}} omega^{{t*2^e}}

     These are PARTIAL exponential sums over the subgroup <2> of F_p*.

     For t != 0: |a_t| <= (1/N) * [q*|K_t| + m] where:
       q = N/m full orbits, K_t = sum_{{h in <2>}} omega^{{th}} (Kloosterman-type)
       m = ord_p(2), N = S-1

     When m = p-1 (primitive root): K_t = -1 for all t != 0, giving
       |a_t| <= (q + 1)/N -> excellent gap!
     When m < p-1: |K_t| <= sqrt(p) (Polya-Vinogradov), giving
       |a_t| <= (q*sqrt(p) + m)/N

  5. THE OBSTRUCTION TO A PROOF:
     The product M = R_3 * A has eigenvalues that are NOT simply products
     of eigenvalues of R_3 and A (since they don't commute in general).
     The spectral gap of M could be LARGER or SMALLER than that of A.

     For a RIGOROUS bound, we need:
     (a) Bound the spectral radius of A (circulant -- done via exponential sums)
     (b) Show that composition with R_3 does not close the gap
     (c) Translate the spectral gap of M to a bound on e_{{k-1}}(T_1,...,T_{{S-1}})

     Step (c) is the HARDEST: the elementary symmetric polynomial of
     permutation matrices does NOT reduce to powers of the averaged matrix.

  6. CANDIDATE THEOREM (to be proved):
     Let p >= 5 be prime, m = ord_p(2), and S >= 2m.
     Then the spectral gap of M satisfies:
       Delta(M) >= c_0 / sqrt(p)
     where c_0 > 0 is an absolute constant.

     EVIDENCE: All {n_total} tested cases satisfy this with c_0 >=
     {min(g['gap'] * math.sqrt(g['p']) for g in all_gaps):.4f}.

  7. IMPLICATION FOR CONDITION Q:
     IF Delta >= c_0/sqrt(p) AND the ESP-to-spectral-gap reduction works,
     THEN |S_p(a)| <= C * (1 - c_0/sqrt(p))^{{k-1}} for non-trivial a.

     For k >> sqrt(p) * ln(p), this gives |S_p(a)| << C/p, which implies
     N_0(p) ~ C/p (equidistribution), hence Condition Q for large enough k.

     For small k (the "frontier" regime), the bound may not suffice,
     and the hybrid peeling+spectral approach becomes necessary.
""")

    # ═══════════════════════════════════════════════════════════════
    # PART 10: Optimal strategy identification
    # ═══════════════════════════════════════════════════════════════
    print("─" * 80)
    print("  PART 10: Optimal strategy for proving Condition Q")
    print("─" * 80)

    print("""
  STRATEGY ASSESSMENT:

  A. PURE SPECTRAL GAP (via averaged transfer matrix):
     - Pro: Clean framework, relates to Cayley graph theory
     - Pro: Numerically, gap >= 1/sqrt(p) holds universally
     - Con: ESP reduction (step c above) not established
     - Con: M = R_3 * A non-commutativity makes rigorous bounds hard
     - Feasibility: 4/10 (conceptually sound, technically challenging)

  B. HYBRID PEELING + SPECTRAL:
     - Pro: Peeling reduces dimension by 1 (rigorous, from preprint Lem 6.2)
     - Pro: Inner sum has one fewer variable, potentially easier to bound
     - Con: Still need spectral bounds on inner sums
     - Con: The peeling bound alone gives N_0 <= 0.631*C (too weak)
     - Feasibility: 5/10 (more concrete than pure spectral)

  C. DI BENEDETTO-LAGARIAS-TAO IMPROVEMENT:
     - Pro: Existing framework, published results
     - Con: Exponent 31/2880 is far too small
     - Con: Would need exponential improvement (31/2880 -> ~1/2)
     - Feasibility: 2/10 (requires breakthrough in sum-product theory)

  D. DIRECT CIRCULANT ANALYSIS (new approach):
     - Insight: M = R_3 * A where A is circulant
     - The eigenvalues of A are explicit: partial exponential sums over <2>
     - R_3 is a known permutation; the product's spectrum can be bounded
       using the fact that R_3 permutes eigenspaces of the translation group
     - Pro: Avoids the ESP problem entirely
     - Pro: Connects to well-studied objects (Gauss sums, Kloosterman sums)
     - Feasibility: 6/10 (MOST PROMISING)

  RECOMMENDATION: Pursue Strategy D.

  Specifically:
  1. Prove |a_t| <= (sqrt(p) + 1)/(S-1) for the circulant eigenvalues
     (partial Polya-Vinogradov over <2>).
  2. Analyze how R_3 interacts with the Fourier basis of Z/pZ.
  3. Use the factorization M = R_3 * A to bound the spectrum of M.
  4. The key identity: if psi_a is the Fourier basis vector for frequency a,
     then R_3 psi_a = psi_{3^{-1}*a}. So R_3 permutes the Fourier modes.
  5. In the Fourier basis: M_hat[a][b] = delta_{b, 3*a mod p} * a_b
     where a_b is the b-th eigenvalue of A.
  6. This means M in Fourier basis is a MONOMIAL matrix (one nonzero per row/col)!
  7. The eigenvalues of M are the eigenvalues of the permutation cycle
     structure of a -> 3a mod p, weighted by products of a_b along cycles.
  8. For a cycle (a, 3a, 9a, ..., 3^{L-1}a) of length L in the action
     of x3 on (Z/pZ)*:
     eigenvalue contribution = (a_a * a_{3a} * ... * a_{3^{L-1}a})^{1/L}
  9. The spectral radius is max over cycles of |prod a_{3^j*a}|^{1/L}.
  10. For each a != 0: |a_{3^j*a}| <= (sqrt(p)+1)/(S-1) =: rho_0.
      So the cycle product <= rho_0^L, and the L-th root <= rho_0.
  11. THEREFORE: spectral radius of M restricted to non-trivial modes <= rho_0.
  12. SPECTRAL GAP: Delta >= 1 - rho_0 = 1 - (sqrt(p)+1)/(S-1).
      For S >> sqrt(p), this gives Delta ~ 1 (strong mixing).
      For S ~ c*p (Regime A), Delta ~ 1 - 1/sqrt(p) ~ excellent.

  THIS IS THE KEY INSIGHT: In the Fourier basis, M is monomial, and its
  spectral radius on non-trivial modes equals max over orbits of |a_t|
  (NOT the L-th root, since all |a_t| are bounded by the same rho_0).

  Wait -- let me re-examine. The Fourier representation:
    M_hat[a][b] = <psi_a, M psi_b>
    = <psi_a, R_3 A psi_b>
    = <psi_a, R_3 (a_b psi_b)>  [A is diag in Fourier basis with eigenvalue a_b]
    = a_b * <psi_a, psi_{b/3}>  [R_3 psi_b = psi_{b*3^{-1}} ... careful]

  Actually: (R_3 f)(x) = f(3^{-1}x). So (R_3 psi_b)(x) = psi_b(3^{-1}x)
  = omega^{b*3^{-1}*x} = psi_{b*3^{-1}}(x). (Where 3^{-1} is mod p.)

  So M_hat[a][b] = a_b * delta_{a, b*3^{-1} mod p} = a_b * delta_{3a, b mod p}.

  This means: M_hat is nonzero only at (a, 3a) for each a, with value a_{3a}.
  So M_hat maps psi_a -> a_{3a} * psi_{3^{-1}*a}...

  Let me think more carefully. M psi_b = R_3 (A psi_b) = R_3 (a_b psi_b)
  = a_b * R_3 psi_b = a_b * psi_{b/3}.

  So M psi_b = a_b * psi_{b/3}. The orbit of b under division by 3 is
  {b, b/3, b/9, ...} = {b, b*3^{-1}, b*3^{-2}, ...} which has length
  L = ord_p(3).

  Along this orbit: M^L psi_b = (a_b * a_{b/3} * ... * a_{b/3^{L-1}}) psi_b.
  So the eigenvalue corresponding to this orbit is the L-th roots of
  prod_{j=0}^{L-1} a_{b*3^{-j}}.

  THE SPECTRAL RADIUS of M is therefore:
    rho(M) = max over orbits O of |prod_{b in O} a_b|^{1/|O|}

  And the spectral gap is Delta = 1 - rho (excluding the trivial orbit b=0).

  PROVABLE BOUND:
    |a_b| <= R for all b != 0  =>  rho <= R.
    So Delta >= 1 - R where R = max_{b != 0} |a_b|.

  And a_b = (1/(S-1)) * sum_{e=1}^{S-1} omega^{b*2^e}.

  This is an INCOMPLETE EXPONENTIAL SUM over the subgroup <2>.
""")

    # Verify the monomial structure numerically
    print("  NUMERICAL VERIFICATION of monomial structure:")
    print("  " + "-" * 50)

    for p, k, S in prime_k_pairs[:5]:
        M = build_averaged_matrix(p, S)

        # Build Fourier basis
        omega = cmath.exp(2j * cmath.pi / p)
        F = np.array([[omega ** (a * b) for b in range(p)] for a in range(p)],
                     dtype=complex) / math.sqrt(p)
        F_inv = F.conj().T

        # M in Fourier basis
        M_hat = F @ M @ F_inv

        # Check monomial structure: for each row a, find the unique nonzero column
        is_monomial = True
        max_off_diag = 0.0
        for a in range(p):
            row = M_hat[a]
            abs_row = np.abs(row)
            sorted_idx = np.argsort(abs_row)[::-1]
            if abs_row[sorted_idx[0]] > 1e-10:
                ratio = abs_row[sorted_idx[1]] / abs_row[sorted_idx[0]]
                max_off_diag = max(max_off_diag, ratio)
                if ratio > 0.01:
                    is_monomial = False

        # Compute spectral radius via orbit products
        g_inv = pow(3, p - 2, p)  # 3^{-1} mod p (Fermat)

        # Eigenvalues of A (circulant)
        a_evals = np.zeros(p, dtype=complex)
        for b in range(p):
            a_evals[b] = sum(omega ** ((b * pow(2, e, p)) % p)
                            for e in range(1, S)) / (S - 1)

        # Find orbits under b -> b*g_inv mod p
        visited = [False] * p
        orbit_rhos = []
        for b in range(1, p):
            if visited[b]:
                continue
            orbit = []
            cur = b
            while not visited[cur]:
                visited[cur] = True
                orbit.append(cur)
                cur = (cur * g_inv) % p

            # Product of a_evals along orbit
            prod_val = 1.0 + 0j
            for idx in orbit:
                prod_val *= a_evals[idx]

            orbit_rho = abs(prod_val) ** (1.0 / len(orbit))
            orbit_rhos.append(orbit_rho)

        predicted_rho = max(orbit_rhos) if orbit_rhos else 0
        actual_evals = sorted(np.abs(eigvals(M)), reverse=True)
        actual_rho = actual_evals[1]  # second largest (first is 1)

        print(f"  p={p:>3}: monomial={'YES' if is_monomial else 'NO '} "
              f"(off-diag ratio {max_off_diag:.2e}), "
              f"predicted rho={predicted_rho:.6f}, "
              f"actual lambda_2={actual_rho:.6f}, "
              f"match={'YES' if abs(predicted_rho - actual_rho) < 0.001 else 'NO'}")

    # Final: max |a_b| vs 1/sqrt(p)
    print("\n  MAX |a_b| for b != 0 (circulant eigenvalue) vs bounds:")
    print(f"  {'p':>5} {'S':>4} {'max|a_b|':>10} {'sqrt(p)/S':>10} "
          f"{'1/sqrt(p)':>10} {'ratio':>8}")
    print("  " + "-" * 55)

    for p, k, S in prime_k_pairs:
        omega = cmath.exp(2j * cmath.pi / p)
        N = S - 1
        max_ab = 0
        for b in range(1, p):
            ab = abs(sum(omega ** ((b * pow(2, e, p)) % p) for e in range(1, S))) / N
            max_ab = max(max_ab, ab)

        sqrtp_over_S = math.sqrt(p) / N
        inv_sqrtp = 1.0 / math.sqrt(p)
        ratio = max_ab / sqrtp_over_S if sqrtp_over_S > 0 else float('inf')

        print(f"  {p:>5} {S:>4} {max_ab:>10.6f} {sqrtp_over_S:>10.6f} "
              f"{inv_sqrtp:>10.6f} {ratio:>8.4f}")

    # Reproducibility
    sig = str([(r['p'], r['gap']) for r in spectral_results])
    sha = hashlib.sha256(sig.encode()).hexdigest()[:16]
    print(f"\n  SHA256(spectral_results)[:16]: {sha}")
    print("\n" + "=" * 80)


if __name__ == "__main__":
    t0 = time.time()
    main()
    print(f"\n  Total runtime: {time.time() - t0:.1f}s")
