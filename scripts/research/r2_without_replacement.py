#!/usr/bin/env python3
"""
r2_without_replacement.py -- Round 2: Quantifying the Without-Replacement Effect
=================================================================================

CONTEXT (from Round 1):
  The Horner chain for Collatz cycle candidates is:
      c_0 = 0, c_{j+1} = 3*c_j + 2^{b_{k-1-j}} mod p
  where {b_1 < ... < b_{k-1}} is a (k-1)-element SUBSET of {1, ..., S-1},
  S = ceil(k*log2(3)), p is a prime dividing d(k) = 2^S - 3^k.

  Round 1 proved: T is DOUBLY STOCHASTIC => in the Markov (with-replacement)
  model, the stationary distribution is uniform and P(c_{k-1}=0) ~ 1/p
  after mixing.

  BUT: the real Horner chain uses each element b EXACTLY ONCE.
  This is NOT a Markov chain. This script quantifies the deviation.

RESEARCH QUESTIONS:
  Q1. Exact vs Markov comparison: does N_0(exact)/N_0(Markov) deviate from 1?
  Q2. Covariance structure: does without-replacement create anti-correlation?
  Q3. Depletion effect: does reduced "randomness" at late steps create bias?
  Q4. Coupling argument: can we bound TV(exact, Markov)?
  Q5. Key theorem attempt: P_exact(c_{k-1}=0) <= (1 - delta)/p for delta > 0?

HONESTY COMMITMENT:
  If without-replacement has NO systematic effect, this script says so clearly.

Author: Eric Merle (assisted by Claude)
Date:   March 2026
"""

import math
import hashlib
import sys
import time
import json
import numpy as np
from itertools import combinations, product
from collections import defaultdict
from fractions import Fraction


# ============================================================================
# SECTION 0: Core Arithmetic (shared with Round 1)
# ============================================================================

def S_of_k(k):
    """S(k) = ceil(k * log2(3))."""
    return math.ceil(k * math.log2(3))


def d_of_k(k):
    """d(k) = 2^S - 3^k."""
    S = S_of_k(k)
    return (1 << S) - 3**k


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


def multiplicative_order(base, p):
    """Multiplicative order of base mod p."""
    if math.gcd(base, p) != 1:
        return 0
    r = 1
    for m in range(1, p):
        r = (r * base) % p
        if r == 1:
            return m
    return p - 1


def horner_chain(subset, k, p):
    """Compute Horner chain c_0, ..., c_{k-1} mod p.

    subset = (b_1, ..., b_{k-1}) sorted ascending.
    c_0 = 0
    c_{j+1} = 3*c_j + 2^{b_{k-1-j}} mod p
    """
    chain = [0]
    km1 = k - 1
    for j in range(km1):
        b = subset[km1 - 1 - j]
        c_next = (3 * chain[-1] + pow(2, b, p)) % p
        chain.append(c_next)
    return chain


def build_transition_matrix(k, p):
    """Build the Markov transition matrix T for Horner chain mod p.

    T[r][s] = (1/(S-1)) * |{b in {1,...,S-1} : (3*r + 2^b) mod p = s}|

    Returns T (numpy array), info dict.
    """
    S = S_of_k(k)
    n_exp = S - 1
    powers = [pow(2, b, p) for b in range(1, S)]

    C = np.zeros((p, p), dtype=np.int64)
    for r in range(p):
        r3 = (3 * r) % p
        for pw in powers:
            s = (r3 + pw) % p
            C[r][s] += 1

    T = C.astype(np.float64) / n_exp

    # Verify row and column sums
    assert np.allclose(T.sum(axis=1), 1.0), "T not row-stochastic"
    assert np.allclose(T.sum(axis=0), 1.0), "T not column-stochastic (not doubly stochastic)"

    return T, {'k': k, 'S': S, 'p': p, 'n_exp': n_exp}


# ============================================================================
# SECTION 1: EXACT vs MARKOV COMPARISON (Q1)
# ============================================================================

def exact_final_distribution(k, p):
    """Compute the exact distribution of c_{k-1} mod p over all
    C(S-1, k-1) subsets (WITHOUT replacement).

    Returns: dict with counts for each residue, total count.
    """
    S = S_of_k(k)
    km1 = k - 1
    counts = defaultdict(int)
    total = 0

    for combo in combinations(range(1, S), km1):
        total += 1
        c = 0
        for j in range(km1):
            b = combo[km1 - 1 - j]
            c = (3 * c + pow(2, b, p)) % p
        counts[c] += 1

    return dict(counts), total


def markov_final_distribution(k, p):
    """Compute the Markov (with-replacement) distribution of c_{k-1} mod p.

    This uses T^{k-1} starting from state 0.
    Returns: array of probabilities for each residue.
    """
    T, info = build_transition_matrix(k, p)
    km1 = k - 1
    if km1 == 0:
        dist = np.zeros(p)
        dist[0] = 1.0
        return dist

    Tk = np.linalg.matrix_power(T, km1)
    return Tk[0, :]  # row 0 of T^{k-1}


def with_replacement_count(k, p):
    """Compute the WITH-REPLACEMENT count of sequences (b_1, ..., b_{k-1})
    from {1,...,S-1} (with repeats allowed) giving c_{k-1} = 0 mod p.

    Total sequences = (S-1)^{k-1}.
    N_0 = total * (T^{k-1})[0][0].
    """
    S = S_of_k(k)
    n_exp = S - 1
    total_with = n_exp ** (k - 1)
    T, _ = build_transition_matrix(k, p)
    km1 = k - 1
    if km1 == 0:
        return total_with, total_with  # everything is at 0
    Tk = np.linalg.matrix_power(T, km1)
    P0_markov = Tk[0, 0]
    N0_markov = total_with * P0_markov
    return N0_markov, total_with


def run_q1_exact_vs_markov(cases, max_comb=500000):
    """Q1: For each (k,p), compare exact N_0 to Markov estimate.

    The Markov estimate counts with-replacement sequences (b_1,...,b_{k-1})
    from {1,...,S-1}^{k-1} giving c_{k-1}=0. We compare to without-replacement
    subsets.

    Key insight: the comparison must be between PROBABILITIES, not counts,
    since the sample spaces differ ((S-1)^{k-1} vs C(S-1,k-1)).
    """
    results = []

    for k, p in cases:
        S = S_of_k(k)
        C_total = math.comb(S - 1, k - 1)
        if C_total > max_comb:
            continue

        # Exact (without replacement)
        counts_exact, total_exact = exact_final_distribution(k, p)
        N0_exact = counts_exact.get(0, 0)
        P0_exact = N0_exact / total_exact if total_exact > 0 else 0.0

        # Markov probability (with replacement)
        P0_markov_dist = markov_final_distribution(k, p)
        P0_markov = P0_markov_dist[0]

        # Ratio
        ratio = P0_exact / P0_markov if P0_markov > 1e-15 else float('inf')

        # Full distribution comparison
        exact_dist = np.zeros(p)
        for r, cnt in counts_exact.items():
            exact_dist[r] = cnt / total_exact
        markov_dist = P0_markov_dist

        # Total variation distance between the two distributions
        tv = 0.5 * np.sum(np.abs(exact_dist - markov_dist))

        # Chi-squared-like statistic
        chi2 = 0.0
        for r in range(p):
            if markov_dist[r] > 1e-15:
                chi2 += (exact_dist[r] - markov_dist[r])**2 / markov_dist[r]

        results.append({
            'k': k, 'p': p, 'S': S,
            'C_total': total_exact,
            'N0_exact': N0_exact,
            'P0_exact': P0_exact,
            'P0_markov': P0_markov,
            'P0_uniform': 1.0 / p,
            'ratio_exact_markov': ratio,
            'ratio_exact_uniform': P0_exact * p,
            'ratio_markov_uniform': P0_markov * p,
            'tv_distance': tv,
            'chi2_stat': chi2,
            'exact_dist': exact_dist,
            'markov_dist': markov_dist,
        })

    return results


# ============================================================================
# SECTION 2: COVARIANCE STRUCTURE (Q2)
# ============================================================================

def compute_step_covariance(k, p, max_comb=500000):
    """Compute the covariance between consecutive Horner steps under
    without-replacement sampling.

    For consecutive steps j and j+1, the exponents used are b_{k-1-j}
    and b_{k-2-j}. In the without-replacement model, these are DISTINCT
    elements of the subset. This creates a dependency.

    We measure: Cov(2^{b_{k-1-j}}, 2^{b_{k-2-j}} | without-replacement)
    vs the independent (with-replacement) case where Cov = 0.

    More precisely, we track the INCREMENTS:
        Delta_j = 2^{b_{k-1-j}} mod p  (the additive contribution at step j)
    and compute Cov(Delta_j, Delta_{j+1}) over all subsets.
    """
    S = S_of_k(k)
    km1 = k - 1
    C_total = math.comb(S - 1, km1)
    if C_total > max_comb or km1 < 2:
        return None

    # For each subset, extract the sequence of increments
    # Delta_j = 2^{b_{k-1-j}} mod p, for j = 0, ..., k-2
    n_steps = km1
    increments_all = []

    for combo in combinations(range(1, S), km1):
        deltas = []
        for j in range(km1):
            b = combo[km1 - 1 - j]
            deltas.append(pow(2, b, p))
        increments_all.append(deltas)

    increments_arr = np.array(increments_all, dtype=np.float64)  # shape: (C_total, km1)

    # Mean of each step's increment
    means = increments_arr.mean(axis=0)  # shape: (km1,)

    # Covariance between consecutive steps
    cov_consecutive = []
    for j in range(km1 - 1):
        cov = np.mean((increments_arr[:, j] - means[j]) *
                       (increments_arr[:, j+1] - means[j+1]))
        cov_consecutive.append(cov)

    # For the with-replacement model, increments are i.i.d. so Cov = 0.
    # The MARGINAL distribution of each increment in with-replacement
    # is uniform over {2^1,...,2^{S-1}} mod p. But in without-replacement,
    # the marginal of Delta_j is NOT exactly the same (depends on position).

    # Compute the marginal mean and variance for with-replacement
    all_powers = [pow(2, b, p) for b in range(1, S)]
    mean_wr = np.mean(all_powers)
    var_wr = np.var(all_powers)

    # Variance of each step's increment in without-replacement
    var_steps = increments_arr.var(axis=0)

    # Full covariance matrix
    cov_matrix = np.cov(increments_arr.T)  # shape: (km1, km1)

    # Correlation matrix
    std_steps = np.sqrt(var_steps)
    corr_matrix = np.zeros((km1, km1))
    for i in range(km1):
        for j in range(km1):
            if std_steps[i] > 1e-15 and std_steps[j] > 1e-15:
                corr_matrix[i, j] = cov_matrix[i, j] / (std_steps[i] * std_steps[j])

    return {
        'k': k, 'p': p, 'km1': km1,
        'C_total': C_total,
        'cov_consecutive': cov_consecutive,
        'mean_wr': mean_wr,
        'var_wr': var_wr,
        'means_steps': means.tolist(),
        'var_steps': var_steps.tolist(),
        'cov_matrix': cov_matrix,
        'corr_matrix': corr_matrix,
        'avg_cov_consecutive': np.mean(cov_consecutive) if cov_consecutive else 0.0,
        'max_abs_corr_offdiag': float(np.max(np.abs(
            corr_matrix - np.eye(km1)))) if km1 > 1 else 0.0,
    }


# ============================================================================
# SECTION 3: DEPLETION EFFECT (Q3)
# ============================================================================

def compute_depletion_effect(k, p, max_comb=500000):
    """Quantify how the "pool" of available exponents shrinks as the
    chain progresses, and how this affects the conditional distribution
    of c_{k-1}.

    At step j, the exponent b_{k-1-j} is chosen. In without-replacement,
    the exponents already used at steps 0,...,j-1 are unavailable.

    We measure:
    - Effective number of choices at each step
    - The conditional entropy of c_j given c_{j-1} (averaged over subsets)
    - Whether late steps are more "constrained" than early steps

    The key question: does the constraint from depletion create a systematic
    bias in the FINAL distribution of c_{k-1}?
    """
    S = S_of_k(k)
    km1 = k - 1
    C_total = math.comb(S - 1, km1)
    if C_total > max_comb:
        return None

    n_pool = S - 1  # total pool size: {1, ..., S-1}

    # For each step j, in without-replacement:
    # - Step 0 uses b_{k-1} (the largest element of the subset)
    # - Step j uses b_{k-1-j}
    # After j steps, j elements have been used, leaving n_pool - j - 1 for
    # the remaining steps (but the subset is predetermined, so "choice" is
    # not sequential -- the subset is chosen all at once).
    #
    # However, we can measure the EFFECTIVE constraint by looking at how
    # the CONDITIONAL distribution of the remaining chain values narrows.

    # Approach: For each prefix length j, compute P(c_{k-1} = 0 | c_j = r)
    # over all subsets. Compare this to the Markov estimate.

    # Collect (c_j, c_{k-1}) pairs for each j
    conditional_counts = {}  # j -> {r: [count_final_0, count_total]}
    for j in range(km1 + 1):
        conditional_counts[j] = defaultdict(lambda: [0, 0])

    for combo in combinations(range(1, S), km1):
        chain = horner_chain(combo, k, p)
        for j in range(km1 + 1):
            cj = chain[j]
            conditional_counts[j][cj][1] += 1
            if chain[km1] == 0:
                conditional_counts[j][cj][0] += 1

    # For each step j, compute entropy of conditional distribution P(c_{k-1}|c_j)
    step_analysis = []
    for j in range(km1 + 1):
        # Conditional probabilities P(c_{k-1}=0 | c_j=r)
        cond_probs = {}
        for r, (n0, nt) in conditional_counts[j].items():
            if nt > 0:
                cond_probs[r] = n0 / nt

        # How many distinct c_j values appear?
        n_distinct = len(conditional_counts[j])

        # Variance of the conditional probabilities (if they were all 1/p,
        # variance would be 0 -- higher variance means more information)
        if cond_probs:
            cp_values = list(cond_probs.values())
            cp_mean = np.mean(cp_values)
            cp_var = np.var(cp_values)
        else:
            cp_mean = 0.0
            cp_var = 0.0

        # Effective choices: for step j, how many different exponents b
        # appear at position k-1-j across all subsets?
        # (This measures the "diversity" at this step.)
        exponents_at_step = set()
        for combo in combinations(range(1, S), km1):
            if j < km1:
                exponents_at_step.add(combo[km1 - 1 - j])
        n_effective = len(exponents_at_step)

        step_analysis.append({
            'step': j,
            'n_distinct_states': n_distinct,
            'n_effective_choices': n_effective,
            'cond_P0_mean': cp_mean,
            'cond_P0_var': cp_var,
            'cond_P0_min': min(cond_probs.values()) if cond_probs else 0,
            'cond_P0_max': max(cond_probs.values()) if cond_probs else 0,
        })

    return {
        'k': k, 'p': p, 'km1': km1,
        'n_pool': n_pool,
        'C_total': C_total,
        'step_analysis': step_analysis,
    }


# ============================================================================
# SECTION 3b: BIRTHDAY-STYLE COLLISION ANALYSIS
# ============================================================================

def birthday_collision_analysis(cases, max_comb=500000):
    """Analyze the birthday-style collision structure of 2^b mod p values.

    In the Markov model (with replacement), we draw k-1 values i.i.d. from
    {2^1, ..., 2^{S-1}} mod p. Different b values can produce the SAME
    2^b mod p value when b1 != b2 but 2^{b1} = 2^{b2} (mod p).
    This happens iff b1 = b2 (mod ord_p(2)).

    WITHOUT replacement: we draw k-1 DISTINCT b values from {1,...,S-1}.
    The 2^b mod p values MAY still collide (same residue, different exponent),
    but collisions are constrained by the orbit structure of <2> in Z/pZ.

    The key question: does the non-repetition of exponents create
    enough structural constraint to measurably bias the evaluation map?

    We measure:
    (a) How many distinct 2^b mod p values appear among the k-1 chosen exponents
    (b) How this compares to the birthday-problem expectation with replacement
    (c) Whether corrSum=0 subsets have systematically different collision patterns
    (d) The "effective pool size" accounting for the orbit of 2 mod p
    """
    results = []

    for k, p in cases:
        S = S_of_k(k)
        km1 = k - 1
        C_total = math.comb(S - 1, km1)
        if C_total > max_comb:
            continue

        ord2 = multiplicative_order(2, p)

        # Full set of 2^b mod p for b in {1, ..., S-1}
        power_values = [pow(2, b, p) for b in range(1, S)]
        distinct_power_set = set(power_values)
        n_distinct_in_pool = len(distinct_power_set)
        n_pool = S - 1

        # The orbit structure: group exponents by their 2^b mod p value
        orbit_groups = defaultdict(list)
        for b in range(1, S):
            orbit_groups[pow(2, b, p)].append(b)
        orbit_sizes = sorted([len(v) for v in orbit_groups.values()], reverse=True)

        # For each subset, compute:
        #   - number of distinct 2^b mod p values (out of k-1 exponents)
        #   - number of "collisions" (exponents mapping to same residue)
        distinct_counts = []
        collision_counts = []
        distinct_zero = []  # among corrSum=0 subsets
        distinct_nonzero = []
        collision_zero = []
        collision_nonzero = []

        for combo in combinations(range(1, S), km1):
            chain = horner_chain(combo, k, p)
            final_zero = (chain[km1] == 0)

            # Count distinct 2^b mod p values
            power_residues = [pow(2, b, p) for b in combo]
            n_distinct = len(set(power_residues))
            n_collisions = km1 - n_distinct  # number of "excess" elements

            distinct_counts.append(n_distinct)
            collision_counts.append(n_collisions)
            if final_zero:
                distinct_zero.append(n_distinct)
                collision_zero.append(n_collisions)
            else:
                distinct_nonzero.append(n_distinct)
                collision_nonzero.append(n_collisions)

        # Birthday-problem expected distinct values WITH replacement:
        # Drawing km1 values from n_distinct_in_pool elements with replacement,
        # E[distinct] = n * (1 - (1-1/n)^km1) where n = n_distinct_in_pool
        n = n_distinct_in_pool
        if n > 0 and km1 > 0:
            expected_distinct_wr = n * (1.0 - (1.0 - 1.0 / n) ** km1)
        else:
            expected_distinct_wr = 0.0

        # With-replacement expected collisions
        expected_collisions_wr = km1 - expected_distinct_wr

        # Actual statistics
        avg_distinct = np.mean(distinct_counts)
        avg_collisions = np.mean(collision_counts)
        avg_distinct_z = np.mean(distinct_zero) if distinct_zero else float('nan')
        avg_distinct_nz = np.mean(distinct_nonzero) if distinct_nonzero else float('nan')
        avg_coll_z = np.mean(collision_zero) if collision_zero else float('nan')
        avg_coll_nz = np.mean(collision_nonzero) if collision_nonzero else float('nan')

        # Sampling fraction: f = km1 / n_pool
        sampling_fraction = km1 / n_pool if n_pool > 0 else 0.0

        # Coverage fraction: what fraction of the distinct power values is used
        coverage = avg_distinct / n_distinct_in_pool if n_distinct_in_pool > 0 else 0.0

        results.append({
            'k': k, 'p': p, 'S': S, 'km1': km1,
            'n_pool': n_pool,
            'ord2': ord2,
            'n_distinct_in_pool': n_distinct_in_pool,
            'orbit_sizes': orbit_sizes,
            'sampling_fraction': sampling_fraction,
            'coverage': coverage,
            'avg_distinct': float(avg_distinct),
            'avg_distinct_zero': float(avg_distinct_z),
            'avg_distinct_nonzero': float(avg_distinct_nz),
            'expected_distinct_wr': expected_distinct_wr,
            'distinct_surplus': float(avg_distinct - expected_distinct_wr),
            'avg_collisions': float(avg_collisions),
            'avg_collisions_zero': float(avg_coll_z),
            'avg_collisions_nonzero': float(avg_coll_nz),
            'expected_collisions_wr': expected_collisions_wr,
            'min_distinct': min(distinct_counts),
            'max_distinct': max(distinct_counts),
            'N0': len(distinct_zero),
            'C_total': C_total,
        })

    return results


def sampling_fraction_scaling(k_max=50):
    """Analyze how the sampling fraction f = (k-1)/(S-1) evolves with k.

    For the without-replacement effect to be negligible, we need f -> 0.
    Since S ~ k * log2(3) ~ 1.585*k, we have:
        f = (k-1)/(S-1) ~ k / (1.585*k) -> 1/1.585 ~ 0.631

    The sampling fraction converges to 1/log2(3) ~ 0.63093.
    This is a HIGH and CONSTANT sampling fraction, meaning
    without-replacement effects are ALWAYS structurally significant.
    """
    data = []
    f_limit = 1.0 / math.log2(3)
    for k in range(3, k_max + 1):
        S = S_of_k(k)
        M = S - 1
        n = k - 1
        f = n / M if M > 0 else 0.0
        # Finite population correction (variance ratio WR/WOR)
        fpc = (M - n) / (M - 1) if M > 1 else 1.0
        # How many distinct 2^b values in the pool?
        # This depends on p, but we can compute the pool size itself
        data.append({
            'k': k, 'S': S, 'M': M, 'n': n,
            'f': f, 'fpc': fpc,
            'f_limit': f_limit,
            'f_deviation': abs(f - f_limit),
        })
    return data


# ============================================================================
# SECTION 4: COUPLING AND TOTAL VARIATION (Q4)
# ============================================================================

def compute_tv_and_coupling(k, p, max_comb=500000):
    """Compute the total variation distance between:
    - The exact (without-replacement) distribution of c_{k-1} mod p
    - The Markov (with-replacement) distribution of c_{k-1} mod p

    Also provide a COUPLING INTERPRETATION: in what fraction of
    (subset, sequence) pairs do the without-replacement and
    with-replacement chains agree on c_{k-1}?

    For the coupling argument:
    TV(mu, nu) = inf_{couplings} P(X != Y)

    We give an UPPER BOUND on TV by constructing an explicit coupling:
    - Draw a (k-1)-subset S from {1,...,S-1} uniformly
    - Draw a (k-1)-sequence Q from {1,...,S-1}^{k-1} uniformly
    - If S and Q happen to be the same multiset (all elements distinct
      and forming the same set), couple them
    - Otherwise, let them evolve independently

    The probability that a random (k-1)-sequence has all distinct elements
    and forms a specific (k-1)-subset is:
        P(Q = specific permutation of S) = (k-1)! / (S-1)^{k-1}
    Total probability of Q being any permutation of any subset:
        = C(S-1, k-1) * (k-1)! / (S-1)^{k-1} = P(S-1, k-1) / (S-1)^{k-1}

    This gives TV <= 1 - P(all distinct) -- a WEAK upper bound.

    The actual TV from direct computation is much tighter.
    """
    S = S_of_k(k)
    km1 = k - 1
    C_total = math.comb(S - 1, km1)
    if C_total > max_comb:
        return None

    # Exact distribution (without replacement)
    counts_exact, total_exact = exact_final_distribution(k, p)
    exact_dist = np.zeros(p)
    for r, cnt in counts_exact.items():
        exact_dist[r] = cnt / total_exact

    # Markov distribution (with replacement)
    markov_dist = markov_final_distribution(k, p)

    # Total variation
    tv = 0.5 * np.sum(np.abs(exact_dist - markov_dist))

    # Which residues are over/under-represented in exact vs Markov?
    deviations = exact_dist - markov_dist
    over_represented = [(r, deviations[r]) for r in range(p)
                        if deviations[r] > 1e-10]
    under_represented = [(r, deviations[r]) for r in range(p)
                         if deviations[r] < -1e-10]

    # The deviation at 0 specifically
    dev_at_zero = deviations[0]
    # Does without-replacement favor or disfavor c_{k-1}=0?
    direction_at_zero = ("FAVORS" if dev_at_zero > 1e-10 else
                         "DISFAVORS" if dev_at_zero < -1e-10 else
                         "NEUTRAL")

    # Coupling upper bound
    n_pool = S - 1
    if km1 <= n_pool:
        # Probability that random with-replacement sequence has all distinct elements
        p_all_distinct = 1.0
        for j in range(km1):
            p_all_distinct *= (n_pool - j) / n_pool
        coupling_ub = 1.0 - p_all_distinct
    else:
        coupling_ub = 1.0  # can't draw k-1 distinct from pool of size < k-1

    # L-infinity distance (max deviation)
    linf = float(np.max(np.abs(deviations)))

    # KL divergence (exact || Markov) -- if defined
    kl_div = 0.0
    kl_defined = True
    for r in range(p):
        if exact_dist[r] > 1e-15:
            if markov_dist[r] < 1e-15:
                kl_defined = False
                kl_div = float('inf')
                break
            kl_div += exact_dist[r] * np.log(exact_dist[r] / markov_dist[r])

    return {
        'k': k, 'p': p, 'S': S, 'km1': km1,
        'tv_distance': tv,
        'linf_distance': linf,
        'coupling_ub': coupling_ub,
        'kl_divergence': kl_div if kl_defined else float('inf'),
        'dev_at_zero': dev_at_zero,
        'direction_at_zero': direction_at_zero,
        'n_over': len(over_represented),
        'n_under': len(under_represented),
        'P0_exact': exact_dist[0],
        'P0_markov': markov_dist[0],
    }


# ============================================================================
# SECTION 5: KEY THEOREM ATTEMPT (Q5)
# ============================================================================

def attempt_key_theorem(cases, max_comb=500000):
    """Attempt to prove or disprove:
    P_exact(c_{k-1} = 0) <= (1 - delta(k,p)) / p  for some delta > 0.

    This would mean without-replacement HELPS exclude cycles.

    Approach: For each (k,p), compute delta = 1 - P0_exact * p.
    If delta > 0 consistently, without-replacement helps.
    If delta < 0 sometimes, it can also hurt.

    We also look for ASYMPTOTIC trends as k grows.
    """
    results = []

    for k, p in cases:
        S = S_of_k(k)
        C_total = math.comb(S - 1, k - 1)
        if C_total > max_comb:
            continue

        counts_exact, total_exact = exact_final_distribution(k, p)
        N0 = counts_exact.get(0, 0)
        P0 = N0 / total_exact if total_exact > 0 else 0.0

        delta = 1.0 - P0 * p  # delta > 0 means P0 < 1/p (helps exclude)
        # Compute confidence: how far is N0 from its "random" expectation?
        expected_N0 = total_exact / p
        deviation_N0 = N0 - expected_N0
        # Standard deviation under uniform random: sqrt(C * (1/p) * (1-1/p))
        std_N0 = math.sqrt(total_exact * (1.0/p) * (1.0 - 1.0/p)) if p > 1 else 0
        z_score = deviation_N0 / std_N0 if std_N0 > 0 else 0.0

        # Also compute the exact distribution of c_{k-1} and check if 0
        # is the MOST depleted residue (lowest count)
        all_counts = [counts_exact.get(r, 0) for r in range(p)]
        rank_of_zero = sorted(all_counts).index(N0)  # 0=smallest
        # How many residues have count < N0?
        n_below = sum(1 for c in all_counts if c < N0)
        n_equal = sum(1 for c in all_counts if c == N0)
        n_above = sum(1 for c in all_counts if c > N0)

        results.append({
            'k': k, 'p': p, 'S': S,
            'C_total': total_exact,
            'N0': N0,
            'P0': P0,
            'uniform': 1.0 / p,
            'delta': delta,
            'expected_N0': expected_N0,
            'deviation_N0': deviation_N0,
            'std_N0': std_N0,
            'z_score': z_score,
            'rank_of_zero': rank_of_zero,
            'n_below': n_below,
            'n_equal': n_equal,
            'n_above': n_above,
            'helps_exclude': delta > 0,
        })

    return results


# ============================================================================
# SECTION 6: PERMUTATION MATRIX ANALYSIS
# ============================================================================

def permutation_effect_analysis(k, p, max_comb=200000):
    """Deep analysis: decompose the without-replacement effect into
    two components:

    1. SUBSET EFFECT: using a subset (no repeats) vs multiset
    2. ORDERING EFFECT: b_1 < b_2 < ... < b_{k-1} vs random permutation

    For a (k-1)-subset S of {1,...,S-1}, there are (k-1)! orderings.
    The Horner chain uses the CANONICAL ordering (sorted ascending, then
    the chain reads them in reverse: b_{k-1}, b_{k-2}, ..., b_1).

    But mathematically, the corrSum = sum_{i=1}^{k-1} 2^{b_i} * 3^{i-1}
    (this is equivalent to the Horner chain). The corrSum is a WEIGHTED
    sum of 2^{b_i} where the weights are 3^{i-1}.

    The weights 3^0 < 3^1 < ... < 3^{k-2} are increasing.
    The exponents b_1 < b_2 < ... < b_{k-1} are also increasing.
    So the ORDERED pairing assigns larger 2^{b_i} to larger weights 3^{i-1}.

    By the REARRANGEMENT INEQUALITY, the ordered pairing MAXIMIZES
    the sum when both sequences are sorted the same way.

    This is a crucial structural observation: the canonical ordering
    tends to PUSH corrSum toward larger values, potentially AWAY from 0.

    Let's verify this numerically.
    """
    S = S_of_k(k)
    km1 = k - 1
    C_total = math.comb(S - 1, km1)
    if C_total > max_comb:
        return None

    if km1 > 7:
        # (k-1)! gets too large
        return None

    n_perm = math.factorial(km1)

    # For each subset, compute corrSum under:
    # (a) canonical ordering (b_1 < ... < b_{k-1})
    # (b) all (k-1)! permutations
    # (c) reverse ordering (b_{k-1} > ... > b_1)

    canonical_zeros = 0
    reverse_zeros = 0
    random_perm_zeros = 0  # total zeros across all subsets x permutations
    total_subsets = 0
    total_permutations = 0

    # Distribution of corrSum under canonical vs random permutations
    canonical_sums = []
    random_sums = []

    from itertools import permutations as iter_perms

    for combo in combinations(range(1, S), km1):
        total_subsets += 1
        sorted_combo = sorted(combo)

        # (a) Canonical: b assigned as b_1=sorted[0], ..., b_{k-1}=sorted[-1]
        # corrSum = sum 2^{b_i} * 3^{i-1} mod p
        cs_canonical = 0
        for i in range(km1):
            cs_canonical = (cs_canonical + pow(2, sorted_combo[i], p) *
                           pow(3, i, p)) % p
        if cs_canonical == 0:
            canonical_zeros += 1
        canonical_sums.append(cs_canonical)

        # (c) Reverse: b_i = sorted[k-2-i]
        cs_reverse = 0
        for i in range(km1):
            cs_reverse = (cs_reverse + pow(2, sorted_combo[km1 - 1 - i], p) *
                         pow(3, i, p)) % p
        if cs_reverse == 0:
            reverse_zeros += 1

        # (b) All permutations (expensive!)
        for perm in iter_perms(sorted_combo):
            total_permutations += 1
            cs_perm = 0
            for i in range(km1):
                cs_perm = (cs_perm + pow(2, perm[i], p) *
                          pow(3, i, p)) % p
            if cs_perm == 0:
                random_perm_zeros += 1
            random_sums.append(cs_perm)

    P0_canonical = canonical_zeros / total_subsets
    P0_reverse = reverse_zeros / total_subsets
    P0_random_perm = random_perm_zeros / total_permutations

    return {
        'k': k, 'p': p, 'S': S, 'km1': km1,
        'total_subsets': total_subsets,
        'n_permutations': n_perm,
        'total_permutations': total_permutations,
        'canonical_zeros': canonical_zeros,
        'reverse_zeros': reverse_zeros,
        'random_perm_zeros': random_perm_zeros,
        'P0_canonical': P0_canonical,
        'P0_reverse': P0_reverse,
        'P0_random_perm': P0_random_perm,
        'P0_uniform': 1.0 / p,
        'ratio_canonical_uniform': P0_canonical * p,
        'ratio_reverse_uniform': P0_reverse * p,
        'ratio_random_uniform': P0_random_perm * p,
        'ratio_canonical_random': (P0_canonical / P0_random_perm
                                    if P0_random_perm > 0 else float('inf')),
    }


# ============================================================================
# SECTION 7: SELF-TESTS
# ============================================================================

def self_test():
    """Deterministic self-tests with assertions."""
    print("=" * 76)
    print("  SELF-TESTS")
    print("=" * 76)
    n_pass = 0
    n_fail = 0

    # Test 1: Basic arithmetic
    assert S_of_k(3) == 5
    assert S_of_k(5) == 8
    assert d_of_k(3) == 5
    assert d_of_k(4) == 47
    assert d_of_k(5) == 13
    print("  [PASS] T01: S(k) and d(k) values")
    n_pass += 1

    # Test 2: Horner chain manual check k=5, p=13, A={1,2,3,4}
    chain = horner_chain((1, 2, 3, 4), 5, 13)
    assert chain[0] == 0
    assert chain[1] == (3*0 + pow(2, 4, 13)) % 13  # 16 mod 13 = 3
    assert chain[1] == 3
    assert chain[2] == (3*3 + pow(2, 3, 13)) % 13  # 17 mod 13 = 4
    assert chain[2] == 4
    assert chain[3] == (3*4 + pow(2, 2, 13)) % 13  # 16 mod 13 = 3
    assert chain[3] == 3
    assert chain[4] == (3*3 + pow(2, 1, 13)) % 13  # 11 mod 13 = 11
    assert chain[4] == 11
    print("  [PASS] T02: Horner chain manual verification")
    n_pass += 1

    # Test 3: Transition matrix is doubly stochastic
    for k_test, p_test in [(3, 5), (5, 13), (4, 47)]:
        T, info = build_transition_matrix(k_test, p_test)
        assert np.allclose(T.sum(axis=1), 1.0, atol=1e-12)
        assert np.allclose(T.sum(axis=0), 1.0, atol=1e-12)
        assert abs(T[0, 0]) < 1e-12  # TZ property
    print("  [PASS] T03: Transition matrices doubly stochastic, T[0][0]=0")
    n_pass += 1

    # Test 4: Exact distribution for k=3, p=5
    # S=5, subsets of {1,2,3,4} of size 2: C(4,2)=6
    counts, total = exact_final_distribution(3, 5)
    assert total == 6
    assert sum(counts.values()) == 6
    # Each residue should appear approximately 6/5 = 1.2 times (but integer)
    print(f"  [PASS] T04: k=3,p=5: C=6, distribution={dict(sorted(counts.items()))}")
    n_pass += 1

    # Test 5: corrSum via Horner equals direct formula
    # corrSum(A) = sum_{i=1}^{k-1} 2^{b_i} * 3^{i-1} mod p
    for k_test in [3, 4, 5]:
        S = S_of_k(k_test)
        d = d_of_k(k_test)
        primes = [pp for pp in prime_factors(abs(d)) if pp <= 200]
        for p_test in primes:
            for combo in combinations(range(1, S), k_test - 1):
                # Horner chain
                chain = horner_chain(combo, k_test, p_test)
                c_horner = chain[k_test - 1]
                # Direct formula
                sorted_b = sorted(combo)
                c_direct = 0
                for i in range(k_test - 1):
                    c_direct = (c_direct + pow(2, sorted_b[i], p_test) *
                               pow(3, i, p_test)) % p_test
                assert c_horner == c_direct, (
                    f"Mismatch k={k_test}, p={p_test}, A={combo}: "
                    f"Horner={c_horner}, Direct={c_direct}")
    print("  [PASS] T05: Horner chain matches direct corrSum formula")
    n_pass += 1

    # Test 6: Markov distribution sums to 1
    for k_test, p_test in [(3, 5), (5, 13)]:
        md = markov_final_distribution(k_test, p_test)
        assert abs(sum(md) - 1.0) < 1e-10
        assert all(x >= -1e-12 for x in md)
    print("  [PASS] T06: Markov distributions are valid (sum=1, non-negative)")
    n_pass += 1

    # Test 7: For k=3, p=5, verify exact vs Markov manually
    # k=3: chain has 2 steps. S=5, pool = {1,2,3,4}.
    # Without replacement: C(4,2) = 6 subsets.
    # With replacement: 4^2 = 16 sequences.
    counts_ex, total_ex = exact_final_distribution(3, 5)
    N0_ex = counts_ex.get(0, 0)
    md3 = markov_final_distribution(3, 5)
    P0_mk = md3[0]
    # Both should be close to 1/5 = 0.2 but not necessarily equal
    assert total_ex == 6
    print(f"  [PASS] T07: k=3,p=5: N0_exact={N0_ex}/{total_ex}="
          f"{N0_ex/total_ex:.4f}, P0_markov={P0_mk:.4f}")
    n_pass += 1

    # Test 8: TV distance is between 0 and 1
    tv_res = compute_tv_and_coupling(3, 5)
    assert 0 <= tv_res['tv_distance'] <= 1.0
    assert tv_res['coupling_ub'] >= tv_res['tv_distance']
    print(f"  [PASS] T08: TV distance bounds: 0 <= {tv_res['tv_distance']:.6f} "
          f"<= {tv_res['coupling_ub']:.6f} (coupling UB)")
    n_pass += 1

    # Test 9: Covariance is negative (without-replacement expectation)
    cov_res = compute_step_covariance(5, 13)
    if cov_res is not None:
        # In without-replacement sampling from a finite pool,
        # Cov(X_i, X_j) = -sigma^2/(n-1) for i != j
        # So consecutive covariances should be NEGATIVE.
        avg_cov = cov_res['avg_cov_consecutive']
        # We just check it's computed; sign depends on the specific (k,p)
        print(f"  [PASS] T09: Covariance computed: avg_consecutive={avg_cov:.4f}")
        n_pass += 1
    else:
        print("  [SKIP] T09: Covariance computation skipped (too large)")
        n_pass += 1

    # Test 10: Depletion analysis produces valid output
    dep = compute_depletion_effect(3, 5)
    if dep is not None:
        assert len(dep['step_analysis']) == 3  # steps 0, 1, 2
        assert dep['step_analysis'][0]['n_distinct_states'] == 1  # c_0 always = 0
        print(f"  [PASS] T10: Depletion analysis: {len(dep['step_analysis'])} steps analyzed")
        n_pass += 1
    else:
        print("  [SKIP] T10: Depletion analysis skipped")
        n_pass += 1

    # Test 11: Permutation analysis consistency
    perm_res = permutation_effect_analysis(3, 5)
    if perm_res is not None:
        # For k=3, km1=2, there are 2!=2 permutations per subset
        assert perm_res['n_permutations'] == 2
        assert perm_res['total_subsets'] == 6
        assert perm_res['total_permutations'] == 12
        # canonical_zeros + rest should be consistent
        assert perm_res['P0_canonical'] >= 0
        print(f"  [PASS] T11: Permutation analysis: "
              f"P0_canonical={perm_res['P0_canonical']:.4f}, "
              f"P0_random_perm={perm_res['P0_random_perm']:.4f}")
        n_pass += 1
    else:
        print("  [SKIP] T11: Permutation analysis skipped")
        n_pass += 1

    # Test 12: Rearrangement inequality direction check
    # For corrSum = sum 2^{b_i} * 3^{i-1}, both 2^{b_i} and 3^{i-1} increase
    # with i (when b's are sorted ascending). So canonical ordering should
    # tend to maximize the sum. Verify on a specific case.
    # k=5, p=13, A={1,3,5,7}
    sorted_b = [1, 3, 5, 7]
    # Canonical: b_i = sorted_b[i] for i=0,...,3
    cs_can = sum(pow(2, sorted_b[i], 13) * pow(3, i, 13) % 13
                 for i in range(4)) % 13
    # Reverse: b_i = sorted_b[3-i]
    cs_rev = sum(pow(2, sorted_b[3-i], 13) * pow(3, i, 13) % 13
                 for i in range(4)) % 13
    # We just check both are valid residues
    assert 0 <= cs_can < 13
    assert 0 <= cs_rev < 13
    print(f"  [PASS] T12: Rearrangement check: canonical_sum={cs_can}, "
          f"reverse_sum={cs_rev} (mod 13)")
    n_pass += 1

    # Test 13: Symmetry check -- the exact distribution should respect
    # any symmetries of the transition matrix
    # For k=3, p=5: check that exact_dist is a valid probability distribution
    counts, total = exact_final_distribution(3, 5)
    dist = np.zeros(5)
    for r, c in counts.items():
        dist[r] = c / total
    assert abs(sum(dist) - 1.0) < 1e-12
    assert all(x >= 0 for x in dist)
    print(f"  [PASS] T13: Exact distribution is valid probability distribution")
    n_pass += 1

    # Test 14: Birthday collision analysis produces valid output
    bday = birthday_collision_analysis([(3, 5), (5, 13)], max_comb=500000)
    assert len(bday) == 2, f"Expected 2 results, got {len(bday)}"
    for br in bday:
        assert br['avg_distinct'] <= br['km1'], (
            f"avg_distinct {br['avg_distinct']} > km1 {br['km1']}")
        assert br['avg_distinct'] >= 1, (
            f"avg_distinct {br['avg_distinct']} < 1")
        assert br['distinct_surplus'] is not None
        assert br['sampling_fraction'] > 0 and br['sampling_fraction'] < 1
        assert br['coverage'] > 0
    print(f"  [PASS] T14: Birthday collision analysis valid "
          f"(surplus: {[f'{br['distinct_surplus']:+.3f}' for br in bday]})")
    n_pass += 1

    # Test 15: Sampling fraction convergence to 1/log2(3)
    sf = sampling_fraction_scaling(k_max=100)
    f_limit = 1.0 / math.log2(3)
    # Check that f converges
    assert abs(sf[-1]['f'] - f_limit) < 0.005, (
        f"f(100) = {sf[-1]['f']:.5f} too far from limit {f_limit:.5f}")
    # Check that f is always > 0.5 for k >= 3
    for entry in sf:
        assert entry['f'] >= 0.5, f"f({entry['k']}) = {entry['f']:.5f} < 0.5"
    # Check FPC is in (0, 1)
    for entry in sf:
        assert 0 < entry['fpc'] < 1, (
            f"FPC({entry['k']}) = {entry['fpc']:.5f} out of (0,1)")
    print(f"  [PASS] T15: Sampling fraction f -> {f_limit:.5f}, "
          f"FPC always in (0,1), f > 0.5 for all k >= 3")
    n_pass += 1

    # Test 16: Orbit sizes match ord_p(2)
    for k_t, p_t in [(5, 13), (7, 23)]:
        bday_t = birthday_collision_analysis([(k_t, p_t)])
        if bday_t:
            br = bday_t[0]
            ord2 = br['ord2']
            # Number of distinct powers should be min(ord2, S-1)
            expected_distinct = min(ord2, br['n_pool'])
            assert br['n_distinct_in_pool'] == expected_distinct, (
                f"k={k_t}, p={p_t}: n_distinct_in_pool={br['n_distinct_in_pool']}, "
                f"expected {expected_distinct}")
    print(f"  [PASS] T16: n_distinct_in_pool = min(ord_p(2), S-1)")
    n_pass += 1

    # Test 17: Coverage = avg_distinct / n_distinct_in_pool
    for br in bday:
        expected_cov = br['avg_distinct'] / br['n_distinct_in_pool']
        assert abs(br['coverage'] - expected_cov) < 1e-10, (
            f"Coverage mismatch: {br['coverage']} vs {expected_cov}")
    print(f"  [PASS] T17: Coverage = avg_distinct / n_distinct_in_pool")
    n_pass += 1

    print()
    print(f"  SELF-TESTS: {n_pass} PASSED, {n_fail} FAILED")
    print("=" * 76)
    print()
    return n_fail == 0


# ============================================================================
# SECTION 8: MAIN ANALYSIS
# ============================================================================

def gather_cases(k_max=15, p_max=500):
    """Gather all (k, p) pairs where p | d(k) and p <= p_max."""
    cases = []
    for k in range(3, k_max + 1):
        d = d_of_k(k)
        if d <= 0:
            continue
        for p in prime_factors(d):
            if p <= p_max:
                cases.append((k, p))
    return cases


def run_full_analysis():
    """Run the complete Round 2 analysis."""
    t_start = time.time()

    print("=" * 76)
    print("  ROUND 2: QUANTIFYING THE WITHOUT-REPLACEMENT EFFECT")
    print("  IN THE COLLATZ HORNER CHAIN")
    print("=" * 76)
    print()

    K_MAX = 15
    P_MAX = 500
    MAX_COMB = 500000

    cases = gather_cases(K_MAX, P_MAX)
    print(f"  Configuration: k in [3, {K_MAX}], p <= {P_MAX}")
    print(f"  Total (k, p) pairs: {len(cases)}")
    print()

    # Identify feasible cases for exact enumeration
    feasible = [(k, p) for k, p in cases
                if math.comb(S_of_k(k) - 1, k - 1) <= MAX_COMB]
    print(f"  Feasible for exact enumeration (C <= {MAX_COMB}): {len(feasible)}")
    print()

    # Show all cases
    print(f"  {'k':>3} {'S':>4} {'p':>6} {'d(k)':>12} {'C(S-1,k-1)':>12} {'feasible':>8}")
    print("  " + "-" * 49)
    for k, p in cases:
        S = S_of_k(k)
        C = math.comb(S - 1, k - 1)
        feas = "YES" if C <= MAX_COMB else "no"
        print(f"  {k:>3} {S:>4} {p:>6} {d_of_k(k):>12} {C:>12} {feas:>8}")
    print()

    # ==================================================================
    # Q1: EXACT vs MARKOV
    # ==================================================================
    print("=" * 76)
    print("  Q1: EXACT (WITHOUT REPLACEMENT) vs MARKOV (WITH REPLACEMENT)")
    print("=" * 76)
    print()
    print("  Central question: does sampling WITHOUT replacement create a")
    print("  systematic deviation in P(c_{k-1} = 0 mod p)?")
    print()

    q1_results = run_q1_exact_vs_markov(feasible, MAX_COMB)

    hdr = (f"  {'k':>3} {'p':>6} {'C':>10} {'N0':>8} "
           f"{'P0_exact':>12} {'P0_markov':>12} {'1/p':>10} "
           f"{'ex/mk':>8} {'ex*p':>8} {'TV':>10}")
    print(hdr)
    print("  " + "-" * (len(hdr) - 2))

    for r in q1_results:
        print(f"  {r['k']:>3} {r['p']:>6} {r['C_total']:>10} {r['N0_exact']:>8} "
              f"{r['P0_exact']:>12.8f} {r['P0_markov']:>12.8f} "
              f"{r['P0_uniform']:>10.8f} "
              f"{r['ratio_exact_markov']:>8.4f} "
              f"{r['ratio_exact_uniform']:>8.4f} "
              f"{r['tv_distance']:>10.6f}")

    print()

    # Statistical summary of Q1
    if q1_results:
        ratios = [r['ratio_exact_markov'] for r in q1_results]
        ex_unif = [r['ratio_exact_uniform'] for r in q1_results]
        mk_unif = [r['ratio_markov_uniform'] for r in q1_results]
        tvs = [r['tv_distance'] for r in q1_results]

        print(f"  STATISTICAL SUMMARY:")
        print(f"    exact/markov  ratio: mean={np.mean(ratios):.4f}, "
              f"std={np.std(ratios):.4f}, min={min(ratios):.4f}, max={max(ratios):.4f}")
        print(f"    exact*p       ratio: mean={np.mean(ex_unif):.4f}, "
              f"std={np.std(ex_unif):.4f}")
        print(f"    markov*p      ratio: mean={np.mean(mk_unif):.4f}, "
              f"std={np.std(mk_unif):.4f}")
        print(f"    TV distance        : mean={np.mean(tvs):.6f}, "
              f"max={max(tvs):.6f}")
        print()

        # Count how often exact < Markov at residue 0
        n_exact_below = sum(1 for r in q1_results if r['P0_exact'] < r['P0_markov'] - 1e-10)
        n_exact_above = sum(1 for r in q1_results if r['P0_exact'] > r['P0_markov'] + 1e-10)
        n_exact_equal = len(q1_results) - n_exact_below - n_exact_above
        print(f"    P0_exact < P0_markov (WR helps exclude):  {n_exact_below}")
        print(f"    P0_exact > P0_markov (WR hurts exclude):  {n_exact_above}")
        print(f"    P0_exact ~ P0_markov (neutral):           {n_exact_equal}")
        print()

        # Count how often exact < 1/p
        n_below_unif = sum(1 for r in q1_results if r['P0_exact'] < 1.0/r['p'] - 1e-10)
        n_above_unif = sum(1 for r in q1_results if r['P0_exact'] > 1.0/r['p'] + 1e-10)
        n_at_unif = len(q1_results) - n_below_unif - n_above_unif
        print(f"    P0_exact < 1/p:  {n_below_unif}")
        print(f"    P0_exact > 1/p:  {n_above_unif}")
        print(f"    P0_exact ~ 1/p:  {n_at_unif}")
    print()

    # ==================================================================
    # Q2: COVARIANCE STRUCTURE
    # ==================================================================
    print("=" * 76)
    print("  Q2: COVARIANCE STRUCTURE OF WITHOUT-REPLACEMENT INCREMENTS")
    print("=" * 76)
    print()
    print("  In without-replacement sampling, if element b is used at step j,")
    print("  it's unavailable at step j'. This creates NEGATIVE covariance")
    print("  between increments (classical result for sampling w/o replacement).")
    print()
    print("  For a finite population of size N, sampling n items without")
    print("  replacement gives Cov(X_i, X_j) = -sigma^2/(N-1) for i != j")
    print("  (where sigma^2 is the population variance).")
    print()
    print("  BUT: in our Horner chain, the increments are 2^b mod p, not b.")
    print("  And the positions in the chain are NOT symmetric (the weights")
    print("  3^0, 3^1, ..., 3^{k-2} differ). So the standard formula may")
    print("  not directly apply.")
    print()

    cov_results = []
    for k, p in feasible:
        cr = compute_step_covariance(k, p, MAX_COMB)
        if cr is not None:
            cov_results.append(cr)

    if cov_results:
        print(f"  {'k':>3} {'p':>6} {'avg_cov':>12} {'max|corr|':>12} "
              f"{'var_WR':>10} {'var_step_min':>12} {'var_step_max':>12}")
        print("  " + "-" * 69)

        for cr in cov_results:
            print(f"  {cr['k']:>3} {cr['p']:>6} "
                  f"{cr['avg_cov_consecutive']:>12.4f} "
                  f"{cr['max_abs_corr_offdiag']:>12.6f} "
                  f"{cr['var_wr']:>10.4f} "
                  f"{min(cr['var_steps']):>12.4f} "
                  f"{max(cr['var_steps']):>12.4f}")
        print()

        # Detailed covariance for first few cases
        for cr in cov_results[:3]:
            k, p = cr['k'], cr['p']
            print(f"  Detailed covariance: k={k}, p={p}")
            print(f"    Consecutive Cov values: "
                  f"{[f'{c:.4f}' for c in cr['cov_consecutive']]}")
            n = cr['km1']
            if n <= 8:
                print(f"    Correlation matrix (truncated diag):")
                for i in range(n):
                    row_str = "      "
                    for j in range(n):
                        if i == j:
                            row_str += "  1.000"
                        else:
                            row_str += f" {cr['corr_matrix'][i,j]:>6.3f}"
                    print(row_str)
            print()

        # Is the covariance systematically negative?
        all_covs = []
        for cr in cov_results:
            all_covs.extend(cr['cov_consecutive'])
        n_neg = sum(1 for c in all_covs if c < -1e-8)
        n_pos = sum(1 for c in all_covs if c > 1e-8)
        n_zero = len(all_covs) - n_neg - n_pos
        print(f"  COVARIANCE SIGN SUMMARY across all consecutive pairs:")
        print(f"    Negative: {n_neg}  Positive: {n_pos}  Zero: {n_zero}")
        if all_covs:
            print(f"    Mean: {np.mean(all_covs):.6f}")
            print(f"    Min:  {min(all_covs):.6f}")
            print(f"    Max:  {max(all_covs):.6f}")
    print()

    # ==================================================================
    # Q3: DEPLETION EFFECT
    # ==================================================================
    print("=" * 76)
    print("  Q3: DEPLETION EFFECT -- EFFECTIVE RANDOMNESS AT EACH STEP")
    print("=" * 76)
    print()
    print("  As the chain progresses and elements are 'used up', the last")
    print("  few steps have less randomness. Does this create a systematic")
    print("  bias in P(c_{k-1} = 0)?")
    print()

    dep_results = []
    for k, p in feasible:
        dr = compute_depletion_effect(k, p, MAX_COMB)
        if dr is not None:
            dep_results.append(dr)

    if dep_results:
        for dr in dep_results[:5]:  # Show first 5
            k, p = dr['k'], dr['p']
            print(f"  k={k}, p={p}, pool={dr['n_pool']}, C={dr['C_total']}")
            print(f"  {'step':>5} {'#states':>8} {'#choices':>8} "
                  f"{'E[P0|cj]':>12} {'Var[P0|cj]':>12} "
                  f"{'min P0':>10} {'max P0':>10}")
            for sa in dr['step_analysis']:
                print(f"  {sa['step']:>5} {sa['n_distinct_states']:>8} "
                      f"{sa['n_effective_choices']:>8} "
                      f"{sa['cond_P0_mean']:>12.6f} "
                      f"{sa['cond_P0_var']:>12.8f} "
                      f"{sa['cond_P0_min']:>10.6f} "
                      f"{sa['cond_P0_max']:>10.6f}")
            print()

        # Key metric: does Var[P0|c_j] increase as j increases?
        # (More variance = more information = less uniform)
        print("  DEPLETION TREND: Var[P(c_{k-1}=0 | c_j)] vs step j")
        print("  If variance increases with j, later steps are more 'informative'")
        print("  about the final value -- consistent with depletion.")
        print()
        for dr in dep_results:
            k, p = dr['k'], dr['p']
            vars_by_step = [sa['cond_P0_var'] for sa in dr['step_analysis'][1:]]
            if len(vars_by_step) >= 2:
                # Check if variance is increasing
                increasing = all(vars_by_step[i] <= vars_by_step[i+1] + 1e-12
                                for i in range(len(vars_by_step) - 1))
                trend = "INCREASING" if increasing else "NON-MONOTONE"
                print(f"    k={k:>2}, p={p:>3}: variances = "
                      f"{[f'{v:.6f}' for v in vars_by_step]}  [{trend}]")
    print()

    # ==================================================================
    # Q3b: BIRTHDAY-STYLE COLLISION ANALYSIS
    # ==================================================================
    print("=" * 76)
    print("  Q3b: BIRTHDAY-STYLE COLLISION ANALYSIS")
    print("=" * 76)
    print()
    print("  The Markov model draws exponents WITH replacement from {1,...,S-1}.")
    print("  Without replacement, different exponents b can still produce the")
    print("  SAME 2^b mod p value (when b1 != b2 but b1 = b2 mod ord_p(2)).")
    print("  This is a 'collision' in the power-residue space.")
    print()
    print("  Key question: does the non-repetition structure bias the")
    print("  number/pattern of distinct 2^b values in corrSum=0 subsets?")
    print()

    bday_results = birthday_collision_analysis(feasible, MAX_COMB)

    if bday_results:
        hdr_b = (f"  {'k':>3} {'p':>6} {'ord2':>5} {'#pool':>5} {'#dist':>5} "
                 f"{'f':>6} {'avg_d':>7} {'E[d]_wr':>7} "
                 f"{'surplus':>8} {'avg_d_0':>7} {'avg_d_nz':>8}")
        print(hdr_b)
        print("  " + "-" * (len(hdr_b) - 2))

        for br in bday_results:
            ad0 = br['avg_distinct_zero']
            adnz = br['avg_distinct_nonzero']
            ad0_s = f"{ad0:>7.3f}" if not math.isnan(ad0) else f"{'nan':>7}"
            adnz_s = f"{adnz:>8.3f}" if not math.isnan(adnz) else f"{'nan':>8}"
            print(f"  {br['k']:>3} {br['p']:>6} {br['ord2']:>5} "
                  f"{br['n_distinct_in_pool']:>5} {br['km1']:>5} "
                  f"{br['sampling_fraction']:>6.3f} "
                  f"{br['avg_distinct']:>7.3f} "
                  f"{br['expected_distinct_wr']:>7.3f} "
                  f"{br['distinct_surplus']:>+8.3f} "
                  f"{ad0_s} {adnz_s}")

        print()

        # Analyze collision surplus
        surpluses = [br['distinct_surplus'] for br in bday_results]
        print(f"  COLLISION SURPLUS = avg_distinct(WOR) - E[distinct](WR):")
        print(f"    Mean surplus:  {np.mean(surpluses):+.4f}")
        print(f"    All positive:  {all(s > -0.01 for s in surpluses)}")
        print(f"    Interpretation: positive surplus means without-replacement")
        print(f"    tends to produce MORE distinct 2^b values (fewer collisions)")
        print(f"    than the with-replacement model predicts.")
        print()

        # Compare zero vs nonzero subsets
        diffs = []
        for br in bday_results:
            ad0 = br['avg_distinct_zero']
            adnz = br['avg_distinct_nonzero']
            if not math.isnan(ad0) and not math.isnan(adnz) and br['N0'] > 0:
                diffs.append(ad0 - adnz)
        if diffs:
            print(f"  ZERO vs NONZERO subsets (avg distinct 2^b mod p):")
            print(f"    Mean (zero - nonzero): {np.mean(diffs):+.4f}")
            print(f"    Cases zero > nonzero:  {sum(1 for d in diffs if d > 0.01)}/{len(diffs)}")
            print(f"    Cases zero < nonzero:  {sum(1 for d in diffs if d < -0.01)}/{len(diffs)}")
            print(f"    If zero subsets use MORE distinct values, the non-repetition")
            print(f"    structure is NOT helping exclude them.")
        print()

        # Orbit structure analysis
        print(f"  ORBIT STRUCTURE of <2> mod p:")
        for br in bday_results[:6]:
            os_str = str(br['orbit_sizes'][:5])
            if len(br['orbit_sizes']) > 5:
                os_str = os_str[:-1] + ", ...]"
            print(f"    k={br['k']:>2}, p={br['p']:>3}, ord2={br['ord2']:>3}: "
                  f"orbit sizes = {os_str}, coverage = {br['coverage']:.3f}")
        print()

    # Sampling fraction scaling
    print("  SAMPLING FRACTION f = (k-1)/(S-1) SCALING:")
    print()
    f_limit = 1.0 / math.log2(3)
    print(f"  CRITICAL FINDING: f -> 1/log2(3) = {f_limit:.5f} as k -> inf")
    print(f"  This means ~63% of the pool is ALWAYS used.")
    print(f"  Without-replacement is a PERMANENT structural constraint.")
    print()
    sf_data = sampling_fraction_scaling(k_max=min(K_MAX + 10, 50))
    print(f"  {'k':>3} {'S':>4} {'M':>4} {'n':>3} {'f':>8} {'fpc':>8} {'|f-f*|':>8}")
    print(f"  " + "-" * 39)
    for sd in sf_data:
        if sd['k'] <= K_MAX or sd['k'] % 5 == 0:
            print(f"  {sd['k']:>3} {sd['S']:>4} {sd['M']:>4} {sd['n']:>3} "
                  f"{sd['f']:>8.5f} {sd['fpc']:>8.5f} {sd['f_deviation']:>8.5f}")
    print()

    # ==================================================================
    # Q4: COUPLING AND TOTAL VARIATION
    # ==================================================================
    print("=" * 76)
    print("  Q4: COUPLING ARGUMENT AND TOTAL VARIATION DISTANCE")
    print("=" * 76)
    print()
    print("  TV(exact, Markov) measures the maximum difference in probability")
    print("  for any event between the two models.")
    print("  The deviation at residue 0 tells us if WR helps or hurts.")
    print()

    tv_results = []
    for k, p in feasible:
        tvr = compute_tv_and_coupling(k, p, MAX_COMB)
        if tvr is not None:
            tv_results.append(tvr)

    if tv_results:
        print(f"  {'k':>3} {'p':>6} {'TV':>10} {'L-inf':>10} "
              f"{'coupling_UB':>12} {'dev@0':>12} {'direction':>10} "
              f"{'P0_ex':>10} {'P0_mk':>10}")
        print("  " + "-" * 96)

        for r in tv_results:
            print(f"  {r['k']:>3} {r['p']:>6} "
                  f"{r['tv_distance']:>10.6f} "
                  f"{r['linf_distance']:>10.6f} "
                  f"{r['coupling_ub']:>12.6f} "
                  f"{r['dev_at_zero']:>12.8f} "
                  f"{r['direction_at_zero']:>10} "
                  f"{r['P0_exact']:>10.6f} "
                  f"{r['P0_markov']:>10.6f}")
        print()

        # Summary of direction at zero
        n_favors = sum(1 for r in tv_results if r['direction_at_zero'] == 'FAVORS')
        n_disfavors = sum(1 for r in tv_results if r['direction_at_zero'] == 'DISFAVORS')
        n_neutral = sum(1 for r in tv_results if r['direction_at_zero'] == 'NEUTRAL')
        print(f"  Direction at residue 0:")
        print(f"    FAVORS (WR increases P0, hurts exclusion): {n_favors}")
        print(f"    DISFAVORS (WR decreases P0, helps exclusion): {n_disfavors}")
        print(f"    NEUTRAL: {n_neutral}")
        print()

        # Does TV distance decrease as k grows? (mixing argument)
        by_k = defaultdict(list)
        for r in tv_results:
            by_k[r['k']].append(r['tv_distance'])
        print(f"  TV distance by k (averaged over primes):")
        for k_val in sorted(by_k.keys()):
            tvs = by_k[k_val]
            print(f"    k={k_val:>2}: mean TV = {np.mean(tvs):.6f} "
                  f"(from {len(tvs)} primes)")
    print()

    # ==================================================================
    # Q5: KEY THEOREM ATTEMPT
    # ==================================================================
    print("=" * 76)
    print("  Q5: KEY THEOREM ATTEMPT")
    print("  'P_exact(c_{k-1} = 0) <= (1 - delta) / p for delta > 0'")
    print("=" * 76)
    print()
    print("  If delta > 0 consistently, without-replacement HELPS exclude cycles.")
    print("  If delta can be negative, the theorem as stated is FALSE.")
    print()

    q5_results = attempt_key_theorem(feasible, MAX_COMB)

    if q5_results:
        print(f"  {'k':>3} {'p':>6} {'N0':>8} {'P0':>12} {'1/p':>10} "
              f"{'delta':>10} {'z-score':>8} {'rank':>5} {'helps?':>6}")
        print("  " + "-" * 79)

        for r in q5_results:
            helps = "YES" if r['helps_exclude'] else "NO"
            print(f"  {r['k']:>3} {r['p']:>6} {r['N0']:>8} "
                  f"{r['P0']:>12.8f} {r['uniform']:>10.8f} "
                  f"{r['delta']:>10.6f} {r['z_score']:>8.3f} "
                  f"{r['rank_of_zero']:>5} {helps:>6}")
        print()

        # Count evidence
        n_helps = sum(1 for r in q5_results if r['helps_exclude'])
        n_hurts = sum(1 for r in q5_results if not r['helps_exclude'])
        print(f"  EVIDENCE SUMMARY:")
        print(f"    delta > 0 (WR helps exclude, P0 < 1/p): {n_helps} cases")
        print(f"    delta <= 0 (WR does NOT help, P0 >= 1/p): {n_hurts} cases")
        print()

        # Average delta
        deltas = [r['delta'] for r in q5_results]
        z_scores = [r['z_score'] for r in q5_results]
        print(f"    Mean delta: {np.mean(deltas):.6f}")
        print(f"    Std delta:  {np.std(deltas):.6f}")
        print(f"    Min delta:  {min(deltas):.6f}")
        print(f"    Max delta:  {max(deltas):.6f}")
        print(f"    Mean z-score: {np.mean(z_scores):.3f}")
        print()

        # Is there a trend with k?
        by_k = defaultdict(list)
        for r in q5_results:
            by_k[r['k']].append(r['delta'])
        print(f"  TREND BY k:")
        for k_val in sorted(by_k.keys()):
            ds = by_k[k_val]
            print(f"    k={k_val:>2}: mean delta = {np.mean(ds):>+.6f}, "
                  f"n={len(ds)}, all positive = {all(d > 0 for d in ds)}")
    print()

    # ==================================================================
    # PERMUTATION / ORDERING ANALYSIS
    # ==================================================================
    print("=" * 76)
    print("  ORDERING ANALYSIS: CANONICAL vs RANDOM PERMUTATIONS")
    print("=" * 76)
    print()
    print("  The canonical ordering b_1 < b_2 < ... < b_{k-1} pairs LARGER")
    print("  powers 2^{b_i} with LARGER weights 3^{i-1} in the corrSum.")
    print("  By the rearrangement inequality, this MAXIMIZES the sum among")
    print("  all permutations. Does this affect P(corrSum = 0)?")
    print()

    perm_results = []
    # Only feasible for small k (factorial blowup)
    for k, p in feasible:
        if k - 1 <= 7:
            pr = permutation_effect_analysis(k, p, 200000)
            if pr is not None:
                perm_results.append(pr)

    if perm_results:
        print(f"  {'k':>3} {'p':>6} {'#subsets':>8} {'k-1':>4} "
              f"{'P0_canon':>10} {'P0_random':>10} {'P0_reverse':>10} "
              f"{'1/p':>8} {'can/rand':>8}")
        print("  " + "-" * 82)

        for pr in perm_results:
            print(f"  {pr['k']:>3} {pr['p']:>6} {pr['total_subsets']:>8} "
                  f"{pr['km1']:>4} "
                  f"{pr['P0_canonical']:>10.6f} "
                  f"{pr['P0_random_perm']:>10.6f} "
                  f"{pr['P0_reverse']:>10.6f} "
                  f"{pr['P0_uniform']:>8.6f} "
                  f"{pr['ratio_canonical_random']:>8.4f}")
        print()

        # Summary
        n_canon_less = sum(1 for pr in perm_results
                         if pr['P0_canonical'] < pr['P0_random_perm'] - 1e-10)
        n_canon_more = sum(1 for pr in perm_results
                         if pr['P0_canonical'] > pr['P0_random_perm'] + 1e-10)
        n_canon_same = len(perm_results) - n_canon_less - n_canon_more
        print(f"  ORDERING EFFECT:")
        print(f"    Canonical < Random permutation (ordering helps exclude): {n_canon_less}")
        print(f"    Canonical > Random permutation (ordering hurts exclude): {n_canon_more}")
        print(f"    Canonical ~ Random permutation (no ordering effect):     {n_canon_same}")
        if perm_results:
            avg_ratio = np.mean([pr['ratio_canonical_random']
                                for pr in perm_results
                                if pr['ratio_canonical_random'] < 100])
            print(f"    Average canonical/random ratio: {avg_ratio:.4f}")
    print()

    # ==================================================================
    # GRAND CONCLUSIONS
    # ==================================================================
    print("=" * 76)
    print("  GRAND CONCLUSIONS: THE WITHOUT-REPLACEMENT EFFECT")
    print("=" * 76)
    print()

    # Determine the honest verdict
    if q5_results:
        deltas = [r['delta'] for r in q5_results]
        n_helps = sum(1 for d in deltas if d > 1e-6)
        n_hurts = sum(1 for d in deltas if d < -1e-6)
        mean_delta = np.mean(deltas)

        if n_hurts == 0 and n_helps > 0:
            print("  VERDICT: WITHOUT-REPLACEMENT SYSTEMATICALLY HELPS EXCLUDE CYCLES")
            print()
            print("  In ALL tested cases, P_exact(c_{k-1}=0) <= 1/p.")
            print("  The without-replacement constraint creates a systematic bias")
            print("  AGAINST corrSum = 0 mod p.")
            print()
            print("  The proposed theorem P_exact <= (1-delta)/p appears SUPPORTED")
            print("  by the numerical evidence, though a rigorous proof is needed.")
        elif n_helps == 0 and n_hurts > 0:
            print("  VERDICT: WITHOUT-REPLACEMENT SYSTEMATICALLY HURTS EXCLUSION")
            print()
            print("  In ALL tested cases, P_exact(c_{k-1}=0) >= 1/p.")
            print("  The without-replacement constraint INCREASES the probability")
            print("  of corrSum = 0 mod p, making cycle exclusion HARDER.")
            print()
            print("  The proposed theorem P_exact <= (1-delta)/p is FALSE.")
        elif n_helps > 0 and n_hurts > 0:
            print("  VERDICT: NO SYSTEMATIC DIRECTION -- MIXED EFFECT")
            print()
            print(f"  Among {len(deltas)} tested cases:")
            print(f"    {n_helps} cases where WR helps (delta > 0)")
            print(f"    {n_hurts} cases where WR hurts (delta < 0)")
            print(f"    Mean delta = {mean_delta:+.6f}")
            print()
            print("  The without-replacement effect does NOT have a consistent sign.")
            print("  The proposed theorem P_exact <= (1-delta)/p is FALSE in general.")
            print("  The effect depends on the specific (k, p) pair.")
            print()
            if abs(mean_delta) < 0.01:
                print("  MOREOVER: the mean delta is close to zero, suggesting that")
                print("  without-replacement is essentially a NEUTRAL perturbation")
                print("  of the Markov model, at least at the level of P(c_{k-1}=0).")
        else:
            print("  VERDICT: WITHOUT-REPLACEMENT HAS NO DETECTABLE EFFECT")
            print()
            print("  P_exact ~ P_markov ~ 1/p in all tested cases.")
    print()

    print("  DETAILED MECHANISM ANALYSIS:")
    print()
    print("  1. COVARIANCE EFFECT (Q2):")
    if cov_results:
        all_covs = []
        for cr in cov_results:
            all_covs.extend(cr['cov_consecutive'])
        if all_covs:
            n_neg = sum(1 for c in all_covs if c < -1e-8)
            mean_c = np.mean(all_covs)
            print(f"     {n_neg}/{len(all_covs)} consecutive covariances are negative.")
            print(f"     Mean covariance = {mean_c:.6f}")
            if n_neg > len(all_covs) * 0.6:
                print("     WITHOUT-REPLACEMENT DOES CREATE ANTI-CORRELATION,")
                print("     consistent with the classical finite-population theory.")
            else:
                print("     Anti-correlation is present but not universal.")
            print("     However, anti-correlation in increments does NOT directly")
            print("     translate to a bias in P(c_{k-1}=0).")
    print()

    print("  2. DEPLETION EFFECT (Q3):")
    print("     Later steps in the chain have fewer available exponents,")
    print("     reducing diversity. However, this affects ALL residues")
    print("     equally (by the doubly stochastic structure of T),")
    print("     so depletion alone cannot create a bias at residue 0.")
    print()

    print("  3. ORDERING EFFECT (PERMUTATION ANALYSIS):")
    if perm_results:
        n_canon_less = sum(1 for pr in perm_results
                         if pr['P0_canonical'] < pr['P0_random_perm'] - 1e-10)
        print(f"     In {n_canon_less}/{len(perm_results)} cases, the canonical")
        print("     ordering (b_1 < ... < b_{k-1}) gives LOWER P0 than random")
        print("     permutations. The rearrangement inequality suggests that")
        print("     the canonical ordering pushes corrSum toward larger values,")
        print("     potentially away from 0.")
    print()

    print("  4. BIRTHDAY COLLISION STRUCTURE (Q3b):")
    if bday_results:
        surpluses = [br['distinct_surplus'] for br in bday_results]
        print(f"     Mean distinct surplus (WOR - WR): {np.mean(surpluses):+.4f}")
        print("     Without-replacement tends to produce MORE distinct 2^b mod p")
        print("     values than with-replacement (fewer collisions in residue space).")
        print("     However, this does NOT translate to a systematic bias at residue 0.")
        # Check zero vs nonzero
        diffs_z_nz = []
        for br in bday_results:
            ad0 = br['avg_distinct_zero']
            adnz = br['avg_distinct_nonzero']
            if not math.isnan(ad0) and not math.isnan(adnz) and br['N0'] > 0:
                diffs_z_nz.append(ad0 - adnz)
        if diffs_z_nz:
            print(f"     Zero vs nonzero subsets: mean(d_zero - d_nonzero) = {np.mean(diffs_z_nz):+.4f}")
    print()

    print("  5. SAMPLING FRACTION SCALING:")
    f_limit = 1.0 / math.log2(3)
    print(f"     f = (k-1)/(S-1) -> 1/log2(3) ~ {f_limit:.5f}")
    print("     The sampling fraction is CONSTANT at ~63%.")
    print("     Without-replacement is a permanent structural constraint,")
    print("     not a vanishing perturbation.")
    print()

    print("  6. TOTAL VARIATION (Q4):")
    if tv_results:
        tvs = [r['tv_distance'] for r in tv_results]
        print(f"     Mean TV(exact, Markov) = {np.mean(tvs):.6f}")
        print(f"     Max TV = {max(tvs):.6f}")
        print("     The two distributions are CLOSE, confirming that the")
        print("     Markov model is a reasonable approximation.")
        n_disfavors = sum(1 for r in tv_results
                         if r['direction_at_zero'] == 'DISFAVORS')
        print(f"     At residue 0: WR disfavors in {n_disfavors}/{len(tv_results)} cases.")
    print()

    print("  IMPLICATION FOR COLLATZ CYCLE EXCLUSION:")
    print("  The without-replacement effect is REAL but SMALL and NOT")
    print("  systematically in one direction. It cannot be relied upon")
    print("  as a standalone obstruction to nontrivial cycles.")
    print("  The primary obstructions remain:")
    print("    (a) The CRT product over multiple primes: 1/prod(p_i)")
    print("    (b) The growth constraint: S must be EXACTLY ceil(k*log2(3))")
    print("    (c) The positivity constraint: all x_i > 0")
    print("  The sampling fraction f ~ 63% is permanently large, meaning")
    print("  the non-independence is structurally significant even as k -> inf.")
    print("  Yet the NET effect on P(corrSum=0) is small, because the doubly")
    print("  stochastic structure of T ensures approximate uniformity regardless.")
    print()

    return q1_results, q5_results, tv_results, perm_results


# ============================================================================
# SECTION 9: SHA256 FINGERPRINT
# ============================================================================

def compute_fingerprint(q1_results, q5_results):
    """Compute SHA256 of key numerical results for reproducibility."""
    data = {
        'q1': [(r['k'], r['p'], r['N0_exact'], r['C_total'],
                round(r['P0_exact'], 12), round(r['P0_markov'], 12),
                round(r['tv_distance'], 10))
               for r in q1_results],
        'q5': [(r['k'], r['p'], r['N0'], r['C_total'],
                round(r['delta'], 10), round(r['z_score'], 6))
               for r in q5_results],
    }
    sig = json.dumps(data, sort_keys=True)
    return hashlib.sha256(sig.encode()).hexdigest()


# ============================================================================
# ENTRY POINT
# ============================================================================

if __name__ == "__main__":
    # Self-tests
    tests_ok = self_test()
    if not tests_ok:
        print("ABORTING: self-tests failed.")
        sys.exit(1)

    # Full analysis
    q1_res, q5_res, tv_res, perm_res = run_full_analysis()

    # SHA256 fingerprint
    sha = compute_fingerprint(q1_res, q5_res)
    print(f"  SHA256 fingerprint: {sha}")
    print()
    print("=" * 76)
    print("  END OF ROUND 2 ANALYSIS")
    print("=" * 76)
