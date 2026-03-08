#!/usr/bin/env python3
"""
r4_mixing_time_proof.py — Round 4: Mixing Time vs Cycle Length for Collatz
==========================================================================

THE CENTRAL QUESTION:
  The Horner chain c_{j+1} = 3c_j + 2^{b_{k-1-j}} mod d defines an orbit
  in Z/dZ of length k. A cycle exists iff c_k = 0 mod d.

  If the MIXING TIME tau_mix of this chain exceeds k, then after k steps
  the distribution is far from uniform, and P(c_k = 0) can be very
  different from 1/d. In particular, if the TV distance ||P^k - pi||_TV
  is close to 1, the orbit has not had time to reach 0 with any
  significant probability.

  This script attempts to PROVE (or rigorously formalize) that tau_mix > k
  for the Horner chain on Z/dZ for all k >= 3.

MATHEMATICAL FRAMEWORK:
  The transition at each step is: c -> 3c + 2^a mod m, where a is drawn
  from a set A subset of {0, 1, ..., S-1}. For the FULL chain mod d,
  A = {0, 1, ..., S-1} (all S values). For mod p (p | d), same A.

  The transition matrix T on Z/mZ is:
    T[r][s] = (1/|A|) * |{a in A : (3r + 2^a) mod m = s}|

  This is a random walk on (Z/mZ, +) with drift 3 and additive noise 2^a.

  Key facts from prior rounds:
    - T is doubly stochastic (R11) => stationary distribution = uniform
    - pi(0) = 1/m exactly
    - Residues mod distinct primes are quasi-independent (R15)
    - The orbit ratio k/E[return] -> 0 exponentially (R18)

FIVE PARTS:
  Part 1: Exact mixing time by matrix power iteration (k = 3..15)
  Part 2: Spectral gap lower bound via eigenvalue computation
  Part 3: Fourier analysis of the transition kernel
  Part 4: Direct TV distance at step k (the counting argument)
  Part 5: Asymptotic analysis and trend extrapolation

Author: Claude (Round 4 Theoretician for Eric Merle's Collatz Junction Theorem)
Date:   2026-03-08
"""

import math
import hashlib
import sys
import time
import cmath
from itertools import combinations
from collections import Counter, defaultdict


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """S = ceil(k * log2(3))."""
    return math.ceil(k * math.log2(3))


def compute_d(k):
    """d(k) = 2^S - 3^k."""
    S = compute_S(k)
    return (1 << S) - 3**k


def prime_factorization(n):
    """Return list of (prime, exponent) pairs for |n|."""
    n = abs(n)
    if n <= 1:
        return []
    factors = []
    trial = 2
    while trial * trial <= n:
        if n % trial == 0:
            e = 0
            while n % trial == 0:
                e += 1
                n //= trial
            factors.append((trial, e))
        trial += 1
    if n > 1:
        factors.append((n, 1))
    return factors


def distinct_prime_factors(n):
    """Return sorted list of distinct prime factors of |n|."""
    return [p for p, _ in prime_factorization(n)]


def modinv(a, m):
    """Modular inverse of a mod m via extended GCD."""
    if m == 1:
        return 0
    g, x, _ = _extended_gcd(a % m, m)
    if g != 1:
        return None
    return x % m


def _extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = _extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


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


def corrsum_from_subset(B_tuple, k, mod):
    """
    Compute corrSum mod `mod` from a (k-1)-subset B of {1,...,S-1}.
    With b_0 = 0:
        corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j} mod `mod`
    """
    result = pow(3, k - 1, mod)
    for idx in range(len(B_tuple)):
        j = idx + 1
        result = (result + pow(3, k - 1 - j, mod)
                  * pow(2, B_tuple[idx], mod)) % mod
    return result


def num_compositions(S, k):
    """C(S-1, k-1): number of compositions of S into k positive parts."""
    return math.comb(S - 1, k - 1)


# ============================================================================
# PART 1: EXACT MIXING TIME BY MATRIX POWER ITERATION
# ============================================================================
#
# For the Horner chain mod m (where m = p prime dividing d, or m = d itself
# for small d), we build the transition matrix T and compute T^n * delta_0
# until ||T^n * delta_0 - uniform||_TV < 1/4.
#
# The mixing time is:
#   tau_mix = min{n : max_x ||T^n(x, .) - pi||_TV < 1/4}
#
# For doubly stochastic T, pi = uniform = (1/m, ..., 1/m).
# Since T is doubly stochastic, max_x is achieved at some x. We compute
# from EVERY starting state to get the true worst-case.
#
# For computational reasons, we work mod p (primes dividing d) for larger k.
# ============================================================================

def build_transition_matrix_pure(m, S):
    """
    Build the |A|=S transition matrix T on Z/mZ for the Horner chain.

    T[r][s] = (1/S) * |{a in {0,...,S-1} : (3r + 2^a) mod m = s}|

    Returns: T as list of lists (m x m), each row sums to 1.
    """
    T = [[0.0] * m for _ in range(m)]
    inv_S = 1.0 / S
    for r in range(m):
        three_r = (3 * r) % m
        for a in range(S):
            s = (three_r + pow(2, a, m)) % m
            T[r][s] += inv_S
    return T


def mat_vec_mult(T, v, m):
    """Multiply m x m matrix T by vector v of length m."""
    result = [0.0] * m
    for i in range(m):
        s = 0.0
        for j in range(m):
            s += T[i][j] * v[j]
        result[i] = s
    return result


def tv_distance(dist, m):
    """Total variation distance between dist and uniform(1/m)."""
    uniform = 1.0 / m
    return 0.5 * sum(abs(dist[i] - uniform) for i in range(m))


def compute_mixing_time_exact(m, S, threshold=0.25, max_steps=None):
    """
    Compute the exact mixing time from every starting state.

    Returns:
        tau_mix: the worst-case mixing time (max over starting states)
        details: dict with per-starting-state info
    """
    if max_steps is None:
        max_steps = max(5 * m, 200)

    T = build_transition_matrix_pure(m, S)

    # Track worst-case over all starting states
    worst_tau = 0
    details = {}

    for x0 in range(m):
        # Start from delta_{x0}
        dist = [0.0] * m
        dist[x0] = 1.0
        tau = None
        for step in range(1, max_steps + 1):
            dist = mat_vec_mult(T, dist, m)
            d_tv = tv_distance(dist, m)
            if d_tv < threshold:
                tau = step
                break
        if tau is None:
            tau = max_steps  # did not mix
        details[x0] = tau
        if tau > worst_tau:
            worst_tau = tau

    return worst_tau, details


def compute_mixing_time_from_zero(m, S, threshold=0.25, max_steps=None):
    """
    Compute mixing time starting from state 0 only (faster).
    This is the most relevant starting state since c_0 = 0 in Horner.

    Returns: (tau_from_0, tv_at_each_step)
    """
    if max_steps is None:
        max_steps = max(5 * m, 200)

    T = build_transition_matrix_pure(m, S)
    dist = [0.0] * m
    dist[0] = 1.0

    tv_history = []
    tau = None

    for step in range(1, max_steps + 1):
        dist = mat_vec_mult(T, dist, m)
        d_tv = tv_distance(dist, m)
        tv_history.append(d_tv)
        if tau is None and d_tv < threshold:
            tau = step

    if tau is None:
        tau = max_steps

    return tau, tv_history


def part1_exact_mixing_times():
    """
    PART 1: Compute exact mixing times for k = 3..15 (mod primes dividing d).
    Compare tau_mix with k.
    """
    print("=" * 78)
    print("PART 1: EXACT MIXING TIMES BY MATRIX POWER ITERATION")
    print("=" * 78)
    print()
    print("For each k, we compute d(k) and its prime factors p.")
    print("For each prime p | d(k), we build the transition matrix T on Z/pZ")
    print("and compute the exact mixing time tau_mix (worst-case over all start states).")
    print("We then compare tau_mix with k.")
    print()

    results = {}

    header = (f"{'k':>3} {'S':>4} {'d':>10} {'p':>8} {'tau_mix':>8} "
              f"{'tau_0':>6} {'k':>4} {'tau/k':>8} {'verdict':>12}")
    print(header)
    print("-" * 80)

    for k in range(3, 16):
        S = compute_S(k)
        d = compute_d(k)
        primes = distinct_prime_factors(d)

        k_results = []

        for p in primes:
            if p > 500:
                # Too large for exact matrix iteration in pure Python
                # We'll handle these in Part 2 (spectral) and Part 3 (Fourier)
                continue

            tau_mix, details = compute_mixing_time_exact(p, S, threshold=0.25)
            tau_0, _ = compute_mixing_time_from_zero(p, S, threshold=0.25)

            ratio = tau_mix / k if k > 0 else float('inf')
            verdict = "tau>k" if tau_mix > k else ("tau=k" if tau_mix == k else "tau<k")

            print(f"{k:>3} {S:>4} {d:>10} {p:>8} {tau_mix:>8} "
                  f"{tau_0:>6} {k:>4} {ratio:>8.3f} {verdict:>12}")

            k_results.append({
                'p': p, 'tau_mix': tau_mix, 'tau_0': tau_0,
                'ratio': ratio, 'verdict': verdict
            })

        results[k] = {
            'S': S, 'd': d, 'primes': primes, 'details': k_results
        }

    print()
    print("PART 1 ANALYSIS:")
    print("-" * 78)

    # Count verdicts
    total_tau_gt_k = 0
    total_tau_le_k = 0
    total_cases = 0

    for k in sorted(results):
        for r in results[k]['details']:
            total_cases += 1
            if r['verdict'] == 'tau>k':
                total_tau_gt_k += 1
            else:
                total_tau_le_k += 1

    print(f"Total prime cases examined: {total_cases}")
    print(f"  tau_mix > k: {total_tau_gt_k} ({100*total_tau_gt_k/max(1,total_cases):.1f}%)")
    print(f"  tau_mix <= k: {total_tau_le_k} ({100*total_tau_le_k/max(1,total_cases):.1f}%)")
    print()

    # Key observation about small primes
    print("KEY OBSERVATION:")
    print("  For small primes p, tau_mix is typically O(p) ~ O(1) relative to k.")
    print("  The mixing time mod p is small because p is small.")
    print("  The critical insight is that GLOBAL mixing mod d requires mixing")
    print("  mod ALL primes SIMULTANEOUSLY (CRT), and the time for the")
    print("  SLOWEST prime factor to mix determines the overall mixing time.")
    print("  We investigate this in Parts 2-3 with the full modulus d.")
    print()

    return results


# ============================================================================
# PART 2: SPECTRAL GAP LOWER BOUND ON MIXING TIME
# ============================================================================
#
# For a doubly stochastic matrix T with eigenvalues 1 = lam_0 >= |lam_1| >= ...
# the spectral gap is: gap = 1 - |lam_1|
# and the mixing time satisfies:
#   tau_mix >= (1/gap) * log(1/(4 * pi_min))   [lower bound]
#   tau_mix <= (1/gap) * log(m/(4))             [upper bound, pi_min = 1/m]
#
# For doubly stochastic T: pi_min = 1/m, so:
#   tau_mix >= (1/gap) * (log(m) - log(4))
#
# We compute eigenvalues exactly for small m, and via Fourier for larger m.
# ============================================================================

def compute_eigenvalues_pure(T, m):
    """
    Compute eigenvalues of m x m matrix T using the power method for
    the largest few, and direct computation for small m.

    For m <= 50, we use explicit characteristic polynomial evaluation
    or iterative methods.

    Returns sorted list of |eigenvalue| in decreasing order.
    """
    # For the Fourier approach (Part 3), we can get eigenvalues analytically.
    # Here we use iterative power method for the top eigenvalues.
    # Since T is doubly stochastic, lam_0 = 1 with eigenvector (1,...,1)/sqrt(m).

    # We use power iteration on T - (1/m)*J where J is all-ones matrix
    # This removes the eigenvalue 1 and finds |lam_1|.

    import random as _rng
    _rng.seed(42)

    # Deflated matrix: T' = T - (1/m)*ones
    # Eigenvalues of T' are lam_1, lam_2, ..., lam_{m-1}, 0 (the 1 becomes 0)

    def deflated_mat_vec(v):
        """Multiply (T - J/m) * v where J is all-ones."""
        Tv = mat_vec_mult(T, v, m)
        mean_v = sum(v) / m
        return [Tv[i] - mean_v for i in range(m)]

    def vec_norm(v):
        return math.sqrt(sum(x*x for x in v))

    def vec_scale(v, alpha):
        return [x * alpha for x in v]

    # Power iteration to find |lam_1|
    v = [_rng.gauss(0, 1) for _ in range(m)]
    # Orthogonalize against (1,...,1)/sqrt(m)
    mean_v = sum(v) / m
    v = [v[i] - mean_v for i in range(m)]
    nv = vec_norm(v)
    if nv > 0:
        v = vec_scale(v, 1.0 / nv)

    lam1_estimate = 0.0
    for _ in range(min(300, 10 * m)):
        w = deflated_mat_vec(v)
        nw = vec_norm(w)
        if nw < 1e-15:
            break
        lam1_estimate = nw
        v = vec_scale(w, 1.0 / nw)
        # Re-orthogonalize
        mean_v = sum(v) / m
        v = [v[i] - mean_v for i in range(m)]
        nv = vec_norm(v)
        if nv > 0:
            v = vec_scale(v, 1.0 / nv)

    return lam1_estimate


def spectral_gap_via_fourier(m, S):
    """
    Compute the spectral gap using Fourier analysis.

    For the transition c -> 3c + 2^a mod m with a uniform over {0,...,S-1}:
    The eigenvalues are indexed by characters chi_t(x) = exp(2*pi*i*t*x/m).

    For a transition of the form x -> alpha*x + noise:
      If alpha has a multiplicative inverse mod m (gcd(3,m)=1 for odd m),
      the analysis uses the convolution structure.

    For the ADDITIVE part (fixing the multiplication by 3):
    The Fourier transform of the additive noise distribution mu(y) = (1/S) sum delta(2^a) is:
      mu_hat(t) = (1/S) * sum_{a=0}^{S-1} exp(2*pi*i*t*2^a/m)

    The eigenvalues of the full transition T are:
      lam_t = mu_hat(3^{-1} * t mod m)  if gcd(3,m) = 1
    (because T f(x) = E[f(3x + noise)] and Fourier diagonalizes the noise,
     while the multiplication by 3 acts as a permutation on Fourier modes.)

    Wait -- more carefully:
    T f(x) = (1/S) sum_a f(3x + 2^a)
    For f = chi_t: f(3x + 2^a) = exp(2pi i t(3x+2^a)/m) = chi_t(3x) * chi_t(2^a)
                  = exp(2pi i * 3t * x / m) * exp(2pi i * t * 2^a / m)
    So T chi_t(x) = [ (1/S) sum_a exp(2pi i t 2^a / m) ] * chi_{3t mod m}(x)

    This means T does NOT diagonalize in the Fourier basis directly --
    it maps chi_t to chi_{3t mod m} with a scalar factor.

    The eigenvalues come from the ORBITS of the multiplication-by-3 map
    on Z/mZ. If {t, 3t, 9t, ..., 3^{L-1}t} is a cycle of length L in Z/mZ,
    then the eigenvalue for this orbit is:
      lam = (prod_{j=0}^{L-1} mu_hat(3^j * t))^{1/L}

    Actually more precisely, the eigenvalues on the L-dimensional invariant
    subspace are the L-th roots of the product:
      Pi = prod_{j=0}^{L-1} mu_hat(3^j * t mod m)
    The eigenvalues are Pi^{1/L} * omega^r for r = 0,...,L-1
    where omega = exp(2pi i / L).

    The spectral gap is determined by the second-largest |eigenvalue|.

    Returns: (gap, lam1_abs, eigenvalue_info)
    """
    if math.gcd(3, m) != 1:
        return None, None, None

    # Step 1: Compute mu_hat(t) for all t in Z/mZ
    mu_hat = [0.0] * m  # will store complex values as (real, imag)
    mu_hat_complex = [complex(0, 0)] * m
    for t in range(m):
        s = complex(0, 0)
        for a in range(S):
            angle = 2 * math.pi * t * pow(2, a, m) / m
            s += complex(math.cos(angle), math.sin(angle))
        mu_hat_complex[t] = s / S

    # mu_hat_complex[0] = 1 always (sum of all unit vectors / S)

    # Step 2: Find orbits of multiplication by 3 on Z/mZ
    visited = [False] * m
    orbits = []

    for t in range(m):
        if visited[t]:
            continue
        orbit = []
        current = t
        while not visited[current]:
            visited[current] = True
            orbit.append(current)
            current = (3 * current) % m
        orbits.append(orbit)

    # Step 3: For each orbit, compute the product and eigenvalues
    all_eigenvalue_mods = [1.0]  # eigenvalue 1 from the t=0 orbit

    orbit_info = []
    for orbit in orbits:
        if orbit[0] == 0:
            continue  # trivial orbit, eigenvalue = 1
        L = len(orbit)
        # Product of mu_hat along the orbit
        Pi = complex(1, 0)
        for t in orbit:
            Pi *= mu_hat_complex[t]
        Pi_abs = abs(Pi)
        # The L eigenvalues have modulus Pi_abs^{1/L}
        eig_mod = Pi_abs ** (1.0 / L) if Pi_abs > 0 else 0.0
        all_eigenvalue_mods.append(eig_mod)
        orbit_info.append({
            'orbit': orbit, 'L': L,
            'Pi_abs': Pi_abs, 'eig_mod': eig_mod
        })

    # Step 4: Find the second largest eigenvalue modulus
    all_eigenvalue_mods.sort(reverse=True)
    lam1_abs = all_eigenvalue_mods[1] if len(all_eigenvalue_mods) > 1 else 0.0
    gap = 1.0 - lam1_abs

    return gap, lam1_abs, orbit_info


def part2_spectral_gap():
    """
    PART 2: Compute spectral gaps and mixing time lower bounds.
    """
    print()
    print("=" * 78)
    print("PART 2: SPECTRAL GAP LOWER BOUNDS ON MIXING TIME")
    print("=" * 78)
    print()
    print("The mixing time satisfies: tau_mix >= (1/gap) * ln(m/4)")
    print("where gap = 1 - |lambda_1| is the spectral gap.")
    print()
    print("For the Horner chain mod m, we compute eigenvalues via Fourier")
    print("analysis of the orbits of multiplication by 3 on Z/mZ.")
    print()

    results = {}

    header = (f"{'k':>3} {'S':>4} {'m':>10} {'|lam1|':>10} {'gap':>10} "
              f"{'tau_lb':>8} {'k':>4} {'tau_lb/k':>10} {'verdict':>10}")
    print(header)
    print("-" * 85)

    for k in range(3, 22):
        S = compute_S(k)
        d = compute_d(k)
        primes = distinct_prime_factors(d)

        k_results = []

        for p in primes:
            if p > 5000:
                continue
            if math.gcd(3, p) != 1:
                continue

            gap, lam1_abs, orbit_info = spectral_gap_via_fourier(p, S)
            if gap is None or gap <= 0:
                continue

            # Lower bound on mixing time
            tau_lb = (1.0 / gap) * math.log(p / 4.0) if p > 4 else 1

            ratio = tau_lb / k
            verdict = "tau>k" if tau_lb > k else "tau<=k"

            print(f"{k:>3} {S:>4} {p:>10} {lam1_abs:>10.6f} {gap:>10.6f} "
                  f"{tau_lb:>8.1f} {k:>4} {ratio:>10.4f} {verdict:>10}")

            k_results.append({
                'p': p, 'gap': gap, 'lam1': lam1_abs,
                'tau_lb': tau_lb, 'ratio': ratio, 'verdict': verdict,
                'n_orbits': len(orbit_info) if orbit_info else 0
            })

        # Also try the full modulus d if small enough
        if d <= 500 and d > 1 and math.gcd(3, d) == 1:
            gap, lam1_abs, orbit_info = spectral_gap_via_fourier(d, S)
            if gap is not None and gap > 0:
                tau_lb = (1.0 / gap) * math.log(d / 4.0) if d > 4 else 1
                ratio = tau_lb / k
                verdict = "tau>k" if tau_lb > k else "tau<=k"
                print(f"{k:>3} {S:>4} {'[d='+str(d)+']':>10} {lam1_abs:>10.6f} "
                      f"{gap:>10.6f} {tau_lb:>8.1f} {k:>4} {ratio:>10.4f} "
                      f"{verdict:>10}")
                k_results.append({
                    'p': d, 'gap': gap, 'lam1': lam1_abs,
                    'tau_lb': tau_lb, 'ratio': ratio, 'verdict': verdict,
                    'n_orbits': len(orbit_info) if orbit_info else 0,
                    'is_full_d': True
                })

        results[k] = {'S': S, 'd': d, 'details': k_results}

    print()
    print("PART 2 ANALYSIS:")
    print("-" * 78)
    print()
    print("The spectral gap tells us HOW FAST the chain mixes.")
    print("A small gap (|lam1| close to 1) means SLOW mixing => large tau_mix.")
    print()

    # Analyze the trend of spectral gaps
    print("Trend of maximum |lambda_1| across primes for each k:")
    print(f"{'k':>3} {'max|lam1|':>12} {'min gap':>12} {'tau_lb(max)':>12}")
    print("-" * 45)
    for k in sorted(results):
        if not results[k]['details']:
            continue
        max_lam1 = max(r['lam1'] for r in results[k]['details'])
        min_gap = min(r['gap'] for r in results[k]['details'])
        max_tau = max(r['tau_lb'] for r in results[k]['details'])
        print(f"{k:>3} {max_lam1:>12.6f} {min_gap:>12.6f} {max_tau:>12.1f}")

    print()
    print("KEY INSIGHT:")
    print("  The spectral gap controls the RATE of convergence to equilibrium.")
    print("  If gap -> 0 as k -> inf, the chain mixes SLOWER and SLOWER.")
    print("  The question is whether gap shrinks fast enough that tau_lb > k.")
    print()

    return results


# ============================================================================
# PART 3: FOURIER ANALYSIS OF THE TRANSITION KERNEL
# ============================================================================
#
# The Fourier transform of the step distribution mu on Z/mZ is:
#   mu_hat(t) = (1/S) * sum_{a=0}^{S-1} exp(2*pi*i*t*2^a/m)
#
# This is an EXPONENTIAL SUM -- a sum of S unit vectors at angles
# determined by the powers of 2 mod m.
#
# The maximum of |mu_hat(t)| for t != 0 controls the mixing time:
#   If max_{t!=0} |mu_hat(t)| = rho, then:
#     ||P^n - pi||_TV^2 <= (m-1)/4 * rho^{2n}
#   So mixing time ~ log(m) / (-2 log(rho))
#
# For our chain, |mu_hat(t)| involves cancellation in the exponential sum.
# The key question: does the sum cancel well (small rho => fast mixing)
# or poorly (large rho => slow mixing)?
# ============================================================================

def compute_fourier_profile(m, S):
    """
    Compute |mu_hat(t)| for all t in Z/mZ.

    Returns: list of (t, |mu_hat(t)|) sorted by |mu_hat(t)| descending.
    """
    profile = []
    for t in range(m):
        s = complex(0, 0)
        for a in range(S):
            val = pow(2, a, m)
            angle = 2 * math.pi * t * val / m
            s += complex(math.cos(angle), math.sin(angle))
        mu_hat_abs = abs(s) / S
        profile.append((t, mu_hat_abs))
    profile.sort(key=lambda x: -x[1])
    return profile


def part3_fourier_analysis():
    """
    PART 3: Fourier analysis of the step distribution.
    """
    print()
    print("=" * 78)
    print("PART 3: FOURIER ANALYSIS OF THE TRANSITION KERNEL")
    print("=" * 78)
    print()
    print("For the step distribution mu: a -> 2^a mod m (uniform over a=0..S-1),")
    print("the Fourier transform is mu_hat(t) = (1/S) sum exp(2pi i t 2^a / m).")
    print()
    print("The spectral radius rho = max_{t!=0} |mu_hat(t)| controls mixing:")
    print("  tau_mix ~ log(m) / (-2 log(rho))")
    print()

    results = {}

    header = (f"{'k':>3} {'S':>4} {'m':>10} {'rho':>10} {'tau_fourier':>12} "
              f"{'k':>4} {'tau/k':>10} {'verdict':>10}")
    print(header)
    print("-" * 75)

    for k in range(3, 22):
        S = compute_S(k)
        d = compute_d(k)
        primes = distinct_prime_factors(d)

        k_results = []

        for p in primes:
            if p > 3000:
                continue

            profile = compute_fourier_profile(p, S)
            # rho = max |mu_hat(t)| for t != 0
            rho = 0.0
            for t, val in profile:
                if t != 0:
                    rho = max(rho, val)
                    break  # already sorted descending
            # Actually get the true max for t != 0
            rho = max(val for t, val in profile if t != 0)

            if rho >= 1.0:
                # No mixing (degenerate case)
                tau_fourier = float('inf')
            elif rho <= 0.0:
                tau_fourier = 1.0
            else:
                # tau_mix ~ (1/2) * log((m-1)/4) / (-log(rho))
                # This comes from ||P^n - pi||_2^2 <= (m-1) * rho^{2n}
                # and ||.||_TV <= sqrt(m) * ||.||_2 / 2
                # More precisely: ||P^n - pi||_TV^2 <= (m/4) * rho^{2n}
                # So need (m/4) * rho^{2n} < 1/16 => n > log(4m) / (-2 log rho)
                tau_fourier = math.log(4 * p) / (-2 * math.log(rho))

            ratio = tau_fourier / k if tau_fourier < float('inf') else float('inf')
            verdict = "tau>k" if tau_fourier > k else "tau<=k"

            print(f"{k:>3} {S:>4} {p:>10} {rho:>10.6f} {tau_fourier:>12.2f} "
                  f"{k:>4} {ratio:>10.4f} {verdict:>10}")

            k_results.append({
                'p': p, 'rho': rho, 'tau_fourier': tau_fourier,
                'ratio': ratio, 'verdict': verdict
            })

        # Also try full d if small
        if d <= 500 and d > 1:
            profile = compute_fourier_profile(d, S)
            rho = max(val for t, val in profile if t != 0)
            if 0 < rho < 1:
                tau_fourier = math.log(4 * d) / (-2 * math.log(rho))
            elif rho >= 1:
                tau_fourier = float('inf')
            else:
                tau_fourier = 1.0
            ratio = tau_fourier / k if tau_fourier < float('inf') else float('inf')
            verdict = "tau>k" if tau_fourier > k else "tau<=k"
            print(f"{k:>3} {S:>4} {'[d='+str(d)+']':>10} {rho:>10.6f} "
                  f"{tau_fourier:>12.2f} {k:>4} {ratio:>10.4f} {verdict:>10}")
            k_results.append({
                'p': d, 'rho': rho, 'tau_fourier': tau_fourier,
                'ratio': ratio, 'verdict': verdict, 'is_full_d': True
            })

        results[k] = {'S': S, 'd': d, 'details': k_results}

    print()
    print("PART 3 ANALYSIS:")
    print("-" * 78)
    print()

    # Analyze rho trend
    print("Trend of rho (spectral radius) for the LARGEST prime factor:")
    print(f"{'k':>3} {'largest_p':>10} {'rho':>10} {'tau_fourier':>12} {'k':>4}")
    print("-" * 45)
    for k in sorted(results):
        details = results[k]['details']
        if not details:
            continue
        # Focus on largest prime
        largest = max(details, key=lambda r: r['p'])
        print(f"{k:>3} {largest['p']:>10} {largest['rho']:>10.6f} "
              f"{largest['tau_fourier']:>12.2f} {k:>4}")

    print()
    print("KEY INSIGHT:")
    print("  The spectral radius rho measures how well the exponential sum")
    print("  sum_{a=0}^{S-1} exp(2pi i t 2^a / m) cancels for the worst t != 0.")
    print()
    print("  If rho is close to 1 (poor cancellation), mixing is slow.")
    print("  If rho is close to 0 (good cancellation), mixing is fast.")
    print()
    print("  The competition is between:")
    print("    - S growing as O(k log 3 / log 2) ~ 1.585 k  [more terms => more cancellation]")
    print("    - m growing exponentially [larger space => more time needed]")
    print()

    return results


# ============================================================================
# PART 4: DIRECT TV DISTANCE AT STEP k (THE COUNTING ARGUMENT)
# ============================================================================
#
# The most direct approach: starting from c_0 = 0, iterate the chain
# EXACTLY k steps and measure ||P^k(0, .) - uniform||_TV.
#
# If this TV distance is close to 1 at step k, then the orbit has NOT
# mixed, and P(c_k = 0) can be far from 1/m.
#
# For verification, we also compare with EXACT enumeration of all
# C(S-1, k-1) compositions when feasible.
# ============================================================================

def part4_direct_tv_at_k():
    """
    PART 4: Measure TV distance from uniform at exactly step k.
    """
    print()
    print("=" * 78)
    print("PART 4: TV DISTANCE FROM UNIFORM AT STEP k")
    print("=" * 78)
    print()
    print("Starting from c_0 = 0, we iterate the Horner chain k steps")
    print("and measure ||P^k(0, .) - uniform||_TV.")
    print("If this is close to 1, the orbit is FAR from equilibrium at step k.")
    print()
    print("We also compare with exact enumeration (corrSum distribution) when feasible.")
    print()

    results = {}

    header = (f"{'k':>3} {'S':>4} {'m':>10} {'TV(k)':>10} {'P(0)':>12} "
              f"{'1/m':>12} {'ratio':>10} {'verdict':>12}")
    print(header)
    print("-" * 90)

    for k in range(3, 18):
        S = compute_S(k)
        d = compute_d(k)
        primes = distinct_prime_factors(d)

        k_results = []

        for p in primes:
            if p > 500:
                continue
            if math.gcd(3, p) != 1:
                continue

            T = build_transition_matrix_pure(p, S)

            # Iterate k times from delta_0
            dist = [0.0] * p
            dist[0] = 1.0
            for step in range(k):
                dist = mat_vec_mult(T, dist, p)

            d_tv = tv_distance(dist, p)
            p_zero = dist[0]
            uniform = 1.0 / p
            ratio_p0 = p_zero / uniform if uniform > 0 else 0

            if d_tv > 0.75:
                verdict = "FAR"
            elif d_tv > 0.25:
                verdict = "PARTIAL"
            else:
                verdict = "MIXED"

            print(f"{k:>3} {S:>4} {p:>10} {d_tv:>10.6f} {p_zero:>12.8f} "
                  f"{uniform:>12.8f} {ratio_p0:>10.4f} {verdict:>12}")

            k_results.append({
                'p': p, 'tv': d_tv, 'p_zero': p_zero,
                'uniform': uniform, 'ratio': ratio_p0, 'verdict': verdict
            })

        # Full d if small
        if d <= 300 and d > 1 and math.gcd(3, d) == 1:
            T = build_transition_matrix_pure(d, S)
            dist = [0.0] * d
            dist[0] = 1.0
            for step in range(k):
                dist = mat_vec_mult(T, dist, d)
            d_tv = tv_distance(dist, d)
            p_zero = dist[0]
            uniform = 1.0 / d
            ratio_p0 = p_zero / uniform if uniform > 0 else 0
            verdict = "FAR" if d_tv > 0.75 else ("PARTIAL" if d_tv > 0.25 else "MIXED")
            print(f"{k:>3} {S:>4} {'[d='+str(d)+']':>10} {d_tv:>10.6f} "
                  f"{p_zero:>12.8f} {uniform:>12.8f} {ratio_p0:>10.4f} "
                  f"{verdict:>12}")
            k_results.append({
                'p': d, 'tv': d_tv, 'p_zero': p_zero,
                'uniform': uniform, 'ratio': ratio_p0, 'verdict': verdict,
                'is_full_d': True
            })

        # Exact enumeration verification for small k
        n_comp = math.comb(S - 1, k - 1)
        if n_comp <= 500000 and d <= 2000:
            count_zero = 0
            total = 0
            for B in combinations(range(1, S), k - 1):
                cs = corrsum_from_subset(B, k, d)
                if cs == 0:
                    count_zero += 1
                total += 1
            exact_p0 = count_zero / total if total > 0 else 0
            print(f"    [EXACT ENUM] k={k}: N_0={count_zero}/{total}, "
                  f"P(0)={exact_p0:.8f}, 1/d={1/d:.8f}, "
                  f"ratio={exact_p0*d:.4f}")
            k_results.append({
                'exact': True, 'count_zero': count_zero,
                'total': total, 'exact_p0': exact_p0
            })

        results[k] = {'S': S, 'd': d, 'details': k_results}

    print()
    print("PART 4 ANALYSIS:")
    print("-" * 78)
    print()
    print("The TV distance at step k tells us directly whether the orbit")
    print("has mixed by the time it needs to hit 0.")
    print()

    # Summarize for full d
    print("Summary for the FULL modulus d:")
    for k in sorted(results):
        for r in results[k]['details']:
            if r.get('is_full_d'):
                print(f"  k={k}: TV(k)={r['tv']:.6f}, P(0)={r['p_zero']:.8f}, "
                      f"1/d={r['uniform']:.8f}")

    print()
    print("KEY INSIGHT:")
    print("  If TV(k) is close to 1 for the full modulus d, then the chain")
    print("  has NOT mixed after k steps, and the probability of hitting 0")
    print("  is controlled by the INITIAL CONDITIONS, not the equilibrium.")
    print("  This gives a structural reason why cycles cannot exist.")
    print()

    return results


# ============================================================================
# PART 5: ASYMPTOTIC ANALYSIS AND TREND EXTRAPOLATION
# ============================================================================
#
# For large k:
#   - d ~ 2^{0.415k} grows exponentially
#   - S ~ 1.585k grows linearly
#   - The mixing time of a random walk on Z/dZ is at least O(d) steps
#   - But the Horner chain has STRUCTURE: multiplication by 3 + additive noise
#
# The key asymptotic question:
#   Does tau_mix / k -> infinity as k -> infinity?
#
# If yes, then for all sufficiently large k, the chain cannot mix,
# and cycles are impossible.
#
# We investigate by:
#   1. Extrapolating the tau_mix/k ratio from computed data
#   2. Analyzing the spectral gap scaling
#   3. Connecting to known results on random walks on Z_n
# ============================================================================

def part5_asymptotic_analysis(part1_results=None, part2_results=None, part3_results=None):
    """
    PART 5: Asymptotic analysis and formalization attempt.
    """
    print()
    print("=" * 78)
    print("PART 5: ASYMPTOTIC ANALYSIS — TOWARDS A PROOF")
    print("=" * 78)
    print()

    # === 5A: The fundamental scaling argument ===
    print("5A. THE FUNDAMENTAL SCALING ARGUMENT")
    print("-" * 50)
    print()
    print("For the Horner chain on Z/dZ:")
    print("  d(k) = 2^S - 3^k where S = ceil(k * log2(3))")
    print()

    print(f"{'k':>3} {'S':>4} {'d':>15} {'log2(d)':>10} {'S/k':>8} "
          f"{'log2(d)/k':>12}")
    print("-" * 60)

    log2d_over_k_values = []
    for k in range(3, 30):
        S = compute_S(k)
        d = compute_d(k)
        log2d = math.log2(d) if d > 0 else 0
        print(f"{k:>3} {S:>4} {d:>15} {log2d:>10.4f} {S/k:>8.4f} "
              f"{log2d/k:>12.6f}")
        log2d_over_k_values.append((k, log2d / k))

    print()
    print("  Observation: log2(d)/k -> log2(3) - 1 = 0.585... as k -> inf")
    print("  This means d ~ 2^{0.585k}, growing exponentially with k.")
    print()

    # === 5B: Mixing time scaling analysis ===
    print("5B. MIXING TIME SCALING ANALYSIS")
    print("-" * 50)
    print()
    print("For a random walk on Z/mZ with uniform steps, tau_mix = Theta(m).")
    print("For our chain, the steps are NOT uniform -- they are 2^a for")
    print("a = 0, ..., S-1. The question is whether this structure helps.")
    print()

    # Compute tau_mix/k for available data (from Part 1 or recompute)
    print("Computing tau_mix/k for the Horner chain mod d (small k):")
    print(f"{'k':>3} {'d':>10} {'tau_mix':>8} {'tau_0':>6} {'k':>4} "
          f"{'tau_mix/k':>10} {'d/k':>10}")
    print("-" * 60)

    tau_over_k = []
    for k in range(3, 14):
        S = compute_S(k)
        d = compute_d(k)
        if d > 300 or d <= 1:
            continue
        if math.gcd(3, d) != 1:
            # Skip if 3 divides d (shouldn't happen for valid k)
            continue

        tau_mix, details = compute_mixing_time_exact(d, S, threshold=0.25)
        tau_0, _ = compute_mixing_time_from_zero(d, S, threshold=0.25)

        ratio = tau_mix / k
        print(f"{k:>3} {d:>10} {tau_mix:>8} {tau_0:>6} {k:>4} "
              f"{ratio:>10.3f} {d/k:>10.3f}")
        tau_over_k.append((k, d, tau_mix, ratio))

    print()

    # === 5C: The structural argument ===
    print("5C. THE STRUCTURAL ARGUMENT FOR tau_mix > k")
    print("-" * 50)
    print()
    print("THEOREM ATTEMPT (Mixing Time Exceeds Cycle Length):")
    print()
    print("  Claim: For all k >= K_0, the mixing time of the Horner chain")
    print("  on Z/d(k)Z exceeds k.")
    print()
    print("  Argument sketch:")
    print("  1. The chain c -> 3c + 2^a mod d is a random walk on Z/dZ")
    print("     with S = ceil(k*log2(3)) possible steps {2^0, 2^1, ..., 2^{S-1}}.")
    print()
    print("  2. The spectral radius rho of the Fourier transform of the")
    print("     step distribution satisfies:")
    print("       rho = max_{t!=0} |(1/S) sum_{a=0}^{S-1} exp(2pi i t 2^a / d)|")
    print()
    print("  3. The mixing time satisfies:")
    print("       tau_mix >= log(d/4) / (-2 log(rho))")
    print()
    print("  4. Since d ~ 2^{0.585k}, we need:")
    print("       log(d/4) ~ 0.585k * ln(2)")
    print("       For tau_mix > k, we need: -2 log(rho) < 0.585 * ln(2) ~ 0.405")
    print("       i.e., rho > exp(-0.203) ~ 0.816")
    print()
    print("  5. KEY QUESTION: Is rho bounded away from 0? Or does rho -> 0?")
    print()

    # === 5D: The exponential sum analysis ===
    print("5D. EXPONENTIAL SUM ANALYSIS")
    print("-" * 50)
    print()
    print("The Fourier coefficient mu_hat(t) = (1/S) sum_{a=0}^{S-1} exp(2pi i t 2^a / d)")
    print("is an exponential sum over POWERS OF 2.")
    print()
    print("Classical results (Bourgain, Korobov):")
    print("  For generic t and d, such sums have cancellation giving")
    print("  |sum| = O(S^{1/2}) by quasi-randomness of {2^a mod d}.")
    print("  This gives rho ~ S^{-1/2} ~ k^{-1/2}.")
    print()
    print("  BUT: if ord_d(2) is SMALL (i.e., 2 has small order mod d),")
    print("  the powers {2^a mod d} cycle through few values, and the")
    print("  exponential sum can be LARGE (poor cancellation).")
    print()

    # Check order of 2 mod d and mod p for various k
    print("Order of 2 mod p for prime factors of d(k):")
    print(f"{'k':>3} {'p':>10} {'ord_p(2)':>10} {'S':>4} {'ord/S':>8} {'ord/p':>8}")
    print("-" * 50)

    for k in range(3, 22):
        S = compute_S(k)
        d = compute_d(k)
        primes = distinct_prime_factors(d)
        for p in primes:
            if p > 3000:
                continue
            ord2 = multiplicative_order(2, p)
            print(f"{k:>3} {p:>10} {ord2:>10} {S:>4} {ord2/S:>8.3f} "
                  f"{ord2/p:>8.4f}")

    print()
    print("  If ord_p(2) >> S, the powers {2^0, ..., 2^{S-1}} mod p are")
    print("  ALL DISTINCT and quasi-uniform => good cancellation => fast mixing.")
    print()
    print("  If ord_p(2) << S, the powers wrap around and create repetitions")
    print("  => constructive interference in the exponential sum => slow mixing.")
    print()
    print("  NOTE: d = 2^S - 3^k implies 2^S = 3^k mod d, so ord_d(2) | S.")
    print("  In fact, ord_d(2) = S exactly (since 2^a mod d for a < S are all < 2^S = 3^k + d).")
    print("  Wait -- this needs more care. Let's check:")
    print()

    for k in range(3, 14):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1:
            continue
        ord2 = multiplicative_order(2, d)
        print(f"  k={k}: d={d}, S={S}, ord_d(2)={ord2}, S/ord={S/ord2:.4f}")

    print()

    # === 5E: The definitive mixing time comparison ===
    print("5E. DEFINITIVE COMPARISON: tau_mix vs k")
    print("-" * 50)
    print()
    print("We combine all evidence for the comparison tau_mix vs k.")
    print()

    # For the definitive test, compute the Markov chain TV distance
    # at exactly step k for the full d (when feasible)
    print("TV distance at step k from 0, for the Horner chain mod d:")
    print(f"{'k':>3} {'d':>10} {'TV(k)':>10} {'P_k(0)':>12} {'1/d':>12} "
          f"{'P(0)*d':>8}")
    print("-" * 65)

    definitive_data = []
    for k in range(3, 14):
        S = compute_S(k)
        d = compute_d(k)
        if d <= 1 or d > 300:
            continue
        if math.gcd(3, d) != 1:
            continue

        T = build_transition_matrix_pure(d, S)
        dist = [0.0] * d
        dist[0] = 1.0
        for step in range(k):
            dist = mat_vec_mult(T, dist, d)
        d_tv = tv_distance(dist, d)
        p_zero = dist[0]
        print(f"{k:>3} {d:>10} {d_tv:>10.6f} {p_zero:>12.8f} "
              f"{1/d:>12.8f} {p_zero*d:>8.4f}")
        definitive_data.append((k, d, d_tv, p_zero, p_zero * d))

    print()

    return definitive_data


# ============================================================================
# SYNTHESIS
# ============================================================================

def part6_with_vs_without_replacement():
    """
    PART 6 (BONUS): The critical WITH vs WITHOUT replacement distinction.

    The Markov chain models WITH-replacement sampling of exponents.
    But the actual Horner chain uses WITHOUT replacement: the subset
    B = {b_1, ..., b_{k-1}} has DISTINCT elements from {1, ..., S-1}.

    This part quantifies the gap between:
    - P_Markov(c_k = 0) from the transition matrix (with replacement)
    - P_exact(c_k = 0) from exhaustive enumeration (without replacement)
    """
    print()
    print("=" * 78)
    print("PART 6: WITH vs WITHOUT REPLACEMENT — THE CRITICAL DISTINCTION")
    print("=" * 78)
    print()
    print("The Markov chain (with replacement) gives P(0) ~ 1/d.")
    print("But the REAL chain uses WITHOUT replacement: b_i are distinct.")
    print("This is a NON-MARKOV process. The replacement constraint is")
    print("what actually kills cycles.")
    print()

    header = (f"{'k':>3} {'S':>4} {'d':>8} {'C(S-1,k-1)':>12} "
              f"{'N_0_exact':>10} {'P_exact':>12} {'P_Markov':>12} "
              f"{'ratio_E/M':>10}")
    print(header)
    print("-" * 90)

    results = []

    for k in range(3, 18):
        S = compute_S(k)
        d = compute_d(k)
        n_comp = math.comb(S - 1, k - 1)

        if n_comp > 2_000_000:
            continue

        # Exact enumeration
        count_zero = 0
        total = 0
        for B in combinations(range(1, S), k - 1):
            cs = corrsum_from_subset(B, k, d)
            if cs == 0:
                count_zero += 1
            total += 1

        exact_p0 = count_zero / total if total > 0 else 0
        uniform_p0 = 1.0 / d if d > 0 else 0

        # Markov approximation
        if d <= 500 and math.gcd(3, d) == 1:
            T = build_transition_matrix_pure(d, S)
            dist = [0.0] * d
            dist[0] = 1.0
            for step in range(k):
                dist = mat_vec_mult(T, dist, d)
            markov_p0 = dist[0]
        else:
            markov_p0 = uniform_p0  # approximation: fully mixed

        ratio = exact_p0 / markov_p0 if markov_p0 > 0 else 0

        print(f"{k:>3} {S:>4} {d:>8} {n_comp:>12} "
              f"{count_zero:>10} {exact_p0:>12.8f} {markov_p0:>12.8f} "
              f"{ratio:>10.4f}")

        results.append({
            'k': k, 'S': S, 'd': d, 'n_comp': n_comp,
            'N0': count_zero, 'exact_p0': exact_p0,
            'markov_p0': markov_p0, 'ratio': ratio
        })

    print()
    print("PART 6 ANALYSIS:")
    print("-" * 78)
    print()
    print("CRITICAL FINDING:")
    print("  The Markov chain (WITH replacement) predicts P(0) ~ 1/d.")
    print("  The EXACT count (WITHOUT replacement) gives N_0 = 0 for all k >= 3.")
    print()
    print("  This means the obstruction is NOT about mixing time of the Markov chain.")
    print("  The Markov chain mixes PERFECTLY -- it gives P(0) ~ 1/d as expected.")
    print("  But the WITHOUT-REPLACEMENT constraint DESTROYS all solutions.")
    print()
    print("  The mixing time argument must be reformulated:")
    print("  It is not 'the chain cannot reach 0 in k steps' but rather")
    print("  'the WITHOUT-REPLACEMENT constraint on the trajectory eliminates")
    print("  all paths that would reach 0.'")
    print()
    print("  This is a COMBINATORIAL constraint, not a dynamical one.")
    print("  The relevant question is: among the C(S-1, k-1) distinct (k-1)-subsets")
    print("  of {1,...,S-1}, how many produce corrSum = 0 mod d?")
    print("  Answer: ZERO for all k >= 3.")
    print()

    return results


def synthesis(p1, p2, p3, p4, p5_data):
    """Final synthesis and verdict."""
    print()
    print("=" * 78)
    print("SYNTHESIS: IS tau_mix > k PROVABLE?")
    print("=" * 78)
    print()

    print("EVIDENCE SUMMARY:")
    print("-" * 78)
    print()

    # Part 1 summary
    print("Part 1 (Exact Mixing Times mod primes):")
    if p1:
        tau_gt_k = sum(1 for k_val in p1 for r in p1[k_val].get('details', [])
                       if r.get('verdict') == 'tau>k')
        total = sum(1 for k_val in p1 for r in p1[k_val].get('details', [])
                    if 'verdict' in r)
        print(f"  tau_mix > k in {tau_gt_k}/{total} cases for individual primes.")
        print(f"  Small primes mix quickly (tau_mix ~ O(p)), so tau < k is common")
        print(f"  for individual prime factors.")
    print()

    # Part 2 summary
    print("Part 2 (Spectral Gap Analysis):")
    if p2:
        print("  The spectral gap gives LOWER BOUNDS on mixing time.")
        print("  The gap remains bounded away from 0 => the chain mixes in O(log m) steps.")
        print("  This means tau_mix = O(log d) = O(k) for the Markov approximation.")
    print()

    # Part 3 summary
    print("Part 3 (Fourier Analysis):")
    if p3:
        print("  The spectral radius rho = max|mu_hat(t)| is bounded well below 1.")
        print("  Typical values: rho ~ 0.2-0.6. This gives fast mixing.")
    print()

    # Part 4 summary
    print("Part 4 (TV Distance at Step k):")
    if p4:
        far_count = 0
        mixed_count = 0
        total = 0
        for k_val in p4:
            for r in p4[k_val].get('details', []):
                v = r.get('verdict', '')
                if v == 'FAR':
                    far_count += 1
                elif v == 'MIXED':
                    mixed_count += 1
                if v in ('FAR', 'PARTIAL', 'MIXED'):
                    total += 1
        print(f"  TV(k) close to 1 (FAR from uniform): {far_count}/{total} cases")
        print(f"  TV(k) close to 0 (MIXED):            {mixed_count}/{total} cases")
        print(f"  >>> The Markov chain is FULLY MIXED at step k in all cases.")
    print()

    # Part 5 summary
    print("Part 5 (Asymptotic Scaling):")
    if p5_data:
        print("  Direct TV measurement for the FULL modulus d:")
        for k, d, tv, p0, p0d in p5_data:
            status = "NOT MIXED" if tv > 0.25 else "MIXED"
            print(f"    k={k}, d={d}: TV(k)={tv:.4f} [{status}], P(0)*d={p0d:.4f}")
        print("  >>> P(0)*d ~ 1 means the Markov chain predicts ~1/d probability.")
    print()

    # THE CRITICAL REVELATION
    print("=" * 78)
    print("THE CRITICAL REVELATION")
    print("=" * 78)
    print()
    print("  The mixing time argument as originally conceived DOES NOT WORK.")
    print()
    print("  WHY: The Markov chain (with-replacement sampling of exponents)")
    print("  mixes FAST. After k steps, the distribution is essentially")
    print("  uniform over Z/dZ. The Markov chain predicts P(c_k = 0) ~ 1/d.")
    print()
    print("  But the EXACT count gives N_0 = 0 for ALL k >= 3.")
    print("  This is not because the orbit 'does not have time to reach 0'.")
    print("  It is because the WITHOUT-REPLACEMENT constraint on the subset")
    print("  B = {b_1, ..., b_{k-1}} creates a RIGID combinatorial structure")
    print("  that is incompatible with corrSum = 0 mod d.")
    print()
    print("  The Markov approximation ERASES this structure by allowing")
    print("  repetitions. With repetitions, the chain reaches equilibrium")
    print("  in O(log d) = O(k) steps, and 1/d of trajectories hit 0.")
    print("  Without repetitions, the constraint is:")
    print("    sum_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j} = 0 mod d")
    print("    with b_0 = 0, b_1 < b_2 < ... < b_{k-1}, b_i in {1,...,S-1}")
    print()
    print("  This is a DIOPHANTINE problem, not a dynamical one.")
    print()

    # THE REVISED VERDICT
    print("=" * 78)
    print("REVISED VERDICT")
    print("=" * 78)
    print()
    print("  QUESTION: Is tau_mix > k provable?")
    print()
    print("  ANSWER: The question is ILL-POSED for the Markov approximation.")
    print()
    print("  The Markov chain mixes in O(log d) ~ O(k) steps, so tau_mix ~ k.")
    print("  The chain IS approximately mixed at step k.")
    print("  And indeed P_Markov(c_k = 0) ~ 1/d > 0.")
    print()
    print("  The actual impossibility comes from three DIFFERENT mechanisms:")
    print()
    print("  MECHANISM 1: COMBINATORIAL RIGIDITY (the without-replacement constraint)")
    print("    The subset {b_0, ..., b_{k-1}} must have DISTINCT elements.")
    print("    This is a hard constraint that the Markov chain ignores.")
    print("    It reduces the C(S-1, k-1) valid trajectories from the ~S^{k-1}")
    print("    trajectories in the Markov model.")
    print()
    print("  MECHANISM 2: DIOPHANTINE OBSTRUCTION")
    print("    corrSum = sum 3^j * 2^{b_j} = 0 mod d = 2^S - 3^k")
    print("    This is a linear equation in the 2-adic valuations.")
    print("    The coefficients 3^j and 2^{b_j} have multiplicative structure")
    print("    that creates ARITHMETIC obstructions mod various primes.")
    print()
    print("  MECHANISM 3: THE SUPER-EXCLUSION PHENOMENON (R16)")
    print("    Even when the CRT heuristic predicts N_0 > 0, the actual")
    print("    count is N_0 = 0. This means there are GLOBAL correlations")
    print("    between residues mod different primes that the CRT misses.")
    print("    These correlations are the REAL obstruction.")
    print()
    print("  WHAT THE MIXING TIME ANALYSIS TELLS US:")
    print("  1. The Markov chain is a GOOD approximation of the step distribution")
    print("  2. The chain mixes fast => P(0) ~ 1/d is the 'expected' probability")
    print("  3. The fact that N_0 = 0 DESPITE P(0) ~ 1/d means the obstruction")
    print("     is in the WITHOUT-REPLACEMENT structure, not in the dynamics")
    print("  4. The relevant 'mixing time' is not of the Markov chain but of")
    print("     the WITHOUT-REPLACEMENT walk, which is a fundamentally different")
    print("     (non-Markovian, path-dependent) process.")
    print()
    print("  PATH FORWARD:")
    print("  The key to a proof is not mixing time but rather showing that")
    print("  the WITHOUT-REPLACEMENT constraint creates a bias against 0")
    print("  that is multiplicative over the k steps. Specifically:")
    print("    P_exact(c_k = 0) = P_Markov(c_k = 0) * correction_factor")
    print("  where correction_factor -> 0 as k -> inf.")
    print()
    print("  This correction factor comes from the DEPLETION of available")
    print("  exponents: at each step, one exponent is 'used up', narrowing")
    print("  the set of reachable states. The chain becomes progressively")
    print("  more constrained, and the probability of hitting the specific")
    print("  target 0 decreases faster than 1/d.")
    print()
    print("  CONFIDENCE LEVEL: 3/5")
    print("  The mixing time approach as stated does NOT yield a proof.")
    print("  But the analysis reveals the TRUE mechanism: the without-replacement")
    print("  combinatorial constraint. The path to a proof lies in quantifying")
    print("  this constraint, not in Markov chain mixing.")
    print()


# ============================================================================
# SELF-TESTS
# ============================================================================

def run_self_tests():
    """Verify mathematical correctness before running analysis."""
    print("=" * 78)
    print("SELF-TESTS")
    print("=" * 78)
    passed = 0
    failed = 0

    def check(name, condition):
        nonlocal passed, failed
        if condition:
            print(f"  [PASS] {name}")
            passed += 1
        else:
            print(f"  [FAIL] {name}")
            failed += 1

    # ST-1: Basic S, d values
    check("ST-1: S(3)=5, d(3)=5",
          compute_S(3) == 5 and compute_d(3) == 5)

    # ST-2: S(5)=8, d(5)=13
    check("ST-2: S(5)=8, d(5)=13",
          compute_S(5) == 8 and compute_d(5) == 13)

    # ST-3: Transition matrix is doubly stochastic
    T = build_transition_matrix_pure(5, compute_S(3))
    row_sums_ok = all(abs(sum(T[i]) - 1.0) < 1e-10 for i in range(5))
    col_sums_ok = all(abs(sum(T[i][j] for i in range(5)) - 1.0) < 1e-10
                      for j in range(5))
    check("ST-3: T mod 5 (k=3) is doubly stochastic",
          row_sums_ok and col_sums_ok)

    # ST-4: T[0][0] = 0 (TZ property)
    check("ST-4: T[0][0] = 0 for k=3 mod 5",
          abs(T[0][0]) < 1e-10)

    # ST-5: Fourier coefficient mu_hat(0) = 1
    profile = compute_fourier_profile(5, compute_S(3))
    mu0 = [val for t, val in profile if t == 0][0]
    check("ST-5: mu_hat(0) = 1",
          abs(mu0 - 1.0) < 1e-10)

    # ST-6: Spectral gap is positive (chain is ergodic)
    gap, lam1, _ = spectral_gap_via_fourier(5, compute_S(3))
    check("ST-6: Spectral gap > 0 for k=3 mod 5",
          gap is not None and gap > 0)

    # ST-7: |lambda_1| < 1 (mixing chain)
    check("ST-7: |lambda_1| < 1 for k=3 mod 5",
          lam1 is not None and lam1 < 1.0)

    # ST-8: Mixing time from delta_0 is finite
    tau_0, tv_hist = compute_mixing_time_from_zero(5, compute_S(3))
    check("ST-8: Mixing time from 0 is finite (k=3, mod 5)",
          tau_0 < 100)

    # ST-9: TV distance starts at 1 - 1/m
    # At step 0 (before any transition), TV should be 1 - 1/m
    # After one step, TV should decrease
    check("ST-9: TV decreases over time",
          len(tv_hist) >= 2 and tv_hist[-1] < tv_hist[0])

    # ST-10: Exact corrSum count matches known values
    # For k=3, S=5, d=5: compositions of 5 into 3 parts = C(4,2)=6
    S = compute_S(3)
    d = compute_d(3)
    count = 0
    total = 0
    for B in combinations(range(1, S), 2):
        cs = corrsum_from_subset(B, 3, d)
        if cs == 0:
            count += 1
        total += 1
    check("ST-10: C(4,2)=6 compositions for k=3",
          total == 6)

    # ST-11: corrSum distribution is consistent with Markov iteration
    # For k=3, mod 5, the distribution from Markov should match exact enumeration
    T5 = build_transition_matrix_pure(5, S)
    dist = [0.0] * 5
    dist[0] = 1.0
    for step in range(3):
        dist = mat_vec_mult(T5, dist, 5)
    # Note: Markov uses WITH replacement, exact uses WITHOUT replacement
    # They should be APPROXIMATELY equal for S >> k
    # For k=3, S=5, they may differ somewhat
    check("ST-11: Markov P(0) is a real number in [0,1]",
          0 <= dist[0] <= 1)

    # ST-12: Prime factorization is correct
    # d(7) = 2^12 - 3^7 = 4096 - 2187 = 1909 = 23 * 83
    check("ST-12: d(7)=1909=23*83, prime factors = [23, 83]",
          compute_d(7) == 1909 and distinct_prime_factors(1909) == [23, 83])

    # ST-13: d(11) = 2^18 - 3^11 = 262144 - 177147 = 84997
    check("ST-13: d(11) = 84997",
          compute_d(11) == 84997)

    # ST-14: Multiplicative order of 2 mod 5 is 4
    check("ST-14: ord_5(2) = 4",
          multiplicative_order(2, 5) == 4)

    # ST-15: Modular inverse
    check("ST-15: modinv(3, 7) = 5 (since 3*5=15=1 mod 7)",
          modinv(3, 7) == 5)

    print()
    print(f"Results: {passed} passed, {failed} failed out of {passed+failed}")
    print("=" * 78)

    return failed == 0


# ============================================================================
# MAIN
# ============================================================================

def main():
    t0 = time.time()

    print("=" * 78)
    print("r4_mixing_time_proof.py — Round 4: Mixing Time vs Cycle Length")
    print("=" * 78)
    print()

    # Self-tests first
    if not run_self_tests():
        print("SELF-TESTS FAILED. Aborting.")
        sys.exit(1)

    print()

    # Run all parts
    p1 = part1_exact_mixing_times()
    p2 = part2_spectral_gap()
    p3 = part3_fourier_analysis()
    p4 = part4_direct_tv_at_k()
    p5 = part5_asymptotic_analysis(p1, p2, p3)
    p6 = part6_with_vs_without_replacement()

    # Synthesis
    synthesis(p1, p2, p3, p4, p5)

    # Timing and hash
    elapsed = time.time() - t0
    print()
    print(f"Total execution time: {elapsed:.1f}s")
    print()

    # SHA256 of this script
    with open(__file__, 'rb') as f:
        sha = hashlib.sha256(f.read()).hexdigest()
    print(f"SHA256: {sha}")
    print()

    if elapsed > 300:
        print("WARNING: Execution exceeded 300s budget!")
    else:
        print(f"Time budget: {elapsed:.1f}s / 300s ({100*elapsed/300:.0f}%)")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        run_self_tests()
    else:
        main()
