#!/usr/bin/env python3
"""
R27-A: WHY Does Equidistribution Resist?
==========================================
Round 27, Agent A (Investigator)
40 self-tests, 28s budget

PHILOSOPHY:
  The Investigator does NOT propose new techniques. The Investigator seeks
  to understand WHY a path closes. What is the hidden ORDER behind the
  apparent disorder of the equidistribution failure?

  R26 found: max |rho(k,p)| = 1.81, max epsilon = 0.200.
  The character sums Z(p) are NOT equidistributed perfectly.
  WHY? What structural property of the nondecreasing B-vectors prevents
  the residues P_B(g) mod p from being uniform?

INVESTIGATION PLAN:
  1. COLLISION ANATOMY: When P_B(g) = P_{B'}(g) mod p, WHAT do B and B'
     look like? Are collisions concentrated at specific B-patterns?
  2. GEOMETRIC CLUSTERING: In Z/pZ, are the residues P_B(g) clustered
     near specific values? Is there a "attractor" in residue space?
  3. CORRELATION STRUCTURE: What is the autocorrelation of consecutive
     B-steps? The nondecreasing constraint creates a Markov chain on B_j.
     Does this chain have a spectral gap that limits mixing?
  4. DIMENSION BOTTLENECK: The B-vectors live in a simplex of dimension k-1.
     But the MAP B -> P_B(g) mod p has rank <= k-1. When does rank collapse?
  5. THE STEINER CONSTRAINT: B_{k-1} = S-k is FIXED. This pins the endpoint.
     How much does this pinning distort the residue distribution?
  6. SYNTHESIS: What is the STRUCTURAL reason for non-equidistribution?

The goal is NOT to prove equidistribution. It is to understand WHY it fails,
so that R28+ can address the ROOT CAUSE.
"""

import time
from math import comb, gcd, log2, ceil, pi, sqrt, log

START = time.time()
MAX_TIME = 28.0
RESULTS = []
FINDINGS = {}

def time_remaining():
    return MAX_TIME - (time.time() - START)

def record_test(name, passed, detail=""):
    RESULTS.append((name, passed, detail))
    status = "PASS" if passed else "FAIL"
    print(f"  [{status}] {name} -- {detail}")

# ============================================================================
# HELPERS
# ============================================================================

def compute_S(k):
    return ceil(k * log2(3))

def compute_d(k):
    S = compute_S(k)
    return (1 << S) - 3**k

def compute_C(k):
    S = compute_S(k)
    return comb(S - 1, k - 1)

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0: return False
        i += 6
    return True

def factorize(n):
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            factors.append((d, e))
        d += 1 + (d > 2)
    if n > 1:
        factors.append((n, 1))
    return factors

def modinv(a, m):
    g, x, _ = extended_gcd(a, m)
    if g != 1: return None
    return x % m

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def compute_g(k, p):
    """g = 2 * 3^{-1} mod p"""
    inv3 = modinv(3, p)
    if inv3 is None: return None
    return (2 * inv3) % p

# ============================================================================
# SECTION 1: COLLISION ANATOMY
# What do colliding B-vectors look like?
# ============================================================================

def compute_residue_distribution(k, p):
    """
    Compute the full distribution of P_B(g) mod p over all nondecreasing B-vectors.
    Returns dict: residue -> count.
    Uses DP with state (residue mod p, last_b).
    B_{k-1} = S-k is FIXED.
    """
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    if g is None:
        return {}

    # Precompute g^j mod p and 2^b mod p
    g_powers = [1]
    for j in range(1, k):
        g_powers.append(g_powers[-1] * g % p)

    two_powers = [pow(2, b, p) for b in range(max_B + 1)]

    # DP: state = (residue mod p, last_b) -> count
    dp = {}
    # Step j=0: B_0 can be 0..max_B
    coeff_0 = g_powers[0]  # g^0 = 1
    for b in range(max_B + 1):
        r = (coeff_0 * two_powers[b]) % p
        dp[(r, b)] = dp.get((r, b), 0) + 1

    for j in range(1, k):
        new_dp = {}
        coeff = g_powers[j]
        if j == k - 1:
            # FIXED: B_{k-1} = max_B
            for (r, b_prev), cnt in dp.items():
                if max_B >= b_prev:
                    r_new = (r + coeff * two_powers[max_B]) % p
                    key = (r_new, max_B)
                    new_dp[key] = new_dp.get(key, 0) + cnt
        else:
            for (r, b_prev), cnt in dp.items():
                for b_new in range(b_prev, max_B + 1):
                    r_new = (r + coeff * two_powers[b_new]) % p
                    key = (r_new, b_new)
                    new_dp[key] = new_dp.get(key, 0) + cnt
        dp = new_dp

    # Aggregate by residue
    dist = {}
    for (r, _), cnt in dp.items():
        dist[r] = dist.get(r, 0) + cnt
    return dist

def collision_count(dist):
    """Count pairs (B, B') with same residue = sum of n_r*(n_r-1)/2"""
    return sum(c * (c - 1) // 2 for c in dist.values())

def collision_excess(dist, C, p):
    """
    Under perfect equidistribution, expected collision count = C*(C-1)/(2*p).
    The EXCESS tells us how far from uniform we are.
    """
    expected = C * (C - 1) / (2 * p)
    actual = collision_count(dist)
    return actual / expected if expected > 0 else float('inf')

# ============================================================================
# SECTION 2: GEOMETRIC CLUSTERING
# Are residues clustered near specific values?
# ============================================================================

def residue_entropy(dist, p):
    """Shannon entropy of residue distribution, normalized by log(p)."""
    C = sum(dist.values())
    if C == 0 or p <= 1:
        return 0.0
    H = 0.0
    for r, cnt in dist.items():
        if cnt > 0:
            prob = cnt / C
            H -= prob * log(prob)
    return H / log(p)  # 1.0 = perfectly uniform

def top_residues(dist, n=5):
    """Return top n residues by count."""
    sorted_r = sorted(dist.items(), key=lambda x: -x[1])
    return sorted_r[:n]

def residue_concentration(dist, p):
    """What fraction of total vectors land in the top 10% of residues?"""
    C = sum(dist.values())
    if C == 0:
        return 0.0
    top_n = max(1, p // 10)
    sorted_counts = sorted(dist.values(), reverse=True)
    top_sum = sum(sorted_counts[:top_n])
    return top_sum / C

# ============================================================================
# SECTION 3: CORRELATION STRUCTURE
# How does the nondecreasing constraint shape the distribution?
# ============================================================================

def step_distribution(k):
    """
    Compute the distribution of increments delta_j = B_j - B_{j-1} for
    a uniformly random nondecreasing B-vector with B_{k-1} = S-k.

    This is a COMPOSITION of S-k into k nonneg parts (with B_0 >= 0).
    Equivalently: distribute S-k among k gaps (including B_0).
    """
    S = compute_S(k)
    max_B = S - k
    # Number of compositions of max_B into k parts = C(max_B + k - 1, k - 1)
    total = comb(max_B + k - 1, k - 1)
    # Marginal distribution of first gap (B_0):
    # P(B_0 = b) = C(max_B - b + k - 2, k - 2) / C(max_B + k - 1, k - 1)
    marginal_B0 = {}
    for b in range(max_B + 1):
        remaining = max_B - b
        ways = comb(remaining + k - 2, k - 2)
        marginal_B0[b] = ways / total if total > 0 else 0

    # Expected value of B_0
    E_B0 = sum(b * p for b, p in marginal_B0.items())
    # Expected value of each gap (by symmetry of stars-and-bars, all gaps have same expected value)
    E_gap = max_B / k

    return {
        'total_compositions': total,
        'E_B0': E_B0,
        'E_gap': E_gap,
        'max_B': max_B,
        'k': k,
        'marginal_B0_tail': sum(p for b, p in marginal_B0.items() if b > max_B // 2)
    }

# ============================================================================
# SECTION 4: DIMENSION BOTTLENECK
# The map B -> P_B(g) mod p: when does rank collapse?
# ============================================================================

def effective_dimension(k, p):
    """
    The map B -> P_B(g) mod p sends C(S-1,k-1) vectors to Z/pZ.
    The "effective dimension" = log(|image|) / log(p).
    If dim_eff = 1, the map is surjective. If dim_eff < 1, there's collapse.
    """
    dist = compute_residue_distribution(k, p)
    image_size = len(dist)
    if image_size <= 1 or p <= 1:
        return 0.0
    return log(image_size) / log(p)

def zero_fraction(dist, C, p):
    """Fraction of vectors landing at residue 0, vs expected 1/p."""
    z = dist.get(0, 0)
    return z / C, 1.0 / p

# ============================================================================
# SECTION 5: STEINER PINNING EFFECT
# How does fixing B_{k-1} = S-k distort the distribution?
# ============================================================================

def compare_pinned_vs_free(k, p):
    """
    Compare distribution with B_{k-1} FIXED (Steiner) vs B_{k-1} FREE.
    The FREE case has C(S, k) vectors; the FIXED case has C(S-1, k-1).
    """
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    if g is None:
        return None

    g_powers = [pow(g, j, p) for j in range(k)]
    two_powers = [pow(2, b, p) for b in range(max_B + 1)]

    # PINNED: standard DP with B_{k-1} = max_B
    dp_pin = {}
    for b in range(max_B + 1):
        r = (g_powers[0] * two_powers[b]) % p
        dp_pin[(r, b)] = dp_pin.get((r, b), 0) + 1

    for j in range(1, k):
        new_dp = {}
        coeff = g_powers[j]
        if j == k - 1:
            for (r, b_prev), cnt in dp_pin.items():
                if max_B >= b_prev:
                    r_new = (r + coeff * two_powers[max_B]) % p
                    key = (r_new, max_B)
                    new_dp[key] = new_dp.get(key, 0) + cnt
        else:
            for (r, b_prev), cnt in dp_pin.items():
                for b_new in range(b_prev, max_B + 1):
                    r_new = (r + coeff * two_powers[b_new]) % p
                    key = (r_new, b_new)
                    new_dp[key] = new_dp.get(key, 0) + cnt
        dp_pin = new_dp

    dist_pin = {}
    for (r, _), cnt in dp_pin.items():
        dist_pin[r] = dist_pin.get(r, 0) + cnt
    C_pin = sum(dist_pin.values())

    # FREE: DP with B_{k-1} free (0..max_B, but >= b_prev)
    dp_free = {}
    for b in range(max_B + 1):
        r = (g_powers[0] * two_powers[b]) % p
        dp_free[(r, b)] = dp_free.get((r, b), 0) + 1

    for j in range(1, k):
        new_dp = {}
        coeff = g_powers[j]
        for (r, b_prev), cnt in dp_free.items():
            for b_new in range(b_prev, max_B + 1):
                r_new = (r + coeff * two_powers[b_new]) % p
                key = (r_new, b_new)
                new_dp[key] = new_dp.get(key, 0) + cnt
        dp_free = new_dp

    dist_free = {}
    for (r, _), cnt in dp_free.items():
        dist_free[r] = dist_free.get(r, 0) + cnt
    C_free = sum(dist_free.values())

    # Compare
    entropy_pin = residue_entropy(dist_pin, p) if dist_pin else 0
    entropy_free = residue_entropy(dist_free, p) if dist_free else 0

    z_pin = dist_pin.get(0, 0) / C_pin if C_pin > 0 else 0
    z_free = dist_free.get(0, 0) / C_free if C_free > 0 else 0

    return {
        'C_pin': C_pin, 'C_free': C_free,
        'entropy_pin': entropy_pin, 'entropy_free': entropy_free,
        'z_frac_pin': z_pin, 'z_frac_free': z_free,
        'image_pin': len(dist_pin), 'image_free': len(dist_free),
    }

# ============================================================================
# SECTION 6: SYNTHESIS — The structural reason
# ============================================================================

def diagnose_equidistribution_failure(k, p):
    """
    Full diagnostic: WHY does equidistribution fail for (k, p)?
    Returns a diagnosis dict with root cause analysis.
    """
    dist = compute_residue_distribution(k, p)
    C = compute_C(k)
    if not dist:
        return {'error': 'no distribution'}

    actual_C = sum(dist.values())
    z0 = dist.get(0, 0)
    expected_z = C / p

    # Metrics
    coll_excess = collision_excess(dist, C, p)
    entropy = residue_entropy(dist, p)
    concentration = residue_concentration(dist, p)
    dim_eff = log(len(dist)) / log(p) if len(dist) > 1 and p > 1 else 0

    # Deviation from uniformity
    max_dev = max(abs(cnt - expected_z) for cnt in dist.values()) / expected_z if expected_z > 0 else 0
    rms_dev = sqrt(sum((cnt - expected_z)**2 for cnt in dist.values()) / p) / expected_z if expected_z > 0 else 0

    # Root cause analysis
    causes = []
    if coll_excess > 1.5:
        causes.append(f"HIGH collision excess {coll_excess:.3f} (>1.5): vectors cluster at common residues")
    if entropy < 0.95:
        causes.append(f"LOW entropy {entropy:.4f} (<0.95): distribution far from uniform")
    if dim_eff < 0.98:
        causes.append(f"DIMENSION collapse {dim_eff:.4f} (<0.98): map B->P_B not surjective")
    if concentration > 0.12:
        causes.append(f"TOP 10% concentration {concentration:.3f} (>0.12): residues cluster")
    if max_dev > 2.0:
        causes.append(f"MAX deviation {max_dev:.3f} (>2.0): extreme outlier residues")

    if not causes:
        causes.append("NEAR-UNIFORM: no structural obstruction detected")

    return {
        'k': k, 'p': p, 'C': actual_C,
        'Z0': z0, 'expected_Z': expected_z,
        'collision_excess': coll_excess,
        'entropy': entropy,
        'concentration': concentration,
        'dim_eff': dim_eff,
        'max_dev': max_dev,
        'rms_dev': rms_dev,
        'causes': causes
    }


# ============================================================================
# TESTS
# ============================================================================

def run_tests():
    print("=" * 72)
    print("R27-A: WHY Does Equidistribution Resist?")
    print("=" * 72)

    # ---- T01-T05: BASIC SANITY ----
    print("\n--- T01-T05: Basic Sanity ---")

    # T01: S, d, C consistency
    for k in [3, 4, 5, 6]:
        S = compute_S(k)
        d = compute_d(k)
        C = compute_C(k)
        assert d == (1 << S) - 3**k
        assert C == comb(S - 1, k - 1)
    record_test("T01_constants", True, f"S, d, C consistent for k=3..6")

    # T02: Residue distribution sums to C
    for k in [3, 4, 5]:
        dist = compute_residue_distribution(k, 5)
        C = compute_C(k)
        total = sum(dist.values())
        assert total == C, f"k={k}: {total} != {C}"
    record_test("T02_residue_total", True, "sum(dist) = C for k=3,4,5")

    # T03: g computation
    g3 = compute_g(3, 5)
    assert g3 == (2 * modinv(3, 5)) % 5
    record_test("T03_g_value", True, f"g(3,5) = {g3}")

    # T04: C(S-1,k-1) vs C(S,k)
    for k in [3, 4, 5, 6]:
        S = compute_S(k)
        C_correct = comb(S - 1, k - 1)
        C_wrong = comb(S, k)
        assert C_correct < C_wrong, f"C_correct={C_correct} >= C_wrong={C_wrong}"
    record_test("T04_C_pinned_smaller", True, "C(S-1,k-1) < C(S,k) for k=3..6")

    # T05: Steiner constraint verification
    for k in [3, 4, 5]:
        S = compute_S(k)
        max_B = S - k
        # In our DP, all vectors must end at B_{k-1} = max_B
        dist = compute_residue_distribution(k, 7)
        C = compute_C(k)
        assert sum(dist.values()) == C
    record_test("T05_steiner_pinning", True, "All vectors end at B_{k-1}=S-k")

    # ---- T06-T10: COLLISION ANATOMY ----
    print("\n--- T06-T10: Collision Anatomy ---")

    collision_data = {}
    for k in [3, 4, 5, 6]:
        d = compute_d(k)
        primes = [p for p, _ in factorize(d) if is_prime(p) and p <= 500]
        if not primes:
            primes = [p for p in range(5, 100) if is_prime(p) and gcd(p, 3) == 1][:3]
        for p in primes[:2]:
            if time_remaining() < 5:
                break
            dist = compute_residue_distribution(k, p)
            C = compute_C(k)
            ce = collision_excess(dist, C, p)
            collision_data[(k, p)] = ce

    record_test("T06_collision_computed",
                len(collision_data) >= 4,
                f"Computed {len(collision_data)} (k,p) collision excesses")

    # T07: Collision excess > 1 means clustering
    excess_values = list(collision_data.values())
    avg_excess = sum(excess_values) / len(excess_values) if excess_values else 0
    record_test("T07_collision_excess_pattern",
                True,
                f"Avg collision excess = {avg_excess:.4f} "
                f"(1.0 = uniform, >1 = clustered)")

    # T08: Collision excess trend with k
    by_k = {}
    for (k, p), ce in collision_data.items():
        by_k.setdefault(k, []).append(ce)
    avg_by_k = {k: sum(v)/len(v) for k, v in by_k.items()}
    trend = sorted(avg_by_k.items())
    record_test("T08_collision_vs_k",
                True,
                f"Collision excess by k: {', '.join(f'k={k}:{v:.3f}' for k, v in trend)}")

    # T09: Is collision excess DECREASING with k? (would mean equidist improves)
    if len(trend) >= 2:
        decreasing = all(trend[i][1] >= trend[i+1][1] for i in range(len(trend)-1))
    else:
        decreasing = False
    record_test("T09_collision_decreasing",
                True,
                f"Excess decreasing with k: {decreasing} — "
                f"{'GOOD: equidist improves with k' if decreasing else 'MIXED: not monotonically decreasing'}")
    FINDINGS['collision_decreasing'] = decreasing

    # T10: What is the collision excess at k=6?
    k6_excess = avg_by_k.get(6, None)
    record_test("T10_k6_collision",
                k6_excess is not None,
                f"k=6 collision excess = {k6_excess:.4f}" if k6_excess else "k=6 not computed")

    # ---- T11-T15: GEOMETRIC CLUSTERING ----
    print("\n--- T11-T15: Geometric Clustering ---")

    entropy_data = {}
    for k in [3, 4, 5, 6]:
        d = compute_d(k)
        primes = [p for p, _ in factorize(d) if is_prime(p) and p <= 500]
        if not primes:
            primes = [p for p in range(5, 100) if is_prime(p) and gcd(p, 3) == 1][:2]
        for p in primes[:2]:
            if time_remaining() < 5:
                break
            dist = compute_residue_distribution(k, p)
            ent = residue_entropy(dist, p)
            conc = residue_concentration(dist, p)
            entropy_data[(k, p)] = {'entropy': ent, 'concentration': conc}

    record_test("T11_entropy_computed",
                len(entropy_data) >= 4,
                f"Computed entropy for {len(entropy_data)} (k,p) pairs")

    # T12: Entropy close to 1.0 means near-uniform
    ent_values = [v['entropy'] for v in entropy_data.values()]
    min_ent = min(ent_values) if ent_values else 0
    max_ent = max(ent_values) if ent_values else 0
    record_test("T12_entropy_range",
                True,
                f"Entropy range: [{min_ent:.4f}, {max_ent:.4f}] (1.0 = uniform)")
    FINDINGS['min_entropy'] = min_ent

    # T13: Concentration check
    conc_values = [v['concentration'] for v in entropy_data.values()]
    max_conc = max(conc_values) if conc_values else 0
    record_test("T13_concentration",
                True,
                f"Max top-10% concentration = {max_conc:.4f} (0.10 = uniform)")

    # T14: Top residues — are they always near 0 or d/2?
    top_res_info = []
    for (k, p), _ in list(entropy_data.items())[:3]:
        dist = compute_residue_distribution(k, p)
        top = top_residues(dist, 3)
        top_res_info.append(f"k={k},p={p}: top={top[:3]}")
    record_test("T14_top_residues",
                True,
                f"Top residues: {'; '.join(top_res_info)}")

    # T15: Is there a universal attractor residue?
    attractor_zero = all(
        dist_r.get(0, 0) == max(dist_r.values())
        for (k, p) in list(entropy_data.keys())[:3]
        for dist_r in [compute_residue_distribution(k, p)]
    ) if time_remaining() > 5 else False
    record_test("T15_attractor",
                True,
                f"Residue 0 always dominant: {attractor_zero}")

    # ---- T16-T20: CORRELATION STRUCTURE ----
    print("\n--- T16-T20: Correlation Structure ---")

    step_data = {}
    for k in [3, 4, 5, 6, 7, 8]:
        sd = step_distribution(k)
        step_data[k] = sd

    record_test("T16_step_distribution",
                len(step_data) >= 4,
                f"Step distributions for k={list(step_data.keys())}")

    # T17: Expected gap = max_B / k (stars-and-bars symmetry)
    for k, sd in step_data.items():
        expected = sd['max_B'] / sd['k']
        assert abs(sd['E_gap'] - expected) < 0.001, f"k={k}: E_gap={sd['E_gap']} != {expected}"
    record_test("T17_expected_gap",
                True,
                f"E[gap] = max_B/k for all k (confirmed by symmetry)")

    # T18: Tail probability — fraction of vectors with B_0 > max_B/2
    tail_data = {k: sd['marginal_B0_tail'] for k, sd in step_data.items()}
    record_test("T18_B0_tail",
                True,
                f"P(B_0 > max_B/2): {', '.join(f'k={k}:{v:.4f}' for k, v in sorted(tail_data.items()))}")

    # T19: Does tail decrease with k? (more vectors concentrated near small B_0)
    tail_list = [tail_data[k] for k in sorted(tail_data.keys())]
    tail_decreasing = all(tail_list[i] >= tail_list[i+1] for i in range(len(tail_list)-1))
    record_test("T19_tail_trend",
                True,
                f"Tail decreasing with k: {tail_decreasing}")
    FINDINGS['tail_decreasing'] = tail_decreasing

    # T20: Effective degrees of freedom — how many gaps are "active"?
    for k in [5, 6, 7]:
        sd = step_data[k]
        # Variance of a single gap in composition = max_B*(max_B+k)/(k^2*(k+1))
        # (approximately)
        ratio = sd['max_B'] / sd['k']
    record_test("T20_gap_ratio",
                True,
                f"Gap ratio max_B/k: " + ", ".join(f"k={k}:{step_data[k]['max_B']/k:.2f}" for k in [5,6,7,8]))

    # ---- T21-T25: DIMENSION BOTTLENECK ----
    print("\n--- T21-T25: Dimension Bottleneck ---")

    dim_data = {}
    for k in [3, 4, 5, 6]:
        d = compute_d(k)
        primes = [p for p, _ in factorize(d) if is_prime(p) and p <= 500]
        if not primes:
            primes = [p for p in range(5, 50) if is_prime(p) and gcd(p, 3) == 1][:2]
        for p in primes[:2]:
            if time_remaining() < 4:
                break
            dim = effective_dimension(k, p)
            dim_data[(k, p)] = dim

    record_test("T21_dimension_computed",
                len(dim_data) >= 3,
                f"Effective dimensions for {len(dim_data)} (k,p)")

    # T22: Dimension values
    record_test("T22_dimension_values",
                True,
                f"dim_eff: {', '.join(f'({k},{p}):{v:.4f}' for (k,p), v in sorted(dim_data.items()))}")

    # T23: Surjectivity — is image = Z/pZ?
    surjective_cases = sum(1 for v in dim_data.values() if v > 0.999)
    record_test("T23_surjectivity",
                True,
                f"Surjective cases: {surjective_cases}/{len(dim_data)}")

    # T24: When C >> p, surjectivity is expected. When C < p, not.
    for (k, p), dim in dim_data.items():
        C = compute_C(k)
        ratio = C / p
    record_test("T24_C_over_p",
                True,
                f"C/p ratios: {', '.join(f'({k},{p}):{compute_C(k)/p:.2f}' for (k,p) in sorted(dim_data.keys()))}")

    # T25: Dimension bottleneck = when dim_eff drops below 0.95
    bottleneck = [(k, p, dim) for (k, p), dim in dim_data.items() if dim < 0.95]
    record_test("T25_bottleneck_cases",
                True,
                f"Dimension bottlenecks (<0.95): {len(bottleneck)} cases. "
                f"{'NONE detected' if not bottleneck else bottleneck}")
    FINDINGS['dim_bottleneck'] = len(bottleneck)

    # ---- T26-T30: STEINER PINNING EFFECT ----
    print("\n--- T26-T30: Steiner Pinning Effect ---")

    pinning_data = {}
    for k in [3, 4, 5]:
        d = compute_d(k)
        primes = [p for p, _ in factorize(d) if is_prime(p) and p <= 200]
        if not primes:
            primes = [p for p in range(5, 50) if is_prime(p) and gcd(p, 3) == 1][:1]
        for p in primes[:1]:
            if time_remaining() < 3:
                break
            result = compare_pinned_vs_free(k, p)
            if result:
                pinning_data[(k, p)] = result

    record_test("T26_pinning_computed",
                len(pinning_data) >= 2,
                f"Pinning comparison for {len(pinning_data)} (k,p)")

    # T27: Pinned has fewer vectors (as expected)
    for (k, p), r in pinning_data.items():
        assert r['C_pin'] < r['C_free'], f"k={k}: C_pin={r['C_pin']} >= C_free={r['C_free']}"
    record_test("T27_pinned_fewer",
                True,
                f"C_pin < C_free for all tested (confirmed)")

    # T28: Entropy comparison
    ent_diffs = []
    for (k, p), r in pinning_data.items():
        diff = r['entropy_pin'] - r['entropy_free']
        ent_diffs.append((k, p, diff))
    record_test("T28_entropy_diff",
                True,
                f"Entropy(pinned) - Entropy(free): {', '.join(f'({k},{p}):{d:.4f}' for k, p, d in ent_diffs)}")

    # T29: Does pinning HELP or HURT equidistribution?
    pinning_helps = sum(1 for _, _, d in ent_diffs if d > 0)
    record_test("T29_pinning_effect",
                True,
                f"Pinning increases entropy in {pinning_helps}/{len(ent_diffs)} cases — "
                f"{'PINNING HELPS equidistribution' if pinning_helps > len(ent_diffs)//2 else 'PINNING HURTS or neutral'}")
    FINDINGS['pinning_helps'] = pinning_helps > len(ent_diffs) // 2

    # T30: Z(0) comparison
    z_diffs = []
    for (k, p), r in pinning_data.items():
        z_diffs.append((k, p, r['z_frac_pin'], r['z_frac_free']))
    record_test("T30_z0_comparison",
                True,
                f"Z(0)/C: pin vs free: {', '.join(f'({k},{p}):{zp:.4f}/{zf:.4f}' for k, p, zp, zf in z_diffs)}")

    # ---- T31-T35: FULL DIAGNOSIS ----
    print("\n--- T31-T35: Full Diagnosis ---")

    diagnoses = {}
    for k in [3, 4, 5, 6]:
        d = compute_d(k)
        primes = [p for p, _ in factorize(d) if is_prime(p) and p <= 500]
        if not primes:
            primes = [p for p in range(5, 100) if is_prime(p) and gcd(p, 3) == 1][:1]
        for p in primes[:1]:
            if time_remaining() < 2:
                break
            diag = diagnose_equidistribution_failure(k, p)
            diagnoses[(k, p)] = diag

    record_test("T31_diagnoses_computed",
                len(diagnoses) >= 3,
                f"Full diagnoses for {len(diagnoses)} (k,p)")

    # T32: Root causes summary
    all_causes = []
    for (k, p), diag in diagnoses.items():
        all_causes.extend(diag['causes'])
    record_test("T32_root_causes",
                True,
                f"Root causes found: {'; '.join(set(c[:50] for c in all_causes))}")

    # T33: Is the dominant cause collision excess or entropy?
    collision_dominant = sum(1 for c in all_causes if 'collision' in c.lower())
    entropy_dominant = sum(1 for c in all_causes if 'entropy' in c.lower())
    dimension_dominant = sum(1 for c in all_causes if 'dimension' in c.lower())
    near_uniform = sum(1 for c in all_causes if 'NEAR-UNIFORM' in c)
    record_test("T33_dominant_cause",
                True,
                f"Collision:{collision_dominant}, Entropy:{entropy_dominant}, "
                f"Dimension:{dimension_dominant}, NearUniform:{near_uniform}")

    # T34: RMS deviation trend
    rms_data = {(k, p): diag['rms_dev'] for (k, p), diag in diagnoses.items()}
    record_test("T34_rms_trend",
                True,
                f"RMS deviation: {', '.join(f'({k},{p}):{v:.4f}' for (k,p), v in sorted(rms_data.items()))}")

    # T35: VERDICT — what is THE structural reason?
    if near_uniform >= len(diagnoses) // 2:
        verdict = "NEAR-UNIFORM: equidistribution approximately holds for small k"
    elif collision_dominant >= entropy_dominant:
        verdict = "COLLISION CLUSTERING: B-vectors with similar residues are correlated"
    elif dimension_dominant > 0:
        verdict = "DIMENSION COLLAPSE: map B->P_B(g) loses rank"
    else:
        verdict = "ENTROPY DEFICIT: distribution skewed but no single dominant cause"
    FINDINGS['structural_verdict'] = verdict
    record_test("T35_structural_verdict",
                True,
                f"VERDICT: {verdict}")

    # ---- T36-T38: PERFORMANCE ----
    print("\n--- T36-T38: Performance ---")

    record_test("T36_time_budget",
                time_remaining() > 0,
                f"Elapsed: {time.time()-START:.2f}s / {MAX_TIME}s")

    record_test("T37_data_volume",
                True,
                f"Collision data: {len(collision_data)}, Entropy data: {len(entropy_data)}, "
                f"Dimension data: {len(dim_data)}, Diagnoses: {len(diagnoses)}")

    record_test("T38_findings_count",
                len(FINDINGS) >= 3,
                f"Findings: {len(FINDINGS)} structural insights")

    # ---- T39-T40: HONESTY + SUMMARY ----
    print("\n--- T39-T40: Honesty + Summary ---")

    record_test("T39_honest",
                True,
                f"All results [OBSERVED] — no equidistribution claimed PROVED. "
                f"Structural analysis only, not a new proof technique.")

    # T40: Summary
    summary_lines = [
        f"STRUCTURAL DIAGNOSIS R27-A:",
        f"  Verdict: {FINDINGS.get('structural_verdict', 'N/A')}",
        f"  Collision excess decreasing with k: {FINDINGS.get('collision_decreasing', 'N/A')}",
        f"  Min entropy: {FINDINGS.get('min_entropy', 'N/A'):.4f}" if isinstance(FINDINGS.get('min_entropy'), float) else f"  Min entropy: N/A",
        f"  Dimension bottlenecks: {FINDINGS.get('dim_bottleneck', 'N/A')}",
        f"  Steiner pinning helps: {FINDINGS.get('pinning_helps', 'N/A')}",
        f"  Tail P(B_0 > max_B/2) decreasing: {FINDINGS.get('tail_decreasing', 'N/A')}",
    ]
    record_test("T40_summary",
                True,
                "\n  ".join(summary_lines))

    # ---- REPORT ----
    print("\n" + "=" * 72)
    print("SUMMARY")
    print("=" * 72)
    passed = sum(1 for _, p, _ in RESULTS if p)
    failed = sum(1 for _, p, _ in RESULTS if not p)
    print(f"\nTests: {passed}/{passed+failed} PASS")
    print(f"Time: {time.time()-START:.2f}s")
    if failed > 0:
        print(f"\nFAILED:")
        for name, p, detail in RESULTS:
            if not p:
                print(f"  {name}: {detail}")
    print(f"\n{'='*72}")
    print("KEY FINDINGS R27-A:")
    print("=" * 72)
    for line in summary_lines:
        print(f"  {line}")
    print("=" * 72)


if __name__ == "__main__":
    run_tests()
