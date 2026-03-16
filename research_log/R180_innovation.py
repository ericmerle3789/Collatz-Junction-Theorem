#!/usr/bin/env python3
"""
R180 — INNOVATION : NOVEL APPROACHES TO COLLATZ CYCLE EXCLUSION

Five unconventional angles beyond the classical reformulation:

1. STABILIZATION-CYCLE INCOMPATIBILITY
   If D-gaps stabilize to 2 (trajectory to 1), cycles need non-stabilizing
   D-sequences. What algebraic constraint does this impose?

2. MODULAR ARITHMETIC CASCADE
   g(v) mod small primes: systematic obstructions to divisibility by d.

3. ENTROPY / DENSITY ARGUMENT
   Among C(S,x) vectors, what fraction satisfies ALL cycle conditions?

4. A_m GROWTH RATE vs d CONSTRAINT
   A_{x-1}/3^{x-1} growth vs S constraint from d = 2^S - 3^x.

5. CROSS-CUTTING PATTERNS
   Combine all of the above to identify structural impossibilities.

Author: R180 research exploration
"""

import math
import random
from itertools import combinations
from collections import defaultdict, Counter
from math import gcd, log2, comb, factorial


# ═══════════════════════════════════════════════════════════════════════════
# CORE UTILITIES
# ═══════════════════════════════════════════════════════════════════════════

def v2(n):
    """2-adic valuation of n."""
    if n == 0:
        return float('inf')
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def odd_part(n):
    """Odd part of n: n / 2^{v2(n)}."""
    while n > 0 and n % 2 == 0:
        n //= 2
    return n


def collatz_odd(n):
    """Compressed Collatz on odd numbers: n -> odd(3n+1)."""
    return odd_part(3 * n + 1)


def compute_A_sequence(k, x):
    """
    A_0 = 3k+1, A_{m+1} = 3A_m + 2^{v2(A_m)}.
    Returns (As, Bs, valuations, D_gaps).
    """
    A = 3 * k + 1
    As = [A]
    Bs = [odd_part(A)]
    vals = [v2(A)]
    D_gaps = []

    for m in range(1, x):
        A = 3 * A + 2 ** v2(A)
        As.append(A)
        Bs.append(odd_part(A))
        vals.append(v2(A))

    # D_m = cumulative valuations
    Ds = [vals[0]]
    for i in range(1, len(vals)):
        Ds.append(Ds[-1] + vals[i])

    # Actually, D_m are the positions in the binary vector
    # D_0 = v2(A_0), and D_m = v2(remainder at step m)
    # Let me recompute properly using the descent
    return As, Bs, vals, Ds


def compute_D_sequence(k, x):
    """
    Compute the D-sequence (positions) for the 2-adic descent.
    D_0 = v2(3k+1), then D_m = v2(remainder_m).
    Returns Ds list and the gaps.
    """
    C = (3 * k + 1) * 3 ** (x - 1)
    Ds = [v2(C)]  # D_0

    for m in range(1, x):
        coeff = 3 ** (x - 1 - m)
        C = C + coeff * 2 ** Ds[-1]
        D_m = v2(C)
        Ds.append(D_m)

    gaps = [Ds[i + 1] - Ds[i] for i in range(len(Ds) - 1)]
    return Ds, gaps


def compute_g(positions, x):
    """g(v) = sum_{j=0}^{x-1} 3^{x-1-j} * 2^{e_j}."""
    return sum(3 ** (x - 1 - j) * 2 ** positions[j] for j in range(x))


def multiplicative_order(a, n):
    """Order of a modulo n."""
    if gcd(a, n) != 1:
        return None
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order


def is_periodic_vector(positions, S):
    """Check if the binary vector with 1s at 'positions' is periodic in {0,...,S-1}."""
    pos_set = set(positions)
    for p in range(1, S):
        if S % p != 0:
            continue
        if p >= S:
            break
        shifted = set((pos + p) % S for pos in pos_set)
        if shifted == pos_set:
            return True, p
    return False, None


# ═══════════════════════════════════════════════════════════════════════════
# PART 1: STABILIZATION-CYCLE INCOMPATIBILITY
# ═══════════════════════════════════════════════════════════════════════════

def part1_stabilization():
    """
    Study D-gap stabilization. For trajectories reaching 1, gaps -> 2.
    A cycle would require non-stabilizing gaps. What does this mean algebraically?
    """
    print("=" * 80)
    print("PART 1: STABILIZATION-CYCLE INCOMPATIBILITY")
    print("=" * 80)

    # 1a. Study gap patterns for k=3..999
    print("\n--- 1a. D-gap stabilization statistics ---")
    stabilization_data = []

    for k in range(3, 1000, 2):
        # Compute Collatz trajectory (compressed)
        b = k
        trajectory = [k]
        vals = []
        for step in range(200):
            val = v2(3 * b + 1)
            vals.append(val)
            b = collatz_odd(b)
            trajectory.append(b)
            if b == 1:
                break

        if b != 1:
            continue  # Didn't reach 1 in 200 steps

        # Compute gaps in valuation sequence
        gaps = vals  # These are the gaps: D_{m+1} - D_m = v2(3*B_m + 1)

        # Find stabilization point: where gaps become constantly 2
        x_len = len(gaps)
        stab_point = x_len  # Default: never stabilizes within trajectory
        for i in range(x_len - 1, -1, -1):
            if gaps[i] != 2:
                stab_point = i + 1
                break
        else:
            stab_point = 0  # All gaps are 2

        # Count how many gaps equal 2
        n_gap2 = sum(1 for g in gaps if g == 2)
        frac_gap2 = n_gap2 / x_len if x_len > 0 else 0

        # Record gap variety before stabilization
        pre_stab_gaps = gaps[:stab_point]
        gap_variety = len(set(pre_stab_gaps)) if pre_stab_gaps else 0

        stabilization_data.append({
            'k': k, 'x': x_len, 'stab': stab_point,
            'frac2': frac_gap2, 'variety': gap_variety,
            'max_gap': max(gaps) if gaps else 0,
            'gaps': gaps[:min(20, len(gaps))]
        })

    # Statistics
    print(f"  Analyzed {len(stabilization_data)} odd numbers k in [3,999]")

    avg_frac2 = sum(d['frac2'] for d in stabilization_data) / len(stabilization_data)
    avg_variety = sum(d['variety'] for d in stabilization_data) / len(stabilization_data)
    max_gap_ever = max(d['max_gap'] for d in stabilization_data)

    print(f"  Average fraction of gap=2: {avg_frac2:.4f}")
    print(f"  Average gap variety (pre-stabilization): {avg_variety:.2f}")
    print(f"  Maximum gap observed: {max_gap_ever}")

    # Gap distribution
    all_gaps = []
    for d in stabilization_data:
        all_gaps.extend(d['gaps'])
    gap_counts = Counter(all_gaps)
    total_gaps = len(all_gaps)
    print(f"\n  Gap distribution (total {total_gaps} gaps):")
    for gap_val in sorted(gap_counts.keys()):
        count = gap_counts[gap_val]
        print(f"    gap={gap_val}: {count} ({100*count/total_gaps:.1f}%)")

    # 1b. KEY INSIGHT: For a cycle, B_m NEVER reaches 1.
    # If B_m cycles through k1, k2, ..., k_x, k1, ...
    # then the gaps v2(3*k_i + 1) form a PERIODIC sequence.
    # The D-sequence has periodic gaps => positions are arithmetic-like.
    print("\n--- 1b. CYCLE implies PERIODIC gap sequence ---")
    print("""
  KEY OBSERVATION:
  If k is in a cycle of length x: B_0, B_1, ..., B_{x-1}, B_0, ...
  Then v_2(3*B_m + 1) is PERIODIC with period x (same orbit repeated).

  The D-gaps = (g_0, g_1, ..., g_{x-1}) with g_m = v_2(3*B_m + 1).
  The positions D_m = sum_{i=0}^{m-1} g_i are determined by these gaps.
  S = sum of all gaps = D_0 + g_0 + g_1 + ... + g_{x-1}.

  CONSTRAINT: The binary vector v in {0,1}^S must be APERIODIC.
  But: if the gaps g_m are "too regular", the positions may be periodic!
""")

    # 1c. Study what gap patterns would make positions periodic
    print("--- 1c. When do periodic gaps => periodic vector? ---")

    # If all gaps are equal (= s), positions are {0, s, 2s, ..., (x-1)s}, S = xs.
    # Vector has period s if s | S, which is s | xs => always true!
    # So CONSTANT gaps => PERIODIC vector => excluded!
    print("  Theorem: If all gaps are equal to s, vector has period s.")
    print("  Proof: positions = {0, s, 2s, ..., (x-1)s}, S = xs + D_0.")
    print("         If D_0 = 0: translation by s maps positions to positions mod S. QED")
    print()

    # What if gaps take exactly 2 distinct values?
    # Example: gaps alternate between a and b: positions 0, a, a+b, 2a+b, 2a+2b,...
    # Period = a+b if x is even.
    print("  QUESTION: What about gaps with limited variety?")
    print("  Testing: for hypothetical 'cycle-like' gap patterns...")

    # Simulate hypothetical cycle gap patterns
    test_patterns = [
        [2, 2, 2, 2, 2],        # All 2s
        [1, 3, 1, 3, 1],        # Alternating 1,3
        [2, 1, 2, 1, 2],        # Alternating 2,1
        [1, 2, 3, 1, 2],        # Period 3
        [1, 1, 4, 1, 1],        # Mostly 1 with spike
        [3, 2, 1, 2, 3],        # Palindrome
        [1, 2, 1, 3, 2],        # Irregular
        [4, 1, 1, 1, 1],        # One big gap
    ]

    for gaps_pattern in test_patterns:
        x = len(gaps_pattern)
        # Assume D_0 = 0 for simplicity (v2(3k+1) contribution already counted)
        positions = [0]
        for g in gaps_pattern[:-1]:  # x-1 gaps between x positions
            positions.append(positions[-1] + g)
        S = positions[-1] + gaps_pattern[-1]  # Close the cycle: S = last pos + last gap

        is_per, period = is_periodic_vector(positions, S)
        print(f"    Gaps {gaps_pattern}: positions={positions}, S={S}, "
              f"periodic={'YES (p=' + str(period) + ')' if is_per else 'NO'}")

    # 1d. THE CRUCIAL CONSTRAINT: cycle gaps must satisfy S/x = average gap > log2(3)
    print("\n--- 1d. Average gap constraint for cycles ---")
    print(f"  For d = 2^S - 3^x > 0: S/x > log2(3) = {log2(3):.6f}")
    print(f"  For k >= 3 odd: k = g(v)/d >= 3, so g(v) >= 3d = 3(2^S - 3^x)")
    print(f"  Average valuation v2(3B+1) for 'random' odd B: E[v2(3B+1)] = 2")
    print(f"  (P(v2(3B+1) = n) = 1/2^n for n >= 1)")
    print(f"  So 'expected' S/x = 2, which satisfies > log2(3) ~ 1.585")

    # 1e. NON-STABILIZATION means gap variance stays bounded away from 0
    print("\n--- 1e. Non-stabilization: gap variance for trajectories vs cycles ---")

    # For real trajectories (reaching 1), compute variance of gaps
    variances_real = []
    for d in stabilization_data[:100]:
        gaps = d['gaps']
        if len(gaps) >= 5:
            mean_g = sum(gaps) / len(gaps)
            var_g = sum((g - mean_g) ** 2 for g in gaps) / len(gaps)
            variances_real.append(var_g)

    print(f"  Real trajectories (k=3..199): mean gap variance = {sum(variances_real)/len(variances_real):.4f}")

    # For a cycle: gaps repeat exactly. Variance of a full cycle period = variance of one period.
    # The constraint is that gaps must produce an APERIODIC vector.
    # From 1c: constant gaps => periodic. Low-variety gaps often => periodic.
    # So cycles need HIGH gap variety... but they're deterministic from the orbit!

    return stabilization_data


# ═══════════════════════════════════════════════════════════════════════════
# PART 2: MODULAR ARITHMETIC CASCADE
# ═══════════════════════════════════════════════════════════════════════════

def part2_modular_cascade():
    """
    Study g(v) mod small primes for valid vectors.
    Look for systematic obstructions.
    """
    print("\n\n" + "=" * 80)
    print("PART 2: MODULAR ARITHMETIC CASCADE")
    print("=" * 80)

    primes = [5, 7, 11, 13, 17, 19, 23, 29, 31]

    # For each (S, x) pair, compute d = 2^S - 3^x and factorize
    print("\n--- 2a. Factor structure of d = 2^S - 3^x ---")

    d_factors = {}
    for x in range(2, 20):
        S_min = int(math.ceil(x * log2(3))) + 1
        for S in range(S_min, S_min + 10):
            d = 2 ** S - 3 ** x
            if d <= 0:
                continue
            # Simple factorization
            factors = {}
            temp = d
            for p in range(2, min(1000, abs(temp) + 1)):
                while temp % p == 0:
                    factors[p] = factors.get(p, 0) + 1
                    temp //= p
                if abs(temp) == 1:
                    break
            if abs(temp) > 1:
                factors[abs(temp)] = 1
            d_factors[(S, x)] = (d, factors)

    # Show some examples
    print(f"  {'(S,x)':<12} {'d':>15} {'factorization'}")
    count = 0
    for (S, x), (d, factors) in sorted(d_factors.items()):
        if count >= 25:
            break
        if d > 0 and d < 10**8:
            fstr = ' * '.join(f'{p}^{e}' if e > 1 else str(p) for p, e in sorted(factors.items()))
            print(f"  ({S},{x}){'':<6} {d:>15} = {fstr}")
            count += 1

    # 2b. For each prime p, study g(v) mod p
    print("\n--- 2b. g(v) mod p analysis ---")

    for x in range(2, 8):
        S_min = int(math.ceil(x * log2(3))) + 1
        for S in range(S_min, S_min + 3):
            d = 2 ** S - 3 ** x
            if d <= 0:
                continue

            # Enumerate all vectors (feasible for small S, x)
            if comb(S, x) > 50000:
                continue

            n_total = 0
            n_div_d = 0
            n_odd_quotient = 0
            n_ge3 = 0
            n_aperiodic = 0
            n_full_valid = 0

            mod_counts = {p: defaultdict(int) for p in primes}

            for positions in combinations(range(S), x):
                n_total += 1
                g = compute_g(positions, x)

                for p in primes:
                    mod_counts[p][g % p] += 1

                if g % d != 0:
                    continue
                n_div_d += 1

                q = g // d
                if q % 2 != 1:
                    continue
                n_odd_quotient += 1

                if q < 3:
                    continue
                n_ge3 += 1

                # Check aperiodicity
                is_per, _ = is_periodic_vector(positions, S)
                if is_per:
                    continue
                n_aperiodic += 1
                n_full_valid += 1

            print(f"\n  (S={S}, x={x}): C(S,x) = {n_total}")
            print(f"    g(v) == 0 mod d={d}: {n_div_d} ({100*n_div_d/n_total:.2f}%)" if n_total > 0 else "")
            print(f"    + odd quotient:      {n_odd_quotient}")
            print(f"    + quotient >= 3:     {n_ge3}")
            print(f"    + aperiodic:         {n_aperiodic}")
            print(f"    CYCLE CANDIDATES:    {n_full_valid}")

            # Show g(v) mod p distribution
            for p in [5, 7, 11]:
                if d % p == 0:
                    dist = mod_counts[p]
                    zero_count = dist.get(0, 0)
                    expected = n_total / p
                    print(f"    g mod {p}: #{0}={zero_count} (expected ~{expected:.1f}), "
                          f"ratio={zero_count/expected:.3f}" if expected > 0 else "")

    # 2c. THE KEY QUESTION: does the "cascade" of conditions compound?
    print("\n--- 2c. Cascade compounding analysis ---")
    print("""
  For a cycle to exist, ALL of these must hold simultaneously:
    (i)   g(v) = 0 mod d
    (ii)  g(v)/d is odd
    (iii) g(v)/d >= 3
    (iv)  vector is aperiodic

  If conditions were independent (they're NOT), probability would be:
    P(i)   ~ 1/d (random divisibility)
    P(ii)  ~ 1/2
    P(iii) ~ high (most quotients > 3 when they exist)
    P(iv)  ~ 1 - x/S (most vectors are aperiodic for large S)

  Combined: ~ C(S,x) / (2d) candidates.
  Since d ~ 2^S (for S >> x), this is ~ C(S,x) / 2^{S+1}.
""")

    # Compute the ratio C(S,x) / 2^{S+1} for various (S,x)
    print("  Expected candidates C(S,x) / (2d):")
    for x in range(2, 25):
        S = int(math.ceil(x * log2(3))) + 1
        d = 2 ** S - 3 ** x
        if d <= 0:
            S += 1
            d = 2 ** S - 3 ** x
        log_comb = sum(log2(S - i) - log2(i + 1) for i in range(x)) if x > 0 and S >= x else 0
        log_expected = log_comb - log2(2) - log2(d)
        print(f"    x={x:3d}, S={S:4d}: log2(C(S,x))={log_comb:.1f}, "
              f"log2(2d)={log2(2*d):.1f}, log2(expected)={log_expected:.1f}")


# ═══════════════════════════════════════════════════════════════════════════
# PART 3: ENTROPY / DENSITY ARGUMENT
# ═══════════════════════════════════════════════════════════════════════════

def part3_entropy_density():
    """
    Estimate density of cycle-compatible vectors and whether it goes to 0.
    """
    print("\n\n" + "=" * 80)
    print("PART 3: ENTROPY / DENSITY ARGUMENT")
    print("=" * 80)

    # 3a. Exact counts for small (S, x)
    print("\n--- 3a. Exact cycle candidate counts ---")
    results = []

    for x in range(2, 12):
        S_min = int(math.ceil(x * log2(3))) + 1
        for S in range(S_min, min(S_min + 8, 30)):
            d = 2 ** S - 3 ** x
            if d <= 0:
                continue

            total = comb(S, x)
            if total > 200000:
                continue

            candidates = 0
            for positions in combinations(range(S), x):
                g = compute_g(positions, x)
                if g % d != 0:
                    continue
                q = g // d
                if q % 2 != 1 or q < 3:
                    continue
                is_per, _ = is_periodic_vector(positions, S)
                if is_per:
                    continue
                candidates += 1

            density = candidates / total if total > 0 else 0
            results.append((x, S, d, total, candidates, density))
            if candidates > 0:
                print(f"  x={x:2d}, S={S:3d}: d={d:10d}, C(S,x)={total:8d}, "
                      f"candidates={candidates}, density={density:.2e}")
            elif total <= 50000:
                print(f"  x={x:2d}, S={S:3d}: d={d:10d}, C(S,x)={total:8d}, "
                      f"candidates=0")

    # 3b. For larger (S,x), use random sampling
    print("\n--- 3b. Random sampling for larger (S, x) ---")

    for x in range(5, 20):
        S_min = int(math.ceil(x * log2(3))) + 1
        for S_offset in range(1, 4):
            S = S_min + S_offset
            d = 2 ** S - 3 ** x
            if d <= 0:
                continue

            n_samples = 100000
            n_div = 0
            n_odd = 0
            n_ge3 = 0

            for _ in range(n_samples):
                # Random sorted positions
                positions = sorted(random.sample(range(S), x))
                g = compute_g(tuple(positions), x)
                if g % d == 0:
                    n_div += 1
                    q = g // d
                    if q % 2 == 1:
                        n_odd += 1
                        if q >= 3:
                            n_ge3 += 1

            est_prob = n_div / n_samples
            est_odd = n_odd / n_samples
            est_ge3 = n_ge3 / n_samples
            print(f"  x={x:2d}, S={S:3d}: P(d|g)={est_prob:.6f} "
                  f"(expected ~{1/d:.6f}), "
                  f"P(odd q)={est_odd:.6f}, P(q>=3)={est_ge3:.6f} "
                  f"[{n_samples} samples]")

    # 3c. Theoretical density bound
    print("\n--- 3c. Theoretical density bound ---")
    print("""
  HEURISTIC DENSITY FORMULA:

  Number of cycle candidates ~ C(S,x) / d  (divisibility by d)
                              * 1/2          (odd quotient)
                              * f(S,x)       (aperiodic fraction)

  Key: C(S,x) / d = C(S,x) / (2^S - 3^x)

  For S ~ 2x (average gap = 2 in cycles):
    C(2x, x) ~ 4^x / sqrt(pi*x)  (Stirling)
    d = 2^{2x} - 3^x = 4^x - 3^x = 4^x(1 - (3/4)^x)

  So: C(2x,x) / d ~ 4^x/sqrt(pi*x) / (4^x(1-(3/4)^x))
                    = 1 / (sqrt(pi*x) * (1-(3/4)^x))
                    ~ 1 / sqrt(pi*x)   as x -> infinity

  CONCLUSION: The expected number of candidates ~ 1/(2*sqrt(pi*x))
  This goes to 0 as x -> infinity!

  But this is a HEURISTIC, not a proof. The difficulty: g(v) mod d is
  NOT uniformly distributed (g has strong structure).
""")

    # Verify the heuristic
    print("  Verification of heuristic C(2x,x)/d:")
    for x in range(2, 25):
        S = 2 * x
        d = 2 ** S - 3 ** x
        if d <= 0:
            continue
        ratio = comb(S, x) / d
        heuristic = 1 / math.sqrt(math.pi * x)
        print(f"    x={x:3d}: C({S},{x})/d = {ratio:.6f}, "
              f"1/sqrt(pi*x) = {heuristic:.6f}, "
              f"ratio/heuristic = {ratio/heuristic:.4f}")


# ═══════════════════════════════════════════════════════════════════════════
# PART 4: A_m GROWTH RATE ANALYSIS
# ═══════════════════════════════════════════════════════════════════════════

def part4_growth_rate():
    """
    Study A_{x-1} / 3^{x-1} and its implications for cycle existence.
    """
    print("\n\n" + "=" * 80)
    print("PART 4: A_m GROWTH RATE vs d CONSTRAINT")
    print("=" * 80)

    # 4a. Compute A_{x-1} / 3^{x-1} for various k
    print("\n--- 4a. Growth rate R(k,x) = A_{x-1} / (k * 2^S) ---")
    print("  For a cycle: R(k,x) = 1 exactly (since A_{x-1} = k * 2^S)")

    for k in [3, 5, 7, 9, 11, 13, 27, 31, 127]:
        print(f"\n  k={k}:")
        b = k
        cum_val = 0
        for m in range(20):
            val = v2(3 * b + 1)
            cum_val += val
            b_next = collatz_odd(b)

            # A_m ~ 3^{m+1} * k * product of corrections
            # For a cycle at step x: A_{x-1} = k * 2^S where S = cum_val at x
            # So A_{x-1} / (k * 2^S) = 1 iff cycle

            # Compute: B_m / k (if this returns to 1, we have a cycle)
            ratio_B = b_next / k

            if m < 12:
                print(f"    m={m:2d}: B_m={b_next:10d}, v2={val}, cum_S={cum_val:4d}, "
                      f"B_m/k={ratio_B:.6f}")

            b = b_next
            if b == 1:
                print(f"    -> Reached 1 at step {m+1}")
                break

    # 4b. The KEY: for a cycle, B_{x-1} must equal k.
    # Study how B_m/k evolves: does it tend to grow or shrink?
    print("\n--- 4b. B_m/k trajectory analysis ---")
    print("  Question: does B_m/k tend away from 1?")

    growth_data = []
    for k in range(3, 500, 2):
        b = k
        ratios = [1.0]
        for m in range(100):
            b = collatz_odd(b)
            ratios.append(b / k)
            if b == 1:
                break

        # Check if ratio ever comes close to 1 again (excluding m=0)
        min_distance_from_1 = min(abs(r - 1) for r in ratios[1:]) if len(ratios) > 1 else float('inf')
        closest_step = min(range(1, len(ratios)), key=lambda i: abs(ratios[i] - 1)) if len(ratios) > 1 else -1

        growth_data.append({
            'k': k,
            'orbit_len': len(ratios) - 1,
            'min_dist': min_distance_from_1,
            'closest_step': closest_step,
            'closest_ratio': ratios[closest_step] if closest_step >= 0 else None,
        })

    # How close does B_m/k get to 1?
    closest_approaches = sorted(growth_data, key=lambda d: d['min_dist'])
    print("\n  Top 15 closest approaches of B_m/k to 1 (excluding m=0):")
    for d in closest_approaches[:15]:
        print(f"    k={d['k']:5d}: closest ratio={d['closest_ratio']:.8f} at step {d['closest_step']}, "
              f"distance={d['min_dist']:.8f}")

    # 4c. Growth rate of A_m / 3^m
    print("\n--- 4c. A_m / 3^m growth ---")
    print("  A_{m+1} = 3*A_m + 2^{v2(A_m)}")
    print("  So A_{m+1}/3^{m+1} = A_m/3^m + 2^{v2(A_m)}/3^{m+1}")
    print("  Define alpha_m = A_m / 3^m. Then:")
    print("  alpha_{m+1} = alpha_m + 2^{v2(A_m)} / 3^{m+1}")
    print("  Since alpha_m is MONOTONICALLY INCREASING (adding positive terms),")
    print("  alpha_m -> limit (or infinity).")

    for k in [3, 7, 27, 127]:
        A = 3 * k + 1
        alphas = [A / 3]
        for m in range(1, 30):
            correction = 2 ** v2(A)
            A = 3 * A + correction
            alphas.append(A / 3 ** (m + 1))

        print(f"\n  k={k}: alpha_m = A_m/3^m")
        for m in range(min(15, len(alphas))):
            print(f"    m={m:2d}: alpha = {alphas[m]:.10f}")

        # Check: alpha is increasing
        is_increasing = all(alphas[i] < alphas[i + 1] for i in range(len(alphas) - 1))
        print(f"    Monotonically increasing: {is_increasing}")

    # 4d. CRITICAL INSIGHT: For a cycle at (k, x, S):
    #   A_{x-1} = k * 2^S. So alpha_{x-1} = A_{x-1}/3^{x-1} = k*2^S/3^{x-1}.
    #   Also alpha_0 = A_0/3 = (3k+1)/3 = k + 1/3.
    #   And alpha_m is increasing.
    #   So: k + 1/3 < alpha_1 < ... < alpha_{x-1} = k * 2^S / 3^{x-1}.
    #   This gives: k + 1/3 < k * 2^S / 3^{x-1}
    #   => (k + 1/3) * 3^{x-1} < k * 2^S
    #   => k*3^{x-1} + 3^{x-2} < k*2^S
    #   => 3^{x-2} < k*(2^S - 3^{x-1}) = k * (2^S - 3*3^{x-2})  ... hmm
    print("\n--- 4d. Alpha monotonicity constraint on cycles ---")
    print("""
  For a hypothetical cycle (k, x, S):
    alpha_0 = (3k+1)/3 = k + 1/3
    alpha_{x-1} = k * 2^S / 3^{x-1}

  Since alpha is strictly increasing:
    k + 1/3 < k * 2^S / 3^{x-1}
    => 3^{x-1}(k + 1/3) < k * 2^S
    => k * 3^{x-1} + 3^{x-2} < k * 2^S
    => 3^{x-2} < k * (2^S - 3^{x-1})

  But 2^S - 3^{x-1} = 2^S - 3^x/3 = (3*2^S - 3^x) / 3 = (3d + 2*3^x + ... )

  Actually: d = 2^S - 3^x, so 2^S - 3^{x-1} = d + 3^x - 3^{x-1} = d + 2*3^{x-1}
  => 3^{x-2} < k * (d + 2*3^{x-1}) = k*d + 2k*3^{x-1}

  Since k = g(v)/d and g(v) <= g_max:
  g_max = sum_{j=0}^{x-1} 3^{x-1-j} * 2^{S-x+j}
        = 3^{x-1} * 2^{S-x} * sum (2/3)^j  [geometric sum]
        ~ 3^{x-1} * 2^{S-x} * 3 * (1 - (2/3)^x) for large x
        ~ 3^x * 2^{S-x}

  So k_max ~ 3^x * 2^{S-x} / d = 3^x * 2^{S-x} / (2^S - 3^x)

  For S = 2x: k_max ~ 3^x * 2^x / (4^x - 3^x) = (3/2)^x * 4^x / (4^x - 3^x)
                     ~ (3/2)^x / (1 - (3/4)^x) ~ (3/2)^x

  So k_max grows as (3/2)^x. This is EXPONENTIAL.
  The Steiner bound says k >= 2^{40} for x >= 70. Let's check:
  (3/2)^70 ~ 2^{40.8}. Consistent!
""")

    # Compute k_max bounds
    print("  k_max bounds vs Steiner-like lower bounds:")
    for x in range(2, 30):
        S = 2 * x
        d = 2 ** S - 3 ** x
        if d <= 0:
            S += 1
            d = 2 ** S - 3 ** x
        if d <= 0:
            continue

        # Compute actual k_max
        g_max_val = sum(3 ** (x - 1 - j) * 2 ** (S - x + j) for j in range(x))
        k_max = g_max_val // d

        print(f"    x={x:3d}: S={S}, d={d}, k_max={k_max}, "
              f"log2(k_max)={log2(k_max):.2f}, "
              f"(3/2)^x={1.5**x:.1f}, log2((3/2)^x)={x*log2(1.5):.2f}")


# ═══════════════════════════════════════════════════════════════════════════
# PART 5: CROSS-CUTTING PATTERNS & NOVEL DISCOVERIES
# ═══════════════════════════════════════════════════════════════════════════

def part5_novel_patterns():
    """
    Combine all angles to find structural impossibilities.
    """
    print("\n\n" + "=" * 80)
    print("PART 5: CROSS-CUTTING PATTERNS & NOVEL DISCOVERIES")
    print("=" * 80)

    # 5a. THE v2(3k+1) CONSTRAINT FOR CYCLES
    print("\n--- 5a. The v2(3k+1) constraint ---")
    print("""
  For a cycle through k: the orbit is k, B_1=T(k), B_2=T^2(k), ..., B_{x-1}=T^{x-1}(k), then B_x=k.
  The valuations are v_m = v2(3*B_m + 1) for m = 0,...,x-1 where B_0 = T(k)...

  Wait: B_0 = odd(3k+1) = T(k). And B_{x-1} = T^x(k) = k.
  So the orbit of T starting from T(k) returns to k after x-1 more steps.

  The sum S = v2(3k+1) + v2(3*T(k)+1) + ... + v2(3*T^{x-1}(k)+1)

  And d = 2^S - 3^x > 0 requires S > x*log2(3).
  Also: k = g(v)/d >= 3.

  NEW ANGLE: What are the v2 constraints?
  For k = 3 mod 8: v2(3k+1) = v2(10) = 1... no. 3*3+1 = 10, v2(10) = 1.
  For k = 1 mod 8: v2(3+1) = 2. For k = 5 mod 8: v2(16) = 4.

  Actually: 3k+1 mod 8 depends on k mod 8.
  k=1: 3+1=4, v2=2. k=3: 9+1=10, v2=1. k=5: 15+1=16, v2=4. k=7: 21+1=22, v2=1.
""")

    # Study v2(3k+1) distribution
    print("  v2(3k+1) for k mod 16:")
    for k_mod in range(1, 16, 2):
        val = v2(3 * k_mod + 1)
        print(f"    k = {k_mod} mod 16: v2(3k+1) = {val}")

    # 5b. FORBIDDEN CONFIGURATIONS via the alpha monotonicity + divisibility
    print("\n--- 5b. Simultaneous constraints: alpha + divisibility + aperiodicity ---")

    # For each small (S, x), enumerate ALL possible k values and check ALL constraints
    print("\n  Exhaustive search for cycle candidates:")
    total_candidates = 0

    for x in range(2, 15):
        S_min = int(math.ceil(x * log2(3))) + 1
        for S in range(S_min, min(S_min + 12, 40)):
            d = 2 ** S - 3 ** x
            if d <= 0:
                continue
            if d % 2 == 0:
                continue  # d must be odd for k to be odd (since g(v) = k*d and g(v) parity...)
                          # Actually g(v) has terms 3^{...}*2^{...}, all even except possibly the first.
                          # Let me not filter here.

            # Maximum k
            g_max_val = sum(3 ** (x - 1 - j) * 2 ** (S - x + j) for j in range(x))
            k_max = g_max_val // d

            # For each candidate k (odd, >= 3), check if the Collatz orbit returns
            n_odd_k = 0
            n_returns = 0
            for k in range(3, min(k_max + 1, 10001), 2):
                n_odd_k += 1
                # Check T^x(k) = k
                b = k
                for step in range(x):
                    b = collatz_odd(b)
                if b == k:
                    n_returns += 1
                    # Also check: the D-sequence must be valid (strictly increasing, < S)
                    # and the vector must be aperiodic
                    curr = k
                    positions = []
                    cum = 0
                    valid = True
                    for m in range(x):
                        val = v2(3 * curr + 1)
                        positions.append(cum)
                        cum += val
                        curr = collatz_odd(curr)
                    actual_S = cum

                    if actual_S == S:
                        is_per, per = is_periodic_vector(positions, S)
                        print(f"  *** x={x}, S={S}, k={k}: T^x(k)=k, S_actual={actual_S}, "
                              f"periodic={is_per} (p={per})")
                        if not is_per:
                            total_candidates += 1
                            print(f"      !!! VALID CYCLE CANDIDATE !!!")

            if n_returns > 0:
                print(f"  x={x}, S={S}: {n_returns} return(s) among {n_odd_k} tested")

    print(f"\n  TOTAL VALID CYCLE CANDIDATES FOUND: {total_candidates}")

    # 5c. THE NOVEL INSIGHT: Combining alpha-monotonicity with gap analysis
    print("\n--- 5c. Novel: Alpha-gap correlation ---")
    print("""
  INSIGHT: alpha_m = A_m / 3^m is strictly increasing.
  The INCREMENT is delta_m = 2^{v2(A_m)} / 3^{m+1} = 2^{D_m} / 3^{m+1}
  where D_m is the m-th position.

  For alpha to be EXACTLY k*2^S/3^{x-1} at step x-1 (cycle condition):
    sum_{m=0}^{x-2} delta_m = k*2^S/3^{x-1} - (k + 1/3)

  This is a DIOPHANTINE constraint on the positions D_0 < D_1 < ... < D_{x-1}.

  Combined with g(v) = k*d:
    sum_{j=0}^{x-1} 3^{x-1-j} * 2^{D_j} = k * (2^S - 3^x)

  These are TWO constraints on x variables (D_0,...,D_{x-1}), both of which
  are weighted sums with EXPONENTIAL coefficients (3^{...} and 2^{...}).

  The question: does the monotonicity D_0 < D_1 < ... < D_{x-1} < S,
  combined with the exponential weights, make the system overdetermined?
""")

    # 5d. RATIO TEST: g(v) / d mod 2 analysis
    print("\n--- 5d. Parity of g(v)/d: a structural obstruction? ---")

    for x in range(2, 9):
        S_min = int(math.ceil(x * log2(3))) + 1
        for S in range(S_min, S_min + 5):
            d = 2 ** S - 3 ** x
            if d <= 0 or comb(S, x) > 100000:
                continue

            n_div = 0
            n_even_q = 0
            n_odd_q = 0

            for positions in combinations(range(S), x):
                g = compute_g(positions, x)
                if g % d == 0:
                    n_div += 1
                    q = g // d
                    if q % 2 == 0:
                        n_even_q += 1
                    else:
                        n_odd_q += 1

            if n_div > 0:
                parity_ratio = n_odd_q / n_div
                print(f"  (S={S:2d}, x={x}): d={d:6d}, g|d in {n_div:4d} cases, "
                      f"odd_q={n_odd_q} ({100*parity_ratio:.1f}%), "
                      f"even_q={n_even_q} ({100*(1-parity_ratio):.1f}%)")

    # 5e. THE BIG PICTURE: combine density + parity + aperiodicity
    print("\n--- 5e. Combined exclusion power ---")
    print("""
  SUMMARY OF CONSTRAINTS (each removes candidates):

  1. DIVISIBILITY: g(v) ≡ 0 mod d removes ~(1-1/d) fraction
     Power: HUGE for large d, but d can be small for S close to x*log2(3)

  2. ODD QUOTIENT: g(v)/d must be odd removes ~50% of remaining
     Power: MODERATE, but varies (see 5d parity bias)

  3. QUOTIENT ≥ 3: g(v)/d ≥ 3 removes k=1 case (always periodic by T196)
     Power: SMALL (most valid quotients are ≥ 3 for large enough S)

  4. APERIODICITY: vector must not be periodic
     Power: SMALL for large S/x, but CRUCIAL for small x

  5. COLLATZ RETURN: T^x(k) = k (the orbit must actually return)
     Power: THIS IS THE HARD ONE — equivalent to the full conjecture

  NEW ANGLE #1 (Gap Analysis):
     For a cycle, D-gaps are periodic (repeat the cycle's valuation pattern).
     Periodic gap sequences often => periodic vectors (excluded by 4).
     If we could show: for ALL possible gap patterns consistent with a cycle,
     the resulting vector is periodic, we'd have a proof!

  NEW ANGLE #2 (Alpha-Monotonicity):
     alpha_m = A_m/3^m is strictly increasing with computable increments.
     For a cycle: alpha jumps from k+1/3 to exactly k*2^S/3^{x-1}.
     The increments 2^{D_m}/3^{m+1} must sum to exactly this difference.
     With exponentially decaying weights and increasing D_m, this is
     a very constrained Diophantine problem.

  NEW ANGLE #3 (Modular Cascade):
     For each prime p dividing d, g(v) ≡ 0 mod p is a separate constraint.
     If d has many prime factors, the constraints compound (CRT).
     But d = 2^S - 3^x may have very few prime factors for specific (S,x).
     QUESTION: Is there a lower bound on omega(d) (number of prime factors)?
""")

    # 5f. Study omega(d) = number of distinct prime factors of d
    print("\n--- 5f. Number of prime factors of d = 2^S - 3^x ---")

    for x in range(2, 30):
        S_min = int(math.ceil(x * log2(3))) + 1
        for S in range(S_min, S_min + 3):
            d = 2 ** S - 3 ** x
            if d <= 0:
                continue

            # Count prime factors
            temp = d
            factors = set()
            p = 2
            while p * p <= temp and p < 10000:
                while temp % p == 0:
                    factors.add(p)
                    temp //= p
                p += 1
            if temp > 1:
                factors.add(temp)

            print(f"    x={x:2d}, S={S:3d}: d={d}, omega(d)={len(factors)}, "
                  f"factors={sorted(factors)[:8]}{'...' if len(factors) > 8 else ''}")


# ═══════════════════════════════════════════════════════════════════════════
# PART 6: THE BOLDEST IDEA — PERIODIC GAPS => PERIODIC VECTOR?
# ═══════════════════════════════════════════════════════════════════════════

def part6_periodic_gap_theorem():
    """
    THE MOST PROMISING ANGLE:
    For a cycle, the D-gaps form a periodic sequence (period x).
    When does this force the vector to be periodic (and thus excluded)?
    """
    print("\n\n" + "=" * 80)
    print("PART 6: PERIODIC GAPS => PERIODIC VECTOR?")
    print("=" * 80)

    print("""
  SETUP: In a cycle of length x through k:
    - B_0 = T(k), B_1 = T^2(k), ..., B_{x-1} = T^x(k) = k
    - Gaps: g_m = v2(3*B_m + 1) for m = 0,...,x-1
    - S = g_0 + g_1 + ... + g_{x-1}
    - Positions: D_0 = 0 (... actually D_0 = v2(3k+1), then D_1 = D_0 + g_0, etc.)

  Wait — let me be precise. In the Junction framework:
    - The binary vector v ∈ {0,1}^S has 1s at positions e_0 < e_1 < ... < e_{x-1}
    - In the descent, D_m = e_m
    - g_m = D_{m+1} - D_m for m = 0,...,x-2, and the "last gap" is S - D_{x-1}

  For the Collatz orbit: D_0 = 0 isn't right. Let me recompute.

  Actually the positions come from the cumulative valuations:
    D_0 is determined by the descent. For a cycle starting at k:
    The first gap is v2(3k+1). And D_0 = v2(A_0) where A_0 = 3k+1.

  Let me just work with the GAP SEQUENCE (g_0,...,g_{x-1}) and test periodicity.
""")

    # For a hypothetical cycle: gaps = (g_0,...,g_{x-1}), S = sum(gaps).
    # Positions: D_0 = 0, D_1 = g_0, D_2 = g_0+g_1, ..., D_{x-1} = sum(g_0..g_{x-2}).
    # The vector has 1s at D_0,...,D_{x-1} in {0,...,S-1}.
    # Vector is periodic with period p iff for all i: D_i + p mod S ∈ {D_0,...,D_{x-1}}.

    # THEOREM ATTEMPT: If all gaps are equal, vector is periodic.
    # What about ALMOST equal? What about exactly 2 distinct values?

    print("\n--- 6a. Systematic test: gap sequences with 2 distinct values ---")

    results_2val = []
    for x in range(3, 12):
        for a in range(1, 8):
            for b in range(a + 1, 8):
                # Try all distributions of a's and b's in a sequence of length x
                for n_a in range(1, x):
                    n_b = x - n_a
                    S = n_a * a + n_b * b

                    # Try a few permutations of the gap sequence
                    # Most relevant: the "canonical" ones
                    # Pattern 1: all a's first, then b's
                    gaps = [a] * n_a + [b] * n_b
                    positions = [0]
                    for g in gaps[:-1]:
                        positions.append(positions[-1] + g)

                    is_per, per = is_periodic_vector(positions, S)
                    if not is_per:
                        results_2val.append((x, a, b, n_a, n_b, S, gaps, positions))

                    # Pattern 2: alternating (if possible)
                    if n_a == n_b or abs(n_a - n_b) == 1:
                        gaps2 = []
                        ia, ib = 0, 0
                        for i in range(x):
                            if i % 2 == 0 and ia < n_a:
                                gaps2.append(a)
                                ia += 1
                            elif ib < n_b:
                                gaps2.append(b)
                                ib += 1
                            elif ia < n_a:
                                gaps2.append(a)
                                ia += 1
                        if len(gaps2) == x:
                            positions2 = [0]
                            for g in gaps2[:-1]:
                                positions2.append(positions2[-1] + g)
                            is_per2, per2 = is_periodic_vector(positions2, S)
                            if not is_per2:
                                results_2val.append((x, a, b, n_a, n_b, S, gaps2, positions2))

    print(f"  Found {len(results_2val)} aperiodic configurations with 2 gap values")
    if results_2val:
        print("  First 20:")
        for (x, a, b, na, nb, S, gaps, pos) in results_2val[:20]:
            print(f"    x={x}, gaps in {{{a},{b}}}, ({na}x{a}+{nb}x{b}), S={S}: "
                  f"gaps={gaps}, aperiodic!")

    # 6b. THE REAL TEST: for actual Collatz orbits, compute the gap sequence
    # and check if the HYPOTHETICAL periodically-extended vector would be periodic
    print("\n--- 6b. Collatz orbits: gap sequences and vector periodicity ---")

    for k in range(3, 200, 2):
        b = k
        gaps = []
        orbit = [k]
        for step in range(300):
            val = v2(3 * b + 1)
            gaps.append(val)
            b = collatz_odd(b)
            orbit.append(b)
            if b == 1:
                break

        if b != 1 or len(gaps) < 3:
            continue

        x = len(gaps)
        S = sum(gaps)
        positions = [0]
        for g in gaps[:-1]:
            positions.append(positions[-1] + g)

        is_per, per = is_periodic_vector(positions, S)

        # Count distinct gap values
        n_distinct = len(set(gaps))
        gap_dist = Counter(gaps)

        if k <= 51 or (k % 50 == 1 and k <= 301):
            print(f"  k={k:5d}: x={x:3d}, S={S:5d}, "
                  f"distinct_gaps={n_distinct}, "
                  f"gap_dist={dict(sorted(gap_dist.items()))}, "
                  f"periodic={'YES(p='+str(per)+')' if is_per else 'NO'}")

    # 6c. KEY THEORETICAL QUESTION
    print("\n--- 6c. When can periodic gap sequence => aperiodic vector? ---")
    print("""
  For a CYCLE of length x, the gap sequence is EXACTLY:
    (g_0, g_1, ..., g_{x-1}) with g_m = v2(3*B_m + 1)
  and S = sum of these gaps.

  The positions are: D_0 = 0, D_m = sum_{i=0}^{m-1} g_i.

  OBSERVATION: The vector is periodic with period p iff
    {D_0, ..., D_{x-1}} is invariant under +p mod S.

  This means: for each D_m, (D_m + p) mod S = D_{sigma(m)} for some permutation sigma.

  If gcd(p, S) = p (i.e., p | S), and x = S/p, then we need EXACTLY one
  position per residue class mod p among {0, p, 2p, ..., (x-1)p}.

  But D_m = sum of first m gaps. For this to be periodic:
    D_m ≡ D_m mod (S/p)... this is complicated.

  SIMPLER QUESTION: when is gcd(S, x) > 1?
  If gcd(S, x) = c > 1, then p = S/c could be a period if positions align.
  For a cycle: S/x = average gap. If S/x = s (integer), period s is possible.

  CRUCIAL: For k=1, S/x = 2 (integer), period = 2. ALWAYS periodic.
  For k >= 3 in a cycle: S/x = average(v2(3*B_m+1)) over the orbit.
  If this is an INTEGER, periodicity is POSSIBLE (not guaranteed).
  If NOT an integer, period S/gcd(S,x) requires more positions per period.
""")

    # Test: for what fraction of (S, x) pairs is gcd(S, x) > 1?
    print("  gcd(S, x) analysis for S in [x*log2(3)+1, ..., 3x]:")
    for x in range(2, 20):
        S_min = int(math.ceil(x * log2(3))) + 1
        S_max = 3 * x
        gcds = []
        for S in range(S_min, S_max + 1):
            d = 2 ** S - 3 ** x
            if d <= 0:
                continue
            gcds.append((S, gcd(S, x)))

        gcd_gt1 = sum(1 for _, g in gcds if g > 1)
        print(f"    x={x:2d}: {gcd_gt1}/{len(gcds)} have gcd(S,x)>1: "
              f"{[(S, g) for S, g in gcds if g > 1][:6]}")


# ═══════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════

def main():
    print("*" * 80)
    print("R180 — INNOVATION: NOVEL APPROACHES TO COLLATZ CYCLE EXCLUSION")
    print("*" * 80)
    print()

    random.seed(42)  # Reproducibility

    stab_data = part1_stabilization()
    part2_modular_cascade()
    part3_entropy_density()
    part4_growth_rate()
    part5_novel_patterns()
    part6_periodic_gap_theorem()

    # FINAL SYNTHESIS
    print("\n\n" + "*" * 80)
    print("FINAL SYNTHESIS: MOST PROMISING DIRECTIONS")
    print("*" * 80)
    print("""
  RANKING OF APPROACHES BY NOVELTY AND FEASIBILITY:

  1. ★★★★★ PERIODIC GAPS => PERIODIC VECTOR (Part 6)
     The most promising NEW angle. For a cycle, the D-gap sequence is
     deterministic from the orbit. If we can show that for k >= 3,
     the resulting gap pattern ALWAYS produces a periodic vector,
     we'd exclude all non-trivial cycles.
     STATUS: Needs deeper analysis of when gap periodicity forces
     vector periodicity. The gcd(S,x) > 1 condition is necessary
     but not sufficient.

  2. ★★★★☆ ALPHA-MONOTONICITY CONSTRAINT (Part 4)
     alpha_m = A_m/3^m is strictly increasing with known increments.
     For a cycle, the total increment must hit an exact target.
     This is a Diophantine equation with exponential coefficients.
     STATUS: The constraint is real but hard to turn into a proof.
     Could combine with modular analysis.

  3. ★★★☆☆ DENSITY / ENTROPY ARGUMENT (Part 3)
     Expected number of cycle candidates ~ 1/sqrt(pi*x) -> 0.
     This is a strong HEURISTIC but not a proof (doesn't rule out
     rare structured vectors).
     STATUS: Could be made rigorous if g(v) mod d were shown to be
     "sufficiently random" (equidistribution result needed).

  4. ★★★☆☆ MODULAR CASCADE (Part 2)
     Each prime factor of d gives a constraint on g(v).
     The CRT makes these compound. But d may have few prime factors.
     STATUS: Useful for specific (S,x) but hard to make universal.

  5. ★★☆☆☆ STABILIZATION INCOMPATIBILITY (Part 1)
     Real trajectories stabilize (gaps -> 2). Cycles can't stabilize.
     But this is essentially restating that cycles don't reach 1.
     STATUS: The gap variance analysis is interesting but circular.

  RECOMMENDED NEXT STEP:
  Focus on Part 6 — the "periodic gaps => periodic vector" angle.
  Specifically:
  (a) Prove: if gcd(S, x) | S and the gap sequence has certain
      regularity properties, the vector is necessarily periodic.
  (b) Show: for any odd k >= 3, the Collatz orbit's valuation
      pattern satisfies these regularity conditions.
  (c) This would give: cycle => periodic vector => excluded by
      Junction Theorem => no cycle. QED.
""")


if __name__ == '__main__':
    main()
