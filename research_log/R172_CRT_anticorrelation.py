#!/usr/bin/env python3
"""
R172 — CRT Anticorrelation Analysis for Collatz k-cycles
=========================================================
For k-cycles: corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}
with 0 <= B_0 <= B_1 <= ... <= B_{k-1} = S-k  (monotone compositions)
d = 2^S - 3^k, and we need corrSum ≡ 0 mod d.

CRITICAL OBSERVATION from first run:
  N_0(d) is NOT always 0 at S_min! For k=3,4,5,10,13,14, N_0(d)=1.
  The single survivor in those cases must be analyzed — is it the "trivial"
  composition (all B_j forced), and does it yield n_0 > 0 (positive integer)?

This script:
1. Computes N_0(d) for k=3..14 at S_min
2. When N_0(d) > 0, identifies the survivor and checks if it gives a valid cycle
3. For k where N_0(d) = 0, performs full CRT anticorrelation analysis
4. Also checks S = S_min, S_min+1, ..., S_min+5 to see the pattern across S
5. Looks for universal patterns in the CRT elimination mechanism
"""

import math
from itertools import combinations
from collections import defaultdict
from sympy import factorint

def S_min(k):
    """Minimal S such that 2^S > 3^k."""
    S = math.ceil(k * math.log2(3))
    if 2**S <= 3**k:
        S += 1
    return S

def enumerate_monotone_compositions(k, S):
    """
    Enumerate all monotone compositions B = (B_0, ..., B_{k-1})
    with 0 <= B_0 <= B_1 <= ... <= B_{k-1} = S - k.
    """
    top = S - k
    if top < 0:
        return []
    results = []
    def backtrack(idx, prev, current):
        if idx == k - 1:
            current.append(top)
            results.append(tuple(current))
            current.pop()
            return
        for val in range(prev, top + 1):
            current.append(val)
            backtrack(idx + 1, val, current)
            current.pop()
    backtrack(0, 0, [])
    return results

def corrSum(B, k):
    """Compute corrSum for a given monotone composition B."""
    s = 0
    for j in range(k):
        s += pow(3, k - 1 - j) * pow(2, B[j])
    return s

def corrSum_mod(B, k, m):
    """Compute corrSum mod m efficiently."""
    s = 0
    for j in range(k):
        s = (s + pow(3, k - 1 - j, m) * pow(2, B[j], m)) % m
    return s

def n0_from_composition(B, k, S):
    """
    Given a monotone composition B with corrSum ≡ 0 mod d,
    compute n_0 = corrSum / d. For a valid cycle, need n_0 >= 1 and odd.
    """
    d = 2**S - 3**k
    cs = corrSum(B, k)
    if cs % d != 0:
        return None
    n0 = cs // d
    return n0

def multiplicative_order(a, n):
    """Multiplicative order of a mod n."""
    if math.gcd(a, n) != 1:
        return None
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None
    return order

def analyze_k_full(k, S, verbose=True):
    """Full CRT anticorrelation analysis for given k and S."""
    d = 2**S - 3**k
    if d <= 0:
        return None

    factors = factorint(d)
    primes = sorted(factors.keys())
    prime_powers = {p: p**factors[p] for p in primes}

    comps = enumerate_monotone_compositions(k, S)
    C_total = len(comps)

    if C_total == 0:
        return None

    # For each prime p|d, compute S_p
    S_p = {}
    for p in primes:
        S_p[p] = set()
        for i, B in enumerate(comps):
            if corrSum_mod(B, k, p) == 0:
                S_p[p].add(i)

    # Full d check
    S_d = set()
    survivors = []
    for i, B in enumerate(comps):
        if corrSum_mod(B, k, d) == 0:
            S_d.add(i)
            n0 = n0_from_composition(B, k, S)
            survivors.append((B, n0))

    # Pairwise intersections
    pair_data = {}
    for p1, p2 in combinations(primes, 2):
        inter = S_p[p1] & S_p[p2]
        expected = len(S_p[p1]) * len(S_p[p2]) / C_total if C_total > 0 else 0
        ratio = len(inter) / expected if expected > 0 else float('inf')
        pair_data[(p1, p2)] = {
            'inter_size': len(inter),
            'expected': expected,
            'ratio': ratio,
            'inter_set': inter
        }

    # CRT elimination chain (greedy)
    remaining = set(range(C_total))
    chain = [('ALL', C_total)]
    available = list(primes)
    while remaining and available:
        best_p = None
        best_surviving = None
        best_count = len(remaining) + 1
        for p in available:
            surv = remaining & S_p[p]
            if len(surv) < best_count:
                best_count = len(surv)
                best_p = p
                best_surviving = surv
        remaining = best_surviving
        available.remove(best_p)
        chain.append((best_p, len(remaining)))

    # Minimal killing set
    killing_set = None
    # Singles
    for p in primes:
        if len(S_p[p]) == 0:
            killing_set = (p,)
            break
    # Pairs
    if killing_set is None:
        for p1, p2 in combinations(primes, 2):
            if pair_data[(p1, p2)]['inter_size'] == 0:
                killing_set = (p1, p2)
                break
    # Triples+
    if killing_set is None:
        for size in range(3, len(primes) + 1):
            found = False
            for subset in combinations(primes, size):
                inter = set(range(C_total))
                for p in subset:
                    inter &= S_p[p]
                    if not inter:
                        break
                if not inter:
                    killing_set = subset
                    found = True
                    break
            if found:
                break

    return {
        'k': k, 'S': S, 'd': d,
        'factors': factors, 'primes': primes,
        'C_total': C_total,
        'N0_d': len(S_d),
        'survivors': survivors,
        'S_p_sizes': {p: len(S_p[p]) for p in primes},
        'pair_data': pair_data,
        'killing_set': killing_set,
        'chain': chain,
    }


def main():
    print("R172 — CRT Anticorrelation Analysis for Collatz k-cycles")
    print("=" * 72)

    # ===================================================================
    # PART 1: Survey k=3..14 at S_min — understand N_0(d) landscape
    # ===================================================================
    print("\n" + "=" * 72)
    print("PART 1: N_0(d) at S_min for k=3..14")
    print("=" * 72)

    for k in range(3, 15):
        S = S_min(k)
        d = 2**S - 3**k
        if d <= 0:
            print(f"  k={k}: d <= 0, skip")
            continue

        n_comps = math.comb(S - k + k - 1, k - 1)
        if n_comps > 2_000_000:
            print(f"  k={k}: S={S}, d={d}, ~{n_comps} compositions — too many")
            continue

        r = analyze_k_full(k, S)
        if r is None:
            continue

        factors = r['factors']
        factor_str = " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(factors.items()))

        print(f"\n  k={k}, S={S}, d={d} = {factor_str}")
        print(f"    #compositions = {r['C_total']}, N_0(d) = {r['N0_d']}")

        if r['N0_d'] > 0:
            for B, n0 in r['survivors']:
                cs = corrSum(B, k)
                # Check if n0 is odd and positive
                valid = "VALID CYCLE" if (n0 is not None and n0 > 0 and n0 % 2 == 1) else "INVALID"
                if n0 is not None and n0 == 0:
                    valid = "TRIVIAL (n0=0)"
                print(f"    SURVIVOR: B={B}, corrSum={cs}, n_0={n0}  [{valid}]")

                # Verify the cycle equation: n_0 * (2^S - 3^k) = corrSum
                if n0 is not None:
                    check = n0 * d == cs
                    print(f"      Verify: {n0} * {d} = {n0*d}, corrSum = {cs}, match={check}")

                    # For a real k-cycle, need n_0 odd, and the a_j (odd steps) must work out
                    # The steps are: a_j = 2^{b_j} where b_j = B_j - B_{j-1} (with B_{-1}=0)
                    b_steps = [B[0]] + [B[j] - B[j-1] for j in range(1, k)]
                    a_vals = [2**b for b in b_steps]
                    print(f"      b-steps = {b_steps}, a-values = {a_vals}")

        # Per-prime info
        for p in r['primes']:
            frac = r['S_p_sizes'][p] / r['C_total']
            print(f"    p={p}: |S_p|={r['S_p_sizes'][p]}, frac={frac:.4f}, expected 1/p={1/p:.4f}")

        if r['N0_d'] == 0:
            print(f"    KILLING SET: {r['killing_set']}")
            print(f"    Chain: {r['chain']}")

    # ===================================================================
    # PART 2: For k with N_0(d)>0 at S_min, check multiple S values
    # ===================================================================
    print("\n\n" + "=" * 72)
    print("PART 2: Sweep S = S_min to S_min+10 for interesting k values")
    print("=" * 72)

    for k in [3, 4, 5, 6, 7, 8, 10, 13]:
        Sm = S_min(k)
        print(f"\n  k={k}, S_min={Sm}")
        print(f"    {'S':>4} {'d':>15} {'factorization':>30} {'#comps':>8} {'N0(d)':>6}")
        print(f"    {'-'*70}")

        for S in range(Sm, Sm + 11):
            d = 2**S - 3**k
            if d <= 0:
                continue

            n_comps = math.comb(S - k + k - 1, k - 1)
            if n_comps > 500_000:
                print(f"    {S:>4} {d:>15} {'(too many comps)':>30} {n_comps:>8}")
                continue

            r = analyze_k_full(k, S, verbose=False)
            if r is None:
                continue

            factors = r['factors']
            factor_str = " * ".join(f"{p}^{e}" if e > 1 else str(p) for p, e in sorted(factors.items()))
            if len(factor_str) > 30:
                factor_str = factor_str[:27] + "..."

            surv_info = ""
            if r['N0_d'] > 0:
                for B, n0 in r['survivors']:
                    odd_str = "odd" if n0 and n0 % 2 == 1 else "even"
                    surv_info += f" n0={n0}({odd_str})"
            else:
                ks = r['killing_set']
                if ks:
                    surv_info = f" kill={ks}"

            print(f"    {S:>4} {d:>15} {factor_str:>30} {r['C_total']:>8} {r['N0_d']:>6}{surv_info}")

    # ===================================================================
    # PART 3: Deep CRT analysis for k where N_0(d)=0
    # ===================================================================
    print("\n\n" + "=" * 72)
    print("PART 3: CRT Anticorrelation — Deep analysis for N_0(d)=0 cases")
    print("=" * 72)

    zero_cases = []
    for k in range(3, 15):
        Sm = S_min(k)
        # Check a few S values
        for S in range(Sm, Sm + 8):
            d = 2**S - 3**k
            if d <= 0:
                continue
            n_comps = math.comb(S - k + k - 1, k - 1)
            if n_comps > 500_000:
                continue
            r = analyze_k_full(k, S, verbose=False)
            if r and r['N0_d'] == 0 and len(r['primes']) >= 2:
                zero_cases.append(r)

    print(f"\n  Found {len(zero_cases)} cases with N_0(d)=0 and >= 2 prime factors")

    # Detailed anticorrelation analysis
    print(f"\n  {'k':>3} {'S':>3} {'d':>12} {'#p':>3} {'killing':>15} {'chain':>40}")
    print(f"  {'-'*80}")

    killing_size_hist = defaultdict(int)
    for r in zero_cases:
        ks = r['killing_set']
        ks_str = str(ks) if ks else "?"
        chain_str = " -> ".join(f"{p}:{n}" for p, n in r['chain'])
        if len(chain_str) > 40:
            chain_str = chain_str[:37] + "..."
        print(f"  {r['k']:>3} {r['S']:>3} {r['d']:>12} {len(r['primes']):>3} {ks_str:>15} {chain_str:>40}")
        if ks:
            killing_size_hist[len(ks)] += 1

    print(f"\n  Killing set size distribution: {dict(killing_size_hist)}")

    # Anticorrelation ratios
    print(f"\n  --- Anticorrelation ratios for killing pairs ---")
    print(f"  {'k':>3} {'S':>3} {'p1':>8} {'p2':>8} {'|S1|':>6} {'|S2|':>6} "
          f"{'|inter|':>7} {'expected':>8} {'ratio':>8}")
    print(f"  {'-'*72}")

    for r in zero_cases:
        if r['killing_set'] and len(r['killing_set']) == 2:
            p1, p2 = r['killing_set']
            key = (min(p1, p2), max(p1, p2))
            pd = r['pair_data'].get(key)
            if pd:
                print(f"  {r['k']:>3} {r['S']:>3} {p1:>8} {p2:>8} "
                      f"{r['S_p_sizes'][p1]:>6} {r['S_p_sizes'][p2]:>6} "
                      f"{pd['inter_size']:>7} {pd['expected']:>8.2f} {pd['ratio']:>8.4f}")

    # ===================================================================
    # PART 4: Arithmetic structure of killing pairs
    # ===================================================================
    print("\n\n" + "=" * 72)
    print("PART 4: Arithmetic structure of killing pairs")
    print("=" * 72)

    print(f"\n  For each killing pair (p1, p2), analyze:")
    print(f"  - ord_p(2), ord_p(3)")
    print(f"  - Whether 3 in <2> mod p")
    print(f"  - The constraint 2^S ≡ 3^k mod p")
    print()

    for r in zero_cases:
        if not r['killing_set'] or len(r['killing_set']) != 2:
            continue
        k, S, d = r['k'], r['S'], r['d']
        p1, p2 = r['killing_set']

        print(f"  k={k}, S={S}, d={d}, killing pair = ({p1}, {p2})")
        for p in [p1, p2]:
            o2 = multiplicative_order(2, p)
            o3 = multiplicative_order(3, p)
            # Check if 3 in <2> mod p
            three_in_H = False
            if o2:
                # 3 in <2> iff 3^((p-1)/o2) ≡ 1 mod p
                three_in_H = pow(3, (p-1)//o2, p) == 1
            gcd_rk = math.gcd(o2, k) if o2 else None
            print(f"    p={p}: ord_p(2)={o2}, ord_p(3)={o3}, "
                  f"gcd(ord,k)={gcd_rk}, 3 in <2>={three_in_H}, "
                  f"|S_p|={r['S_p_sizes'][p]}")
        print()

    # ===================================================================
    # PART 5: The survivor compositions — what makes them special?
    # ===================================================================
    print("\n" + "=" * 72)
    print("PART 5: Survivor analysis (N_0(d) > 0 cases)")
    print("=" * 72)

    print("\n  When N_0(d) > 0, the survivor composition has corrSum/d = n_0.")
    print("  For a valid k-cycle, need n_0 odd and positive.")
    print("  Key question: Is the survivor always 'trivial' (forced by structure)?")
    print()

    for k in range(3, 15):
        S = S_min(k)
        d = 2**S - 3**k
        if d <= 0:
            continue
        n_comps = math.comb(S - k + k - 1, k - 1)
        if n_comps > 2_000_000:
            continue
        r = analyze_k_full(k, S, verbose=False)
        if r and r['N0_d'] > 0:
            for B, n0 in r['survivors']:
                cs = corrSum(B, k)
                # The composition where all B_j = 0 except B_{k-1} = S-k
                trivial_B = tuple([0]*(k-1) + [S-k])
                is_trivial = (B == trivial_B)
                # Check: corrSum of trivial = 3^{k-1}*1 + 3^{k-2}*1 + ... + 3^0*2^{S-k}
                #       = (3^k - 1)/2 + 2^{S-k}  ... hmm, let me just compute
                trivial_cs = corrSum(trivial_B, k)

                # n_0 = corrSum/d. For k-cycle to exist with specific n_0:
                # n_0 must be odd, and the trajectory must close
                print(f"  k={k}, S={S}: B={B}, corrSum={cs}, n_0={n0}, "
                      f"n0 odd={n0 % 2 == 1 if n0 else None}, "
                      f"is_minimal_B={is_trivial}")

                # Check: does this n_0 actually produce a valid cycle?
                # A k-cycle with these B-values would have step sizes a_j = B_j - B_{j-1}
                # (with B_{-1} = 0 implicitly, interpreting as number of doublings)
                # Actually a_j = b_j + 1 where b_j = B_j - B_{j-1}
                # No: in Steiner's formulation, if we have S total doublings split as
                # a_0 + a_1 + ... + a_{k-1} = S with a_j >= 1,
                # then B_j = a_0 + a_1 + ... + a_j - j (cumulative minus index)
                # Let me re-derive...
                # Actually B_j = sum_{i=0}^{j} a_i - (j+1) where a_i >= 1
                # Equivalently a_i = B_i - B_{i-1} + 1 with B_{-1} = -1
                a_vals = [B[0] + 1] + [B[j] - B[j-1] + 1 for j in range(1, k)]
                print(f"         a-values (doublings per step) = {a_vals}, sum = {sum(a_vals)}")

    # ===================================================================
    # PART 6: Grand pattern search
    # ===================================================================
    print("\n\n" + "=" * 72)
    print("PART 6: Grand pattern — N_0(d) across k and S")
    print("=" * 72)

    print(f"\n  Notation: For each (k,S), showing N_0(d) and #prime_factors(d)")
    print(f"  The conjecture is: no valid k-cycle exists for k >= 2.")
    print(f"  This means: for every (k,S) with d > 0, either N_0(d)=0,")
    print(f"  or every survivor gives n_0 even (or n_0 not leading to valid cycle).\n")

    for k in range(3, 13):
        Sm = S_min(k)
        print(f"  k={k}: ", end="")
        for S in range(Sm, Sm + 12):
            d = 2**S - 3**k
            if d <= 0:
                print("-- ", end="")
                continue
            n_comps = math.comb(S - k + k - 1, k - 1)
            if n_comps > 300_000:
                print("?? ", end="")
                continue
            r = analyze_k_full(k, S, verbose=False)
            if r is None:
                print("?? ", end="")
                continue

            n0_d = r['N0_d']
            n_primes = len(r['primes'])
            if n0_d == 0:
                print(f"0({n_primes}) ", end="")
            else:
                # Check survivors for validity
                has_valid = False
                for B, n0 in r['survivors']:
                    if n0 and n0 > 0 and n0 % 2 == 1:
                        has_valid = True
                if has_valid:
                    print(f"{n0_d}!({n_primes}) ", end="")
                else:
                    print(f"{n0_d}*({n_primes}) ", end="")
        print()

    print(f"\n  Legend: N(#primes), *=all survivors have even n_0, !=has valid odd n_0")

    # ===================================================================
    # PART 7: Focus on the EVEN n_0 mechanism
    # ===================================================================
    print("\n\n" + "=" * 72)
    print("PART 7: Even n_0 analysis — the 'parity sieve'")
    print("=" * 72)

    print(f"\n  For cases where N_0(d) > 0, check if n_0 is always even.")
    print(f"  If so, the cycle is impossible because n_0 must be odd.\n")

    all_survivors = []
    for k in range(3, 15):
        Sm = S_min(k)
        for S in range(Sm, Sm + 8):
            d = 2**S - 3**k
            if d <= 0:
                continue
            n_comps = math.comb(S - k + k - 1, k - 1)
            if n_comps > 500_000:
                continue
            r = analyze_k_full(k, S, verbose=False)
            if r and r['N0_d'] > 0:
                for B, n0 in r['survivors']:
                    parity = "ODD" if n0 % 2 == 1 else "EVEN"
                    all_survivors.append((k, S, d, B, n0, parity))
                    print(f"  k={k}, S={S}, d={d}: n_0={n0} [{parity}], B={B}")

    n_odd = sum(1 for x in all_survivors if x[5] == "ODD")
    n_even = sum(1 for x in all_survivors if x[5] == "EVEN")
    print(f"\n  Total survivors: {len(all_survivors)}, ODD n_0: {n_odd}, EVEN n_0: {n_even}")

    if n_odd > 0:
        print(f"\n  WARNING: Found {n_odd} cases with ODD n_0 — these need further analysis!")
        print(f"  (Must check if the a-values actually produce a valid Collatz cycle)")
        for x in all_survivors:
            if x[5] == "ODD":
                k, S, d, B, n0, _ = x
                # Reconstruct the supposed cycle
                a_vals = [B[0] + 1] + [B[j] - B[j-1] + 1 for j in range(1, k)]
                print(f"    k={k}, S={S}: n_0={n0}, a={a_vals}")
                # Verify: apply k steps of Collatz to n_0
                n = n0
                trajectory = [n]
                for a in a_vals:
                    # One odd step: n -> 3n+1, then a-1 divisions by 2
                    # Actually: n -> (3n+1)/2^a
                    n_next = 3*n + 1
                    if n_next % (2**a) != 0:
                        print(f"      Step fails: 3*{n}+1 = {n_next} not divisible by 2^{a}")
                        break
                    n = n_next // (2**a)
                    trajectory.append(n)
                else:
                    if trajectory[-1] == trajectory[0]:
                        print(f"      VALID CYCLE FOUND: {trajectory}")
                    else:
                        print(f"      NOT a cycle: {trajectory[0]} -> ... -> {trajectory[-1]}")
    else:
        print(f"\n  ALL survivors have EVEN n_0 — parity sieve eliminates everything!")

    # ===================================================================
    # SYNTHESIS
    # ===================================================================
    print("\n\n" + "=" * 72)
    print("SYNTHESIS")
    print("=" * 72)
    print(f"""
Two complementary mechanisms prevent k-cycles (k >= 2):

MECHANISM 1 — CRT Anticorrelation (N_0(d) = 0):
  When d = 2^S - 3^k has >= 2 prime factors, the sets S_p (compositions
  with corrSum ≡ 0 mod p) are individually nonempty but their intersection
  is often empty. The 'killing pair' of primes forces mutual exclusion.
  This handles many (k,S) pairs directly.

MECHANISM 2 — Parity Sieve (n_0 even):
  When N_0(d) > 0, survivors exist but n_0 = corrSum/d may be even.
  Since cycle elements must be odd, even n_0 means no valid cycle.
  This handles cases where d is prime or CRT is insufficient.

MECHANISM 3 — Trajectory Verification:
  Even if n_0 is odd, the step sizes a_j must divide 3*n_j + 1 at each
  step. This provides a final filter.

The UNIVERSAL proof would need to show that for ALL (k,S) with k >= 2:
  Either N_0(d) = 0, or all survivors have even n_0,
  or all odd-n_0 survivors fail trajectory verification.
""")


if __name__ == "__main__":
    main()
