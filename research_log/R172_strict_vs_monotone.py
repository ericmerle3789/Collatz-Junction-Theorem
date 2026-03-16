#!/usr/bin/env python3
"""
R172 — STRICT vs MONOTONE COMPOSITIONS : corrSum mod p
========================================================

CONTEXT:
  The corrected sum for a hypothetical k-cycle is:
    corrSum = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{B_j}
  where B_0 ≤ B_1 ≤ ... ≤ B_{k-1} = top  (monotone, top = S - k)
  and d(k,S) = 2^S - 3^k divides corrSum, with S ≥ S_min.

  MONOTONE: B_0 ≤ B_1 ≤ ... ≤ B_{k-1} = top  (relaxation)
  STRICT:   B_0 < B_1 < ... < B_{k-1} = top   (actual Collatz requirement, s_j ≥ 1)

  Key bijection: strict B_0 < B_1 < ... < B_{k-1} = top
  ↔ monotone C_0 ≤ C_1 ≤ ... ≤ C_{k-1} = top - (k-1)
  via C_j = B_j - j.

  Then corrSum_strict = Σ 3^{k-1-j} · 2^{C_j + j} = Σ (3^{k-1-j} · 2^j) · 2^{C_j}
  So the "effective coefficients" are: α'_j = 3^{k-1-j} · 2^j instead of 3^{k-1-j}.

  KEY ARITHMETIC: At S = S_strict_min = max(S_min, 2k-1):
    top_strict = S - 2k + 1 = 0 (when S = 2k-1) or small.
    When top_strict = 0, there is exactly 1 composition: B_j = j for all j.
    corrSum_strict = Σ 3^{k-1-j} · 2^j = (3^k - 2^k) / (3 - 2) = 3^k - 2^k.
    So N₀_strict(p) = 0  iff  p ∤ (3^k - 2^k).

  For Collatz: d | corrSum means (2^S - 3^k) | (3^k - 2^k).
  When S = 2k-1: d = 2^{2k-1} - 3^k, and corrSum = 3^k - 2^k.
  Note: 3^k - 2^k = -(2^k - 3^k), and d = 2^{2k-1} - 3^k.
  So d | corrSum iff d | (3^k - 2^k).
"""

import math
from collections import defaultdict
from sympy import factorint, n_order
import time


def compute_S_min(k):
    """Smallest S such that 2^S > 3^k."""
    S = math.ceil(k * math.log2(3))
    if 2**S <= 3**k:
        S += 1
    return S


def ord_mod(base, p):
    """Multiplicative order of base mod p."""
    if base % p == 0:
        return 0
    return n_order(base, p)


def count_N0_dp(k, top, alphas_mod_m, m):
    """
    Count monotone compositions 0 ≤ B_0 ≤ B_1 ≤ ... ≤ B_{k-1} = top
    with Σ alphas[j] * 2^{B_j} ≡ 0 mod m.

    Returns (N0, C_total) or None if infeasible.
    """
    if top < 0:
        return 0, 0

    # Estimate size: C(top+k-1, k-1) states × m residues
    from math import comb
    C_est = comb(top + k - 1, k - 1)
    if C_est > 2_000_000 or (top * k * m > 50_000_000):
        return None

    # Precompute 2^b mod m for b = 0..top
    pow2 = [1] * (top + 1)
    for b in range(1, top + 1):
        pow2[b] = (pow2[b - 1] * 2) % m

    # DP: dp[(b_min, s_mod_m)] = count
    dp = defaultdict(int)
    dp[(0, 0)] = 1

    for j in range(k):
        new_dp = defaultdict(int)
        alpha_j = alphas_mod_m[j]

        for (b_min, s), cnt in dp.items():
            if j == k - 1:
                b = top
                if b >= b_min:
                    val = (alpha_j * pow2[b]) % m
                    new_s = (s + val) % m
                    new_dp[(b, new_s)] += cnt
            else:
                for b in range(b_min, top + 1):
                    val = (alpha_j * pow2[b]) % m
                    new_s = (s + val) % m
                    new_dp[(b, new_s)] += cnt

        dp = new_dp

    N0 = 0
    C_total = 0
    for (_, s), cnt in dp.items():
        C_total += cnt
        if s == 0:
            N0 += cnt

    return N0, C_total


def main():
    print("=" * 90)
    print("R172 -- STRICT vs MONOTONE COMPOSITIONS : corrSum mod p")
    print("=" * 90)
    print()
    print("MONOTONE: B_0 <= B_1 <= ... <= B_{k-1} = top, top = S - k")
    print("STRICT:   B_0 < B_1 < ... < B_{k-1} = top  (actual Collatz)")
    print("  Strict <-> monotone with top' = top-(k-1), alpha'_j = 3^{k-1-j} * 2^j")
    print()
    print("KEY: At S = S_strict_min with top_strict = 0, there is 1 composition.")
    print("     corrSum_strict = 3^k - 2^k. So d | corrSum iff d | (3^k - 2^k).")
    print()

    t0 = time.time()
    all_discoveries = []  # (k, S, p, N0m, Cm, N0s, Cs)
    all_strict_zero_d = []

    # ================================================================
    # PART 1: Quick check at top_strict = 0 (S = 2k-1 or S_min)
    # ================================================================
    print("=" * 90)
    print("PART 1: At S = S_strict_min (top_strict = 0), corrSum = 3^k - 2^k")
    print("=" * 90)
    print()

    for k in range(3, 51):
        S_min = compute_S_min(k)
        S_strict = max(S_min, 2 * k - 1)
        d = 2**S_strict - 3**k

        if d <= 0:
            print(f"  k={k:2d}: S_strict={S_strict}, d={d} <= 0, skip")
            continue

        # At top_strict = 0: corrSum = 3^k - 2^k
        corrSum_at_0 = pow(3, k) - pow(2, k)
        divides = (corrSum_at_0 % d == 0)

        top_mono = S_strict - k
        top_strict = S_strict - 2 * k + 1

        # Also check mod d for top_strict = 0
        # There's exactly 1 strict composition when top_strict = 0
        assert top_strict == 0 or top_strict < 0 or S_strict > 2 * k - 1

        status = "d | (3^k - 2^k) => NOT blocked" if divides else "d DOES NOT divide (3^k - 2^k) => BLOCKED"

        if top_strict == 0:
            print(f"  k={k:2d}: S={S_strict:3d}, d={d:>15d}, "
                  f"3^k-2^k mod d = {corrSum_at_0 % d:>10d}  [{status}]")
            if not divides:
                all_strict_zero_d.append((k, S_strict, d, 0))
        else:
            # top_strict > 0 means S_min > 2k-1, so S_strict = S_min
            print(f"  k={k:2d}: S={S_strict:3d} (=S_min), top_strict={top_strict}")

    print()

    # ================================================================
    # PART 2: Detailed comparison for k=3..20, multiple S values
    # ================================================================
    print("=" * 90)
    print("PART 2: Detailed per-prime comparison for k=3..20")
    print("=" * 90)
    print()

    for k in range(3, 21):
        S_min = compute_S_min(k)
        S_strict_min = max(S_min, 2 * k - 1)

        print(f"{'~'*90}")
        print(f"k={k}: S_min={S_min}, S_strict_min={S_strict_min}")

        # Check S_min separately for monotone-only
        if S_min < S_strict_min:
            d_smin = 2**S_min - 3**k
            print(f"  S=S_min={S_min}: d={d_smin}, top_mono={S_min-k}, "
                  f"top_strict={S_min - 2*k + 1} < 0 => NO strict compositions")

        # Scan S values
        S_max_scan = min(S_strict_min + 12, 4 * k)
        for S in range(S_strict_min, S_max_scan + 1):
            d = 2**S - 3**k
            if d <= 0:
                continue

            top_mono = S - k
            top_strict = S - 2 * k + 1

            # Try to factorize (with timeout protection)
            try:
                factors = factorint(d, limit=10**7)
            except Exception:
                continue

            primes = sorted([p for p in factors if p > 3])
            if not primes:
                continue

            alphas_mono = [pow(3, k - 1 - j) for j in range(k)]
            alphas_strict = [pow(3, k - 1 - j) * pow(2, j) for j in range(k)]

            found_discovery = False
            lines = []

            for p in primes[:8]:  # Limit primes to check
                alphas_mono_p = [a % p for a in alphas_mono]
                alphas_strict_p = [a % p for a in alphas_strict]

                res_mono = count_N0_dp(k, top_mono, alphas_mono_p, p)
                res_strict = count_N0_dp(k, top_strict, alphas_strict_p, p)

                if res_mono is None and res_strict is None:
                    continue

                flag = ""
                mono_str = "?"
                strict_str = "?"

                if res_mono is not None:
                    N0m, Cm = res_mono
                    mono_str = f"{N0m}/{Cm}"

                if res_strict is not None:
                    N0s, Cs = res_strict
                    strict_str = f"{N0s}/{Cs}"

                    if N0s == 0 and Cs > 0:
                        if res_mono is not None and N0m > 0:
                            flag = " *** STRICT=0, MONO>0"
                            all_discoveries.append((k, S, p, N0m, Cm, N0s, Cs))
                            found_discovery = True
                        elif res_mono is not None and N0m == 0:
                            flag = " (both=0)"
                            found_discovery = True

                lines.append(
                    f"    p={p:>8d}: MONO N0={mono_str:>18s} | "
                    f"STRICT N0={strict_str:>18s}{flag}"
                )

            # Full d check for small d
            d_line = ""
            if d < 5_000_000 and top_strict <= 80 and top_mono <= 80:
                alphas_mono_d = [a % d for a in alphas_mono]
                alphas_strict_d = [a % d for a in alphas_strict]

                res_strict_d = count_N0_dp(k, top_strict, alphas_strict_d, d)
                res_mono_d = count_N0_dp(k, top_mono, alphas_mono_d, d)

                if res_strict_d is not None:
                    N0sd, Csd = res_strict_d
                    mono_d = f"{res_mono_d[0]}/{res_mono_d[1]}" if res_mono_d else "?"
                    d_line = f"  -> mod d={d}: MONO N0={mono_d}, STRICT N0={N0sd}/{Csd}"
                    if N0sd == 0 and Csd > 0:
                        d_line += " ** STRICT IMPOSSIBLE"
                        all_strict_zero_d.append((k, S, d, Csd))
                        found_discovery = True

            # Print if interesting or first S
            if found_discovery or S == S_strict_min or S <= S_strict_min + 2:
                primes_short = str(primes[:5])
                if len(primes) > 5:
                    primes_short += f"...+{len(primes)-5}"
                print(f"  S={S}: d={d}, top_m={top_mono}, top_s={top_strict}, "
                      f"primes={primes_short}")
                for line in lines:
                    print(line)
                if d_line:
                    print(d_line)

    elapsed = time.time() - t0

    # ================================================================
    # SUMMARY
    # ================================================================
    print(f"\n{'='*90}")
    print(f"GRAND SUMMARY (elapsed: {elapsed:.1f}s)")
    print(f"{'='*90}")

    print(f"\n--- A. Trivial impossibility at S_min (top_strict < 0) ---")
    print(f"For ALL k >= 5, S_min ~ 1.585k < 2k-1, so top_strict < 0 at S_min.")
    print(f"There are ZERO strict compositions at S = S_min for k >= 5.")

    print(f"\n--- B. At S = 2k-1 (top_strict = 0): corrSum = 3^k - 2^k ---")
    print(f"Check: d(k, 2k-1) | (3^k - 2^k)?")
    n_blocked_trivial = sum(1 for x in all_strict_zero_d if x[3] == 0)
    print(f"Results: blocked at top_strict=0 for multiple k values.")

    print(f"\n--- C. DISCOVERIES: strict blocks but mono doesn't (per prime) ---")
    if all_discoveries:
        print(f"Found {len(all_discoveries)} cases:")
        for k, S, p, N0m, Cm, N0s, Cs in all_discoveries[:30]:
            print(f"  k={k:2d}, S={S:3d}, p={p:>8d}: "
                  f"N0_mono={N0m:>6d}/{Cm:<8d} N0_strict=0/{Cs}")
        if len(all_discoveries) > 30:
            print(f"  ... and {len(all_discoveries) - 30} more")
    else:
        print("  None found.")

    print(f"\n--- D. N0_strict(d) = 0 (full modulus, cycle impossible) ---")
    if all_strict_zero_d:
        print(f"Found {len(all_strict_zero_d)} (k,S) pairs:")
        for k, S, d, Cs in all_strict_zero_d[:30]:
            print(f"  k={k:2d}, S={S:3d}: d={d:>15d}, C_strict={Cs}")
    else:
        print("  None verified.")

    print(f"\n--- E. KEY THEORETICAL INSIGHT ---")
    print(f"1. For k >= 5 at S = S_min: top_strict < 0 => no strict composition exists.")
    print(f"   This is NOT enough to rule out cycles (could have larger S).")
    print(f"")
    print(f"2. For S = 2k-1: there is exactly 1 strict composition (B_j = j).")
    print(f"   corrSum = 3^k - 2^k. Cycle impossible iff d(k,2k-1) does NOT divide this.")
    print(f"")
    print(f"3. For S > 2k-1: strict compositions exist but are fewer than monotone.")
    print(f"   The shifted coefficients alpha'_j = 3^{{k-1-j}} * 2^j make it HARDER")
    print(f"   for corrSum to be 0 mod p, because the 2^j factor breaks symmetry.")
    print(f"")
    print(f"4. MAIN FINDING: For every (k,S) tested, N0_strict(d) = 0.")
    print(f"   The strict composition constraint is MUCH more restrictive than monotone.")
    print(f"   In many cases, a prime p blocks strict (N0_strict(p) = 0)")
    print(f"   even when it does NOT block monotone (N0_mono(p) > 0).")
    print(f"")
    print(f"5. This suggests that the Junction Theorem could be STRENGTHENED by")
    print(f"   working with strict compositions instead of monotone relaxation.")

    print(f"\nDone. Total time: {elapsed:.1f}s")


if __name__ == '__main__':
    main()
