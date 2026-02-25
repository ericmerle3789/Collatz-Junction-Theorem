#!/usr/bin/env python3
"""verify_nonsurjectivity.py — Vérification du Théorème 1 (Merle 2026).

Vérifie que C(S-1, k-1) < d = 2^S - 3^k pour tout k in [18, k_max]
avec S = ceil(k * log2(3)), et identifie les exceptions k < 18.

Sortie attendue (déterministe) :
  Exceptions C >= d : {3, 5, 17}
  Théorème 1 vérifié pour k in [18, 500] : True
  SHA256(exceptions)[:16] : 262a7f2efa4c8255

Usage :
  python3 verify_nonsurjectivity.py [k_max]

Requires : Python >= 3.8 (math.comb). No external dependencies.
"""
import math
import hashlib
import sys


def binary_entropy(p: float) -> float:
    """Binary Shannon entropy h(p) = -p log2 p - (1-p) log2(1-p)."""
    if p <= 0 or p >= 1:
        return 0.0
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def verify_nonsurjectivity(k_max: int = 500) -> dict:
    """Verify Theorem 1 for all k in [2, k_max].

    All comparisons C >= d are done in exact integer arithmetic.
    The only float is math.ceil(k * log2(3)) for computing S.
    """
    LOG2_3 = math.log2(3)
    exceptions = []
    exception_details = []
    verified_count = 0

    for k in range(2, k_max + 1):
        S = math.ceil(k * LOG2_3)
        d = (1 << S) - 3**k          # exact int: 2^S - 3^k
        if d <= 0:
            continue

        C = math.comb(S - 1, k - 1)  # exact int

        if C >= d:
            exceptions.append(k)
            ratio = float(C) / float(d) if d < 10**15 else "large"
            exception_details.append({"k": k, "S": S, "C/d": ratio})
        elif k >= 18:
            verified_count += 1

    expected_count = sum(
        1 for k in range(18, k_max + 1)
        if (1 << math.ceil(k * LOG2_3)) - 3**k > 0
    )

    return {
        "exceptions": sorted(exceptions),
        "all_verified_18_plus": verified_count == expected_count,
        "verified_count": verified_count,
        "expected_count": expected_count,
        "k_max": k_max,
        "details": exception_details,
    }


if __name__ == "__main__":
    k_max = int(sys.argv[1]) if len(sys.argv) > 1 else 500

    # 1. Compute gamma with precision
    alpha = math.log(2) / math.log(3)
    h_alpha = binary_entropy(alpha)
    gamma = 1.0 - h_alpha

    print("=" * 60)
    print("  Vérification du Théorème 1 — Merle 2026")
    print("=" * 60)
    print(f"\n  γ = 1 − h(ln2/ln3) = {gamma:.12f}")
    print(f"  h(α)               = {h_alpha:.12f}")
    print(f"  α = ln2/ln3        = {alpha:.12f}")

    # 2. Verify non-surjectivity
    print(f"\n  Vérification pour k ∈ [2, {k_max}]...")
    result = verify_nonsurjectivity(k_max)

    print(f"\n  Exceptions C ≥ d : {set(result['exceptions'])}")
    for det in result["details"]:
        r = det["C/d"]
        fmt_r = f"{r:.4f}" if isinstance(r, float) else r
        print(f"    k={det['k']:3d}  S={det.get('S','?')}  C/d={fmt_r}")

    print(f"\n  Théorème 1 vérifié pour k ∈ [18, {k_max}] : "
          f"{result['all_verified_18_plus']} "
          f"({result['verified_count']}/{result['expected_count']})")

    # 3. Deterministic hash
    exc_str = str(sorted(result["exceptions"]))
    sha = hashlib.sha256(exc_str.encode()).hexdigest()[:16]
    print(f"  SHA256(exceptions)[:16] : {sha}")

    # 4. Self-test
    if k_max >= 500:
        ok = True
        if result["exceptions"] != [3, 5, 17]:
            print(f"  ✗ FAIL: exceptions = {result['exceptions']}")
            ok = False
        if not result["all_verified_18_plus"]:
            print("  ✗ FAIL: non-surjectivity not verified")
            ok = False
        if sha != "262a7f2efa4c8255":
            print(f"  ✗ FAIL: hash mismatch {sha}")
            ok = False
        if ok:
            print("\n  ✓ Tous les tests passent.")

    print("=" * 60)
