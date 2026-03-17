"""
Prover — Automated Proof Extension (Syracuse-JEPA v2.1)

Extends the verified range beyond native_decide using:
1. Steiner n_min argument (R171): cycle → n_min ≤ bound → n_min converges → ⊥
2. CRT interference analysis: quantify how primes combine
3. Gap analysis: identify the hardest k values

For k ≤ 40: native_decide (already in Theorems.lean)
For k = 41..120: Steiner n_min + Barina/Hercher verification bounds
For k ≥ 18: nonsurjectivity C < d (entropy deficit γ ≈ 0.05)
"""

import math
from dataclasses import dataclass
from typing import List, Tuple, Optional

from syracuse_jepa.pipeline.analyst import compute_S, compute_d, factorize


# Known verification limits from literature
VERIFICATION_LIMITS = {
    'steiner_1977': 2**32,           # Original Steiner
    'oliveira_2002': 2**40,          # Oliveira & Silva
    'simons_deweger_2003': 2**60,    # Simons & de Weger (covers k ≤ 68)
    'hercher_2022': 2**68,           # Hercher (covers k ≤ 91)
    'barina_2025': 2**71,            # Barina (covers k ≤ ~120)
}


@dataclass
class SteinerProof:
    """A proof of N₀(d(k))=0 via the Steiner n_min argument."""
    k: int
    S: int
    d: int
    n_min_bound: int         # upper bound on n_min if a cycle existed
    n_min_bits: int          # bit-length of n_min_bound
    verification_source: str # which verification limit is used
    verification_limit: int
    is_proved: bool
    proof_sketch: str


def compute_n_min_bound(k: int) -> Tuple[int, int]:
    """
    Compute the upper bound on n_min for a hypothetical k-cycle.

    If a cycle of length k exists with corrSum = m·d(k), then the
    smallest element n_min = corrSum / d = m.

    The MAXIMUM possible corrSum for monotone A with sum S is achieved
    when A is concentrated at the top: A = (0, 0, ..., 0, S).
    corrSum_max = 3^0 · 2^S = 2^S (but this is not monotone for k>1).

    For monotone compositions of S into k parts:
    corrSum_max occurs at A = (v, v, ..., v, v+1, ..., v+1) with max skew.
    Upper bound: corrSum_max ≤ (3^k - 1) / (3 - 1) · 2^{S} / 2^{S-k+1}
    Simpler bound: corrSum_max ≤ (3^k - 1) · 2^{S-1}

    So n_min ≤ corrSum_max / d = (3^k - 1) · 2^{S-1} / d.

    Actually the tighter bound from R171:
    n_min ≤ corrSum_max / d where corrSum_max uses the actual max composition.
    """
    S = compute_S(k)
    d = compute_d(k)

    if d <= 0:
        return 0, 0

    # Maximum corrSum: all weight at the end.
    # For monotone A=(a_0,...,a_{k-1}) with a_0 ≤ ... ≤ a_{k-1} and Σa_i = S:
    # corrSum = Σ 3^{k-1-i} · 2^{a_i}
    # To maximize: want large a_i paired with small 3^{k-1-i} (which means large i).
    # Worst case (flattest): A = (v,...,v,v+1,...,v+1)
    # But the MAXIMUM corrSum over all monotone compositions is with A = (0,0,...,0,S-(k-1),S-(k-1),...,S)
    # Actually no — monotone means a_0 ≤ a_1 ≤ ... ≤ a_{k-1}. The max corrSum
    # is with the most weight on the LAST positions (smallest 3^{k-1-i}).
    # With monotonicity: the most skewed is A = (0, 0, ..., 0, S).
    # Wait — that requires a_0 ≤ a_1 ≤ ... ≤ a_{k-1}, and Σ = S.
    # If a_0 = ... = a_{k-2} = 0 and a_{k-1} = S, then Σ = S. ✓ Monotone? 0 ≤ 0 ≤ ... ≤ S. ✓
    # corrSum = 3^{k-1} · 2^0 + ... + 3^1 · 2^0 + 3^0 · 2^S
    #         = (3^k - 3)/(3-1) + 2^S = (3^k - 3)/2 + 2^S
    # This is the max because 2^S >> (3^k-3)/2 for S = ceil(k·log₂3).

    # More careful: corrSum_max = max over monotone A of Σ 3^{k-1-i} · 2^{a_i}
    # The composition (0,...,0,S) gives corrSum = (3^k-3)/2 + 2^S
    corrsum_max = (3**k - 3) // 2 + (1 << S)

    n_min_bound = corrsum_max // d
    n_min_bits = n_min_bound.bit_length()

    return n_min_bound, n_min_bits


def prove_via_steiner(k: int) -> SteinerProof:
    """
    Prove N₀(d(k))=0 via the Steiner n_min argument.

    Logic: Assume a k-cycle exists. Then ∃ n_min (smallest element in cycle)
    with n_min ≤ corrSum_max / d. If all n ≤ n_min_bound are known to converge
    to 1 (from computational verification), then n_min is NOT in a cycle. ⊥
    """
    S = compute_S(k)
    d = compute_d(k)
    n_min_bound, n_min_bits = compute_n_min_bound(k)

    # Find which verification limit covers this
    is_proved = False
    source = "none"
    limit = 0

    for src_name, src_limit in sorted(VERIFICATION_LIMITS.items(), key=lambda x: x[1]):
        if n_min_bound <= src_limit:
            is_proved = True
            source = src_name
            limit = src_limit
            break

    sketch = (
        f"Suppose a {k}-cycle exists with smallest element n_min.\n"
        f"By the Junction Theorem: n_min = corrSum(A,{k}) / d({k}) for some monotone A.\n"
        f"Maximum corrSum over monotone compositions of {S} into {k} parts:\n"
        f"  corrSum_max = (3^{k} - 3)/2 + 2^{S} = {(3**k - 3)//2 + (1 << S)}\n"
        f"  n_min ≤ corrSum_max / d = {n_min_bound} (≈ 2^{{{n_min_bits}}})\n"
    )

    if is_proved:
        sketch += (
            f"By {source}: all n ≤ {limit} (≈ 2^{{{limit.bit_length()}}}) converge to 1.\n"
            f"Since {n_min_bound} ≤ {limit}, n_min converges → NOT in a cycle. ⊥\n"
            f"∴ No {k}-cycle exists. N₀(d({k})) = 0. □"
        )
    else:
        sketch += (
            f"n_min_bound = 2^{{{n_min_bits}}} exceeds all known verification limits.\n"
            f"Steiner argument INSUFFICIENT for k={k}."
        )

    return SteinerProof(
        k=k, S=S, d=d,
        n_min_bound=n_min_bound,
        n_min_bits=n_min_bits,
        verification_source=source,
        verification_limit=limit,
        is_proved=is_proved,
        proof_sketch=sketch,
    )


def extended_proof_scan(k_min: int = 3, k_max: int = 200) -> List[dict]:
    """
    Scan all k values and determine proof method:
    - k ≤ 40: native_decide (Lean verified)
    - k ≤ K_steiner: Steiner n_min argument
    - k ≥ 18: nonsurjectivity (at least 1 residue omitted, not necessarily 0)
    """
    results = []

    print("┌─ PROVER — Extended Proof Scan ───────────────────────────┐")
    print(f"  Methods: native_decide (k≤40), Steiner n_min, nonsurjectivity")
    print()

    max_steiner_k = 0
    methods = {'native_decide': 0, 'steiner': 0, 'nonsurjectivity_only': 0, 'open': 0}

    for k in range(k_min, k_max + 1):
        if k == 4:
            # k=4 is the phantom — N₀ = 1, not 0
            method = "phantom"
            proved_n0_zero = False
        elif k <= 40:
            method = "native_decide"
            proved_n0_zero = True
            methods['native_decide'] += 1
        else:
            steiner = prove_via_steiner(k)
            if steiner.is_proved:
                method = f"steiner_{steiner.verification_source}"
                proved_n0_zero = True
                max_steiner_k = max(max_steiner_k, k)
                methods['steiner'] += 1
            elif k >= 18:
                method = "nonsurjectivity_only"
                proved_n0_zero = False  # only proves ≥1 residue omitted
                methods['nonsurjectivity_only'] += 1
            else:
                method = "open"
                methods['open'] += 1
                proved_n0_zero = False

        r = {
            'k': k,
            'method': method,
            'proved_N0_zero': proved_n0_zero,
        }

        if k > 40 and method.startswith('steiner'):
            steiner = prove_via_steiner(k)
            r['n_min_bits'] = steiner.n_min_bits
            r['verification_source'] = steiner.verification_source

        results.append(r)

        if k <= 45 or k % 10 == 0 or (k > 40 and method.startswith('steiner')
                                        and k == max_steiner_k):
            status = "N₀=0 ✓" if proved_n0_zero else "OPEN"
            extra = ""
            if k > 40 and method.startswith('steiner'):
                extra = f"  n_min ≤ 2^{steiner.n_min_bits}"
            print(f"  k={k:3d}  {method:30s}  {status}{extra}")

    print()
    print(f"  SUMMARY:")
    print(f"    native_decide (k≤40):    {methods['native_decide']:3d} proved")
    print(f"    Steiner n_min:           {methods['steiner']:3d} proved (max k={max_steiner_k})")
    print(f"    Nonsurjectivity only:    {methods['nonsurjectivity_only']:3d} (≥1 omitted, NOT N₀=0)")
    print(f"    Open:                    {methods['open']:3d}")
    print(f"  TOTAL N₀=0 PROVED:        {methods['native_decide'] + methods['steiner']} / {k_max - k_min + 1}")
    print(f"└─────────────────────────────────────────────────────────┘")

    return results


def generate_proof_certificate(k_max_steiner: int = 120) -> str:
    """Generate a mathematical proof certificate."""
    lines = []
    lines.append("=" * 72)
    lines.append("  PROOF CERTIFICATE — Collatz Non-Trivial Cycle Exclusion")
    lines.append("  Generated by Syracuse-JEPA v2.1")
    lines.append("=" * 72)
    lines.append("")

    lines.append("THEOREM: There is no non-trivial cycle of length k for k = 3..K₀,")
    lines.append(f"where K₀ is determined by computational verification limits.")
    lines.append("")

    lines.append("PROOF STRUCTURE:")
    lines.append("")
    lines.append("CASE 1: k = 3..40 (native_decide in Lean 4)")
    lines.append("  For each k, enumerate ALL monotone compositions of S(k) into k parts.")
    lines.append("  Verify computationally that none has corrSum ≡ 0 mod d(k).")
    lines.append("  Formally verified by Lean 4 kernel via native_decide.")
    lines.append("  Exception: k=4 has ONE composition (1,1,1,4) with corrSum = 2·d(4),")
    lines.append("  corresponding to the trivial cycle {1,2,4}.")
    lines.append("")

    lines.append("CASE 2: k = 41..K₀ (Steiner n_min argument)")
    lines.append("  Assume a k-cycle exists with smallest element n_min.")
    lines.append("  By the Junction Theorem: n_min ≤ corrSum_max / d(k).")
    lines.append("  By computational verification (Barina 2025: all n ≤ 2^71 converge),")
    lines.append("  n_min is not in a cycle. Contradiction.")
    lines.append("")

    # Compute the actual limit
    for k in range(41, 300):
        steiner = prove_via_steiner(k)
        if not steiner.is_proved:
            k_limit = k - 1
            break
    else:
        k_limit = 299

    lines.append(f"  With Barina (2^71): covers k ≤ {k_limit}")
    lines.append(f"  With Hercher (2^68): covers k ≤ {prove_steiner_limit('hercher_2022')}")
    lines.append("")

    lines.append("CASE 3: k ≥ 18 (Nonsurjectivity)")
    lines.append("  C(k) < d(k) for k ≥ 18 (entropy deficit γ ≈ 0.05).")
    lines.append("  This proves at least ONE residue is not in Im(Ev_d),")
    lines.append("  but does NOT prove that residue 0 is among the omitted.")
    lines.append("  STATUS: OPEN for general k (the Stage II problem).")
    lines.append("")

    lines.append("OPEN PROBLEM (Stage II): Prove 0 ∈ omitted residues for all k ≥ 3.")
    lines.append("  Top strategy: LDS + FCQ Combined Attack (score 86.4/100)")
    lines.append("  Critical question: uniform ρ_p < 1-ε for all p|d(k)")
    lines.append("")

    lines.append("=" * 72)
    return "\n".join(lines)


def prove_steiner_limit(source: str) -> int:
    """Find the maximum k for which Steiner argument works with given source."""
    limit = VERIFICATION_LIMITS.get(source, 0)
    for k in range(3, 500):
        n_min_bound, _ = compute_n_min_bound(k)
        if n_min_bound > limit:
            return k - 1
    return 499


if __name__ == '__main__':
    results = extended_proof_scan(3, 200)

    print()
    print(generate_proof_certificate())

    # Exact Steiner limits
    print("\n═══ STEINER LIMITS BY SOURCE ═══")
    for name, limit in sorted(VERIFICATION_LIMITS.items(), key=lambda x: x[1]):
        k_max = prove_steiner_limit(name)
        print(f"  {name:25s}  (2^{limit.bit_length()-1})  →  k ≤ {k_max}")
