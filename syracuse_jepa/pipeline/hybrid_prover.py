#!/usr/bin/env python3
"""
Hybrid Prover — Combine ALL Available Methods
══════════════════════════════════════════════

The creative engine revealed: NO SINGLE METHOD proves ALL k.
We need a hybrid approach that chains methods:

METHOD ARSENAL:
  A. FCQ Primitive Root: ρ=1/(p-1), works when d(k) has prim root factor
  B. Spectral DP: direct N₀(p) computation, works for small k·p
  C. FCQ General: ρ_p < 1 for any p with high order, works asymptotically
  D. Steiner n_min: works for all k ≤ 120 (with Barina for larger)
  E. Large prime search: factor d(k) deeper to find better primes

STRATEGY:
  For each k, try methods in order of cost (cheapest first):
  1. FCQ with known small primes (instant)
  2. Spectral DP for small primes (fast for small p)
  3. Factor d(k) deeper (find primes up to 10^6)
  4. FCQ with newly found primes
  5. Steiner n_min bound (always works for k ≤ 120)

GOAL: prove N₀(d(k)) = 0 for ALL k = 3..200 with method certificates.
"""

import math
import time
from dataclasses import dataclass
from typing import List, Dict, Optional

from syracuse_jepa.pipeline.analyst import compute_S, compute_d, factorize, multiplicative_order
from syracuse_jepa.pipeline.spectral import count_compositions_with_residue
import cmath


def compute_rho_free(p: int) -> float:
    """Compute the free FCQ spectral radius for prime p."""
    q = multiplicative_order(2, p)
    omega = cmath.exp(2j * cmath.pi / p)
    powers = [pow(2, j, p) for j in range(q)]
    max_rho = 0
    for a in range(1, p):
        S_a = sum(omega ** (a * pw % p) for pw in powers)
        rho_a = abs(S_a) / q
        max_rho = max(max_rho, rho_a)
    return max_rho


@dataclass
class ProofCertificate:
    """A machine-checkable certificate that N₀(d(k)) = 0."""
    k: int
    proved: bool
    method: str               # "fcq_prim", "spectral_dp", "fcq_general", "steiner", "combined"
    witness_prime: int        # the prime p used (0 for steiner)
    witness_ord: int          # ord_p(2)
    is_primitive_root: bool
    rho: float
    R_bound: float            # q·ρ^{k-1}
    n0_exact: int             # -1 if not computed
    n_total: int
    computation_time: float   # seconds
    details: str


def try_fcq_primitive(k: int, max_prime: int = 50000) -> Optional[ProofCertificate]:
    """Try FCQ with primitive root primes (cheapest method)."""
    t0 = time.time()
    S = compute_S(k)
    d = compute_d(k)
    if d <= 1:
        return None

    factors = factorize(d)

    for p, _ in factors:
        if p > max_prime:
            continue
        q = multiplicative_order(2, p)
        if q == p - 1:  # primitive root
            rho = 1 / (p - 1)
            R = q * rho ** (k - 1)
            if R < 1:
                return ProofCertificate(
                    k=k, proved=True, method="fcq_prim",
                    witness_prime=p, witness_ord=q,
                    is_primitive_root=True,
                    rho=rho, R_bound=R,
                    n0_exact=-1, n_total=-1,
                    computation_time=time.time() - t0,
                    details=f"2 is primitive root mod {p}, ρ={rho:.6f}, R={R:.2e}"
                )
    return None


def try_spectral_dp(k: int, max_prime: int = 500) -> Optional[ProofCertificate]:
    """Try direct DP computation of N₀(p) for small primes."""
    t0 = time.time()
    S = compute_S(k)
    d = compute_d(k)
    if d <= 1:
        return None

    factors = factorize(d)
    small_primes = sorted(set(p for p, _ in factors if p <= max_prime))

    for p in small_primes:
        # Skip if computation would be too expensive
        # DP complexity: O(k × p × S²) — skip if > ~10^8
        if k * p * S * S > 1e8:
            continue

        n0, n_total = count_compositions_with_residue(k, S, p, target_r=0)
        if n0 == 0:
            q = multiplicative_order(2, p)
            return ProofCertificate(
                k=k, proved=True, method="spectral_dp",
                witness_prime=p, witness_ord=q,
                is_primitive_root=(q == p - 1),
                rho=0, R_bound=0,
                n0_exact=0, n_total=n_total,
                computation_time=time.time() - t0,
                details=f"N₀({p})=0 among {n_total} compositions (direct DP)"
            )
    return None


def try_fcq_general(k: int, max_prime: int = 50000) -> Optional[ProofCertificate]:
    """Try FCQ with any prime (not just primitive roots)."""
    t0 = time.time()
    S = compute_S(k)
    d = compute_d(k)
    if d <= 1:
        return None

    factors = factorize(d)
    rho_cache = {}

    for p, _ in sorted(factors, key=lambda x: x[0]):
        if p > max_prime or p < 5:
            continue
        q = multiplicative_order(2, p)

        if p not in rho_cache:
            if q <= 5000:  # feasible to compute rho
                rho_cache[p] = compute_rho_free(p)
            else:
                continue

        rho = rho_cache[p]
        if rho < 1:
            R = q * rho ** (k - 1)
            if R < 1:
                return ProofCertificate(
                    k=k, proved=True, method="fcq_general",
                    witness_prime=p, witness_ord=q,
                    is_primitive_root=(q == p - 1),
                    rho=rho, R_bound=R,
                    n0_exact=-1, n_total=-1,
                    computation_time=time.time() - t0,
                    details=f"FCQ via p={p}, q={q}, ρ={rho:.6f}, R={R:.2e}"
                )
    return None


def try_steiner(k: int) -> Optional[ProofCertificate]:
    """
    Steiner n_min argument: if cycle exists, n_min ≤ bound.
    If all n ≤ bound converge, no cycle.
    Barina (2025) verified convergence for all n up to 2^71.
    """
    t0 = time.time()
    S = compute_S(k)
    d = compute_d(k)
    if d <= 0:
        return None

    # n_min bound: (3^k - 1) * 2^{S-k-1} / d
    try:
        numerator = (3**k - 1) * (2 ** (S - k - 1))
        n_min_bound = numerator // d + 1
    except (OverflowError, ValueError):
        return None

    bits = n_min_bound.bit_length()

    if bits <= 71:
        return ProofCertificate(
            k=k, proved=True, method="steiner_barina",
            witness_prime=0, witness_ord=0,
            is_primitive_root=False,
            rho=0, R_bound=0,
            n0_exact=-1, n_total=-1,
            computation_time=time.time() - t0,
            details=f"Steiner+Barina: n_min ≤ 2^{bits}, "
                    f"within Barina's verified range 2^71"
        )
    return None


def prove_all(k_min: int = 3, k_max: int = 200) -> List[ProofCertificate]:
    """
    Try to prove N₀(d(k)) = 0 for all k in range.
    Uses methods in order of cost.
    """
    certificates = []
    methods_used = {}

    print(f"  Proving k={k_min}..{k_max} using hybrid approach...")
    print()

    for k in range(k_min, k_max + 1):
        # Try methods in order of cost
        cert = None

        # Method A: FCQ Primitive Root (instant)
        if cert is None:
            cert = try_fcq_primitive(k, max_prime=50000)

        # Method B: Spectral DP (fast for small primes)
        if cert is None:
            cert = try_spectral_dp(k, max_prime=200)

        # Method C: FCQ General (medium cost)
        if cert is None:
            cert = try_fcq_general(k, max_prime=10000)

        # Method D: Steiner n_min (always works for k ≤ ~120)
        if cert is None:
            cert = try_steiner(k)

        if cert is None:
            cert = ProofCertificate(
                k=k, proved=False, method="NONE",
                witness_prime=0, witness_ord=0,
                is_primitive_root=False,
                rho=0, R_bound=0,
                n0_exact=-1, n_total=-1,
                computation_time=0,
                details="ALL METHODS FAILED"
            )

        certificates.append(cert)
        method = cert.method if cert.proved else "OPEN"
        methods_used[method] = methods_used.get(method, 0) + 1

        if k <= 50 or k % 20 == 0 or not cert.proved:
            status = f"✓ {cert.method}" if cert.proved else "✗ OPEN"
            print(f"    k={k:3d}  {status:20s}  {cert.details[:50]}")

    return certificates


def run_hybrid_prover(k_min: int = 3, k_max: int = 200) -> dict:
    """Full hybrid prover run."""
    print()
    print("╔" + "═" * 68 + "╗")
    print("║  HYBRID PROVER — All Methods Combined                            ║")
    print("║  FCQ Prim + Spectral DP + FCQ General + Steiner + Barina         ║")
    print("╚" + "═" * 68 + "╝")
    print()

    print("┌─ PROVING ALL k ───────────────────────────────────────────┐")
    certs = prove_all(k_min, k_max)
    print(f"└─ {len(certs)} k values processed ────────────────────────┘\n")

    # Statistics
    proved = [c for c in certs if c.proved]
    open_cases = [c for c in certs if not c.proved]

    methods = {}
    for c in proved:
        methods[c.method] = methods.get(c.method, 0) + 1

    print("╔" + "═" * 68 + "╗")
    print("║  HYBRID PROVER RESULTS                                           ║")
    print("╠" + "═" * 68 + "╣")
    print(f"║  PROVED: {len(proved)} / {len(certs)} k values")
    print(f"║")
    print(f"║  Methods breakdown:")
    for method, count in sorted(methods.items(), key=lambda x: -x[1]):
        bar = "█" * min(count, 40)
        print(f"║    {method:20s}: {count:4d} |{bar}")
    print(f"║")

    if open_cases:
        print(f"║  OPEN CASES ({len(open_cases)}):")
        for c in open_cases[:20]:
            print(f"║    k={c.k}: {c.details[:55]}")
        if len(open_cases) > 20:
            print(f"║    ... and {len(open_cases) - 20} more")
    else:
        print(f"║  ★ ALL k={k_min}..{k_max} PROVED — N₀(d(k)) = 0 ★")

    print(f"║")
    total_time = sum(c.computation_time for c in certs)
    print(f"║  Total computation time: {total_time:.2f}s")
    print("╚" + "═" * 68 + "╝")

    return {
        "n_proved": len(proved),
        "n_total": len(certs),
        "n_open": len(open_cases),
        "methods": methods,
        "open_k": [c.k for c in open_cases],
        "certificates": [
            {"k": c.k, "proved": c.proved, "method": c.method,
             "witness_prime": c.witness_prime, "details": c.details}
            for c in certs
        ],
    }


if __name__ == '__main__':
    import json
    import sys

    k_max = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    result = run_hybrid_prover(3, k_max)

    with open('syracuse_jepa/pipeline/hybrid_results.json', 'w') as f:
        json.dump(result, f, indent=2, ensure_ascii=False)
    print(f"\nSaved to hybrid_results.json")
