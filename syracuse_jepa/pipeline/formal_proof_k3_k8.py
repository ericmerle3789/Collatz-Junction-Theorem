#!/usr/bin/env python3
"""
FORMAL PROOFS for k=3..8 via the ordering obstruction mechanism
=================================================================

For each k: enumerate ALL free solutions, verify sorting correction ≠ 0.
The proof for each k consists of:
1. List all free δ-sequences with F(δ) ≡ 0 mod d
2. For each: compute sorting correction, verify ≠ 0 mod d
3. Certificate: the specific correction values

This is a COMPLETE, VERIFIABLE proof for k=3..8.
"""

import sys, os, json
from math import ceil, log2, gcd
from itertools import product as cart_product

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
from syracuse_jepa.pipeline.cumulative_generator import compute_S, compute_d


def generate_proof_certificate(k):
    S = compute_S(k)
    d = compute_d(k)
    if d <= 0: return None
    max_delta = S - k

    inv3 = pow(3, -1, d)
    rho = (2 * inv3) % d
    rho_pow = [pow(rho, i, d) for i in range(k)]
    two_pow = [pow(2, j, d) for j in range(max_delta + 1)]

    total_free = (max_delta + 1) ** (k - 1)

    cert = {
        'k': k, 'S': S, 'd': d,
        'rho': rho, 'max_delta': max_delta,
        'total_free_sequences': total_free,
        'free_solutions': [],
        'all_corrections_nonzero': True,
        'proof_status': 'UNKNOWN',
    }

    if total_free > 5000000:
        cert['proof_status'] = 'TOO_LARGE'
        return cert

    for deltas in cart_product(range(max_delta + 1), repeat=k-1):
        f_val = (1 + sum(rho_pow[i+1] * two_pow[deltas[i]] % d for i in range(k-1))) % d
        if f_val != 0:
            continue

        sorted_d = tuple(sorted(deltas))
        f_sorted = (1 + sum(rho_pow[i+1] * two_pow[sorted_d[i]] % d for i in range(k-1))) % d
        correction = (f_sorted - f_val) % d  # = f_sorted since f_val = 0

        sol = {
            'delta_unsorted': list(deltas),
            'delta_sorted': list(sorted_d),
            'F_unsorted': 0,
            'F_sorted': f_sorted,
            'correction': correction,
            'is_nonzero': correction != 0,
        }
        cert['free_solutions'].append(sol)

        if correction == 0:
            cert['all_corrections_nonzero'] = False

    cert['n_free_solutions'] = len(cert['free_solutions'])
    cert['proof_status'] = 'PROVED' if cert['all_corrections_nonzero'] else 'FAILED'

    return cert


def main():
    print("FORMAL PROOF CERTIFICATES for k=3..8")
    print("=" * 60)

    all_certs = []
    for k in range(3, 9):
        cert = generate_proof_certificate(k)
        if cert is None: continue
        all_certs.append(cert)

        status = cert['proof_status']
        n = cert['n_free_solutions']
        print(f"\nk={k}: d={cert['d']}, free_solutions={n}, status={status}")

        if status == 'PROVED':
            corrections = [s['correction'] for s in cert['free_solutions']]
            print(f"  Corrections: {corrections}")
            print(f"  ALL nonzero: ✓")

            # Proof summary
            if k == 3:
                print(f"  PROOF (k=3): Single swap (δ₁,δ₂)→(δ₂,δ₁).")
                print(f"  Correction = ρ(1-ρ)(2^δ₂-2^δ₁) = (2/9)(2^δ₂-2^δ₁) mod {cert['d']}.")
                print(f"  Since gcd(2,{cert['d']})=1 and ord_{cert['d']}(2)={4} > S-k={2}:")
                print(f"  (2^|Δ|-1) ≢ 0 mod {cert['d']} for all Δ ≤ {cert['max_delta']}. QED.")

    # Save certificates
    out = '/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_log/proof_certificates_k3_k8.json'
    with open(out, 'w') as f:
        json.dump(all_certs, f, indent=2)
    print(f"\nCertificates saved to {out}")

    print("\n" + "=" * 60)
    print("SUMMARY")
    for cert in all_certs:
        print(f"  k={cert['k']}: {cert['n_free_solutions']} free solutions, "
              f"status={cert['proof_status']}")


if __name__ == '__main__':
    main()
