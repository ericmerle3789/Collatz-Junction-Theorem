#!/usr/bin/env python3
"""
SP10 Level 8 — DEBUG : Investigation des (Q) FAIL pour k=108, 114, 160, 174
=============================================================================
CRITICAL : Des echecs (Q) ont ete detectes. Il faut les analyser en detail.
Possibilites :
  a) Bug dans le calcul de rho_Weil (borne trop lache)
  b) Bug dans fast_order_2
  c) Veritable echec (ce serait un probleme pour le theoreme)
  d) Le facteur est en regime DI_B et rho_Weil > 1 mais rho_reel < seuil

ANTI-HALLUCINATION : on recalcule TOUT from scratch.
"""

import math
import cmath
import sys
from sympy import isprime, factorint, n_order

sys.stdout = open(sys.stdout.fileno(), mode='w', buffering=1)

def S(k):
    return int(math.ceil(k * math.log2(3)))

def compute_rho_exact(p, m, max_c=None):
    """Calcule rho EXACT = max_c |sum_{j=0}^{m-1} omega^{c*2^j}| / m"""
    if max_c is None:
        max_c = p - 1  # Exhaustif
    omega = cmath.exp(2j * cmath.pi / p)
    pows = [pow(2, j, p) for j in range(m)]
    max_val = 0
    for c in range(1, min(p, max_c + 1)):
        s = sum(omega ** ((c * pw) % p) for pw in pows)
        val = abs(s) / m
        if val > max_val:
            max_val = val
    return max_val

print("=" * 70)
print("DEBUG : Investigation des (Q) FAIL")
print("=" * 70)

fail_ks = [108, 114, 160, 174]

for k in fail_ks:
    print(f"\n{'='*70}")
    print(f"k = {k}")
    print(f"{'='*70}")

    Sk = S(k)
    dk = (1 << Sk) - 3**k
    if dk <= 0:
        Sk += 1
        dk = (1 << Sk) - 3**k

    print(f"  S(k) = {Sk}")
    print(f"  d(k) = 2^{Sk} - 3^{k}")
    print(f"  d(k) bits = {dk.bit_length()}")

    # Factorisation complete
    factors = factorint(dk)
    print(f"  Facteurs de d(k) :")

    for p_factor, exp in sorted(factors.items()):
        if not isprime(p_factor):
            print(f"    {p_factor}^{exp} (COMPOSITE - pas un vrai facteur)")
            continue

        # Calculer m = ord_p(2)
        m = n_order(2, p_factor)
        n_idx = (p_factor - 1) // m

        # Borne de Weil
        rho_weil = (1 + max(n_idx - 1, 0) * math.sqrt(p_factor)) / max(p_factor - 1, 1)
        ratio = p_factor / (m * m)

        regime = "WEIL" if ratio < 1 else ("DI_B" if ratio < m*m else "HARD")

        # Condition (Q) avec Weil
        if rho_weil < 1:
            q_weil = (p_factor - 1) * rho_weil ** (k - 17)
            q_weil_pass = q_weil < 0.041
        else:
            q_weil = float('inf')
            q_weil_pass = False

        print(f"\n    p = {p_factor}, m = ord_p(2) = {m}, n = (p-1)/m = {n_idx}")
        print(f"    p/m^2 = {ratio:.4f}, regime = {regime}")
        print(f"    rho_Weil = {rho_weil:.6f}, (Q)_Weil = {q_weil:.2e}, {'PASS' if q_weil_pass else 'FAIL'}")

        # Si (Q) FAIL avec Weil, calculer rho EXACT
        if not q_weil_pass or ratio >= 1:
            if p_factor < 10**7:
                print(f"    -> Calcul rho EXACT (p < 10^7, exhaustif)...")
                rho_exact = compute_rho_exact(p_factor, m)
                q_exact = (p_factor - 1) * rho_exact ** (k - 17)
                q_exact_pass = q_exact < 0.041
                print(f"    rho_exact = {rho_exact:.6f}")
                print(f"    (Q)_exact = {q_exact:.2e}, {'PASS ✓' if q_exact_pass else 'FAIL ⚠️'}")
                print(f"    Rapport rho_exact/rho_Weil = {rho_exact/max(rho_weil,1e-10):.4f}")
            elif p_factor < 10**9:
                print(f"    -> Calcul rho approx (p < 10^9, c=1..10000)...")
                rho_approx = compute_rho_exact(p_factor, m, max_c=10000)
                q_approx = (p_factor - 1) * rho_approx ** (k - 17)
                q_approx_pass = q_approx < 0.041
                print(f"    rho_approx = {rho_approx:.6f}")
                print(f"    (Q)_approx = {q_approx:.2e}, {'PASS ✓' if q_approx_pass else 'FAIL ⚠️'}")
            else:
                print(f"    -> p trop grand pour calcul direct ({p_factor.bit_length()} bits)")
                print(f"    STATUT : INDETERMINE")
        else:
            print(f"    -> (Q) PASS avec Weil, pas besoin de calcul exact")

print(f"\n{'='*70}")
print(f"SYNTHESE DEBUG")
print(f"{'='*70}")
print(f"""
Les FAIL (Q) avec la borne de Weil NE SONT PAS necessairement des echecs reels.
La borne de Weil donne rho <= (1 + (n-1)*sqrt(p)) / (p-1), qui est une
BORNE SUPERIEURE. Le rho reel est typiquement BEAUCOUP plus petit.

Si rho_exact donne (Q) PASS, alors le "FAIL" etait un faux positif de la borne.
""")
