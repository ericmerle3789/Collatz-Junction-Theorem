#!/usr/bin/env python3
"""
SP9-O5b : Vérification mpmath des NOUVEAUX pires cas (D29, D30)
"""
import mpmath
mpmath.mp.dps = 50
from math import gcd, ceil, log

def compute_ord(base, p):
    r = 1
    for m in range(1, p):
        r = (r * base) % p
        if r == 1: return m
    return p - 1

def compute_rho_mpmath(p, m, max_c=10000):
    orbit = []
    h = 1
    for _ in range(m):
        orbit.append(h)
        h = (h * 2) % p
    assert len(set(orbit)) == m and h == 1
    best = mpmath.mpf(0)
    for c in range(1, min(p-1, max_c) + 1):
        sr, si = mpmath.mpf(0), mpmath.mpf(0)
        for hv in orbit:
            ang = 2 * mpmath.pi * mpmath.mpf((c * hv) % p) / p
            sr += mpmath.cos(ang)
            si += mpmath.sin(ang)
        amp = mpmath.sqrt(sr**2 + si**2) / m
        if amp > best: best = amp
    return float(best)

# Nouveaux pires cas SP9
NEW_WORST = [
    # (k, p, expected_m, label)
    (424, 6529, 102, "D29 — nouveau pire ρ"),
    (312, 165313, 246, "D30 — pire p/m²"),
    (96, 6553, 117, "SP8 pire ρ (contrôle)"),
    (260, 14951, 115, "D30b — p/m² = 1.13"),
    (182, 2857, 102, "Top6 ρ"),
]

print("=" * 65)
print("SP9-O5b : Vérification mpmath NOUVEAUX pires cas")
print("=" * 65)

all_pass = True
for k, p, expected_m, label in NEW_WORST:
    S = ceil(k * log(3) / log(2))
    m = compute_ord(2, p)
    assert m == expected_m, f"ord mismatch: {m} vs {expected_m} for p={p}"

    # p | d(k) ?
    assert (pow(2, S, p) - pow(3, k, p)) % p == 0, f"p={p} ∤ d({k})"

    # D25
    r = S % m
    assert pow(2, r, p) == pow(3, k, p), "D25 fail"

    # ρ mpmath
    rho = compute_rho_mpmath(p, m)
    pm2 = p / (m * m)

    # (Q)
    import math
    if rho > 0:
        log_conv = (k - 17) * math.log(rho) + math.log(p - 1)
        q_pass = log_conv < math.log(0.041)
    else:
        q_pass = True

    status = "PASS" if q_pass else "FAIL"
    if not q_pass: all_pass = False

    print(f"\n{label}:")
    print(f"  k={k}, p={p}, m={m}")
    print(f"  ρ (mpmath 50dp) = {rho:.15f}")
    print(f"  p/m² = {pm2:.6f}")
    print(f"  ρ_Weil = {pm2**0.5:.6f}")
    print(f"  D25 : PASS")
    print(f"  (Q)  : {status}", end="")
    if rho > 0:
        marge = 0.041 / (p - 1) / (rho ** (k - 17)) if (rho ** (k - 17)) > 0 else float('inf')
        print(f"  (marge = {marge:.2e})" if marge < 1e100 else "  (marge astronomique)")
    else:
        print()

print(f"\n{'='*65}")
if all_pass:
    print("VERDICT O5b : TOUS LES NOUVEAUX PIRES CAS VÉRIFIÉS ✓")
else:
    print("VERDICT O5b : ÉCHEC(S) DÉTECTÉ(S) !")
print("=" * 65)
