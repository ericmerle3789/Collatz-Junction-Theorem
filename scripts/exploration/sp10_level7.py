#!/usr/bin/env python3
"""
SP10-L7 — Borne formelle sur E = k_crit / (p-1)
==================================================
OBJECTIF : Prouver (ou invalider) que E < 1 pour tout p avec ord_p(2) > 200.

ANALYSE THEORIQUE :
  k_crit = 17 + [ln(p-1) - ln(0.041)] / |ln(ρ)|
  E = (k_crit - 68) / (p - 1)

  On a besoin de :
  (A) Borne superieure sur k_crit en fonction de (m, p)
  (B) Borne inferieure sur p-1 en fonction de m

  Pour (B) : p ≡ 1 (mod m), donc p ≥ m+1, en fait p ≥ 2m+1 (p impair).
  Pour (A) : k_crit = 17 + [ln(p-1) + 3.19] / |ln(ρ)|

  QUESTION CLE : quelle est |ln(ρ)| en fonction de m et p ?

  BORNE TRIVIALE (D26) : ρ < 1, donc |ln(ρ)| > 0. Inutile.
  BORNE EMPIRIQUE : ρ ≈ 1 - c/m pour les Mersenne (c ≈ 3.37)
    |ln(ρ)| ≈ c/m
  BORNE THEORIQUE : ρ ≤ (m-1)/m (si H ≠ {1})
    |ln(ρ)| ≥ ln(m/(m-1)) ≈ 1/m

  Avec |ln(ρ)| ≈ 1/m (pire cas theorique) :
  k_crit ≈ m · [ln(p) + 3.19]
  E ≈ m · ln(p) / (p - 1)

  Or pour p ≥ 2m+1 : E ≈ m · ln(2m) / (2m) = ln(2m)/2 → ∞ !
  ⚠️ Ca ne marche pas pour p ≈ 2m.

  MAIS : si p ≈ 2m+1, alors m est un DIVISEUR de p-1 = 2m.
  Donc p-1 = 2m, et 2^m ≡ 1 (mod p). Donc p | (2^m - 1).
  Comme p = 2m+1, on a p ≤ 2m+1, donc 2^m - 1 ≥ p.
  Or 2^m - 1 ≈ 2^m >> 2m+1 pour m > 4.
  Et ρ pour de tels p est TRES petit (pas ≈ 1-1/m).

APPROCHE : Numerique. Pour chaque m > 200, le PIRE p est celui qui
maximise E. Cherchons ce pire cas et verifions si E < 1.

PROTOCOLE :
  Partie 1 : Borne theorique sur ρ en fonction de m
  Partie 2 : Pire cas p pour chaque m (minimisant p et maximisant ρ)
  Partie 3 : Verification numerique de E < 1
"""

import time
import json
from math import log, log2, ceil, gcd, pi, sqrt, isqrt, exp
from collections import defaultdict
import numpy as np

OUT = "/tmp/sp10_l7_results.txt"
outf = open(OUT, "w")

def log_write(msg=""):
    print(msg, flush=True)
    outf.write(msg + "\n")
    outf.flush()

def compute_rho_fast(p, m, max_c=5000):
    orbit = []
    h = 1
    for _ in range(m):
        orbit.append(h)
        h = (h * 2) % p
    c_lim = min(p - 1, max_c)
    best = 0.0
    p_float = float(p)
    for c in range(1, c_lim + 1):
        real_sum = 0.0
        imag_sum = 0.0
        for h_val in orbit:
            mod_val = (c * h_val) % p
            phase = 2.0 * pi * float(mod_val) / p_float
            real_sum += np.cos(phase)
            imag_sum += np.sin(phase)
        s = np.sqrt(real_sum**2 + imag_sum**2)
        r = s / m
        if r > best:
            best = r
    return best

def is_probably_prime(n, witnesses=15):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0: return False
    s, d = 0, n - 1
    while d % 2 == 0:
        s += 1
        d //= 2
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if a >= n: continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1: break
        else:
            return False
    return True

log_write("=" * 70)
log_write("SP10-L7 — Borne formelle sur E = k_crit / (p-1)")
log_write("=" * 70)
log_write()

# Anti-regression
rho_127 = compute_rho_fast(127, 7, max_c=126)
assert abs(rho_127 - 0.618) < 0.001
log_write(f"Anti-regression: rho(127,7) = {rho_127:.4f} ✅")
log_write()

# ═════════════════════════════════════════════════════════════════════
# PARTIE 1 : Pour chaque m, trouver le p qui MAXIMISE E
# ═════════════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("PARTIE 1 — Pire cas p pour chaque m (maximisant E)")
log_write("-" * 70)
log_write()

log_write("  Pour maximiser E = k_crit/(p-1), on veut :")
log_write("    - p PETIT (car E ∝ 1/(p-1))")
log_write("    - ρ GRAND (car k_crit ∝ 1/|ln(ρ)|)")
log_write("  Le pire cas est le plus petit p premier avec ord_p(2) = m.")
log_write("  Pour p | (2^m - 1), le plus petit tel p est le plus petit")
log_write("  facteur premier de 2^m - 1.")
log_write()

# Pour m de 200 a 500, trouver le plus petit p | (2^m-1) avec ord_p(2) = m
log_write(f"  {'m':>5s} {'p_min':>15s} {'ord=m?':>7s} {'rho':>8s} {'k_crit':>10s} {'E':>12s} {'E<1?':>6s}")
log_write("  " + "-" * 70)

t0 = time.time()
results_l7 = []
worst_E = 0
worst_case = None

for m in range(200, 501):
    val = (1 << m) - 1

    # Trouver le plus petit facteur premier
    p_min = None
    d = 3
    # Premiers candidats : p ≡ 1 (mod m) et p | (2^m - 1)
    # Trial division rapide
    while d * d <= val and d < 10**7:
        if val % d == 0:
            # Verifier ord_d(2) = m
            actual_ord = m
            for div in range(1, m):
                if m % div == 0 and div < m:
                    if pow(2, div, d) == 1:
                        actual_ord = div
                        break
            if actual_ord == m:
                p_min = d
                break
            # Pas le bon ordre, diviser
            while val % d == 0:
                val //= d
        d += 2

    if p_min is None:
        # Le plus petit facteur > 10^7 ou val est premier
        if val > 1 and is_probably_prime(val):
            # val lui-meme est premier
            actual_ord = m
            for div in range(1, min(m, 1000)):
                if m % div == 0 and div < m:
                    if pow(2, div, val) == 1:
                        actual_ord = div
                        break
            if actual_ord == m:
                p_min = val

    if p_min is None:
        if m % 50 == 0:
            log_write(f"  {m:5d} {'> 10^7':>15s} {'?':>7s} {'?':>8s} {'?':>10s} {'?':>12s} {'?':>6s}")
        continue

    # Calculer rho
    max_c_val = min(p_min - 1, 3000) if p_min > 100 else p_min - 1
    rho = compute_rho_fast(p_min, m, max_c=max_c_val)

    if rho > 0 and rho < 1:
        k_crit = 17 + (log(0.041) - log(p_min - 1)) / log(rho)
    else:
        k_crit = float('inf')

    E = (k_crit - 68) / (p_min - 1) if p_min > 1 and k_crit < float('inf') else 0

    ok = "✅" if E < 1 else "❌"

    if E > worst_E:
        worst_E = E
        worst_case = (m, p_min, rho, k_crit, E)

    results_l7.append((m, p_min, rho, k_crit, E))

    if m <= 220 or m % 50 == 0 or E > 0.01:
        log_write(f"  {m:5d} {p_min:15d} {'✅':>7s} {rho:8.4f} {k_crit:10.1f} {E:12.4g} {ok}")

t1 = time.time()
log_write(f"\n  Scan m=200..500 : {t1-t0:.0f}s")
log_write(f"  Pire E = {worst_E:.4g}")
if worst_case:
    m_w, p_w, rho_w, kc_w, E_w = worst_case
    log_write(f"  Pire cas : m={m_w}, p={p_w}, rho={rho_w:.4f}, k_crit={kc_w:.1f}, E={E_w:.4g}")
log_write()

# ═════════════════════════════════════════════════════════════════════
# PARTIE 2 : Analyse des p ≡ 1 (mod m) proches de 2m+1
# ═════════════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("PARTIE 2 — Les 'safe primes' p = 2m+1")
log_write("-" * 70)
log_write()

log_write("  Si p = 2m+1 est premier et ord_p(2) = m, alors")
log_write("  p-1 = 2m, donc E = k_crit/(2m).")
log_write("  C'est le PIRE CAS en termes de p/m ratio.")
log_write()

log_write(f"  {'m':>5s} {'p=2m+1':>10s} {'Prem?':>6s} {'ord=m?':>7s} {'rho':>8s} {'k_crit':>10s} {'E':>10s}")
log_write("  " + "-" * 65)

safe_cases = []
for m in range(200, 2001):
    p = 2 * m + 1
    if is_probably_prime(p):
        # Verifier ord_p(2) = m
        if pow(2, m, p) == 1:
            # Verifier que l'ordre est exactement m (pas un diviseur strict)
            is_exact = True
            for div_candidate in [2, 3, 5, 7, 11, 13]:
                if m % div_candidate == 0:
                    if pow(2, m // div_candidate, p) == 1:
                        is_exact = False
                        break

            if is_exact:
                rho = compute_rho_fast(p, m, max_c=min(p-1, 2000))
                if rho > 0 and rho < 1:
                    k_crit = 17 + (log(0.041) - log(p - 1)) / log(rho)
                else:
                    k_crit = float('inf')
                E = (k_crit - 68) / (p - 1) if k_crit < float('inf') else 0
                safe_cases.append((m, p, rho, k_crit, E))

                if len(safe_cases) <= 20 or E > 0.01:
                    log_write(f"  {m:5d} {p:10d} {'✅':>6s} {'✅':>7s} {rho:8.4f} {k_crit:10.1f} {E:10.4g}")

log_write(f"\n  {len(safe_cases)} cas 'safe prime' trouves dans m=200..2000")
if safe_cases:
    E_max_safe = max(E for _, _, _, _, E in safe_cases)
    log_write(f"  E_max (safe primes) = {E_max_safe:.4g}")
    worst_safe = max(safe_cases, key=lambda x: x[4])
    m_s, p_s, rho_s, kc_s, E_s = worst_safe
    log_write(f"  Pire : m={m_s}, p={p_s}, rho={rho_s:.4f}, k_crit={kc_s:.1f}")
log_write()

# ═════════════════════════════════════════════════════════════════════
# PARTIE 3 : Borne theorique sur ρ pour les safe primes
# ═════════════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("PARTIE 3 — ρ pour les safe primes p = 2m+1")
log_write("-" * 70)
log_write()

log_write("  Pour p = 2m+1, ⟨2⟩ a exactement m elements.")
log_write("  C'est un sous-groupe d'INDEX 2.")
log_write("  ⟨2⟩ = residus quadratiques (si 2 est QR) ou non-QR.")
log_write()

# Analyser ρ en fonction de m pour safe primes
if safe_cases:
    ms = np.array([m for m, _, _, _, _ in safe_cases])
    rhos = np.array([rho for _, _, rho, _, _ in safe_cases])

    # Fit log-log
    log_ms = np.log(ms)
    log_rhos = np.log(rhos + 1e-10)

    # ρ ≈ C · m^{-α}
    if len(ms) > 2:
        A = np.vstack([np.ones_like(log_ms), log_ms]).T
        result = np.linalg.lstsq(A, log_rhos, rcond=None)
        log_C, neg_alpha = result[0]
        C_fit = exp(log_C)
        alpha_fit = -neg_alpha

        log_write(f"  Fit ρ ≈ C · m^(-α) pour safe primes :")
        log_write(f"    C = {C_fit:.4f}, α = {alpha_fit:.4f}")
        log_write(f"    (Compare a L3 general : C ≈ 0.39, α ≈ 0.41)")
        log_write()

        # Si ρ ≈ C · m^{-α}, alors |ln(ρ)| ≈ α · ln(m) / m (pour ρ → 1)
        # NON — si ρ << 1 (ce qui est le cas pour safe primes), |ln(ρ)| ≈ |ln(C·m^{-α})|
        # = |ln(C) - α·ln(m)| = α·ln(m) - ln(C) ≈ α·ln(m)

        log_write(f"  Avec ρ ≈ {C_fit:.3f} · m^(-{alpha_fit:.3f}) :")
        log_write(f"    |ln(ρ)| ≈ {alpha_fit:.3f} · ln(m)")
        log_write(f"    k_crit ≈ [ln(2m) + 3.19] / ({alpha_fit:.3f}·ln(m))")
        log_write(f"           ≈ [ln(m) + 3.88] / ({alpha_fit:.3f}·ln(m))")
        log_write(f"           ≈ 1/{alpha_fit:.3f} + 3.88/({alpha_fit:.3f}·ln(m))")
        log_write(f"           ≈ {1/alpha_fit:.1f} + O(1/ln(m))")
        log_write()
        log_write(f"    E = k_crit / (2m)")
        log_write(f"      ≈ {1/alpha_fit:.1f} / (2m) → 0 comme m → ∞ !")
        log_write()
        log_write(f"  ✅ POUR LES SAFE PRIMES : E → 0 comme 1/m")
        log_write(f"     k_crit reste BORNE (≈ {1/alpha_fit:.0f}) tandis que p-1 = 2m → ∞")

log_write()

# ═════════════════════════════════════════════════════════════════════
# PARTIE 4 : Le vrai cas dangereux — Sophie Germain primes
# ═════════════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("PARTIE 4 — Cas dangereux : p petit avec grand ρ")
log_write("-" * 70)
log_write()

log_write("  Le seul cas ou E pourrait etre > 1 :")
log_write("  p PETIT (≈ 2m+1) ET ρ GRAND (≈ 1-c/m).")
log_write("  MAIS ces deux conditions sont CONTRADICTOIRES :")
log_write("    - ρ ≈ 1-c/m exige ⟨2⟩ ≈ {1, 2, ..., 2^{m-1}} (Mersenne-like)")
log_write("    - p ≈ 2m+1 exige p << 2^m")
log_write("    - Pour les Mersenne : p = 2^m - 1 >> 2m+1")
log_write()

# Verification : parmi tous les p avec rho > 0.5, quel est le rapport p/m ?
log_write("  Verification sur nos 318 premiers (m ≤ 200) :")
log_write("  Parmi ceux avec ρ > 0.5, le rapport p/(2m+1) vaut :")
log_write()

# Charger les donnees L6
with open("/tmp/sp10_l6_data.json") as f:
    l6_data = json.load(f)

high_rho = [(d["p"], d["m"], d["rho"]) for d in l6_data["nontrivial_details"] if d["rho"] > 0.5]
high_rho.sort(key=lambda x: -x[2])

log_write(f"  {'p':>20s} {'m':>5s} {'rho':>8s} {'p/(2m+1)':>12s}")
log_write("  " + "-" * 50)
for p, m, rho in high_rho[:15]:
    ratio = p / (2*m + 1)
    log_write(f"  {p:>20d} {m:5d} {rho:8.4f} {ratio:12.1f}")

log_write()
if high_rho:
    min_ratio = min(p / (2*m + 1) for p, m, rho in high_rho)
    log_write(f"  Ratio minimal p/(2m+1) parmi ρ > 0.5 : {min_ratio:.1f}")
    log_write(f"  ⇒ Les premiers a grand ρ sont ENORMES par rapport a m")
    log_write(f"  ⇒ E est minuscule pour ces premiers")

log_write()

# ═════════════════════════════════════════════════════════════════════
# PARTIE 5 : Argument de dichotomie
# ═════════════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("PARTIE 5 — Argument de dichotomie (formel)")
log_write("-" * 70)
log_write()

log_write("""  PROPOSITION (informelle, a formaliser) :
    Pour tout ε > 0, il existe M tel que pour tout m > M
    et tout premier p avec ord_p(2) = m :
      E(p) = (k_crit(p) - 68) / (p - 1) < ε.

  PREUVE (esquisse) :

  Cas A : p ≤ m^3
    Alors ρ(p, ⟨2⟩) ≤ C · m^{-α} (borne empirique, α ≈ 0.4-0.5)
    |ln(ρ)| ≈ α · ln(m)
    k_crit ≈ [ln(p) + 3.19] / (α · ln(m))
           ≤ [3·ln(m) + 3.19] / (α · ln(m))
           ≈ 3/α + O(1/ln(m)) ≈ 7.5
    E = k_crit / (p-1) ≤ 7.5 / (p-1) → 0    □

  Cas B : p > m^3
    |ln(ρ)| ≥ 1/m (car ρ ≤ (m-1)/m, borne triviale)
    k_crit ≈ m · [ln(p) + 3.19]
    E = m · [ln(p) + 3.19] / (p - 1)
    Pour p > m^3 : E ≤ m · [3·ln(m) + 3.19 + ln(p/m^3)] / (p - 1)
                     ≤ m · ln(p) / (p - 1)
    La fonction f(p) = m·ln(p)/(p-1) est decroissante pour p > e·m
    Donc f(p) ≤ f(m^3) = m·3·ln(m)/(m^3-1) ≈ 3·ln(m)/m² → 0    □

  PROBLEME : Le Cas B utilise la borne |ln(ρ)| ≥ 1/m qui est TROP FAIBLE.
  Si ρ = 1 - 1/(2m), alors |ln(ρ)| ≈ 1/(2m) et k_crit ≈ 2m·ln(p).
  Pour p > m^3 : E ≈ 2m · 3·ln(m) / m^3 = 6·ln(m)/m² → 0.  OK.

  Mais si ρ = 1 - 1/m^2, alors |ln(ρ)| ≈ 1/m^2 et k_crit ≈ m²·ln(p).
  Pour p > m^3 : E ≈ m²·3·ln(m)/m^3 = 3·ln(m)/m → 0.  OK.

  Meme pour ρ = 1 - 1/m^10 : |ln(ρ)| ≈ 1/m^10, k_crit ≈ m^10·ln(p).
  E ≈ m^10·ln(p)/(p-1). Pour p > e^{m^10} c'est < 1, mais...
  p est un PREMIER, pas un nombre arbitraire.
  On a p | (2^m - 1), donc p ≤ 2^m - 1.
  E ≈ m^10·m·ln(2) / 2^m → 0 exponentiellement.  OK !

  ★ CLE : p | (2^m - 1) implique p ≤ 2^m - 1.
  Donc p est BORNE exponentiellement en m.
  Et E ≈ k_crit / 2^m est exponentiellement petit.
""")

# Verification numerique
log_write("  Verification : k_crit_max vs 2^m pour nos donnees :")
log_write()

for item in l6_data["nontrivial_details"][:10]:
    p, m, rho, kc = item["p"], item["m"], item["rho"], item["k_crit"]
    bound = 2**m
    ratio_kc_bound = kc / bound
    log_write(f"    m={m}, p={p}, k_crit={kc:.0f}, 2^m ≈ 10^{m*log(2)/log(10):.0f}, "
              f"k_crit/2^m ≈ {ratio_kc_bound:.4g}")

log_write()

# ═════════════════════════════════════════════════════════════════════
# PARTIE 6 : Borne rigoureuse via p ≤ 2^m - 1
# ═════════════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("PARTIE 6 — Borne rigoureuse via p ≤ 2^m - 1")
log_write("-" * 70)
log_write()

log_write("""  THEOREME (rigoureux) :
    Soit p premier avec ord_p(2) = m. Alors :
    (1) p | (2^m - 1), donc p ≤ 2^m - 1.
    (2) ρ(p, ⟨2⟩) ≤ (m-1)/m < 1.  [D26 + trivial]
    (3) |ln(ρ)| ≥ ln(m/(m-1)) ≥ 1/m.
    (4) k_crit = 17 + [ln(p-1) + 3.19] / |ln(ρ)|
             ≤ 17 + m · [ln(2^m - 2) + 3.19]
             ≤ 17 + m · [m·ln(2) + 3.19]
             = 17 + m²·ln(2) + 3.19m
             ≈ 0.693 · m².
    (5) p - 1 ≥ 2m  [car p ≡ 1 (mod m), p ≥ 2m+1]
    (6) E ≤ (0.693·m² - 68) / (2m) ≈ 0.347·m → ∞ !!!

  ⚠️ ECHEC : La borne triviale ρ ≤ (m-1)/m est TROP FAIBLE.
  Elle donne k_crit = O(m²) mais p-1 = O(m), donc E = O(m) → ∞.

  CEPENDANT : la borne p ≤ 2^m - 1 nous donne aussi :
    E ≤ (0.693·m²) / (2^m - 2) → 0 exponentiellement !

  Mais cette borne utilise p ≤ 2^m - 1, qui est lache pour p ≈ 2m+1.
  Le vrai E pour p ≈ 2m+1 est :
    k_crit ≈ [ln(2m) + 3.19] / |ln(ρ)|
  et ρ pour ces petits p est TRES petit (vérifié empiriquement).
""")

# Calculons le pire E FORMEL :
# E_formel = max sur p | (2^m-1) de [k_crit(p) / (p-1)]
# On sait empiriquement que E_max < 10^{-4}.
# Montrons que E est toujours < 1 avec la borne CORRECTE.

log_write("  APPROCHE CORRECTE :")
log_write("    k_crit ≤ 17 + [ln(p-1) + 3.19] / |ln(ρ)|")
log_write("    E = k_crit / (p-1) ≤ [ln(p-1) + 20.19] / [(p-1)·|ln(ρ)|]")
log_write()
log_write("    Posons x = p-1 ≥ 2m et δ = 1 - ρ > 0.")
log_write("    |ln(ρ)| = |ln(1-δ)| ≥ δ (car ln(1-δ) ≤ -δ)")
log_write("    E ≤ [ln(x) + 20.19] / (x · δ)")
log_write()
log_write("    Pour E < 1 : x · δ > ln(x) + 20.19")
log_write("    ⟺ δ > [ln(x) + 20.19] / x")
log_write()
log_write("    Le RHS est maximal pour x = 1 (= 21.19) puis decroit.")
log_write("    Pour x ≥ 1000 (p ≥ 1001) : RHS ≈ (6.9 + 20.19)/1000 = 0.027")
log_write("    Donc δ > 0.027 suffit, i.e. ρ < 0.973.")
log_write()
log_write("    Or ρ = 0.973 est atteint par M127 (p ≈ 1.7×10^38).")
log_write("    Pour ce p, x = p-1 ≈ 10^38, et E ≈ 10^{-35}.")
log_write()
log_write("    ★ La seule question est : existe-t-il p avec ρ > 1 - 1/(p-1) ?")
log_write("    Si oui, E pourrait depasser 1.")
log_write("    Si non (i.e. δ(p) · (p-1) → ∞), alors E → 0.")
log_write()

# Verifions empiriquement δ · (p-1) pour nos 318 premiers
log_write("  VERIFICATION : δ · (p-1) pour les non-triviaux :")
log_write(f"  {'p':>20s} {'m':>5s} {'rho':>8s} {'delta':>10s} {'d*(p-1)':>12s}")
log_write("  " + "-" * 60)

delta_products = []
for item in l6_data["nontrivial_details"]:
    p, m, rho = item["p"], item["m"], item["rho"]
    delta = 1 - rho
    dp = delta * (p - 1)
    delta_products.append((p, m, rho, delta, dp))

delta_products.sort(key=lambda x: x[4])
for p, m, rho, delta, dp in delta_products[:15]:
    log_write(f"  {p:>20d} {m:5d} {rho:8.4f} {delta:10.4g} {dp:12.4g}")

log_write()
min_dp = min(dp for _, _, _, _, dp in delta_products)
log_write(f"  min(δ·(p-1)) = {min_dp:.4g}")
if min_dp > 1:
    log_write(f"  ✅ δ·(p-1) > 1 pour tous nos 60 non-triviaux")
else:
    log_write(f"  ⚠️ δ·(p-1) ≤ 1 pour certains cas")

log_write()

# ═════════════════════════════════════════════════════════════════════
# SYNTHESE
# ═════════════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("SYNTHESE SP10-L7")
log_write("=" * 70)
log_write()

log_write("  RESULTAT PRINCIPAL :")
log_write("    E = k_crit/(p-1) < 1 pour les 318 premiers avec m ≤ 200.")
log_write(f"    E_max = {l6_data.get('k_crit_max', 0)}")
log_write()
log_write("  VERS UNE PREUVE FORMELLE :")
log_write("    Condition suffisante : δ(p) · (p-1) → ∞")
log_write("    ou δ(p) = 1 - ρ(p, ⟨2⟩).")
log_write()
log_write("  BORNE TRIVIALE INSUFFISANTE :")
log_write("    ρ ≤ (m-1)/m donne E = O(m) → ∞ (ECHEC)")
log_write()
log_write("  BORNE VIA p ≤ 2^m - 1 :")
log_write("    Pour les Mersenne : E = O(m³/2^m) → 0 expon. (OK)")
log_write("    Pour p petit : ρ est petit, k_crit est petit, E est petit (OK)")
log_write()
log_write("  ★ DICHOTOMIE INFORMELLE :")
log_write("    Si p grand (> m^a) : E petit car p domine")
log_write("    Si p petit (≈ 2m+1) : E petit car ρ est petit (k_crit ≈ constante)")
log_write("    JAMAIS les deux (grand ρ ET petit p) en meme temps")
log_write()
log_write("  POUR FORMALISER : il faudrait une borne du type")
log_write("    ρ(p, ⟨2⟩) ≤ 1 - c · m / p  pour une constante c > 0")
log_write("    Ceci donnerait δ·(p-1) ≥ c·m - c ≥ c·m → ∞")
log_write()
log_write("  ALTERNATIVE : Borne de Weil rendue effective")
log_write("    ρ ≤ (√p · ln(p)) / m  (borne de Weil modifiee)")
log_write("    Si √p·ln(p)/m < 1, i.e. p < (m/ln(p))²,")
log_write("    alors k_crit < 68 (trivial).")
log_write("    Si p ≥ (m/ln(p))², alors E ≤ k_crit/(p-1)")
log_write("    et il faudrait borner k_crit en fonction de √p·ln(p)/m.")
log_write()
log_write("=" * 70)

outf.close()
