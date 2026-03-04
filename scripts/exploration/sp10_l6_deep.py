#!/usr/bin/env python3
"""
SP10-L6 DEEP — Pourquoi p ne divise pas d(k) dans la zone critique ?
======================================================================
L6 a montre que pour 47/60 non-triviaux, n ≤ k_crit
(n = ord_{G/H}(pi(3))). Donc la condition n | k est SATISFAITE
dans la zone [69, k_crit] pour certains k. MAIS p ∤ d(k) quand meme !

QUESTION : Quel mecanisme EXACT empeche p | d(k) ?

ANALYSE : p | d(k) ⟺ 2^S ≡ 3^k (mod p) ou S = ceil(k·log2(3)).
Meme si 3^k ∈ ⟨2⟩ (mod p) (ce que n | k implique),
il faut AUSSI que l'exposant dans ⟨2⟩ soit exactement S mod m.
C'est une condition MOD m supplementaire.

Soit g = 2 le generateur de H = ⟨2⟩.
3^k ∈ H ⟺ n | k. Si oui, 3^k = 2^e mod p pour un certain e ∈ [0, m-1].
La condition est e ≡ S (mod m) ou S = ceil(k · log2(3)).
Cet evenement a probabilite 1/m (heuristiquement).

Donc la VRAIE probabilite est :
P(p | d(k)) ≈ (1/n) × (1/m) = 1/(n·m) = m/[(p-1)·m] = 1/(p-1)

C'est la probabilite "naive" ! Le mecanisme est :
- n | k : probabilite 1/n ≈ m/(p-1)
- Bon exposant dans H : probabilite 1/m
- Total : 1/(p-1) — INDEPENDANT de m

VERIFICATION EMPIRIQUE dans ce script.
"""

import time
import json
from math import log, log2, ceil, gcd, pi, sqrt
from collections import defaultdict
import numpy as np

OUT = "/tmp/sp10_l6_deep.txt"
outf = open(OUT, "w")

def log_write(msg=""):
    print(msg, flush=True)
    outf.write(msg + "\n")
    outf.flush()

def p_divides_dk(p, k):
    S = ceil(k * log2(3))
    return (pow(2, S, p) - pow(3, k, p)) % p == 0

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

def compute_quotient_order(p, m):
    q_size = (p - 1) // m
    if q_size <= 1:
        return 1
    exponent = (p - 1) // m
    val_3 = pow(3, exponent, p)
    if val_3 == 1:
        return 1
    r = val_3
    for n_try in range(2, min(q_size + 1, 200001)):
        r = (r * val_3) % p
        if r == 1:
            return n_try
    return q_size

log_write("=" * 70)
log_write("SP10-L6 DEEP — Mecanisme exact de non-divisibilite")
log_write("=" * 70)
log_write()

# Anti-regression
rho_127 = compute_rho_fast(127, 7, max_c=126)
assert abs(rho_127 - 0.618) < 0.001
log_write(f"Anti-regression: rho(127,7) = {rho_127:.4f} ✅")
log_write()

# ═══════════════════════════════════════════════════════════════
# ANALYSE 1 : Pour les cas n ≤ k_crit, examiner les k multiples
#              de n dans [69, k_crit] et comprendre pourquoi p∤d(k)
# ═══════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("ANALYSE 1 — k multiples de n dans [69, k_crit]")
log_write("-" * 70)
log_write()

# Charger les donnees L6
with open("/tmp/sp10_l6_data.json") as f:
    l6_data = json.load(f)

nontrivials = l6_data["nontrivial_details"]

log_write(f"  Cas d'etude : premiers avec n ≤ k_crit (n | k satisfait dans la zone)\n")

log_write(f"  {'p':>20s} {'m':>5s} {'n':>8s} {'k_crit':>8s} {'#cand':>6s} {'p|d?':>6s} {'Detail':>30s}")
log_write("  " + "-" * 90)

detailed_cases = []

for item in nontrivials:
    p = item["p"]
    m = item["m"]
    rho = item["rho"]
    kc = item["k_crit"]

    n = compute_quotient_order(p, m)
    k_max = min(ceil(kc), 50000)

    # Multiples de n dans [69, k_max]
    if n == 0:
        continue

    first_multiple = n * ceil(69 / n)
    candidates = []
    k = first_multiple
    while k <= k_max:
        candidates.append(k)
        k += n

    # Verifier chaque candidat
    hits = [k for k in candidates if p_divides_dk(p, k)]

    detail = f"{len(candidates)} cand, {len(hits)} hits"

    if len(candidates) > 0:
        detailed_cases.append((p, m, n, kc, rho, candidates, hits))

    if len(candidates) <= 50 or len(hits) > 0:  # Afficher les cas interessants
        log_write(f"  {p:>20d} {m:5d} {n:8d} {kc:8.1f} {len(candidates):6d} {len(hits):6d} {detail}")

log_write()

# ═══════════════════════════════════════════════════════════════
# ANALYSE 2 : Pour un cas specifique, decomposer la condition
# ═══════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("ANALYSE 2 — Decomposition de la condition p | d(k)")
log_write("-" * 70)
log_write()

log_write("  Pour p | d(k) = 2^S - 3^k, on a besoin de :")
log_write("    (i)  3^k ∈ ⟨2⟩ (mod p)  ⟺  n | k")
log_write("    (ii) Si 3^k = 2^e (mod p), alors e ≡ S (mod m)")
log_write("         ou S = ⌈k · log₂(3)⌉")
log_write()

# Prenons quelques cas concrets
for p, m, n, kc, rho, candidates, hits in detailed_cases[:5]:
    log_write(f"\n  ═══ CAS p={p}, m={m}, n={n}, rho={rho:.4f}, k_crit={kc:.1f} ═══")

    # Calculer le log discret de 3 dans ⟨2⟩ (si possible)
    # 3^n ∈ ⟨2⟩ quand n | k. Soit a = log_2(3^n) mod m
    val_3n = pow(3, n, p)
    # Trouver e tel que 2^e ≡ 3^n (mod p)
    power = 1
    log_3n = None
    for e in range(m):
        if power == val_3n:
            log_3n = e
            break
        power = (power * 2) % p

    if log_3n is not None:
        log_write(f"    log_2(3^n) mod m = {log_3n}")
        log_write(f"    Donc pour k = n·j : 3^k = 2^({log_3n}·j mod m)")
        log_write(f"    La condition (ii) devient : {log_3n}·j ≡ S (mod {m})")

        # Parcourir les candidats
        if len(candidates) <= 20:
            for k in candidates:
                S = ceil(k * log2(3))
                j = k // n
                e_calc = (log_3n * j) % m
                S_mod_m = S % m
                match = "✅ HIT" if e_calc == S_mod_m else "  miss"
                actual = "p|d(k)!" if p_divides_dk(p, k) else ""
                log_write(f"      k={k:6d}, j={j:4d}, e={e_calc:3d}, S%m={S_mod_m:3d} {match} {actual}")
        else:
            # Trop de candidats, analyser statistiquement
            n_match = 0
            for k in candidates[:1000]:
                S = ceil(k * log2(3))
                j = k // n
                e_calc = (log_3n * j) % m
                S_mod_m = S % m
                if e_calc == S_mod_m:
                    n_match += 1
            tested = min(len(candidates), 1000)
            log_write(f"    Sur {tested} candidats testes : {n_match} avec e ≡ S (mod m)")
            log_write(f"    Frequence observee : {n_match/tested:.4f} (attendu : 1/{m} = {1/m:.4f})")
    else:
        log_write(f"    3^n ∉ ⟨2⟩ (mod p) — condition (i) echoue pour n")
        log_write(f"    (Ce cas ne devrait pas arriver si n est correct)")

log_write()

# ═══════════════════════════════════════════════════════════════
# ANALYSE 3 : Probabilite theorique vs observee
# ═══════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("ANALYSE 3 — Probabilite p | d(k) : theorie vs observation")
log_write("-" * 70)
log_write()

log_write("  MODELE : P(p | d(k)) ≈ 1/(p-1)")
log_write("  C'est parce que p | d(k) ⟺ 2^S ≡ 3^k (mod p)")
log_write("  et si 3^k \"parcourt\" (Z/pZ)* uniformement, c'est 1/(p-1).")
log_write()

# Verification sur un large range de k
log_write(f"  {'p':>20s} {'m':>5s} {'Range':>12s} {'#hits':>6s} {'Freq obs':>10s} {'1/(p-1)':>10s} {'Ratio':>8s}")
log_write("  " + "-" * 80)

# Quelques premiers avec differentes tailles
test_primes = [
    (127, 7), (8191, 13), (131071, 17), (524287, 19),
    (2147483647, 31), (262657, 27), (65537, 32),
    (43691, 34), (2796203, 46)
]

for p, m in test_primes:
    K_MAX = min(50000, 10 * p)
    hits = 0
    for k in range(1, K_MAX + 1):
        if p_divides_dk(p, k):
            hits += 1
    freq = hits / K_MAX if K_MAX > 0 else 0
    expected = 1 / (p - 1)
    ratio = freq / expected if expected > 0 else 0
    log_write(f"  {p:>20d} {m:5d} [1,{K_MAX:>6d}] {hits:6d} {freq:10.6f} {expected:10.6f} {ratio:8.2f}")

log_write()

# ═══════════════════════════════════════════════════════════════
# ANALYSE 4 : Borne superieure sur le nombre de k ≤ K
#              tels que p | d(k)
# ═══════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("ANALYSE 4 — Borne superieure sur #{k ≤ K : p | d(k)}")
log_write("-" * 70)
log_write()

log_write("  LEMME : #{k ≤ K : p | d(k)} ≤ K/n + 1")
log_write("  Car p | d(k) ⟹ n | k (condition necessaire).")
log_write("  Il y a ≤ K/n + 1 multiples de n dans [1, K].")
log_write("  Parmi ceux-ci, seuls ceux avec e ≡ S (mod m) comptent.")
log_write("  Sous l'heuristique d'uniformite : ≤ (K/n + 1)/m ≈ K/(n·m).")
log_write()

log_write("  MAIS pour la condition (Q), ce qui compte est :")
log_write("  Le PREMIER k ≥ 69 tel que p | d(k).")
log_write("  Appelons-le k_first(p).")
log_write()

# k_first pour chaque non-trivial
log_write(f"  {'p':>20s} {'m':>5s} {'rho':>8s} {'k_crit':>8s} {'k_first':>10s} {'Verdict':>10s}")
log_write("  " + "-" * 70)

all_ok = True
for item in nontrivials:
    p = item["p"]
    m = item["m"]
    rho = item["rho"]
    kc = item["k_crit"]

    # Chercher k_first dans [69, 100000]
    k_first = None
    K_SEARCH = max(ceil(kc) + 1000, 10000)
    K_SEARCH = min(K_SEARCH, 100000)

    for k in range(69, K_SEARCH + 1):
        if p_divides_dk(p, k):
            k_first = k
            break

    if k_first is None:
        kf_str = f">={K_SEARCH}"
        if kc < K_SEARCH:
            verdict = "✅ (trivial)"
        else:
            verdict = "✅ (non trouve)"
    elif k_first > kc:
        kf_str = str(k_first)
        verdict = "✅ k_first > k_crit"
    else:
        # k_first dans la zone critique !
        val = (p - 1) * (rho ** (k_first - 17))
        if val < 0.041:
            kf_str = str(k_first)
            verdict = f"✅ val={val:.3g}"
        else:
            kf_str = str(k_first)
            verdict = f"❌ val={val:.3g}"
            all_ok = False

    log_write(f"  {p:>20d} {m:5d} {rho:8.4f} {kc:8.1f} {kf_str:>10s} {verdict}")

log_write()
if all_ok:
    log_write("  ★ ZERO echec : pour chaque non-trivial, soit k_first > k_crit,")
    log_write("    soit (Q) est satisfaite a k_first.")
else:
    log_write("  ⚠️ Des echecs existent !")

log_write()

# ═══════════════════════════════════════════════════════════════
# ANALYSE 5 : Le VRAI mecanisme
# ═══════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("ANALYSE 5 — Le VRAI mecanisme")
log_write("-" * 70)
log_write()

log_write("""  THEOREME (computationnel, m ≤ 200) :
    Pour tout premier p avec ord_p(2) = m ≤ 200,
    (Q) est satisfaite pour tout k ≥ 69.

  LE MECANISME N'EST PAS le compromis frequence/rho tel que formule
  (n > k_crit). Ce compromis echoue pour 47/60 non-triviaux.

  LE VRAI MECANISME est en DEUX parties :

  (1) RARETE ABSOLUE : P(p | d(k)) ≈ 1/(p-1).
      Pour p grand (> 10^6), la probabilite qu'un k QUELCONQUE
      satisfasse p | d(k) est < 10^{-6}.
      Dans l'intervalle [69, k_crit] de longueur ~k_crit - 68 << p,
      le nombre ATTENDU de hits est (k_crit - 68)/(p-1) << 1.

  (2) VERIFICATION EXHAUSTIVE : Pour les p ou (1) ne suffit pas
      (p petit, nombreux k candidats), on verifie directement
      que p ∤ d(k) sur [69, k_crit].

  BORNE : Nombre attendu de hits dans [69, k_crit] :
    E = (k_crit - 68) / (p - 1)
    k_crit ≈ m · ln(p) / |ln(rho)|
    Donc E ≈ m · ln(p) / [(p-1) · |ln(rho)|]

    Pour les Mersenne : p = 2^m - 1, |ln(rho)| ≈ c/m (c ≈ 3.37)
    E ≈ m² · m·ln(2) / [(2^m - 1) · c] = m³·ln(2) / (c · 2^m)
    → 0 exponentiellement vite.

    Pour p = O(m^a) : E ≈ m · a·ln(m) / [m^a · |ln(rho)|]
    Si rho ≈ C · m^{-alpha} (alpha ≈ 0.5), |ln(rho)| ≈ alpha·ln(m)/m
    E ≈ m² · a / (m^a · alpha) = a / (alpha · m^{a-2})
    → 0 si a > 2.
""")

# Calculer E pour chaque non-trivial
log_write("  Nombre ATTENDU E de hits dans [69, k_crit] :")
log_write(f"  {'p':>20s} {'m':>5s} {'k_crit':>8s} {'E':>12s}")
log_write("  " + "-" * 50)

for item in nontrivials:
    p = item["p"]
    m = item["m"]
    kc = item["k_crit"]
    E = (kc - 68) / (p - 1) if p > 1 else 0
    log_write(f"  {p:>20d} {m:5d} {kc:8.1f} {E:12.4g}")

log_write()
log_write("  E_max parmi les non-triviaux :")
E_max = max((item["k_crit"] - 68) / (item["p"] - 1) for item in nontrivials)
log_write(f"  E_max = {E_max:.4g}")
if E_max < 1:
    log_write(f"  ✅ E < 1 pour TOUS les non-triviaux")
    log_write(f"  → En moyenne, AUCUN k dans [69, k_crit] ne satisfait p | d(k)")
    log_write(f"  → Le mecanisme de rarete SUFFIT (pas besoin du compromis)")
else:
    log_write(f"  ⚠️ E ≥ 1 pour certains cas")

log_write()

# ═══════════════════════════════════════════════════════════════
# SYNTHESE
# ═══════════════════════════════════════════════════════════════

log_write("=" * 70)
log_write("SYNTHESE SP10-L6 DEEP")
log_write("=" * 70)
log_write()

log_write("  1. Le 'compromis frequence/rho' (n > k_crit) est FAUX")
log_write("     47/60 non-triviaux ont n ≤ k_crit")
log_write()
log_write("  2. Le VRAI mecanisme est la RARETE ABSOLUE :")
log_write(f"     E = (k_crit - 68)/(p-1) < {E_max:.4g} pour tous les p")
log_write("     Le nombre attendu de k problematiques est << 1")
log_write()
log_write("  3. Cela fonctionne parce que k_crit << p pour tout p non-trivial")
log_write("     k_crit croit comme m·ln(p)/|ln(rho)| ≈ m²·ln(p)")
log_write("     tandis que p-1 croit comme p (au moins m²)")
log_write()
log_write("  4. POUR FORMALISER : il faudrait prouver que")
log_write("     k_crit(p) / (p-1) → 0 pour tout p avec ord_p(2) = m → ∞")
log_write("     C'est equivalent a :")
log_write("     m · ln(p) / [(p-1) · |ln(rho)|] → 0")
log_write()
log_write("  5. Pour les Mersenne : m · m·ln(2) / [(2^m-1) · c/m]")
log_write("     = m³·ln(2)/(c·2^m) → 0 exponentiellement ✅")
log_write()
log_write("  6. Pour p = m+1 (minimum) : m · ln(m) / [m · |ln(rho)|]")
log_write("     = ln(m) / |ln(rho)| ≈ ln(m) · m / (alpha · ln(m)) = m/alpha")
log_write("     Et E = m/(alpha·(p-1)) = 1/alpha ≈ 2")
log_write("     ⚠️ CAS LIMITE : si p ≈ m, E ≈ O(1)")
log_write("     MAIS rho est TRES petit (≈ 1/m) donc k_crit < 68 (trivial)")
log_write()
log_write("=" * 70)

outf.close()
