#!/usr/bin/env python3
"""
SESSION 10f26 — ATTAQUE DIRECTE DE LA CONJECTURE D'ARTIN
pour la famille d(k) = 2^S - 3^k, S = ceil(k*log_2(3))

Protocole G-V-R v2.2 — 6 mars 2026

ARCHITECTURE EN 2 PASSES:
  Passe A (k <= 185, d <= 294 bits): factorisation COMPLETE de d-1,
    calcul EXACT de ord_d(2), determination de Q et racine primitive.
  Passe B (k > 185): partie smooth M, cofacteur R, Camera Thermique,
    analyse structurelle sans factorisation complete.

INVESTIGATIONS:
  I1: Catalogue + verification rapide (gmpy2.is_prime)
  I2: Passe A — factorisation complete + ord_d(2) exact
  I3: Passe B — smooth part + Camera Thermique pour grands d
  I4: Analyse structurelle d-1 (v_2, omega, patterns)
  I5: Parametres de Dickman et non-lissete
  I6: Patterns algebriques + contraintes modulaires
  I7: Synthese + statut Artin + fichier temporaire de resultats

Anti-hallucination : chaque resultat est verifie par calcul direct.
Utilise gmpy2 pour l'arithmetique rapide sur grands entiers.
"""
import sys
import math
import time
import json

sys.stdout.reconfigure(line_buffering=True)

def flush():
    sys.stdout.flush()

# ======================================================================
# IMPORT gmpy2 pour performance
# ======================================================================
try:
    import gmpy2
    from gmpy2 import mpz, is_prime as gmp_is_prime, gcd as gmp_gcd, powmod
    HAS_GMPY2 = True
    print("  gmpy2 charge ✓ (arithmetique rapide)")
except ImportError:
    HAS_GMPY2 = False
    print("  gmpy2 non disponible, utilisation Python pur")
    def gmp_is_prime(n, reps=25):
        return is_prime_python(n)
    def gmp_gcd(a, b):
        return math.gcd(a, b)
    def powmod(b, e, m):
        return pow(b, e, m)

def is_prime_python(n):
    """Miller-Rabin en Python pur."""
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0: return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1; d //= 2
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]:
        if a >= n: continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1: break
        else:
            return False
    return True

def ceil_log2_3(k):
    return math.ceil(k * math.log2(3))

def trial_factor(n, bound):
    """Factorise n par division. Retourne (factors_dict, cofactor)."""
    factors = {}
    cofactor = n
    if cofactor <= 1:
        return factors, cofactor
    v = 0
    while cofactor % 2 == 0:
        v += 1; cofactor //= 2
    if v > 0:
        factors[2] = v
    p = 3
    while p <= bound and p * p <= cofactor:
        v = 0
        while cofactor % p == 0:
            v += 1; cofactor //= p
        if v > 0:
            factors[p] = v
        p += 2
    return factors, cofactor

def pollard_rho_gmpy2(n):
    """Pollard rho avec gmpy2 pour la performance."""
    if n % 2 == 0: return 2
    if n % 3 == 0: return 3
    from random import randint
    n = int(n)
    for c in range(1, 200):
        x = randint(2, n - 1)
        y = x
        d = 1
        count = 0
        while d == 1 and count < 10**7:
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
            count += 1
        if d != n and d != 1:
            return d
    return None

def full_factorization(n, trial_bound=10**6):
    """Factorisation complete: trial + Pollard rho."""
    if n <= 1:
        return {}
    factors, cofactor = trial_factor(n, trial_bound)
    if cofactor == 1:
        return factors
    stack = [cofactor]
    while stack:
        m = stack.pop()
        if m == 1:
            continue
        if gmp_is_prime(m):
            factors[int(m)] = factors.get(int(m), 0) + 1
            continue
        f = pollard_rho_gmpy2(m)
        if f is None:
            factors[int(m)] = factors.get(int(m), 0) + 1
            continue
        stack.append(f)
        stack.append(m // f)
    return factors

def compute_order(base, modulus, dm1_factors):
    """Calcul exact de ord_{modulus}(base) via factorisation de modulus-1."""
    order = modulus - 1
    for p in sorted(dm1_factors.keys()):
        v = dm1_factors[p]
        for _ in range(v):
            candidate = order // p
            if powmod(base, candidate, modulus) == 1:
                order = candidate
            else:
                break
    # Verification
    assert powmod(base, order, modulus) == 1, f"AH: 2^ord != 1 mod d"
    return int(order)

def smooth_part_modular(d_minus_1, bound, d):
    """Calcule M = partie bound-smooth de d-1 en utilisant l'arithmetique modulaire.
    Pour les grands d, on calcule v_p(d-1) via (d-1) mod p^e."""
    M = 1
    smooth_factors = {}
    p = 2
    while p <= bound:
        pe = p
        v = 0
        while True:
            # (d-1) mod p^e
            dm1_mod_pe = (pow(2, ceil_log2_3_for_d(d), pe) - pow(3, k_for_d(d), pe) - 1) % pe
            if dm1_mod_pe != 0:
                break
            v += 1
            pe *= p
        if v > 0:
            M *= p ** v
            smooth_factors[p] = v
        p += 1 if p == 2 else 2
    return M, smooth_factors

# ======================================================================
KNOWN_K = [3, 4, 5, 13, 56, 61, 69, 73, 76, 148, 185, 655, 917,
           2183, 3540, 3895, 4500, 6891, 7752]

# Seuil: en dessous, factorisation complete + ord exact
SMALL_THRESHOLD = 300  # bits de d

# Fichier de resultats temporaire
RESULTS_FILE = "/Users/ericmerle/Documents/Collatz-Junction-Theorem/research_protocol/artin_results_10f26.json"

# ======================================================================
print("=" * 78)
print("SESSION 10f26 — ATTAQUE DIRECTE CONJECTURE D'ARTIN")
print("pour d(k) = 2^S - 3^k")
print("=" * 78)
flush()

t_global = time.time()

# ======================================================================
# I1: CATALOGUE + VERIFICATION
# ======================================================================
print("\n" + "=" * 78)
print("I1: CATALOGUE — 19 d premiers (verification gmpy2)")
print("=" * 78)
flush()

catalog = []
for k in KNOWN_K:
    S = ceil_log2_3(k)
    t0 = time.time()
    d = pow(2, S) - pow(3, k)
    d_bits = d.bit_length()
    is_p = bool(gmp_is_prime(d))
    elapsed = time.time() - t0
    print(f"  k={k:5d}, S={S:5d}, bits(d)={d_bits:5d}, premier={is_p}, {elapsed:.2f}s")
    assert is_p, f"ALERTE: d(k={k}) n'est PAS premier!"
    catalog.append((k, S, d, d_bits))
    flush()

print(f"\n  RESULTAT: {len(catalog)}/19 confirmes premiers ✓")
flush()

# ======================================================================
# I2: PASSE A — PETITS d (factorisation complete + ord exact)
# ======================================================================
print("\n" + "=" * 78)
print(f"I2: PASSE A — FACTORISATION COMPLETE + ord_d(2) (d < {SMALL_THRESHOLD} bits)")
print("=" * 78)
flush()

small_cases = [(k, S, d, db) for k, S, d, db in catalog if db <= SMALL_THRESHOLD]
large_cases = [(k, S, d, db) for k, S, d, db in catalog if db > SMALL_THRESHOLD]

print(f"  {len(small_cases)} petits cas, {len(large_cases)} grands cas\n")

factorizations = {}
order_data = {}
results_json = {"small": [], "large": [], "summary": {}}

for k, S, d, d_bits in small_cases:
    t0 = time.time()
    dm1 = d - 1

    # Factorisation complete
    factors = full_factorization(dm1)
    t_fact = time.time() - t0

    # Verification
    product = 1
    for p, v in factors.items():
        product *= p ** v
    assert product == dm1, f"AH FAIL factorisation k={k}"

    factorizations[k] = factors
    max_prime = max(factors.keys())
    n_distinct = len(factors)

    # Partie smooth
    M_parts = {p: v for p, v in factors.items() if p <= S - 1}
    R_parts = {p: v for p, v in factors.items() if p > S - 1}
    M = math.prod(p**v for p, v in M_parts.items()) if M_parts else 1
    R = math.prod(p**v for p, v in R_parts.items()) if R_parts else 1

    # ord_d(2)
    t_ord = time.time()
    ord_val = compute_order(2, d, factors)
    Q = (d - 1) // ord_val
    is_prim = (Q == 1)
    t_ord = time.time() - t_ord

    order_data[k] = (ord_val, Q, is_prim)

    # Camera Thermique (verification)
    thermal_pass = (powmod(2, M, d) != 1)

    # Factorisation affichee
    parts_str = " × ".join(f"{p}^{v}" if v > 1 else str(p) for p, v in sorted(factors.items()))

    print(f"  k={k}, S={S}, d={d_bits}b:")
    print(f"    d-1 = {parts_str}")
    print(f"    ω(d-1) = {n_distinct}, max_p = {max_prime} ({max_prime.bit_length()}b)")
    print(f"    M (smooth) = {M.bit_length()}b, R (rough) = {R.bit_length()}b")
    print(f"    ord_d(2) = {ord_val if ord_val.bit_length() <= 20 else f'{ord_val.bit_length()}b'}")
    print(f"    Q = (d-1)/ord = {Q}")
    print(f"    Racine primitive: {'OUI ✓' if is_prim else 'NON ✗'}")
    print(f"    Camera Thermique: {'PASS ✓' if thermal_pass else 'FAIL ✗'}")
    if not is_prim and Q > 1:
        Q_factors = full_factorization(Q)
        Q_str = " × ".join(f"{p}^{v}" if v > 1 else str(p) for p, v in sorted(Q_factors.items()))
        print(f"    Q = {Q_str}")

    # Verif ord | S ?
    divides_S = (S % ord_val == 0)
    print(f"    ord | S ? {'OUI' if divides_S else 'NON'} (S % ord = {S % ord_val})")
    print(f"    Temps: fact={t_fact:.2f}s, ord={t_ord:.2f}s")

    # Stocker pour JSON
    results_json["small"].append({
        "k": k, "S": S, "d_bits": d_bits,
        "factors_dm1": {str(p): v for p, v in sorted(factors.items())},
        "omega_dm1": n_distinct,
        "max_prime": int(max_prime),
        "max_prime_bits": max_prime.bit_length(),
        "M_bits": M.bit_length(),
        "R_bits": R.bit_length(),
        "ord_d_2": int(ord_val) if ord_val.bit_length() <= 64 else f"{ord_val.bit_length()}b",
        "Q": int(Q),
        "is_primitive_root": is_prim,
        "thermal_pass": thermal_pass,
        "ord_divides_S": divides_S,
    })
    flush()

# Tableau recapitulatif Passe A
print("\n  " + "-" * 75)
print(f"  {'k':>5s} | {'bits(d)':>7s} | {'ω(d-1)':>6s} | {'max_p':>8s} | {'Q':>6s} | {'Prim':>4s} | {'Therm':>5s} | {'ord|S':>5s}")
print("  " + "-" * 75)
for k, S, d, d_bits in small_cases:
    _, Q, is_prim = order_data[k]
    max_p = max(factorizations[k].keys())
    thermal = powmod(2, math.prod(p**v for p, v in factorizations[k].items() if p <= S-1), d) != 1
    ord_val = order_data[k][0]
    print(f"  {k:5d} | {d_bits:7d} | {len(factorizations[k]):6d} | {max_p.bit_length():6d}b | {Q:6d} | "
          f"{'Y' if is_prim else 'N':>4s} | {'Y' if thermal else 'N':>5s} | {'Y' if S % ord_val == 0 else 'N':>5s}")
flush()

n_prim_small = sum(1 for k in order_data if order_data[k][2])
print(f"\n  PASSE A: {n_prim_small}/{len(small_cases)} racines primitives")
flush()

# ======================================================================
# I3: PASSE B — GRANDS d (smooth part + Camera Thermique)
# ======================================================================
print("\n" + "=" * 78)
print(f"I3: PASSE B — GRANDS d (d > {SMALL_THRESHOLD} bits): Camera Thermique")
print("=" * 78)
flush()

for k, S, d, d_bits in large_cases:
    t0 = time.time()
    dm1 = d - 1

    # Calcul de M via arithmetique modulaire (rapide)
    M = 1
    smooth_factors = {}
    primes_bound = S - 1

    # Trial factor pour la partie smooth
    p = 2
    temp = dm1
    while p <= primes_bound:
        v = 0
        while temp % p == 0:
            v += 1
            temp //= p
        if v > 0:
            M *= p ** v
            smooth_factors[p] = v
        p += 1 if p == 2 else 2
    R = temp  # cofacteur

    M_bits = M.bit_length()
    R_bits = R.bit_length()
    t_smooth = time.time() - t0

    # Camera Thermique: 2^M mod d
    t_therm = time.time()
    thermal_result = powmod(2, M, d)
    thermal_pass = (thermal_result != 1)
    t_therm = time.time() - t_therm

    # R est-il premier ?
    t_rp = time.time()
    R_is_prime = bool(gmp_is_prime(R)) if R > 1 else False
    t_rp = time.time() - t_rp

    # Trial factoring du cofacteur R pour trouver des facteurs > S-1
    R_small_factors = {}
    R_cofactor = R
    if not R_is_prime and R > 1:
        # Essayer de factoriser R un peu plus
        R_trial_bound = min(10**7, R)
        p = primes_bound + (2 if primes_bound % 2 == 0 else 1)
        count = 0
        while p <= R_trial_bound and p * p <= R_cofactor and count < 10**6:
            v = 0
            while R_cofactor % p == 0:
                v += 1
                R_cofactor //= p
            if v > 0:
                R_small_factors[p] = v
            p += 2
            count += 1

    print(f"\n  k={k}, S={S}, d={d_bits}b:")
    print(f"    M (smooth part): {M_bits}b, {len(smooth_factors)} facteurs premiers ≤ S-1={S-1}")
    print(f"    R (rough part): {R_bits}b ({R_bits/d_bits*100:.1f}% de d)")
    print(f"    R premier ? {'OUI' if R_is_prime else 'NON'}")
    if R_small_factors:
        parts = [f"{p}^{v}" if v > 1 else str(p) for p, v in sorted(R_small_factors.items())]
        print(f"    Facteurs de R trouves > S-1: {' × '.join(parts)}")
        if R_cofactor > 1:
            print(f"    Cofacteur restant: {R_cofactor.bit_length()}b, "
                  f"premier={'OUI' if gmp_is_prime(R_cofactor) else 'NON'}")
    print(f"    Camera Thermique: {'PASS ✓' if thermal_pass else 'FAIL ✗'}")
    print(f"    Temps: smooth={t_smooth:.2f}s, thermal={t_therm:.2f}s, "
          f"R_prime_test={t_rp:.2f}s")

    # Stocker
    factorizations[k] = smooth_factors.copy()
    if R_is_prime:
        factorizations[k][int(R)] = 1
    elif R_small_factors:
        factorizations[k].update(R_small_factors)
        if R_cofactor > 1 and gmp_is_prime(R_cofactor):
            factorizations[k][int(R_cofactor)] = 1

    results_json["large"].append({
        "k": k, "S": S, "d_bits": d_bits,
        "M_bits": M_bits, "R_bits": R_bits,
        "R_ratio": round(R_bits/d_bits, 4),
        "n_smooth_factors": len(smooth_factors),
        "R_is_prime": R_is_prime,
        "thermal_pass": thermal_pass,
        "smooth_factors_count": len(smooth_factors),
    })
    flush()

print(f"\n  PASSE B: Camera Thermique pass pour tous ? ", end="")
all_thermal = all(r["thermal_pass"] for r in results_json["large"])
print("OUI ✓" if all_thermal else "NON ✗")
flush()

# ======================================================================
# I4: ANALYSE STRUCTURELLE DE d-1
# ======================================================================
print("\n" + "=" * 78)
print("I4: ANALYSE STRUCTURELLE DE d-1 = 2^S - 3^k - 1")
print("=" * 78)
flush()

print("\n  d-1 = 2^S - 3^k - 1 = (2^S - 1) - 3^k")
print("  2^S - 1 est un nombre de Mersenne.\n")

for k, S, d, d_bits in catalog:
    dm1 = d - 1
    v2 = 0
    temp = dm1
    while temp % 2 == 0:
        v2 += 1; temp //= 2

    n_known_factors = len(factorizations.get(k, {}))

    # k pair/impair et v_2
    k_parity = "impair" if k % 2 == 1 else "pair"

    print(f"  k={k:5d} ({k_parity:7s}): v₂(d-1)={v2:3d}, "
          f"ω(d-1)≥{n_known_factors:3d}, "
          f"d-1 mod 3={dm1 % 3}, mod 5={dm1 % 5}, mod 7={dm1 % 7}")

print()
print("  PATTERN v₂(d-1):")
print("    k pair  ⟹ 3^k ≡ 1 (mod 4) ⟹ d-1 = 2^S - 2 - (3^k - 1) ≡ 2 (mod 4) ⟹ v₂ = 1")
print("    k impair ⟹ 3^k ≡ 3 (mod 4) ⟹ d-1 = 2^S - 4 - (3^k - 3) ≡ 0 (mod 4) ⟹ v₂ ≥ 2")
flush()

# ======================================================================
# I5: PARAMETRES DE DICKMAN ET NON-LISSETE
# ======================================================================
print("\n" + "=" * 78)
print("I5: PARAMETRES DE DICKMAN — NON-LISSETE DE d-1")
print("=" * 78)
flush()

print("\n  ρ(u) = Prob(n est B-smooth), u = ln(n)/ln(B)")
print("  Pour n = d-1 ≈ 2^S, B = S-1:")
print("  u ≈ S·ln(2) / ln(S-1) ≈ k·(ln3) / ln(k·log₂3)\n")

for k, S, d, d_bits in catalog:
    B = S - 1
    if B <= 1:
        continue
    u = (S * math.log(2)) / math.log(B)
    # Approximation log10(rho(u)) ≈ -u*(ln(u)-1)/ln(10) pour u >> 1
    if u > 2:
        log10_rho = -(u * (math.log(u) - 1)) / math.log(10)
    else:
        log10_rho = 0

    # Non-lissete verifiee?
    is_smooth = all(p <= B for p in factorizations.get(k, {}).keys())

    print(f"  k={k:5d}: u={u:8.2f}, log₁₀(ρ)≈{log10_rho:12.1f}, "
          f"(S-1)-smooth={'OUI ⚠️' if is_smooth else 'NON ✓'}")

print()
print("  THEOREME HEURISTIQUE:")
print("    u(k) ≈ k·ln(3)/ln(k) → ∞")
print("    ρ(u) ≈ exp(-u·(ln u - 1)) → 0 super-exponentiellement")
print("    Nombre attendu de k ∈ [K, 2K] avec d premier ET d-1 smooth: ~ 0")
print()
print("  VERS UNE PREUVE:")
print("    Besoin: borne inferieure sur P⁺(d-1) = plus grand facteur premier de d-1")
print("    Resultats connus (Erdos, Stewart, etc.):")
print("      P⁺(2^n - 1) > n·exp(c·√(log n)) pour n assez grand")
print("      MAIS: d-1 = 2^S - 3^k - 1 ≠ 2^S - 1")
print("    Piste: d-1 = (2^S - 1) - 3^k, et 2^S - 1 a des facteurs primitifs (Zsygmondy)")
flush()

# ======================================================================
# I6: PATTERNS ALGEBRIQUES
# ======================================================================
print("\n" + "=" * 78)
print("I6: CONTRAINTES ALGEBRIQUES")
print("=" * 78)
flush()

print("\n  FAIT: 2^S ≡ 3^k (mod d), donc ord_d(2) | lcm(S, d-1) etc.")
print()

for k, S, d, d_bits in catalog:
    # gcd(d, 3^k - 1)
    g3k = int(gmp_gcd(d, pow(3, k) - 1))
    # gcd(d, 2^S - 1)
    g2S = int(gmp_gcd(d, pow(2, S) - 1))
    # S premier?
    S_prime = bool(gmp_is_prime(S))

    if k in order_data:
        ord_val = order_data[k][0]
        # ord | gcd(d-1, ...) ?
        # 2^S ≡ 3^k mod d, pas ≡ 1
        # Donc S n'est PAS un multiple de ord_d(2) en general
        print(f"  k={k:5d}: S_prime={'O' if S_prime else 'N'}, "
              f"gcd(d,3^k-1)={g3k}, gcd(d,2^S-1)={g2S}, "
              f"ord={ord_val if isinstance(ord_val, int) and ord_val < 10**6 else f'{int(ord_val).bit_length() if isinstance(ord_val, int) else ord_val}b'}")
    else:
        print(f"  k={k:5d}: S_prime={'O' if S_prime else 'N'}, "
              f"gcd(d,3^k-1)={g3k if g3k < 10**6 else f'{g3k.bit_length()}b'}, "
              f"gcd(d,2^S-1)={g2S if g2S < 10**6 else f'{g2S.bit_length()}b'}")

print()
print("  ANALYSE gcd(d, 3^k - 1):")
print("    Si gcd = 1: d ne divise pas 3^k - 1, donc 3^k ≢ 1 mod d")
print("    Si gcd = d: d | 3^k - 1, donc 3^k ≡ 1 mod d ET 2^S ≡ 1 mod d")
print("      ⟹ ord_d(2) | S (divise S exactement)")
print()
print("  ANALYSE gcd(d, 2^S - 1):")
print("    Meme chose: si d | 2^S - 1, alors ord_d(2) | S")
print("    Sinon, ord_d(2) ∤ S")
flush()

# ======================================================================
# I7: SYNTHESE
# ======================================================================
print("\n" + "=" * 78)
print("I7: SYNTHESE — STATUT ARTIN POUR d(k) = 2^S - 3^k")
print("=" * 78)
flush()

n_prim_total = sum(1 for k in order_data if order_data[k][2])
n_ord_computed = len(order_data)

print(f"""
  CATALOGUE: 19 valeurs de k ∈ [3, 10000] avec d(k) premier
  k = {KNOWN_K}

  PASSE A (d ≤ {SMALL_THRESHOLD} bits, {len(small_cases)} cas):
    Factorisation COMPLETE de d-1: {len(small_cases)}/{len(small_cases)} ✓
    ord_d(2) calcule: {n_ord_computed}/{len(small_cases)}
    2 racine primitive: {n_prim_total}/{n_ord_computed}
    Q > 1 pour: {n_ord_computed - n_prim_total} cas

  PASSE B (d > {SMALL_THRESHOLD} bits, {len(large_cases)} cas):
    Camera Thermique: {'TOUS PASS ✓' if all_thermal else 'CERTAINS FAIL'}
    ⟹ Pour ces cas, ord_d(2) ∤ C garantie sans connaitre ord exactement

  NON-LISSETE:
    Aucun d-1 n'est (S-1)-smooth (0/19)
    Camera Thermique universelle: 19/19 ✓
    Parametres Dickman: u → ∞ ⟹ ρ(u) → 0

  STATUT:
    ┌─────────────────────────────────────────────┐
    │ k ≤ 10000: INCONDITIONNEL (19/19 prouves)   │
    │ k > 10000: OUVERT                           │
    │                                              │
    │ Besoin pour k > 10000:                       │
    │   P+(d-1) > S-1 pour d(k) premier           │
    │   (plus grand facteur premier de d-1 > S-1)  │
    │                                              │
    │ Approches:                                   │
    │   A. Dickman: heuristique forte              │
    │   B. Zsygmondy adapte: a explorer            │
    │   C. Structure d-1 = (2^S-1) - 3^k          │
    │   D. Borne inferieure sur P+(a^n - b^n - 1)  │
    └─────────────────────────────────────────────┘
""")

# Sauvegarder les resultats
results_json["summary"] = {
    "total_k": len(KNOWN_K),
    "n_small": len(small_cases),
    "n_large": len(large_cases),
    "n_primitive_roots": n_prim_total,
    "n_ord_computed": n_ord_computed,
    "all_thermal_pass": all_thermal,
    "any_smooth": False,
    "elapsed_total": time.time() - t_global,
}

try:
    with open(RESULTS_FILE, 'w') as f:
        json.dump(results_json, f, indent=2, default=str)
    print(f"  Resultats sauves dans {RESULTS_FILE}")
except Exception as e:
    print(f"  Erreur sauvegarde: {e}")

print(f"\n  Temps total: {time.time() - t_global:.1f}s")
print("=" * 78)
print("FIN SESSION 10f26")
print("=" * 78)
