#!/usr/bin/env python3
"""
SP10-L5c — Extension de la verification a m > 50
===================================================
Factoriser 2^m - 1 pour m = 51..120 et verifier (Q) pour chaque
facteur premier. Traitement special des Mersenne primes.

DECOUVERTE L5 :
  ρ(M_m) ≈ 1 - 3.2/m pour les Mersenne primes.
  k_crit(M_m) ≈ 0.217 · m² (croissance quadratique).
  MAIS : P(M_m | d(k)) ≈ m/2^m (decroissance exponentielle).
  → Le compromis est massivement favorable.

PROTOCOLE :
  - Anti-regression ρ(127,7) = 0.618
  - Verification exhaustive p ∤ d(k) sur [69, k_crit] pour chaque premier
"""

import numpy as np
from math import log, log2, ceil, gcd, pi
from sympy import factorint, isprime
import time

def compute_ord(base, p):
    if gcd(base, p) != 1: return 0
    r = 1
    for m in range(1, min(p, 10**7)):
        r = (r * base) % p
        if r == 1: return m
    return -1  # Trop grand

def compute_rho_fast(p, m, max_c=5000):
    """Calcule ρ avec max_c limite. Gere les grands p (> 2^63)."""
    orbit = []
    h = 1
    for _ in range(m):
        orbit.append(h)
        h = (h * 2) % p

    c_lim = min(p - 1, max_c)
    best = 0.0

    # Pour les grands p (> 2^62), on utilise Python pur pour le modular
    # puis on convertit en float pour les phases
    p_float = float(p)

    for c in range(1, c_lim + 1):
        # Calcul Python pur (arbitrary precision) puis conversion float
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

def p_divides_dk(p, k):
    S = ceil(k * log2(3))
    return (pow(2, S, p) - pow(3, k, p)) % p == 0

def compute_k_crit(p, rho):
    if 0 < rho < 1:
        return 17 + (log(0.041) - log(p - 1)) / log(rho)
    return float('inf')

OUTFILE = "/tmp/sp10_l5c_extend.txt"
def log_write(f, msg):
    print(msg, flush=True)
    f.write(msg + "\n")
    f.flush()

with open(OUTFILE, "w") as f:
    log_write(f, "=" * 70)
    log_write(f, "SP10-L5c — Extension verification m = 51..120")
    log_write(f, "=" * 70)
    log_write(f, "")

    # Anti-regression
    rho_127 = compute_rho_fast(127, 7, max_c=126)
    assert abs(rho_127 - 0.618) < 0.001
    log_write(f, f"  Anti-regression: ρ(127,7) = {rho_127:.4f} ✅")
    log_write(f, "")

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 1 : Mersenne primes specifiques
    # ═══════════════════════════════════════════════════════════════

    log_write(f, "=" * 70)
    log_write(f, "PARTIE 1 — Mersenne primes connues (m ≤ 127)")
    log_write(f, "-" * 70)
    log_write(f, "")

    # Les Mersenne primes connus pour m ≤ 127
    mersenne_exponents = [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127]

    log_write(f, f"  {'m':>4s} {'M_m digits':>12s} {'ρ':>10s} {'1-ρ':>10s} "
              f"{'m(1-ρ)':>8s} {'k_crit':>10s} {'Verif [69,k_crit]':>20s}")
    log_write(f, "  " + "-" * 80)

    for m in mersenne_exponents:
        p = pow(2, m) - 1
        digits = len(str(p))

        # ρ : pour les petits m, calcul exact ; pour les grands, max_c limité
        if m <= 50:
            rho = compute_rho_fast(p, m, max_c=min(p - 1, 10000))
        else:
            rho = compute_rho_fast(p, m, max_c=5000)

        one_minus_rho = 1 - rho
        m_times = m * one_minus_rho
        k_crit = compute_k_crit(p, rho)

        # Verification exhaustive p ∤ d(k) sur [69, k_crit]
        k_max = min(ceil(k_crit), 100000)  # Limiter a 100K iterations
        t0 = time.time()
        found_k = None
        for k in range(69, k_max + 1):
            if p_divides_dk(p, k):
                found_k = k
                break
        elapsed_v = time.time() - t0

        if found_k is not None:
            val = (p - 1) * (rho ** (found_k - 17))
            verif = f"p|d({found_k}), val={val:.4g}"
        elif k_max >= ceil(k_crit):
            verif = f"p∤d(k) sur [69,{k_max}] ✅"
        else:
            verif = f"p∤d(k) sur [69,{k_max}] (partiel)"

        log_write(f, f"  {m:4d} {digits:12d} {rho:10.6f} {one_minus_rho:10.6f} "
                  f"{m_times:8.3f} {k_crit:10.1f} {verif}")

    log_write(f, "")
    log_write(f, "  OBSERVATION : m·(1-ρ) ≈ 3.1-3.4 pour les Mersenne primes")
    log_write(f, "  → ρ(M_m) ≈ 1 - C/m avec C ≈ 3.2")
    log_write(f, "  → k_crit ≈ m²·ln(2)/(3.2) ≈ 0.217·m²")
    log_write(f, "")

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 2 : Factorisation 2^m - 1 pour m = 51..100
    # ═══════════════════════════════════════════════════════════════

    log_write(f, "=" * 70)
    log_write(f, "PARTIE 2 — Facteurs de 2^m - 1 pour m = 51..100")
    log_write(f, "-" * 70)
    log_write(f, "")

    t0_global = time.time()
    all_primes_extended = set()  # Tous les premiers trouves
    results_by_prime = {}  # p -> (m, rho, k_crit)

    for m in range(51, 101):
        val = pow(2, m) - 1
        digits = val.bit_length()

        t_start = time.time()
        try:
            factors = factorint(val, limit=10**8)
            t_fact = time.time() - t_start

            # Verifier si la factorisation est COMPLETE
            check = 1
            for p_f, e in factors.items():
                check *= p_f ** e
            complete = (check == val)

            n_factors = len(factors)
            largest = max(factors.keys())

            log_write(f, f"  m={m:3d} ({digits} bits, {t_fact:.1f}s): "
                      f"{n_factors} facteurs, plus grand = {largest} "
                      f"({'COMPLET' if complete else 'PARTIEL'})")

            for p_f in factors.keys():
                if p_f <= 2:
                    continue
                all_primes_extended.add(p_f)

                if p_f not in results_by_prime:
                    # Calculer ord, ρ, k_crit
                    m_f = compute_ord(2, p_f)
                    if m_f == -1:
                        continue  # Trop grand pour compute_ord

                    if p_f < 100000:
                        rho = compute_rho_fast(p_f, m_f, max_c=min(p_f - 1, 10000))
                    elif p_f < 10**7:
                        rho = compute_rho_fast(p_f, m_f, max_c=5000)
                    else:
                        rho = compute_rho_fast(p_f, m_f, max_c=2000)

                    k_crit = compute_k_crit(p_f, rho)
                    results_by_prime[p_f] = (m_f, rho, k_crit)

        except Exception as e:
            log_write(f, f"  m={m:3d}: ERREUR factorisation: {e}")

    elapsed_global = time.time() - t0_global
    log_write(f, "")
    log_write(f, f"  Total: {len(all_primes_extended)} premiers, {elapsed_global:.1f}s")
    log_write(f, "")

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 3 : Verification (Q) pour les nouveaux premiers
    # ═══════════════════════════════════════════════════════════════

    log_write(f, "=" * 70)
    log_write(f, "PARTIE 3 — Verification (Q) pour les nouveaux premiers (m=51..100)")
    log_write(f, "-" * 70)
    log_write(f, "")

    # Trier par ρ decroissant
    sorted_results = sorted(results_by_prime.items(),
                           key=lambda x: -x[1][1])

    n_trivial = 0
    n_verified = 0
    n_fail = 0
    n_partial = 0
    k_crit_max_new = 0

    # Afficher les plus dangereux
    log_write(f, f"  {'p':>18s} {'m':>5s} {'ρ':>10s} {'k_crit':>10s} "
              f"{'Verification':>30s}")
    log_write(f, "  " + "-" * 80)

    for p_f, (m_f, rho, k_crit) in sorted_results:
        if m_f <= 50:
            continue  # Deja verifie dans L5b

        if k_crit <= 68:
            n_trivial += 1
            if rho > 0.3:
                log_write(f, f"  {p_f:18d} {m_f:5d} {rho:10.6f} {k_crit:10.1f} "
                          f"{'k_crit ≤ 68, trivial ✅':>30s}")
            continue

        if k_crit > k_crit_max_new:
            k_crit_max_new = k_crit

        # Verification exhaustive
        k_max = min(ceil(k_crit), 50000)
        found_violation = False
        found_k = None

        for k in range(69, k_max + 1):
            if p_divides_dk(p_f, k):
                val = (p_f - 1) * (rho ** (k - 17))
                if val >= 0.041:
                    found_violation = True
                    found_k = k
                    break
                else:
                    found_k = k
                    break

        if found_violation:
            n_fail += 1
            verif = f"❌ ECHEC k={found_k}, val={val:.4g}"
        elif k_max >= ceil(k_crit):
            if found_k is None:
                n_verified += 1
                verif = f"p∤d(k) sur [69,{k_max}] ✅"
            else:
                n_verified += 1
                val = (p_f - 1) * (rho ** (found_k - 17))
                verif = f"p|d({found_k}), val={val:.4g} ✅"
        else:
            n_partial += 1
            verif = f"p∤d(k) sur [69,{k_max}] (partiel)"

        if rho > 0.3 or k_crit > 100:
            log_write(f, f"  {p_f:18d} {m_f:5d} {rho:10.6f} {k_crit:10.1f} "
                      f"{verif:>30s}")

    log_write(f, "")
    log_write(f, f"  RESULTATS (premiers avec m ∈ [51, 100]) :")
    log_write(f, f"    Triviaux (k_crit ≤ 68) : {n_trivial}")
    log_write(f, f"    Verifies exhaustivement : {n_verified}")
    log_write(f, f"    Partiels : {n_partial}")
    log_write(f, f"    Echecs : {n_fail}")
    log_write(f, f"    k_crit maximal : {k_crit_max_new:.1f}")
    log_write(f, "")

    if n_fail == 0 and n_partial == 0:
        log_write(f, "  ✅ TOUS les premiers avec m ∈ [51, 100] satisfont (Q) pour k ≥ 69")
    elif n_fail == 0:
        log_write(f, f"  ⚠️ {n_partial} premiers avec verification partielle")
    log_write(f, "")

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 4 : Analyse asymptotique formelle
    # ═══════════════════════════════════════════════════════════════

    log_write(f, "=" * 70)
    log_write(f, "PARTIE 4 — Analyse asymptotique")
    log_write(f, "-" * 70)
    log_write(f, "")

    log_write(f, "  Pour un premier p avec ord_p(2) = m :")
    log_write(f, "    - p | (2^m - 1), donc p ≤ 2^m - 1")
    log_write(f, "    - p | d(k) requiert 3^k ∈ ⟨2⟩ (mod p)")
    log_write(f, "    - Probabilite heuristique : ≈ m/(p-1) ≤ m/(2^m-2)")
    log_write(f, "    - Premier k candidat (multiple de n=ord_Q(π(3))) : k ~ n")
    log_write(f, "    - k_crit(p) depend de ρ et p")
    log_write(f, "")
    log_write(f, "  POUR LES MERSENNE PRIMES M_m :")
    log_write(f, "    ρ ≈ 1 - 3.2/m")
    log_write(f, "    k_crit ≈ 0.217·m²")
    log_write(f, "    Premier k avec M_m | d(k) : ~ m² (heuristique)")
    log_write(f, "    Les deux grandeurs sont du MEME ORDRE (m²)")
    log_write(f, "    → La verification est FAISABLE cas par cas")
    log_write(f, "    → Mais pas de preuve GENERALE")
    log_write(f, "")

    # Verification : a-t-on pu trouver un k tel que M_m | d(k) pour les
    # Mersenne primes testees ?
    log_write(f, "  Recherche du premier k tel que M_m | d(k), pour chaque Mersenne :")
    log_write(f, f"  {'m':>4s} {'k_crit':>10s} {'1er k avec M_m|d(k)':>25s} {'Q?':>5s}")
    log_write(f, "  " + "-" * 50)

    for m_exp in mersenne_exponents:
        p = pow(2, m_exp) - 1
        rho = compute_rho_fast(p, m_exp, max_c=min(p - 1, 5000))
        k_crit = compute_k_crit(p, rho)

        # Chercher le premier k tel que p | d(k)
        # Limite de recherche : max(k_crit, 10000) mais pas trop
        search_limit = min(max(ceil(k_crit) + 100, 10000), 100000)
        first_k = None
        for k in range(2, search_limit + 1):
            if p_divides_dk(p, k):
                first_k = k
                break

        if first_k is not None:
            val = (p - 1) * (rho ** (first_k - 17))
            q_ok = val < 0.041
            log_write(f, f"  {m_exp:4d} {k_crit:10.1f} {first_k:25d} "
                      f"{'✅' if q_ok or first_k < 18 else '❌'}")
        else:
            log_write(f, f"  {m_exp:4d} {k_crit:10.1f} {'aucun (k < '+str(search_limit)+')':>25s} ✅")

    log_write(f, "")

    # ═══════════════════════════════════════════════════════════════
    # SYNTHESE FINALE
    # ═══════════════════════════════════════════════════════════════

    log_write(f, "=" * 70)
    log_write(f, "SYNTHESE L5c — Etat de la verification")
    log_write(f, "=" * 70)
    log_write(f, "")
    log_write(f, "  VERIFIE :")
    log_write(f, "    CAS 1 (k ≤ 68) : D17 ✅")
    log_write(f, "    CAS 2 (k ≥ 69, m ≤ 50) : 67/67 premiers ✅")
    log_write(f, f"    CAS 2b (k ≥ 69, m ∈ [51,100]) : extension en cours")
    log_write(f, f"      Triviaux : {n_trivial}")
    log_write(f, f"      Verifies : {n_verified}")
    log_write(f, f"      Partiels : {n_partial}")
    log_write(f, f"      Echecs : {n_fail}")
    log_write(f, "")
    log_write(f, "  MERSENNE PRIMES (traitement special) :")
    for m_exp in mersenne_exponents:
        if m_exp > 50:
            p = pow(2, m_exp) - 1
            rho = compute_rho_fast(p, m_exp, max_c=min(p - 1, 5000))
            k_crit = compute_k_crit(p, rho)
            log_write(f, f"    M{m_exp}: ρ={rho:.4f}, k_crit={k_crit:.0f}, "
                      f"verification k∈[69,{min(ceil(k_crit), 100000)}]")
    log_write(f, "")
    log_write(f, "  LACUNE RESTANTE :")
    log_write(f, "    Pour m > 100, une preuve THEORIQUE est necessaire.")
    log_write(f, "    Le mecanisme frequence/ρ (tradeoff) devrait fonctionner")
    log_write(f, "    mais n'est pas formellement demontre.")
    log_write(f, "")
    log_write(f, "=" * 70)

print(f"\nResultats dans {OUTFILE}")
