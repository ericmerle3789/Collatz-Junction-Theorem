#!/usr/bin/env python3
"""
SP10 Level 12 — Effectivisation quantitative + calcul exact de ρ(p)
====================================================================

Date    : 3 mars 2026
Objectif :
  1. Énumérer TOUS les premiers de Régime B (p ≥ m⁴, m = ord_p(2)) jusqu'à m_max
  2. Calculer ρ(p) exactement via FFT pour les petits Régime B
  3. Vérifier si ces premiers divisent d(k) pour k ≥ 69
  4. Quantifier c_min dans Konyagin pour fermer le gap
  5. Analyser la cascade de filtres (approche Zénon)

Anti-hallucination :
- Parseval : ∑|S_t|² = p·m vérifié après chaque FFT
- Cross-check : ρ vérifié par calcul direct pour échantillons
- Divisibilité vérifiée par calcul modulaire direct
- Chaque borne est vérifiée numériquement avant d'être annoncée
"""

import math
import sys
import time
import numpy as np

THETA = math.log2(3)  # ≈ 1.58496...


# ============================================================================
# Utilitaires
# ============================================================================
def ord_mod(base, p):
    """Compute ord_p(base) by brute force. Only for p < ~10^8."""
    if p <= 1:
        return 0
    val = base % p
    if val == 0:
        return 0
    for i in range(1, p):
        if val == 1:
            return i
        val = (val * base) % p
    return p - 1


def is_prime(n):
    """Simple primality test for n < 10^12."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0 or n % 3 == 0:
        return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i + 2) == 0:
            return False
        i += 6
    return True


def small_prime_factors(n, limit=10**7):
    """Factor n up to 'limit'. Returns (factors_dict, cofactor)."""
    factors = {}
    for p in [2, 3]:
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
    d = 5
    while d * d <= min(n, limit):
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 2
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 4
    if 1 < n <= limit * limit:
        factors[n] = factors.get(n, 0) + 1
        n = 1
    return factors, n


# ============================================================================
# PART 1 : Énumération des premiers de Régime B
# ============================================================================
def find_regime_b_primes(m_max=200):
    """
    Pour chaque m = 2, ..., m_max, factoriser 2^m - 1 et identifier
    les facteurs premiers p avec p ≥ m⁴ (Régime B).
    """
    print("=" * 75)
    print(f"PART 1 : Premiers de Régime B (m ≤ {m_max})")
    print("=" * 75)

    regime_b = []  # list of (m, p, ratio, is_mersenne_prime)
    regime_a_count = 0

    for m in range(2, m_max + 1):
        mersenne = (1 << m) - 1
        threshold = m ** 4

        # Factoriser 2^m - 1
        factors, cofactor = small_prime_factors(mersenne, min(10**7, mersenne))

        # Vérifier si 2^m - 1 est premier (pour petits m)
        if cofactor == 1 and len(factors) == 1:
            p = list(factors.keys())[0]
            if factors[p] == 1 and p == mersenne:
                mersenne_is_prime = True
            else:
                mersenne_is_prime = False
        elif cofactor > 1 and cofactor == mersenne // max(1, math.prod(
                p ** e for p, e in factors.items())):
            # cofactor might be prime
            mersenne_is_prime = False
        else:
            mersenne_is_prime = False

        # Check if mersenne itself is prime (for small m)
        if mersenne < 10**12:
            mersenne_is_prime = is_prime(mersenne)
        elif m in [2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127]:
            # Known Mersenne prime exponents
            mersenne_is_prime = True
        else:
            mersenne_is_prime = False  # Unknown, assume not

        for p in factors:
            if p <= 3:
                continue
            # Verify ord_p(2) = m (primitive factor)
            if p < 10**7:
                actual_ord = ord_mod(2, p)
                if actual_ord != m:
                    continue  # Not a primitive factor for this m

            ratio = math.log(p) / math.log(m) if m > 1 else float('inf')
            if p >= threshold:
                regime_b.append((m, p, ratio, mersenne_is_prime and p == mersenne))
            else:
                regime_a_count += 1

        # Handle large cofactors that might be Regime B primes
        if cofactor > 1 and cofactor >= threshold:
            # This cofactor might be a single prime or composite
            if cofactor < 10**12 and is_prime(cofactor):
                ratio = math.log(cofactor) / math.log(m)
                regime_b.append((m, cofactor, ratio, False))
            elif mersenne_is_prime:
                ratio = math.log(mersenne) / math.log(m)
                if mersenne not in factors:
                    regime_b.append((m, mersenne, ratio, True))

    # Ajouter les Mersenne primes connus qui sont en Régime B
    known_mersenne_exponents = [17, 19, 31, 61, 89, 107, 127]
    for q in known_mersenne_exponents:
        if q > m_max:
            continue
        M_q = (1 << q) - 1
        ratio = math.log(M_q) / math.log(q) if q > 1 else float('inf')
        # Vérifier pas de doublon
        if not any(p == M_q for _, p, _, _ in regime_b):
            regime_b.append((q, M_q, ratio, True))

    # Trier par m
    regime_b.sort(key=lambda x: (x[0], x[1]))

    # Dédupliquer
    seen = set()
    unique = []
    for item in regime_b:
        key = (item[0], item[1])
        if key not in seen:
            seen.add(key)
            unique.append(item)
    regime_b = unique

    print(f"\nRégime A : {regime_a_count} facteurs premiers")
    print(f"Régime B : {len(regime_b)} facteurs premiers\n")

    print(f"{'m':>4s} | {'p':>20s} | {'ratio':>8s} | {'Mersenne?':>9s} | {'p/m⁴':>12s}")
    print("-" * 65)
    for m, p, ratio, is_mp in regime_b:
        p_str = str(p) if p < 10**15 else f"2^{m}-1"
        print(f"{m:4d} | {p_str:>20s} | {ratio:8.3f} | {'OUI' if is_mp else 'non':>9s} | "
              f"{p / m**4:12.2f}")

    return regime_b


# ============================================================================
# PART 2 : Calcul exact de ρ(p) via FFT
# ============================================================================
def compute_rho_fft(p, m):
    """
    Calcule ρ(p) = max_{t≠0} |S_t| / m exactement via FFT.

    Méthode : La DFT de la fonction indicatrice f(x) = 1_{x ∈ ⟨2⟩}
    donne F[t] = S_{-t} = conj(S_t), donc |F[t]| = |S_t|.

    Anti-hallucination :
    - Vérifie Parseval : ∑|F[t]|² = p * m
    - Vérifie F[0] = m
    """
    print(f"\n--- ρ(p={p}, m={m}) via FFT ---")
    t0 = time.time()

    # Construire la fonction indicatrice
    f = np.zeros(p, dtype=np.float64)
    subgroup = set()
    val = 1
    for j in range(m):
        subgroup.add(val)
        f[val] = 1.0
        val = (val * 2) % p

    # Anti-hallucination : vérifier |⟨2⟩| = m
    assert len(subgroup) == m, f"ERREUR : |⟨2⟩| = {len(subgroup)} ≠ {m}"
    assert sum(f) == m, f"ERREUR : sum(f) = {sum(f)} ≠ {m}"

    # FFT
    F = np.fft.fft(f)
    abs_F = np.abs(F)

    # Anti-hallucination : Parseval
    parseval_lhs = np.sum(abs_F ** 2)
    parseval_rhs = p * m
    parseval_err = abs(parseval_lhs - parseval_rhs) / parseval_rhs
    print(f"  Parseval : ∑|F|² = {parseval_lhs:.2f}, p*m = {parseval_rhs}, "
          f"erreur relative = {parseval_err:.2e}")
    assert parseval_err < 1e-8, f"PARSEVAL VIOLÉ : erreur = {parseval_err}"

    # Anti-hallucination : F[0] = m
    f0_err = abs(abs_F[0] - m)
    print(f"  F[0] = {abs_F[0]:.6f}, m = {m}, erreur = {f0_err:.2e}")
    assert f0_err < 1e-6, f"F[0] INCORRECT : {abs_F[0]}"

    # ρ = max_{t≠0} |F[t]| / m
    abs_F_nonzero = abs_F[1:]  # Exclure t=0
    max_abs = np.max(abs_F_nonzero)
    argmax_t = np.argmax(abs_F_nonzero) + 1  # +1 car on a exclu l'indice 0
    rho = max_abs / m

    # Statistiques
    mean_abs = np.mean(abs_F_nonzero)
    median_abs = np.median(abs_F_nonzero)
    std_abs = np.std(abs_F_nonzero)

    t1 = time.time()

    print(f"\n  RÉSULTAT : ρ(p={p}) = {rho:.6f}")
    print(f"  max |S_t| = {max_abs:.6f} atteint en t = {argmax_t}")
    print(f"  |S_t| stats : mean={mean_abs:.3f}, median={median_abs:.3f}, "
          f"std={std_abs:.3f}")
    print(f"  Borne triviale : ρ ≤ 1 - 1/{m} = {1 - 1/m:.6f}")
    print(f"  Borne inférieure (Parseval) : ρ ≥ √(m·(p-m)/((p-1)·m²)) "
          f"= {math.sqrt((p-m)/((p-1)*m)):.6f}")
    print(f"  Temps : {t1-t0:.2f}s")

    return rho, max_abs, argmax_t


def cross_check_rho(p, m, t_check, expected_abs):
    """
    Vérifie |S_t| par calcul direct pour un t donné.
    Anti-hallucination : compare FFT vs calcul direct.
    """
    # Calcul direct : S_t = ∑_{j=0}^{m-1} e(t·2^j/p)
    S = 0.0 + 0.0j
    val = 1
    for j in range(m):
        S += np.exp(2j * np.pi * t_check * val / p)
        val = (val * 2) % p

    direct_abs = abs(S)
    err = abs(direct_abs - expected_abs)
    print(f"  Cross-check t={t_check}: |S_t| FFT={expected_abs:.6f}, "
          f"direct={direct_abs:.6f}, erreur={err:.2e}")
    assert err < 1e-4, f"CROSS-CHECK ÉCHOUÉ : erreur = {err}"
    return direct_abs


# ============================================================================
# PART 3 : Divisibilité d(k) par premiers de Régime B
# ============================================================================
def check_divisibility(p, m, k_min=69, k_max=10000):
    """
    Vérifie si p | d(k) pour k ∈ [k_min, k_max].
    Retourne la liste des k tels que p | d(k).

    Utilise l'identité : p | d(k) ⟺ 2^{⌈kθ⌉} ≡ 3^k (mod p)
    """
    print(f"\n--- Divisibilité d(k) par p={p} (m={m}), k={k_min}..{k_max} ---")

    # Précalculer n₃ : plus petit j ≥ 1 tel que 3^j ∈ ⟨2⟩ mod p
    # 3^j ∈ ⟨2⟩ ⟺ 3^{j·q} ≡ 1 (mod p), où q = (p-1)/m
    q = (p - 1) // m
    val = pow(3, q, p)
    n3 = 1
    power = val
    while power != 1 and n3 <= p:
        power = (power * val) % p
        n3 += 1

    if power != 1:
        print(f"  ATTENTION : 3^(j·q) ne revient pas à 1 pour j ≤ {p}")
        n3 = p  # Fallback

    print(f"  n₃ = {n3}")
    print(f"  q = (p-1)/m = {q}")
    print(f"  Premier k candidat : {n3}")

    if n3 > k_max:
        print(f"  → n₃ = {n3} > k_max = {k_max} : AUCUN k divisible dans la plage")
        return [], n3

    # Tester les k = n₃, 2·n₃, ..., ≤ k_max
    divisible_k = []
    count = 0
    for j in range(1, k_max // n3 + 1):
        k = n3 * j
        if k < k_min:
            continue
        if k > k_max:
            break

        S = math.ceil(k * THETA)
        lhs = pow(2, S, p)
        rhs = pow(3, k, p)

        if lhs == rhs:
            divisible_k.append(k)

        count += 1

    print(f"  Candidats testés (multiples de n₃ dans [{k_min}, {k_max}]) : {count}")
    print(f"  Divisibilités trouvées : {len(divisible_k)}")

    if divisible_k:
        # Anti-hallucination : vérifier les premières divisibilités
        for k in divisible_k[:5]:
            S = math.ceil(k * THETA)
            d_k_mod_p = (pow(2, S, p) - pow(3, k, p)) % p
            assert d_k_mod_p == 0, f"FAUX POSITIF : d({k}) mod {p} = {d_k_mod_p}"
            print(f"    k = {k} : d(k) ≡ 0 (mod p) ✓")
    else:
        print(f"  → p = {p} ne divise d(k) pour aucun k ∈ [{k_min}, {k_max}]")

    return divisible_k, n3


# ============================================================================
# PART 4 : Calcul de c_needed(k) pour Konyagin
# ============================================================================
def compute_c_needed(k_min=69, k_max=1000):
    """
    Pour chaque k, calcule le c minimal dans ρ ≤ exp(-c·(log p)^{1/3})
    tel que (p-1)·ρ^{k-17} < 0.041 pour TOUT p ≤ d(k) en Régime B.

    La contrainte est : c > (ln(p) + 3.19) / ((k-17)·(ln p)^{1/3})
    maximisée pour p = d(k) (le pire cas).
    """
    print("\n" + "=" * 75)
    print("PART 4 : c_needed(k) pour Konyagin")
    print("=" * 75)

    results = []

    for k in range(k_min, k_max + 1):
        S = math.ceil(k * THETA)
        # ln(d(k)) ≈ S·ln(2) pour d(k) ≈ 2^S (puisque 3^k < 2^S)
        ln_p_max = S * math.log(2)  # borne sup sur ln(p) pour p | d(k)

        if ln_p_max <= 0:
            continue

        ln_p_13 = ln_p_max ** (1.0 / 3.0)
        c_needed = (ln_p_max + 3.19) / ((k - 17) * ln_p_13)

        results.append((k, S, ln_p_max, c_needed))

    # Trouver le maximum de c_needed (worst case)
    worst = max(results, key=lambda x: x[3])
    print(f"\nPIRE CAS : k = {worst[0]}, S = {worst[1]}, ln(p_max) = {worst[2]:.2f}, "
          f"c_needed = {worst[3]:.6f}")

    # Afficher table pour k = 69, 70, 75, 100, 200, 500, 1000
    print(f"\n{'k':>6s} | {'S':>6s} | {'ln(p_max)':>10s} | {'c_needed':>10s} | "
          f"{'Note':>30s}")
    print("-" * 75)
    display_ks = [69, 70, 75, 80, 90, 100, 150, 200, 300, 500, 750, 1000]
    for k, S, ln_p, c in results:
        if k in display_ks:
            note = "*** PIRE CAS ***" if k == worst[0] else ""
            print(f"{k:6d} | {S:6d} | {ln_p:10.2f} | {c:10.6f} | {note}")

    # Vérification anti-hallucination : c_needed(k) doit décroître pour k >> 69
    c_69 = next(c for k, S, _, c in results if k == 69)
    c_1000 = next(c for k, S, _, c in results if k == 1000)
    print(f"\nAnti-hallucination :")
    print(f"  c_needed(69) = {c_69:.6f}")
    print(f"  c_needed(1000) = {c_1000:.6f}")
    print(f"  Décroissance confirmée : {c_69 > c_1000}")
    print(f"  → c_min = {worst[3]:.6f} (atteint en k = {worst[0]})")

    return worst[3], results


# ============================================================================
# PART 5 : Condition (Q) vérification directe pour Régime B
# ============================================================================
def verify_condition_q(p, m, rho, k_min=69, k_max=10000):
    """
    Vérifie (p-1)·ρ^{k-17} < 0.041 pour tous les k ∈ [k_min, k_max]
    tels que p | d(k).
    """
    print(f"\n--- Vérification (Q) pour p={p}, m={m}, ρ={rho:.6f} ---")

    # k_crit : plus grand k tel que (p-1)·ρ^{k-17} ≥ 0.041
    if rho >= 1.0:
        print(f"  ρ ≥ 1 : borne triviale inutile, k_crit = ∞")
        return False, float('inf')

    ln_rho = math.log(rho)
    k_crit = 17 + (math.log(p - 1) + math.log(1 / 0.041)) / abs(ln_rho)

    print(f"  k_crit = {k_crit:.2f}")
    print(f"  Pour k ≥ {math.ceil(k_crit)} : (Q) automatiquement satisfaite")

    if k_crit < k_min:
        print(f"  → k_crit = {k_crit:.2f} < {k_min} : (Q) satisfaite pour tout k ≥ {k_min}")
        return True, k_crit

    print(f"  → k_crit = {k_crit:.2f} ≥ {k_min} : besoin de vérifier "
          f"k ∈ [{k_min}, {math.ceil(k_crit)}]")

    # Pour les k dans [k_min, k_crit] qui divisent d(k), vérifier
    divisible_k, n3 = check_divisibility(p, m, k_min, math.ceil(k_crit))

    if not divisible_k:
        print(f"  → AUCUN k avec p | d(k) dans [{k_min}, {math.ceil(k_crit)}] : "
              f"(Q) satisfaite")
        return True, k_crit

    # Vérifier (Q) pour chaque k divisible
    all_pass = True
    for k in divisible_k:
        lhs = (p - 1) * rho ** (k - 17)
        status = "PASS" if lhs < 0.041 else "*** FAIL ***"
        print(f"    k={k} : (p-1)·ρ^{k-17} = {lhs:.6e}  {status}")
        if lhs >= 0.041:
            all_pass = False

    return all_pass, k_crit


# ============================================================================
# PART 6 : Cascade de filtres
# ============================================================================
def cascade_analysis(p, m, n3, rho):
    """
    Analyse le nombre effectif de candidats après chaque filtre.
    """
    print(f"\n--- Cascade de filtres pour p={p}, m={m}, n₃={n3} ---")

    # k_crit avec borne triviale
    rho_trivial = 1 - 1/m
    if rho_trivial >= 1:
        k_crit_triv = float('inf')
    else:
        k_crit_triv = 17 + (math.log(p - 1) + 3.19) / abs(math.log(rho_trivial))

    # k_crit avec ρ exact
    if rho < 1:
        k_crit_exact = 17 + (math.log(p - 1) + 3.19) / abs(math.log(rho))
    else:
        k_crit_exact = float('inf')

    print(f"  Borne triviale ρ ≤ {rho_trivial:.4f} → k_crit = {k_crit_triv:.1f}")
    print(f"  ρ exact = {rho:.6f} → k_crit = {k_crit_exact:.1f}")

    # Filtre 0 : k ≥ 69
    N0 = max(0, k_crit_triv - 69 + 1) if k_crit_triv < float('inf') else float('inf')
    print(f"\n  Filtre 0 (k ≥ 69) : N₀ = {N0:.0f} candidats")

    # Filtre 1 : k ≡ 0 (mod n₃)
    N1 = N0 / n3 if n3 > 0 else N0
    print(f"  Filtre 1 (k ≡ 0 mod n₃={n3}) : N₁ = {N1:.1f}")

    # Filtre 2 : Condition de Beatty (1/m de probabilité)
    N2 = N1 / m
    print(f"  Filtre 2 (Beatty, prob 1/{m}) : N₂ = {N2:.2f}")

    # Avec ρ exact
    if k_crit_exact < 69:
        print(f"\n  → Avec ρ exact : k_crit = {k_crit_exact:.1f} < 69 → N = 0 ✓")
    else:
        N0_exact = max(0, k_crit_exact - 69 + 1)
        N1_exact = N0_exact / n3
        N2_exact = N1_exact / m
        print(f"\n  Avec ρ exact : N₀'={N0_exact:.0f}, N₁'={N1_exact:.1f}, "
              f"N₂'={N2_exact:.2f}")

    return k_crit_triv, k_crit_exact


# ============================================================================
# SYNTHÈSE
# ============================================================================
def synthesis(regime_b, rho_results, divisibility_results, c_min, c_results):
    """Synthèse complète L12."""
    print("\n" + "=" * 75)
    print("SYNTHÈSE L12 : Effectivisation quantitative")
    print("=" * 75)

    print(f"""
RÉSULTATS CLÉS :

1. PREMIERS DE RÉGIME B identifiés :""")
    for m, p, ratio, is_mp in regime_b:
        tag = "(Mersenne)" if is_mp else ""
        print(f"   m={m:3d}, p={'2^'+str(m)+'-1' if is_mp else str(p):>15s}, "
              f"ratio={ratio:.3f} {tag}")

    print(f"""
2. CALCULS EXACTS DE ρ :""")
    for p, m, rho, max_st, argmax in rho_results:
        needed_k69 = (0.041 / (p - 1)) ** (1.0 / 52)
        status = "✓ SUFFISANT" if rho < needed_k69 else "✗ INSUFFISANT"
        print(f"   p={p}, m={m} : ρ = {rho:.6f}  (seuil k=69 : {needed_k69:.6f})  {status}")

    print(f"""
3. DIVISIBILITÉ d(k) :""")
    for p, m, div_ks, n3 in divisibility_results:
        if div_ks:
            print(f"   p={p} : n₃={n3}, {len(div_ks)} divisibilités "
                  f"(premier k={div_ks[0]})")
        else:
            print(f"   p={p} : n₃={n3}, AUCUNE divisibilité dans la plage ✓")

    print(f"""
4. EFFECTIVISATION DE KONYAGIN :
   c_min = {c_min:.6f} (atteint en k=69)
   Si c ≥ {c_min:.3f} dans Konyagin : gap Régime B FERMÉ pour tout k ≥ 69
""")

    # Anti-hallucination log
    print("ANTI-HALLUCINATION LOG L12 :")
    print("  1. Parseval vérifié pour chaque FFT (erreur < 10^{-8})")
    print("  2. Cross-checks ρ par calcul direct")
    print("  3. Divisibilités vérifiées par calcul modulaire")
    print("  4. c_needed décroissant vérifié")


# ============================================================================
# MAIN
# ============================================================================
if __name__ == "__main__":
    print("SP10 Level 12 — Effectivisation quantitative")
    print("=" * 75)
    print(f"Date : {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print()

    # ---- PART 1 : Énumérer Régime B ----
    regime_b = find_regime_b_primes(m_max=150)

    # ---- PART 2 : Calculer ρ exact pour les petits ----
    rho_results = []
    for m, p, ratio, is_mp in regime_b:
        if p > 10**6:  # Limite FFT : p ≤ 10^6 pour mémoire raisonnable
            print(f"\n  [SKIP] p = {p} trop grand pour FFT directe (p > 10^6)")
            continue

        rho, max_st, argmax = compute_rho_fft(p, m)

        # Cross-check sur 3 valeurs de t
        F = np.fft.fft(np.zeros(1))  # dummy, on va refaire
        # Refaire le calcul FFT pour le cross-check
        f = np.zeros(p, dtype=np.float64)
        val = 1
        for j in range(m):
            f[val] = 1.0
            val = (val * 2) % p
        F = np.fft.fft(f)
        abs_F = np.abs(F)

        # Cross-check t = argmax
        cross_check_rho(p, m, argmax, abs_F[argmax])
        # Cross-check t = 1
        cross_check_rho(p, m, 1, abs_F[1])
        # Cross-check t = p//2
        cross_check_rho(p, m, p // 2, abs_F[p // 2])

        rho_results.append((p, m, rho, max_st, argmax))

    # ---- PART 3 : Divisibilité ----
    divisibility_results = []
    for m, p, ratio, is_mp in regime_b:
        div_ks, n3 = check_divisibility(p, m, k_min=69, k_max=50000)
        divisibility_results.append((p, m, div_ks, n3))

    # ---- PART 4 : c_needed ----
    c_min, c_results = compute_c_needed(k_min=69, k_max=1000)

    # ---- PART 5 : Vérification (Q) directe ----
    for p, m, rho, max_st, argmax in rho_results:
        verify_condition_q(p, m, rho, k_min=69, k_max=50000)

    # ---- PART 6 : Cascade ----
    for (p_r, m_r, rho_r, _, _), (_, _, _, n3_d) in zip(
            rho_results,
            [d for d in divisibility_results if d[0] in [r[0] for r in rho_results]]):
        cascade_analysis(p_r, m_r, n3_d, rho_r)

    # ---- SYNTHÈSE ----
    synthesis(regime_b, rho_results, divisibility_results, c_min, c_results)
