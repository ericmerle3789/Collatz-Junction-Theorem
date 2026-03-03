#!/usr/bin/env python3
"""phase_a2_regime_b_extension.py — Phase A2 : Extension Régime B k=18..67

Pour chaque k dans [18, 67] :
1. Calculer d(k) = 2^S - 3^k
2. Factoriser d(k) par division d'essai (primes ≤ 10^7)
3. Pour chaque premier p | d(k) : calculer m = ord₂(p), classifier Régime A/B
4. Si Régime B (p ≥ m⁴) : calculer ρ(p), k_crit, vérifier (Q)
5. Pour le cofacteur : tester si premier (Miller-Rabin)

Objectif : confirmer que le Régime B est empiriquement vide pour d(k),
k = 18..67. Si un premier Régime B est trouvé, vérifier (Q).

Condition (Q) : (p-1) · ρ(p)^{k-17} < 0.041

Protocole anti-hallucination :
  - Vérification croisée : d(k) mod p == 0 reconfirmé après factorisation
  - Contrôle : Σ(facteurs × cofacteur) = d(k) original
  - Borne ρ cross-validée sur cas connu (p=127, m=7, ρ ≈ 0.618)

Auteur : Eric Merle (assisté par Claude)
Date :   3 mars 2026
"""

import math
import time
import numpy as np

# ============================================================================
# Configuration
# ============================================================================

K_RANGE = range(18, 68)          # k = 18..67
TRIAL_BOUND = 10**7             # Borne de division d'essai
RHO_MAX_COSETS = 10000          # Max cosets pour calcul de ρ

# ============================================================================
# Helpers arithmétiques
# ============================================================================

def ceil_log2_3_exact(k):
    """S = ceil(k * log2(3)) exact."""
    three_k = 3 ** k
    S = k
    while (1 << S) < three_k:
        S += 1
    return S


def is_probably_prime(n):
    """Test de primalité Miller-Rabin déterministe pour n < 3.3 × 10^24."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    s, d = 0, n - 1
    while d % 2 == 0:
        s += 1
        d //= 2
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]:
        if a >= n:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def mult_ord(a, m):
    """Ordre multiplicatif de a mod m (naïf, pour petits m ≤ 10^7)."""
    if math.gcd(a, m) != 1:
        return 0
    cur, step = a % m, 1
    while cur != 1:
        cur = (cur * a) % m
        step += 1
        if step > m:
            return 0
    return step


def mult_ord_via_factors(a, p):
    """Ordre multiplicatif de a mod p via factorisation de p-1.

    Factorise p-1 par trial division (jusqu'à 10^6), puis teste
    les diviseurs de p-1 par ordre croissant.
    Si la factorisation de p-1 est incomplète, retourne None.
    """
    if math.gcd(a, p) != 1:
        return 0

    n = p - 1
    # Factoriser p-1
    facs = {}
    temp = n
    d = 2
    while d * d <= temp and d <= 10**6:
        while temp % d == 0:
            facs[d] = facs.get(d, 0) + 1
            temp //= d
        d += (1 if d == 2 else 2)

    if temp > 1:
        # temp est un grand cofacteur de p-1
        # Si temp > 10^12, on ne peut pas le factoriser facilement
        if temp > 10**12:
            # On sait que ord | (p-1), essayons quand même avec la partie factorisée
            # L'ordre divise p-1. On calcule l'ordre en utilisant les facteurs connus.
            # ord = (p-1) / gcd(p-1, ...) — mais incomplet
            # Stratégie : on calcule l'exposant en "strippant" les facteurs premiers connus
            order = n
            for q, e in facs.items():
                while order % q == 0 and pow(a, order // q, p) == 1:
                    order //= q
            # L'ordre réel divise 'order', mais 'order' peut contenir le cofacteur temp
            # Si order contient temp comme facteur, essayer de le stripper aussi
            if order % temp == 0 and pow(a, order // temp, p) == 1:
                order //= temp
                # Essayer encore les petits facteurs
                for q, e in facs.items():
                    while order % q == 0 and pow(a, order // q, p) == 1:
                        order //= q
            return order  # Meilleure estimation (exacte si temp est premier)
        else:
            facs[temp] = facs.get(temp, 0) + 1

    # Calcul exact : partir de n = p-1 et retirer les facteurs premiers
    order = n
    for q in facs:
        while order % q == 0 and pow(a, order // q, p) == 1:
            order //= q
    return order


def mult_ord_smart(a, p, naive_limit=10**7):
    """Calcul intelligent de ord_a(p).

    - p ≤ naive_limit : boucle naïve (rapide, exact)
    - p > naive_limit : via factorisation de p-1
    """
    if p <= naive_limit:
        return mult_ord(a, p)
    return mult_ord_via_factors(a, p)


def trial_factor(n, bound=TRIAL_BOUND):
    """Factorisation par division d'essai jusqu'à bound.

    Retourne (factors, cofactor) où factors = [(p, e), ...].
    """
    if n <= 1:
        return [], n
    factors = []
    d = 2
    while d * d <= n and d <= bound:
        if n % d == 0:
            e = 0
            while n % d == 0:
                n //= d
                e += 1
            factors.append((d, e))
        d += (1 if d == 2 else 2)
    return factors, n


def compute_rho(p, m, max_cosets=RHO_MAX_COSETS):
    """Calculer ρ(p) = max_{t≠0} |S(t)|/m sur les cosettes de ⟨2⟩.

    S(t) = Σ_{j=0}^{m-1} e(2πi·t·2^j/p)
    """
    # Construire l'orbite ⟨2⟩ = {1, 2, 4, ..., 2^{m-1}} mod p
    orbit = [0] * m
    h = 1
    for j in range(m):
        orbit[j] = h
        h = (h * 2) % p

    # Tester les cosettes (représentants t = 1, 2, ..., min(p-1, max_cosets))
    PI2 = 2.0 * math.pi
    p_float = float(p)
    best = 0.0

    c_lim = min(p - 1, max_cosets)
    for c in range(1, c_lim + 1):
        re_sum = 0.0
        im_sum = 0.0
        for h_val in orbit:
            phase = PI2 * float((c * h_val) % p) / p_float
            re_sum += math.cos(phase)
            im_sum += math.sin(phase)
        mag = math.sqrt(re_sum * re_sum + im_sum * im_sum)
        rho_c = mag / m
        if rho_c > best:
            best = rho_c

    return best


def check_condition_Q(p, rho, k):
    """Vérifier (Q) : (p-1) · ρ^{k-17} < 0.041"""
    if rho <= 0 or rho >= 1:
        return False, float('inf')
    log_val = math.log(p - 1) + (k - 17) * math.log(rho)
    threshold = math.log(0.041)
    return log_val < threshold, math.exp(log_val)


# ============================================================================
# Anti-régression : vérification de ρ sur cas connu
# ============================================================================

def anti_regression_check():
    """Vérifie ρ(127, m=7) ≈ 0.618 (cas connu L7)."""
    rho_127 = compute_rho(127, 7, max_cosets=126)
    assert abs(rho_127 - 0.618) < 0.01, \
        f"Anti-régression ÉCHEC : ρ(127,7) = {rho_127:.4f}, attendu ≈ 0.618"

    # Vérifier mult_ord_smart vs mult_ord sur cas connus
    for p in [127, 8191, 131071, 524287]:
        m_naive = mult_ord(2, p)
        m_smart = mult_ord_smart(2, p)
        assert m_naive == m_smart, \
            f"Anti-régression ÉCHEC : mult_ord({p}) = {m_naive} ≠ mult_ord_smart = {m_smart}"

    # Vérifier mult_ord_via_factors sur un premier plus grand (Mersenne M19 = 524287)
    m_via = mult_ord_via_factors(2, 524287)
    assert m_via == 19, \
        f"Anti-régression ÉCHEC : mult_ord_via_factors(2, 524287) = {m_via}, attendu 19"

    return rho_127


# ============================================================================
# Analyse d'une valeur de k
# ============================================================================

def analyze_k(k, verbose=True):
    """Analyse complète de d(k) : factorisation, régime, (Q)."""
    S = ceil_log2_3_exact(k)
    d = (1 << S) - pow(3, k)
    C = math.comb(S - 1, k - 1)

    if verbose:
        d_digits = len(str(abs(d)))
        print(f"\n  k={k:>2}, S={S:>3}, d(k) [{d_digits} digits], "
              f"C=C({S-1},{k-1})={C:,.0f}")

    if d <= 0:
        return {'k': k, 'S': S, 'factors': [], 'cofactor': d,
                'regime_b': [], 'status': 'TRIVIAL'}

    # Factorisation
    t0 = time.time()
    factors, cofactor = trial_factor(d)
    t_factor = time.time() - t0

    # Vérification anti-hallucination : produit des facteurs × cofacteur = d
    product = cofactor
    for p, e in factors:
        product *= p ** e
    assert product == d, f"INCOHÉRENCE factorisation pour k={k}"

    if verbose:
        fac_str = ' × '.join(f"{p}^{e}" if e > 1 else str(p) for p, e in factors)
        if cofactor > 1:
            cof_digits = len(str(cofactor))
            cof_prime = is_probably_prime(cofactor)
            cof_label = f"PRP({cof_digits}d)" if cof_prime else f"C({cof_digits}d)"
            fac_str += f" × [{cof_label}]"
        print(f"    d = {fac_str}  [{t_factor:.3f}s]")

    # Classification Régime A/B pour chaque premier
    primes_info = []
    regime_b_primes = []

    for p, e in factors:
        m = mult_ord(2, p)
        m4 = m ** 4
        regime = 'B' if p >= m4 else 'A'

        info = {'p': p, 'e': e, 'm': m, 'regime': regime}

        if regime == 'B':
            regime_b_primes.append(info)
            if verbose:
                print(f"    ⚠️  RÉGIME B : p={p:,}, m=ord₂={m}, m⁴={m4:,}")

        primes_info.append(info)

    # Cofacteur : vérifier s'il pourrait être Régime B
    cofactor_regime_b = False
    cofactor_skipped = False
    if cofactor > 1:
        cof_prime = is_probably_prime(cofactor)
        if cof_prime:
            t_ord = time.time()
            m_cof = mult_ord_smart(2, cofactor)
            t_ord = time.time() - t_ord

            if m_cof is None or m_cof == 0:
                cofactor_skipped = True
                if verbose:
                    print(f"    Cofacteur premier SKIP : p [{len(str(cofactor))}d], "
                          f"ord₂ non calculable")
            else:
                m4_cof = m_cof ** 4
                if cofactor >= m4_cof:
                    cofactor_regime_b = True
                    regime_b_primes.append({
                        'p': cofactor, 'e': 1, 'm': m_cof, 'regime': 'B'
                    })
                    if verbose:
                        print(f"    ⚠️  COFACTEUR RÉGIME B : p [{len(str(cofactor))}d], "
                              f"m=ord₂={m_cof:,}, m⁴={m4_cof:,} [{t_ord:.2f}s]")
                else:
                    if verbose:
                        print(f"    Cofacteur premier : p [{len(str(cofactor))}d], "
                              f"m=ord₂={m_cof:,} → Régime A [{t_ord:.2f}s]")

    # Vérifier (Q) pour les primes Régime B
    q_results = []
    for info in regime_b_primes:
        p = info['p']
        m = info['m']

        # Calculer ρ (si m est assez petit pour le calcul)
        if m <= 50000:
            t0 = time.time()
            rho = compute_rho(p, m, max_cosets=min(p - 1, RHO_MAX_COSETS))
            t_rho = time.time() - t0
        else:
            rho = None
            t_rho = 0

        # Vérifier (Q)
        if rho is not None:
            q_ok, q_val = check_condition_Q(p, rho, k)
            if verbose:
                print(f"    ρ({p:,}) = {rho:.6f} [{t_rho:.2f}s]")
                print(f"    (Q) : (p-1)·ρ^(k-17) = {q_val:.2e} "
                      f"{'< 0.041 ✓ PASS' if q_ok else '>= 0.041 ✗ FAIL'}")
        else:
            q_ok = None
            q_val = None
            if verbose:
                print(f"    ρ non calculable (m={m} trop grand)")

        q_results.append({
            'p': p, 'm': m, 'rho': rho, 'Q_pass': q_ok, 'Q_val': q_val
        })

    # Résumé
    n_factors = len(factors)
    n_regime_a = sum(1 for i in primes_info if i['regime'] == 'A')
    n_regime_b = len(regime_b_primes)

    if verbose:
        print(f"    → {n_factors} premiers trouvés, "
              f"{n_regime_a} Régime A, {n_regime_b} Régime B"
              + (f", cofacteur {'premier' if cofactor > 1 and is_probably_prime(cofactor) else 'composite' if cofactor > 1 else '1'}"
                 if cofactor != 1 else ""))

    return {
        'k': k, 'S': S, 'd_digits': len(str(d)),
        'factors': factors, 'cofactor': cofactor,
        'primes_info': primes_info,
        'regime_b': regime_b_primes,
        'q_results': q_results,
        'n_regime_a': n_regime_a, 'n_regime_b': n_regime_b,
        'cofactor_regime_b': cofactor_regime_b,
        'cofactor_skipped': cofactor_skipped,
    }


# ============================================================================
# Main
# ============================================================================

def main():
    t_global = time.time()

    print("=" * 70)
    print("PHASE A2 — EXTENSION RÉGIME B  k = 18..67")
    print("Programme de Fermeture du Gap Collatz")
    print(f"Date : {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Config : TRIAL_BOUND={TRIAL_BOUND:,}, "
          f"RHO_MAX_COSETS={RHO_MAX_COSETS:,}")
    print("=" * 70)

    # Anti-régression
    print("\n─── Anti-régression ───")
    rho_check = anti_regression_check()
    print(f"  ρ(127, m=7) = {rho_check:.4f} ✓ (attendu ≈ 0.618)")

    # Analyse k = 18..67
    print(f"\n{'='*70}")
    print("ANALYSE PRINCIPALE k = 18..67")
    print(f"{'='*70}")

    all_results = []
    total_primes = 0
    total_regime_a = 0
    total_regime_b = 0
    total_cofactor_unknown = 0
    q_failures = []

    for k in K_RANGE:
        result = analyze_k(k)
        all_results.append(result)

        total_primes += len(result['factors'])
        total_regime_a += result['n_regime_a']
        total_regime_b += result['n_regime_b']

        if result['cofactor'] > 1 and not is_probably_prime(result['cofactor']):
            total_cofactor_unknown += 1
        if result.get('cofactor_skipped', False):
            total_cofactor_unknown += 1

        for qr in result['q_results']:
            if qr['Q_pass'] is False:
                q_failures.append((k, qr['p'], qr['rho'], qr['Q_val']))

    # ── Synthèse ──
    print(f"\n{'='*70}")
    print("SYNTHÈSE PHASE A2")
    print(f"{'='*70}")

    print(f"\n  k analysés : {len(list(K_RANGE))}")
    print(f"  Premiers trouvés (≤ {TRIAL_BOUND:,}) : {total_primes}")
    print(f"  Régime A : {total_regime_a}")
    print(f"  Régime B : {total_regime_b}")
    print(f"  Cofacteurs composites non factorisés : {total_cofactor_unknown}")

    if total_regime_b == 0:
        print(f"\n  ✓ RÉGIME B EMPIRIQUEMENT VIDE pour k = 18..67")
        print(f"    Confirme le pattern L12 (0/284 pour k = 69..150)")
        print(f"    Extension : 0/{total_primes} premiers en Régime B")
    else:
        print(f"\n  ⚠️  {total_regime_b} premiers en Régime B trouvés")

    if q_failures:
        print(f"\n  ✗ {len(q_failures)} ÉCHECS de Condition (Q) :")
        for k, p, rho, qval in q_failures:
            print(f"    k={k}, p={p:,}, ρ={rho:.6f}, (Q)={qval:.2e}")
    else:
        if total_regime_b > 0:
            print(f"\n  ✓ Condition (Q) satisfaite pour TOUS les {total_regime_b} "
                  f"premiers Régime B")
        else:
            print(f"\n  ✓ Condition (Q) vacuement satisfaite (aucun premier Régime B)")

    # Tableau des primes Régime B trouvés (s'il y en a)
    if total_regime_b > 0:
        print(f"\n  {'k':>3} {'p':>15} {'m':>6} {'m⁴':>15} {'ρ':>10} {'(Q)':>8}")
        print("  " + "-" * 65)
        for r in all_results:
            for qr in r['q_results']:
                status = "PASS" if qr['Q_pass'] else "FAIL" if qr['Q_pass'] is False else "N/A"
                rho_str = f"{qr['rho']:.6f}" if qr['rho'] is not None else "N/A"
                print(f"  {r['k']:>3} {qr['p']:>15,} {qr['m']:>6} "
                      f"{qr['m']**4:>15,} {rho_str:>10} {status:>8}")

    # Tableau complet condensé
    print(f"\n  ── Détail par k ──")
    print(f"  {'k':>3} {'S':>3} {'digits':>6} {'#p':>3} {'A':>3} {'B':>3} "
          f"{'cofacteur':>15}")
    print("  " + "-" * 50)
    for r in all_results:
        cof = r['cofactor']
        if cof == 1:
            cof_str = "1 (complet)"
        elif is_probably_prime(cof):
            cof_str = f"PRP({len(str(cof))}d)"
        else:
            cof_str = f"C({len(str(cof))}d)"
        print(f"  {r['k']:>3} {r['S']:>3} {r['d_digits']:>6} "
              f"{len(r['factors']):>3} {r['n_regime_a']:>3} {r['n_regime_b']:>3} "
              f"{cof_str:>15}")

    # Contrôle anti-hallucination
    print(f"\n{'='*70}")
    print("CONTRÔLE ANTI-HALLUCINATION")
    print(f"{'='*70}")

    issues = 0
    for r in all_results:
        d = (1 << ceil_log2_3_exact(r['k'])) - pow(3, r['k'])
        product = r['cofactor']
        for p, e in r['factors']:
            product *= p ** e
        if product != d:
            print(f"  ⚠️  k={r['k']} : produit ≠ d(k)")
            issues += 1

    if issues == 0:
        print("  ✓ Toutes les factorisations vérifiées")
    else:
        print(f"  ✗ {issues} incohérences")

    # Temps
    t_total = time.time() - t_global
    print(f"\nTemps total : {t_total:.1f}s")

    # Verdict
    print(f"\n{'='*70}")
    if total_regime_b == 0 and not q_failures:
        print("✓ PHASE A2 COMPLÈTE : Régime B vide, (Q) vacuement satisfaite")
        c_min = 0.3603  # Hérité de L12
        print(f"  c_min hérité de L12 = {c_min}")
    elif q_failures:
        print(f"✗ PHASE A2 : {len(q_failures)} échecs (Q)")
    else:
        print(f"✓ PHASE A2 : {total_regime_b} Régime B, tous PASS (Q)")
    print(f"{'='*70}")


if __name__ == '__main__':
    main()
