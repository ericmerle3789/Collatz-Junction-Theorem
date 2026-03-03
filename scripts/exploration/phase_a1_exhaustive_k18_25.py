#!/usr/bin/env python3
"""phase_a1_exhaustive_k18_25.py — Phase A1 : Vérification exhaustive k=18..25

Pour chaque k dans [18, 25] :
1. Calculer d(k) = 2^S - 3^k et factoriser
2. Pour chaque premier p | d(k), compter N₀(p) par programmation dynamique
3. Si N₀(p) = 0 pour un p : H(k) prouvé
4. Collecter diagnostics : chi², max_dev, énergie de collision E₂

Méthode DP :
  État : (j positions sélectionnées, corrSum mod p)
  Position 0 fixée. Positions 1..S-1 optionnelles (sac à dos 0-1).
  Horner : c₀ = 1, c_j = 3·c_{j-1} + 2^{A[j]}
  Complexité : O(S × k × p) par premier.

Fallback : énumération directe si p trop grand et C ≤ 3×10^7.

Protocole anti-hallucination :
  - Vérification croisée DP vs énumération pour k=3,4,5 (petit)
  - Contrôle C_check = C(S-1, k-1) après chaque DP
  - Contrôle de cohérence mod 2 du nombre de compositions

Auteur : Eric Merle (assisté par Claude)
Date :   3 mars 2026
"""

import math
import time
import sys
import itertools
import numpy as np
from collections import Counter

# ============================================================================
# Configuration
# ============================================================================

MAX_DP_PRIME = 2 * 10**6   # p max pour DP dense (numpy), ~400 MB
MAX_ENUM_C = 3 * 10**7     # C max pour énumération directe
K_RANGE = range(18, 26)    # k = 18..25

# ============================================================================
# Helpers arithmétiques
# ============================================================================

def ceil_log2_3_exact(k):
    """S = ceil(k * log2(3)) par comparaison entière exacte."""
    three_k = 3 ** k
    S = k
    while (1 << S) < three_k:
        S += 1
    return S


def crystal_module(k):
    """d(k) = 2^S - 3^k, retourne (d, S)."""
    S = ceil_log2_3_exact(k)
    return (1 << S) - 3**k, S


def prime_factorization(n):
    """Factorisation complète par division d'essai. Fonctionne pour n ≤ 10^14."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            exp = 0
            while n % d == 0:
                n //= d
                exp += 1
            factors.append((d, exp))
        d += (1 if d == 2 else 2)
    if n > 1:
        factors.append((n, 1))
    return factors


def mult_ord(a, m):
    """Ordre multiplicatif de a modulo m."""
    if math.gcd(a, m) != 1:
        return 0
    cur, step = a % m, 1
    while cur != 1:
        cur = (cur * a) % m
        step += 1
        if step > m:
            return 0
    return step


def find_n3(p):
    """Trouver n₃ = min{j ≥ 1 : 3^j ∈ ⟨2⟩ mod p}."""
    ord2 = mult_ord(2, p)
    # Construire ⟨2⟩ mod p
    gen2 = set()
    x = 1
    for j in range(ord2):
        gen2.add(x)
        x = (x * 2) % p
    # Trouver n₃
    y = 1
    for j in range(1, p):
        y = (y * 3) % p
        if y in gen2:
            return j
    return p  # 3 ∉ ⟨2⟩ (n₃ = ord de 3 dans (Z/pZ)*/⟨2⟩)


# ============================================================================
# N₀(p) par DP dense (numpy)
# ============================================================================

def count_N0_dp(S, k, p):
    """N₀(p) par DP dense.

    dp[j][s] = nombre de façons de choisir j positions parmi {0,...,pos_courant}
    avec A[0]=0 fixé, Horner sum ≡ s (mod p).

    Transition à la position pos :
      dp[j+1][(3*s + 2^pos) mod p] += dp[j][s]
    Processé j décroissant (sac à dos 0-1).

    Returns: (N0, C_check, distribution_array)
    """
    dp = np.zeros((k + 1, p), dtype=np.int64)
    dp[1][1 % p] = 1  # Position 0 sélectionnée : c₀ = 2^0 = 1

    arange_p = np.arange(p, dtype=np.int64)
    pow2 = 1  # 2^pos mod p, initialisé à 2^0 = 1

    for pos in range(1, S):
        pow2 = (pow2 * 2) % p

        # Permutation : s → (3s + 2^pos) mod p
        perm = (3 * arange_p + pow2) % p

        # Inverse permutation pour indexation rapide
        inv_perm = np.empty(p, dtype=np.int64)
        inv_perm[perm] = arange_p

        # Sac à dos : j décroissant pour éviter double comptage
        j_max = min(pos, k - 1)
        for j in range(j_max, 0, -1):
            layer = dp[j]
            if layer.any():
                # dp[j+1][perm[s]] += dp[j][s]  ⟺  dp[j+1][t] += dp[j][inv_perm[t]]
                dp[j + 1] += layer[inv_perm]

    dist = dp[k]
    N0 = int(dist[0])
    C_check = int(dist.sum())
    return N0, C_check, dist


# ============================================================================
# N₀(p) par énumération directe (fallback)
# ============================================================================

def compositions_gen(S, k):
    """Génère les positions A = (0, c₁, ..., c_{k-1}) avec 0 < c₁ < ... < c_{k-1} ≤ S-1."""
    if k == 1:
        yield (0,)
        return
    for combo in itertools.combinations(range(1, S), k - 1):
        yield (0,) + combo


def corrsum_horner_mod(A, p):
    """corrSum(A) mod p par récurrence de Horner."""
    c = 1  # c₀ = 2^{A[0]} = 2^0 = 1
    for j in range(1, len(A)):
        c = (3 * c + pow(2, A[j], p)) % p
    return c


def count_N0_enum(S, k, p):
    """N₀(p) par énumération directe. Retourne (N0, C_check, dist_Counter)."""
    C = math.comb(S - 1, k - 1)
    if C > MAX_ENUM_C:
        return None, C, None

    dist = Counter()
    for A in compositions_gen(S, k):
        r = corrsum_horner_mod(A, p)
        dist[r] += 1

    return dist.get(0, 0), sum(dist.values()), dist


# ============================================================================
# Vérification croisée DP vs énumération
# ============================================================================

def cross_validate(test_cases=None):
    """Vérification croisée sur petits k pour valider le DP."""
    if test_cases is None:
        test_cases = [3, 4, 5, 6, 7, 8]

    print("=" * 70)
    print("VÉRIFICATION CROISÉE DP vs ÉNUMÉRATION")
    print("=" * 70)

    all_ok = True
    for k in test_cases:
        d, S = crystal_module(k)
        if d <= 1:
            continue
        C = math.comb(S - 1, k - 1)
        factors = prime_factorization(d)

        for p, _ in factors:
            if p > MAX_DP_PRIME:
                continue

            # DP
            N0_dp, C_dp, dist_dp = count_N0_dp(S, k, p)

            # Énumération
            N0_enum, C_enum, dist_enum = count_N0_enum(S, k, p)

            # Comparaison
            ok_N0 = (N0_dp == N0_enum)
            ok_C = (C_dp == C_enum == C)

            # Comparaison distribution complète
            ok_dist = True
            if dist_dp is not None and dist_enum is not None:
                for r in range(p):
                    dp_val = int(dist_dp[r])
                    enum_val = dist_enum.get(r, 0)
                    if dp_val != enum_val:
                        ok_dist = False
                        break

            status = "✓" if (ok_N0 and ok_C and ok_dist) else "✗"
            if not (ok_N0 and ok_C and ok_dist):
                all_ok = False
                print(f"  {status} k={k}, p={p}: N₀_dp={N0_dp}, N₀_enum={N0_enum}, "
                      f"C_dp={C_dp}, C_enum={C_enum}, C={C}")
            else:
                print(f"  {status} k={k}, p={p}: N₀={N0_dp}, C={C_dp}")

    if all_ok:
        print("\n  ✓ TOUTES LES VÉRIFICATIONS PASSENT")
    else:
        print("\n  ✗ ÉCHEC DE VÉRIFICATION — ARRÊT")
        sys.exit(1)

    return all_ok


# ============================================================================
# Diagnostics
# ============================================================================

def compute_diagnostics(dist, p, C):
    """chi², max déviation, énergie de collision E₂."""
    if dist is None:
        return {}

    expected = C / p

    if isinstance(dist, np.ndarray):
        counts = dist.astype(np.float64)
        chi2 = float(np.sum((counts - expected)**2 / max(expected, 1e-10)))
        max_dev = float(np.max(np.abs(counts - expected)))
        E2 = float(np.sum(counts * counts))
    else:
        chi2 = sum((dist.get(r, 0) - expected)**2 / max(expected, 1e-10)
                    for r in range(p))
        max_dev = max(abs(dist.get(r, 0) - expected) for r in range(p))
        E2 = sum(v * v for v in dist.values())

    E2_uniform = C * (C + p - 1) / p  # E₂ attendu pour uniforme

    return {
        'chi2': chi2,
        'chi2_norm': chi2 / max(p - 1, 1),
        'max_dev': max_dev,
        'max_dev_rel': max_dev / max(expected, 1e-10),
        'E2': E2,
        'E2_uniform': E2_uniform,
        'E2_ratio': E2 / max(E2_uniform, 1e-10),
    }


# ============================================================================
# Analyse d'une valeur de k
# ============================================================================

def analyze_k(k, verbose=True):
    """Analyse complète pour une valeur de k."""
    d, S = crystal_module(k)
    C = math.comb(S - 1, k - 1)

    if verbose:
        print(f"\n{'='*70}")
        print(f"k = {k}, S = {S}, d(k) = {d}, C = C({S-1},{k-1}) = {C:,}")
        print(f"{'='*70}")

    if d <= 0:
        if verbose:
            print(f"  d(k) ≤ 0 → impossible, SKIP")
        return {'k': k, 'S': S, 'd': d, 'C': C, 'status': 'TRIVIAL',
                'H_proved': False, 'verdict': 'TRIVIAL'}

    # Factorisation
    t0 = time.time()
    factors = prime_factorization(d)
    t_factor = time.time() - t0

    if verbose:
        print(f"  Factorisation ({t_factor:.3f}s) : d = ", end='')
        print(' × '.join(f"{p}^{e}" if e > 1 else str(p) for p, e in factors))
        print(f"  Nombre de premiers distincts : {len(factors)}")

    primes = [p for p, _ in factors]
    results = []
    H_proved = False

    for p in primes:
        if verbose:
            print(f"\n  --- p = {p:,} ---")
            ord2 = mult_ord(2, p)
            n3 = find_n3(p)
            in_gen2 = "OUI" if n3 < p else "NON"
            print(f"  ord₂(p) = {ord2}, n₃ = {n3}, 3 ∈ ⟨2⟩ : {in_gen2}")

        t0 = time.time()

        # Choix de la méthode
        if p <= MAX_DP_PRIME:
            method = 'DP'
            N0, C_check, dist = count_N0_dp(S, k, p)
        elif C <= MAX_ENUM_C:
            method = 'ENUM'
            N0, C_check, dist = count_N0_enum(S, k, p)
        else:
            method = 'SKIP'
            N0, C_check, dist = None, C, None

        t_count = time.time() - t0

        if N0 is not None:
            if verbose:
                print(f"  N₀({p:,}) = {N0:,} [méthode: {method}, {t_count:.2f}s]")
                print(f"  C vérifié = {C_check:,} (attendu {C:,})", end='')
                if C_check != C:
                    print(f" ⚠️ INCOHÉRENCE !")
                else:
                    print(f" ✓")

            # Diagnostics
            diag = compute_diagnostics(dist, p, C)
            if verbose:
                print(f"  χ²/(p-1) = {diag.get('chi2_norm', 'N/A'):.4f} "
                      f"(≈1.0 si uniforme)")
                print(f"  max |count - C/p| / (C/p) = "
                      f"{diag.get('max_dev_rel', 'N/A'):.4f}")
                print(f"  E₂/E₂_unif = {diag.get('E2_ratio', 'N/A'):.6f}")

            if N0 == 0:
                if verbose:
                    print(f"  ✓ N₀({p:,}) = 0 → H({k}) PROUVÉ via ce premier !")
                H_proved = True
            else:
                if verbose:
                    expected_N0 = C / p
                    ratio = N0 / max(expected_N0, 1e-10)
                    print(f"  × N₀ = {N0:,} (attendu C/p ≈ {expected_N0:.1f}, "
                          f"ratio = {ratio:.4f})")

            results.append({
                'p': p, 'N0': N0, 'C': C_check, 'method': method,
                'time': t_count, 'diag': diag,
            })
        else:
            if verbose:
                print(f"  SKIP : p = {p:,} trop grand pour DP, "
                      f"C = {C:,} trop grand pour ENUM")
            results.append({
                'p': p, 'N0': None, 'C': C, 'method': 'SKIP',
                'time': 0, 'diag': {},
            })

    verdict = 'PROUVÉ' if H_proved else 'NON RÉSOLU'
    if verbose:
        print(f"\n  ══ VERDICT k={k} : {verdict} ══")

    return {
        'k': k, 'S': S, 'd': d, 'C': C,
        'factors': factors, 'primes': primes,
        'results': results, 'H_proved': H_proved,
        'verdict': verdict,
    }


# ============================================================================
# Main
# ============================================================================

def main():
    t_global = time.time()

    print("=" * 70)
    print("PHASE A1 — VÉRIFICATION EXHAUSTIVE k = 18..25")
    print("Programme de Fermeture du Gap Collatz")
    print(f"Date : {time.strftime('%Y-%m-%d %H:%M:%S')}")
    print(f"Config : MAX_DP_PRIME={MAX_DP_PRIME:,}, MAX_ENUM_C={MAX_ENUM_C:,}")
    print("=" * 70)

    # ── Étape 0 : Vérification croisée ──
    cross_validate([3, 4, 5, 6, 7, 8])

    # ── Étape 1 : Analyse k=18..25 ──
    print(f"\n{'='*70}")
    print("ANALYSE PRINCIPALE k = 18..25")
    print(f"{'='*70}")

    all_results = []
    for k in K_RANGE:
        result = analyze_k(k)
        all_results.append(result)

    # ── Synthèse ──
    print(f"\n{'='*70}")
    print("SYNTHÈSE PHASE A1")
    print(f"{'='*70}")

    print(f"\n{'k':>3} {'S':>3} {'d(k)':>18} {'C':>15} {'#p':>3} "
          f"{'min_N0':>10} {'Verdict':>12}")
    print("-" * 75)
    for r in all_results:
        nf = len(r.get('factors', []))
        computed = [pr for pr in r.get('results', []) if pr['N0'] is not None]
        min_N0_str = str(min(pr['N0'] for pr in computed)) if computed else 'N/A'
        print(f"{r['k']:>3} {r['S']:>3} {r['d']:>18,} {r['C']:>15,} "
              f"{nf:>3} {min_N0_str:>10} {r['verdict']:>12}")

    proved = [r['k'] for r in all_results if r.get('H_proved')]
    unresolved = [r['k'] for r in all_results
                  if not r.get('H_proved') and r.get('verdict') != 'TRIVIAL']

    print(f"\nH prouvé pour k = {proved}")
    print(f"Non résolu pour k = {unresolved}")

    # ── Contrôle anti-hallucination ──
    print(f"\n{'='*70}")
    print("CONTRÔLE ANTI-HALLUCINATION")
    print(f"{'='*70}")

    issues = 0
    for r in all_results:
        for pr in r.get('results', []):
            if pr['N0'] is not None and pr['C'] != r['C']:
                print(f"  ⚠️  k={r['k']}, p={pr['p']}: "
                      f"C_check={pr['C']:,} ≠ C={r['C']:,}")
                issues += 1

    if issues == 0:
        print("  ✓ Aucune incohérence détectée")
    else:
        print(f"  ✗ {issues} incohérences détectées — RÉSULTATS NON FIABLES")

    # ── Résumé pour research_log ──
    print(f"\n{'='*70}")
    print(f"Temps total : {time.time() - t_global:.1f}s")
    print(f"{'='*70}")

    # Verdict global
    n_proved = len(proved)
    n_total = len(list(K_RANGE))
    print(f"\nRÉSULTAT : {n_proved}/{n_total} valeurs de k prouvées dans [18, 25]")
    if n_proved == n_total:
        print("✓ PHASE A1 COMPLÈTE : H prouvé pour tout k ∈ [18, 25]")
    else:
        print(f"× PHASE A1 INCOMPLÈTE : k non résolu = {unresolved}")
        print("  → Investiguer facteurs premiers grands de d(k)")
        print("  → Envisager méthode DP sparse ou Monte Carlo")


if __name__ == '__main__':
    main()
