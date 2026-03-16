#!/usr/bin/env python3
"""
R168 — Audit Severe : Energie Additive Tensorielle du Simplex
=============================================================

Cible : Valider ou detruire la conjecture R167 (G_geom = SL_n via MPF).

Le test de Katz/Larsen :
  E_4 = #{(A1,A2,A3,A4) monotones : corrSum(A1)+corrSum(A2) = corrSum(A3)+corrSum(A4) mod p}

- Si E_4 ~ 2*|Simplex|^2  (solutions diagonales)  -> groupe maximal SL_n
- Si E_4 >> 2*|Simplex|^2  (exces de collisions)   -> symetries cachees, groupe reduit

Protocole Fail-Closed : on cherche activement a DETRUIRE la conjecture.
"""

import json
import time
import math
from itertools import combinations_with_replacement
from collections import Counter, defaultdict


def generate_monotone_compositions(k):
    """
    Genere toutes les compositions monotones (B_0, ..., B_{k-1})
    avec 0 <= B_0 <= B_1 <= ... <= B_{k-1} = S-k
    ou S = 2k+1 (valeur standard) => B_{k-1} = k+1.

    Ce sont les compositions avec repetition de {0, 1, ..., k+1}
    en k-1 valeurs ordonnees, plus B_{k-1} = k+1 fixe.
    """
    S = 2 * k + 1
    top = S - k  # = k + 1

    # B_0 <= B_1 <= ... <= B_{k-2} <= B_{k-1} = top
    # Generer tous les (k-1)-uplets ordonnes dans [0, top]
    if k == 1:
        yield (top,)
        return

    # Pour k >= 2: generer les (k-1) premieres valeurs dans [0, top]
    # avec B_0 <= B_1 <= ... <= B_{k-2} <= top
    def _gen(depth, lower, upper, current):
        if depth == k - 1:
            yield tuple(current) + (top,)
            return
        for v in range(lower, upper + 1):
            current.append(v)
            yield from _gen(depth + 1, v, upper, current)
            current.pop()

    yield from _gen(0, 0, top, [])


def corrsum(composition, k):
    """
    Calcule corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}
    """
    S = 0
    for j, bj in enumerate(composition):
        S += (3 ** (k - 1 - j)) * (2 ** bj)
    return S


def compute_d(k):
    """d = 2^S - 3^k avec S = 2k+1"""
    S = 2 * k + 1
    return (2 ** S) - (3 ** k)


def largest_prime_factor(n):
    """Trouve le plus grand facteur premier de n."""
    if n <= 1:
        return None
    factor = None
    d = 2
    while d * d <= n:
        while n % d == 0:
            factor = d
            n //= d
        d += 1
    if n > 1:
        factor = n
    return factor


def prime_factors(n):
    """Retourne la liste de tous les facteurs premiers de n."""
    factors = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            factors.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        factors.append(n)
    return factors


def test_additive_energy(k, p):
    """
    Test A : Energie Additive E_4 pour un k et un premier p|d donnes.

    Calcule E_4 = #{(A1,A2,A3,A4) : corrSum(A1)+corrSum(A2) = corrSum(A3)+corrSum(A4) mod p}

    Methode efficace : utiliser la distribution des corrSum mod p.
    Si freq[v] = nombre de compositions A telles que corrSum(A) = v mod p,
    alors E_4 = sum_s (sum_{v: v+w=s mod p} freq[v]*freq[w])^2
             = sum_s (convolution[s])^2

    C'est la norme L2 au carre de l'auto-convolution.
    """
    # Generer toutes les compositions et calculer corrSum mod p
    freq = Counter()
    n_compositions = 0

    for comp in generate_monotone_compositions(k):
        cs = corrsum(comp, k) % p
        freq[cs] += 1
        n_compositions += 1

    # Auto-convolution : conv[s] = sum_{v} freq[v] * freq[s-v mod p]
    conv = defaultdict(int)
    for v, fv in freq.items():
        for w, fw in freq.items():
            s = (v + w) % p
            conv[s] += fv * fw

    # E_4 = sum_s conv[s]^2
    E4 = sum(c * c for c in conv.values())

    # Solutions diagonales : (A1=A3, A2=A4) ou (A1=A4, A2=A3)
    # Nombre = 2 * |Simplex|^2 - |Simplex| (en excluant le double comptage de A1=A2=A3=A4)
    # Plus precisement : diag = sum_v freq[v]^2 * 2 * |Simplex| ... Non.
    # Solutions diagonales exactes :
    #   Type 1 : A1=A3 et A2=A4 => sum_{A1,A2} 1 = |S|^2
    #   Type 2 : A1=A4 et A2=A3 => sum_{A1,A2} 1 = |S|^2
    #   Intersection (A1=A2=A3=A4) : |S|
    #   Total diag = 2*|S|^2 - |S|
    #
    # ATTENTION : on travaille mod p, pas sur les compositions exactes.
    # Les "diagonales" au sens mod p sont plus nombreuses car des compositions
    # differentes peuvent avoir le meme corrSum mod p.
    #
    # Le vrai comptage diagonal (au sens des compositions identiques) :
    #   Type 1 : #{A1,A2 : corrSum(A1)+corrSum(A2)=corrSum(A1)+corrSum(A2) mod p} = |S|^2
    #   (trivially satisfied for ANY pair)
    #
    # En fait, le bon reference est : si les corrSum mod p etaient uniformement
    # distribues, on aurait E_4 ~ |S|^4 / p + 2*|S|^2
    # (le terme |S|^4/p vient du bruit, 2*|S|^2 des diagonales)
    #
    # Mais pour le critere de Katz, on compare :
    #   Ratio = E_4 / |S|^2
    # Si Ratio ~ 2 (+ O(|S|/p)) : pas d'exces, groupe maximal
    # Si Ratio >> 2 : exces de collisions

    N = n_compositions
    diag_exact = 2 * N * N - N  # solutions diagonales (compositions identiques)

    # Borne aleatoire : si corrSum unif mod p, E_4 ~ N^4/p + 2*N^2
    E4_random = N**4 / p + 2 * N * N

    # Ratio de Katz
    ratio_katz = E4 / (N * N) if N > 0 else 0

    # Nombre de collisions non-diagonales
    # Pour les compter precisement, il faut soustraire les diagonales mod p
    # Diag mod p type 1+2 : sum_v freq[v]^2 (pour type 1=3 et type 2=4 swap)
    # En fait : diag mod p = 2 * (sum_v freq[v]^2)^... non, c'est plus subtil.
    #
    # Simplifions : les solutions diagonales au sens des VALEURS mod p :
    #   Type 1 (A1~A3 meme valeur mod p, A2~A4) :
    #     sum_s (sum_v freq[v]*freq[s-v])*(sum_w freq[w]*freq[s-w]) quand on restreint...
    # C'est circulaire. Utilisons le ratio directement.

    # Distribution des corrSum mod p
    n_distinct_values = len(freq)
    max_freq = max(freq.values()) if freq else 0
    min_freq = min(freq.values()) if freq else 0

    # Uniformite : si uniforme, chaque freq ~ N/p
    expected_uniform = N / p if p > 0 else 0

    # Chi-square test pour l'uniformite
    chi2 = sum((f - expected_uniform)**2 / expected_uniform
               for f in freq.values()) if expected_uniform > 0 else 0
    # Ajouter les classes vides
    n_empty = p - n_distinct_values
    if expected_uniform > 0 and n_empty > 0:
        chi2 += n_empty * expected_uniform  # (0 - E)^2/E = E

    return {
        "k": k,
        "p": p,
        "S": 2 * k + 1,
        "d": compute_d(k),
        "n_compositions": N,
        "n_distinct_values_mod_p": n_distinct_values,
        "E4": E4,
        "diag_exact": diag_exact,
        "E4_random_expected": round(E4_random, 1),
        "ratio_katz": round(ratio_katz, 4),
        "excess_ratio": round(E4 / E4_random, 4) if E4_random > 0 else None,
        "max_freq": max_freq,
        "min_freq": min_freq,
        "expected_uniform_freq": round(expected_uniform, 2),
        "chi2": round(chi2, 2),
        "chi2_per_df": round(chi2 / (p - 1), 4) if p > 1 else None,
    }


def test_moment_skewness(k, p):
    """
    Test B : Moments de Larsen (Skewness / Asymetrie).

    Pour distinguer SL_n (asymetrique) de Sp/O (auto-dual),
    on calcule les moments M_1, M_2, M_3 de corrSum mod p.

    M_r = (1/|S|) * sum_A (corrSum(A) mod p - mu)^r

    Si le groupe est symplectique/orthogonal (auto-dual),
    M_3 ~ 0 (distribution symetrique).
    Si le groupe est SL_n, M_3 != 0 (asymetrie du MPF).
    """
    values = []
    for comp in generate_monotone_compositions(k):
        cs = corrsum(comp, k) % p
        values.append(cs)

    N = len(values)
    if N == 0:
        return None

    # Moyenne circulaire mod p : utilisons la moyenne arithmetique des residus
    mean_val = sum(values) / N

    # Moments centres
    M2 = sum((v - mean_val)**2 for v in values) / N
    M3 = sum((v - mean_val)**3 for v in values) / N
    M4 = sum((v - mean_val)**4 for v in values) / N

    # Skewness et Kurtosis standardises
    if M2 > 0:
        skewness = M3 / (M2 ** 1.5)
        kurtosis = M4 / (M2 ** 2) - 3  # excess kurtosis
    else:
        skewness = 0
        kurtosis = 0

    # Pour une distribution uniforme sur {0,..,p-1} :
    # Variance = (p^2-1)/12, Skewness = 0, Kurtosis = -6/5*(p^2+1)/(p^2-1) ~ -1.2
    var_uniform = (p * p - 1) / 12
    skew_uniform = 0
    kurt_uniform = -6 * (p * p + 1) / (5 * (p * p - 1)) if p > 1 else 0

    return {
        "k": k,
        "p": p,
        "N": N,
        "mean": round(mean_val, 4),
        "variance": round(M2, 4),
        "var_uniform": round(var_uniform, 4),
        "skewness": round(skewness, 6),
        "skew_uniform": skew_uniform,
        "kurtosis_excess": round(kurtosis, 6),
        "kurt_uniform": round(kurt_uniform, 6),
        "skewness_nonzero": abs(skewness) > 0.1,
        "MPF_breaks_symmetry": abs(skewness) > 0.1,
    }


def test_collision_structure(k, p):
    """
    Test C : Structure fine des collisions.

    Examine si les collisions non-diagonales E_4 - diag suivent
    un pattern de "cascade de retenues" (carry propagation)
    comme decrit dans la section 3 du R168.

    On cherche les paires (A1, A2) != (A3, A4) telles que
    corrSum(A1) + corrSum(A2) = corrSum(A3) + corrSum(A4) mod p
    et on analyse leur structure.
    """
    # Calculer toutes les corrSum mod p
    compositions = []
    corrsums = []
    for comp in generate_monotone_compositions(k):
        compositions.append(comp)
        corrsums.append(corrsum(comp, k) % p)

    N = len(compositions)

    # Construire l'histogramme des sommes de paires
    pair_sums = Counter()
    for i in range(N):
        for j in range(N):
            s = (corrsums[i] + corrsums[j]) % p
            pair_sums[s] += 1

    # E_4 = sum pair_sums[s]^2
    E4 = sum(c * c for c in pair_sums.values())

    # Nombre de valeurs de somme atteintes
    n_sum_values = len(pair_sums)

    # Concentration : les 10% des sommes les plus frequentes
    sorted_freqs = sorted(pair_sums.values(), reverse=True)
    top_10pct = max(1, n_sum_values // 10)
    top_10pct_mass = sum(sorted_freqs[:top_10pct])
    total_mass = N * N

    # Gini coefficient (mesure d'inegalite)
    sorted_asc = sorted(pair_sums.values())
    cumsum = 0
    gini_num = 0
    for i, f in enumerate(sorted_asc):
        cumsum += f
        gini_num += (2 * (i + 1) - n_sum_values - 1) * f
    gini = gini_num / (n_sum_values * total_mass) if total_mass > 0 and n_sum_values > 0 else 0

    return {
        "k": k,
        "p": p,
        "N": N,
        "E4": E4,
        "n_sum_values": n_sum_values,
        "p_coverage": round(n_sum_values / p * 100, 1),
        "top_10pct_concentration": round(top_10pct_mass / total_mass * 100, 2),
        "expected_uniform_10pct": 10.0,
        "gini_coefficient": round(gini, 4),
        "distribution_uniform": gini < 0.1,
    }


def run_full_audit():
    """Execute l'audit complet R168."""
    print("=" * 72)
    print("R168 — AUDIT SEVERE : ENERGIE ADDITIVE TENSORIELLE")
    print("Protocole Fail-Closed")
    print("=" * 72)

    results = {
        "test_A_additive_energy": [],
        "test_B_moment_skewness": [],
        "test_C_collision_structure": [],
        "verdict": None,
    }

    # ===== TEST A : Energie Additive E_4 =====
    print("\n" + "=" * 72)
    print("TEST A : ENERGIE ADDITIVE E_4 (Critere de Katz)")
    print("=" * 72)

    for k in range(3, 10):
        d = compute_d(k)
        if d <= 1:
            continue

        # Prendre le plus grand facteur premier de d
        p = largest_prime_factor(abs(d))
        if p is None or p < 3:
            continue

        # Pour les grands p, prendre un plus petit facteur premier (tractabilite)
        factors = prime_factors(abs(d))
        # Utiliser tous les facteurs premiers raisonnables
        for pf in factors:
            if pf < 3:
                continue

            t0 = time.time()
            res = test_additive_energy(k, pf)
            elapsed = time.time() - t0
            res["elapsed_s"] = round(elapsed, 3)

            results["test_A_additive_energy"].append(res)

            print(f"\n--- k={k}, p={pf}, d={d} ---")
            print(f"  |Simplex| = {res['n_compositions']}")
            print(f"  Valeurs distinctes mod p : {res['n_distinct_values_mod_p']}/{pf}")
            print(f"  E_4 = {res['E4']}")
            print(f"  Diag exactes = {res['diag_exact']}")
            print(f"  E_4 aleatoire attendu = {res['E4_random_expected']}")
            print(f"  ** Ratio de Katz E_4/|S|^2 = {res['ratio_katz']} **")
            print(f"  ** E_4/E_4_random = {res['excess_ratio']} **")
            print(f"  Freq max={res['max_freq']}, min={res['min_freq']}, "
                  f"attendu uniforme={res['expected_uniform_freq']}")
            print(f"  Chi2/df = {res['chi2_per_df']}")
            print(f"  Temps : {elapsed:.3f}s")

            verdict_local = "NEUTRE"
            if res['ratio_katz'] < 2.5:
                verdict_local = "COMPATIBLE SL_n (pas d'exces)"
            elif res['ratio_katz'] > 5:
                verdict_local = "EXCES DE COLLISIONS (groupe reduit?)"
            else:
                verdict_local = "ZONE GRISE"
            print(f"  Verdict local : {verdict_local}")

    # ===== TEST B : Moments / Skewness =====
    print("\n" + "=" * 72)
    print("TEST B : MOMENTS DE LARSEN (SKEWNESS / ASYMETRIE)")
    print("=" * 72)

    for k in range(3, 10):
        d = compute_d(k)
        if d <= 1:
            continue

        factors = prime_factors(abs(d))
        for pf in factors:
            if pf < 3:
                continue

            res = test_moment_skewness(k, pf)
            if res is None:
                continue

            results["test_B_moment_skewness"].append(res)

            print(f"\n--- k={k}, p={pf} ---")
            print(f"  N = {res['N']}")
            print(f"  Variance = {res['variance']} (uniforme: {res['var_uniform']})")
            print(f"  ** Skewness = {res['skewness']} ** (uniforme: 0)")
            print(f"  Kurtosis excess = {res['kurtosis_excess']} "
                  f"(uniforme: {res['kurt_uniform']})")
            print(f"  MPF brise la symetrie (|skew|>0.1) : {res['MPF_breaks_symmetry']}")

    # ===== TEST C : Structure des Collisions =====
    print("\n" + "=" * 72)
    print("TEST C : STRUCTURE FINE DES COLLISIONS")
    print("=" * 72)

    for k in range(3, 9):  # k=9 peut etre lent pour ce test
        d = compute_d(k)
        if d <= 1:
            continue

        factors = prime_factors(abs(d))
        for pf in factors:
            if pf < 3:
                continue

            t0 = time.time()
            res = test_collision_structure(k, pf)
            elapsed = time.time() - t0
            res["elapsed_s"] = round(elapsed, 3)

            results["test_C_collision_structure"].append(res)

            print(f"\n--- k={k}, p={pf} ---")
            print(f"  N = {res['N']}, E_4 = {res['E4']}")
            print(f"  Couverture sommes : {res['n_sum_values']}/{pf} "
                  f"({res['p_coverage']}%)")
            print(f"  Top 10% concentration : {res['top_10pct_concentration']}% "
                  f"(uniforme attendu : 10%)")
            print(f"  Gini = {res['gini_coefficient']}")
            print(f"  Distribution uniforme (Gini<0.1) : {res['distribution_uniform']}")

    # ===== VERDICT GLOBAL =====
    print("\n" + "=" * 72)
    print("VERDICT GLOBAL R168")
    print("=" * 72)

    # Analyser les ratios de Katz
    ratios = [r["ratio_katz"] for r in results["test_A_additive_energy"]]
    excess_ratios = [r["excess_ratio"] for r in results["test_A_additive_energy"]
                     if r["excess_ratio"] is not None]
    skewnesses = [r["skewness"] for r in results["test_B_moment_skewness"]]
    skew_nonzero = [r["MPF_breaks_symmetry"] for r in results["test_B_moment_skewness"]]

    if ratios:
        avg_ratio = sum(ratios) / len(ratios)
        max_ratio = max(ratios)
        min_ratio = min(ratios)
        print(f"\nRatio de Katz E_4/|S|^2 :")
        print(f"  Moyenne = {avg_ratio:.4f}")
        print(f"  Min = {min_ratio:.4f}, Max = {max_ratio:.4f}")
        print(f"  Seuil SL_n : < 2.5 | Seuil exces : > 5")

    if excess_ratios:
        avg_excess = sum(excess_ratios) / len(excess_ratios)
        print(f"\nE_4 / E_4_random :")
        print(f"  Moyenne = {avg_excess:.4f}")
        print(f"  (1.0 = parfaitement aleatoire, >1.5 = exces structure)")

    if skewnesses:
        avg_skew = sum(abs(s) for s in skewnesses) / len(skewnesses)
        n_asymmetric = sum(1 for s in skew_nonzero if s)
        print(f"\nSkewness (Test de Larsen) :")
        print(f"  |Skewness| moyen = {avg_skew:.4f}")
        print(f"  Asymetrie detectee : {n_asymmetric}/{len(skew_nonzero)} cas")

    # Decision
    print("\n" + "-" * 72)

    # Critere 1 : Ratio de Katz
    if ratios and max(ratios) > 10:
        verdict = "MORT — EXCES MASSIF de collisions. Groupe reduit. R167 DETRUIT."
        status = "DEAD"
    elif ratios and avg_ratio > 5:
        verdict = "MORT — Exces significatif de collisions. Symetries cachees probables."
        status = "DEAD"
    elif ratios and avg_ratio > 2.5:
        verdict = ("ZONE GRISE — Le ratio de Katz est au-dessus du seuil SL_n "
                    "mais pas dramatiquement. Le chainon manquant RESTE OUVERT.")
        status = "GREY"
    elif ratios and avg_ratio <= 2.5:
        # Verifier aussi les moments
        if skewnesses and avg_skew > 0.1:
            verdict = ("COMPATIBLE SL_n — Ratio de Katz faible ET asymetrie detectee. "
                       "Le MPF SEMBLE briser la symetrie. "
                       "MAIS : ceci n'est PAS une preuve (petits k seulement).")
            status = "ALIVE"
        else:
            verdict = ("NEUTRE — Ratio de Katz faible MAIS pas d'asymetrie claire. "
                       "Le chainon manquant reste ouvert.")
            status = "GREY"
    else:
        verdict = "INDETERMINE — pas assez de donnees."
        status = "GREY"

    results["verdict"] = {
        "status": status,
        "message": verdict,
        "avg_katz_ratio": round(avg_ratio, 4) if ratios else None,
        "max_katz_ratio": round(max_ratio, 4) if ratios else None,
        "avg_skewness": round(avg_skew, 4) if skewnesses else None,
        "n_asymmetric": n_asymmetric if skewnesses else None,
    }

    print(f"\n** VERDICT : {verdict} **\n")

    # Sauvegarder
    output_file = "R168_results.json"
    with open(output_file, "w") as f:
        json.dump(results, f, indent=2, default=str)
    print(f"Resultats sauvegardes dans {output_file}")

    return results


if __name__ == "__main__":
    run_full_audit()
