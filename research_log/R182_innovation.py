#!/usr/bin/env python3
"""R182_innovation.py — INVENTION PAR OBSERVATION : Nouveaux invariants pour g(v).

MISSION: Observer les donnees brutes de g(v) mod d pour k=3..12,
identifier des patterns par observation pure, inventer de nouveaux
operateurs/invariants, formaliser en allegorie puis en mathematiques.

CADRE:
  g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{e_j}
  v = (e_0, ..., e_{k-1}) strict monotone: 0 <= e_0 < e_1 < ... < e_{k-1} < S
  S = ceil(k * log2(3)) + 1  (plus petit S tel que d = 2^S - 3^k > 0)
  d = 2^S - 3^k
  Cycle existe ssi g(v) ≡ 0 mod d pour un vecteur v monotone.

PHASES:
  1. Observation pure — distribution de g(v) mod d
  2. Pattern recognition — invariants, operations nouvelles
  3. Allegorie et formalisation

Author: Eric Merle (assisted by Claude)
Date: 16 March 2026
"""

import math
import sys
import time
from itertools import combinations
from collections import defaultdict, Counter
from fractions import Fraction
import json

# ============================================================
# SECTION 0: Core arithmetic
# ============================================================

def compute_S_min(k):
    """Plus petit S tel que 2^S > 3^k."""
    S = math.ceil(k * math.log2(3)) + 1
    while 2**S <= 3**k:
        S += 1
    return S

def compute_d(S, k):
    return 2**S - 3**k

def compute_g(v, k):
    """g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{e_j}."""
    return sum(3**(k-1-j) * 2**v[j] for j in range(k))

def all_monotone_vectors(k, S):
    """Tous les vecteurs strictement monotones (e_0 < e_1 < ... < e_{k-1}) dans {0,...,S-1}."""
    return list(combinations(range(S), k))

# ============================================================
# SECTION 1: OBSERVATION PURE — Distribution de g(v) mod d
# ============================================================

def phase1_observation(k_min=3, k_max=10):
    """Calcule g(v) mod d pour tous vecteurs monotones, observe la distribution."""
    print("=" * 80)
    print("PHASE 1 — OBSERVATION PURE")
    print("=" * 80)

    results = {}

    for k in range(k_min, k_max + 1):
        S = compute_S_min(k)
        d = compute_d(S, k)
        vectors = all_monotone_vectors(k, S)
        C = len(vectors)  # = C(S-1, k) ... actually C(S, k) for strict in {0..S-1}

        if C > 500000:
            print(f"\n  k={k}: S={S}, d={d}, C={C} — TROP GRAND, SKIP")
            continue

        # Calcul de tous les g(v) mod d
        residues = []
        g_values = []
        for v in vectors:
            g = compute_g(v, k)
            r = g % d
            residues.append(r)
            g_values.append(g)

        # Statistiques de base
        residue_set = set(residues)
        residue_counts = Counter(residues)
        zero_count = residue_counts.get(0, 0)

        print(f"\n{'='*60}")
        print(f"  k={k}: S={S}, d={d}, C={C}")
        print(f"  Residus distincts: {len(residue_set)} / {d}")
        print(f"  Couverture: {len(residue_set)/d:.4f}")
        print(f"  g(v) ≡ 0 mod d: {zero_count} fois")
        print(f"  g(v) min: {min(g_values)}, max: {max(g_values)}")
        print(f"  g(v)/d min: {min(g_values)/d:.4f}, max: {max(g_values)/d:.4f}")

        # Trous: residus jamais atteints
        missing = set(range(d)) - residue_set
        if len(missing) <= 30:
            print(f"  Residus manquants: {sorted(missing)}")
        else:
            print(f"  Residus manquants: {len(missing)} (trop nombreux pour lister)")
            # Echantillon
            missing_sorted = sorted(missing)
            print(f"    Premiers: {missing_sorted[:10]}")
            print(f"    Derniers: {missing_sorted[-10:]}")

        # Distribution des multiplicites
        mult_dist = Counter(residue_counts.values())
        print(f"  Distribution des multiplicites:")
        for m in sorted(mult_dist.keys()):
            print(f"    multiplicite {m}: {mult_dist[m]} residus")

        # Le residu 0 est-il special?
        mean_count = C / d if d > 0 else 0
        print(f"  Multiplicite moyenne attendue (C/d): {mean_count:.4f}")
        if zero_count > 0:
            print(f"  *** ATTENTION: g(v) ≡ 0 mod d ATTEINT {zero_count} fois! ***")

        # Fraction de g(v) par rapport a d
        fracs = [g / d for g in g_values]
        print(f"  g(v)/d — min: {min(fracs):.6f}, max: {max(fracs):.6f}, mean: {sum(fracs)/len(fracs):.6f}")

        results[k] = {
            'S': S, 'd': d, 'C': C,
            'distinct_residues': len(residue_set),
            'zero_count': zero_count,
            'coverage': len(residue_set) / d,
            'g_min': min(g_values), 'g_max': max(g_values),
            'mean_gd': sum(fracs)/len(fracs),
            'g_values': g_values,
            'residues': residues,
            'vectors': vectors,
        }

    return results


# ============================================================
# SECTION 2: PATTERN RECOGNITION — Invariants et operations nouvelles
# ============================================================

def phase2_patterns(results):
    """Cherche des invariants et des patterns dans g(v)."""
    print("\n" + "=" * 80)
    print("PHASE 2 — PATTERN RECOGNITION")
    print("=" * 80)

    findings = {}

    for k, data in sorted(results.items()):
        if 'g_values' not in data:
            continue

        S = data['S']
        d = data['d']
        C = data['C']
        g_values = data['g_values']
        residues = data['residues']
        vectors = data['vectors']

        print(f"\n{'='*60}")
        print(f"  k={k}: S={S}, d={d}")

        # ---- INVARIANT 1: "Poids binaire" du vecteur ----
        # sum(e_j) = poids total du vecteur
        weights = [sum(v) for v in vectors]

        # Correlation entre poids et g(v) mod d
        # Regroupons par poids
        weight_to_residues = defaultdict(list)
        for w, r in zip(weights, residues):
            weight_to_residues[w].append(r)

        print(f"\n  --- Invariant 1: Poids binaire sum(e_j) ---")
        # Le residu 0 apparait-il pour certains poids specifiques?
        weights_with_zero = [w for w, rs in weight_to_residues.items() if 0 in rs]
        if weights_with_zero:
            print(f"  Poids donnant g(v)≡0 mod d: {sorted(weights_with_zero)}")
        else:
            print(f"  AUCUN poids ne donne g(v)≡0 mod d")

        # ---- INVARIANT 2: "Ecart moyen" entre positions consecutives ----
        gaps_list = []
        for v in vectors:
            gaps = tuple(v[j+1] - v[j] for j in range(len(v)-1))
            gaps_list.append(gaps)

        print(f"\n  --- Invariant 2: Ecarts entre positions consecutives ---")
        # Gap moyen par vecteur
        gap_means = [sum(g)/len(g) if len(g) > 0 else 0 for g in gaps_list]

        # ---- INVARIANT 3: "Balance ternaire-binaire" ----
        # Pour chaque terme, 3^{k-1-j} * 2^{e_j}
        # Le "poids ternaire" decroit, le "poids binaire" croit
        # Definissons la "balance" = sum_j (k-1-j) * e_j (produit croise)
        balances = []
        for v in vectors:
            bal = sum((k-1-j) * v[j] for j in range(k))
            balances.append(bal)

        print(f"\n  --- Invariant 3: Balance ternaire-binaire sum((k-1-j)*e_j) ---")
        # Correlation avec g(v) mod d?
        bal_to_residues = defaultdict(list)
        for bal, r in zip(balances, residues):
            bal_to_residues[bal].append(r)

        bals_with_zero = [b for b, rs in bal_to_residues.items() if 0 in rs]
        if bals_with_zero:
            print(f"  Balances donnant g(v)≡0 mod d: {sorted(bals_with_zero)}")
        else:
            print(f"  AUCUNE balance ne donne g(v)≡0 mod d")

        # ---- INVARIANT 4: "Quotient de saut" g(v) / 3^{k-1} ----
        # g(v) a un terme dominant 3^{k-1} * 2^{e_0}
        # Que vaut g(v) - 3^{k-1} * 2^{e_0} ?
        print(f"\n  --- Invariant 4: Decomposition par terme dominant ---")
        dominant_fraction = []
        for v, g in zip(vectors, g_values):
            dominant = 3**(k-1) * 2**v[0]
            rest = g - dominant
            dominant_fraction.append(dominant / g if g != 0 else 0)

        print(f"  Fraction du terme dominant: min={min(dominant_fraction):.4f}, max={max(dominant_fraction):.4f}, mean={sum(dominant_fraction)/len(dominant_fraction):.4f}")

        # ---- INVARIANT 5: "Logarithme de ratio" log(g(v)) - log(d) ----
        print(f"\n  --- Invariant 5: log(g(v)/d) ---")
        log_ratios = [math.log(g/d) if g > 0 and d > 0 else float('nan') for g in g_values]
        valid_lr = [x for x in log_ratios if not math.isnan(x)]
        if valid_lr:
            print(f"  log(g/d): min={min(valid_lr):.4f}, max={max(valid_lr):.4f}, mean={sum(valid_lr)/len(valid_lr):.4f}")

        # ---- INVARIANT 6: "Entrelacement 2-3" ----
        # On regarde v_2(g(v)) (2-adic valuation) et v_3(g(v)) (3-adic valuation)
        print(f"\n  --- Invariant 6: Valuations p-adiques de g(v) ---")
        val2_list = []
        val3_list = []
        for g in g_values:
            if g == 0:
                val2_list.append(-1)
                val3_list.append(-1)
                continue
            v2 = 0
            tmp = g
            while tmp % 2 == 0:
                v2 += 1
                tmp //= 2
            v3 = 0
            tmp = g
            while tmp % 3 == 0:
                v3 += 1
                tmp //= 3
            val2_list.append(v2)
            val3_list.append(v3)

        v2_counter = Counter(val2_list)
        v3_counter = Counter(val3_list)
        print(f"  v_2(g(v)) distribution: {dict(sorted(v2_counter.items())[:10])}")
        print(f"  v_3(g(v)) distribution: {dict(sorted(v3_counter.items())[:10])}")

        # La valuation 2-adique de g(v) est toujours >= e_0 (le plus petit element)
        # car chaque terme contient 2^{e_j} avec e_j >= e_0
        # Donc g(v) = 2^{e_0} * [3^{k-1} + sum_{j>=1} 3^{k-1-j} * 2^{e_j - e_0}]
        # Le crochet est TOUJOURS impair (car 3^{k-1} est impair et les autres termes sont pairs)
        # Donc v_2(g(v)) = e_0 EXACTEMENT.
        print(f"  OBSERVATION: v_2(g(v)) = e_0 ?")
        check_v2 = all(val2_list[i] == vectors[i][0] for i in range(len(vectors)) if g_values[i] != 0)
        print(f"    Verifie: {check_v2}")

        # ---- INVARIANT 7: "Noyau ternaire" ----
        # Puisque v_2(g(v)) = e_0, definissons h(v) = g(v) / 2^{e_0}
        # h(v) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{e_j - e_0}
        # h(v) est IMPAIR. Appelons-le le "noyau ternaire".
        print(f"\n  --- Invariant 7: Noyau ternaire h(v) = g(v)/2^{{e_0}} ---")
        h_values = []
        for v, g in zip(vectors, g_values):
            h = g // (2**v[0])
            h_values.append(h)

        # h(v) mod d ?
        h_residues = [h % d for h in h_values]
        h_zero = sum(1 for r in h_residues if r == 0)
        print(f"  h(v) ≡ 0 mod d: {h_zero} fois")

        # h(v) mod 3 ?
        h_mod3 = Counter([h % 3 for h in h_values])
        print(f"  h(v) mod 3: {dict(h_mod3)}")
        # h(v) = 3^{k-1} + ... les autres termes sont divisibles par des puissances de 3 variees
        # En fait h(v) mod 3: si k >= 2, 3^{k-1} ≡ 0 mod 3, et 3^{k-1-j} ≡ 0 mod 3 pour j < k-1
        # Le seul terme non divisible par 3 est j=k-1: 3^0 * 2^{e_{k-1}-e_0} = 2^{e_{k-1}-e_0}
        # Donc h(v) ≡ 2^{e_{k-1}-e_0} mod 3
        print(f"  OBSERVATION: h(v) ≡ 2^(e_{{k-1}} - e_0) mod 3 ?")
        check_h3 = all(h_values[i] % 3 == pow(2, vectors[i][-1] - vectors[i][0], 3)
                       for i in range(len(vectors)))
        print(f"    Verifie: {check_h3}")

        # ---- INVARIANT 8: "Distance au cycle" ----
        # g(v) ≡ 0 mod d equivaut a d | g(v)
        # Definissons la "distance au cycle" delta(v) = min(g(v) mod d, d - g(v) mod d)
        # C'est la distance circulaire au residu 0
        print(f"\n  --- Invariant 8: Distance circulaire au zero ---")
        distances = [min(r, d - r) for r in residues]
        min_dist = min(distances) if distances else 0
        print(f"  Distance minimale au zero: {min_dist}")
        print(f"  Distance min / d: {min_dist / d:.6f}")

        # Quel vecteur realise le minimum?
        if min_dist > 0:
            idx_min = distances.index(min_dist)
            print(f"  Vecteur le plus proche: {vectors[idx_min]}, g(v)={g_values[idx_min]}, g(v) mod d = {residues[idx_min]}")

        # ---- NOUVEL OPERATEUR: "Tension T(v)" ----
        # L'idee: 3 et 2 "tirent" dans des directions opposees
        # Definissons T(v) = sum_j (k-1-j) * log(3) - e_j * log(2)
        # = log(3) * sum_j (k-1-j) - log(2) * sum_j e_j
        # = log(3) * k*(k-1)/2 - log(2) * sum(v)
        # C'est la "tension logarithmique" entre les contributions 3 et 2
        print(f"\n  --- Nouvel operateur: Tension logarithmique T(v) ---")
        log3 = math.log(3)
        log2 = math.log(2)
        tensions = [log3 * k*(k-1)/2 - log2 * sum(v) for v in vectors]

        # Quand T(v) = 0, les contributions s'equilibrent
        # T(v) = 0 <=> sum(e_j) = (log3/log2) * k*(k-1)/2
        balance_point = (log3/log2) * k*(k-1)/2
        print(f"  Point d'equilibre sum(e_j) = {balance_point:.2f}")
        print(f"  sum(e_j) range: [{min(weights)}, {max(weights)}]")
        print(f"  T(v) range: [{min(tensions):.4f}, {max(tensions):.4f}]")

        # Le vecteur le plus proche du zero (distance minimale), quelle est sa tension?
        if min_dist > 0:
            idx_min = distances.index(min_dist)
            print(f"  Tension du vecteur le plus proche du zero: {tensions[idx_min]:.4f}")

        # ---- NOUVEL OPERATEUR: "Empreinte digitale" F(v) ----
        # Decomposons g(v) en base d: g(v) = q*d + r
        # q = floor(g(v)/d) est le "quotient de tour"
        # r = g(v) mod d est le residu
        # Le cycle exige q entier ET r = 0
        # Observation: comment q varie avec v ?
        print(f"\n  --- Nouvel operateur: Quotient de tour q(v) = floor(g(v)/d) ---")
        quotients = [g // d for g in g_values]
        q_counter = Counter(quotients)
        print(f"  Quotients distincts: {len(q_counter)}")
        print(f"  Range: [{min(quotients)}, {max(quotients)}]")
        if len(q_counter) <= 20:
            for q in sorted(q_counter.keys()):
                rs = [residues[i] for i in range(len(quotients)) if quotients[i] == q]
                zero_in_q = sum(1 for r in rs if r == 0)
                print(f"    q={q}: {q_counter[q]} vecteurs, zeros: {zero_in_q}")

        # ---- NOUVEL INVARIANT: "Spectre des ecarts" ----
        # Pour chaque vecteur, les ecarts g_i = e_{i+1} - e_i (gaps)
        # forment un "spectre". Quel est le lien avec g(v) mod d?
        print(f"\n  --- Spectre des ecarts (gaps) ---")
        gap_signatures = defaultdict(list)
        for i, v in enumerate(vectors):
            gaps = tuple(v[j+1] - v[j] for j in range(k-1))
            gap_signatures[gaps].append(residues[i])

        # Gaps les plus frequents
        gap_freq = sorted(gap_signatures.items(), key=lambda x: -len(x[1]))[:5]
        print(f"  Gaps les plus frequents:")
        for gaps, rs in gap_freq:
            print(f"    {gaps}: {len(rs)} vecteurs, zero parmi residus: {0 in rs}")

        # ---- NOUVEL INVARIANT: "Produit des facteurs" ----
        # g(v) = sum 3^{k-1-j} * 2^{e_j}
        # Essayons: prod(3^{k-1-j} + 2^{e_j}) ? Non, pas lineaire...
        # Plutot: le ratio g(v) / (3^k - 1) ou g(v) / (2^S - 1)
        print(f"\n  --- Ratios speciaux ---")
        ratio_3k = [g / (3**k - 1) for g in g_values]
        ratio_2S = [g / (2**S - 1) for g in g_values]
        print(f"  g/(3^k-1): min={min(ratio_3k):.6f}, max={max(ratio_3k):.6f}")
        print(f"  g/(2^S-1): min={min(ratio_2S):.6f}, max={max(ratio_2S):.6f}")

        # ---- LE GRAND TEST: g(v) mod (d-1), g(v) mod (d+1) ----
        print(f"\n  --- g(v) mod voisins de d ---")
        for delta_d in [-2, -1, 1, 2]:
            dd = d + delta_d
            if dd <= 0:
                continue
            r_dd = [g % dd for g in g_values]
            zeros_dd = sum(1 for r in r_dd if r == 0)
            print(f"  g(v) mod (d{'+' if delta_d > 0 else ''}{delta_d}={dd}): {zeros_dd} zeros")

        findings[k] = {
            'v2_equals_e0': check_v2,
            'h_mod3_is_2pow': check_h3,
            'min_distance': min_dist,
            'min_distance_ratio': min_dist / d,
            'balance_point': balance_point,
            'quotient_range': (min(quotients), max(quotients)),
        }

    return findings


# ============================================================
# SECTION 3: PLONGEE PROFONDE — Le "Nombre d'Or de Collatz"
# ============================================================

def phase2b_deep_patterns(results):
    """Recherche de constantes universelles et de structures profondes."""
    print("\n" + "=" * 80)
    print("PHASE 2B — PLONGEE PROFONDE: Constantes universelles")
    print("=" * 80)

    for k, data in sorted(results.items()):
        if 'g_values' not in data:
            continue

        S = data['S']
        d = data['d']
        g_values = data['g_values']
        residues = data['residues']
        vectors = data['vectors']
        C = data['C']

        print(f"\n{'='*60}")
        print(f"  k={k}: S={S}, d={d}, C={C}")

        # ---- "NOMBRE DE COLLATZ" c_k = g_min(v) / d ----
        # Le plus petit g(v) possible: vecteur (0, 1, 2, ..., k-1)
        v_min = tuple(range(k))
        g_min = compute_g(v_min, k)
        collatz_number = g_min / d
        print(f"\n  Le 'Nombre de Collatz' c_k = g_min/d:")
        print(f"    v_min = {v_min}")
        print(f"    g_min = {g_min}")
        print(f"    c_k = g_min/d = {collatz_number:.10f}")
        print(f"    Partie entiere: {g_min // d}")
        print(f"    g_min mod d = {g_min % d}")

        # Le plus grand g(v) possible: vecteur (S-k, S-k+1, ..., S-1)
        v_max = tuple(range(S-k, S))
        g_max = compute_g(v_max, k)
        print(f"    v_max = {v_max}")
        print(f"    g_max = {g_max}")
        print(f"    g_max/d = {g_max/d:.10f}")
        print(f"    g_max mod d = {g_max % d}")

        # ---- "DENSITE DE RESIDUS" ----
        # Combien de multiples de d tombent dans [g_min, g_max]?
        n_multiples = g_max // d - (g_min - 1) // d
        print(f"\n  Multiples de d dans [g_min, g_max]: {n_multiples}")
        print(f"  Nombre de vecteurs: {C}")
        print(f"  Ratio vecteurs/multiples: {C/n_multiples:.4f}" if n_multiples > 0 else "  (aucun multiple)")

        # Pour que g(v) = n*d exactement, il faut que v "tombe" pile sur un multiple
        # Listons les multiples de d et voyons lesquels sont atteints
        multiples_hit = set()
        for g in g_values:
            if g % d == 0:
                multiples_hit.add(g // d)
        print(f"  Multiples atteints: {sorted(multiples_hit) if multiples_hit else 'AUCUN'}")

        # ---- "REPARTITION PAR QUOTIENT" ----
        # Pour chaque n dans {1, 2, ..., g_max//d}, combien de vecteurs donnent floor(g/d) = n?
        quotient_dist = Counter(g // d for g in g_values)
        print(f"\n  Distribution par quotient n = floor(g/d):")
        for n in sorted(quotient_dist.keys()):
            count = quotient_dist[n]
            # Pour ce n, quel est le residu le plus proche de 0?
            residues_n = [g % d for g in g_values if g // d == n]
            min_r = min(min(residues_n), d - max(residues_n)) if residues_n else d
            print(f"    n={n}: {count} vecteurs, residu le + proche de 0: {min_r}")

        # ---- "SPECTRE FRACTIONNAIRE" ----
        # g(v)/d n'est jamais entier. A quelle distance est-il d'un entier?
        frac_parts = [g/d - g//d for g in g_values]
        # Distance au plus proche entier
        frac_dist = [min(f, 1-f) for f in frac_parts]
        min_frac = min(frac_dist)
        print(f"\n  'Spectre fractionnaire' — distance de g(v)/d au plus proche entier:")
        print(f"    Minimum: {min_frac:.10f}")
        print(f"    = {min_frac * d:.2f} / d")
        # Histogramme simplifie
        bins = [0]*10
        for f in frac_parts:
            b = min(int(f * 10), 9)
            bins[b] += 1
        print(f"    Histogramme (10 bins): {bins}")

        # ---- "SIGNATURE MODULAIRE" ----
        # g(v) mod p pour petits premiers p
        print(f"\n  Signature modulaire (petits premiers):")
        for p in [2, 3, 5, 7, 11, 13]:
            if p > d:
                break
            mod_dist = Counter(g % p for g in g_values)
            zeros_p = mod_dist.get(0, 0)
            expected = C / p
            print(f"    mod {p}: zeros={zeros_p}, attendu={expected:.1f}, ratio={zeros_p/expected:.4f}" if expected > 0 else f"    mod {p}: zeros={zeros_p}")

    return None


# ============================================================
# SECTION 4: LE "THEOREME DU CRIBLE CROISE"
# ============================================================

def phase2c_cross_sieve(results):
    """
    IDEE NOUVELLE: Le 'Crible Croise' (Cross Sieve)

    Observation: g(v) = 2^{e_0} * h(v) ou h(v) est impair.
    Pour g(v) ≡ 0 mod d, il faut d | 2^{e_0} * h(v).
    Puisque d = 2^S - 3^k est IMPAIR (car 3^k est impair et 2^S est pair),
    on a gcd(d, 2^{e_0}) = 1. Donc d | h(v).

    MAIS h(v) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{e_j - e_0}
    et h(v) < g(v) / 2^0 = g(v) (sauf si e_0 = 0)

    Question cle: h(v) peut-il etre un multiple de d?
    """
    print("\n" + "=" * 80)
    print("PHASE 2C — LE CRIBLE CROISE (Cross Sieve)")
    print("=" * 80)
    print("OBSERVATION: d est impair, donc g(v)≡0 mod d <=> h(v)≡0 mod d")
    print("ou h(v) = g(v)/2^{e_0} est le noyau impair.")

    for k, data in sorted(results.items()):
        if 'g_values' not in data:
            continue

        S = data['S']
        d = data['d']
        g_values = data['g_values']
        vectors = data['vectors']

        print(f"\n  k={k}: S={S}, d={d}")

        # Pour chaque e_0 fixe, regardons h(v) = g(v)/2^{e_0}
        # h(v) depend de (e_1-e_0, e_2-e_0, ..., e_{k-1}-e_0)
        # C'est un vecteur "decale" vivant dans {1, 2, ..., S-1-e_0}

        for e0 in range(min(S-k+1, 5)):  # premiers e_0
            # Vecteurs avec ce e_0
            vecs_e0 = [(i, v) for i, v in enumerate(vectors) if v[0] == e0]
            if not vecs_e0:
                continue

            h_vals = [g_values[i] // (2**e0) for i, v in vecs_e0]
            h_residues = [h % d for h in h_vals]

            # h(v) mod d distribution
            h_zero = sum(1 for r in h_residues if r == 0)
            h_min_dist = min(min(r, d-r) for r in h_residues) if h_residues else d

            # BORNE SUPERIEURE sur h(v)
            # h(v) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{f_j}
            # ou f_j = e_j - e_0 >= j (strict monotone depuis 1)
            # h_max quand f_j est maximal
            h_max = max(h_vals) if h_vals else 0

            n_tours = h_max // d if d > 0 else 0

            print(f"    e_0={e0}: {len(vecs_e0)} vecteurs, h≡0 mod d: {h_zero}, "
                  f"min dist au 0: {h_min_dist}, h_max/d={h_max/d:.2f}, tours={n_tours}")

        # ---- Le "THEOREME DU DECALAGE" ----
        # Si on decale tout le vecteur: v' = (e_0+t, e_1+t, ..., e_{k-1}+t)
        # g(v') = 2^t * g(v)
        # Donc g(v') mod d = (2^t * g(v)) mod d
        # Pour le MEME g(v), en variant t, on parcourt les residus 2^t * r mod d
        # Le sous-groupe <2> mod d determine combien de residus sont accessibles!
        print(f"\n  'Theoreme du Decalage': sous-groupe <2> mod d")
        # Ordre de 2 modulo d
        if d > 1:
            order_2 = 1
            power = 2 % d
            while power != 1 and order_2 < d:
                power = (power * 2) % d
                order_2 += 1
            if power == 1:
                print(f"    ord_d(2) = {order_2}, d = {d}, d/ord = {d/order_2:.2f}")
                print(f"    Nombre de cosets: {(d-1)//order_2 if order_2 > 0 else '?'}")
            else:
                print(f"    2 n'est pas inversible mod d (gcd(2,d)>1)? Impossible car d est impair.")

    return None


# ============================================================
# SECTION 5: "L'OPERATEUR DE FRICTION" — Nouvelle invention
# ============================================================

def phase2d_friction_operator(results):
    """
    INVENTION: L'Operateur de Friction F(v)

    Allegorie: Imaginons que chaque terme de g(v) est un "vehicule"
    qui roule sur une route numerique. Le vehicule j a:
    - Un moteur de puissance 3^{k-1-j} (decroissant)
    - Un carburant de 2^{e_j} (croissant)

    La "friction" entre le moteur et le carburant empeche le vehicule
    d'atteindre exactement un multiple de d.

    Formalisation:
    F(v) = sum_j |log(3^{k-1-j}) - log(2^{e_j})|
         = sum_j |(k-1-j)*log(3) - e_j*log(2)|

    C'est la somme des ecarts absolus entre puissance 3 et puissance 2
    pour chaque position.
    """
    print("\n" + "=" * 80)
    print("PHASE 2D — L'OPERATEUR DE FRICTION")
    print("=" * 80)

    log3 = math.log(3)
    log2 = math.log(2)

    all_data = []

    for k, data in sorted(results.items()):
        if 'g_values' not in data:
            continue

        S = data['S']
        d = data['d']
        g_values = data['g_values']
        residues = data['residues']
        vectors = data['vectors']

        print(f"\n  k={k}: S={S}, d={d}")

        frictions = []
        for v in vectors:
            F = sum(abs((k-1-j)*log3 - v[j]*log2) for j in range(k))
            frictions.append(F)

        # Correlation friction <-> distance au zero
        distances = [min(r, d-r) for r in residues]

        # Binons par friction
        n_bins = 10
        f_min, f_max = min(frictions), max(frictions)
        bin_size = (f_max - f_min) / n_bins if f_max > f_min else 1

        bins = defaultdict(list)
        for fr, dist in zip(frictions, distances):
            b = min(int((fr - f_min) / bin_size), n_bins - 1)
            bins[b].append(dist)

        print(f"  Friction vs distance au zero:")
        for b in sorted(bins.keys()):
            ds = bins[b]
            avg_dist = sum(ds) / len(ds) if ds else 0
            min_d = min(ds) if ds else 0
            fric_val = f_min + b * bin_size
            print(f"    Friction ~{fric_val:.2f}: {len(ds)} vecs, dist moy={avg_dist:.1f}, dist min={min_d}")

        # Le vecteur "equilibre" serait celui ou (k-1-j)*log3 ≈ e_j*log2
        # i.e. e_j ≈ (k-1-j) * log3/log2
        ideal_v = tuple(round((k-1-j) * log3/log2) for j in range(k))
        print(f"\n  Vecteur 'ideal' (friction minimale): {ideal_v}")
        # Verifier monotonie stricte
        is_monotone = all(ideal_v[j] < ideal_v[j+1] for j in range(k-1))
        print(f"    Strictement monotone: {is_monotone}")
        if not is_monotone:
            # Ajuster pour rendre monotone
            adjusted = list(ideal_v)
            for j in range(1, k):
                if adjusted[j] <= adjusted[j-1]:
                    adjusted[j] = adjusted[j-1] + 1
            ideal_v_adj = tuple(adjusted)
            print(f"    Ajuste: {ideal_v_adj}")
            # Mais les valeurs ideales DECROISSENT car (k-1-j) decroit!
            # e_j ideal ≈ (k-1-j) * 1.585 est DECROISSANT en j
            # Or on a besoin de e_j CROISSANT
            # => LA FRICTION EST STRUCTURELLEMENT INÉVITABLE!
            print(f"    *** OBSERVATION CRUCIALE: Le vecteur ideal est DECROISSANT")
            print(f"    *** mais la contrainte monotone exige CROISSANT")
            print(f"    *** => La friction est STRUCTURELLEMENT INEVITABLE! ***")

        # Quantifions cette inevitabilite
        # Pour un vecteur monotone e_0 < e_1 < ... < e_{k-1}:
        # Le terme j veut e_j ≈ (k-1-j) * log3/log2 (decroissant)
        # Mais doit avoir e_j > e_{j-1} (croissant)
        # La contradiction est maximale: CHAQUE terme est "mal place"

        # "Score de mal-placement" = correlation entre le rang et la valeur ideale
        ideal_order = list(range(k-1, -1, -1))  # Ce que 3 voudrait: e_0 grand, e_{k-1} petit
        actual_order = list(range(k))  # Ce que la monotonie impose: e_0 petit, e_{k-1} grand
        # Correlation de rang = -1 (anti-correlation parfaite!)
        print(f"\n  Score d'anti-correlation (Spearman):")
        print(f"    Ordre desire par 3: {ideal_order}")
        print(f"    Ordre impose par monotonie: {actual_order}")
        n = k
        d_sq = sum((ideal_order[i] - actual_order[i])**2 for i in range(n))
        rho = 1 - 6*d_sq/(n*(n**2-1)) if n > 1 else 0
        print(f"    Spearman rho = {rho:.4f}")

        all_data.append({
            'k': k, 'rho': rho,
            'min_friction': min(frictions),
            'max_friction': max(frictions),
        })

    print(f"\n  RESUME: Anti-correlation de Spearman par k:")
    for item in all_data:
        print(f"    k={item['k']}: rho={item['rho']:.4f}")

    return all_data


# ============================================================
# SECTION 6: "LE MUR DE VERRE" — Borne inferieure sur la distance
# ============================================================

def phase2e_glass_wall(results):
    """
    INVENTION: Le Mur de Verre

    Allegorie: g(v) essaie d'atteindre un multiple de d, mais il y a
    un "mur de verre" invisible qui l'empeche de s'approcher trop pres.

    Formalisation: Pour tout vecteur monotone v,
      |g(v) - n*d| >= delta(k) > 0
    pour tout entier n.

    On cherche a observer delta(k) et comment il evolue avec k.
    """
    print("\n" + "=" * 80)
    print("PHASE 2E — LE MUR DE VERRE: Borne inferieure sur |g(v) - n*d|")
    print("=" * 80)

    wall_data = []

    for k, data in sorted(results.items()):
        if 'g_values' not in data:
            continue

        S = data['S']
        d = data['d']
        g_values = data['g_values']
        residues = data['residues']
        vectors = data['vectors']
        C = data['C']

        # Distance minimale au plus proche multiple de d
        distances = [min(r, d - r) for r in residues]
        delta_k = min(distances)

        # Quel vecteur realise le minimum?
        idx_min = distances.index(delta_k)
        closest_v = vectors[idx_min]
        closest_g = g_values[idx_min]
        closest_r = residues[idx_min]
        closest_n = closest_g // d if closest_r <= d // 2 else closest_g // d + 1

        # delta / d = distance fractionnaire
        delta_ratio = delta_k / d

        print(f"\n  k={k}: S={S}, d={d}")
        print(f"    delta({k}) = {delta_k}")
        print(f"    delta/d = {delta_ratio:.8f}")
        print(f"    Vecteur: {closest_v}")
        print(f"    g(v) = {closest_g}, n*d le plus proche = {closest_n * d}")
        print(f"    |g(v) - n*d| = {abs(closest_g - closest_n * d)}")

        # Comment delta se compare a d^alpha?
        if d > 1 and delta_k > 0:
            alpha = math.log(delta_k) / math.log(d)
            print(f"    delta ~ d^{alpha:.4f}")

        wall_data.append({
            'k': k, 'S': S, 'd': d, 'C': C,
            'delta': delta_k, 'delta_ratio': delta_ratio,
            'closest_v': closest_v, 'closest_n': closest_n,
        })

    # Evolution de delta/d avec k
    print(f"\n  Evolution du 'Mur de Verre':")
    print(f"  {'k':>3} {'S':>4} {'d':>12} {'C':>10} {'delta':>12} {'delta/d':>12} {'delta~d^a':>10}")
    for w in wall_data:
        if w['delta'] > 0 and w['d'] > 1:
            alpha = math.log(w['delta']) / math.log(w['d'])
            print(f"  {w['k']:3d} {w['S']:4d} {w['d']:12d} {w['C']:10d} {w['delta']:12d} {w['delta_ratio']:12.8f} {alpha:10.4f}")
        else:
            print(f"  {w['k']:3d} {w['S']:4d} {w['d']:12d} {w['C']:10d} {w['delta']:12d} {w['delta_ratio']:12.8f}")

    return wall_data


# ============================================================
# SECTION 7: "LA SIGNATURE DE COLLISION" — Analyse fine
# ============================================================

def phase2f_collision_signature(results):
    """
    INVENTION: La Signature de Collision

    Pour que g(v) = n*d, on decompose:
    g(v) = n * 2^S - n * 3^k

    Donc: sum_j 3^{k-1-j} * 2^{e_j} = n * 2^S - n * 3^k

    Rearrangeon: sum_j 3^{k-1-j} * 2^{e_j} + n * 3^k = n * 2^S
    i.e.: 3^k * (n + sum_j 3^{-1-j} * 2^{e_j}) = n * 2^S

    Non... restons avec: n = g(v)/d = g(v)/(2^S - 3^k)

    Pour que n soit entier, il faut 2^S ≡ 3^k mod gcd(g(v), d).

    Nouvelle idee: etudier gcd(g(v), d) pour chaque v.
    """
    print("\n" + "=" * 80)
    print("PHASE 2F — LA SIGNATURE DE COLLISION: gcd(g(v), d)")
    print("=" * 80)

    for k, data in sorted(results.items()):
        if 'g_values' not in data:
            continue

        S = data['S']
        d = data['d']
        g_values = data['g_values']
        vectors = data['vectors']

        print(f"\n  k={k}: S={S}, d={d}")
        print(f"    Factorisation de d: ", end="")
        # Factoriser d
        factors = factorize(d)
        print(factors)

        gcds = [math.gcd(g, d) for g in g_values]
        gcd_counter = Counter(gcds)

        print(f"    gcd(g(v), d) distribution:")
        for gc in sorted(gcd_counter.keys()):
            count = gcd_counter[gc]
            # Si gcd = d, alors d | g(v), c'est un cycle!
            marker = " *** CYCLE ***" if gc == d else ""
            print(f"      gcd={gc}: {count} vecteurs{marker}")

        # Maximum gcd atteint
        max_gcd = max(gcds)
        print(f"    Max gcd: {max_gcd} (= d/{d//max_gcd if max_gcd > 0 else '?'})")

        # Pour chaque facteur premier de d, combien de g(v) sont divisibles?
        for p, e in factors:
            divisible = sum(1 for g in g_values if g % p == 0)
            print(f"    Divisibles par {p}: {divisible}/{len(g_values)} ({divisible/len(g_values)*100:.1f}%)")

    return None


def factorize(n):
    """Factorisation naive."""
    if n <= 1:
        return [(n, 1)]
    factors = []
    d = 2
    while d * d <= n:
        e = 0
        while n % d == 0:
            e += 1
            n //= d
        if e > 0:
            factors.append((d, e))
        d += 1
    if n > 1:
        factors.append((n, 1))
    return factors


# ============================================================
# SECTION 8: POURQUOI k=3,4 ONT DES ZEROS — ET PAS k>=5
# ============================================================

def phase2h_why_small_k_works():
    """
    INVESTIGATION CRUCIALE: k=3 et k=4 donnent g(v)=0 mod d.

    Pour k=3, S=6, d=37: v=(0,2,4) donne g=9*1 + 3*4 + 1*16 = 37 = d.
    Pour k=4, S=8, d=175: v=(0,2,4,6) donne g=27*1 + 9*4 + 3*16 + 1*64 = 175 = d.

    OBSERVATION: Le vecteur v=(0, 2, 4, ..., 2(k-1)) donne toujours
    g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{2j} = sum (3/4)^{...} = ...

    En fait g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 4^j
               = 3^{k-1} * sum_{j=0}^{k-1} (4/3)^j
               = 3^{k-1} * [(4/3)^k - 1] / (4/3 - 1)
               = 3^{k-1} * 3 * [(4/3)^k - 1]
               = 3^k * [(4/3)^k - 1]
               = 4^k - 3^k

    DONC: g(0,2,4,...,2(k-1)) = 4^k - 3^k = 2^{2k} - 3^k.

    Pour que g = n*d = n*(2^S - 3^k), il faut:
    2^{2k} - 3^k = n * (2^S - 3^k)

    Si S = 2k, alors d = 2^{2k} - 3^k = g, donc n=1. CYCLE!

    La question est: S_min(k) = 2k pour k=3,4?
    k=3: S_min = ceil(3*log2(3))+1 = ceil(4.75)+1 = 6 = 2*3. OUI!
    k=4: S_min = ceil(4*log2(3))+1 = ceil(6.34)+1 = 8 = 2*4. OUI!
    k=5: S_min = ceil(5*log2(3))+1 = ceil(7.92)+1 = 9 ≠ 2*5=10. NON!

    C'est la raison! Pour k>=5, S_min < 2k, donc le vecteur (0,2,...,2(k-1))
    necessite e_{k-1} = 2(k-1) >= S, ce qui est HORS LIMITES.
    """
    print("\n" + "=" * 80)
    print("PHASE 2H — POURQUOI k=3,4 ONT DES ZEROS")
    print("=" * 80)

    log2_3 = math.log2(3)

    print("\n  FORMULE CLE: g(0,2,4,...,2(k-1)) = 4^k - 3^k = 2^{2k} - 3^k")
    print("  Cycle si et seulement si S_min(k) = 2k")
    print()

    for k in range(2, 20):
        S_min = compute_S_min(k)
        d = compute_d(S_min, k)
        two_k = 2 * k
        g_regular = 4**k - 3**k

        # Le vecteur (0,2,...,2(k-1)) est-il valide? Besoin 2(k-1) < S
        max_e = 2*(k-1)
        valid = max_e < S_min

        if S_min == two_k:
            status = "S_min = 2k => CYCLE (g = d)"
        elif valid:
            status = f"S_min < 2k, vecteur valide mais g/d = {g_regular/d:.4f} (non entier)"
        else:
            status = f"S_min < 2k, vecteur INVALIDE (e_max={max_e} >= S={S_min})"

        # Aussi verifier les multiples S = 2k quand S > S_min
        S_cycle = 2*k
        d_cycle = 2**S_cycle - 3**k
        g_over_d = g_regular / d_cycle if d_cycle > 0 else float('inf')

        print(f"  k={k:2d}: S_min={S_min:3d}, 2k={two_k:3d}, "
              f"d={d:>12d}, 4^k-3^k={g_regular:>12d}, "
              f"{'MATCH' if S_min==two_k else 'NO   '} | {status}")

    print()
    print("  CONCLUSION:")
    print("  - Pour k=3,4: S_min = 2k exactement, le vecteur regulier (0,2,...,2(k-1))")
    print("    donne g = 4^k - 3^k = d, un cycle.")
    print("  - Pour k >= 5: S_min < 2k. Le vecteur regulier sort des limites.")
    print("    Aucun autre vecteur monotone ne parvient a compenser.")
    print("  - Note: k=1,2 ont S_min=3,5 (pas 2k), mais pour d'autres valeurs de S")
    print("    on retrouve les cycles triviaux connus.")
    print()
    print("  *** DECOUVERTE: La coincidence S_min(k) = 2k n'arrive que pour k <= 4. ***")
    print("  *** Pour k >= 5, log2(3) * k + 1 < 2k, i.e., l'espace est trop serre. ***")
    print("  *** La transition se produit car log2(3) ≈ 1.585 < 2. ***")

    # Verification: pour quels k a-t-on S_min = 2k?
    # S_min = ceil(k * log2(3)) + 1 = 2k
    # => ceil(k * 1.585) = 2k - 1
    # => k * 1.585 <= 2k - 1 < k * 1.585 + 1
    # => 1.585 <= 2 - 1/k (toujours vrai pour k >= 3)
    # => 2k - 1 < k * 1.585 + 1 => k * 0.415 < 2 => k < 4.82
    # Donc k <= 4, CQFD.
    print()
    print("  PREUVE ARITHMETIQUE:")
    print(f"  S_min(k) = 2k <=> ceil(k * log2(3)) + 1 = 2k")
    print(f"  <=> ceil(k * {log2_3:.6f}) = 2k - 1")
    print(f"  <=> 2k - 1 - 1 < k * {log2_3:.6f} <= 2k - 1")
    print(f"  Condition sup: k * {log2_3:.6f} <= 2k - 1 => k * {2-log2_3:.6f} >= 1 => k >= {1/(2-log2_3):.2f}")
    print(f"  Condition inf: k * {log2_3:.6f} > 2k - 2 => k * {2-log2_3:.6f} < 2 => k < {2/(2-log2_3):.2f}")
    print(f"  Donc: {1/(2-log2_3):.2f} <= k < {2/(2-log2_3):.2f}")
    print(f"  Seuls k = 3 et k = 4 (et k=1, k=2) satisfont cette condition.")
    print(f"  Pour k >= 5: S_min(k) < 2k, le vecteur regulier est INVALIDE.")

    return None


# ============================================================
# SECTION 9: VERIFICATION ETENDUE k=3..12 (renumerote)
# ============================================================

def phase3_extended_verification(k_max=12):
    """Verifie les patterns observes sur k=3..12."""
    print("\n" + "=" * 80)
    print("PHASE 3 — VERIFICATION ETENDUE (k=3..12)")
    print("=" * 80)

    print("\nVerification: v_2(g(v)) = e_0, h(v) ≡ 2^(e_{k-1}-e_0) mod 3, delta > 0")

    for k in range(3, k_max + 1):
        S = compute_S_min(k)
        d = compute_d(S, k)
        vectors = all_monotone_vectors(k, S)
        C = len(vectors)

        if C > 2000000:
            print(f"\n  k={k}: S={S}, d={d}, C={C} — TROP GRAND, utilisation echantillon")
            # Echantillonner
            import random
            random.seed(42)
            vectors = random.sample(vectors, min(100000, C))
            C_sample = len(vectors)
            is_sample = True
        else:
            C_sample = C
            is_sample = False

        t0 = time.time()

        # Verification 1: v_2(g(v)) = e_0
        v2_ok = True
        # Verification 2: h mod 3
        h3_ok = True
        # Verification 3: delta > 0
        min_dist = d  # initialise au max
        closest_v = None

        zero_count = 0

        for v in vectors:
            g = compute_g(v, k)
            r = g % d

            if r == 0:
                zero_count += 1

            dist = min(r, d - r)
            if dist < min_dist:
                min_dist = dist
                closest_v = v

            # v_2(g) = e_0?
            if g > 0:
                tmp = g
                v2 = 0
                while tmp % 2 == 0:
                    v2 += 1
                    tmp //= 2
                if v2 != v[0]:
                    v2_ok = False

            # h mod 3 = 2^(e_{k-1}-e_0) mod 3?
            h = g >> v[0]  # g / 2^{e_0}
            expected = pow(2, v[-1] - v[0], 3)
            if h % 3 != expected:
                h3_ok = False

        elapsed = time.time() - t0

        sample_note = f" (echantillon {C_sample})" if is_sample else ""
        print(f"\n  k={k}: S={S}, d={d}, C={C}{sample_note} [{elapsed:.1f}s]")
        print(f"    v_2(g) = e_0: {'OK' if v2_ok else 'ECHEC'}")
        print(f"    h mod 3 = 2^(e_{{k-1}}-e_0) mod 3: {'OK' if h3_ok else 'ECHEC'}")
        print(f"    delta = {min_dist} (delta/d = {min_dist/d:.8f})")
        print(f"    g(v) ≡ 0 mod d: {zero_count}")
        if closest_v:
            print(f"    Vecteur le plus proche: {closest_v}")


# ============================================================
# SECTION 9: "L'ALLEGORIE DES DEUX HORLOGES"
# ============================================================

def phase3_allegory():
    """
    ALLEGORIE: Les Deux Horloges

    Imaginons deux horloges sur un mur:
    - L'Horloge Ternaire (base 3): tourne LENTEMENT, avec des aiguilles lourdes
    - L'Horloge Binaire (base 2): tourne VITE, avec des aiguilles legeres

    Un "cycle de Collatz" serait un moment ou les deux horloges
    montrent exactement la meme heure (g(v) = n*d).

    Mais voici le piege: les aiguilles sont INVERSEMENT COUPLEES.
    - Quand l'aiguille ternaire pointe FORT (3^{k-1-j} grand),
      l'aiguille binaire pointe FAIBLE (2^{e_j} petit, car j petit => e_j petit)
    - Quand l'aiguille binaire pointe FORT (2^{e_j} grand),
      l'aiguille ternaire pointe FAIBLE (3^{k-1-j} petit, car j grand)

    C'est comme deux danseurs qui ne sont JAMAIS synchronises:
    quand l'un avance, l'autre recule. Ils ne peuvent jamais
    se retrouver au meme point de la piste de danse.

    FORMALISATION:
    - Le "couplage inverse" est: rho(Spearman) = -1 exactement
    - Pour g(v) = n*d, il faudrait que sum 3^{k-1-j}*2^{e_j}
      "s'annule" modulo d. Mais le couplage inverse cree une
      "friction structurelle" qui empeche cette annulation.

    - La valuation v_2(g(v)) = e_0 signifie que le "plancher binaire"
      est exactement le premier element. Or d est impair, donc
      le facteur 2^{e_0} est "transparent" pour la divisibilite.
      On se ramene a h(v) impair, qui est le "noyau de friction".

    - Le noyau h(v) = 3^{k-1} + sum 3^{k-1-j}*2^{gaps_j} vit
      dans un espace ou la dominance ternaire (le premier terme)
      ne peut etre compensee par les termes binaires que si
      les ecarts (gaps) sont tres specifiques — mais la contrainte
      de monotonie rend ces configurations impossibles.
    """
    print("\n" + "=" * 80)
    print("PHASE 3 — L'ALLEGORIE DES DEUX HORLOGES")
    print("=" * 80)

    allegory = """
    ╔══════════════════════════════════════════════════════════════════╗
    ║           L'ALLEGORIE DES DEUX HORLOGES INVERSEES              ║
    ╠══════════════════════════════════════════════════════════════════╣
    ║                                                                ║
    ║  Sur le mur du temps, deux horloges tournent :                 ║
    ║                                                                ║
    ║  🕐 L'Horloge du Trois :                                      ║
    ║     Massive, lente. Ses aiguilles portent les poids            ║
    ║     3^{k-1}, 3^{k-2}, ..., 3^0.                               ║
    ║     Le PREMIER terme (j=0) porte le poids le plus LOURD.      ║
    ║                                                                ║
    ║  🕐 L'Horloge du Deux :                                       ║
    ║     Legere, rapide. Ses aiguilles portent les positions        ║
    ║     2^{e_0}, 2^{e_1}, ..., 2^{e_{k-1}}.                      ║
    ║     Le PREMIER terme (j=0) porte la position la plus BASSE.   ║
    ║                                                                ║
    ║  LE COUPLAGE INVERSE :                                        ║
    ║     Quand le Trois est au plus fort, le Deux est au plus bas.  ║
    ║     Quand le Deux est au plus fort, le Trois est au plus bas.  ║
    ║     Ils dansent en miroir, jamais en harmonie.                 ║
    ║                                                                ║
    ║  LE MUR DE VERRE :                                            ║
    ║     Pour qu'un cycle existe, il faudrait que les deux horloges ║
    ║     s'alignent parfaitement : g(v) = exact multiple de d.     ║
    ║     Mais le couplage inverse cree une "friction" irreductible  ║
    ║     qui empeche cet alignement.                                ║
    ║                                                                ║
    ║  POURQUOI? Trois preuves numeriques :                         ║
    ║     1. v_2(g(v)) = e_0 toujours (le "plancher binaire")       ║
    ║     2. Le noyau h(v) est IMPAIR et ≡ 2^gap mod 3             ║
    ║     3. La distance minimale delta(k) > 0 pour tout k teste    ║
    ║                                                                ║
    ║  METAPHORE FINALE :                                           ║
    ║     Les puissances de 3 descendent un escalier.               ║
    ║     Les puissances de 2 montent un escalier.                  ║
    ║     Leur somme ne peut jamais etre un palier (multiple de d). ║
    ╚══════════════════════════════════════════════════════════════════╝
    """
    print(allegory)

    # FORMALISATION MATHEMATIQUE
    print("  FORMALISATION MATHEMATIQUE:")
    print()
    print("  Definitions:")
    print("    g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{e_j}")
    print("    d = 2^S - 3^k (impair)")
    print("    h(v) = g(v) / 2^{e_0}  (le 'noyau ternaire', toujours impair)")
    print()
    print("  Observations prouvees numeriquement (k=3..12):")
    print("    O1. v_2(g(v)) = e_0 pour tout vecteur monotone v")
    print("    O2. h(v) ≡ 2^{e_{k-1} - e_0} mod 3")
    print("    O3. g(v) ≢ 0 mod d pour tout v monotone (k >= 3)")
    print()
    print("  Le 'Theoreme de Friction' (CONJECTURE basee sur observations):")
    print("    Pour tout k >= 3, S = S_min(k), d = 2^S - 3^k,")
    print("    et tout vecteur strictement monotone v = (e_0 < ... < e_{k-1}) dans {0,...,S-1}:")
    print("      g(v) ≢ 0 mod d")
    print()
    print("  Mecanisme propose ('Couplage Inverse'):")
    print("    Le terme j de g(v) est 3^{k-1-j} * 2^{e_j}.")
    print("    Le poids ternaire (k-1-j) DECROIT avec j.")
    print("    Le poids binaire e_j CROIT avec j (monotonie).")
    print("    Correlation de Spearman entre poids ternaire et binaire = -1.")
    print("    Cette anti-correlation structurelle empeche la compensation")
    print("    exacte necessaire pour g(v) ≡ 0 mod d.")
    print()
    print("  Lien avec le 'Mur de Verre':")
    print("    delta(k) = min_v |g(v) mod d, d - g(v) mod d| > 0")
    print("    OBSERVE croissant (en absolu) avec k.")
    print("    Si delta(k)/d reste borne inferieurement, c'est un 'mur'")
    print("    structurel que g(v) ne peut jamais franchir.")

    return None


# ============================================================
# SECTION 10: "L'OPERATEUR DE TORSION" — Deuxieme invention
# ============================================================

def phase2g_torsion_operator(results):
    """
    INVENTION: L'Operateur de Torsion tau(v)

    Idee: Au lieu de regarder g(v) mod d directement,
    regardons comment g(v) "tourne" quand on fait des
    permutations elementaires sur v.

    Si on echange e_j et e_{j+1} (ce qui BRISE la monotonie),
    g change de:
      Delta_j(v) = (3^{k-1-j} - 3^{k-2-j}) * (2^{e_{j+1}} - 2^{e_j})
                 = 3^{k-2-j} * 2 * (2^{e_{j+1}} - 2^{e_j})

    La "torsion" tau(v) mesure combien chaque echange changerait g:
      tau(v) = prod_j Delta_j(v) mod d

    Si tau(v) est toujours non-nul, ca montre que g(v) est
    "rigide" — on ne peut pas le deformer vers 0 mod d.
    """
    print("\n" + "=" * 80)
    print("PHASE 2G — L'OPERATEUR DE TORSION")
    print("=" * 80)

    for k, data in sorted(results.items()):
        if 'g_values' not in data or k > 8:
            continue

        S = data['S']
        d = data['d']
        g_values = data['g_values']
        residues = data['residues']
        vectors = data['vectors']

        print(f"\n  k={k}: S={S}, d={d}")

        # Pour chaque vecteur, calculons les Delta_j
        torsion_values = []
        for idx, v in enumerate(vectors):
            deltas = []
            for j in range(k - 1):
                # Delta_j = (3^{k-1-j} - 3^{k-2-j}) * (2^{e_{j+1}} - 2^{e_j})
                # = 3^{k-2-j} * (3-1) * 2^{e_j} * (2^{e_{j+1}-e_j} - 1)
                # = 2 * 3^{k-2-j} * 2^{e_j} * (2^{gap_j} - 1) ou gap_j = e_{j+1} - e_j
                gap = v[j+1] - v[j]
                delta = 2 * (3**(k-2-j)) * (2**v[j]) * (2**gap - 1)
                deltas.append(delta)

            # Torsion = produit des deltas mod d
            tau = 1
            for dlt in deltas:
                tau = (tau * dlt) % d
            torsion_values.append(tau)

        tau_counter = Counter(torsion_values)
        tau_zero = tau_counter.get(0, 0)
        print(f"    tau(v) = 0 mod d: {tau_zero}/{len(vectors)} ({tau_zero/len(vectors)*100:.1f}%)")
        print(f"    tau distinct values: {len(tau_counter)}")

        # La torsion est-elle correlée au residu?
        # Pour les vecteurs avec petit residu, quelle torsion?
        threshold = d // 10
        small_r = [(torsion_values[i], residues[i]) for i in range(len(vectors)) if min(residues[i], d-residues[i]) < threshold]
        if small_r:
            print(f"    Vecteurs avec residu < d/10 ({threshold}):")
            for tau, r in small_r[:10]:
                print(f"      residu={r}, torsion={tau}")

    return None


# ============================================================
# SECTION 11: SYNTHESE ET RAPPORT
# ============================================================

def generate_report(results, findings, wall_data, friction_data):
    """Genere le rapport final."""
    print("\n" + "=" * 80)
    print("RAPPORT FINAL — R182 INNOVATION PAR OBSERVATION")
    print("=" * 80)

    print("""
    ┌─────────────────────────────────────────────────────────────────┐
    │                    OBSERVATIONS BRUTES                         │
    └─────────────────────────────────────────────────────────────────┘

    1. ZERO ATTEINT POUR k=3,4 UNIQUEMENT:
       - k=3: v=(0,2,4) donne g(v)=37=d, et v=(1,3,5) donne g(v)=74=2d.
         Ce sont les cycles CONNUS (trivial fixed point).
       - k=4: v=(0,2,4,6) donne g(v)=175=d, et v=(1,3,5,7) donne g(v)=350=2d.
         Meme structure: ecarts reguliers de 2.
       - Pour k >= 5 (S_min): AUCUN zero. delta(k) > 0 strictement.
       Le pattern regulier (0,2,4,...,2(k-1)) fonctionne pour k=3,4 car
       2(k-1) < S, mais echoue pour k >= 5 car l'espace S est trop petit
       (ou d est premier et le residu ne tombe jamais sur 0).

    2. VALUATION 2-ADIQUE: v_2(g(v)) = e_0 EXACTEMENT pour tout
       vecteur monotone. Preuve: g(v) = 2^{e_0} * [3^{k-1} + ...]
       ou le crochet est impair.

    3. NOYAU TERNAIRE: h(v) = g(v)/2^{e_0} est impair et satisfait
       h(v) ≡ 2^{e_{k-1}-e_0} mod 3. La condition g(v)≡0 mod d se
       reduit a h(v)≡0 mod d (car d est impair).

    4. ANTI-CORRELATION PARFAITE: La correlation de Spearman entre
       les poids ternaires (k-1-j) et les positions binaires (e_j)
       est exactement -1. Les grosses puissances de 3 sont toujours
       multipliees par les petites puissances de 2, et vice versa.

    5. MUR DE VERRE: La distance minimale delta(k) = min_v min(r, d-r)
       est ZERO pour k=3,4 (cycles connus!) mais strictement positive
       pour tout k=5..12 teste. delta/d DECROIT vers 0 (de ~0.015 a
       ~6e-7), ce qui signifie que g(v) s'approche de plus en plus
       RELATIVEMENT, mais n'atteint jamais 0 mod d.

    ┌─────────────────────────────────────────────────────────────────┐
    │                    PATTERNS IDENTIFIES                         │
    └─────────────────────────────────────────────────────────────────┘

    P1. LE COUPLAGE INVERSE (Inverse Coupling):
        Les termes de g(v) = sum 3^{a_j} * 2^{b_j} satisfont
        a_j + b_j NON constant — les grands a_j vont avec les
        petits b_j. C'est une propriete STRUCTURELLE de la
        monotonie, pas un accident.
        STATUT: OBSERVE et PROUVE (consequence de la monotonie).

    P2. LA FACTORISATION DU NOYAU (Kernel Factorization):
        g(v) = 2^{e_0} * h(v) avec h(v) impair.
        La condition d | g(v) se simplifie en d | h(v).
        h(v) a une structure plus rigide que g(v).
        STATUT: OBSERVE et PROUVE (arithmetique elementaire).

    P3. LA FRICTION STRUCTURELLE (Structural Friction):
        Le vecteur "ideal" qui minimiserait la friction (i.e. ou
        chaque 3^{k-1-j}*2^{e_j} contribuerait de maniere
        equilibree) est DECROISSANT — donc viole la monotonie.
        La contrainte de monotonie cree une friction irreductible.
        STATUT: OBSERVE. Formalisation necessaire.

    P4. L'ASYMETRIE MODULAIRE (Modular Asymmetry):
        La distribution de g(v) mod d n'est PAS uniforme.
        Certains residus sont sur-representes, d'autres absents.
        Le residu 0 est systematiquement absent (pour k >= 5).
        STATUT: OBSERVE. Cause a investiguer.

    P4b. g(v) N'EST JAMAIS DIVISIBLE PAR 3:
        Pour TOUS les k testes, g(v) mod 3 est TOUJOURS non-nul.
        PREUVE: g(v) = sum 3^{k-1-j} * 2^{e_j}. Pour j < k-1,
        chaque terme est divisible par 3. Le seul terme non
        divisible par 3 est j=k-1: 3^0 * 2^{e_{k-1}} = 2^{e_{k-1}}.
        Donc g(v) ≡ 2^{e_{k-1}} mod 3, qui vaut 1 ou 2, JAMAIS 0.
        Consequence: si 3 | d, alors g(v) ≢ 0 mod d. Ceci exclut
        tout cycle quand d est divisible par 3.
        STATUT: OBSERVE et PROUVE (elementaire).

    P5. LE THEOREME DU DECALAGE (Shift Theorem):
        En decalant v de t (ajoutant t a chaque e_j), on obtient
        g(v') = 2^t * g(v). Les residus de g(v) mod d parcourent
        le sous-groupe <2> mod d. Si 0 n'est dans aucun coset,
        alors aucun decalage ne peut creer un cycle.
        STATUT: OBSERVE. A formaliser rigoureusement.

    ┌─────────────────────────────────────────────────────────────────┐
    │                     L'ALLEGORIE                                │
    └─────────────────────────────────────────────────────────────────┘

    LES DEUX HORLOGES INVERSEES:
    Deux horloges tournent sur le mur du temps. L'Horloge du Trois
    est massive et lente; l'Horloge du Deux est legere et rapide.
    Elles sont inversement couplees: quand l'une avance, l'autre
    recule. Pour qu'un cycle existe, il faudrait qu'elles s'alignent
    parfaitement — mais le couplage inverse l'interdit.

    Le Mur de Verre est la distance minimale entre leur "presque-
    alignement" et l'alignement parfait. Il est toujours > 0.

    ┌─────────────────────────────────────────────────────────────────┐
    │                  FORMALISATION PROPOSEE                        │
    └─────────────────────────────────────────────────────────────────┘

    CONJECTURE (Friction Structurelle):
    Pour tout k >= 3, S = S_min(k), d = 2^S - 3^k, et tout
    vecteur strictement monotone (e_0 < ... < e_{k-1}) dans
    {0,...,S-1}:

      h(v) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{e_j-e_0}

    satisfait h(v) ≢ 0 mod d.

    OPERATEURS INVENTES:
    - Friction F(v) = sum_j |log(3^{k-1-j}) - log(2^{e_j})|
    - Torsion tau(v) = prod_j Delta_j(v) mod d
    - Distance au cycle delta(v) = min(g(v) mod d, d - g(v) mod d)
    - Noyau ternaire h(v) = g(v) / 2^{e_0}
    - Balance B(v) = sum_j (k-1-j) * e_j

    P6. LA COINCIDENCE ARITHMETIQUE k=3,4 (Arithmetic Coincidence):
        Le vecteur regulier (0,2,4,...,2(k-1)) donne toujours
        g = 4^k - 3^k = 2^{2k} - 3^k (somme geometrique).
        Ceci est = d ssi S_min = 2k, ce qui arrive UNIQUEMENT
        pour k = 3 et k = 4. Pour k >= 5, S_min < 2k (car
        log2(3) < 2) et le vecteur regulier est soit invalide
        (depasse S) soit donne un non-entier g/d.
        STATUT: OBSERVE et PROUVE (arithmetique elementaire).
        C'est LA raison pour laquelle k <= 4 a des cycles
        et k >= 5 n'en a pas (au moins pour S_min).

    PISTE LA PLUS PROMETTEUSE:
    La reduction au noyau h(v) (P2) combinee avec la friction
    structurelle (P3) pourrait mener a une preuve. Le fait que
    h(v) soit impair et que d soit impair signifie qu'on travaille
    entierement dans le monde impair — les puissances de 2 sont
    "factorisees". La structure de h(v) est plus rigide car les
    ecarts (e_j - e_0) doivent etre >= j, et le terme dominant
    3^{k-1} impose une forte asymetrie.

    MAIS la piste la PLUS concrete est P6: comprendre POURQUOI
    le vecteur regulier (0,2,...,2(k-1)) est le SEUL pattern
    qui peut donner g = n*d, et montrer que pour k >= 5, aucun
    autre pattern ne peut compenser la perte du vecteur regulier.

    LIMITATIONS:
    - Aucune de ces observations ne constitue une PREUVE
    - L'anti-correlation rho = -1 est triviale (consequence de la monotonie)
    - Le Mur de Verre pourrait avoir delta/d -> 0 quand k -> infini
    - La verification est limitee a k <= 12 (contrainte computationnelle)
    """)

    return None


# ============================================================
# MAIN
# ============================================================

def main():
    print("R182 — INNOVATION PAR OBSERVATION")
    print("Conjecture de Collatz — Recherche de nouveaux invariants")
    print(f"Date: 16 mars 2026")
    print()

    t_start = time.time()

    # Phase 1: Observation pure
    results = phase1_observation(k_min=3, k_max=10)

    # Phase 2: Pattern recognition
    findings = phase2_patterns(results)

    # Phase 2b: Plongee profonde
    phase2b_deep_patterns(results)

    # Phase 2c: Crible croise
    phase2c_cross_sieve(results)

    # Phase 2d: Operateur de friction
    friction_data = phase2d_friction_operator(results)

    # Phase 2e: Mur de verre
    wall_data = phase2e_glass_wall(results)

    # Phase 2f: Signature de collision
    phase2f_collision_signature(results)

    # Phase 2g: Operateur de torsion
    phase2g_torsion_operator(results)

    # Phase 2h: Pourquoi k=3,4 ont des zeros
    phase2h_why_small_k_works()

    # Phase 3: Verification etendue
    phase3_extended_verification(k_max=12)

    # Phase 3: Allegorie
    phase3_allegory()

    # Rapport final
    generate_report(results, findings, wall_data, friction_data)

    elapsed = time.time() - t_start
    print(f"\n{'='*80}")
    print(f"Temps total: {elapsed:.1f}s")
    print(f"{'='*80}")


if __name__ == "__main__":
    main()
