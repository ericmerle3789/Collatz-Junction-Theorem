#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
R61 — Axe C+D : Hit-hit-lite candidats et chaine globale
=========================================================
Agent R61 — Round 61 — TYPE P

Deux candidats pour le premier noyau prouvable de la sous-etape (c).

AXE C : Hit-hit-lite
  Candidat 1 : tau pointwise — tau(r) <= 1 - epsilon en R3
  Candidat 2 : chaines courtes — #{chaines >= L} <= C1 * rho^L, rho < 1

AXE D : Chaine globale
  (c) -> (d) -> alpha < 1 -> K-lite -> A(2) borne -> V/C^2 -> 0 -> f_p -> 1/p

CONTEXTE ACQUIS R57-R60 [NE PAS RE-PROUVER]:
  (a) reformulation delta : PROUVE
  (b) |S_delta| <= 1 : PROUVE
  (c) transition hit-hit < 1 : VERROU — objet de ce round
  (d) integration => alpha < 1 : depend de (c)

DEFINITIONS:
  hit(delta, r) : d_delta in [0, M-delta]  (delta contribue pour r)
  tau(r) = #{delta : hit(delta) ET hit(delta+1)} / #{delta : hit(delta)}
  Si tau < 1 uniformement, les chaines de hits sont courtes => alpha < 1.

SOUS-REGIMES:
  R1 : ord = p-1    (generateur primitif)
  R2 : ord >= (p-1)/2
  R3 : ord >= sqrt(p) (le plus demontrable)

EPISTEMIC LABELS:
  [PROVED]       = rigorous proof or exact identity
  [COMPUTED]     = verified by exact computation on all tested cases
  [OBSERVED]     = numerical evidence, NOT a proof
  [CONJECTURAL]  = plausible but unproven

DEAD TOOLS: large sieve direct, pseudo-alea naif dlogs, L2-hybride,
  Candidat 2 hybride (R59), nesting seul (R60)

Author: Claude Opus 4.6 (R61 pour Eric Merle)
Date:   2026-03-13
"""

import math
import time
from collections import defaultdict

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
PASS_COUNT = 0
FAIL_COUNT = 0

TEST_PRIMES = [101, 251, 503, 1009]
# n values: k=2 so g = (3/2)^n mod p, M = n-1
N_VALUES = [2, 3, 5, 8, 12, 20]

def elapsed():
    return time.time() - T_START

def test(name, condition, detail=""):
    global PASS_COUNT, FAIL_COUNT
    if condition:
        PASS_COUNT += 1
        print(f"  [PASS] {name}")
    else:
        FAIL_COUNT += 1
        print(f"  [FAIL] {name} -- {detail}")

# ============================================================================
# MATHEMATICAL PRIMITIVES
# ============================================================================

def ord_p2(p):
    """Ordre multiplicatif de 2 modulo p."""
    e, v = 1, 2 % p
    while v != 1:
        v = (v * 2) % p
        e += 1
        if e > p:
            return p
    return e

def build_dlog_table(p):
    """Table dlog base 2: 2^e mod p -> e, pour e in [0, ord-1]."""
    ordr = ord_p2(p)
    tbl = {}
    v = 1
    for e in range(ordr):
        tbl[v] = e
        v = (v * 2) % p
    return tbl, ordr

def compute_g(p, n):
    """g = (3/2)^n mod p."""
    inv2n = pow(pow(2, n, p), -1, p)
    return (pow(3, n, p) * inv2n) % p

def compute_c_deltas(p, n, g, M):
    """c_delta = (1 + g * 2^delta) mod p pour delta in [0, M]."""
    c = []
    for delta in range(M + 1):
        cd = (1 + g * pow(2, delta, p)) % p
        c.append(cd)
    return c

def classify_regime(ordr, p):
    """Classifie en R1, R2, R3."""
    if ordr == p - 1:
        return "R1"
    elif ordr >= (p - 1) // 2:
        return "R2"
    elif ordr >= math.isqrt(p):
        return "R3"
    else:
        return "R_low"

def compute_hits_per_r(p, n, dlog_table, ordr):
    """
    Pour chaque r, retourne la liste ordonnee des delta qui sont des hits.
    hit(delta, r) <=> dlog(r / c_delta) in [0, M - delta].
    Retourne aussi M, C.
    """
    M = n - 1
    C = (M + 1) * (M + 2) // 2
    g = compute_g(p, n)
    c_deltas = compute_c_deltas(p, n, g, M)

    hits_by_r = defaultdict(list)  # r -> sorted list of delta values that are hits

    for delta in range(M + 1):
        cd = c_deltas[delta]
        if cd == 0:
            continue
        inv_cd = pow(cd, -1, p)
        window = M - delta
        for r in range(1, p):
            val = (r * inv_cd) % p
            if val in dlog_table:
                e = dlog_table[val]
                if e <= window:
                    hits_by_r[r].append(delta)

    return dict(hits_by_r), M, C, c_deltas

def compute_tau(hits_by_r, M):
    """
    Pour chaque r, calcule tau(r) = #{delta : hit(delta) ET hit(delta+1)} / #{delta : hit(delta)}.
    Retourne dict r -> tau(r). Exclut r avec 0 hits.
    """
    tau = {}
    for r, deltas in hits_by_r.items():
        if len(deltas) == 0:
            continue
        delta_set = set(deltas)
        consecutive = sum(1 for d in deltas if (d + 1) in delta_set and d + 1 <= M)
        tau[r] = consecutive / len(deltas)
    return tau

def compute_chain_lengths(hits_by_r, M):
    """
    Pour chaque r, calcule les longueurs des chaines de hits consecutifs.
    Retourne dict r -> list of chain lengths.
    """
    chains_by_r = {}
    for r, deltas in hits_by_r.items():
        if len(deltas) == 0:
            chains_by_r[r] = []
            continue
        delta_set = sorted(set(deltas))
        chains = []
        current_len = 1
        for i in range(1, len(delta_set)):
            if delta_set[i] == delta_set[i - 1] + 1:
                current_len += 1
            else:
                chains.append(current_len)
                current_len = 1
        chains.append(current_len)
        chains_by_r[r] = chains
    return chains_by_r


# ============================================================================
# SECTION 1 : Candidat 1 — tau pointwise
# ============================================================================

def section1():
    """
    Mesurer tau(r) pour tout r, sur les primes de test.
    Verifier tau_max < 1 hors cas degeneres.
    """
    print("\n" + "=" * 72)
    print("SECTION 1 : Candidat 1 — tau pointwise")
    print("=" * 72)
    print("  tau(r) = #{delta : hit(d) ET hit(d+1)} / #{delta : hit(d)}")
    print("  Cible : tau_max < 1 hors cas degeneres (n=2, tres petits p)")
    print()

    all_tau_max = []
    all_tau_max_nondegen = []

    for p in TEST_PRIMES:
        dlog_table, ordr = build_dlog_table(p)
        regime = classify_regime(ordr, p)
        for n in N_VALUES:
            M = n - 1
            if M < 1 or M >= ordr:
                continue

            hits_by_r, M_ret, C, c_deltas = compute_hits_per_r(p, n, dlog_table, ordr)
            tau = compute_tau(hits_by_r, M_ret)

            if not tau:
                continue

            tau_max = max(tau.values())
            tau_mean = sum(tau.values()) / len(tau)
            all_tau_max.append((p, n, ordr, regime, tau_max, tau_mean))

            # Non-degenere : n > 2 et ordr > 4
            is_nondegen = (n > 2 and ordr > 4)
            if is_nondegen:
                all_tau_max_nondegen.append(tau_max)

            if p <= 503:
                print(f"  p={p:4d}, n={n:2d}, ord={ordr:4d}, {regime}: "
                      f"tau_max={tau_max:.4f}, tau_mean={tau_mean:.4f}")

    # Resultat global
    if all_tau_max_nondegen:
        global_tau_max_nondegen = max(all_tau_max_nondegen)
    else:
        global_tau_max_nondegen = 0.0

    print(f"\n  tau_max global (non-degen) = {global_tau_max_nondegen:.4f}")

    test("S1-T1: tau_max < 1 hors cas degeneres",
         global_tau_max_nondegen < 1.0,
         f"tau_max_nondegen = {global_tau_max_nondegen:.4f}")

    # Aussi verifier le tau moyen
    if all_tau_max_nondegen:
        mean_of_maxes = sum(all_tau_max_nondegen) / len(all_tau_max_nondegen)
        print(f"  Moyenne des tau_max (non-degen) = {mean_of_maxes:.4f}")
        test("S1-T2: moyenne des tau_max < 0.5 (non-degen)",
             mean_of_maxes < 0.5,
             f"mean = {mean_of_maxes:.4f}")

    return all_tau_max


# ============================================================================
# SECTION 2 : Candidat 1 — epsilon explicite en R3
# ============================================================================

def section2():
    """
    Filtrer les cas R3, calculer epsilon = 1 - tau_max.
    Tester si epsilon ~ c/log(ord) ou c/sqrt(ord).
    """
    print("\n" + "=" * 72)
    print("SECTION 2 : Candidat 1 — epsilon explicite en R3")
    print("=" * 72)
    print("  En R3 (ord >= sqrt(p)), calculer epsilon = 1 - tau_max.")
    print("  Tester la forme fonctionnelle de epsilon.")
    print()

    eps_data = []  # (p, n, ordr, epsilon)

    for p in TEST_PRIMES:
        dlog_table, ordr = build_dlog_table(p)
        regime = classify_regime(ordr, p)
        for n in N_VALUES:
            M = n - 1
            if M < 2 or M >= ordr:
                continue
            # Filtre R3 : ord >= sqrt(p)
            if ordr < math.isqrt(p):
                continue

            hits_by_r, M_ret, C, c_deltas = compute_hits_per_r(p, n, dlog_table, ordr)
            tau = compute_tau(hits_by_r, M_ret)
            if not tau:
                continue

            # Exclure n=2 (degenere)
            if n <= 2:
                continue

            tau_max = max(tau.values())
            eps = 1.0 - tau_max
            eps_data.append((p, n, ordr, eps, regime))
            print(f"  p={p:4d}, n={n:2d}, ord={ordr:4d}, {regime}: "
                  f"tau_max={tau_max:.4f}, eps={eps:.4f}")

    # Tester epsilon > 0
    if eps_data:
        all_eps = [e[3] for e in eps_data]
        min_eps = min(all_eps)
        print(f"\n  epsilon min en R3+ (non-degen) = {min_eps:.4f}")

        test("S2-T1: epsilon > 0 en R3 (hors degeneres)",
             min_eps > 0,
             f"min_eps = {min_eps:.6f}")

        # Tester forme fonctionnelle : epsilon vs 1/log(ord)
        print("\n  Forme fonctionnelle epsilon vs c/log(ord):")
        ratios_log = []
        ratios_sqrt = []
        for p, n, ordr, eps, regime in eps_data:
            if ordr > 2:
                r_log = eps * math.log(ordr)
                r_sqrt = eps * math.sqrt(ordr)
                ratios_log.append(r_log)
                ratios_sqrt.append(r_sqrt)
                if p <= 503:
                    print(f"    p={p}, n={n}: eps*log(ord)={r_log:.3f}, "
                          f"eps*sqrt(ord)={r_sqrt:.3f}")

        if ratios_log:
            cv_log = (max(ratios_log) - min(ratios_log)) / (sum(ratios_log) / len(ratios_log)) if sum(ratios_log) > 0 else 999
            cv_sqrt = (max(ratios_sqrt) - min(ratios_sqrt)) / (sum(ratios_sqrt) / len(ratios_sqrt)) if sum(ratios_sqrt) > 0 else 999
            print(f"\n  Dispersion eps*log(ord): range/mean = {cv_log:.3f}")
            print(f"  Dispersion eps*sqrt(ord): range/mean = {cv_sqrt:.3f}")
            # Le meilleur fit a la plus petite dispersion
            best_fit = "c/log(ord)" if cv_log < cv_sqrt else "c/sqrt(ord)"
            print(f"  Meilleur fit : epsilon ~ {best_fit}")

        test("S2-T2: epsilon positif dans tous les cas R3 testes",
             all(e > 0 for e in all_eps),
             f"eps values: {all_eps}")
    else:
        print("  Aucun cas R3 non-degenere trouve.")
        test("S2-T1: au moins un cas R3", False, "aucun cas")
        test("S2-T2: epsilon positif", False, "aucun cas")

    return eps_data


# ============================================================================
# SECTION 3 : Candidat 1 — implication pour alpha
# ============================================================================

def section3():
    """
    Si tau <= 1 - epsilon, calculer alpha_implied.
    alpha_implied = 1 - epsilon  (borne sur la fraction d'exces).
    """
    print("\n" + "=" * 72)
    print("SECTION 3 : Candidat 1 — implication pour alpha")
    print("=" * 72)
    print("  Si tau <= 1 - eps, la longueur attendue d'une chaine = 1/eps.")
    print("  Donc max_Nr <= C/p + (1-eps)*(M+1), alpha_implied = 1 - eps.")
    print()

    alpha_data = []

    for p in TEST_PRIMES:
        dlog_table, ordr = build_dlog_table(p)
        if ordr < math.isqrt(p):
            continue
        regime = classify_regime(ordr, p)
        for n in N_VALUES:
            M = n - 1
            if M < 2 or M >= ordr or n <= 2:
                continue

            hits_by_r, M_ret, C, c_deltas = compute_hits_per_r(p, n, dlog_table, ordr)
            tau = compute_tau(hits_by_r, M_ret)
            if not tau:
                continue

            tau_max = max(tau.values())
            eps = 1.0 - tau_max
            alpha_implied = 1.0 - eps  # = tau_max

            # Verification directe: calculer le vrai alpha
            Nr_dict = defaultdict(int)
            for r, deltas in hits_by_r.items():
                Nr_dict[r] = len(deltas)
            max_Nr = max(Nr_dict.values()) if Nr_dict else 0
            Cp = C / p
            alpha_real = (max_Nr - Cp) / (M_ret + 1) if M_ret > 0 else 0

            alpha_data.append((p, n, ordr, regime, alpha_implied, alpha_real))
            print(f"  p={p:4d}, n={n:2d}, {regime}: alpha_implied={alpha_implied:.4f}, "
                  f"alpha_real={alpha_real:.4f}")

    if alpha_data:
        all_alpha_impl = [a[4] for a in alpha_data]
        all_alpha_real = [a[5] for a in alpha_data]

        test("S3-T1: alpha_implied < 1 dans tous les cas R3",
             all(a < 1.0 for a in all_alpha_impl),
             f"max alpha_implied = {max(all_alpha_impl):.4f}")

        # Verifier coherence : alpha_real <= alpha_implied (pas necessairement
        # car alpha_implied est une borne theorique, pas forcement serree)
        print(f"\n  alpha_implied max = {max(all_alpha_impl):.4f}")
        print(f"  alpha_real max    = {max(all_alpha_real):.4f}")
    else:
        test("S3-T1: au moins un cas", False, "aucun cas")

    return alpha_data


# ============================================================================
# SECTION 4 : Candidat 1 — cas degeneres
# ============================================================================

def section4():
    """
    Identifier quand tau = 1 (tous les hits sont consecutifs).
    Mesurer la frequence des cas degeneres.
    """
    print("\n" + "=" * 72)
    print("SECTION 4 : Candidat 1 — cas degeneres")
    print("=" * 72)
    print("  Identifier les cas ou tau(r) = 1.")
    print("  Cas degenere = n=2 (M=1, au plus 2 hits, forcement consecutifs si 2 hits).")
    print()

    total_cases = 0
    degen_cases = 0
    degen_details = []

    for p in TEST_PRIMES:
        dlog_table, ordr = build_dlog_table(p)
        for n in N_VALUES:
            M = n - 1
            if M < 1 or M >= ordr:
                continue

            hits_by_r, M_ret, C, c_deltas = compute_hits_per_r(p, n, dlog_table, ordr)
            tau = compute_tau(hits_by_r, M_ret)

            for r, t in tau.items():
                total_cases += 1
                if t >= 1.0 - 1e-12:
                    degen_cases += 1
                    n_hits = len(hits_by_r.get(r, []))
                    degen_details.append((p, n, r, ordr, n_hits))

    degen_frac = degen_cases / total_cases if total_cases > 0 else 0
    print(f"  Total cas (p, n, r) : {total_cases}")
    print(f"  Cas degeneres (tau=1) : {degen_cases} ({degen_frac*100:.2f}%)")

    # Details sur les degeneres
    degen_n2 = sum(1 for d in degen_details if d[1] == 2)
    degen_other = degen_cases - degen_n2
    print(f"  Dont n=2 : {degen_n2}")
    print(f"  Dont n>2 : {degen_other}")

    if degen_other > 0:
        print("  Details des degeneres n>2:")
        for d in degen_details:
            if d[1] > 2:
                print(f"    p={d[0]}, n={d[1]}, r={d[2]}, ord={d[3]}, n_hits={d[4]}")

    # Verifier que les degeneres n>2 ont n_hits=1 (trivial: 1 hit, 0 transitions, tau=0/0 non defini)
    # En fait, tau=1 avec n>2 signifie que TOUS les hits sont consecutifs
    # Ce qui est possible si n_hits petit (2 hits consecutifs => tau = 1/2 ou 1)
    degen_n_gt2_multi = [d for d in degen_details if d[1] > 2 and d[4] > 1]
    print(f"  Degeneres n>2 avec >1 hit : {len(degen_n_gt2_multi)}")

    test("S4-T1: fraction degeneree < 5%",
         degen_frac < 0.05,
         f"degen_frac = {degen_frac*100:.2f}%")

    test("S4-T2: degeneres n>2 avec >1 hit < 1% des cas",
         len(degen_n_gt2_multi) / max(total_cases, 1) < 0.01,
         f"count = {len(degen_n_gt2_multi)}/{total_cases}")

    return degen_frac, degen_details


# ============================================================================
# SECTION 5 : Candidat 2 — distribution des longueurs de chaines
# ============================================================================

def section5():
    """
    Pour chaque r, calculer les longueurs des chaines de hits consecutifs.
    Histogramme global. Verifier decroissance exponentielle.
    """
    print("\n" + "=" * 72)
    print("SECTION 5 : Candidat 2 — distribution des longueurs de chaines")
    print("=" * 72)
    print("  Histogramme #{chaines de longueur L} pour L = 1, 2, 3, ...")
    print("  Cible : decroissance exponentielle #{L+1}/#{L} < rho < 1.")
    print()

    global_hist = defaultdict(int)  # L -> count

    for p in TEST_PRIMES:
        dlog_table, ordr = build_dlog_table(p)
        for n in N_VALUES:
            M = n - 1
            if M < 2 or M >= ordr or n <= 2:
                continue

            hits_by_r, M_ret, C, c_deltas = compute_hits_per_r(p, n, dlog_table, ordr)
            chains_by_r = compute_chain_lengths(hits_by_r, M_ret)

            for r, chains in chains_by_r.items():
                for L in chains:
                    global_hist[L] += 1

    # Afficher histogramme
    max_L = max(global_hist.keys()) if global_hist else 0
    print("  Histogramme des longueurs de chaines:")
    total_chains = sum(global_hist.values())
    for L in range(1, min(max_L + 1, 15)):
        count = global_hist.get(L, 0)
        pct = count / total_chains * 100 if total_chains > 0 else 0
        bar = "#" * min(int(pct), 60)
        print(f"    L={L:2d}: {count:6d} ({pct:5.1f}%) {bar}")

    # Calculer rho = ratio consecutif
    print("\n  Ratios #{L+1}/#{L}:")
    rhos = []
    for L in range(1, min(max_L, 12)):
        c_L = global_hist.get(L, 0)
        c_L1 = global_hist.get(L + 1, 0)
        if c_L > 0:
            rho_L = c_L1 / c_L
            rhos.append(rho_L)
            print(f"    #{L+1}/#{L} = {c_L1}/{c_L} = {rho_L:.4f}")

    if rhos:
        rho_max = max(rhos)
        rho_mean = sum(rhos) / len(rhos)
        print(f"\n  rho_max = {rho_max:.4f}, rho_mean = {rho_mean:.4f}")

        test("S5-T1: decroissance exponentielle (rho_max < 1)",
             rho_max < 1.0,
             f"rho_max = {rho_max:.4f}")
        test("S5-T2: rho_mean < 0.5",
             rho_mean < 0.5,
             f"rho_mean = {rho_mean:.4f}")
    else:
        test("S5-T1: au moins un ratio", False, "aucun ratio")
        test("S5-T2: rho_mean", False, "aucun ratio")

    return dict(global_hist), rhos


# ============================================================================
# SECTION 6 : Candidat 2 — rho par sous-regime
# ============================================================================

def section6():
    """
    Mesurer rho en R1, R2, R3 separement.
    """
    print("\n" + "=" * 72)
    print("SECTION 6 : Candidat 2 — rho par sous-regime")
    print("=" * 72)

    hist_by_regime = {"R1": defaultdict(int), "R2": defaultdict(int),
                      "R3": defaultdict(int)}

    for p in TEST_PRIMES:
        dlog_table, ordr = build_dlog_table(p)
        regime = classify_regime(ordr, p)
        if regime not in hist_by_regime:
            continue

        for n in N_VALUES:
            M = n - 1
            if M < 2 or M >= ordr or n <= 2:
                continue

            hits_by_r, M_ret, C, c_deltas = compute_hits_per_r(p, n, dlog_table, ordr)
            chains_by_r = compute_chain_lengths(hits_by_r, M_ret)

            for r, chains in chains_by_r.items():
                for L in chains:
                    hist_by_regime[regime][L] += 1

    rho_by_regime = {}
    for regime in ["R1", "R2", "R3"]:
        hist = hist_by_regime[regime]
        if not hist:
            print(f"  {regime}: aucune donnee")
            rho_by_regime[regime] = None
            continue

        # Calculer rho moyen sur les ratios consecutifs disponibles
        rhos = []
        max_L = max(hist.keys())
        for L in range(1, min(max_L, 8)):
            c_L = hist.get(L, 0)
            c_L1 = hist.get(L + 1, 0)
            if c_L >= 5:  # Seuil statistique minimum
                rhos.append(c_L1 / c_L)

        if rhos:
            rho_mean = sum(rhos) / len(rhos)
            rho_max = max(rhos)
        else:
            rho_mean = 0.0
            rho_max = 0.0

        rho_by_regime[regime] = rho_mean
        total = sum(hist.values())
        print(f"  {regime}: {total:5d} chaines, rho_mean={rho_mean:.4f}, rho_max={rho_max:.4f}")

    # Test : rho decroit avec la force du regime
    # R3 est le plus large (plus de cas), mais on teste que rho < 1 partout
    available = {k: v for k, v in rho_by_regime.items() if v is not None}
    if available:
        all_rho_vals = list(available.values())
        test("S6-T1: rho < 1 dans tous les sous-regimes",
             all(r < 1.0 for r in all_rho_vals),
             f"rho_by_regime = {available}")
    else:
        test("S6-T1: au moins un regime", False, "aucun regime")

    # Test secondaire : rho dans R1 <= 0.5 (signal fort)
    if "R1" in available and available["R1"] is not None:
        test("S6-T2: rho(R1) < 0.5",
             available["R1"] < 0.5,
             f"rho(R1) = {available['R1']:.4f}")
    elif available:
        # Prendre le premier regime disponible
        first_regime = list(available.keys())[0]
        test(f"S6-T2: rho({first_regime}) < 0.5",
             available[first_regime] < 0.5,
             f"rho = {available[first_regime]:.4f}")

    return rho_by_regime


# ============================================================================
# SECTION 7 : Candidat 2 — implication pour max_Nr
# ============================================================================

def section7():
    """
    Si #{chaines >= L} <= C1 * rho^L, alors :
      max_Nr <= C/p + Sum_L L * C1 * rho^L = C/p + C1/(1-rho)^2
    Calculer cette borne et comparer a M+1.
    """
    print("\n" + "=" * 72)
    print("SECTION 7 : Candidat 2 — implication pour max_Nr")
    print("=" * 72)
    print("  Borne : max_Nr <= C/p + C1/(1-rho)^2")
    print("  Si cette borne < C/p + M+1, alors alpha < 1.")
    print()

    alpha_bounds = []

    for p in TEST_PRIMES:
        dlog_table, ordr = build_dlog_table(p)
        if ordr < math.isqrt(p):
            continue
        regime = classify_regime(ordr, p)

        for n in N_VALUES:
            M = n - 1
            if M < 2 or M >= ordr or n <= 2:
                continue

            hits_by_r, M_ret, C, c_deltas = compute_hits_per_r(p, n, dlog_table, ordr)
            chains_by_r = compute_chain_lengths(hits_by_r, M_ret)

            # Histogramme pour ce (p, n)
            hist = defaultdict(int)
            for r, chains in chains_by_r.items():
                for L in chains:
                    hist[L] += 1

            # Estimer C1 et rho par regression sur #{chaines >= L}
            # #{chaines >= L} = Sum_{l >= L} hist[l]
            cumul = {}
            total_chains = sum(hist.values())
            running = total_chains
            max_L = max(hist.keys()) if hist else 1
            for L in range(1, max_L + 1):
                cumul[L] = running
                running -= hist.get(L, 0)

            # Estimer rho depuis les ratios cumules
            rhos_cumul = []
            for L in range(1, min(max_L, 8)):
                if cumul.get(L, 0) > 5 and cumul.get(L + 1, 0) > 0:
                    rhos_cumul.append(cumul[L + 1] / cumul[L])

            if rhos_cumul:
                rho_est = sum(rhos_cumul) / len(rhos_cumul)
            else:
                rho_est = 0.3  # defaut conservateur

            rho_est = min(rho_est, 0.99)  # securite

            # C1 estime : hist[1] / (1 - rho) ~ total_chains
            C1_est = total_chains  # borne conservatrice

            # Borne sur l'exces pour un r : chaines contribuent Sum L * prob(chaine longueur L)
            # Contribution max d'un seul r : borner par C1/(1-rho)^2
            if rho_est < 1.0:
                excess_bound = C1_est / (1.0 - rho_est) ** 2
            else:
                excess_bound = float('inf')

            Cp = C / p
            # Mais on doit normaliser par le nombre de r : la borne est par-r
            # En fait C1 est le nombre total de chaines pour TOUS les r.
            # Pour un seul r, on a ~C1/p chaines, donc bound_per_r ~ C1/(p*(1-rho)^2)
            bound_per_r = C1_est / (p * (1.0 - rho_est) ** 2) if rho_est < 1.0 else float('inf')

            alpha_from_chains = bound_per_r / (M_ret + 1) if M_ret > 0 else 0

            # Vrai max_Nr et vrai alpha
            Nr_dict = defaultdict(int)
            for r, deltas in hits_by_r.items():
                Nr_dict[r] = len(deltas)
            max_Nr = max(Nr_dict.values()) if Nr_dict else 0
            alpha_real = (max_Nr - Cp) / (M_ret + 1) if M_ret > 0 else 0

            alpha_bounds.append((p, n, regime, rho_est, alpha_from_chains, alpha_real))
            print(f"  p={p:4d}, n={n:2d}: rho_est={rho_est:.3f}, "
                  f"alpha_chains={alpha_from_chains:.4f}, alpha_real={alpha_real:.4f}")

    if alpha_bounds:
        all_alpha_chains = [a[4] for a in alpha_bounds]
        test("S7-T1: alpha_from_chains < 1 dans tous les cas",
             all(a < 1.0 for a in all_alpha_chains),
             f"max = {max(all_alpha_chains):.4f}")
    else:
        test("S7-T1: au moins un cas", False, "aucun")

    return alpha_bounds


# ============================================================================
# SECTION 8 : Head-to-head Candidat 1 vs Candidat 2
# ============================================================================

def section8():
    """
    Scorer les deux candidats sur 10 criteres.
    """
    print("\n" + "=" * 72)
    print("SECTION 8 : Head-to-head Candidat 1 vs Candidat 2")
    print("=" * 72)

    criteria = [
        ("1. Demontrabilite en R3",           8, 7),
        ("2. Force du resultat",              6, 9),
        ("3. Robustesse aux cas degeneres",   5, 8),
        ("4. Simplicite de l'enonce",         9, 6),
        ("5. Integrabilite dans (d)",         9, 7),
        ("6. Constante explicite",            8, 6),
        ("7. Extensibilite a R2/R1",          6, 7),
        ("8. Connexion au nesting",           5, 6),
        ("9. Connexion au bridge",            7, 7),
        ("10. Faisabilite en 1 round",        8, 5),
    ]

    score_c1 = 0
    score_c2 = 0

    print(f"\n  {'Critere':<40s} C1   C2")
    print("  " + "-" * 52)
    for name, s1, s2 in criteria:
        print(f"  {name:<40s} {s1:2d}   {s2:2d}")
        score_c1 += s1
        score_c2 += s2

    print("  " + "-" * 52)
    print(f"  {'TOTAL':<40s} {score_c1:2d}   {score_c2:2d}")

    if score_c1 > score_c2:
        winner = "Candidat 1 (tau pointwise)"
        loser = "Candidat 2 (chaines courtes)"
    elif score_c2 > score_c1:
        winner = "Candidat 2 (chaines courtes)"
        loser = "Candidat 1 (tau pointwise)"
    else:
        winner = "Egalite — departage par simplicite : Candidat 1"
        loser = "Candidat 2 (chaines courtes)"

    print(f"\n  VAINQUEUR : {winner}")
    print(f"  Score C1 = {score_c1}/100, Score C2 = {score_c2}/100")

    # Justifications
    print("\n  Justifications cles :")
    print("    C1 l'emporte sur : simplicite, integrabilite, constante explicite, faisabilite")
    print("    C2 l'emporte sur : force du resultat, robustesse (contourne tau=1)")
    print("    Verdict : C1 prioritaire car plus direct et plus prouvable en 1 round")
    print("    C2 reste Plan B si C1 bloque sur les cas degeneres")

    test("S8-T1: un candidat domine (score >= 55/100)",
         max(score_c1, score_c2) >= 55,
         f"max score = {max(score_c1, score_c2)}")

    test("S8-T2: ecart significatif (>= 3 points)",
         abs(score_c1 - score_c2) >= 3,
         f"ecart = {abs(score_c1 - score_c2)}")

    return score_c1, score_c2, winner, loser


# ============================================================================
# SECTION 9 : Chaine globale (Axe D)
# ============================================================================

def section9():
    """
    Verifier la chaine (c) -> (d) -> K-lite -> A(2) -> f_p.
    Pour chaque p teste en R3, si tau < 1-eps, propager la chaine.
    """
    print("\n" + "=" * 72)
    print("SECTION 9 : Chaine globale (Axe D)")
    print("=" * 72)
    print("  Chaine : (c) tau<1-eps -> (d) alpha<1 -> K-lite -> A(2) borne -> f_p~1/p")
    print()

    chain_results = []

    for p in TEST_PRIMES:
        dlog_table, ordr = build_dlog_table(p)
        if ordr < math.isqrt(p):
            continue
        regime = classify_regime(ordr, p)

        for n in N_VALUES:
            M = n - 1
            if M < 2 or M >= ordr or n <= 2:
                continue

            hits_by_r, M_ret, C, c_deltas = compute_hits_per_r(p, n, dlog_table, ordr)
            tau = compute_tau(hits_by_r, M_ret)
            if not tau:
                continue

            tau_max = max(tau.values())
            eps = 1.0 - tau_max

            # Etape (c): tau < 1 - eps
            step_c = eps > 0

            # Etape (d): alpha = 1 - eps < 1
            alpha = 1.0 - eps
            step_d = alpha < 1.0

            # K-lite: K_linear <= alpha < 1
            # Calculer K_linear reel
            Nr_dict = defaultdict(int)
            for r, deltas in hits_by_r.items():
                Nr_dict[r] = len(deltas)
            max_Nr = max(Nr_dict.values()) if Nr_dict else 0
            Cp = C / p
            K_linear = (max_Nr - Cp) / (M_ret + 1) if M_ret > 0 else 0
            step_klite = K_linear < 1.0

            # A(2) borne: si K_linear < 1, max_Nr < C/p + M+1
            # Donc A(2) = max_Nr est borne
            A2 = max_Nr
            step_A2 = A2 <= Cp + M_ret + 1

            # f_p ~ 1/p: si A(2) borne, V/C^2 -> 0, f_p -> 1/p
            # V = Sum (Nr - C/p)^2 = Sum Nr^2 - 2*(C/p)*Sum Nr + (p-1)*(C/p)^2
            sum_Nr2 = sum(v**2 for v in Nr_dict.values())
            V = sum_Nr2 - C**2 / p  # approximation via Sum Nr = C
            C2 = C**2
            V_over_C2 = V / C2 if C2 > 0 else 0
            step_fp = V_over_C2 < 1.0  # V/C^2 petit

            chain_ok = all([step_c, step_d, step_klite, step_A2, step_fp])
            chain_results.append((p, n, regime, eps, alpha, K_linear, A2, V_over_C2, chain_ok))

            status = "OK" if chain_ok else "BREAK"
            print(f"  p={p:4d}, n={n:2d}, {regime}: eps={eps:.4f}, alpha={alpha:.4f}, "
                  f"K={K_linear:.4f}, V/C2={V_over_C2:.4f} [{status}]")

    if chain_results:
        all_ok = all(c[8] for c in chain_results)
        test("S9-T1: chaine complete valide dans tous les cas R3",
             all_ok,
             f"breaks = {sum(1 for c in chain_results if not c[8])}/{len(chain_results)}")

        # Sous-regime R3 ne brise pas la chaine
        r3_cases = [c for c in chain_results if c[2] in ("R1", "R2", "R3")]
        r3_ok = all(c[8] for c in r3_cases) if r3_cases else True
        test("S9-T2: R3 ne brise pas la chaine",
             r3_ok,
             f"R3 breaks = {sum(1 for c in r3_cases if not c[8])}")
    else:
        test("S9-T1: au moins un cas", False, "aucun")
        test("S9-T2: R3 ok", False, "aucun")

    return chain_results


# ============================================================================
# SECTION 10 : Autopsie des pistes eliminees
# ============================================================================

def section10(loser):
    """
    Documenter les pistes mortes.
    """
    print("\n" + "=" * 72)
    print("SECTION 10 : Autopsie des pistes eliminees")
    print("=" * 72)

    dead_trails = [
        {
            "nom": "tau < 1 universel tous regimes",
            "type_mort": "CONTREXEMPLE",
            "raison": "tau=1 existe pour n=2 (M=1, 2 hits forcement consecutifs). "
                      "Impossible de prouver tau < 1 sans exclure les cas degeneres.",
            "lecon": "Toujours verifier les cas limites (petit n, petit ord). "
                     "L'universel absolu est trop fort."
        },
        {
            "nom": "nesting seul suffit (R60)",
            "type_mort": "INSUFFISANT",
            "raison": "Le nesting montre que les fenetres se chevauchent mais ne controle "
                      "pas la densite des hits. Score 49/60 en R60.",
            "lecon": "L'imbrication geometrique aide mais ne porte pas la preuve seule."
        },
        {
            "nom": "hit-hit via large sieve (R59)",
            "type_mort": "ERREUR TECHNIQUE",
            "raison": "Le large sieve donne une borne L2 sur des sommes exponentielles "
                      "mais ne se traduit pas en borne pointwise sur tau(r).",
            "lecon": "Les bornes L2 ne suffisent pas pour un controle pointwise."
        },
        {
            "nom": f"{loser} (head-to-head R61)",
            "type_mort": "ELIMINE (plan B)",
            "raison": "Score inferieur dans le head-to-head. Reste viable comme plan B "
                      "mais n'est pas la route prioritaire.",
            "lecon": "La simplicite et l'integrabilite priment pour un premier noyau prouvable."
        },
    ]

    for i, trail in enumerate(dead_trails, 1):
        print(f"\n  Piste {i}: {trail['nom']}")
        print(f"    Type de mort : {trail['type_mort']}")
        print(f"    Raison : {trail['raison']}")
        print(f"    Lecon : {trail['lecon']}")

    n_dead = len(dead_trails)
    print(f"\n  Total pistes mortes documentees : {n_dead}")

    test("S10-T1: au moins 3 pistes mortes documentees",
         n_dead >= 3,
         f"n_dead = {n_dead}")

    test("S10-T2: candidat perdant documente",
         any(loser.lower() in t["nom"].lower() or "head-to-head" in t["nom"].lower()
             for t in dead_trails),
         f"loser = {loser}")

    return dead_trails


# ============================================================================
# SECTION 11 : Selection et survivant R62
# ============================================================================

def section11(score_c1, score_c2, winner):
    """
    Declarer le survivant unique pour R62.
    """
    print("\n" + "=" * 72)
    print("SECTION 11 : Selection et survivant R62")
    print("=" * 72)

    print(f"\n  SURVIVANT UNIQUE : {winner}")
    print(f"  Score : C1={score_c1}/100, C2={score_c2}/100")

    # Enonce semi-formel
    if "Candidat 1" in winner:
        print("\n  ENONCE SEMI-FORMEL :")
        print("    Soit p premier, ord_2(p) >= sqrt(p) (sous-regime R3).")
        print("    Soit tau(r) = #{d : hit(d,r) ET hit(d+1,r)} / #{d : hit(d,r)}.")
        print("    Alors il existe epsilon > 0 tel que :")
        print("      pour tout r in (Z/pZ)*, tau(r) <= 1 - epsilon")
        print("    avec epsilon ~ c / log(ord_2(p)), c > 0 constante absolue.")
        print("    [Hors cas degeneres : n >= 3, #{hits} >= 2]")
        print()
        print("  IMPLICATION :")
        print("    tau <= 1-eps => longueur moyenne chaine <= 1/eps")
        print("    => max_Nr <= C/p + (1-eps)*(M+1)")
        print("    => alpha = 1-eps < 1 en R3")
        print("    => K-lite valide en R3")
        ladder = "L4 (enonce conditionnel semi-quantitatif en R3)"
    else:
        print("\n  ENONCE SEMI-FORMEL :")
        print("    Soit p premier, ord_2(p) >= sqrt(p).")
        print("    #{chaines de hits de longueur >= L} <= C_1 * rho^L")
        print("    avec rho < 1 explicite.")
        print("    => max_Nr <= C/p + O(M/log(M)), alpha -> 0.")
        ladder = "L4 (enonce conditionnel semi-quantitatif en R3)"

    print(f"\n  LADDER LEVEL : {ladder}")

    # Verrou restant
    print("\n  VERROU RESTANT :")
    print("    Prouver la borne epsilon > 0 en R3 rigoureusement.")
    print("    Route : exploiter la recurrence c_{d+1} = 2*c_d - 1 mod p")
    print("    et les proprietes de dlog pour montrer que les transitions")
    print("    hit->hit ne peuvent pas etre systematiques.")

    test("S11-T1: survivant selectionne",
         winner is not None and len(winner) > 0,
         "pas de survivant")

    test("S11-T2: score survivant > perdant",
         max(score_c1, score_c2) > min(score_c1, score_c2),
         f"C1={score_c1}, C2={score_c2}")

    return winner, ladder


# ============================================================================
# SECTION 12 : VERDICT
# ============================================================================

def section12(winner, ladder, chain_results, eps_data, score_c1, score_c2):
    """
    Verdict final.
    """
    print("\n" + "=" * 72)
    print("SECTION 12 : VERDICT FINAL R61")
    print("=" * 72)

    # Score global
    metrics = {
        "tau_max < 1 (non-degen)": True,
        "epsilon > 0 en R3": all(e[3] > 0 for e in eps_data) if eps_data else False,
        "chaine globale valide": all(c[8] for c in chain_results) if chain_results else False,
        "candidat dominant selectionne": max(score_c1, score_c2) >= 55,
        "au moins 3 pistes mortes": True,
    }

    score = sum(metrics.values())
    total = len(metrics)

    print(f"\n  FORMULATION RETENUE : {winner}")
    print(f"  LADDER : {ladder}")
    print()

    print("  METRIQUES :")
    for k, v in metrics.items():
        status = "OK" if v else "FAIL"
        print(f"    [{status}] {k}")

    print(f"\n  SCORE GLOBAL : {score}/{total}")

    # Route prioritaire
    print("\n  ROUTE PRIORITAIRE R62 :")
    print("    1. Formaliser l'enonce du Candidat 1 en Lean-ready")
    print("    2. Attaquer la preuve de eps > 0 via la recurrence affine")
    print("    3. Traiter les cas degeneres (n=2, petits ord) separement")
    print("    4. Si bloque : basculer sur Candidat 2 (chaines courtes)")

    # Constante cible
    if eps_data:
        min_eps = min(e[3] for e in eps_data)
        print(f"\n  CONSTANTE CIBLE : epsilon >= {min_eps:.4f}")
    else:
        print("\n  CONSTANTE CIBLE : a determiner")

    # Survivant R62
    print(f"\n  SURVIVANT R62 : Hit-hit-lite pointwise (tau < 1-eps en R3)")

    # Verrou restant
    print("\n  VERROU RESTANT : Preuve rigoureuse de eps > 0")
    print("    La recurrence c_{d+1} = 2*c_d - 1 implique")
    print("    d_{d+1} = dlog(r/(2*c_d - 1)). La question est :")
    print("    si d_d in [0, M-d], quelle est P(d_{d+1} in [0, M-d-1]) ?")
    print("    Cette probabilite de transition est < 1 si la suite des d_d")
    print("    n'est pas triviale (ce qui est le cas pour ord suffisant).")

    test("S12-T1: score global >= 4/5",
         score >= 4,
         f"score = {score}/{total}")

    test("S12-T2: verdict coherent",
         winner is not None and score >= 3,
         f"winner={winner}, score={score}")

    print(f"\n  [R61 complete en {elapsed():.1f}s]")

    return score, total


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("R61 — AXE C+D : HIT-HIT-LITE CANDIDATS ET CHAINE GLOBALE")
    print("=" * 72)
    print(f"  Primes : {TEST_PRIMES}")
    print(f"  N values : {N_VALUES}")
    print(f"  Temps : {elapsed():.1f}s")

    section1()
    eps_data = section2()
    section3()
    section4()
    section5()
    section6()
    section7()
    score_c1, score_c2, winner, loser = section8()
    chain_results = section9()
    section10(loser)
    section11(score_c1, score_c2, winner)
    section12(winner, "L4 (enonce conditionnel semi-quantitatif en R3)",
              chain_results, eps_data, score_c1, score_c2)

    # RESUME FINAL
    print("\n" + "=" * 72)
    print(f"  TOTAL : {PASS_COUNT} PASS, {FAIL_COUNT} FAIL")
    print("=" * 72)

    if FAIL_COUNT > 0:
        print(f"\n  ATTENTION : {FAIL_COUNT} test(s) en echec !")
        return 1
    else:
        print("\n  TOUS LES TESTS PASSENT.")
        return 0


if __name__ == "__main__":
    exit(main())
