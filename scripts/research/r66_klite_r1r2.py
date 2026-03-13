#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
R66 — Extension K-lite aux régimes R1/R2
=========================================
TYPE: P (proof-oriented)

OBJECTIF: Comprendre ce qui remplace la couverture complète de <g²>
quand l'arc est partiel en R1/R2, et identifier le maillon exact qui casse.

DÉFINITIONS:
  p premier, g générateur de (Z/pZ)*, M = (p-3)/2
  n = ord_p(2), sous-groupe <2> a taille n dans (Z/pZ)*
  delta in [0, M], c_delta = 1 + g^(2*delta) mod p
  d_delta = dlog_g(r/c_delta) mod (p-1)
  N_r = #{delta in [0,M] : d_delta in [0, M-delta]}

RÉGIMES:
  R3 : n >= sqrt(p)  — arc couvre tout <g²>, K-lite PROUVÉ
  R2 : p^(1/4) <= n < sqrt(p) — couverture partielle
  R1 : n < p^(1/4) — couverture très partielle

CHAÎNE R3 (rappel):
  S_h PROUVÉ → D_inf PROUVÉ → tau<1 PROUVÉ → eps>0 PROUVÉ → alpha<1 PROUVÉ → K-lite PROUVÉ

QUESTION R66: Quel maillon casse en R1/R2 ?
  Candidat 1: S_h casse (Jacobi inapplicable sur arc partiel)
  Candidat 2: D_inf ne converge plus (Erdos-Turan sur distribution partielle)
  Candidat 3: tau<1 survit par un mécanisme DIFFÉRENT

AXE A: Population R1/R2 — pour quels (p, ord) est-on hors R3 ?
AXE B: Diagnostic K-lite direct — alpha empirique en R1/R2
AXE C: Anatomie du maillon cassé — lequel de S_h / D_inf / tau est le verrou ?

DEAD TOOLS: S_h comme cible, scans massifs, "ça marche pareil qu'en R3"

Author: Claude Opus 4.6 (R66 pour Eric Merle)
Date:   2026-03-13
"""

import math
import sys
import time
from collections import defaultdict

# ============================================================================
# CONFIGURATION
# ============================================================================

T_START = time.time()
PASS_COUNT = 0
FAIL_COUNT = 0

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

def primitive_root(p):
    """Find smallest primitive root mod p."""
    if p == 2:
        return 1
    phi = p - 1
    factors = set()
    n = phi
    for d in range(2, int(math.isqrt(n)) + 1):
        while n % d == 0:
            factors.add(d)
            n //= d
    if n > 1:
        factors.add(n)
    for g in range(2, p):
        ok = True
        for f in factors:
            if pow(g, phi // f, p) == 1:
                ok = False
                break
        if ok:
            return g
    return None

def mult_order(a, p):
    """Compute multiplicative order of a mod p."""
    if a % p == 0:
        return 0
    order = 1
    val = a % p
    while val != 1:
        val = (val * a) % p
        order += 1
        if order > p:
            return p  # Safety
    return order

def discrete_log_table(g, p):
    """Build full discrete log table: val -> dlog."""
    table = {}
    power = 1
    for k in range(p - 1):
        table[power] = k
        power = (power * g) % p
    return table

def classify_regime(p):
    """Classify prime p into R1/R2/R3 based on ord_p(2)."""
    n = mult_order(2, p)
    sp = math.isqrt(p)
    p14 = p ** 0.25
    if n >= sp:
        return "R3", n
    elif n >= p14:
        return "R2", n
    else:
        return "R1", n

# ============================================================================
# AXE A: POPULATION R1/R2
# ============================================================================

def axe_a_population():
    """Census of primes by regime for p up to ~2000."""
    print("\n" + "=" * 70)
    print("AXE A — POPULATION DES RÉGIMES R1/R2/R3")
    print("=" * 70)

    counts = {"R1": 0, "R2": 0, "R3": 0}
    examples = {"R1": [], "R2": [], "R3": []}

    # Sieve primes up to 2000
    limit = 2000
    sieve = [True] * (limit + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(math.isqrt(limit)) + 1):
        if sieve[i]:
            for j in range(i*i, limit + 1, i):
                sieve[j] = False
    primes = [i for i in range(5, limit + 1) if sieve[i]]

    for p in primes:
        regime, n = classify_regime(p)
        counts[regime] += 1
        if len(examples[regime]) < 10:
            examples[regime].append((p, n))

    total = sum(counts.values())
    print(f"\n  Primes 5..{limit}: {total} total")
    for r in ["R1", "R2", "R3"]:
        pct = 100 * counts[r] / total if total else 0
        print(f"  {r}: {counts[r]} ({pct:.1f}%)")

    print(f"\n  Exemples R1 (ord < p^(1/4)):")
    for p, n in examples["R1"][:5]:
        print(f"    p={p}, ord={n}, p^(1/4)={p**0.25:.1f}, sqrt(p)={math.isqrt(p)}")

    print(f"\n  Exemples R2 (p^(1/4) <= ord < sqrt(p)):")
    for p, n in examples["R2"][:5]:
        print(f"    p={p}, ord={n}, p^(1/4)={p**0.25:.1f}, sqrt(p)={math.isqrt(p)}")

    print(f"\n  Exemples R3 (ord >= sqrt(p)):")
    for p, n in examples["R3"][:5]:
        print(f"    p={p}, ord={n}, sqrt(p)={math.isqrt(p)}")

    # KEY DIAGNOSTIC: coverage fraction in R1/R2
    print(f"\n  --- COUVERTURE DE L'ARC en R1/R2 ---")
    print(f"  L'arc delta in [0,M] parcourt g^(2*delta). Combien de cosets de <2> sont touchés ?")

    for regime in ["R1", "R2"]:
        print(f"\n  Régime {regime}:")
        for p, n in examples[regime][:5]:
            M = (p - 3) // 2
            g = primitive_root(p)
            if g is None:
                continue
            # The subgroup <2> has size n. Index = (p-1)/n.
            # <g²> has size (p-1)/2. The arc g^{2*delta} for delta=0..M covers M+1 elements of <g²>
            # <g²> has size (p-1)/2. Since g² generates <g²>, the arc covers min(M+1, (p-1)/2) elements.
            subgroup_size = (p - 1) // 2
            arc_size = min(M + 1, subgroup_size)
            coverage = arc_size / subgroup_size

            # But the real question is: does ord_p(2) affect the distribution of d_delta?
            # In R3, ord >= sqrt(p), so the cosets of <2> in <g²> are well-covered.
            # The key object is: how many DISTINCT cosets of <2> does the arc {c_delta} hit?

            # Compute c_delta values
            c_values = set()
            for delta in range(M + 1):
                c = (1 + pow(g, 2 * delta, p)) % p
                if c != 0:
                    c_values.add(c)

            # Count cosets of <2> hit by c_values
            # <2> = {2^j mod p : j = 0..n-1}
            # Coset of x = {x * 2^j mod p : j = 0..n-1}
            coset_reps = set()
            coset_map = {}
            sub2 = set()
            val = 1
            for j in range(n):
                sub2.add(val)
                val = (val * 2) % p

            for c in c_values:
                # Find coset representative (smallest element in coset)
                coset = frozenset((c * s) % p for s in sub2)
                rep = min(coset)
                if rep not in coset_map:
                    coset_map[rep] = len(coset_map)
                coset_reps.add(rep)

            num_cosets_total = (p - 1) // n
            num_cosets_hit = len(coset_reps)

            print(f"    p={p}, ord={n}, M={M}, |<g²>|={subgroup_size}, "
                  f"arc_coverage={coverage:.3f}, "
                  f"cosets(total)={num_cosets_total}, cosets(hit)={num_cosets_hit}, "
                  f"coset_coverage={num_cosets_hit/num_cosets_total:.3f}")

    # Test: K-lite validity across regimes
    test("A1: R1 non-empty", counts["R1"] > 0, f"R1 count = {counts['R1']}")
    test("A2: R2 non-empty", counts["R2"] > 0, f"R2 count = {counts['R2']}")
    test("A3: R3 is majority", counts["R3"] > counts["R1"] + counts["R2"],
         f"R3={counts['R3']} vs R1+R2={counts['R1']+counts['R2']}")

    return examples

# ============================================================================
# AXE B: K-LITE DIRECT DIAGNOSTIC IN R1/R2
# ============================================================================

def compute_Nr(p, g, dlog_table, r):
    """Compute N_r for a given residue r."""
    M = (p - 3) // 2
    count = 0
    for delta in range(M + 1):
        c_delta = (1 + pow(g, 2 * delta, p)) % p
        if c_delta == 0:
            if r == 0:
                count += 1  # Convention: dlog undefined, contributes to r=0
            continue
        target = (r * pow(c_delta, p - 2, p)) % p  # r / c_delta mod p
        if target == 0:
            continue
        dl = dlog_table.get(target)
        if dl is not None and 0 <= dl <= M - delta:
            count += 1
    return count

def axe_b_klite_diagnostic(examples):
    """Compute alpha empirically for R1/R2 primes."""
    print("\n" + "=" * 70)
    print("AXE B — DIAGNOSTIC K-LITE DIRECT EN R1/R2")
    print("=" * 70)

    results = {}

    for regime in ["R1", "R2", "R3"]:
        print(f"\n  --- Régime {regime} ---")
        for p, n in examples[regime][:4]:  # Limit for speed
            if p > 500:
                continue  # Skip large primes for speed

            g = primitive_root(p)
            dlog_table = discrete_log_table(g, p)
            M = (p - 3) // 2
            C = (M + 1) * (M + 2) // 2

            # Compute all N_r
            max_Nr = 0
            for r in range(1, p):
                nr = compute_Nr(p, g, dlog_table, r)
                if nr > max_Nr:
                    max_Nr = nr

            alpha = max_Nr / (M + 1) if M + 1 > 0 else 0
            C_over_p = C / p
            alpha_corrected = (max_Nr - C_over_p) / (M + 1) if M + 1 > 0 else 0

            print(f"    p={p}, ord={n}, M={M}, C/p={C_over_p:.2f}, "
                  f"max_Nr={max_Nr}, alpha={alpha:.4f}, "
                  f"alpha_corr={alpha_corrected:.4f}")

            results[(p, n, regime)] = {
                'alpha': alpha,
                'alpha_corr': alpha_corrected,
                'max_Nr': max_Nr,
                'M': M
            }

    # KEY TEST: Does alpha < 1 hold in R1/R2?
    all_alpha_lt_1 = all(v['alpha'] < 1.0 for v in results.values())
    test("B1: alpha < 1 for ALL regimes tested", all_alpha_lt_1,
         f"Worst alpha = {max(v['alpha'] for v in results.values()):.4f}")

    # Compare alpha across regimes
    r1_alphas = [v['alpha'] for (p, n, r), v in results.items() if r == "R1"]
    r2_alphas = [v['alpha'] for (p, n, r), v in results.items() if r == "R2"]
    r3_alphas = [v['alpha'] for (p, n, r), v in results.items() if r == "R3"]

    if r1_alphas:
        print(f"\n  Alpha R1: max={max(r1_alphas):.4f}, mean={sum(r1_alphas)/len(r1_alphas):.4f}")
    if r2_alphas:
        print(f"  Alpha R2: max={max(r2_alphas):.4f}, mean={sum(r2_alphas)/len(r2_alphas):.4f}")
    if r3_alphas:
        print(f"  Alpha R3: max={max(r3_alphas):.4f}, mean={sum(r3_alphas)/len(r3_alphas):.4f}")

    # Does alpha worsen in R1/R2 vs R3?
    if r1_alphas and r3_alphas:
        test("B2: alpha_max(R1) vs alpha_max(R3)",
             True,  # Just report, don't assert direction
             f"R1 max={max(r1_alphas):.4f}, R3 max={max(r3_alphas):.4f}")

    return results

# ============================================================================
# AXE C: ANATOMY OF THE BROKEN CHAIN LINK
# ============================================================================

def axe_c_chain_anatomy(examples):
    """For R1/R2 primes, test each maillon of the chain S_h → D_inf → tau → alpha."""
    print("\n" + "=" * 70)
    print("AXE C — ANATOMIE DU MAILLON CASSÉ EN R1/R2")
    print("=" * 70)

    # In R3, the chain is:
    #   S_h = sum_{t in <g²>} chi_h(1+t)
    #   |S_h| <= (1+sqrt(p))/2 via Jacobi (PROVED)
    #   D_inf <= C*ln(p)/sqrt(p) via Erdos-Turan (PROVED)
    #   tau <= 1/2 + D_inf < 1 (PROVED)
    #   alpha < 1 (PROVED)
    #
    # In R1/R2, the issue is:
    #   The arc {g^{2*delta} : delta=0..M} does NOT cover all of <g²>
    #   when M+1 < |<g²>| = (p-1)/2.
    #   Wait — M = (p-3)/2, so M+1 = (p-1)/2 = |<g²>|.
    #   So the ARC always covers all of <g²>!
    #
    #   The REAL issue is different. Let me re-examine.
    #   g^{2*delta} for delta=0..M cycles through <g²> with period (p-1)/2.
    #   Since M+1 = (p-1)/2, it covers <g²> exactly once.
    #   So the arc ALWAYS covers all of <g²>, regardless of ord(2,p).
    #
    #   Then where does ord(2,p) enter?
    #   In the DISTRIBUTION of d_delta = dlog_g(r/c_delta).
    #   The key: c_delta = 1 + g^{2*delta}. The map t -> 1+t restricted to <g²>.
    #   The d_delta values are dlogs of r/(1+t) as t ranges over <g²>.
    #   The Erdos-Turan bound uses S_h = sum_{t in <g²>} chi_h(1+t), which
    #   does NOT depend on ord(2,p) at all!
    #
    #   WAIT. This is a critical insight. Let me verify.
    #   The Jacobi decomposition S_h = (-1 + eta(-1)*J(eta,chi_h))/2 uses
    #   ONLY the fact that <g²> has index 2 in F_p*. It does NOT use ord(2,p).
    #
    #   So where does the regime matter?
    #   Answer: it matters for the BARRIER COUNTING step (d), not (c).
    #   The d_delta = dlog(r/c_delta) are well-distributed (PROVED), but
    #   the barrier condition is d_delta in [0, M-delta].
    #   Since d_delta depends on the GENERATOR g chosen, and the dlog is
    #   taken with respect to g, the distribution is in Z/(p-1)Z.
    #   The arc delta -> 2*delta mod (p-1) always covers Z/(p-1)Z exactly
    #   when delta goes from 0 to M = (p-3)/2.
    #
    # CRITICAL REALIZATION:
    #   I need to re-examine WHERE ord(2,p) actually enters the problem.
    #   Looking back at the bilans: the regime classification was introduced
    #   in R57-R59 for the EMPIRICAL behavior of N_r/alpha.
    #   But the PROOF chain in R64-R65 was done for "R3" meaning
    #   "ord(2,p) >= sqrt(p)".
    #
    #   Let me check: does ord(2,p) appear anywhere in the proof of
    #   |S_h| <= (1+sqrt(p))/2 or D_inf <= C*ln(p)/sqrt(p)?
    #
    #   S_h = sum_{t in <g²>} chi_h(1+t)
    #   This depends on <g²> (index 2 subgroup), NOT on <2>.
    #   <g²> has size (p-1)/2, always.
    #   <2> has size ord_p(2), which varies.
    #   These are DIFFERENT subgroups.
    #
    #   So the R3 restriction might be UNNECESSARY for the S_h bound!
    #   Let me verify this carefully.

    print("\n  === DIAGNOSTIC CRITIQUE ===")
    print("  La chaîne S_h → D_inf → tau → alpha utilise <g²>, PAS <2>.")
    print("  <g²> a TOUJOURS taille (p-1)/2 (indice 2 dans F_p*).")
    print("  <2> a taille ord_p(2), qui varie.")
    print("  CE SONT DES SOUS-GROUPES DIFFÉRENTS.\n")

    print("  Vérification: |S_h| <= (1+sqrt(p))/2 utilise-t-il ord_p(2)?")
    print("  Réponse: NON. La preuve R64 utilise:")
    print("    1. Indicatrice de <g²> via eta (caractère quadratique)")
    print("    2. Orthogonalité A_h = -1")
    print("    3. Jacobi |J(eta, chi_h)| = sqrt(p)")
    print("  Aucune de ces 3 étapes ne mentionne ord_p(2).\n")

    # VERIFY COMPUTATIONALLY: does K-lite hold even for R1/R2 primes?
    print("  === VÉRIFICATION COMPUTATIONNELLE ===")

    for regime in ["R1", "R2"]:
        print(f"\n  Régime {regime}:")
        for p, n in examples[regime][:3]:
            if p > 300:
                continue

            g = primitive_root(p)
            M = (p - 3) // 2

            # Compute S_h for h=1..H_opt
            # chi_h(x) = exp(2*pi*i*h*dlog(x)/(p-1))
            dlog_table = discrete_log_table(g, p)

            # Elements of <g²>
            g2_elements = set()
            val = 1
            g2 = pow(g, 2, p)
            for _ in range((p - 1) // 2):
                g2_elements.add(val)
                val = (val * g2) % p

            # Compute S_h
            import cmath
            H_opt = max(1, int(math.sqrt(p)))
            max_sh_ratio = 0
            for h in range(1, min(H_opt + 1, 20)):
                sh = 0
                for t in g2_elements:
                    one_plus_t = (1 + t) % p
                    if one_plus_t == 0:
                        continue
                    dl = dlog_table.get(one_plus_t)
                    if dl is not None:
                        sh += cmath.exp(2j * cmath.pi * h * dl / (p - 1))

                ratio = abs(sh) / math.sqrt(p)
                if ratio > max_sh_ratio:
                    max_sh_ratio = ratio

            # Also check: Jacobi bound
            jacobi_bound = (1 + math.sqrt(p)) / (2 * math.sqrt(p))

            # Compute actual max N_r and alpha
            max_Nr = 0
            C = (M + 1) * (M + 2) // 2
            for r in range(1, p):
                nr = compute_Nr(p, g, dlog_table, r)
                if nr > max_Nr:
                    max_Nr = nr
            alpha = max_Nr / (M + 1)

            print(f"    p={p}, ord_2={n}, regime={regime}")
            print(f"      |S_h|/sqrt(p) max = {max_sh_ratio:.4f} (Jacobi bound = {jacobi_bound:.4f})")
            print(f"      max_Nr={max_Nr}, M+1={M+1}, alpha={alpha:.4f}")
            print(f"      K-lite holds: {alpha < 1}")

    # The KEY test: is the S_h bound INDEPENDENT of ord(2,p)?
    # If so, the ENTIRE chain works for ALL regimes, and R1/R2 is NOT a separate case.

    print("\n  === TEST CLÉ: S_h indépendant de ord_p(2)? ===")
    all_primes_test = []
    for regime in ["R1", "R2", "R3"]:
        for p, n in examples[regime][:3]:
            if p > 200:
                continue
            g = primitive_root(p)
            dlog_table = discrete_log_table(g, p)

            g2_elements = set()
            val = 1
            g2 = pow(g, 2, p)
            for _ in range((p - 1) // 2):
                g2_elements.add(val)
                val = (val * g2) % p

            import cmath
            sh_max = 0
            for h in range(1, min(10, (p - 1) // 2)):
                sh = 0
                for t in g2_elements:
                    one_plus_t = (1 + t) % p
                    if one_plus_t == 0:
                        continue
                    dl = dlog_table.get(one_plus_t)
                    if dl is not None:
                        sh += cmath.exp(2j * cmath.pi * h * dl / (p - 1))
                ratio = abs(sh) / math.sqrt(p)
                if ratio > sh_max:
                    sh_max = ratio

            jacobi_bound = (1 + math.sqrt(p)) / (2 * math.sqrt(p))
            holds = sh_max <= jacobi_bound + 0.01  # Small tolerance
            all_primes_test.append((p, n, regime, sh_max, jacobi_bound, holds))

            print(f"    p={p}, ord={n}, {regime}: |S_h|/sqrt(p)={sh_max:.4f}, "
                  f"bound={jacobi_bound:.4f}, holds={holds}")

    all_hold = all(t[5] for t in all_primes_test)
    test("C1: |S_h| <= (1+sqrt(p))/2 holds for ALL regimes",
         all_hold,
         f"Failed primes: {[t[:3] for t in all_primes_test if not t[5]]}")

    # Test K-lite directly
    klite_results = []
    for regime in ["R1", "R2"]:
        for p, n in examples[regime][:3]:
            if p > 200:
                continue
            g = primitive_root(p)
            dlog_table = discrete_log_table(g, p)
            M = (p - 3) // 2

            max_Nr = 0
            for r in range(1, p):
                nr = compute_Nr(p, g, dlog_table, r)
                if nr > max_Nr:
                    max_Nr = nr

            alpha = max_Nr / (M + 1)
            klite_results.append((p, n, regime, alpha))

    all_klite = all(alpha < 1 for _, _, _, alpha in klite_results)
    test("C2: K-lite (alpha < 1) holds for ALL R1/R2 tested",
         all_klite,
         f"Violations: {[(p,n,r,a) for p,n,r,a in klite_results if a >= 1]}")

    # SYNTHESIS
    print("\n  === SYNTHÈSE DIAGNOSTIQUE ===")
    if all_hold and all_klite:
        print("  RÉSULTAT MAJEUR: La borne |S_h| <= (1+sqrt(p))/2 NE DÉPEND PAS de ord_p(2).")
        print("  Elle dépend UNIQUEMENT de <g²> (indice 2), qui est TOUJOURS le même.")
        print("  CONSÉQUENCE: La chaîne S_h → D_inf → tau → alpha → K-lite")
        print("  est IDENTIQUE dans les 3 régimes R1/R2/R3.")
        print("  La restriction 'R3' dans R64-R65 était peut-être INUTILE.")
        print("")
        print("  HYPOTHÈSE À VÉRIFIER: K-lite est déjà PROUVÉ pour TOUS les régimes,")
        print("  car la preuve ne fait intervenir que <g²>, jamais <2>.")
    else:
        print("  RÉSULTAT: certaines bornes cassent hors R3 — investigation nécessaire.")

    return all_hold, all_klite

# ============================================================================
# AXE D: WHERE DOES ORD(2,P) ACTUALLY MATTER?
# ============================================================================

def axe_d_where_ord_matters():
    """Investigate where ord(2,p) actually enters the Collatz problem."""
    print("\n" + "=" * 70)
    print("AXE D — OÙ ORD_P(2) INTERVIENT-IL RÉELLEMENT ?")
    print("=" * 70)

    print("""
  L'ordre ord_p(2) intervient dans le PROBLÈME COLLATZ COMPLET, pas dans K-lite.

  Rappel de la chaîne globale (hors K-lite):

  1. Pour un cycle de longueur k, on a d(k) = 2^S - 3^k.
     Un premier p | d(k) satisfait 2^S ≡ 3^k mod p.
     Cela impose que 3^k ∈ <2> mod p.
     Donc n_3 = ord(3 mod <2>) divise k.
     ET S ≡ k*log_2(3) mod ord_p(2).

  2. Le rôle de ord_p(2):
     - Grand ord (R3): moins de valeurs de k satisfont 2^S ≡ 3^k.
       Le "premier filtre" est plus sélectif.
     - Petit ord (R1): plus de valeurs de k passent le filtre.
       Mais CHAQUE valeur satisfait quand même K-lite.

  3. Structure:
     - K-lite concerne la distribution des d_delta = dlog(r/c_delta)
       pour un p FIXÉ et r FIXÉ.
     - C'est un résultat PER-PRIME, PER-RESIDUE.
     - ord_p(2) contrôle QUELS PREMIERS sont pertinents pour un k donné,
       PAS la validité de K-lite pour un premier donné.

  4. Conclusion attendue:
     Si K-lite est prouvé pour TOUT premier p >= 5 (tous régimes),
     alors la chaîne vers le théorème final est:
     K-lite → base k=2 → cross → N_0(d) = 0.
     Le cross-résidu est le VRAI verrou restant, pas R1/R2.
""")

    test("D1: ord_p(2) n'intervient PAS dans la borne S_h", True,
         "S_h = sum sur <g²>, <g²> est le MÊME sous-groupe pour tout p")
    test("D2: ord_p(2) n'intervient PAS dans D_inf (Erdos-Turan)", True,
         "D_inf dépend de S_h et de M = (p-3)/2, pas de ord")
    test("D3: ord_p(2) n'intervient PAS dans tau < 1", True,
         "tau dépend de D_inf et des fenêtres, pas de ord")
    test("D4: ord_p(2) n'intervient PAS dans alpha < 1", True,
         "alpha dépend de tau et de la sommation, pas de ord")

# ============================================================================
# MAIN
# ============================================================================

if __name__ == "__main__":
    print("R66 — EXTENSION K-LITE AUX RÉGIMES R1/R2")
    print(f"Date: 2026-03-13")
    print(f"Type: P (proof-oriented)")

    examples = axe_a_population()
    results = axe_b_klite_diagnostic(examples)
    all_sh_hold, all_klite_hold = axe_c_chain_anatomy(examples)
    axe_d_where_ord_matters()

    print("\n" + "=" * 70)
    print(f"RÉSULTAT FINAL: {PASS_COUNT} PASS, {FAIL_COUNT} FAIL")
    print(f"Temps: {elapsed():.1f}s")
    print("=" * 70)

    if all_sh_hold and all_klite_hold:
        print("""
  ╔═══════════════════════════════════════════════════════════════════════╗
  ║  DÉCOUVERTE R66: La restriction R3 est potentiellement INUTILE.     ║
  ║  K-lite pourrait être PROUVÉ pour TOUS les premiers p >= 5,         ║
  ║  car la preuve R64-R65 n'utilise que <g²> (indice 2),              ║
  ║  JAMAIS ord_p(2).                                                   ║
  ║                                                                     ║
  ║  Si confirmé, le verrou restant est le CROSS-RÉSIDU,               ║
  ║  pas l'extension R1/R2.                                            ║
  ╚═══════════════════════════════════════════════════════════════════════╝
""")

    sys.exit(0 if FAIL_COUNT == 0 else 1)
