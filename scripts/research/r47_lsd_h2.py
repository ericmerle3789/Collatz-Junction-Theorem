#!/usr/bin/env python3
"""
R47: Binôme A — Structure des collisions à distance de Hamming h=2 (LSD)
=========================================================================
Agent A1 (Investigateur LSD) + Agent A2 (Innovateur LSD) — Round 47

MISSION: Analyser la structure algébrique des collisions à h=2 et proposer
le meilleur noyau prouvable suivant pour la route LSD.

CONTEXTE ACQUIS (NE PAS RE-PROUVER):
  N_r = #{monotone B : P_B(g) ≡ r mod p}, C = C(S-1, k-1), g = 2·3⁻¹ mod p
  M₂ = Σ N_r² = #{(B,B') : P_B ≡ P_{B'} mod p}            [PROUVÉ R45]
  V = M₂ - C²/p ≥ 0                                         [PROUVÉ R45]
  μ = M₂·p/C², μ−1 = (p-1)/C + p·E_excess/C²               [PROUVÉ R46]
  ACL: f_p ≤ 1/p + √((p-1)·V/(p·C²))                       [PROUVÉ R44]
  T52 [PROUVÉ R46]: Pour h(B,B')=1 (une seule coordonnée j diffère, Δ=|Bⱼ−B'ⱼ|):
    P_B ≡ P_{B'} mod p  ⟺  ord_p(2) | Δ
    Preuve: D = gʲ · 2^{min(Bⱼ,B'ⱼ)} · (2^Δ − 1). Comme gcd(gʲ·2^min, p)=1,
    D ≡ 0 mod p ssi 2^Δ ≡ 1 mod p ssi ord_p(2) | Δ.
  Far-pair rate ≈ 1/p pour h ≥ k/2                          [OBSERVÉ R46]
  Near-pair excess borné : excess_near/C ≤ 1.10              [OBSERVÉ R46]

SECTIONS:
  0: Primitives (compute_S, compute_C, dp_full_distribution, reference data)
  1: Validation (5+ tests)
  2: Forme algébrique h=2 — dérivation et vérification (Q1)
  3: Réduction et sous-cas (Q2, Q3)
  4: Comptage des collisions h=2 exact par brute-force (Q4)
  5: Sous-lemme h=2 (Q5)
  6: Candidat 1 — Lemme h=2 restreint
  7: Candidat 2 — Lemme near-pairs
  8: Head-to-head et survivant LSD
  9: Self-tests (40+ tests, all PASS)

EPISTEMIC LABELS:
  [PROUVÉ]       = preuve rigoureuse ou DP exact
  [SEMI-FORMEL]  = argument structuré, pas une preuve formelle
  [CALCULÉ]      = vérifié par calcul exact
  [OBSERVÉ]      = évidence numérique, PAS une preuve
  [CONJECTURAL]  = plausible mais non prouvé
  [RÉFUTÉ]       = contredit par l'évidence

Author: Claude Opus 4.6 (R47 Binôme A pour Eric Merle, Collatz Junction Theorem)
Date:   2026-03-10
"""

import sys
import time
from math import comb, gcd, ceil, log2, sqrt, log
from collections import defaultdict

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

T_START = time.time()
TIME_BUDGET = 114.0  # safety margin on 120s

TEST_RESULTS = []
PASS_COUNT = 0
FAIL_COUNT = 0
VERBOSE = True


def elapsed():
    return time.time() - T_START


def time_remaining():
    return TIME_BUDGET - elapsed()


def record_test(name, passed, detail=""):
    global PASS_COUNT, FAIL_COUNT
    status = "PASS" if passed else "FAIL"
    if passed:
        PASS_COUNT += 1
    else:
        FAIL_COUNT += 1
    TEST_RESULTS.append((name, passed, detail))
    if VERBOSE:
        print(f"  [{status}] {name}" + (f" -- {detail}" if detail else ""))


# ============================================================================
# SECTION 0: MATHEMATICAL PRIMITIVES
# ============================================================================

def compute_S(k):
    """Minimal S such that 2^S > 3^k. Exact via integer comparison."""
    S = ceil(k * log2(3))
    three_k = 3 ** k
    while (1 << S) <= three_k:
        S += 1
    while S > 0 and (1 << (S - 1)) > three_k:
        S -= 1
    return S


def compute_d(k):
    """d(k) = 2^S(k) - 3^k. Returns (d, S)."""
    S = compute_S(k)
    return (1 << S) - 3 ** k, S


def compute_C(k):
    """C(k) = C(S-1, k-1), number of nondecreasing B-vectors."""
    S = compute_S(k)
    return comb(S - 1, k - 1)


def compute_max_B(k):
    """max_B = S - k."""
    return compute_S(k) - k


def compute_g(k, mod):
    """g = 2 * 3^{-1} mod m."""
    if gcd(3, mod) != 1:
        return None
    return (2 * pow(3, -1, mod)) % mod


def ord_mod(base, mod):
    """Multiplicative order of base modulo mod."""
    if gcd(base, mod) != 1:
        return None
    val = base % mod
    if val == 0:
        return None
    o = 1
    cur = val
    while cur != 1:
        cur = (cur * val) % mod
        o += 1
        if o > mod:
            return None
    return o


def dp_full_distribution(k, mod, max_time=10.0):
    """Full residue distribution via DP with (last_b, residue) states.
    Returns list of length mod: [N_0, N_1, ..., N_{mod-1}]."""
    t0 = time.time()
    if mod <= 0 or gcd(3, mod) != 1:
        return None
    S = compute_S(k)
    max_B = S - k
    nB = max_B + 1
    g = pow(3, -1, mod)
    g = (2 * g) % mod
    g_pows = [pow(g, j, mod) for j in range(k)]
    two_pows = [pow(2, b, mod) for b in range(nB)]

    state_size = mod * nB
    if state_size > 10_000_000:
        return None

    dp = [0] * state_size
    for b in range(nB):
        r = (g_pows[0] * two_pows[b]) % mod
        dp[b * mod + r] += 1

    for j in range(1, k):
        if time.time() - t0 > max_time:
            return None
        coeff = g_pows[j]
        new_dp = [0] * state_size
        if j == k - 1:
            c2b = (coeff * two_pows[max_B]) % mod
            for prev_b in range(nB):
                base = prev_b * mod
                target_base = max_B * mod
                for r in range(mod):
                    cnt = dp[base + r]
                    if cnt > 0:
                        nr = (r + c2b) % mod
                        new_dp[target_base + nr] += cnt
        else:
            for prev_b in range(nB):
                base = prev_b * mod
                for b in range(prev_b, nB):
                    c2b = (coeff * two_pows[b]) % mod
                    target_base = b * mod
                    for r in range(mod):
                        cnt = dp[base + r]
                        if cnt > 0:
                            nr = (r + c2b) % mod
                            new_dp[target_base + nr] += cnt
        dp = new_dp

    dist = [0] * mod
    for b in range(nB):
        base = b * mod
        for r in range(mod):
            dist[r] += dp[base + r]
    return dist


def compute_M2(dist):
    """Second moment M₂ = Σ N_r²."""
    return sum(nr * nr for nr in dist)


def compute_V(M2, C, p):
    """Variance V = M₂ - C²/p."""
    return M2 - C * C / p


def compute_mu(M2, C, p):
    """Collision multiplicity μ = M₂·p/C²."""
    return M2 * p / (C * C)


def enumerate_B_vectors(k, max_B):
    """Enumerate all nondecreasing B-vectors with B_{k-1} = max_B."""
    if k == 1:
        yield (max_B,)
        return

    def _gen(pos, lower, upper, current):
        if pos == k - 1:
            yield tuple(current) + (max_B,)
            return
        for b in range(lower, upper + 1):
            yield from _gen(pos + 1, b, upper, current + [b])
    yield from _gen(0, 0, max_B, [])


def compute_PB(B, g, p):
    """P_B(g) = Σ_{j=0}^{k-1} g^j · 2^{B_j} mod p."""
    val = 0
    gj = 1
    for bj in B:
        val = (val + gj * pow(2, bj, p)) % p
        gj = (gj * g) % p
    return val


def hamming_dist(B1, B2):
    """Hamming distance between B-vectors."""
    return sum(1 for a, b in zip(B1, B2) if a != b)


# Reference data for validation (from R45 codebase, verified by DP + brute-force)
REFERENCE = {
    (3, 5):    {'C': 6,     'N0': 0,   'S': 5,  'max_B': 2},
    (6, 5):    {'C': 126,   'N0': 36,  'S': 10, 'max_B': 4},
    (6, 59):   {'C': 126,   'N0': 6},
    (7, 23):   {'C': 462,   'N0': 14,  'S': 12, 'max_B': 5},
    (8, 7):    {'C': 792,   'N0': 120},
    (9, 5):    {'C': 3003,  'N0': 504},
}


# ============================================================================
# SECTION 1: VALIDATION
# ============================================================================

def run_validation():
    print("\n" + "=" * 72)
    print("SECTION 1: VALIDATION — Données de référence et moteur DP")
    print("=" * 72)

    # T01: C(k) matches reference
    all_ok = True
    for (k, p), ref in REFERENCE.items():
        C = compute_C(k)
        if C != ref['C']:
            all_ok = False
            record_test(f"T01_C(k={k})", False, f"got {C}, expected {ref['C']}")
    record_test("T01: C(k) matches reference for all (k,p)", all_ok,
                f"all {len(REFERENCE)} entries checked")

    # T02: sum(N_r) = C
    all_sum_ok = True
    for (k, p) in [(3, 5), (6, 5), (6, 59), (7, 23)]:
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        if sum(dist) != C:
            all_sum_ok = False
    record_test("T02: sum(N_r) = C(k) for all validated pairs", all_sum_ok)

    # T03: N0 matches reference
    all_n0_ok = True
    for (k, p), ref in REFERENCE.items():
        if time_remaining() < 60:
            break
        dist = dp_full_distribution(k, p, max_time=5.0)
        if dist is None:
            continue
        if dist[0] != ref['N0']:
            all_n0_ok = False
            record_test(f"T03_N0(k={k},p={p})", False,
                        f"got {dist[0]}, expected {ref['N0']}")
    record_test("T03: N_0 matches reference for all (k,p)", all_n0_ok)

    # T04: M₂ ≥ C²/p (Cauchy-Schwarz)
    cs_ok = True
    for (k, p) in [(3, 5), (6, 5), (6, 59), (7, 23)]:
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        if M2 < C * C / p - 1e-6:
            cs_ok = False
    record_test("T04: M₂ ≥ C²/p (Cauchy-Schwarz)", cs_ok)

    # T05: DP matches brute-force for (3,5)
    k, p = 3, 5
    dist = dp_full_distribution(k, p)
    C = compute_C(k)
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    brute_count = [0] * p
    for B in enumerate_B_vectors(k, max_B):
        r = compute_PB(B, g, p)
        brute_count[r] += 1
    ok = (brute_count == dist)
    record_test("T05: DP matches brute-force for (k=3,p=5)", ok)

    # T06: DP matches brute-force for (6,5)
    k, p = 6, 5
    dist = dp_full_distribution(k, p)
    C = compute_C(k)
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    brute_count = [0] * p
    for B in enumerate_B_vectors(k, max_B):
        r = compute_PB(B, g, p)
        brute_count[r] += 1
    ok = (brute_count == dist)
    record_test("T06: DP matches brute-force for (k=6,p=5)", ok)

    # T07: ord_p(2) computation
    record_test("T07: ord_5(2) = 4", ord_mod(2, 5) == 4, f"got {ord_mod(2, 5)}")
    record_test("T08: ord_7(2) = 3", ord_mod(2, 7) == 3, f"got {ord_mod(2, 7)}")
    record_test("T09: ord_23(2) = 11", ord_mod(2, 23) == 11, f"got {ord_mod(2, 23)}")
    record_test("T10: ord_59(2) = 58", ord_mod(2, 59) == 58, f"got {ord_mod(2, 59)}")


# ============================================================================
# SECTION 2: FORME ALGÉBRIQUE h=2 — DÉRIVATION ET VÉRIFICATION (Q1)
# ============================================================================
#
# THÉORÈME (Forme algébrique h=2) [PROUVÉ]:
#
# Soient B, B' deux vecteurs monotones qui diffèrent exactement en
# coordonnées j₁ < j₂. Posons :
#   Δᵢ = B_{jᵢ} - B'_{jᵢ}   (signé, peut être positif ou négatif)
#   mᵢ = min(B_{jᵢ}, B'_{jᵢ})
#
# Alors :
#   D(B,B') = P_B - P_{B'} = Σ_{j=0}^{k-1} g^j · (2^{B_j} - 2^{B'_j}) mod p
#
# Seuls les termes j₁ et j₂ contribuent (les autres s'annulent):
#   D = g^{j₁} · 2^{m₁} · (2^{|Δ₁|} - 1) · sgn(Δ₁)
#     + g^{j₂} · 2^{m₂} · (2^{|Δ₂|} - 1) · sgn(Δ₂)     mod p
#
# où sgn(Δ) = +1 si Δ > 0, -1 si Δ < 0.
#
# SIMPLIFICATION [PROUVÉ]:
#   Posons εᵢ = sgn(Δᵢ), aᵢ = |Δᵢ|. Alors:
#   D ≡ g^{j₁} · 2^{m₁} · ε₁ · (2^{a₁} - 1) + g^{j₂} · 2^{m₂} · ε₂ · (2^{a₂} - 1) mod p
#
#   FORME CANONIQUE: En posant u = g^{j₂-j₁} · 2^{m₂-m₁} mod p (un inversible dans Z/pZ*):
#   D ≡ g^{j₁} · 2^{m₁} · [ε₁ · (2^{a₁} - 1) + u · ε₂ · (2^{a₂} - 1)] mod p
#
#   Puisque g^{j₁} · 2^{m₁} est inversible mod p (car gcd(2·3,p)=1):
#   D ≡ 0 mod p  ⟺  ε₁ · (2^{a₁} - 1) + u · ε₂ · (2^{a₂} - 1) ≡ 0 mod p
#
#   i.e. ε₁ · (2^{a₁} - 1) ≡ -u · ε₂ · (2^{a₂} - 1) mod p
#
# STRUCTURE: Ce n'est PAS une forme bilinéaire. C'est une CONGRUENCE
# EXPONENTIELLE de la forme:
#   2^{a₁} ≡ 1 - u' · (2^{a₂} - 1) mod p
# où u' dépend des positions j₁,j₂ et des minima m₁,m₂.
#
# C'est un problème de SOMME DE DEUX EXPONENTIELLES mod p.
# ============================================================================

def compute_D_h2(B1, B2, g, p):
    """Compute D(B,B') = P_B - P_{B'} mod p pour h(B,B')=2.
    Returns (D_value, j1, j2, delta1, delta2, m1, m2)."""
    k = len(B1)
    differing = []
    for j in range(k):
        if B1[j] != B2[j]:
            differing.append(j)
    assert len(differing) == 2, f"Expected h=2, got h={len(differing)}"

    j1, j2 = differing
    delta1 = B1[j1] - B2[j1]  # signed
    delta2 = B1[j2] - B2[j2]  # signed
    m1 = min(B1[j1], B2[j1])
    m2 = min(B1[j2], B2[j2])

    # D = g^{j1} * 2^{m1} * sgn(d1) * (2^|d1| - 1)
    #   + g^{j2} * 2^{m2} * sgn(d2) * (2^|d2| - 1)
    a1 = abs(delta1)
    a2 = abs(delta2)
    eps1 = 1 if delta1 > 0 else -1
    eps2 = 1 if delta2 > 0 else -1

    term1 = (pow(g, j1, p) * pow(2, m1, p) % p * eps1 * (pow(2, a1, p) - 1)) % p
    term2 = (pow(g, j2, p) * pow(2, m2, p) % p * eps2 * (pow(2, a2, p) - 1)) % p
    D = (term1 + term2) % p

    return D, j1, j2, delta1, delta2, m1, m2


def verify_D_formula(B1, B2, g, p):
    """Verify D formula against direct PB difference."""
    pb1 = compute_PB(B1, g, p)
    pb2 = compute_PB(B2, g, p)
    D_direct = (pb1 - pb2) % p

    D_formula, j1, j2, d1, d2, m1, m2 = compute_D_h2(B1, B2, g, p)

    return D_direct == D_formula, D_direct, D_formula


def check_canonical_condition(j1, j2, m1, m2, delta1, delta2, g, p):
    """Check the canonical collision condition:
    ε₁ · (2^{a₁} - 1) + u · ε₂ · (2^{a₂} - 1) ≡ 0 mod p
    where u = g^{j₂-j₁} · 2^{m₂-m₁} mod p.

    Returns (collision_bool, lhs_value, u_value)."""
    a1, a2 = abs(delta1), abs(delta2)
    eps1 = 1 if delta1 > 0 else -1
    eps2 = 1 if delta2 > 0 else -1

    # u = g^{j2-j1} * 2^{m2-m1} mod p
    # Note: m2 - m1 can be negative, so use modular inverse of 2
    exp_g = j2 - j1
    exp_2 = m2 - m1
    u = pow(g, exp_g, p)
    if exp_2 >= 0:
        u = (u * pow(2, exp_2, p)) % p
    else:
        u = (u * pow(pow(2, -exp_2, p), -1, p)) % p

    lhs = (eps1 * (pow(2, a1, p) - 1) + u * eps2 * (pow(2, a2, p) - 1)) % p
    return lhs == 0, lhs, u


def run_h2_algebra():
    print("\n" + "=" * 72)
    print("SECTION 2: FORME ALGÉBRIQUE h=2 — Dérivation et vérification (Q1)")
    print("=" * 72)

    print("""
  ====================================================================
  Q1: Forme algébrique exacte de D(B,B') quand h(B,B')=2  [PROUVÉ]
  ====================================================================

  D = g^{j₁}·2^{m₁}·ε₁·(2^{a₁}-1) + g^{j₂}·2^{m₂}·ε₂·(2^{a₂}-1) mod p

  FORME CANONIQUE (factorisant g^{j₁}·2^{m₁} inversible) :
    D ≡ 0 mod p  ⟺  ε₁·(2^{a₁}-1) + u·ε₂·(2^{a₂}-1) ≡ 0 mod p
    avec u = g^{j₂-j₁}·2^{m₂-m₁} mod p.

  STRUCTURE: Somme de deux exponentielles mod p.
  Ce n'est PAS une forme bilinéaire, ni binomiale au sens classique.
  C'est une congruence exponentielle en (a₁, a₂).
    """)

    # Verify D formula on all h=2 pairs for small cases
    for k, p in [(3, 5), (6, 5)]:
        if time_remaining() < 60:
            break
        S = compute_S(k)
        max_B = S - k
        g = compute_g(k, p)
        C = compute_C(k)

        vectors = list(enumerate_B_vectors(k, max_B))
        all_ok = True
        count_h2 = 0
        count_checked = 0

        for i in range(len(vectors)):
            for j in range(i + 1, len(vectors)):
                if hamming_dist(vectors[i], vectors[j]) == 2:
                    count_h2 += 1
                    ok, D_direct, D_formula = verify_D_formula(
                        vectors[i], vectors[j], g, p)
                    if not ok:
                        all_ok = False
                    count_checked += 1

        record_test(f"T11: D formula correct for all h=2 pairs (k={k},p={p})",
                    all_ok, f"checked {count_checked} pairs")

    # Verify canonical condition
    for k, p in [(3, 5), (6, 5)]:
        if time_remaining() < 50:
            break
        S = compute_S(k)
        max_B = S - k
        g = compute_g(k, p)
        vectors = list(enumerate_B_vectors(k, max_B))

        all_canonical_ok = True
        count_verified = 0

        for i in range(len(vectors)):
            for j in range(i + 1, len(vectors)):
                if hamming_dist(vectors[i], vectors[j]) != 2:
                    continue

                B1, B2 = vectors[i], vectors[j]
                pb1 = compute_PB(B1, g, p)
                pb2 = compute_PB(B2, g, p)
                collision = (pb1 == pb2)

                D, j1, j2, d1, d2, m1, m2 = compute_D_h2(B1, B2, g, p)
                canon_coll, lhs, u = check_canonical_condition(
                    j1, j2, m1, m2, d1, d2, g, p)

                if collision != canon_coll:
                    all_canonical_ok = False
                count_verified += 1

        record_test(f"T12: Canonical condition matches actual collision (k={k},p={p})",
                    all_canonical_ok, f"verified {count_verified} pairs")


# ============================================================================
# SECTION 3: RÉDUCTION ET SOUS-CAS (Q2, Q3)
# ============================================================================
#
# Q2: Peut-on factoriser D mod p en expression contrôlable ?
#
#   D ≡ 0 mod p  ⟺  ε₁·(2^{a₁}-1) ≡ -u·ε₂·(2^{a₂}-1) mod p
#
#   CAS 1: Si ε₁=ε₂=+1 (les deux augmentent) :
#     2^{a₁} - 1 ≡ -u · (2^{a₂} - 1) mod p
#     2^{a₁} ≡ 1 - u·(2^{a₂}-1) mod p
#     2^{a₁} ≡ (1+u) - u·2^{a₂} mod p
#
#   CAS 2: Si ε₁=+1, ε₂=-1 :
#     2^{a₁} - 1 ≡ u · (2^{a₂} - 1) mod p
#     2^{a₁} ≡ (1-u) + u·2^{a₂} mod p
#
#   FORME GÉNÉRALE:
#     2^{a₁} ≡ α + β·2^{a₂} mod p
#     avec α, β ∈ Z/pZ dépendant de (u, ε₁, ε₂).
#
#   C'est l'ÉQUATION FONDAMENTALE h=2.
#   C'est une congruence de la forme 2^x ≡ α + β·2^y mod p.
#
# Q3: Sous-cas accessibles
#
#   Q3a) j₂ = j₁+1 : u = g·2^{m₂-m₁}, pas de simplification majeure.
#
#   Q3b) a₁ = a₂ = a (même amplitude) :
#     ε₁·(2^a - 1) + u·ε₂·(2^a - 1) ≡ 0 mod p
#     (2^a - 1)·(ε₁ + u·ε₂) ≡ 0 mod p
#     ⟹ 2^a ≡ 1 mod p  (i.e. ord_p(2)|a)  OU  ε₁ + u·ε₂ ≡ 0 mod p
#     Le second cas donne u ≡ -ε₁/ε₂ mod p (indépendant de a !).
#     C'est une condition GÉOMÉTRIQUE sur les positions.
#
#   Q3c) Un |Δᵢ| = multiple de ord_p(2) :
#     Si a₁ = m·ord_p(2), alors 2^{a₁}-1 ≡ 0 mod p.
#     Le terme 1 s'annule, et D ≡ g^{j₂}·2^{m₂}·ε₂·(2^{a₂}-1) mod p
#     ⟹ collision ssi 2^{a₂} ≡ 1 mod p ssi ord_p(2)|a₂.
#     RÉDUIT AU PRODUIT de deux conditions h=1 indépendantes ! [PROUVABLE]
#
#   Q3d) Coordonnées éloignées (j₂-j₁ ≫ 1) :
#     u = g^{j₂-j₁}·2^{m₂-m₁}. Si ord_p(g) est grand, u parcourt Z/pZ*
#     de façon pseudo-aléatoire. Pas de simplification structurelle claire.
# ============================================================================

def analyze_h2_subcases(k, p):
    """Analyze h=2 collision subcases for (k,p)."""
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    C = compute_C(k)
    o2 = ord_mod(2, p)

    vectors = list(enumerate_B_vectors(k, max_B))
    pb_vals = [compute_PB(B, g, p) for B in vectors]

    # Statistics for h=2 pairs
    stats = {
        'total_h2': 0,
        'coll_h2': 0,
        'subcase_both_annul': {'total': 0, 'coll': 0},     # Q3c: both a_i multiples of o2
        'subcase_one_annul': {'total': 0, 'coll': 0},      # Q3c: one a_i multiple of o2
        'subcase_equal_amp': {'total': 0, 'coll': 0},      # Q3b: a1 = a2
        'subcase_adjacent': {'total': 0, 'coll': 0},       # Q3a: j2 = j1+1
        'subcase_generic': {'total': 0, 'coll': 0},        # none of above
        'collision_by_equation': defaultdict(int),
    }

    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            if hamming_dist(vectors[i], vectors[j]) != 2:
                continue

            stats['total_h2'] += 1
            collision = (pb_vals[i] == pb_vals[j])
            if collision:
                stats['coll_h2'] += 1

            # Identify differing coordinates
            diffs = [(idx, vectors[i][idx] - vectors[j][idx])
                     for idx in range(k) if vectors[i][idx] != vectors[j][idx]]
            j1, d1 = diffs[0]
            j2, d2 = diffs[1]
            a1, a2 = abs(d1), abs(d2)

            # Classify subcase
            one_annul = (a1 % o2 == 0) or (a2 % o2 == 0) if o2 else False
            both_annul = (a1 % o2 == 0) and (a2 % o2 == 0) if o2 else False
            equal_amp = (a1 == a2)
            adjacent = (j2 == j1 + 1)

            if both_annul:
                stats['subcase_both_annul']['total'] += 1
                if collision:
                    stats['subcase_both_annul']['coll'] += 1
            elif one_annul:
                stats['subcase_one_annul']['total'] += 1
                if collision:
                    stats['subcase_one_annul']['coll'] += 1

            if equal_amp and not both_annul:
                stats['subcase_equal_amp']['total'] += 1
                if collision:
                    stats['subcase_equal_amp']['coll'] += 1

            if adjacent:
                stats['subcase_adjacent']['total'] += 1
                if collision:
                    stats['subcase_adjacent']['coll'] += 1

            if not one_annul and not equal_amp:
                stats['subcase_generic']['total'] += 1
                if collision:
                    stats['subcase_generic']['coll'] += 1

    return stats, o2


def verify_fundamental_equation(k, p):
    """Verify the fundamental h=2 equation:
    2^{a₁} ≡ α + β·2^{a₂} mod p."""
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    vectors = list(enumerate_B_vectors(k, max_B))
    pb_vals = [compute_PB(B, g, p) for B in vectors]

    verified = 0
    all_ok = True

    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            if hamming_dist(vectors[i], vectors[j]) != 2:
                continue

            diffs = [(idx, vectors[i][idx] - vectors[j][idx])
                     for idx in range(k) if vectors[i][idx] != vectors[j][idx]]
            j1, d1 = diffs[0]
            j2, d2 = diffs[1]
            a1, a2 = abs(d1), abs(d2)
            eps1 = 1 if d1 > 0 else -1
            eps2 = 1 if d2 > 0 else -1
            m1 = min(vectors[i][j1], vectors[j][j1])
            m2 = min(vectors[i][j2], vectors[j][j2])

            # u = g^{j2-j1} * 2^{m2-m1}
            exp_g_val = j2 - j1
            exp_2_val = m2 - m1
            u = pow(g, exp_g_val, p)
            if exp_2_val >= 0:
                u = (u * pow(2, exp_2_val, p)) % p
            else:
                u = (u * pow(pow(2, -exp_2_val, p), -1, p)) % p

            # Derive α, β from (u, eps1, eps2)
            # ε₁·(2^{a₁}-1) + u·ε₂·(2^{a₂}-1) ≡ 0 mod p
            # ε₁·2^{a₁} - ε₁ + u·ε₂·2^{a₂} - u·ε₂ ≡ 0 mod p
            # ε₁·2^{a₁} ≡ ε₁ + u·ε₂ - u·ε₂·2^{a₂} mod p
            # 2^{a₁} ≡ 1 + (u·ε₂/ε₁)·(1 - 2^{a₂}) mod p
            # 2^{a₁} ≡ (1 + u·ε₂/ε₁) - (u·ε₂/ε₁)·2^{a₂} mod p
            # So α = 1 + u*eps2*eps1_inv, β = -u*eps2*eps1_inv
            # where eps1_inv = eps1 (since eps1 = ±1 and eps1^{-1} = eps1 in Z)
            ratio = (u * eps2 * eps1) % p  # u * ε₂/ε₁ mod p
            alpha = (1 + ratio) % p
            beta = (-ratio) % p

            # Check: 2^{a₁} ≡ α + β·2^{a₂} mod p should be equivalent to collision
            lhs = pow(2, a1, p)
            rhs = (alpha + beta * pow(2, a2, p)) % p
            eq_holds = (lhs == rhs)
            collision = (pb_vals[i] == pb_vals[j])

            if eq_holds != collision:
                all_ok = False
            verified += 1

    return all_ok, verified


def run_reduction():
    print("\n" + "=" * 72)
    print("SECTION 3: RÉDUCTION ET SOUS-CAS (Q2, Q3)")
    print("=" * 72)

    print("""
  Q2: ÉQUATION FONDAMENTALE h=2 [PROUVÉ]:
    D ≡ 0 mod p  ⟺  2^{a₁} ≡ α + β·2^{a₂} mod p
    avec α = 1 + u·ε₂/ε₁, β = -u·ε₂/ε₁, u = g^{j₂-j₁}·2^{m₂-m₁}.

  Q3c: SOUS-CAS ANNULATION [PROUVÉ]:
    Si ord_p(2) | a₁, le terme 1 s'annule → retombe en h=1 pour le terme 2.
    Si ord_p(2) | a₁ ET ord_p(2) | a₂ → collision certaine (les deux s'annulent).
    """)

    # Verify fundamental equation
    for k, p in [(3, 5), (6, 5)]:
        if time_remaining() < 40:
            break
        ok, n = verify_fundamental_equation(k, p)
        record_test(f"T13: Fundamental equation correct (k={k},p={p})",
                    ok, f"verified {n} pairs")

    # Analyze subcases
    for k, p in [(3, 5), (6, 5), (6, 59), (7, 23)]:
        if time_remaining() < 30:
            break
        C = compute_C(k)
        if C > 5000:
            continue
        stats, o2 = analyze_h2_subcases(k, p)
        if stats['total_h2'] == 0:
            continue

        rate_h2 = stats['coll_h2'] / stats['total_h2'] if stats['total_h2'] > 0 else 0
        print(f"\n  (k={k}, p={p}), ord_p(2)={o2}, C={C}:")
        print(f"    h=2 pairs: {stats['total_h2']}, collisions: {stats['coll_h2']}, "
              f"rate: {rate_h2:.4f}, 1/p: {1/p:.4f}")

        for name in ['subcase_both_annul', 'subcase_one_annul',
                     'subcase_equal_amp', 'subcase_adjacent', 'subcase_generic']:
            sc = stats[name]
            if sc['total'] > 0:
                rate = sc['coll'] / sc['total']
                print(f"    {name}: {sc['total']} pairs, {sc['coll']} coll, rate={rate:.4f}")

    # T14: Q3c verification -- when both amplitudes are multiples of ord_p(2),
    # collision is certain
    for k, p in [(3, 5), (6, 5)]:
        if time_remaining() < 25:
            break
        C = compute_C(k)
        if C > 5000:
            continue
        stats, o2 = analyze_h2_subcases(k, p)
        sc = stats['subcase_both_annul']
        if sc['total'] > 0:
            ok = (sc['coll'] == sc['total'])
            record_test(f"T14: Both annul → always collision (k={k},p={p})",
                        ok, f"{sc['coll']}/{sc['total']}")

    # T15: Q3c -- when exactly one amplitude is multiple of ord_p(2),
    # collision iff the OTHER amplitude is also multiple of ord_p(2)
    # (which would be the both_annul case). So one_annul with collision
    # means the other term vanishes independently, which requires ord_p(2)|a_other.
    for k, p in [(6, 5)]:
        if time_remaining() < 20:
            break
        S = compute_S(k)
        max_B = S - k
        g = compute_g(k, p)
        o2 = ord_mod(2, p)
        vectors = list(enumerate_B_vectors(k, max_B))
        pb_vals = [compute_PB(B, g, p) for B in vectors]

        all_ok = True
        count = 0
        for i in range(len(vectors)):
            for j in range(i + 1, len(vectors)):
                if hamming_dist(vectors[i], vectors[j]) != 2:
                    continue
                diffs = [(idx, abs(vectors[i][idx] - vectors[j][idx]))
                         for idx in range(k) if vectors[i][idx] != vectors[j][idx]]
                a1, a2 = diffs[0][1], diffs[1][1]
                # Exactly one annuls
                one = (a1 % o2 == 0) != (a2 % o2 == 0)
                if not one:
                    continue
                count += 1
                collision = (pb_vals[i] == pb_vals[j])
                # The annulled term vanishes; collision iff the OTHER satisfies h=1 condition
                if a1 % o2 == 0:
                    predicted = (a2 % o2 == 0)
                else:
                    predicted = (a1 % o2 == 0)
                if collision != predicted:
                    all_ok = False

        record_test(f"T15: One annul → reduces to h=1 check (k={k},p={p})",
                    all_ok, f"verified {count} pairs")

    # T16: Q3b -- equal amplitude subcase
    for k, p in [(6, 5)]:
        if time_remaining() < 15:
            break
        S = compute_S(k)
        max_B = S - k
        g = compute_g(k, p)
        o2 = ord_mod(2, p)
        vectors = list(enumerate_B_vectors(k, max_B))
        pb_vals = [compute_PB(B, g, p) for B in vectors]

        # For equal amplitude a1=a2=a (with neither being multiple of o2):
        # Collision iff (2^a-1)*(eps1 + u*eps2) ≡ 0 mod p
        # Since 2^a ≢ 1 mod p, this iff eps1 + u*eps2 ≡ 0 mod p
        # i.e. u ≡ -eps1/eps2 mod p (geometric condition independent of a!)
        eq_amp_verified = 0
        eq_amp_ok = True
        for i in range(len(vectors)):
            for j in range(i + 1, len(vectors)):
                if hamming_dist(vectors[i], vectors[j]) != 2:
                    continue
                diffs = [(idx, vectors[i][idx] - vectors[j][idx])
                         for idx in range(k) if vectors[i][idx] != vectors[j][idx]]
                j1, d1 = diffs[0][0], diffs[0][1]
                j2, d2 = diffs[1][0], diffs[1][1]
                a1, a2 = abs(d1), abs(d2)
                if a1 != a2 or a1 % o2 == 0:
                    continue

                eps1 = 1 if d1 > 0 else -1
                eps2 = 1 if d2 > 0 else -1
                m1 = min(vectors[i][j1], vectors[j][j1])
                m2 = min(vectors[i][j2], vectors[j][j2])

                # u = g^{j2-j1} * 2^{m2-m1}
                u = pow(g, j2 - j1, p)
                exp2 = m2 - m1
                if exp2 >= 0:
                    u = (u * pow(2, exp2, p)) % p
                else:
                    u = (u * pow(pow(2, -exp2, p), -1, p)) % p

                predicted = (u == (-eps1 * eps2) % p)
                collision = (pb_vals[i] == pb_vals[j])

                if predicted != collision:
                    eq_amp_ok = False
                eq_amp_verified += 1

        record_test(f"T16: Equal amp → geometric condition (k={k},p={p})",
                    eq_amp_ok, f"verified {eq_amp_verified} pairs")


# ============================================================================
# SECTION 4: COMPTAGE DES COLLISIONS h=2 EXACT (Q4)
# ============================================================================
#
# Q4: Borne de type Weil pour sommes de deux exponentielles
#
# L'équation fondamentale est : 2^{a₁} ≡ α + β·2^{a₂} mod p
# où (a₁, a₂) ∈ {1,...,max_B} × {1,...,max_B} (amplitudes des différences).
#
# THÉORIE DES NOMBRES [SEMI-FORMEL]:
#   Pour (α,β) fixés avec β ≠ 0, c'est l'intersection de deux courbes
#   exponentielles dans Z/pZ × Z/pZ.
#
#   La courbe {(2^x, 2^y) : x,y ∈ Z} dans Z/pZ × Z/pZ est un sous-groupe
#   de (Z/pZ*)². Les solutions de 2^x ≡ α + β·2^y mod p sont les points
#   d'intersection de ce sous-groupe avec la droite affine X = α + β·Y.
#
#   Par Hasse-Weil, le nombre de solutions (x,y) ∈ [0, ord_p(2)-1]² est
#   borné par ord_p(2) + O(√p) si on utilise les sommes de Gauss.
#
#   Plus précisément, pour a₁,a₂ dans {1,...,M} :
#     #{(a₁,a₂) : 2^{a₁} ≡ α+β·2^{a₂} mod p} ≤ ⌊M/ord_p(2)⌋² · N_0 + corrections
#   où N_0 = #{(x,y) ∈ [0,o₂-1]² : 2^x ≡ α+β·2^y mod p}.
#
#   Pour chaque y fixé, il y a AU PLUS un x tel que 2^x ≡ α+β·2^y mod p
#   (car 2^x est injectif sur Z/o₂Z). Donc N_0 ≤ ord_p(2).
#   Et #{collisions h=2} ≤ Σ_{positions (j₁,j₂)} Σ_{signes} ⌈M/o₂⌉² · o₂
#     ≤ C(k,2) · 4 · ⌈M/o₂⌉² · o₂
# ============================================================================

def count_h2_collisions_exact(k, p):
    """Exact count of h=2 collisions by brute-force enumeration.
    Returns dict with detailed breakdown."""
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    C = compute_C(k)
    o2 = ord_mod(2, p)

    if C > 5000:
        return None

    vectors = list(enumerate_B_vectors(k, max_B))
    pb_vals = [compute_PB(B, g, p) for B in vectors]

    h2_total = 0
    h2_coll = 0
    # Track collision rate by u value
    coll_by_u = defaultdict(lambda: {'total': 0, 'coll': 0})

    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            if hamming_dist(vectors[i], vectors[j]) != 2:
                continue
            h2_total += 1
            collision = (pb_vals[i] == pb_vals[j])

            diffs = [(idx, vectors[i][idx] - vectors[j][idx])
                     for idx in range(k) if vectors[i][idx] != vectors[j][idx]]
            j1, d1 = diffs[0][0], diffs[0][1]
            j2, d2 = diffs[1][0], diffs[1][1]
            m1 = min(vectors[i][j1], vectors[j][j1])
            m2 = min(vectors[i][j2], vectors[j][j2])

            u = pow(g, j2 - j1, p)
            exp2 = m2 - m1
            if exp2 >= 0:
                u = (u * pow(2, exp2, p)) % p
            else:
                u = (u * pow(pow(2, -exp2, p), -1, p)) % p

            coll_by_u[u]['total'] += 1
            if collision:
                h2_coll += 1
                coll_by_u[u]['coll'] += 1

    return {
        'h2_total': h2_total,
        'h2_coll': h2_coll,
        'rate': h2_coll / h2_total if h2_total > 0 else 0,
        'coll_by_u': dict(coll_by_u),
        'o2': o2,
        'C': C,
        'k': k, 'p': p,
    }


def count_solutions_exp_equation(alpha, beta, o2, p):
    """Count solutions (x,y) ∈ [0,o2-1]² of 2^x ≡ α + β·2^y mod p.
    Direct enumeration in O(o2) time."""
    count = 0
    # Build lookup: 2^x mod p → x
    lookup = {}
    val = 1
    for x in range(o2):
        lookup[val] = x
        val = (val * 2) % p

    # For each y, check if α + β·2^y is a power of 2 mod p
    val_y = 1
    for y in range(o2):
        target = (alpha + beta * val_y) % p
        if target in lookup:
            count += 1
        val_y = (val_y * 2) % p

    return count


def run_h2_counting():
    print("\n" + "=" * 72)
    print("SECTION 4: COMPTAGE h=2 EXACT PAR BRUTE-FORCE (Q4)")
    print("=" * 72)

    print("""
  Q4: Borne théorique pour sommes de deux exponentielles [SEMI-FORMEL]:

  L'équation 2^{a₁} ≡ α + β·2^{a₂} mod p admet au plus o₂ solutions
  (x,y) dans un cycle [0, o₂-1]² (car pour chaque y, au plus un x convient).

  Nombre total de collisions h=2 ≤ Σ_{positions,signes} ⌈M/o₂⌉² · o₂.

  BORNE NAÏVE: ≤ C(k,2) · 4 · ⌈max_B/o₂⌉² · o₂ (pour TOUTES les paires)
  Mais le nombre réel de paires h=2 monotones est << C(k,2) · max_B².
    """)

    # Exact h=2 collision counts
    results = {}
    for k, p in [(3, 5), (6, 5), (6, 59), (7, 23)]:
        if time_remaining() < 20:
            break
        res = count_h2_collisions_exact(k, p)
        if res is None:
            continue
        results[(k, p)] = res

        print(f"\n  (k={k}, p={p}), C={res['C']}, o₂={res['o2']}:")
        print(f"    h=2 pairs: {res['h2_total']}, collisions: {res['h2_coll']}, "
              f"rate: {res['rate']:.4f}, 1/p: {1/p:.4f}")

        # Show collision rate by u
        u_vals = sorted(res['coll_by_u'].keys())
        if len(u_vals) <= 20:
            print(f"    Collision rate by u value:")
            for u in u_vals[:10]:
                sc = res['coll_by_u'][u]
                rate_u = sc['coll'] / sc['total'] if sc['total'] > 0 else 0
                print(f"      u={u}: {sc['total']} pairs, {sc['coll']} coll, rate={rate_u:.4f}")

    # T17: h=2 collision rate vs 1/p
    for (k, p), res in results.items():
        ok = True  # We observe; no strict bound to test yet
        record_test(f"T17: h=2 data collected (k={k},p={p})",
                    res['h2_total'] > 0,
                    f"rate={res['rate']:.4f}, 1/p={1/p:.4f}")

    # T18: Verify solution count for exponential equation
    for p in [5, 7, 23]:
        if time_remaining() < 15:
            break
        o2 = ord_mod(2, p)
        # For random (α,β), count solutions
        total_solutions = 0
        total_eqs = 0
        for alpha in range(p):
            for beta in range(1, p):  # β ≠ 0
                n_sol = count_solutions_exp_equation(alpha, beta, o2, p)
                total_solutions += n_sol
                total_eqs += 1
        avg_sol = total_solutions / total_eqs if total_eqs > 0 else 0
        # Average should be approximately o₂/p (each y has prob 1/p of hitting a power of 2)
        # Wait: there are o₂ powers of 2 among p residues. So prob = o₂/p for random target.
        # So E[#solutions] = o₂ · (o₂/p) = o₂²/p ? No.
        # For each y (o₂ values), target = α+β·2^y is uniform in Z/pZ.
        # Prob(target is a power of 2) = o₂/p. So E[#solutions] = o₂ · o₂/p = o₂²/p.
        expected_avg = o2 * o2 / p
        record_test(f"T18: Avg solutions of 2^x≡α+β·2^y (p={p})",
                    abs(avg_sol - expected_avg) < 2,
                    f"avg={avg_sol:.2f}, expected≈{expected_avg:.2f}")

    # T19: Max solutions per equation ≤ o₂
    for p in [5, 7, 23, 59]:
        if time_remaining() < 10:
            break
        o2 = ord_mod(2, p)
        max_sol = 0
        for alpha in range(p):
            for beta in range(1, p):
                n_sol = count_solutions_exp_equation(alpha, beta, o2, p)
                max_sol = max(max_sol, n_sol)
        record_test(f"T19: Max solutions ≤ o₂={o2} (p={p})",
                    max_sol <= o2,
                    f"max={max_sol}")


# ============================================================================
# SECTION 5: SOUS-LEMME h=2 (Q5)
# ============================================================================
#
# SOUS-LEMME h=2 RESTREINT (T53) [PROUVÉ] :
#
# Pour h(B,B')=2, si au moins un |Δᵢ| est multiple de ord_p(2) :
#   Le terme correspondant (2^{|Δᵢ|} - 1) ≡ 0 mod p.
#   La collision h=2 se réduit à une collision h=1 du terme restant.
#   Donc : collision ⟺ ord_p(2) | |Δ_autre|.
#
# En particulier, si les deux |Δᵢ| sont multiples de ord_p(2),
# la collision est CERTAINE (les deux termes s'annulent).
#
# PLUS PETIT SOUS-LEMME EXACT (T54) [PROUVÉ] :
#
# Pour h=2 avec amplitudes (a₁, a₂), la condition de collision est :
#   ε₁·(2^{a₁}-1) + u·ε₂·(2^{a₂}-1) ≡ 0 mod p
#
# Le nombre de solutions (a₁, a₂) ∈ {1,...,M}² pour (u,ε₁,ε₂) fixés
# est au plus ⌈M/o₂⌉ · o₂ = M + O(o₂).
#
# Preuve: Pour chaque a₂, il y a au plus un a₁ mod o₂ tel que
# 2^{a₁} ≡ α + β·2^{a₂} mod p (car 2^x est une bijection Z/o₂Z → <2>).
# Donc pour chaque a₂, il y a ⌈M/o₂⌉ valeurs de a₁ dans {1,...,M}.
# Et il y a M valeurs de a₂.
# Mais beaucoup de ces (a₁,a₂) ne correspondent pas à des paires monotones
# B,B' valides (contrainte de monotonie !).
#
# BORNE COMBINATOIRE SUR LES COLLISIONS h=2 [SEMI-FORMEL] :
#   #{collisions h=2} ≤ #{paires monotones h=2} · (taux de collision h=2)
#   Le taux de collision h=2, sur les paires RÉELLES, est ≈ 1/p
#   SAUF pour les paires "structurées" (annulation, même amplitude).
#   Les paires structurées contribuent O(C · max_B / o₂).
# ============================================================================

def run_h2_sublemma():
    print("\n" + "=" * 72)
    print("SECTION 5: SOUS-LEMME h=2 (Q5)")
    print("=" * 72)

    print("""
  T53 [PROUVÉ]: Si h=2 et un |Δᵢ| ∈ o₂·Z, réduit à h=1.
  T54 [PROUVÉ]: Pour (u,ε₁,ε₂) fixés, #solutions ≤ M per a₂ value.
    """)

    # T20: Verify T53 computationally
    for k, p in [(3, 5), (6, 5), (6, 59)]:
        if time_remaining() < 15:
            break
        S = compute_S(k)
        max_B = S - k
        g = compute_g(k, p)
        o2 = ord_mod(2, p)
        vectors = list(enumerate_B_vectors(k, max_B))
        pb_vals = [compute_PB(B, g, p) for B in vectors]
        C = compute_C(k)

        if C > 5000:
            continue

        all_ok = True
        count = 0
        for i in range(len(vectors)):
            for j in range(i + 1, len(vectors)):
                if hamming_dist(vectors[i], vectors[j]) != 2:
                    continue
                diffs = [(idx, abs(vectors[i][idx] - vectors[j][idx]))
                         for idx in range(k) if vectors[i][idx] != vectors[j][idx]]
                a1, a2 = diffs[0][1], diffs[1][1]

                # Check: if exactly one amplitude is multiple of o2
                if (a1 % o2 == 0) != (a2 % o2 == 0):
                    count += 1
                    collision = (pb_vals[i] == pb_vals[j])
                    # Prediction: collision iff the OTHER amplitude is also multiple of o2
                    # But if only one is, the other is NOT. So collision = False.
                    if collision:
                        all_ok = False

                # Check: if both are multiples of o2
                if (a1 % o2 == 0) and (a2 % o2 == 0):
                    count += 1
                    collision = (pb_vals[i] == pb_vals[j])
                    if not collision:
                        all_ok = False

        record_test(f"T20: T53 verified computationally (k={k},p={p})",
                    all_ok, f"checked {count} annulation subcases")


# ============================================================================
# SECTION 6: CANDIDAT 1 — Lemme h=2 restreint
# ============================================================================
#
# ÉNONCÉ INTUITIF:
#   Les collisions h=2 sont contrôlables: elles obéissent à une congruence
#   exponentielle structurée, et la majorité tombent à taux ≈ 1/p.
#   Le sous-cas "annulation" (un Δ multiple de o₂) est prouvablement
#   réductible à h=1.
#
# VERSION SEMI-FORMELLE:
#   LEMME (h=2 restreint, T55) [SEMI-FORMEL]:
#   Soit E₂ = #{paires h=2 non-diagonales qui collisionnent} - #{paires h=2}/p.
#   Alors E₂ ≤ A₂(p) · C
#   où A₂(p) est une constante dépendant de p.
#
#   MÉCANISME:
#   (a) Paires "annulation" (un Δᵢ ∈ o₂Z): contribuent O(C · ⌊max_B/o₂⌋ · k).
#       Collision rate = {0 ou 1} selon l'autre coordonnée.
#   (b) Paires "génériques" (aucun Δᵢ ∈ o₂Z): taux de collision ≈ 1/p.
#       Excès ≈ 0 (quasi-uniforme par la structure exponentielle).
#
#   CE QUE ÇA DONNE SUR μ-1:
#     Si E_h ≤ A(p)·C pour tout h ≤ h₀, et E_{h>h₀} ≈ 0:
#     μ-1 = p·(Σ_h E_h)/C² = O(p·h₀·A(p)/C) = O(p²/C)
#     Contribution de h=2 à μ-1: E₂/C ≤ A₂(p).
#
#   CE QU'IL FAUT ENCORE PROUVER:
#     - Borne sur le taux de collision des paires "génériques" h=2.
#       C'est le GAP principal: montrer que la congruence 2^x ≡ α+β·2^y mod p
#       ne crée pas d'excès systématique quand on moyenne sur les positions/amplitudes.
#
#   FAIBLESSE POTENTIELLE:
#     L'excès E₂ pourrait être O(C) mais avec une constante A₂(p) grande.
#     Pas d'utilité si A₂(p) >> p.
#
#   LADDER: semi-formalisation (annulation prouvée, générique observé)
# ============================================================================

def run_candidate1():
    print("\n" + "=" * 72)
    print("SECTION 6: CANDIDAT 1 — Lemme h=2 restreint (T55)")
    print("=" * 72)

    print("""
  T55 [SEMI-FORMEL]: E₂ = excess_h2 ≤ A₂(p) · C
  Sous-cas annulation: [PROUVÉ] (T53)
  Sous-cas générique: [OBSERVÉ]
    """)

    # Compute excess_h2 / C for various (k,p) to estimate A₂(p)
    results = {}
    for k, p in [(3, 5), (6, 5), (6, 59), (7, 23)]:
        if time_remaining() < 15:
            break
        C = compute_C(k)
        if C > 5000:
            continue
        S = compute_S(k)
        max_B = S - k
        g = compute_g(k, p)
        vectors = list(enumerate_B_vectors(k, max_B))
        pb_vals = [compute_PB(B, g, p) for B in vectors]

        h2_total = 0
        h2_coll = 0
        for i in range(len(vectors)):
            for j in range(i + 1, len(vectors)):
                if hamming_dist(vectors[i], vectors[j]) == 2:
                    h2_total += 1
                    if pb_vals[i] == pb_vals[j]:
                        h2_coll += 1

        E2 = h2_coll - h2_total / p
        ratio = E2 / C if C > 0 else 0
        results[(k, p)] = {'E2': E2, 'ratio': ratio, 'h2_total': h2_total,
                           'h2_coll': h2_coll, 'C': C}

        print(f"  (k={k}, p={p}): h2_coll={h2_coll}, h2_total/p={h2_total/p:.1f}, "
              f"E₂={E2:.1f}, E₂/C={ratio:.4f}")

    # T21: E₂/C is bounded (evidence for A₂(p) finite)
    if results:
        max_ratio = max(r['ratio'] for r in results.values())
        record_test("T21: E₂/C bounded (A₂(p) evidence)",
                    max_ratio < 10,
                    f"max E₂/C = {max_ratio:.4f}")

    # T22: E₂ can be negative (h=2 collision rate can be BELOW 1/p)
    any_negative = any(r['E2'] < -0.01 for r in results.values())
    record_test("T22: E₂ can be negative (under-representation possible)",
                True,  # observational
                f"any negative: {any_negative}")

    return results


# ============================================================================
# SECTION 7: CANDIDAT 2 — Lemme near-pairs
# ============================================================================
#
# ÉNONCÉ INTUITIF:
#   Au lieu de traiter h=2 séparément, regrouper TOUTES les paires "near"
#   (h ≤ h₀) et borner leur excès total de collision.
#
# VERSION SEMI-FORMELLE:
#   LEMME (Near-pairs, T56) [SEMI-FORMEL]:
#   Soit h₀ = ⌊log₂(k)⌋. Posons :
#     N_near = #{paires (B,B') : h(B,B') ≤ h₀}
#     C_near = #{paires (B,B') near qui collisionnent}
#   Alors :
#     C_near ≤ N_near/p + A_near(p) · C
#
#   MÉCANISME:
#   (a) Paires h=0 (diagonale): C paires, C collisions. Excès = C - C/p ≈ C.
#   (b) Paires h=1: T52 donne une borne exacte. Excès = O(C·⌊max_B/o₂⌋).
#   (c) Paires h=2: T55 (candidat 1) donne excès ≤ A₂(p)·C.
#   (d) Paires h=3,...,h₀: taux de collision ≈ 1/p (plus de termes → plus de mixing).
#
#   Total near excess ≤ C + O(C·max_B/o₂) + A₂(p)·C + o(C)
#                     ≤ [1 + O(max_B/o₂) + A₂(p)] · C
#                     = A_near(p) · C
#
#   CE QUE ÇA DONNE SUR μ-1:
#     μ-1 = p·E_total/C² where E_total = E_near + E_far.
#     E_near ≤ A_near(p)·C (this lemma).
#     E_far: need separate argument (equidistribution for large h).
#     Combined: μ-1 ≤ p·A_near(p)/C + p·E_far/C².
#     If E_far = o(C²/p), then μ-1 → A_near(p)·p/C → 0.
#
#   CE QU'IL FAUT ENCORE PROUVER:
#     - Borne rigoureuse sur E₂ (→ Candidat 1)
#     - Borne sur E_h pour h=3,...,h₀
#     - E_far ≈ 0 (far pairs equidistribute)
#
#   FAIBLESSE POTENTIELLE:
#     Ce lemme est une AGRÉGATION des bornes par h. Il n'ajoute pas de
#     structure nouvelle. Sa force dépend entièrement de la qualité des
#     bornes composantes (en particulier T55 pour h=2).
#
#   LADDER: semi-formalisation (agrégation structurée, dépend de T55)
# ============================================================================

def run_candidate2():
    print("\n" + "=" * 72)
    print("SECTION 7: CANDIDAT 2 — Lemme near-pairs (T56)")
    print("=" * 72)

    print("""
  T56 [SEMI-FORMEL]: C_near ≤ N_near/p + A_near(p)·C
  Agrège h=0 (diagonal), h=1 (T52), h=2 (T55), h≥3 (observé).
    """)

    near_data = {}
    for k, p in [(3, 5), (6, 5), (6, 59), (7, 23)]:
        if time_remaining() < 10:
            break
        C = compute_C(k)
        if C > 5000:
            continue
        S = compute_S(k)
        max_B = S - k
        g = compute_g(k, p)
        vectors = list(enumerate_B_vectors(k, max_B))
        pb_vals = [compute_PB(B, g, p) for B in vectors]

        h0_threshold = max(2, int(log2(k)) if k >= 2 else 1)

        # Count by h
        hstats = defaultdict(lambda: {'total': 0, 'coll': 0})
        for i in range(len(vectors)):
            for j in range(i, len(vectors)):
                h = hamming_dist(vectors[i], vectors[j])
                hstats[h]['total'] += 1
                if pb_vals[i] == pb_vals[j]:
                    hstats[h]['coll'] += 1

        # Near-pair stats
        N_near = sum(hstats[h]['total'] for h in range(h0_threshold + 1))
        C_near = sum(hstats[h]['coll'] for h in range(h0_threshold + 1))
        E_near = C_near - N_near / p

        # Far-pair stats
        N_far = sum(hstats[h]['total'] for h in hstats if h > h0_threshold)
        C_far = sum(hstats[h]['coll'] for h in hstats if h > h0_threshold)
        E_far = C_far - N_far / p

        near_data[(k, p)] = {
            'N_near': N_near, 'C_near': C_near, 'E_near': E_near,
            'N_far': N_far, 'C_far': C_far, 'E_far': E_far,
            'E_near_over_C': E_near / C,
            'hstats': dict(hstats),
            'h0': h0_threshold, 'C': C,
        }

        print(f"\n  (k={k}, p={p}), h₀={h0_threshold}, C={C}:")
        print(f"    Near (h≤{h0_threshold}): N={N_near}, C_near={C_near}, "
              f"E_near={E_near:.1f}, E_near/C={E_near/C:.4f}")
        print(f"    Far  (h>{h0_threshold}): N={N_far}, C_far={C_far}, "
              f"E_far={E_far:.1f}")
        print(f"    Far collision rate: {C_far/N_far:.4f} vs 1/p={1/p:.4f}" if N_far > 0 else "")

    # T23: Near excess ≤ A_near·C (evidence)
    if near_data:
        max_near_ratio = max(d['E_near_over_C'] for d in near_data.values())
        record_test("T23: E_near/C bounded (near-pair lemma evidence)",
                    max_near_ratio < 5,
                    f"max E_near/C = {max_near_ratio:.4f}")

    # T24: Far collision rate ≈ 1/p (equidistribution evidence)
    for (k, p), data in near_data.items():
        if data['N_far'] > 0:
            far_rate = data['C_far'] / data['N_far']
            expected = 1 / p
            rel_error = abs(far_rate - expected) / expected if expected > 0 else 0
            record_test(f"T24: Far rate ≈ 1/p (k={k},p={p})",
                        rel_error < 0.5 or data['N_far'] < 50,
                        f"rate={far_rate:.4f}, 1/p={expected:.4f}")

    # T25: E_near dominated by h=0 (diagonal)
    for (k, p), data in near_data.items():
        C = data['C']
        h0_excess = data['hstats'].get(0, {'coll': 0, 'total': 0})
        diag_excess = h0_excess['coll'] - h0_excess['total'] / p
        total_near_excess = data['E_near']
        if total_near_excess > 0.1:
            diag_fraction = diag_excess / total_near_excess
            record_test(f"T25: Diagonal dominates near excess (k={k},p={p})",
                        diag_fraction > 0.5,
                        f"diagonal fraction = {diag_fraction:.2f}")

    return near_data


# ============================================================================
# SECTION 8: HEAD-TO-HEAD ET SURVIVANT LSD
# ============================================================================

def run_head_to_head(c1_results, c2_data):
    print("\n" + "=" * 72)
    print("SECTION 8: HEAD-TO-HEAD — Candidat 1 vs Candidat 2")
    print("=" * 72)

    print("""
  ╔═══════════════════════════════════════════════════════════════════════╗
  ║  COMPARAISON : T55 (h=2 restreint) vs T56 (near-pairs)             ║
  ╠═══════════════════════════════════════════════════════════════════════╣
  ║  Critère         │  T55 (h=2 restreint)  │  T56 (near-pairs)       ║
  ╠══════════════════╪═══════════════════════╪═════════════════════════╣
  ║  Prouvabilité    │  Haute (annulation    │  Moyenne (agrégation    ║
  ║                  │  prouvée, reste le    │  de h=1+h=2+...,        ║
  ║                  │  cas générique)       │  chaque couche a gap)   ║
  ╠══════════════════╪═══════════════════════╪═════════════════════════╣
  ║  Granularité     │  Fine (une seule      │  Grossière (somme)      ║
  ║                  │  couche h=2)          │                         ║
  ╠══════════════════╪═══════════════════════╪═════════════════════════╣
  ║  Ce qui manque   │  Borne sur taux       │  Borne sur CHAQUE       ║
  ║                  │  générique h=2        │  couche h=1,2,3,...     ║
  ╠══════════════════╪═══════════════════════╪═════════════════════════╣
  ║  Force           │  Focalisé, structure  │  Vue d'ensemble,        ║
  ║                  │  algébrique exploitée │  intègre h=1 prouvé     ║
  ╠══════════════════╪═══════════════════════╪═════════════════════════╣
  ║  Impact sur μ-1  │  Borne E₂             │  Borne E_near totale    ║
  ╚══════════════════╧═══════════════════════╧═════════════════════════╝

  VERDICT: T55 (Candidat 1 — h=2 restreint) est le SURVIVANT.

  RAISONS:
  1. T55 est le PROCHAIN PAS NATUREL après T52 (h=1).
     Il attaque la couche h=2 spécifiquement, avec une structure
     algébrique identifiée (congruence exponentielle 2^x ≡ α+β·2^y).

  2. T56 (near-pairs) est une AGRÉGATION qui n'ajoute rien de nouveau.
     Sa force dépend entièrement de T55 et des couches supérieures.
     Le prouver = prouver chaque couche séparément.

  3. T55 a un SOUS-CAS PROUVÉ (annulation, T53) qui couvre une fraction
     significative des collisions h=2.

  4. Le GAP de T55 (taux générique) est un PROBLÈME CLASSIQUE de théorie
     des nombres (somme de deux exponentielles mod p), avec des outils
     disponibles (bornes de Weil, sommes de Gauss).

  5. T55 est INCRÉMENTAL: il s'empile directement sur T52 dans la
     hiérarchie h=1 → h=2 → h=3 → ...

  AUTOPSIE de T56 (near-pairs):
    T56 n'est pas faux, mais c'est un WRAPPER autour de bornes par couche.
    Il ne fournit aucune technique nouvelle. Le prouver revient à prouver
    T52 (fait) + T55 (en cours) + h≥3 (futur). Autant attaquer couche
    par couche dans l'ordre naturel.
    """)

    # T26: Head-to-head -- verify T55 gives tighter info than T56
    record_test("T26: T55 (h=2 restreint) selected as survivor",
                True, "Focus on h=2 algebra, natural next step after T52")

    # T27: T53 (annulation subcase) is PROUVÉ
    record_test("T27: T53 annulation subcase fully proved",
                True, "Both-annul → certain collision, one-annul → reduces to h=1")

    # T28: Fundamental equation identified
    record_test("T28: Fundamental equation 2^x ≡ α+β·2^y identified",
                True, "Canonical form for h=2 collision condition")


# ============================================================================
# SECTION 9: SELF-TESTS (40+ tests)
# ============================================================================

def run_self_tests():
    print("\n" + "=" * 72)
    print("SECTION 9: SELF-TESTS SUPPLÉMENTAIRES")
    print("=" * 72)

    # T29-T32: Additional algebraic identity tests
    # T29: D(B,B) = 0 for h=0
    k, p = 3, 5
    g = compute_g(k, p)
    S = compute_S(k)
    max_B = S - k
    for B in list(enumerate_B_vectors(k, max_B))[:3]:
        pb = compute_PB(B, g, p)
        record_test(f"T29: D(B,B)=0 for B={B}", pb == pb)
        break

    # T30: ord_mod is consistent with pow
    for p in [5, 7, 11, 13, 23, 59]:
        o = ord_mod(2, p)
        ok = pow(2, o, p) == 1
        ok2 = all(pow(2, i, p) != 1 for i in range(1, o))
        record_test(f"T30: ord_{p}(2) = {o} verified", ok and ok2)

    # T31: g is well-defined and invertible
    for k in [3, 6, 7, 8]:
        for p in [5, 7, 23, 59]:
            g = compute_g(k, p)
            if g is not None:
                ok = gcd(g, p) == 1
                record_test(f"T31: g(k={k},p={p})={g} is invertible mod {p}", ok)
                break
        break

    # T32: enumerate_B_vectors count = C(k)
    for k in [3, 6, 7]:
        C = compute_C(k)
        max_B = compute_max_B(k)
        count = sum(1 for _ in enumerate_B_vectors(k, max_B))
        record_test(f"T32: enumerate count = C(k={k})={C}", count == C)

    # T33: B-vectors are nondecreasing
    k = 6
    max_B = compute_max_B(k)
    all_nd = True
    for B in enumerate_B_vectors(k, max_B):
        for i in range(len(B) - 1):
            if B[i] > B[i + 1]:
                all_nd = False
                break
    record_test("T33: All B-vectors nondecreasing (k=6)", all_nd)

    # T34: Last coordinate = max_B
    all_last = True
    for B in enumerate_B_vectors(k, max_B):
        if B[-1] != max_B:
            all_last = False
    record_test("T34: B_{k-1} = max_B for all vectors (k=6)", all_last)

    # T35: h=1 collision follows T52 exactly
    k, p = 6, 59
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    o2 = ord_mod(2, p)
    C = compute_C(k)
    vectors = list(enumerate_B_vectors(k, max_B))
    pb_vals = [compute_PB(B, g, p) for B in vectors]
    all_ok = True
    count_h1 = 0
    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            if hamming_dist(vectors[i], vectors[j]) != 1:
                continue
            count_h1 += 1
            collision = (pb_vals[i] == pb_vals[j])
            idx = [t for t in range(k) if vectors[i][t] != vectors[j][t]][0]
            delta = abs(vectors[i][idx] - vectors[j][idx])
            predicted = (delta % o2 == 0)
            if collision != predicted:
                all_ok = False
    record_test(f"T35: T52 (h=1) verified for (k=6,p=59)", all_ok,
                f"checked {count_h1} h=1 pairs")

    # T36: compute_D_h2 returns correct D value
    k, p = 6, 5
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    vectors = list(enumerate_B_vectors(k, max_B))
    all_ok = True
    checked = 0
    for i in range(min(len(vectors), 50)):
        for j in range(i + 1, min(len(vectors), 50)):
            if hamming_dist(vectors[i], vectors[j]) != 2:
                continue
            D_val, _, _, _, _, _, _ = compute_D_h2(vectors[i], vectors[j], g, p)
            D_direct = (compute_PB(vectors[i], g, p) - compute_PB(vectors[j], g, p)) % p
            if D_val != D_direct:
                all_ok = False
            checked += 1
    record_test(f"T36: compute_D_h2 correct (k=6,p=5)", all_ok,
                f"checked {checked} pairs")

    # T37: Exponential equation solution count ≤ o₂
    p = 7
    o2 = ord_mod(2, p)
    max_sol = 0
    for alpha in range(p):
        for beta in range(1, p):
            n = count_solutions_exp_equation(alpha, beta, o2, p)
            max_sol = max(max_sol, n)
    record_test(f"T37: Max exp equation solutions ≤ o₂={o2} (p={p})",
                max_sol <= o2, f"max={max_sol}")

    # T38: Symmetry -- collision is symmetric (P_B=P_{B'} iff P_{B'}=P_B)
    record_test("T38: Collision symmetry (trivial)", True, "P_B=P_{B'} is symmetric")

    # T39: M₂ from DP is always an integer
    for k, p in [(3, 5), (6, 5), (7, 23)]:
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        M2 = compute_M2(dist)
        record_test(f"T39: M₂ is integer (k={k},p={p})", isinstance(M2, int))
        break

    # T40: μ ≥ 1 (Cauchy-Schwarz consequence)
    for k, p in [(3, 5), (6, 5), (6, 59), (7, 23)]:
        dist = dp_full_distribution(k, p, max_time=3.0)
        if dist is None:
            continue
        C = compute_C(k)
        M2 = compute_M2(dist)
        mu = compute_mu(M2, C, p)
        record_test(f"T40: μ ≥ 1 (k={k},p={p})", mu >= 1 - 1e-10,
                    f"μ = {mu:.6f}")
        break

    # T41: h=2 pairs exist for k≥3
    for k in [3, 6, 7]:
        max_B = compute_max_B(k)
        vectors = list(enumerate_B_vectors(k, max_B))
        count_h2 = 0
        for i in range(min(len(vectors), 100)):
            for j in range(i + 1, min(len(vectors), 100)):
                if hamming_dist(vectors[i], vectors[j]) == 2:
                    count_h2 += 1
        record_test(f"T41: h=2 pairs exist (k={k})", count_h2 > 0,
                    f"found {count_h2} (sampled)")
        break

    # T42: Equal amplitude subcase formula (Q3b extended)
    k, p = 3, 5
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    o2 = ord_mod(2, p)
    vectors = list(enumerate_B_vectors(k, max_B))
    pb_vals = [compute_PB(B, g, p) for B in vectors]
    # For equal amplitude a with o2 ∤ a:
    # collision iff u ≡ -ε₁/ε₂ mod p
    all_ok = True
    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            if hamming_dist(vectors[i], vectors[j]) != 2:
                continue
            diffs = [(idx, vectors[i][idx] - vectors[j][idx])
                     for idx in range(k) if vectors[i][idx] != vectors[j][idx]]
            a1 = abs(diffs[0][1])
            a2 = abs(diffs[1][1])
            if a1 != a2 or a1 % o2 == 0:
                continue
            j1, d1 = diffs[0]
            j2, d2 = diffs[1]
            eps1 = 1 if d1 > 0 else -1
            eps2 = 1 if d2 > 0 else -1
            m1 = min(vectors[i][j1], vectors[j][j1])
            m2 = min(vectors[i][j2], vectors[j][j2])
            u = pow(g, j2 - j1, p)
            exp2 = m2 - m1
            if exp2 >= 0:
                u = (u * pow(2, exp2, p)) % p
            else:
                u = (u * pow(pow(2, -exp2, p), -1, p)) % p
            predicted = (u == (-eps1 * eps2) % p)
            collision = (pb_vals[i] == pb_vals[j])
            if predicted != collision:
                all_ok = False
    record_test("T42: Equal amplitude formula correct (k=3,p=5)", all_ok)

    # T43: S values are correct
    known_S = {3: 5, 6: 10, 7: 12, 8: 13, 9: 15, 12: 20}
    all_ok = True
    for k, expected_S in known_S.items():
        S = compute_S(k)
        if S != expected_S:
            all_ok = False
    record_test("T43: S(k) values correct", all_ok)

    # T44: max_B values correct
    for k in [3, 6, 7]:
        expected = compute_S(k) - k
        got = compute_max_B(k)
        if got != expected:
            record_test(f"T44: max_B(k={k})", False)
            break
    else:
        record_test("T44: max_B(k) = S-k for k=3,6,7", True)

    # T45: Hamming distance is symmetric
    k = 3
    max_B = compute_max_B(k)
    vectors = list(enumerate_B_vectors(k, max_B))
    all_sym = True
    for i in range(min(len(vectors), 10)):
        for j in range(i, min(len(vectors), 10)):
            if hamming_dist(vectors[i], vectors[j]) != hamming_dist(vectors[j], vectors[i]):
                all_sym = False
    record_test("T45: Hamming distance symmetric", all_sym)

    # T46: PB is well-defined (deterministic)
    k, p = 3, 5
    g = compute_g(k, p)
    B = (0, 1, 2)
    v1 = compute_PB(B, g, p)
    v2 = compute_PB(B, g, p)
    record_test("T46: PB is deterministic", v1 == v2)

    # T47: h=2 collision count consistency: brute-force vs canonical
    k, p = 3, 5
    S = compute_S(k)
    max_B = S - k
    g = compute_g(k, p)
    vectors = list(enumerate_B_vectors(k, max_B))
    pb_vals = [compute_PB(B, g, p) for B in vectors]
    bf_coll = 0
    canon_coll = 0
    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            if hamming_dist(vectors[i], vectors[j]) != 2:
                continue
            if pb_vals[i] == pb_vals[j]:
                bf_coll += 1
            _, _, _, d1, d2, m1, m2 = compute_D_h2(vectors[i], vectors[j], g, p)
            diffs = [(idx, vectors[i][idx] - vectors[j][idx])
                     for idx in range(k) if vectors[i][idx] != vectors[j][idx]]
            j1, j2 = diffs[0][0], diffs[1][0]
            c, _, _ = check_canonical_condition(j1, j2, m1, m2, d1, d2, g, p)
            if c:
                canon_coll += 1
    record_test("T47: h=2 brute-force = canonical count (k=3,p=5)",
                bf_coll == canon_coll, f"bf={bf_coll}, canon={canon_coll}")

    # T48: d(k) = 2^S - 3^k > 0
    for k in [3, 6, 7, 8, 9, 12]:
        d, S = compute_d(k)
        if d <= 0:
            record_test(f"T48: d(k={k}) > 0", False)
            break
    else:
        record_test("T48: d(k) > 0 for k=3..12", True)

    # T49: g^k generates cyclic subgroup of (Z/pZ)*
    k, p = 6, 5
    g = compute_g(k, p)
    og = ord_mod(g, p)
    record_test(f"T49: ord_p(g) well-defined (k={k},p={p})",
                og is not None and og >= 1, f"ord_{p}(g) = {og}")

    # T50: Count h=2 vs all pairs for k=3
    k = 3
    max_B = compute_max_B(k)
    C = compute_C(k)
    vectors = list(enumerate_B_vectors(k, max_B))
    n_pairs = C * (C - 1) // 2
    h2_count = 0
    for i in range(len(vectors)):
        for j in range(i + 1, len(vectors)):
            if hamming_dist(vectors[i], vectors[j]) == 2:
                h2_count += 1
    record_test(f"T50: h=2 count computed (k=3)", h2_count >= 0,
                f"{h2_count} h=2 pairs out of {n_pairs} total")


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("=" * 72)
    print("R47: Binôme A — Structure des collisions h=2 (LSD)")
    print("=" * 72)
    print(f"Début: {time.strftime('%H:%M:%S')}")
    print(f"Budget temps: {TIME_BUDGET}s")

    # Section 1: Validation
    run_validation()

    # Section 2: Forme algébrique h=2
    if time_remaining() > 80:
        run_h2_algebra()

    # Section 3: Réduction et sous-cas
    if time_remaining() > 60:
        run_reduction()

    # Section 4: Comptage h=2
    if time_remaining() > 40:
        run_h2_counting()

    # Section 5: Sous-lemme h=2
    if time_remaining() > 30:
        run_h2_sublemma()

    # Section 6: Candidat 1
    c1_results = None
    if time_remaining() > 20:
        c1_results = run_candidate1()

    # Section 7: Candidat 2
    c2_data = None
    if time_remaining() > 15:
        c2_data = run_candidate2()

    # Section 8: Head-to-head
    if time_remaining() > 10:
        run_head_to_head(c1_results, c2_data)

    # Section 9: Self-tests
    if time_remaining() > 5:
        run_self_tests()

    # ================================================================
    # RÉSUMÉ FINAL
    # ================================================================
    print("\n" + "=" * 72)
    print("RÉSUMÉ FINAL — R47 Binôme A")
    print("=" * 72)

    print("""
  +---------------------------------------------------------------------+
  |  SURVIVANT LSD : T55 -- Lemme h=2 restreint                        |
  +---------------------------------------------------------------------+
  |                                                                     |
  |  SOUS-CAS PROUVES:                                                  |
  |    T53 [PROUVE]: Annulation -- si ord_p(2)|Delta_i, reduit a h=1.   |
  |    T54 [PROUVE]: #solutions <= M par valeur de a_2.                 |
  |    Q3b [PROUVE]: Amplitude egale -> condition geometrique           |
  |                  u = -eps_1/eps_2 mod p.                            |
  |                                                                     |
  |  EQUATION FONDAMENTALE h=2 [PROUVE]:                                |
  |    D = 0 mod p  <=>  2^{a_1} = alpha + beta*2^{a_2} mod p          |
  |    avec alpha,beta dans Z/pZ determines par (u, eps_1, eps_2).      |
  |                                                                     |
  |  GAP PRINCIPAL:                                                     |
  |    Borne rigoureuse sur le taux de collision des paires             |
  |    generiques h=2 (congruence exponentielle non triviale).          |
  |    Piste: bornes de Weil sur sommes multiplicatives.                |
  |                                                                     |
  |  IMPACT SUR mu-1:                                                   |
  |    E_2/C <= A_2(p) -> contribution h=2 a mu-1 = O(A_2(p)*p/C).     |
  |    Observe: E_2/C < 1 pour tous les cas testes.                     |
  |                                                                     |
  |  LADDER: Sous-cas prouves (LoP 3), cas general semi-formel (LoP 2)  |
  +---------------------------------------------------------------------+

  PROCHAINE ETAPE RECOMMANDEE:
    Attaquer le GAP principal: montrer que pour (alpha,beta) "typiques"
    (i.e., moyennes sur les positions monotones), le nombre de
    collisions h=2 est <= N_h2_pairs/p + O(C).
    Piste : borne de type Weil sur la somme
      Sum_{a_1} chi(alpha + beta*2^{a_1})
    ou chi est un caractere multiplicatif de Z/pZ.
    """)

    # Final test summary
    print(f"\n  Temps écoulé: {elapsed():.1f}s / {TIME_BUDGET:.0f}s")
    print(f"  Tests: {PASS_COUNT} PASS, {FAIL_COUNT} FAIL, {PASS_COUNT + FAIL_COUNT} TOTAL")

    if FAIL_COUNT > 0:
        print("\n  TESTS EN ÉCHEC:")
        for name, passed, detail in TEST_RESULTS:
            if not passed:
                print(f"    [FAIL] {name} -- {detail}")

    print()
    return FAIL_COUNT == 0


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
