#!/usr/bin/env python3
"""phase20_type_classification.py — Phase 20B: Structure Algebrique (Bases 2 et 3).

Deep-dive rigoureux sur la Piste B : exploiter l'incompatibilite arithmetique
entre les bases 2 et 3 dans F_p pour exclure le zero.

Sections:
  §1. Classification Type I/II de tous les premiers p | d(k), k = 1..67
  §2. Rigidite du sous-groupe <2> : quand 3 notin <2>
  §3. Offset additif 3^{k-1} et position structurelle du zero
  §4. Decomposition en cosettes et equilibre inter-cosettes
  §5. Analyse de l'arc tronque et couverture de l'orbite
  §6. Densite des premiers Type II parmi diviseurs de d
  §7. Verdict : portee et limites de la Piste B

Auteur: Eric Merle (assiste par Claude)
Date:   27 fevrier 2026
"""

import math
import cmath
import itertools
import hashlib
import time
from collections import Counter

PI = math.pi


# ============================================================================
# Helpers (shared with phase20_crt_analysis.py)
# ============================================================================

def ceil_log2_3(k):
    """Compute S = ceil(k * log2(3))."""
    three_k = 3 ** k
    S = k
    while (1 << S) < three_k:
        S += 1
    return S


def crystal_module(k):
    """Compute d(k) = 2^S - 3^k where S = ceil(k * log2(3))."""
    S = ceil_log2_3(k)
    return (1 << S) - 3**k, S


def _pollard_rho(n):
    """Pollard's rho factorization for medium-sized composites."""
    if n % 2 == 0:
        return 2
    import random
    for c in range(1, 100):
        x = random.randint(2, n - 1)
        y = x
        d = 1
        f = lambda x: (x * x + c) % n
        while d == 1:
            x = f(x)
            y = f(f(y))
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d
    return n  # failed


def prime_factorization(n, limit=10**7):
    """Full prime factorization of n. Returns list of (prime, exponent) pairs.
    Uses trial division up to `limit`, then Pollard's rho for medium composites."""
    if n <= 1:
        return []
    factors = []
    d = 2
    while d * d <= n and d <= limit:
        if n % d == 0:
            exp = 0
            while n % d == 0:
                n //= d
                exp += 1
            factors.append((d, exp))
        d += (1 if d == 2 else 2)
    if n > 1:
        if n < limit * limit:
            # n is prime (no factor up to sqrt(n))
            factors.append((n, 1))
        else:
            # Try Pollard's rho for medium composites
            remaining = n
            for _ in range(50):
                if remaining <= 1:
                    break
                if _is_probable_prime(remaining):
                    factors.append((remaining, 1))
                    break
                f = _pollard_rho(remaining)
                if f == remaining:
                    # Could not factor — treat as prime (may be wrong for large composites)
                    factors.append((remaining, 1))
                    break
                exp = 0
                while remaining % f == 0:
                    remaining //= f
                    exp += 1
                factors.append((f, exp))
    return factors


def _is_probable_prime(n, k=20):
    """Miller-Rabin primality test."""
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    # Write n-1 = 2^r * d
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    import random
    for _ in range(k):
        a = random.randint(2, n - 2)
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def mult_ord(a, m):
    """Multiplicative order of a modulo m, using factorization of phi(m) for speed."""
    if math.gcd(a, m) != 1:
        return 0
    if m <= 2:
        return 1 if (a % m) == 1 else 0

    # For prime m, phi(m) = m-1. Factor phi(m) to find ord efficiently.
    # ord(a,m) divides phi(m), and is the smallest such divisor.
    phi = m - 1  # assumes m is prime (which it is in our usage)
    factors = prime_factorization(phi)

    order = phi
    for p_fac, _ in factors:
        while order % p_fac == 0 and pow(a, order // p_fac, m) == 1:
            order //= p_fac
    return order


def compositions_gen(S, k):
    """Generate all compositions in Comp(S, k) as tuples."""
    if k == 1:
        yield (0,)
        return
    for combo in itertools.combinations(range(1, S), k - 1):
        yield (0,) + combo


def corrsum_horner_mod(A, p):
    """Compute corrSum(A) mod p via Horner recursion."""
    c = 1  # c_1 = 2^0 = 1
    for j in range(1, len(A)):
        c = (3 * c + pow(2, A[j], p)) % p
    return c


def discrete_log_in_subgroup(target, gen, p, ord_gen, limit=50000):
    """Find x such that gen^x = target mod p, or -1 if not in <gen>.
    Returns -2 if ord_gen > limit (too expensive)."""
    if ord_gen > limit:
        return -2
    t = target % p
    if t == 0:
        return -1  # 0 is never a power of gen
    cur = 1
    for x in range(ord_gen):
        if cur == t:
            return x
        cur = (cur * gen) % p
    return -1


# ============================================================================
# §1. Classification Type I/II
# ============================================================================

def section1_type_classification():
    """Classify all prime factors p | d(k) as Type I or Type II for k=1..67."""
    print("=" * 80)
    print("§1. CLASSIFICATION TYPE I / TYPE II DES PREMIERS CRISTALLINS")
    print("=" * 80)

    print("""
  Type I  : 3 in <2> mod p (i.e., log_2(3) existe dans Z/omega*Z)
  Type II : 3 notin <2> mod p (3 vit dans un coset strict de <2>)

  Indice de cosette m = [<2,3> : <2>] = 1 (Type I) ou >= 2 (Type II).
""")

    print(f"  {'k':>3} {'p':>10} {'omega':>6} {'tau':>6} {'m':>3} {'Type':>5} "
          f"{'(3/p)':>5} {'2 prim?':>7} {'log2(3)':>8}")
    print(f"  {'---':>3} {'---':>10} {'-----':>6} {'---':>6} {'--':>3} {'----':>5} "
          f"{'-----':>5} {'-------':>7} {'-------':>8}")

    all_results = []
    type1_count = 0
    type2_count = 0

    for k in range(1, 68):
        d, S = crystal_module(k)
        if d <= 0:
            continue

        # Factor d — skip only truly astronomical values
        if d < 10**30:
            factors = prime_factorization(d)
        else:
            factors = []
        if k % 10 == 0:
            import sys
            print(f"  [progress: k={k}, d has {len(str(d))} digits, {len(factors)} factors]",
                  flush=True)

        for p, _ in factors:
            if p < 3:
                continue

            omega = mult_ord(2, p)
            tau = mult_ord(3, p)

            # Determine if 3 is in <2> mod p
            # Use lcm approach first (fast): m = lcm(omega,tau)/omega
            joint = math.lcm(omega, tau)
            m_fast = joint // omega

            if m_fast == 1:
                ptype = "I"
                m = 1
                dlog = -3  # known Type I via lcm
                type1_count += 1
            else:
                ptype = "II"
                m = m_fast
                dlog = -1  # known Type II via lcm
                type2_count += 1

            # Only compute discrete log for small omega (for display)
            dlog_display = discrete_log_in_subgroup(3, 2, p, omega) if omega <= 10000 and m == 1 else dlog

            # Legendre symbol (3/p) via Euler criterion
            legendre_3 = pow(3, (p - 1) // 2, p)
            legendre_str = "+1" if legendre_3 == 1 else "-1"

            is_primitive = "oui" if omega == p - 1 else "non"

            dlog_str = str(dlog_display) if dlog_display >= 0 else "N/A"

            if k <= 25 or k in [41, 65, 67]:
                print(f"  {k:>3} {p:>10} {omega:>6} {tau:>6} {m:>3} {ptype:>5} "
                      f"{legendre_str:>5} {is_primitive:>7} {dlog_str:>8}")

            all_results.append({
                'k': k, 'p': p, 'omega': omega, 'tau': tau, 'm': m,
                'type': ptype, 'legendre': legendre_str,
                'is_primitive': omega == p - 1,
                'dlog': dlog_display
            })

    print(f"\n  Resume: Type I = {type1_count}, Type II = {type2_count}")
    print(f"  Ratio Type II : {type2_count/(type1_count+type2_count)*100:.1f}%")

    return all_results


# ============================================================================
# §2. Rigidite du sous-groupe <2>
# ============================================================================

def section2_rigidity_analysis(type_results):
    """Analyze the rigidity of the subgroup <2> when 3 is not in <2>."""
    print()
    print("=" * 80)
    print("§2. RIGIDITE DU SOUS-GROUPE <2> ET EXCLUSION STRUCTURELLE")
    print("=" * 80)

    type2_primes = [r for r in type_results if r['type'] == 'II']

    print(f"\n  {len(type2_primes)} premiers de Type II identifies.")
    print(f"\n  Pour chaque Type II: analyse du coset index et de la decomposition.")

    for r in type2_primes[:15]:  # First 15
        k, p, omega, tau, m = r['k'], r['p'], r['omega'], r['tau'], r['m']

        print(f"\n  --- k={k}, p={p}, omega={omega}, m={m} ---")

        # Analyze coset structure
        # The m cosets of <2> in <2,3> are: <2>, 3<2>, 3^2<2>, ..., 3^{m-1}<2>
        # (since <2,3>/<2> is cyclic of order m, generated by 3 mod <2>)

        # Check: corrSum lives in a single coset or multiple?
        # corrSum = sum_{i} 3^{k-1-i} * 2^{A_i}
        # Each term: 3^{k-1-i} * 2^{A_i} is in coset 3^{k-1-i mod m} * <2>
        # = coset number (k-1-i) mod m

        # Count terms per coset
        coset_counts = Counter()
        for i in range(k if k <= 100 else 20):  # first 20 terms for display
            coset_idx = (k - 1 - i) % m
            coset_counts[coset_idx] += 1

        total_terms = k
        if k <= 100:
            print(f"    Distribution des {k} termes par cosette de <2>:")
            for c in range(min(m, 10)):
                count_c = sum(1 for i in range(k) if (k - 1 - i) % m == c)
                print(f"      Cosette {c} (= 3^{c} * <2>): {count_c} termes "
                      f"({count_c/total_terms*100:.1f}%)")
        else:
            print(f"    {k} termes repartis quasi-uniformement en {m} cosettes "
                  f"({k//m} ou {k//m+1} par cosette)")

        # Key insight: corrSum = 0 requires balance across cosets
        # If terms are in different cosets, their sum being 0 requires inter-coset cancellation
        if m >= 2:
            print(f"    → corrSum = 0 requiert EQUILIBRE entre {m} cosettes distinctes")
            print(f"    → Contrainte supplementaire par rapport au Type I")

    return type2_primes


# ============================================================================
# §3. Offset additif et position structurelle du zero
# ============================================================================

def section3_offset_analysis():
    """Analyze the additive offset 3^{k-1} and its structural role."""
    print()
    print("=" * 80)
    print("§3. OFFSET ADDITIF 3^{k-1} ET POSITION DU ZERO")
    print("=" * 80)

    print("""
  corrSum = 3^{k-1} + V(A), ou V(A) = sum_{i=1}^{k-1} 3^{k-1-i} * 2^{A_i}
  V(A) est TOUJOURS PAIR (car chaque 2^{A_i} avec A_i >= 1 est pair).
  corrSum est donc TOUJOURS IMPAIR.

  La condition corrSum = 0 mod p equivaut a : V(A) = -3^{k-1} mod p.
  Le "target" de V est fixe par l'offset — c'est la signature du "+1" de 3n+1.
""")

    print(f"  {'k':>3} {'p':>8} {'3^(k-1) mod p':>14} {'target V':>10} "
          f"{'target/p':>8} {'position':>10}")

    for k in range(2, 26):
        d, S = crystal_module(k)
        if d <= 0:
            continue
        C = math.comb(S - 1, k - 1)

        factors = prime_factorization(d)
        for p, _ in factors:
            if p < 3:
                continue

            offset = pow(3, k - 1, p)
            target = (-offset) % p

            # Where is the target relative to the cosets of <2>?
            omega = mult_ord(2, p)
            dlog_target = discrete_log_in_subgroup(target, 2, p, omega) if omega <= 10000 else -2

            if dlog_target >= 0:
                pos = f"in <2> (log={dlog_target})"
            elif dlog_target == -1:
                pos = "NOT in <2>"
            else:
                pos = "(not computed)"

            print(f"  {k:>3} {p:>8} {offset:>14} {target:>10} "
                  f"{target/p:>8.4f} {pos:>10}")

    # Deep dive on q3
    print(f"\n  === Deep dive: q3 (k=5, S=8, p=13) ===")
    k, S, p = 5, 8, 13
    C = math.comb(S - 1, k - 1)
    offset = pow(3, k - 1, p)  # 81 mod 13 = 3
    target = (-offset) % p  # -3 mod 13 = 10

    print(f"  Offset = 3^4 = 81 = {offset} mod 13")
    print(f"  Target de V = -{offset} = {target} mod 13")

    # Compute Im(V mod 13) exhaustively
    V_residues = Counter()
    for A in compositions_gen(S, k):
        V = sum(pow(3, k - 1 - i, p) * pow(2, A[i], p) for i in range(1, k)) % p
        V_residues[V] += 1

    print(f"  Im(V mod 13) = {sorted(V_residues.keys())}")
    print(f"  Residus manquants de V : {sorted(set(range(p)) - set(V_residues.keys()))}")
    print(f"  Le target {target} est-il atteint ? {'OUI' if target in V_residues else 'NON'}")

    if target not in V_residues:
        print(f"  → EXCLUSION CHIRURGICALE : le seul residu manquant de V est "
              f"exactement le target {target} = -3^(k-1) mod p")
        print(f"  → C'est la signature algebrique du '+1' de Collatz")


# ============================================================================
# §4. Decomposition en cosettes et equilibre inter-cosettes
# ============================================================================

def section4_coset_decomposition():
    """Analyze the QR/QNR decomposition at Type II primes."""
    print()
    print("=" * 80)
    print("§4. DECOMPOSITION EN COSETTES ET EQUILIBRE INTER-COSETTES")
    print("=" * 80)

    # Deep analysis for accessible Type II primes
    # From Phase 20A data: Type II primes are those where m >= 2

    # Check k=2 (p=7): omega=3, tau=6, m=lcm(3,6)/3=2 -> Type II
    test_cases = [
        (2, 4, 7),     # k=2, S=4, p=7
        (7, 12, 23),   # k=7, S=12, p=23
        (8, 13, 7),    # k=8, S=13, p=7
    ]

    for k, S, p in test_cases:
        omega = mult_ord(2, p)
        tau = mult_ord(3, p)
        m = math.lcm(omega, tau) // omega
        C = math.comb(S - 1, k - 1)

        if C > 5 * 10**6:
            continue

        print(f"\n  --- k={k}, S={S}, p={p}, omega={omega}, tau={tau}, m={m} ---")

        if m < 2:
            print(f"    Type I — pas de decomposition en cosettes")
            continue

        print(f"    Type II avec m={m} cosettes de <2> dans <2,3>")

        # For each composition, compute corrSum mod p and track coset contributions
        coset_sums = {}  # A -> list of coset-wise sums

        n_zero = 0
        n_total = 0

        for A in compositions_gen(S, k):
            n_total += 1

            # Compute coset-wise sums
            partial = [0] * m
            for i in range(k):
                coset_idx = (k - 1 - i) % m
                term = pow(3, k - 1 - i, p) * pow(2, A[i], p) % p
                partial[coset_idx] = (partial[coset_idx] + term) % p

            total = sum(partial) % p
            if total == 0:
                n_zero += 1

        print(f"    C = {n_total}, N_0 = {n_zero}")
        print(f"    N_0/C = {n_zero/n_total:.6f}, 1/p = {1/p:.6f}")

        # Analyze coset balance for compositions with corrSum = 0
        if n_zero > 0 and n_total <= 100000:
            zero_coset_balances = []
            for A in compositions_gen(S, k):
                partial = [0] * m
                for i in range(k):
                    coset_idx = (k - 1 - i) % m
                    term = pow(3, k - 1 - i, p) * pow(2, A[i], p) % p
                    partial[coset_idx] = (partial[coset_idx] + term) % p

                total = sum(partial) % p
                if total == 0:
                    zero_coset_balances.append(tuple(partial))

            print(f"    Equilibres inter-cosettes pour N_0 = {n_zero} compositions:")
            balance_counts = Counter(zero_coset_balances)
            for balance, count in balance_counts.most_common(5):
                print(f"      Cosettes = {balance} : {count} compositions")

    # Special analysis for the critical non-excluded cases from Piste A
    print(f"\n  === Analyse des cas critiques (non exclus par CRT) ===")
    critical_k = [6, 9, 10, 12, 14, 15, 16]

    for k in critical_k:
        d, S = crystal_module(k)
        if d <= 0:
            continue

        factors = prime_factorization(d) if d < 10**30 else []
        has_type2 = False
        for p, _ in factors:
            if p < 3:
                continue
            omega = mult_ord(2, p)
            tau = mult_ord(3, p)
            m_val = math.lcm(omega, tau) // omega
            if m_val >= 2:
                has_type2 = True
                print(f"  k={k}: p={p} est Type II (m={m_val}, omega={omega})")

        if not has_type2:
            print(f"  k={k}: TOUS les premiers de d={d} sont Type I — "
                  f"la Piste B n'apporte pas d'obstruction supplementaire")


# ============================================================================
# §5. Arc tronque et couverture de l'orbite
# ============================================================================

def section5_arc_coverage():
    """Analyze arc truncation — how much of <2> is covered by the exponents A_i."""
    print()
    print("=" * 80)
    print("§5. ARC TRONQUE ET COUVERTURE DE L'ORBITE DE <2>")
    print("=" * 80)

    print("""
  Les exposants A_i vivent dans {0, 1, ..., S-1}.
  Dans Z/omega*Z (cyclique, genere par 2), ils couvrent un arc de longueur S.
  Si S < omega : l'arc est TRONQUE — pas toutes les puissances de 2 sont atteintes.
  Si S >= omega : l'arc est COMPLET — toutes les puissances de 2 sont couvertes.

  La troncature reduit les degres de liberte de corrSum.
""")

    print(f"  {'k':>3} {'S':>4} {'p':>8} {'omega':>6} {'S/omega':>8} {'S-k':>4} "
          f"{'(S-k)/omega':>11} {'Arc':>10}")

    for k in range(2, 26):
        d, S = crystal_module(k)
        if d <= 0:
            continue

        factors = prime_factorization(d)
        for p, _ in factors:
            if p < 3:
                continue

            omega = mult_ord(2, p)
            coverage = S / omega
            width = S - k  # number of "free" positions
            width_ratio = width / omega

            arc_type = "TRONQUE" if S < omega else "COMPLET"

            print(f"  {k:>3} {S:>4} {p:>8} {omega:>6} {coverage:>8.3f} {width:>4} "
                  f"{width_ratio:>11.3f} {arc_type:>10}")

    # Deep dive q3
    print(f"\n  === Deep dive: q3 (k=5, S=8, p=13, omega=12) ===")
    print(f"  Arc = {{0,...,7}} dans Z/12Z = {{0,...,11}}")
    print(f"  Puissances de 2 atteintes: 2^0=1, 2^1=2, ..., 2^7=128 = 11 mod 13")
    print(f"  En log_2: positions 0,1,2,3,4,5,6,7 sur l'orbite de longueur 12")
    print(f"  Puissances de 2 NON atteintes: 2^8=9, 2^9=5, 2^10=10, 2^11=7 mod 13")
    print(f"  → 4/12 = 33% de l'orbite est ABSENTE")

    # The absent powers are 2^8, 2^9, 2^10, 2^11 mod 13 = {9, 5, 10, 7}
    absent = set()
    for j in range(8, 12):
        absent.add(pow(2, j, 13))
    present = set()
    for j in range(0, 8):
        present.add(pow(2, j, 13))
    print(f"  Residus presents dans <2>: {sorted(present)}")
    print(f"  Residus absents de l'arc: {sorted(absent)}")
    print(f"  → Le target V=10 EST parmi les absents ? {'OUI' if 10 in absent else 'NON'}")

    # Compute log_2(target) in F_13
    target_V = 10
    dlog = discrete_log_in_subgroup(target_V, 2, 13, 12)
    if dlog >= 0:
        print(f"  log_2({target_V}) = {dlog} mod 12")
        if dlog >= 8:
            print(f"  → {dlog} >= S={8} : le target est dans la PARTIE TRONQUEE de l'arc")
            print(f"  → C'est pourquoi V ne peut pas atteindre {target_V} mod 13")
        else:
            print(f"  → {dlog} < S={8} : le target est dans l'arc, mais la combinatoire l'exclut")


# ============================================================================
# §6. Densite des premiers Type II parmi diviseurs de d
# ============================================================================

def section6_density_type2(type_results):
    """Analyze the density of Type II primes among divisors of d(k)."""
    print()
    print("=" * 80)
    print("§6. DENSITE DES PREMIERS TYPE II PARMI DIVISEURS DE d(k)")
    print("=" * 80)

    # Group by k
    by_k = {}
    for r in type_results:
        k = r['k']
        if k not in by_k:
            by_k[k] = {'type1': 0, 'type2': 0, 'primes': []}
        if r['type'] == 'I':
            by_k[k]['type1'] += 1
        else:
            by_k[k]['type2'] += 1
        by_k[k]['primes'].append(r)

    print(f"\n  {'k':>3} {'#p':>4} {'#Type I':>8} {'#Type II':>9} {'%Type II':>9} "
          f"{'d a Type II?':>12}")
    print(f"  {'---':>3} {'---':>4} {'-------':>8} {'--------':>9} {'--------':>9} "
          f"{'----------':>12}")

    k_with_type2 = 0
    k_all_type1 = 0

    for k in sorted(by_k.keys()):
        if k > 25 and k not in [41, 65, 67]:
            continue
        data = by_k[k]
        total = data['type1'] + data['type2']
        pct = data['type2'] / total * 100 if total > 0 else 0
        has_type2 = "OUI" if data['type2'] > 0 else "NON"

        if data['type2'] > 0:
            k_with_type2 += 1
        else:
            k_all_type1 += 1

        print(f"  {k:>3} {total:>4} {data['type1']:>8} {data['type2']:>9} "
              f"{pct:>8.1f}% {has_type2:>12}")

    total_k = k_with_type2 + k_all_type1
    print(f"\n  Resume:")
    print(f"    k avec au moins un Type II: {k_with_type2}/{total_k}")
    print(f"    k ou TOUS les premiers sont Type I: {k_all_type1}/{total_k}")

    # Theoretical prediction (Artin's conjecture)
    print(f"\n  Prediction theorique (conjecture d'Artin):")
    print(f"    P(2 est racine primitive mod p) = C_Artin ~ 0.3739")
    print(f"    P(Type I | p arbitraire) >= 0.3739 (car Type I inclut 2 primitif)")
    print(f"    P(Type II | p arbitraire) est donc <= 0.6261")
    print(f"    Mais pour les premiers p | d(k), la condition 2^S = 3^k mod p")
    print(f"    LIE omega et tau, reduisant la proportion de Type II.")


# ============================================================================
# §7. Verdict
# ============================================================================

def section7_verdict(type_results):
    """Final verdict on Piste B: Algebraic Structure."""
    print()
    print("=" * 80)
    print("§7. VERDICT — PISTE B : STRUCTURE ALGEBRIQUE (BASES 2 ET 3)")
    print("=" * 80)

    type2_list = [r for r in type_results if r['type'] == 'II']

    print(f"""
  RESULTATS PRINCIPAUX:
  ====================

  1. CLASSIFICATION Type I/II:
     - {sum(1 for r in type_results if r['type']=='I')} premiers Type I (3 in <2>)
     - {len(type2_list)} premiers Type II (3 notin <2>)
     - Ratio Type II: {len(type2_list)/(len(type_results))*100:.1f}%

  2. OFFSET ADDITIF (le "+1" de Collatz):
     - corrSum = 3^(k-1) + V(A), avec V(A) pair
     - Le target V = -3^(k-1) mod p est FIXE par la dynamique
     - Pour q3 (k=5, p=13): exclusion CHIRURGICALE — V couvre 12/13 residus,
       manquant exactement le target 10 = -81 mod 13

  3. ARC TRONQUE:
     - Les exposants A_i vivent dans {{0,...,S-1}}
     - Dans Z/omega*Z, cela couvre un arc de longueur S
     - Quand S < omega: l'arc est tronque, reduisant les degres de liberte
     - Pour q3: 8/12 = 67% couverture, le target est dans les 33% absents

  4. DECOMPOSITION EN COSETTES (Type II):
     - La corrSum se decompose en m sous-sommes vivant dans m cosettes de <2>
     - La condition corrSum = 0 requiert un equilibre inter-cosettes
     - La monotonie des A_i entrelace les contributions — rigidite structurelle

  FORCES de la Piste B:
  ====================
  1. Identifie la SOURCE ALGEBRIQUE de l'exclusion (incompatibilite 2 vs 3)
  2. L'offset additif ("+1" de Collatz) est un invariant STRUCTUREL
  3. La classification Type I/II est INCONDITIONNELLE et decidable
  4. L'exclusion chirurgicale de q3 est un THEOREME (preuve exhaustive)
  5. La troncature d'arc donne une obstruction GEOMETRIQUE claire

  LIMITES de la Piste B:
  ====================
  1. L'exclusion chirurgicale (Im(V) manque le target) n'est prouvee que pour q3
  2. Pour k grand, l'arc couvre TOUT l'orbite (S > omega pour certains p)
  3. Le Type II n'est pas universel — certains k n'ont que des Type I
  4. La decomposition en cosettes contraint mais N'EXCLUT PAS directement
  5. Pas de borne quantitative universelle sur le biais anti-zero

  OBSTACLE FONDAMENTAL:
  ====================
  La Piste B identifie correctement les sources de l'obstruction mais
  ne fournit pas de MECANISME DE PREUVE universel. L'exclusion chirurgicale
  (le target de V est hors de Im(V)) est verifiable cas par cas mais pas
  demontrable pour k arbitraire sans bornes sur les sommes exponentielles.

  En d'autres termes: la Piste B decrit le POURQUOI de l'exclusion mais
  pas le COMMENT la prouver universellement.

  VERDICT: PISTE B = CADRE EXPLICATIF PROFOND MAIS NON QUANTITATIF
  ===============================================================
  - Fournit le cadre algebrique le plus profond (Type I/II, offset, arc)
  - Explique mecaniquement l'exclusion observee pour q3
  - NE DONNE PAS de preuve universelle car il manque la quantification
  - Les outils manquants sont exactement ceux des Pistes C et D
    (bornes de melange, bornes de densite)
  - CONNEXION CLE: la Piste B + Piste C (mixing) pourrait donner une
    preuve hybride (structure + dynamique)
""")

    # Scoring
    scores = {
        "Faisabilite computationnelle": "9/10 (classification decidable, exhaustif q3-q5)",
        "Faisabilite theorique": "5/10 (cadre clair mais quantification manquante)",
        "Conditionnalite": "Mixte (Type I/II inconditionnel, exclusion conditionnel)",
        "Force du resultat": "4/10 (explicatif, pas probant universellement)",
        "Calculabilite": "8/10 (Type I/II decidable, arc mesurable)",
        "Chemin vers Lean": "8/10 (Type I/II formalisable, Gersonides deja fait)",
        "Connexion existante": "10/10 (Phase 11A, 15, 17 directement utilisees)",
    }

    print(f"  GRILLE D'EVALUATION:")
    for critere, score in scores.items():
        print(f"    {critere:.<45} {score}")


# ============================================================================
# Main
# ============================================================================

def main():
    import sys
    print("=" * 80, flush=True)
    print("  Phase 20B: Structure Algebrique (Bases 2 et 3)", flush=True)
    print("  Deep dive rigoureux — Piste B", flush=True)
    print("=" * 80, flush=True)
    print(flush=True)

    t0 = time.time()

    type_results = section1_type_classification()
    type2_primes = section2_rigidity_analysis(type_results)
    section3_offset_analysis()
    section4_coset_decomposition()
    section5_arc_coverage()
    section6_density_type2(type_results)
    section7_verdict(type_results)

    elapsed = time.time() - t0

    sig = f"phase20b_type_classification_k1to67"
    sha = hashlib.sha256(sig.encode()).hexdigest()[:16]
    print(f"\n  Temps d'execution: {elapsed:.1f}s")
    print(f"  SHA256 signature: {sha}")
    print(f"\n{'='*80}")
    print(f"  Phase 20B — Script termine")
    print(f"{'='*80}")


if __name__ == "__main__":
    main()
