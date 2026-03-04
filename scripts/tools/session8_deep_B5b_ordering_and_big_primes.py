#!/usr/bin/env python3
"""
SESSION 8 — APPROFONDISSEMENT B5b : CONTRAINTE D'ORDRE + GROS PREMIERS
========================================================================
Suite de deep_prime_blocking.py.

DÉCOUVERTES CLÉS (Investigation 3 + 8) :
1. La contrainte d'ORDRE (positions strictement croissantes) est CRITIQUE
   → Sans elle, -1 est TOUJOURS atteint (image couvre Z/pZ)
2. Pour d composé, le PLUS GRAND facteur premier a toujours N₀(p) = 0
3. Les PETITS facteurs premiers ont N₀(p) > 0

QUESTIONS :
Q1. Pourquoi l'ordre crée-t-il le blocking ? Quel mécanisme exactement ?
Q2. Pour d composé, est-ce TOUJOURS le plus grand premier qui bloque ?
Q3. Le "threshold" entre petits/gros premiers, c'est quoi ?
Q4. Peut-on PROUVER que pour le plus grand p|d, N₀(p) = 0 ?
"""

from math import ceil, log2, gcd, comb
from itertools import combinations
from collections import defaultdict, Counter
import random
random.seed(42)

def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    C = comb(S - 1, k - 1)
    return S, d, C

def factorize(n):
    factors = {}
    d_val = 2
    while d_val * d_val <= n:
        while n % d_val == 0:
            factors[d_val] = factors.get(d_val, 0) + 1
            n //= d_val
        d_val += 1
    if n > 1:
        factors[n] = 1
    return factors

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

def ord_mod(a, m):
    if gcd(a, m) != 1: return None
    phi = 1
    for p, e in factorize(m).items():
        phi *= (p - 1) * p**(e - 1)
    order = phi
    for p, e in factorize(phi).items():
        for _ in range(e):
            if pow(a, order // p, m) == 1:
                order //= p
            else:
                break
    return order

# ============================================================
# INVESTIGATION A : Quantifier l'effet de l'ordre
# Retirer progressivement la contrainte d'ordre et observer
# ============================================================
def investigate_progressive_ordering(max_k=8):
    """
    Variantes de la contrainte d'ordre :
    V0 : positions strictement croissantes (original)
    V1 : positions croissantes (non strictes, avec répétitions)
    V2 : positions quelconques (sans ordre)
    V3 : positions croissantes mais avec gap minimum = 2

    Pour chaque variante, compter N₀ et comprendre quel "degré"
    de contrainte est nécessaire pour le blocking.
    """
    print("=" * 70)
    print("  INVESTIGATION A : Variantes de la contrainte d'ordre")
    print("=" * 70)

    for k in range(3, min(max_k + 1, 8)):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d

        print(f"\n  k={k}: p={p}, S={S}")

        # V0 : strictement croissant (original)
        v0_images = set()
        for combo in combinations(range(1, S), k - 1):
            A = (0,) + combo
            cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k)) % p
            v0_images.add(cs)

        # V3 : croissant avec gap minimum g
        for gap in [2, 3]:
            count_zero = 0
            total = 0
            for combo in combinations(range(1, S), k - 1):
                # Vérifier gap minimum
                A = (0,) + combo
                ok = all(A[j+1] - A[j] >= gap for j in range(k - 1))
                if not ok:
                    continue
                total += 1
                cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k)) % p
                if cs == 0:
                    count_zero += 1

            print(f"    Gap ≥ {gap}: {total} compositions, N₀ = {count_zero}")

        # V1 : positions dans {1,...,S-1} sans contrainte (échantillonnage)
        n_samples = 10000
        n_zero = 0
        for _ in range(n_samples):
            positions = sorted(random.choices(range(1, S), k=k-1))
            A = (0,) + tuple(positions)
            cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k)) % p
            if cs == 0:
                n_zero += 1
        print(f"    Non-strict (échant.): N₀ ≈ {n_zero}/{n_samples} = {n_zero/n_samples*100:.1f}%")
        print(f"    Taux attendu aléatoire : {100/p:.1f}%")

        print(f"    V0 (strict): |Image| = {len(v0_images)}/{p}, 0 ∈ Image = {0 in v0_images}")

# ============================================================
# INVESTIGATION B : Quel est le facteur premier qui bloque ?
# Pour k=6..18, identifier systématiquement le "blocking prime"
# ============================================================
def investigate_blocking_prime_pattern(max_k=20):
    """
    Pour chaque k, factoriser d et identifier :
    - Quels p | d ont N₀(p) = 0 (bloqueurs)
    - Quels p | d ont N₀(p) > 0 (non-bloqueurs)
    - Relation entre la TAILLE de p et son statut de bloqueur
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION B : Identification du blocking prime")
    print("=" * 70)

    results = []

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        facts = factorize(d)
        primes = sorted(facts.keys())

        if len(primes) == 1 and facts[primes[0]] == 1:
            # d est premier
            results.append((k, d, [(d, True)], True))
            print(f"\n  k={k}: d={d} PREMIER → blocking automatique")
            continue

        print(f"\n  k={k}: d={d} = {' × '.join(f'{p}^{e}' if e > 1 else str(p) for p, e in sorted(facts.items()))}")

        prime_status = []
        for p in primes:
            # Tester N₀(p)
            if C <= 200000:
                count = 0
                for combo in combinations(range(1, S), k - 1):
                    A = (0,) + combo
                    cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                    if cs % p == 0:
                        count += 1
                is_blocker = (count == 0)
                ratio = count / C
            else:
                n_samples = min(50000, C)
                count = 0
                for _ in range(n_samples):
                    positions = sorted(random.sample(range(1, S), k - 1))
                    A = (0,) + tuple(positions)
                    cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                    if cs % p == 0:
                        count += 1
                is_blocker = (count == 0)
                ratio = count / n_samples

            prime_status.append((p, is_blocker))

            ord_2_p = ord_mod(2, p) if p < 10**7 else "?"
            marker = "✅ BLOQUE" if is_blocker else f"({ratio*100:.1f}%)"
            print(f"    p={p}: N₀(p)={marker}, ord_p(2)={ord_2_p}, p/S={p/S:.1f}")

        results.append((k, d, prime_status, is_prime(d)))

    # SYNTHÈSE
    print("\n" + "=" * 70)
    print("  SYNTHÈSE : Pattern du blocking prime")
    print("=" * 70)

    for k, d, status, d_prime in results:
        if d_prime:
            print(f"  k={k}: d={d} PREMIER → blocking direct")
        else:
            blockers = [p for p, b in status if b]
            non_blockers = [p for p, b in status if not b]
            S = ceil(k * log2(3))
            print(f"  k={k}: d={d}, bloqueurs={blockers}, non-bloqueurs={non_blockers}")
            if blockers:
                min_blocker = min(blockers)
                max_non_blocker = max(non_blockers) if non_blockers else 0
                print(f"         min(bloqueur)={min_blocker}, max(non-bloqueur)={max_non_blocker}")
                print(f"         threshold : bloqueur si p > {max_non_blocker}")

# ============================================================
# INVESTIGATION C : Pourquoi l'ordre bloque : analyse position par position
# Quand on ajoute la contrainte a_{j} > a_{j-1}, quelles sommes
# deviennent inaccessibles ?
# ============================================================
def investigate_order_mechanism(max_k=7):
    """
    Pour d premier, construire l'automate couche par couche
    et observer comment l'ensemble des états atteignables évolue.

    Comparer avec l'automate NON ordonné (positions libres).
    La différence révèle le mécanisme du blocking.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION C : Mécanisme de l'ordre — couche par couche")
    print("=" * 70)

    for k in range(3, min(max_k + 1, 7)):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d

        print(f"\n  k={k}: p={p}, S={S}")

        # AUTOMATE ORDONNÉ : BFS avec (c mod p, dernière_position)
        # Couche j : ensemble de c atteignables
        ordered_c_sets = [set() for _ in range(k)]
        ordered_c_sets[0].add(1)  # c_0 = 1 (terme j=0 avec A_0=0)

        ordered_layers = [{} for _ in range(k)]
        ordered_layers[0][1] = {0}  # c=1 accessible avec position max = 0

        for j in range(k - 1):
            for c, positions in ordered_layers[j].items():
                for last_pos in positions:
                    for a in range(last_pos + 1, S):
                        c_new = (3 * c + pow(2, a, p)) % p
                        if c_new not in ordered_layers[j + 1]:
                            ordered_layers[j + 1][c_new] = set()
                        ordered_layers[j + 1][c_new].add(a)
                        ordered_c_sets[j + 1].add(c_new)

        # AUTOMATE NON ORDONNÉ : positions libres
        unordered_c_sets = [set() for _ in range(k)]
        unordered_c_sets[0].add(1)

        for j in range(k - 1):
            for c in unordered_c_sets[j]:
                for a in range(1, S):
                    c_new = (3 * c + pow(2, a, p)) % p
                    unordered_c_sets[j + 1].add(c_new)

        print(f"    Couche  | Ordonné |Non-ord. | Diff  | 0∈ord | 0∈non-ord")
        print(f"    --------|---------|---------|-------|-------|----------")
        for j in range(k):
            o = len(ordered_c_sets[j])
            u = len(unordered_c_sets[j])
            zo = 0 in ordered_c_sets[j]
            zu = 0 in unordered_c_sets[j]
            print(f"    j={j:2d}    |  {o:4d}   |  {u:4d}   | {u-o:+4d}  |  {'Y' if zo else 'N'}    |    {'Y' if zu else 'N'}")

        # Pour la couche finale, quelles valeurs sont dans non-ordonné mais pas ordonné ?
        diff = unordered_c_sets[k-1] - ordered_c_sets[k-1]
        if len(diff) <= 20:
            print(f"    Non-ord \\ Ord (couche {k-1}) = {sorted(diff)}")
        else:
            print(f"    |Non-ord \\ Ord| (couche {k-1}) = {len(diff)}")

        if 0 in diff:
            print(f"    ★ 0 est dans la DIFFÉRENCE → l'ordre l'exclut spécifiquement !")

# ============================================================
# INVESTIGATION D : ord_p(2) vs S pour les blocking primes
# Hypothèse : le blocking prime p a toujours ord_p(2) >> S
# ============================================================
def investigate_ord_vs_S(max_k=20):
    """
    Pour chaque facteur premier p de d, calculer ord_p(2)
    et comparer à S. Hypothèse : les bloqueurs ont ord_p(2) > S.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION D : ord_p(2) vs S pour facteurs premiers de d")
    print("=" * 70)

    print(f"  {'k':>3} {'p':>10} {'ord_p(2)':>10} {'S':>4} {'ord/S':>8} {'S-1<ord':>8} {'N₀(p)':>8}")
    print(f"  {'---':>3} {'---':>10} {'---':>10} {'---':>4} {'---':>8} {'---':>8} {'---':>8}")

    for k in range(3, max_k + 1):
        S, d, C = compute_params(k)
        facts = factorize(d)

        for p in sorted(facts.keys()):
            ord_2_p = ord_mod(2, p) if p < 5 * 10**6 else None

            # N₀(p) (exact ou échantillonné)
            if C <= 200000:
                count = 0
                for combo in combinations(range(1, S), k - 1):
                    A = (0,) + combo
                    cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                    if cs % p == 0:
                        count += 1
                n0_str = f"{count}"
            else:
                n_samples = min(30000, C)
                count = 0
                for _ in range(n_samples):
                    positions = sorted(random.sample(range(1, S), k - 1))
                    A = (0,) + tuple(positions)
                    cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                    if cs % p == 0:
                        count += 1
                n0_str = f"~{count/n_samples*100:.1f}%"

            if ord_2_p is not None:
                ratio = ord_2_p / S
                ge_S = "YES" if ord_2_p > S - 1 else "NO"
                print(f"  {k:>3} {p:>10} {ord_2_p:>10} {S:>4} {ratio:>8.2f} {ge_S:>8} {n0_str:>8}")
            else:
                print(f"  {k:>3} {p:>10} {'?':>10} {S:>4} {'?':>8} {'?':>8} {n0_str:>8}")

# ============================================================
# INVESTIGATION E : Formulation log-discrète du prime blocking
# Dans (Z/pZ)*, si g est racine primitive, tout élément = g^e.
# corrSum ≡ 0 mod p est impossible.
# Peut-on le voir dans l'espace des logarithmes discrets ?
# ============================================================
def investigate_discrete_log_blocking(max_k=8):
    """
    Écrire chaque terme 3^{k-1-j} · 2^{A_j} = g^{(k-1-j)·a + A_j·b}
    où a = log_g(3), b = log_g(2).

    corrSum = Σ g^{e_j}. C'est 0 mod p ssi cette somme d'éléments du
    groupe multiplicatif s'annule dans Z/pZ.

    FAIT CLÉ : Additionner des éléments du groupe multiplicatif
    pour obtenir 0 est une contrainte très forte.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION E : Blocking via logarithmes discrets")
    print("=" * 70)

    for k in range(3, min(max_k + 1, 8)):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue

        p = d

        # Trouver racine primitive
        g = None
        for candidate in range(2, p):
            if ord_mod(candidate, p) == p - 1:
                g = candidate
                break

        if g is None:
            print(f"  k={k}: p={p}, pas de racine primitive trouvée (impossible)")
            continue

        # Table des logarithmes discrets
        log_table = {}
        val = 1
        for i in range(p - 1):
            log_table[val] = i
            val = (val * g) % p

        log_3 = log_table.get(3 % p)
        log_2 = log_table.get(2 % p)

        print(f"\n  k={k}: p={p}, g={g}")
        print(f"    log_g(2) = {log_2}, log_g(3) = {log_3}")
        print(f"    Relation : k·log(3) + (-S)·log(2) = {k*log_3 + (-S)*log_2} mod {p-1} = {(k*log_3 - S*log_2) % (p-1)}")

        # Pour chaque composition, calculer les exposants {e_j}
        # e_j = (k-1-j)·log_3 + A_j·log_2  mod (p-1)
        all_exp_sets = []
        for combo in combinations(range(1, S), k - 1):
            A = (0,) + combo
            exp_set = []
            for j in range(k):
                e = ((k-1-j) * log_3 + A[j] * log_2) % (p - 1)
                exp_set.append(e)
            all_exp_sets.append(exp_set)

        # Propriété : corrSum = Σ g^{e_j} = 0 mod p
        # ⟺ Σ g^{e_j} ≡ 0 dans Z/pZ

        # Analyser la distribution des exposants
        all_exps_flat = []
        for es in all_exp_sets:
            all_exps_flat.extend(es)

        exp_counter = Counter(all_exps_flat)

        print(f"    Exposants distincts utilisés : {len(exp_counter)}/{p-1}")

        # Exposant du PREMIER terme (j=0) : (k-1)·log_3 (fixe pour toutes compositions)
        e0 = ((k - 1) * log_3) % (p - 1)
        print(f"    Exposant du terme j=0 (fixe) : e_0 = {e0}")
        print(f"    Valeur du terme j=0 : g^{e0} = {pow(g, e0, p)} = 3^{k-1} mod {p} = {pow(3, k-1, p)}")

        # La somme devrait être 0 = additive identity
        # Mais tous les termes sont dans (Z/pZ)* (non nuls)
        # Donc c'est une somme de k éléments non-nuls qui devrait s'annuler

        # Quelle est la SOMME MINIMALE possible ?
        # (min corrSum mod p, en valeur absolue centrée)
        min_val = p
        for es in all_exp_sets:
            s = sum(pow(g, e, p) for e in es) % p
            centered = min(s, p - s)
            if centered < min_val:
                min_val = centered

        print(f"    Distance min de corrSum à 0 : {min_val}")

        # Répartition des corrSum dans les cosets de 0
        cs_values = []
        for es in all_exp_sets:
            s = sum(pow(g, e, p) for e in es) % p
            cs_values.append(s)

        cs_counter = Counter(cs_values)
        if 0 in cs_counter:
            print(f"    ⚠️ 0 ATTEINT {cs_counter[0]} fois !")
        else:
            print(f"    ✅ 0 jamais atteint")
            # Quelle est la valeur la plus proche de 0 ?
            closest = min(cs_counter.keys(), key=lambda x: min(x, p - x))
            print(f"    Valeur la plus proche de 0 : {closest} (dist={min(closest, p-closest)})")
            print(f"    Nombre de compositions à cette distance : {cs_counter[closest]}")

# ============================================================
# INVESTIGATION F : Relation entre taille du premier et blocking
# ============================================================
def investigate_size_threshold():
    """
    Hypothèse : un premier p | d est bloqueur ssi p > seuil(k).
    Quel est ce seuil ? Est-il lié à S, à k, à C ?
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION F : Seuil de taille pour blocking")
    print("=" * 70)

    data = []
    for k in range(3, 19):
        S, d, C = compute_params(k)
        facts = factorize(d)

        if is_prime(d):
            data.append((k, S, d, [(d, True, d)]))
            continue

        primes_data = []
        for p in sorted(facts.keys()):
            if C <= 200000:
                count = 0
                for combo in combinations(range(1, S), k - 1):
                    A = (0,) + combo
                    cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                    if cs % p == 0:
                        count += 1
                blocks = (count == 0)
            else:
                n_samples = min(30000, C)
                count = 0
                for _ in range(n_samples):
                    positions = sorted(random.sample(range(1, S), k - 1))
                    A = (0,) + tuple(positions)
                    cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                    if cs % p == 0:
                        count += 1
                blocks = (count == 0)
            primes_data.append((p, blocks, p))
        data.append((k, S, d, primes_data))

    print(f"\n  {'k':>3} {'S':>4} {'d':>12}  Bloqueurs          Non-bloqueurs      Seuil estimé")
    print(f"  {'---':>3} {'---':>4} {'---':>12}  {'---':>16}  {'---':>16}  {'---':>12}")

    for k, S, d, primes_data in data:
        blockers = [p for p, b, _ in primes_data if b]
        non_blockers = [p for p, b, _ in primes_data if not b]

        min_b = min(blockers) if blockers else "N/A"
        max_nb = max(non_blockers) if non_blockers else "N/A"

        print(f"  {k:>3} {S:>4} {d:>12}  {str(blockers):>16}  {str(non_blockers):>16}  mb={min_b} mnb={max_nb}")

        # Ratio seuil / S
        if blockers and non_blockers:
            threshold = (max(non_blockers) + min(blockers)) / 2
            print(f"  {'':>22} seuil ≈ {threshold:.0f}, seuil/S = {threshold/S:.1f}, seuil/k = {threshold/k:.1f}")

# ============================================================
# INVESTIGATION G : CRT anti-corrélation profonde
# Pour d composé avec ≥ 2 facteurs, montrer que les compositions
# qui annulent mod p1 sont TOUJOURS non-nulles mod p2
# ============================================================
def investigate_crt_deep(max_k=14):
    """
    Pour d = p1 × p2 × ..., calculer les résidus (mod p1, mod p2, ...)
    pour chaque composition. Vérifier que le point (0, 0, ...) n'est
    JAMAIS atteint.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION G : Anti-corrélation CRT profonde")
    print("=" * 70)

    for k in range(6, min(max_k + 1, 13)):
        S, d, C = compute_params(k)
        if is_prime(d):
            continue

        facts = factorize(d)
        primes = sorted(facts.keys())

        if len(primes) < 2:
            continue  # Pas assez de facteurs pour CRT

        print(f"\n  k={k}: d={d} = {' × '.join(str(p) for p in primes)}, C={C}")

        if C > 200000:
            # Échantillonnage
            n_samples = min(50000, C)
            residue_pairs = []
            for _ in range(n_samples):
                positions = sorted(random.sample(range(1, S), k - 1))
                A = (0,) + tuple(positions)
                cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                res = tuple(cs % p for p in primes)
                residue_pairs.append(res)

            # Combien ont tous les résidus = 0 ?
            all_zero = sum(1 for res in residue_pairs if all(r == 0 for r in res))
            print(f"    Échantillon {n_samples}: tous_résidus=0 : {all_zero}")

            # Pour chaque paire (pi, pj), combien ont (0, 0) ?
            for i in range(len(primes)):
                for j in range(i + 1, len(primes)):
                    pair_zero = sum(1 for res in residue_pairs if res[i] == 0 and res[j] == 0)
                    indiv_i = sum(1 for res in residue_pairs if res[i] == 0)
                    indiv_j = sum(1 for res in residue_pairs if res[j] == 0)
                    expected = indiv_i * indiv_j / n_samples if n_samples > 0 else 0
                    print(f"    ({primes[i]},{primes[j]}): (0,0)={pair_zero}, indiv=({indiv_i},{indiv_j}), attendu si indep={expected:.1f}")
        else:
            # Exact
            residue_pairs = []
            for combo in combinations(range(1, S), k - 1):
                A = (0,) + combo
                cs = sum(pow(3, k-1-j) * pow(2, A[j]) for j in range(k))
                res = tuple(cs % p for p in primes)
                residue_pairs.append(res)

            all_zero = sum(1 for res in residue_pairs if all(r == 0 for r in res))
            print(f"    Total C={C}: tous_résidus=0 : {all_zero}")

            # Analyse par paire
            for i in range(len(primes)):
                for j in range(i + 1, len(primes)):
                    pair_zero = sum(1 for res in residue_pairs if res[i] == 0 and res[j] == 0)
                    indiv_i = sum(1 for res in residue_pairs if res[i] == 0)
                    indiv_j = sum(1 for res in residue_pairs if res[j] == 0)
                    expected = indiv_i * indiv_j / C if C > 0 else 0
                    print(f"    ({primes[i]},{primes[j]}): (0,0)={pair_zero}, indiv=({indiv_i},{indiv_j}), attendu si indep={expected:.1f}")

                    # Anti-corrélation : quand cs ≡ 0 mod p_i, que vaut cs mod p_j ?
                    if indiv_i > 0 and indiv_i <= 200:
                        residues_j_given_i = [res[j] for res in residue_pairs if res[i] == 0]
                        counter_j = Counter(residues_j_given_i)
                        print(f"      cs≡0 mod {primes[i]} → distribution mod {primes[j]}: {dict(counter_j)}")

# ============================================================
# MAIN
# ============================================================
if __name__ == "__main__":
    print("SESSION 8 — DEEP B5b : ORDERING CONSTRAINT + BIG PRIMES")
    print("=" * 70)

    investigate_progressive_ordering(max_k=7)
    investigate_blocking_prime_pattern(max_k=18)
    investigate_order_mechanism(max_k=7)
    investigate_ord_vs_S(max_k=18)
    investigate_discrete_log_blocking(max_k=7)
    investigate_size_threshold()
    investigate_crt_deep(max_k=13)

    print("\n" + "=" * 70)
    print("  TOUTES LES INVESTIGATIONS B5b TERMINÉES")
    print("=" * 70)
