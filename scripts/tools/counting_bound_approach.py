"""
SESSION 6 — APPROCHE PAR COMPTAGE : Bornes de taille pour l'Enonce C

OBJECTIF : Explorer si un argument de COMPTAGE peut prouver l'Enonce C.

IDEE : Pour l'Enonce C, on considere les compositions (0, p, p+1, q_3, ..., q_{k-1})
avec p+2 <= q_3 < ... < q_{k-1} <= S-1.

Le nombre de telles compositions est C(S-p-2, k-3).
Le module est d = 2^S - 3^k.

Si C(S-p-2, k-3) < d, alors l'image de Ev_d ne peut pas couvrir tout Z/dZ,
et on a une chance que 0 soit dans les "trous".

MAIS : C < d ne suffit PAS a prouver que 0 specifiquement manque.
Il faut un argument STRUCTUREL supplementaire.

EXPERIENCE 1 : Calculer C(S-p-2, k-3) / d pour differents k et p.
EXPERIENCE 2 : Analyser la distribution des corrSum restreints mod d.
EXPERIENCE 3 : Explorer le "peeling" sur la derniere position.
EXPERIENCE 4 : Argument par les bornes min/max du corrSum restreint.
EXPERIENCE 5 : Comprendre combien de multiples de d sont dans [min, max].
"""

from math import comb, ceil, log2, gcd
from itertools import combinations

def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    return S, d

def experiment1_coverage_ratio():
    """Calcule C(S-p-2, k-3) / d pour differents k et p."""
    print("=" * 70)
    print("EXPERIENCE 1 : Ratio de couverture C(S-p-2, k-3) / d")
    print("=" * 70)

    for k in range(3, 16):
        S, d = compute_params(k)
        if d <= 0:
            continue
        print(f"\nk={k}, S={S}, d={d}, C_total={comb(S-1,k-1)}")

        for p in range(1, min(S-k+1, 10)):
            n_positions = S - p - 2  # positions disponibles : {p+2, ..., S-1}
            n_choices = k - 3        # nombre de positions a choisir
            if n_positions < n_choices:
                continue
            C_restricted = comb(n_positions, n_choices)
            ratio = C_restricted / d
            marker = " ***" if ratio >= 1 else ""
            print(f"  p={p}: C_restreint = C({n_positions},{n_choices}) = {C_restricted}, "
                  f"ratio = {ratio:.4f}{marker}")

def experiment2_corrsum_distribution(k, p=1):
    """Analyse la distribution des corrSum restreints mod d."""
    S, d = compute_params(k)

    print(f"\n{'='*60}")
    print(f"EXPERIENCE 2 : Distribution corrSum restreint, k={k}, p={p}")
    print(f"S={S}, d={d}")
    print(f"{'='*60}")

    # Prefixe : (0, p, p+1)
    prefix = (9 + 5 * pow(2, p)) * pow(3, k-3)

    # Positions pour le suffixe : p+2 <= q_3 < ... < q_{k-1} <= S-1
    available = list(range(p+2, S))
    n_choices = k - 3

    if n_choices > len(available):
        print(f"  Pas assez de positions ({len(available)} < {n_choices})")
        return

    print(f"  Positions disponibles : {len(available)}, choix : {n_choices}")
    print(f"  Nombre de compositions : {comb(len(available), n_choices)}")

    # Calculer tous les corrSum mod d
    residues = []
    target = (-prefix) % d

    for positions in combinations(available, n_choices):
        suffix = 0
        for j_idx, q in enumerate(positions):
            j = 3 + j_idx  # l'indice j dans corrSum
            suffix += pow(3, k-1-j) * pow(2, q)
        residue = suffix % d
        residues.append(residue)

    # Distribution
    from collections import Counter
    dist = Counter(residues)
    n_residues_hit = len(dist)
    n_compositions = len(residues)

    print(f"\n  Residus atteints : {n_residues_hit} / {d}")
    print(f"  Ratio couverture : {n_residues_hit/d:.4f}")
    print(f"  Target = {target}")
    print(f"  Target atteint : {target in dist}")

    if target in dist:
        print(f"  PROBLEME : target EST atteint ! count = {dist[target]}")
    else:
        # Distance au target
        min_dist = min(min(abs(r - target), d - abs(r - target)) for r in dist)
        print(f"  Distance minimale au target : {min_dist}")

    # Distribution des occurrences
    counts = sorted(dist.values())
    print(f"\n  Min occurrences : {counts[0]}")
    print(f"  Max occurrences : {counts[-1]}")
    print(f"  Moyenne : {n_compositions/n_residues_hit:.2f}")

    return dist, target

def experiment3_peeling_analysis(k, p=1):
    """
    Peeling sur la derniere position q_{k-1}.
    Fixer q_{k-1} = Q, puis regarder le probleme interieur.
    """
    S, d = compute_params(k)

    print(f"\n{'='*60}")
    print(f"EXPERIENCE 3 : Peeling sur derniere position, k={k}, p={p}")
    print(f"{'='*60}")

    prefix = (9 + 5 * pow(2, p)) * pow(3, k-3)
    target_full = (-prefix) % d

    available = list(range(p+2, S))
    n_choices = k - 3

    if n_choices < 1 or n_choices > len(available):
        print(f"  Non applicable")
        return

    # Pour chaque valeur de la derniere position Q
    print(f"\n  Peeling de q_{{k-1}} = Q :")
    for Q in range(p + n_choices, S):  # Q doit laisser n_choices-1 positions avant lui
        # Positions restantes : p+2 <= q_3 < ... < q_{k-2} < Q
        inner_available = list(range(p+2, Q))
        inner_choices = n_choices - 1

        if inner_choices > len(inner_available) or inner_choices < 0:
            continue

        # Le terme fixe : 3^0 * 2^Q = 2^Q (car j = k-1, poids = 3^0 = 1)
        fixed_term = pow(2, Q) % d

        # Target interieur
        inner_target = (target_full - fixed_term) % d

        n_inner = comb(len(inner_available), inner_choices)

        # Calculer les residus interieurs si possible
        if inner_choices == 0:
            inner_value = 0
            hit = (inner_value == inner_target)
            print(f"  Q={Q}: inner_choices=0, inner_target={inner_target}, hit={hit}")
            continue

        if n_inner <= 100000:
            inner_residues = set()
            for positions in combinations(inner_available, inner_choices):
                suffix = 0
                for j_idx, q in enumerate(positions):
                    j = 3 + j_idx
                    suffix += pow(3, k-1-j) * pow(2, q)
                inner_residues.add(suffix % d)

            hit = inner_target in inner_residues
            coverage = len(inner_residues) / d if d > 0 else 0
            print(f"  Q={Q}: n_inner={n_inner}, residus={len(inner_residues)}/{d} "
                  f"({coverage:.3f}), target_hit={hit}")
        else:
            print(f"  Q={Q}: n_inner={n_inner} (trop grand), ratio={n_inner/d:.4f}")

def experiment4_size_bounds(k, p=1):
    """
    Bornes min/max du corrSum restreint et nombre de multiples de d.
    """
    S, d = compute_params(k)

    print(f"\n{'='*60}")
    print(f"EXPERIENCE 4 : Bornes de taille, k={k}, p={p}")
    print(f"{'='*60}")

    # Prefixe
    prefix = (9 + 5 * pow(2, p)) * pow(3, k-3)

    # Suffixe minimum : positions les plus petites
    # q_3 = p+2, q_4 = p+3, ..., q_{k-1} = p+k-2
    min_suffix = sum(pow(3, k-1-j) * pow(2, p+j-1) for j in range(3, k))

    # Suffixe maximum : positions les plus grandes
    # q_{k-1} = S-1, q_{k-2} = S-2, ..., q_3 = S-k+3
    max_suffix = sum(pow(3, k-1-j) * pow(2, S-k+j) for j in range(3, k))

    min_corrSum = prefix + min_suffix
    max_corrSum = prefix + max_suffix

    # Multiples de d dans [min, max]
    n_min = (min_corrSum + d - 1) // d  # premier multiple >= min
    n_max = max_corrSum // d             # dernier multiple <= max
    n_multiples = max(0, n_max - n_min + 1)

    print(f"  prefix = {prefix}")
    print(f"  min_suffix = {min_suffix}")
    print(f"  max_suffix = {max_suffix}")
    print(f"  min_corrSum = {min_corrSum}")
    print(f"  max_corrSum = {max_corrSum}")
    print(f"  d = {d}")
    print(f"  Range / d = {(max_corrSum - min_corrSum) / d:.4f}")
    print(f"  n_0 range : [{n_min}, {n_max}]")
    print(f"  Multiples de d dans l'intervalle : {n_multiples}")

    # Nombre de compositions
    n_positions = S - p - 2
    n_choices = k - 3
    C_restricted = comb(n_positions, n_choices) if n_positions >= n_choices else 0

    print(f"  Compositions : {C_restricted}")
    print(f"  Ratio compositions/multiples : {C_restricted/n_multiples:.4f}" if n_multiples > 0 else "  Ratio : inf")

    # Les n_0 candidats
    if n_multiples <= 30:
        print(f"\n  n_0 candidats : {list(range(n_min, n_max+1))}")

    return n_multiples, C_restricted

def experiment5_n0_filtering(k, p=1):
    """
    Pour chaque n_0 candidat, verifier si corrSum = n_0 * d
    est realisable par une composition (0, p, p+1, ...) ordonnee.
    """
    S, d = compute_params(k)

    print(f"\n{'='*60}")
    print(f"EXPERIENCE 5 : Filtrage des n_0 candidats, k={k}, p={p}")
    print(f"{'='*60}")

    prefix = (9 + 5 * pow(2, p)) * pow(3, k-3)

    # Bornes du suffixe
    min_suffix = sum(pow(3, k-1-j) * pow(2, p+j-1) for j in range(3, k))
    max_suffix = sum(pow(3, k-1-j) * pow(2, S-k+j) for j in range(3, k))

    min_corrSum = prefix + min_suffix
    max_corrSum = prefix + max_suffix

    n_min = (min_corrSum + d - 1) // d
    n_max = max_corrSum // d
    n_multiples = max(0, n_max - n_min + 1)

    print(f"  n_0 candidats : {n_min} a {n_max} ({n_multiples} valeurs)")

    if n_multiples > 50:
        print(f"  Trop de candidats ({n_multiples}), test exhaustif...")
        # Enumerer les corrSum
        available = list(range(p+2, S))
        n_choices = k - 3
        if comb(len(available), n_choices) > 500000:
            print(f"  Trop de compositions ({comb(len(available), n_choices)}), abandon")
            return

    # Enumerer les corrSum effectifs
    available = list(range(p+2, S))
    n_choices = k - 3

    if n_choices < 0 or n_choices > len(available):
        print(f"  Pas assez de positions")
        return

    if comb(len(available), n_choices) > 500000:
        print(f"  Trop de compositions ({comb(len(available), n_choices)}), abandon")
        return

    corrSum_set = set()
    for positions in combinations(available, n_choices):
        suffix = sum(pow(3, k-1-j) * pow(2, q) for j, q in zip(range(3, k), positions))
        cs = prefix + suffix
        corrSum_set.add(cs)

    # Verifier chaque n_0
    n_hit = 0
    for n_0 in range(n_min, n_max + 1):
        target_cs = n_0 * d
        if target_cs in corrSum_set:
            n_hit += 1
            print(f"  *** n_0 = {n_0} : corrSum = {target_cs} TROUVE ***")

    if n_hit == 0:
        print(f"  AUCUN n_0 ne donne un corrSum realisable !")
        print(f"  ==> Confirme que corrSum ≢ 0 mod d pour ces compositions")
    else:
        print(f"  {n_hit} n_0 trouvent un corrSum realisable")

    # Analyse des corrSum effectifs
    corrSum_list = sorted(corrSum_set)
    multiples_of_d = sorted(n * d for n in range(n_min, n_max + 1))

    print(f"\n  Nombre de corrSum distincts : {len(corrSum_set)}")
    print(f"  Nombre de multiples de d dans [min,max] : {n_multiples}")

    # Quels multiples de d sont les plus proches des corrSum ?
    if n_multiples <= 20 and len(corrSum_set) <= 5000:
        print(f"\n  Distances minimales aux multiples de d :")
        for mult in multiples_of_d:
            # Trouver le corrSum le plus proche
            import bisect
            idx = bisect.bisect_left(corrSum_list, mult)
            dists = []
            if idx > 0:
                dists.append(abs(mult - corrSum_list[idx-1]))
            if idx < len(corrSum_list):
                dists.append(abs(mult - corrSum_list[idx]))
            min_d = min(dists) if dists else float('inf')
            print(f"    n_0={mult//d}: mult={mult}, dist_min={min_d} ({min_d/d:.4f}*d)")

def experiment6_2adic_constraint():
    """
    Analyse 2-adique : v_2(corrSum) est determine par les premiers termes.
    Pour corrSum = n_0 * d et d impair : v_2(corrSum) = v_2(n_0).
    """
    print(f"\n{'='*60}")
    print(f"EXPERIENCE 6 : Contrainte 2-adique")
    print(f"{'='*60}")

    for k in range(5, 13):
        S, d = compute_params(k)
        p = 1  # s = 5

        prefix = (9 + 5 * pow(2, p)) * pow(3, k-3)

        # v_2(prefix) : prefix = (9 + 10) * 3^{k-3} = 19 * 3^{k-3}
        # 19 est impair, 3^{k-3} est impair, donc v_2(prefix) = 0
        v2_prefix = 0

        # v_2(suffix) : suffix = Sum 3^{k-1-j} * 2^{q_j}
        # Le terme avec le plus petit q_j domine : v_2(suffix) >= min(q_3) = p+2 = 3
        v2_suffix_min = p + 2  # = 3 pour p=1

        # Donc v_2(corrSum) = v_2(prefix + suffix) = min(v2_prefix, v2_suffix) = 0
        # Car prefix est impair et suffix est pair : corrSum est IMPAIR.
        # Donc v_2(corrSum) = 0.

        # Pour corrSum = n_0 * d : v_2(n_0 * d) = v_2(n_0) + v_2(d)
        # d est impair, donc v_2(d) = 0, donc v_2(n_0) = 0.
        # n_0 est IMPAIR.

        # Bornes
        min_suffix = sum(pow(3, k-1-j) * pow(2, p+j-1) for j in range(3, k))
        max_suffix = sum(pow(3, k-1-j) * pow(2, S-k+j) for j in range(3, k))

        min_cs = prefix + min_suffix
        max_cs = prefix + max_suffix

        n_min = (min_cs + d - 1) // d
        n_max = max_cs // d

        odd_n = [n for n in range(n_min, n_max+1) if n % 2 == 1]

        print(f"  k={k}: d={d}, n_0 range [{n_min},{n_max}], "
              f"n_0 impairs : {len(odd_n)}/{n_max-n_min+1}, "
              f"corrSum TOUJOURS impair (v_2=0)")

def main():
    # EXPERIENCE 1 : Ratios de couverture
    experiment1_coverage_ratio()

    # EXPERIENCE 2 : Distribution corrSum restreint
    for k in [5, 6, 7, 8]:
        experiment2_corrsum_distribution(k, p=1)

    # EXPERIENCE 3 : Peeling
    for k in [5, 6]:
        experiment3_peeling_analysis(k, p=1)

    # EXPERIENCE 4 : Bornes de taille
    print("\n\n" + "=" * 70)
    print("EXPERIENCE 4 : Bornes de taille pour tous k et p=1")
    print("=" * 70)
    for k in range(5, 16):
        experiment4_size_bounds(k, p=1)

    # EXPERIENCE 5 : Filtrage n_0
    print("\n\n" + "=" * 70)
    print("EXPERIENCE 5 : Filtrage des n_0 candidats")
    print("=" * 70)
    for k in range(5, 13):
        experiment5_n0_filtering(k, p=1)

    # EXPERIENCE 6 : Contrainte 2-adique
    experiment6_2adic_constraint()

    print("\n\n" + "=" * 70)
    print("FIN DE L'ANALYSE PAR COMPTAGE")
    print("=" * 70)

if __name__ == "__main__":
    main()
