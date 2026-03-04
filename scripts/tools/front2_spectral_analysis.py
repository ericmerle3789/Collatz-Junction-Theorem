#!/usr/bin/env python3
"""
FRONT 2 : ANALYSE SPECTRALE DE L'AUTOMATE DE HORNER
=====================================================
Phase 3, Front E du DISCOVERY_PROTOCOL.md — Idee 9 (Automate de Horner)

OBJECTIF : Modeliser l'automate inhomogene par un produit de matrices
de permutation, analyser le spectre, et comprendre POURQUOI 0 est
structurellement inaccessible.

STRUCTURE CLE :
  Chaque M_p est la matrice de la permutation sigma_p : c -> (3c + 2^p) mod d.
  Dans la base de Fourier : M_p . v_t = omega^{-t*2^p*3^{-1}} * v_{t*3^{-1} mod d}
  => Les ORBITES de <3> dans (Z/dZ)* decomposent l'action en blocs.

ELEMENTS CALCULES :
  1. Matrices de permutation M_p et matrice totale T = Sum M_p
  2. Fonction symetrique elementaire f_{k-1}(S-1) via recurrence
  3. Decomposition de Fourier par orbites de <3>
  4. Eigenvalues de T et des blocs orbitaux
  5. Verification de N_0(d) et analyse du coefficient (0,1)
"""

import numpy as np
import math
from collections import defaultdict
from itertools import combinations


def compute_parameters(k):
    """Calcule S, d, C pour un k donne."""
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    C = math.comb(S - 1, k - 1)
    return S, d, C


def mod_inverse(a, m):
    """Inverse modulaire de a mod m (via algorithme etendu d'Euclide)."""
    g, x, _ = extended_gcd(a, m)
    if g != 1:
        return None
    return x % m


def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def multiplicative_order(a, n):
    """Ordre multiplicatif de a dans (Z/nZ)*."""
    if math.gcd(a, n) != 1:
        return None
    order = 1
    current = a % n
    while current != 1:
        current = (current * a) % n
        order += 1
        if order > n:
            return None  # securite
    return order


def build_permutation(d, p):
    """Construit la permutation sigma_p : c -> (3c + 2^p) mod d.
    Retourne un tableau perm tel que perm[c] = sigma_p(c)."""
    two_p = pow(2, p, d)
    perm = [(3 * c + two_p) % d for c in range(d)]
    return perm


def perm_to_matrix(perm, d):
    """Convertit une permutation en matrice d x d."""
    M = np.zeros((d, d), dtype=np.float64)
    for j in range(d):
        M[perm[j], j] = 1.0
    return M


def compute_orbits_of_3(d):
    """Calcule les orbites de l'action t -> 3t dans Z/dZ.
    Retourne une liste d'orbites (chaque orbite = liste de residus)."""
    visited = set()
    orbits = []
    for t in range(d):
        if t in visited:
            continue
        orbit = []
        current = t
        while current not in visited:
            visited.add(current)
            orbit.append(current)
            current = (3 * current) % d
        orbits.append(orbit)
    return orbits


def fourier_eigenvalue(d, p, t):
    """Calcule l'eigenvalue de M_p sur v_t dans la base de Fourier.
    M_p . v_t = lambda * v_{t*3^{-1} mod d}
    ou lambda = omega^{-t*2^p*3^{-1} mod d}
    avec omega = e^{2*pi*i/d}."""
    inv3 = mod_inverse(3, d)
    if inv3 is None:
        return None
    exponent = (-t * pow(2, p, d) * inv3) % d
    return np.exp(2j * np.pi * exponent / d)


def compute_orbital_block_eigenvalues(d, S, orbit):
    """Pour une orbite O = {t, 3t, 9t, ...} de taille r,
    calcule les eigenvalues du produit M_p sur ce bloc.

    Sur le bloc de taille r, M_p agit par :
      v_{t_i} -> lambda_{p,t_i} * v_{t_{i-1}}  (cyclage)
    La matrice du bloc est un produit de shift * diag(lambdas).
    Les eigenvalues du bloc de M_p sont :
      mu_j = (prod_i lambda_{p,t_i})^{1/r} * omega_r^j  pour j=0,...,r-1
    ou omega_r = e^{2pi*i/r}.

    Mais nous nous interessons au produit SUM M_p, pas a chaque M_p.
    Pour la somme T = Sum_{p=1}^{S-1} M_p, les eigenvalues sur le bloc
    sont plus complexes.

    Retourne les eigenvalues de T restreint a ce bloc orbital.
    """
    r = len(orbit)
    if r == 0:
        return []

    inv3 = mod_inverse(3, d)

    # Construire la matrice du bloc r x r de T = Sum M_p
    # M_p sur le bloc : envoie v_{orbit[i]} vers lambda * v_{orbit[(i-1) mod r]}
    # (car orbit[i]*3^{-1} = orbit[i-1])

    # Verifier l'orbite : orbit[i+1] = 3*orbit[i] mod d
    # Donc orbit[i]*3^{-1} = orbit[i-1 mod r]

    block = np.zeros((r, r), dtype=np.complex128)

    for p in range(1, S):
        # M_p envoie v_{orbit[i]} vers lambda_{p, orbit[i]} * v_{orbit[i-1 mod r]}
        for i in range(r):
            t = orbit[i]
            lam = fourier_eigenvalue(d, p, t)
            target_idx = (i - 1) % r
            block[target_idx, i] += lam

    eigenvalues = np.linalg.eigvals(block)
    return sorted(eigenvalues, key=lambda x: -abs(x))


def compute_elementary_symmetric(d, S, k):
    """Calcule la fonction symetrique elementaire matricielle :
      f_j(q) = Sum_{1<=p_1<...<p_j<=q} M_{p_j} ... M_{p_1}
    via la recurrence :
      f_0(q) = I
      f_j(q) = f_j(q-1) + M_q * f_{j-1}(q-1)

    Retourne f_{k-1}(S-1) qui est une matrice d x d.
    N_0(d) = f_{k-1}(S-1)[0, 1]  (element (etat final=0, etat initial=1)).

    NOTE : Calcul en entiers (pas de flottants) pour exactitude.
    """
    # Precalculer les permutations
    perms = {}
    for p in range(1, S):
        perms[p] = build_permutation(d, p)

    # Initialiser : f_0(q) = I pour tout q
    # On stocke f_j(q) comme matrice d x d
    # Mais on peut optimiser en ne gardant que f_j(q-1) et f_j(q)

    # f[j] = matrice d x d (int64)
    prev_f = [None] * k  # f[j] = f_j pour la position courante
    # f_0 = I
    identity = np.eye(d, dtype=np.int64)

    # On calcule couche par couche
    # f[0](q) = I pour tout q (ne change pas)
    # f[j](q) = f[j](q-1) + M_q . f[j-1](q-1)

    # Strategie : iterer sur q de 1 a S-1
    # A chaque q, mettre a jour f[j] pour j = k-1 down to 1
    f = [np.zeros((d, d), dtype=np.int64) for _ in range(k)]
    f[0] = identity.copy()

    for q in range(1, S):
        # Appliquer M_q : pour j = k-1 down to 1
        # f[j](q) = f[j](q-1) + M_q . f[j-1](q-1)
        # On doit lire f[j-1] AVANT de le modifier !
        # Donc iterer de j = k-1 vers j = 1
        M_q_perm = perms[q]

        for j in range(min(k - 1, q), 0, -1):
            # M_q . f[j-1] : appliquer la permutation aux lignes
            product = np.zeros((d, d), dtype=np.int64)
            for col in range(d):
                for row in range(d):
                    if f[j - 1][row, col] != 0:
                        product[M_q_perm[row], col] += f[j - 1][row, col]
            f[j] = f[j] + product

    return f[k - 1]


def compute_elementary_symmetric_optimized(d, S, k):
    """Version optimisee utilisant les permutations directement.

    Au lieu de stocker des matrices d x d, on peut utiliser le fait
    que M_q est une permutation. M_q . A signifie : la ligne i de M_q.A
    est la ligne sigma_q^{-1}(i) de A. Autrement dit, on permute les LIGNES.

    Mais en fait, M_q[i,j] = 1 si i = sigma_q(j), donc
    (M_q . A)[i, c] = A[sigma_q^{-1}(i), c].
    """
    perms = {}
    inv_perms = {}
    for p in range(1, S):
        perm = build_permutation(d, p)
        perms[p] = perm
        inv_perm = [0] * d
        for c in range(d):
            inv_perm[perm[c]] = c
        inv_perms[p] = inv_perm

    f = [np.zeros((d, d), dtype=np.int64) for _ in range(k)]
    f[0] = np.eye(d, dtype=np.int64)

    for q in range(1, S):
        inv_perm_q = inv_perms[q]

        for j in range(min(k - 1, q), 0, -1):
            # M_q . f[j-1] : permuter les lignes de f[j-1] selon sigma_q
            # (M_q . A)[i, :] = A[sigma_q^{-1}(i), :]
            permuted = f[j - 1][inv_perm_q, :]
            f[j] = f[j] + permuted

    return f[k - 1]


def analyze_spectral(k_val, verbose=True):
    """Analyse spectrale complete pour un k donne."""
    S, d, C = compute_parameters(k_val)

    if d <= 0:
        return None
    if d > 5000:
        if verbose:
            print(f"\nk={k_val}: d={d} trop grand pour l'analyse matricielle complete")
        return None

    if verbose:
        print(f"\n{'='*80}")
        print(f"ANALYSE SPECTRALE : k={k_val}, S={S}, d={d}, C={C}")
        print(f"{'='*80}")

    # 1. Calcul de la fonction symetrique elementaire
    if verbose:
        print(f"\n--- 1. Fonction symetrique elementaire f_{{k-1}}(S-1) ---")

    if C <= 500000 and d <= 3000:
        f_matrix = compute_elementary_symmetric_optimized(d, S, k_val)
        N0 = int(f_matrix[0, 1])
        total_paths = int(np.sum(f_matrix[:, 1]))
        if verbose:
            print(f"  N_0(d) = f[0,1] = {N0}  (DOIT etre 0)")
            print(f"  Total chemins = Sum f[:,1] = {total_paths}  (DOIT etre C={C})")
            assert N0 == 0, f"ERREUR CRITIQUE : N_0 = {N0} != 0 !"
            assert total_paths == C, f"ERREUR : total = {total_paths} != C = {C}"

        # Distribution des etats finaux
        final_dist = f_matrix[:, 1]
        nonzero_states = [(s, int(final_dist[s])) for s in range(d) if final_dist[s] > 0]
        if verbose:
            print(f"  Etats finaux atteints : {len(nonzero_states)}/{d}")
            if d <= 50:
                for s, cnt in sorted(nonzero_states, key=lambda x: -x[1]):
                    print(f"    etat {s:3d} : {cnt:4d} chemins ({100*cnt/C:.1f}%)")
    else:
        if verbose:
            print(f"  SKIP (C={C} ou d={d} trop grand)")
        f_matrix = None

    # 2. Matrice de transfert totale T = Sum M_p
    if verbose:
        print(f"\n--- 2. Matrice de transfert totale T = Sum M_p ---")

    T = np.zeros((d, d), dtype=np.float64)
    for p in range(1, S):
        perm = build_permutation(d, p)
        for c in range(d):
            T[perm[c], c] += 1.0

    eigenvalues_T = np.linalg.eigvals(T)
    eigenvalues_sorted = sorted(eigenvalues_T, key=lambda x: -abs(x))

    if verbose:
        print(f"  Taille de T : {d}x{d}")
        print(f"  Nombre de transitions (S-1) = {S-1}")
        print(f"  Eigenvalues de T (top 10 par |lambda|) :")
        for i, ev in enumerate(eigenvalues_sorted[:10]):
            print(f"    lambda_{i} = {ev.real:+.6f} + {ev.imag:+.6f}i  "
                  f"(|lambda| = {abs(ev):.6f})")

    # 3. Orbites de <3> dans Z/dZ
    if verbose:
        print(f"\n--- 3. Orbites de <3> dans Z/dZ ---")

    orbits = compute_orbits_of_3(d)
    ord_3 = multiplicative_order(3, d)
    ord_2 = multiplicative_order(2, d)

    if verbose:
        print(f"  ord_d(3) = {ord_3}")
        print(f"  ord_d(2) = {ord_2}")
        print(f"  S-1 = {S-1}")
        print(f"  Gap algebrique : ord_d(2) > S-1 ? "
              f"{'OUI' if ord_2 > S - 1 else 'NON (k=3 special)'}")
        print(f"  Nombre d'orbites de <3> : {len(orbits)}")
        orbit_sizes = defaultdict(int)
        for orb in orbits:
            orbit_sizes[len(orb)] += 1
        for sz in sorted(orbit_sizes.keys()):
            print(f"    Taille {sz} : {orbit_sizes[sz]} orbite(s)")

    # 4. Analyse de Fourier par blocs orbitaux
    if verbose:
        print(f"\n--- 4. Analyse de Fourier par blocs orbitaux ---")

    # L'orbite contenant t=0 est speciale : {0} (taille 1)
    # Car 3*0 = 0 mod d.
    # Sur cette orbite, M_p agit par : v_0 -> lambda_{p,0} * v_0
    # lambda_{p,0} = omega^{0} = 1. Donc T . v_0 = (S-1) * v_0.
    # v_0 est le vecteur uniforme => T preserve la somme (evident).

    inv3 = mod_inverse(3, d)

    # Pour chaque orbite non-triviale, calculer les eigenvalues de T
    orbital_eigenvalues = {}
    for idx, orb in enumerate(orbits):
        if len(orb) <= 1:
            # Orbite {0} : eigenvalue = S-1
            if orb[0] == 0:
                orbital_eigenvalues[idx] = [complex(S - 1)]
            else:
                # Orbite fixe non-triviale (t avec 3t = t mod d => 2t = 0 mod d)
                t = orb[0]
                lam_sum = sum(fourier_eigenvalue(d, p, t) for p in range(1, S))
                orbital_eigenvalues[idx] = [lam_sum]
        else:
            evs = compute_orbital_block_eigenvalues(d, S, orb)
            orbital_eigenvalues[idx] = evs

    if verbose:
        print(f"  Eigenvalues par orbite (top 5 orbites par |lambda_max|) :")
        orbit_max = []
        for idx, evs in orbital_eigenvalues.items():
            if len(evs) > 0:
                max_ev = max(abs(ev) for ev in evs)
                orbit_max.append((idx, orbits[idx], evs, max_ev))
        orbit_max.sort(key=lambda x: -x[3])
        for rank, (idx, orb, evs, max_ev) in enumerate(orbit_max[:5]):
            orb_repr = orb[:3]
            if len(orb) > 3:
                orb_str = f"{orb_repr}... (taille {len(orb)})"
            else:
                orb_str = f"{orb}"
            print(f"    Orbite {idx} {orb_str} :")
            for ev in evs[:3]:
                print(f"      lambda = {ev.real:+.6f} + {ev.imag:+.6f}i  "
                      f"(|lambda| = {abs(ev):.6f})")

    # 5. Analyse de la colonne "etat 1" de f_{k-1}
    if f_matrix is not None and verbose:
        print(f"\n--- 5. Structure de f_{{k-1}}[:,1] (chemins depuis etat 1) ---")

        col_1 = f_matrix[:, 1].astype(np.float64)
        # Transformee de Fourier de cette colonne
        col_1_fft = np.fft.fft(col_1)

        print(f"  Composantes de Fourier de la distribution des etats finaux :")
        print(f"  (seules les plus grandes en module)")
        fft_mags = [(t, abs(col_1_fft[t]), col_1_fft[t]) for t in range(d)]
        fft_mags.sort(key=lambda x: -x[1])
        for t, mag, val in fft_mags[:8]:
            print(f"    t={t:4d} : |F(t)| = {mag:.4f}  "
                  f"F(t) = {val.real:+.4f} + {val.imag:+.4f}i")

        # Le coefficient t=0 est C/d * d = C (somme totale)
        print(f"\n  F(0) = {col_1_fft[0].real:.4f} (= C = {C})")
        print(f"  F(0)/d = {col_1_fft[0].real/d:.4f} (= C/d = {C/d:.4f})")

        # Verifier que la somme des F(t) pour t != 0 donne exactement -C
        # (puisque N_0 = 0 => (1/d) * Sum_{t=0}^{d-1} F(t) = 0
        #  => Sum_{t>=1} F(t) = -F(0) = -C)
        sum_nonzero = sum(col_1_fft[t] for t in range(1, d))
        print(f"  Sum_{{t>=1}} F(t) = {sum_nonzero.real:+.4f} + {sum_nonzero.imag:+.4f}i "
              f"(doit etre = -{C})")

    # 6. Test de l'inaccessibilite de l'etat 0
    if f_matrix is not None and verbose:
        print(f"\n--- 6. Pourquoi l'etat 0 est inaccessible ---")

        # La ligne 0 de f_{k-1} : quels etats INITIAUX menent a l'etat 0 ?
        row_0 = f_matrix[0, :]
        sources_to_0 = [(c, int(row_0[c])) for c in range(d) if row_0[c] > 0]
        if sources_to_0:
            print(f"  ALERTE : il existe des etats initiaux menant a 0 !")
            for c, cnt in sources_to_0:
                print(f"    depuis etat initial {c} : {cnt} chemins")
        else:
            print(f"  Ligne 0 de f_{{k-1}} : TOUT ZERO")
            print(f"  => L'etat 0 est inaccessible depuis TOUT etat initial !")
            print(f"  => Ce n'est pas specifique a c_0=1, c'est UNIVERSEL.")

        # Plus fort : quels etats finaux sont completement inaccessibles ?
        inaccessible = []
        for target in range(d):
            if all(f_matrix[target, c] == 0 for c in range(d)):
                inaccessible.append(target)
        if inaccessible:
            print(f"\n  Etats finaux UNIVERSELLEMENT inaccessibles "
                  f"(depuis tout etat initial) : {inaccessible}")
            print(f"  => {len(inaccessible)} etats sur {d} sont inaccessibles")
        else:
            print(f"\n  Seul l'etat 0 est inaccessible depuis c_0=1")
            print(f"  D'autres etats initiaux PEUVENT atteindre 0")

    # 7. Analyse du spectre de la matrice symetrique elementaire
    if f_matrix is not None and d <= 500 and verbose:
        print(f"\n--- 7. Spectre de f_{{k-1}}(S-1) ---")
        f_float = f_matrix.astype(np.float64)
        eigs_f = np.linalg.eigvals(f_float)
        eigs_sorted = sorted(eigs_f, key=lambda x: -abs(x))
        print(f"  Top 10 eigenvalues de f_{{k-1}} :")
        for i, ev in enumerate(eigs_sorted[:10]):
            print(f"    mu_{i} = {ev.real:+.6f} + {ev.imag:+.6f}i  "
                  f"(|mu| = {abs(ev):.6f})")

        # Rang de f_{k-1}
        rank = np.linalg.matrix_rank(f_float)
        print(f"  Rang de f_{{k-1}} : {rank} / {d}")

        # Trace de f_{k-1} (= nombre de "boucles" de longueur k-1)
        trace = int(np.trace(f_matrix))
        print(f"  Trace de f_{{k-1}} : {trace} (chemins revenant au point de depart)")

    return {
        'k': k_val, 'S': S, 'd': d, 'C': C,
        'ord_2': ord_2, 'ord_3': ord_3,
        'gap': ord_2 > S - 1,
        'n_orbits': len(orbits),
        'eigenvalues_T_top': eigenvalues_sorted[:5] if 'eigenvalues_sorted' in dir() else [],
    }


def prove_ord_theorem(k_max=25):
    """Tentative de preuve du Theoreme 7.1 : ord_d(2) > S-1 pour k >= 4.

    Analyse detaillee pour chaque k : pourquoi d ne divise aucun 2^r - 1
    pour r = 1, ..., S-1."""
    print(f"\n{'*'*80}")
    print(f"THEOREME 7.1 : ANALYSE DE ord_d(2) > S-1")
    print(f"{'*'*80}")

    print(f"\n{'k':>3} {'S':>4} {'d':>12} {'ord_d(2)':>10} {'S-1':>5} "
          f"{'ord>S-1':>8} {'2^(S-1)-1':>15} {'d|(2^(S-1)-1)':>14} "
          f"{'(2^(S-1)-1)/d':>14}")
    print("-" * 100)

    for k in range(3, k_max + 1):
        S, d, C = compute_parameters(k)
        if d <= 0:
            continue
        if d > 10**15:
            print(f"{k:3d} {S:4d} {'(trop grand)':>12}")
            continue

        ord_2 = multiplicative_order(2, d) if d < 10**8 else None
        gap = (ord_2 > S - 1) if ord_2 is not None else None

        val_S1 = pow(2, S - 1, d) - 1  # 2^{S-1} - 1 mod d
        if val_S1 < 0:
            val_S1 += d
        div_S1 = (val_S1 == 0)  # d | (2^{S-1} - 1) ?

        # Calcul exact de 2^{S-1} - 1
        two_S1 = 2**(S-1)
        ratio = (two_S1 - 1) / d if d > 0 else float('inf')

        ord_str = str(ord_2) if ord_2 is not None else "?"
        gap_str = "OUI" if gap else ("NON" if gap is not None else "?")

        print(f"{k:3d} {S:4d} {d:12d} {ord_str:>10} {S-1:5d} "
              f"{gap_str:>8} {two_S1-1:15d} {'OUI' if div_S1 else 'non':>14} "
              f"{ratio:14.4f}")

    # Analyse theorique
    print(f"\n{'='*80}")
    print(f"ANALYSE THEORIQUE : Pourquoi ord_d(2) > S-1 pour k >= 4 ?")
    print(f"{'='*80}")

    print(f"""
OBSERVATIONS :
  1. Pour k=3 (SEUL cas special) : d=5, ord_5(2)=4=S-1. Ici d | (2^4 - 1) = 15.
  2. Pour k >= 4 : ord_d(2) > S-1 TOUJOURS.

ARGUMENT CLE (tentative) :
  Supposons ord_d(2) = r <= S-1. Alors d | (2^r - 1).
  Puisque d = 2^S - 3^k, on a (2^S - 3^k) | (2^r - 1).

  ETAPE 1 : Pour r <= S-2 :
    2^r - 1 <= 2^{{S-2}} - 1.
    On a besoin de d | (2^r - 1), donc 2^r - 1 >= d ou 2^r - 1 = 0.
    Le cas 2^r - 1 = 0 est exclu (r >= 1 => 2^r >= 2).
    Or 2^{{S-2}} - 1 < d = 2^S - 3^k ?

    2^{{S-2}} < 2^S - 3^k + 1
    <=> 3^k < 2^S - 2^{{S-2}} + 1 = 3*2^{{S-2}} + 1
    <=> 3^{{k-1}} < 2^{{S-2}} + 1/3

    Puisque S = ceil(k*log_2(3)), on a S >= k*log_2(3),
    donc S-2 >= k*log_2(3) - 2.
    Et (k-1)*log_2(3) = k*log_2(3) - log_2(3) ~ k*log_2(3) - 1.585.

    Donc 3^{{k-1}} = 2^{{(k-1)*log_2(3)}} et 2^{{S-2}} = 2^{{S-2}}.
    3^{{k-1}} < 2^{{S-2}} <=> (k-1)*log_2(3) < S-2 <=> S > (k-1)*log_2(3) + 2.

    S = ceil(k*log_2(3)) ~ k*log_2(3) + theta (0 <= theta < 1).
    Condition : k*log_2(3) + theta > (k-1)*log_2(3) + 2
    <=> log_2(3) + theta > 2
    <=> theta > 2 - log_2(3) ~ 0.415

    CONCLUSION : Pour theta > 0.415 (environ 58% des cas),
    2^{{S-2}} - 1 < d, donc d ne peut pas diviser 2^r - 1 pour r <= S-2.

    Pour theta <= 0.415 : les seuls candidats sont r = S-2 et r = S-1.

  ETAPE 2 : Pour r = S-1 (le cas critique) :
    d | (2^{{S-1}} - 1) <=> (2^S - 3^k) | (2^{{S-1}} - 1).

    2^{{S-1}} - 1 = q * (2^S - 3^k) pour un entier q >= 1.

    2^{{S-1}} - 1 = q*2^S - q*3^k
    2^{{S-1}} - q*2^S = -1 - q*3^k
    (Hmm, cote gauche negatif si q >= 1 car 2^{{S-1}} < 2^S)
    2^{{S-1}}(1 - 2q) = -(1 + q*3^k)
    2^{{S-1}}(2q - 1) = 1 + q*3^k

    Pour q = 1 : 2^{{S-1}} = 1 + 3^k. Verifions :
      k=3 : 2^4 = 16, 1+27 = 28. NON.
      k=4 : 2^6 = 64, 1+81 = 82. NON.
      ...En fait pour k=3 d=5 et q = (2^4-1)/5 = 3, pas 1.

    Pour q = 3 (k=3) : 2^4*5 = 80 = 1 + 3*27 = 82. NON, c'est 15/5 = 3.

    Reprenons : 2^{{S-1}} - 1 = q*d.
    Pour k=3 : (2^4 - 1)/5 = 15/5 = 3 = q. Verifie.
    Pour k=4 : (2^6 - 1)/47 = 63/47 ~ 1.34. Pas entier.
    Pour k=5 : (2^7 - 1)/13 = 127/13 ~ 9.77. Pas entier.

    OBSERVATION : k=3 est le SEUL cas ou d | (2^{{S-1}} - 1).

  ETAPE 3 : Argument structural pour k >= 4
    On cherche a montrer que (2^S - 3^k) ne divise (2^r - 1) pour aucun r <= S-1.

    Posons D = 2^r - 1 et d = 2^S - 3^k. Si d | D :
      2^r = 1 mod (2^S - 3^k)
      et 2^S = 3^k mod (2^S - 3^k)

    Donc 2^S = 3^k et 2^r = 1, ce qui donne :
      2^{{S mod r}} = 3^k mod d (car 2^r = 1)
      Si r | S : 3^k = 1 mod d, i.e., d | (3^k - 1).
        Mais d = 2^S - 3^k, donc (2^S - 3^k) | (3^k - 1).
        Or 3^k - 1 < 3^k < 2^S, et d = 2^S - 3^k,
        donc (3^k - 1)/d = (3^k - 1)/(2^S - 3^k).
        Pour que ce soit entier, on a besoin 3^k - 1 >= 2^S - 3^k,
        i.e., 2*3^k >= 2^S + 1.
        Or 2^S = 2^{{ceil(k*log_2(3))}} > 3^k (toujours), et
        2*3^k > 2^S ssi 3^k > 2^{{S-1}}, ce qui est TOUJOURS VRAI.
        Donc c'est POSSIBLE en taille. Mais est-ce que ca arrive ?

        Verifions : (3^k - 1) mod (2^S - 3^k) pour k=4..15.
""")

    # Verification numerique
    print(f"\n  Verification : (3^k - 1) mod d et (2^{{S-1}} - 1) mod d :")
    print(f"  {'k':>3} {'S':>4} {'d':>12} {'(3^k-1) mod d':>15} "
          f"{'(2^(S-1)-1) mod d':>18} {'(2^(S-2)-1) mod d':>18}")
    for k in range(3, 22):
        S, d, C = compute_parameters(k)
        if d <= 0:
            continue
        val1 = (pow(3, k) - 1) % d
        val2 = (pow(2, S - 1) - 1) % d if S >= 2 else None
        val3 = (pow(2, S - 2) - 1) % d if S >= 3 else None
        v2_str = str(val2) if val2 is not None else "-"
        v3_str = str(val3) if val3 is not None else "-"
        print(f"  {k:3d} {S:4d} {d:12d} {val1:15d} {v2_str:>18} {v3_str:>18}")


# ============================================================
# EXECUTION PRINCIPALE
# ============================================================

if __name__ == "__main__":
    print("*" * 80)
    print("FRONT 2 : ANALYSE SPECTRALE DE L'AUTOMATE DE HORNER")
    print("*" * 80)

    # Analyser les cas ou d est assez petit pour le calcul matriciel complet
    results = []
    for k in [3, 4, 5, 6, 7, 8]:
        S, d, C = compute_parameters(k)
        if d <= 3000 and C <= 500000:
            r = analyze_spectral(k)
            if r:
                results.append(r)
        else:
            print(f"\nk={k}: SKIP (d={d}, C={C})")

    # Synthese spectrale
    print(f"\n\n{'='*80}")
    print(f"SYNTHESE SPECTRALE")
    print(f"{'='*80}")

    print(f"\n{'k':>3} {'d':>8} {'ord_2':>8} {'ord_3':>6} {'gap?':>5} "
          f"{'#orbites':>9} {'|lambda_1|':>12}")
    print("-" * 60)
    for r in results:
        ev_str = f"{abs(r['eigenvalues_T_top'][0]):.4f}" if r['eigenvalues_T_top'] else "?"
        print(f"{r['k']:3d} {r['d']:8d} {r['ord_2']:8d} {r['ord_3']:6d} "
              f"{'OUI' if r['gap'] else 'NON':>5} {r['n_orbits']:9d} {ev_str:>12}")

    # Tentative de preuve du Theoreme 7.1
    prove_ord_theorem(k_max=21)
