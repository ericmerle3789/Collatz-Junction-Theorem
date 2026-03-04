"""
SESSION 6 — PISTE SPECTRALE : Matrice de transfert de l'automate ordonne

OBJECTIF : Capturer l'interaction ordre × structure multiplicative
dans les proprietes spectrales d'une matrice de transfert.

IDEE CLE : L'automate de Horner avec positions ordonnees peut etre
encode comme un produit de matrices. Si on definit :

  M_p = matrice d x d ou M_p[c', c] = 1 si c' = (3c + 2^p) mod d

alors N_0(d) = (M_{p_{k-1}} * ... * M_{p_1})[0, 1]
summe sur toutes les suites p_1 < p_2 < ... < p_{k-1}.

La somme sur les suites ordonnees est la k-1 eme FONCTION SYMETRIQUE
ELEMENTAIRE des matrices M_1, ..., M_{S-1} :

  e_{k-1}(M_1, ..., M_{S-1}) = Sum_{1<=i_1<...<i_{k-1}<=S-1} M_{i_{k-1}} * ... * M_{i_1}

Et N_0(d) = e_{k-1}[0, 1].

NOUVELLE APPROCHE (session 6) : Analyser les proprietes spectrales de
cette somme de produits. L'interaction ordre × structure devrait apparaitre
dans le spectre.

EXPERIENCE 1 : Calculer e_{k-1} directement et analyser son spectre.
EXPERIENCE 2 : Definir la matrice de transfert "restreinte" aux positions ordonnees
               et voir si le spectre explique pourquoi e_{k-1}[0,1] = 0.
EXPERIENCE 3 : Comparer avec la somme NON ordonnee (T = Sum M_p)^{k-1}.
"""

import numpy as np
from math import gcd, ceil, log2, comb
from itertools import combinations

def compute_params(k):
    """Calcule S et d pour un k donne."""
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    return S, d

def build_permutation_matrix(d, p):
    """Construit M_p : c -> (3c + 2^p) mod d."""
    M = np.zeros((d, d), dtype=np.float64)
    two_p = pow(2, p, d)
    for c in range(d):
        c_next = (3 * c + two_p) % d
        M[c_next, c] = 1.0
    return M

def compute_elementary_symmetric(k):
    """
    Calcule e_{k-1}(M_1, ..., M_{S-1}) par la recurrence :
      f_0(q) = I
      f_j(q) = f_j(q-1) + M_q * f_{j-1}(q-1)

    e_{k-1} = f_{k-1}(S-1)
    """
    S, d = compute_params(k)

    if d > 5000:
        print(f"  SKIP k={k} (d={d} trop grand pour matrices pleines)")
        return None, S, d

    print(f"\n{'='*60}")
    print(f"k={k}, S={S}, d={d}, C={comb(S-1, k-1)}")
    print(f"{'='*60}")

    # Precalculer les matrices
    matrices = {}
    for p in range(1, S):
        matrices[p] = build_permutation_matrix(d, p)

    # Recurrence
    # f_j[q] stocke les couches, mais on n'a besoin que de la derniere
    # f_j(q) = matrice d x d

    # Initialement : f_0 = I pour tout q
    # On calcule f_1(q), f_2(q), ..., f_{k-1}(q) par q croissant

    # Pour economiser la memoire : on ne garde que f_j(q) pour j = 0..k-1
    # et on itere sur q

    n_steps = k - 1  # nombre de steps de l'automate

    # f[j] = f_j(q) courant (matrice d x d)
    f = [None] * (n_steps + 1)
    f[0] = np.eye(d)
    for j in range(1, n_steps + 1):
        f[j] = np.zeros((d, d))

    # Iterer q de 1 a S-1
    for q in range(1, S):
        M_q = matrices[q]
        # Mettre a jour de j=n_steps vers j=1 (pour eviter d'ecraser)
        for j in range(min(n_steps, q), 0, -1):
            f[j] = f[j] + M_q @ f[j-1]

    e_km1 = f[n_steps]
    return e_km1, S, d

def analyze_spectrum(e_km1, k, S, d):
    """Analyse le spectre de e_{k-1}."""
    C = comb(S-1, k-1)

    # Verification N_0(d)
    N0 = e_km1[0, 1]
    print(f"\n--- Verification ---")
    print(f"  e_{{k-1}}[0, 1] = {N0:.6f}  (N_0(d) devrait etre 0)")
    print(f"  Trace(e_{{k-1}}) = {np.trace(e_km1):.0f}  (devrait etre C = {C})")

    # Spectre
    eigenvalues = np.linalg.eigvals(e_km1)
    eigenvalues_sorted = sorted(eigenvalues, key=lambda x: -abs(x))

    print(f"\n--- Spectre de e_{{k-1}} ---")
    print(f"  Valeur propre dominante : |lambda_1| = {abs(eigenvalues_sorted[0]):.4f}")
    if len(eigenvalues_sorted) > 1:
        print(f"  Deuxieme :               |lambda_2| = {abs(eigenvalues_sorted[1]):.4f}")
    if len(eigenvalues_sorted) > 2:
        print(f"  Troisieme :              |lambda_3| = {abs(eigenvalues_sorted[2]):.4f}")

    # Ratio spectral
    if len(eigenvalues_sorted) > 1 and abs(eigenvalues_sorted[1]) > 0:
        ratio = abs(eigenvalues_sorted[0]) / abs(eigenvalues_sorted[1])
        print(f"  Ratio |lambda_1|/|lambda_2| = {ratio:.4f}")

    # Distribution des valeurs propres
    abs_eigs = sorted([abs(ev) for ev in eigenvalues], reverse=True)
    print(f"\n  Top 10 |eigenvalues| :")
    for i, ev in enumerate(abs_eigs[:10]):
        print(f"    [{i}] {ev:.6f}")

    # Rang de e_{k-1}
    rank = np.linalg.matrix_rank(e_km1, tol=1e-8)
    print(f"\n  Rang de e_{{k-1}} : {rank} / {d}")

    # Colonne 1 (etat initial c_0 = 1)
    col_1 = e_km1[:, 1]
    print(f"\n--- Colonne 1 (distribution des etats finaux depuis c_0=1) ---")
    nonzero_count = np.sum(np.abs(col_1) > 0.5)
    print(f"  Nombre d'etats atteints : {int(nonzero_count)} / {d}")
    print(f"  Total chemins : {np.sum(col_1):.0f}  (devrait etre C = {C})")
    print(f"  e_km1[0, 1] = {col_1[0]:.0f}  (target = 0)")

    # Quels residus NE sont PAS atteints ?
    missing = [r for r in range(d) if abs(col_1[r]) < 0.5]
    if len(missing) <= 20:
        print(f"  Residus manquants : {missing}")
    else:
        print(f"  Nombre de residus manquants : {len(missing)}")

    return eigenvalues_sorted

def compare_ordered_vs_unordered(k):
    """
    Compare le spectre de e_{k-1} (ordonne) avec T^{k-1} (non ordonne).
    """
    S, d = compute_params(k)

    if d > 3000:
        print(f"  SKIP k={k} (d={d} trop grand)")
        return

    C = comb(S-1, k-1)

    print(f"\n{'='*60}")
    print(f"COMPARAISON ORDONNE vs NON-ORDONNE : k={k}, d={d}")
    print(f"{'='*60}")

    # Matrice T = somme des M_p
    T = np.zeros((d, d))
    for p in range(1, S):
        T += build_permutation_matrix(d, p)

    # T^{k-1} (non ordonne)
    T_power = np.linalg.matrix_power(T, k-1)

    # e_{k-1} (ordonne)
    e_km1, _, _ = compute_elementary_symmetric(k)
    if e_km1 is None:
        return

    print(f"\n--- T^{{k-1}} (non ordonne) ---")
    print(f"  T^{{k-1}}[0, 1] = {T_power[0, 1]:.0f}")
    print(f"  Si non-zero : le target EST atteignable sans ordre")

    print(f"\n--- e_{{k-1}} (ordonne) ---")
    print(f"  e_{{k-1}}[0, 1] = {e_km1[0, 1]:.0f}")

    # Difference
    diff = T_power[0, 1] - e_km1[0, 1]
    print(f"\n--- Difference ---")
    print(f"  T^{{k-1}}[0,1] - e_{{k-1}}[0,1] = {diff:.0f}")
    if T_power[0, 1] > 0 and e_km1[0, 1] == 0:
        print(f"  ==> La contrainte d'ordre SEULE elimine {int(T_power[0,1])} chemins vers 0")

    # Spectre de T
    eigs_T = np.linalg.eigvals(T)
    eigs_T_sorted = sorted(eigs_T, key=lambda x: -abs(x))
    print(f"\n--- Spectre de T ---")
    print(f"  lambda_1(T) = {eigs_T_sorted[0]:.4f} (devrait etre S-1 = {S-1})")
    if len(eigs_T_sorted) > 1:
        print(f"  lambda_2(T) = {abs(eigs_T_sorted[1]):.4f}")

def row_column_analysis(k):
    """
    Analyse fine de la colonne 1 et de la ligne 0 de e_{k-1}.
    Pour comprendre POURQUOI e_{k-1}[0,1] = 0.
    """
    e_km1, S, d = compute_elementary_symmetric(k)
    if e_km1 is None:
        return

    C = comb(S-1, k-1)

    print(f"\n{'='*60}")
    print(f"ANALYSE LIGNE 0 / COLONNE 1 : k={k}")
    print(f"{'='*60}")

    # Colonne 1 : distribution des etats finaux depuis c_0=1
    col_1 = e_km1[:, 1]
    print(f"\n--- Colonne 1 (etats finaux depuis c_0=1) ---")
    for r in range(d):
        if abs(col_1[r]) > 0.5:
            print(f"  etat {r:4d} : {int(col_1[r]):4d} chemins")

    # Ligne 0 : quels etats initiaux menent a c_{k-1}=0 ?
    row_0 = e_km1[0, :]
    print(f"\n--- Ligne 0 (etats initiaux menant a 0) ---")
    initial_to_zero = []
    for c_init in range(d):
        if abs(row_0[c_init]) > 0.5:
            initial_to_zero.append((c_init, int(row_0[c_init])))
            print(f"  c_0={c_init:4d} : {int(row_0[c_init]):4d} chemins vers 0")

    print(f"\n  Nombre d'etats initiaux menant a 0 : {len(initial_to_zero)} / {d}")
    print(f"  c_0=1 ABSENT (confirme N_0=0) : {1 not in [x[0] for x in initial_to_zero]}")

    # Analyse de la structure : decomposition de Fourier
    print(f"\n--- Decomposition de Fourier de la colonne 1 ---")
    col_fft = np.fft.fft(col_1)
    print(f"  col_fft[0] = {col_fft[0].real:.2f} (= C = {C})")
    significant = [(t, abs(col_fft[t])) for t in range(1, d) if abs(col_fft[t]) > C * 0.01]
    print(f"  Coefficients significatifs (|F(t)| > 0.01*C) : {len(significant)}")
    for t, amp in sorted(significant, key=lambda x: -x[1])[:10]:
        print(f"    t={t}: |F(t)| = {amp:.2f}  (= {amp/C:.4f} * C)")

    # Verification de l'annulation
    sum_nonzero = sum(col_fft[t] for t in range(1, d))
    print(f"\n  Sum{{F(t), t>=1}} = {sum_nonzero.real:.6f} + {sum_nonzero.imag:.6f}i")
    print(f"  Devrait etre -C = {-C} (si N_0=0)")

def horner_transfer_spectrum(k):
    """
    Analyse spectrale complete de la matrice de transfert ordonnee.
    On construit la matrice "Big Transfer" sur l'espace etendu
    (etat, derniere_position) pour encoder la contrainte d'ordre.
    """
    S, d = compute_params(k)

    # Espace etendu : (etat c in Z/dZ, derniere position p in {0,...,S-1})
    # Dimension = d * S
    dim = d * S

    if dim > 5000:
        print(f"  SKIP k={k} (dim={dim} trop grand)")
        return

    print(f"\n{'='*60}")
    print(f"MATRICE DE TRANSFERT ORDONNEE ETENDUE : k={k}, d={d}, S={S}")
    print(f"Espace etendu : (etat, position) de dimension {dim}")
    print(f"{'='*60}")

    # Matrice de transfert etendue T_ext
    # T_ext[(c', p'), (c, p)] = 1 si c' = (3c + 2^{p'}) mod d et p' > p
    T_ext = np.zeros((dim, dim))

    def idx(c, p):
        return c * S + p

    for c in range(d):
        for p in range(S):  # derniere position utilisee
            for p_next in range(p + 1, S):  # nouvelle position > p
                c_next = (3 * c + pow(2, p_next, d)) % d
                T_ext[idx(c_next, p_next), idx(c, p)] = 1.0

    # N_0(d) = somme sur q_{k-1} de (T_ext^{k-2})[(0, q_{k-1}), (c_1, p_1)]
    # ou c_1 = (3 + 2^{p_1}) mod d pour l'etat initial c_0 = 1

    # Spectre de T_ext
    print(f"\n  Calcul du spectre de T_ext ({dim}x{dim})...")
    eigenvalues = np.linalg.eigvals(T_ext)
    eigs_sorted = sorted(eigenvalues, key=lambda x: -abs(x))

    print(f"\n--- Spectre de T_ext ---")
    print(f"  Top 15 |eigenvalues| :")
    for i, ev in enumerate(eigs_sorted[:15]):
        print(f"    [{i}] |lambda| = {abs(ev):.6f}, phase = {np.angle(ev):.4f}")

    # Nombre de valeurs propres nulles
    zero_count = sum(1 for ev in eigenvalues if abs(ev) < 1e-8)
    print(f"\n  Valeurs propres nulles : {zero_count} / {dim}")
    print(f"  Valeurs propres non-nulles : {dim - zero_count}")

    # Valeur propre dominante
    lambda_1 = abs(eigs_sorted[0])
    if len(eigs_sorted) > 1 and abs(eigs_sorted[1]) > 1e-10:
        lambda_2 = abs(eigs_sorted[1])
        print(f"\n  Gap spectral : |lambda_1|/|lambda_2| = {lambda_1/lambda_2:.4f}")

    return eigenvalues

def main():
    print("=" * 70)
    print("SESSION 6 — PISTE SPECTRALE : Automate ordonne")
    print("=" * 70)

    # EXPERIENCE 1 : Spectre de e_{k-1} pour petits k
    print("\n\n" + "=" * 70)
    print("EXPERIENCE 1 : Spectre de e_{k-1} (fonctions symetriques)")
    print("=" * 70)

    for k in [3, 4, 5, 6, 7, 8]:
        e_km1, S, d = compute_elementary_symmetric(k)
        if e_km1 is not None:
            analyze_spectrum(e_km1, k, S, d)

    # EXPERIENCE 2 : Comparaison ordonne vs non-ordonne
    print("\n\n" + "=" * 70)
    print("EXPERIENCE 2 : Ordonne vs Non-ordonne")
    print("=" * 70)

    for k in [3, 4, 5]:
        compare_ordered_vs_unordered(k)

    # EXPERIENCE 3 : Analyse ligne/colonne pour k=5
    print("\n\n" + "=" * 70)
    print("EXPERIENCE 3 : Analyse fine colonne 1 / ligne 0")
    print("=" * 70)

    row_column_analysis(5)

    # EXPERIENCE 4 : Matrice de transfert etendue (espace etat × position)
    print("\n\n" + "=" * 70)
    print("EXPERIENCE 4 : Matrice de transfert ordonnee etendue")
    print("=" * 70)

    for k in [3, 4, 5]:
        horner_transfer_spectrum(k)

    print("\n\n" + "=" * 70)
    print("FIN DE L'ANALYSE SPECTRALE")
    print("=" * 70)

if __name__ == "__main__":
    main()
