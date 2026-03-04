"""
SESSION 7 — ANALYSE PAR SOMMES DE CARACTERES

OBJECTIF : Exploiter la structure analytique de N_0(d) via caracteres additifs.

THEORIE :
  N_0 = (1/d) * Sum_{t=0}^{d-1} F(t)

  ou F(t) = Sum_C omega^{t * corrSum(C)} avec omega = e^{2*pi*i/d}

  F(0) = C = nombre de compositions restreintes.

  Si |N_0 - C/d| < 1 et C/d < 1, alors N_0 = 0.

  |N_0 - C/d| <= (1/d) * Sum_{t!=0} |F(t)|

  Donc si (1/d) * Sum_{t!=0} |F(t)| < 1 - C/d, on conclut N_0 = 0.

STRUCTURE DE F(t) :
  F(t) = omega^{t*prefix} * G(t)
  G(t) = Sum_{b_1 < ... < b_m} Prod_{j=1}^{m} omega^{t * w_j * 2^{b_j}}

  ou w_j = 3^{m-j} (poids Horner) et m = k-3.

  G(t) se calcule par la recurrence :
    f(0, j) = delta_{j,0}
    f(r, j) = f(r-1, j) + alpha_j(q_r) * f(r-1, j-1)

  avec alpha_j(q) = omega^{t * w_j * 2^q}.

EXPERIENCES :
  1. Calculer F(t) pour tous t, verifier Sum = 0
  2. Calculer L_1 = (1/d) * Sum_{t!=0} |F(t)|, comparer a 1 - C/d
  3. Analyser la structure de |F(t)| (pics, decroissance)
  4. Factorisation : G(t) comme determinant ?
  5. Borne theorique via Weil/Kloosterman
"""

import numpy as np
from math import comb, ceil, log2, gcd
from itertools import combinations

def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    return S, d

def compute_F_via_recurrence(k, p=1, t_val=None):
    """
    Calcule F(t) pour un t donne, via la recurrence sur les positions.

    G(t) = f(n, m) ou :
      f(0, j) = delta_{j,0}
      f(r, j) = f(r-1, j) + alpha_j(q_r) * f(r-1, j-1)

    alpha_j(q) = omega^{t * 3^{m-j} * 2^q mod d}
    """
    S, d = compute_params(k)
    m = k - 3  # nombre de positions a choisir

    if m < 0:
        return 0.0

    omega = np.exp(2j * np.pi / d)
    prefix = (9 + 5 * pow(2, p)) * pow(3, k-3)

    # Positions disponibles
    positions = list(range(p + 2, S))  # {p+2, ..., S-1}
    n = len(positions)

    if m > n:
        return 0.0

    if t_val is None:
        t_val = 0

    # Poids Horner : w_j = 3^{m-j} pour j = 1, ..., m
    weights = [pow(3, m - j) for j in range(1, m + 1)]

    # Recurrence : f[j] pour j = 0, ..., m
    # Initialisation : f[0] = 1, f[j>0] = 0
    f = np.zeros(m + 1, dtype=complex)
    f[0] = 1.0

    for r_idx, q in enumerate(positions):
        # Traiter de m vers 1 pour eviter d'ecraser les valeurs
        for j in range(min(m, r_idx + 1), 0, -1):
            alpha = omega ** ((t_val * weights[j-1] * pow(2, q)) % d)
            f[j] += alpha * f[j-1]

    G_t = f[m]
    F_t = omega ** ((t_val * prefix) % d) * G_t

    return F_t

def compute_all_F(k, p=1):
    """Calcule F(t) pour tous t = 0, ..., d-1."""
    S, d = compute_params(k)

    F_values = np.zeros(d, dtype=complex)
    for t in range(d):
        F_values[t] = compute_F_via_recurrence(k, p, t)

    return F_values

def experiment1_verify_sum(k_range=range(5, 10), p=1):
    """Verifier que Sum F(t) = 0 pour chaque k."""
    print("=" * 70)
    print("EXPERIENCE 1 : Verification Sum F(t) = 0")
    print("=" * 70)

    for k in k_range:
        S, d = compute_params(k)
        if d <= 0 or d > 5000:
            print(f"\n  k={k}: d={d} trop grand, skip")
            continue

        m = k - 3
        n_positions = S - p - 2
        C = comb(n_positions, m) if n_positions >= m else 0

        F_vals = compute_all_F(k, p)
        total = np.sum(F_vals)
        N0_computed = total / d

        print(f"\n  k={k}, S={S}, d={d}, C={C}, C/d={C/d:.6f}")
        print(f"  F(0) = {F_vals[0].real:.6f} + {F_vals[0].imag:.6f}i")
        print(f"  Sum F(t) = {total.real:.6f} + {total.imag:.6f}i")
        print(f"  N_0 = Sum/d = {N0_computed.real:.6f} + {N0_computed.imag:.6f}i")
        print(f"  |N_0| = {abs(N0_computed):.10f}")
        print(f"  N_0 = 0 ? {'OUI' if abs(N0_computed) < 0.01 else 'NON'}")

def experiment2_L1_bound(k_range=range(5, 10), p=1):
    """Calculer (1/d) Sum_{t!=0} |F(t)| et comparer a 1 - C/d."""
    print("\n" + "=" * 70)
    print("EXPERIENCE 2 : Borne L_1 sur les sommes de caracteres")
    print("=" * 70)

    for k in k_range:
        S, d = compute_params(k)
        if d <= 0 or d > 5000:
            print(f"\n  k={k}: d={d} trop grand, skip")
            continue

        m = k - 3
        n_positions = S - p - 2
        C = comb(n_positions, m) if n_positions >= m else 0

        F_vals = compute_all_F(k, p)

        # L1 norm (excluant t=0)
        abs_F = np.abs(F_vals)
        L1 = np.sum(abs_F[1:]) / d
        threshold = 1 - C/d

        # L_inf
        max_F_nonzero = np.max(abs_F[1:])

        print(f"\n  k={k}, S={S}, d={d}, C={C}")
        print(f"  C/d = {C/d:.6f}")
        print(f"  L_1 = (1/d)*Sum_{{t!=0}} |F(t)| = {L1:.6f}")
        print(f"  Seuil = 1 - C/d = {threshold:.6f}")
        print(f"  L_1 < seuil ? {'OUI => N_0 = 0 PROUVE' if L1 < threshold else 'NON'}")
        print(f"  Max |F(t)| (t!=0) = {max_F_nonzero:.6f}")
        print(f"  Ratio L_1/seuil = {L1/threshold:.4f}" if threshold > 0 else "")

        # Si la borne L1 ne suffit pas, analyser de plus pres
        if L1 >= threshold:
            # Combien de t contribuent significativement ?
            big_t = np.sum(abs_F[1:] > C * 0.1)
            print(f"  Nb de t avec |F(t)| > 0.1*C : {big_t}/{d-1}")

def experiment3_F_distribution(k, p=1):
    """Analyser la distribution de |F(t)| pour t != 0."""
    S, d = compute_params(k)

    print(f"\n{'='*60}")
    print(f"EXPERIENCE 3 : Distribution |F(t)|, k={k}")
    print(f"{'='*60}")

    if d > 5000:
        print(f"  d={d} trop grand")
        return

    m = k - 3
    n_positions = S - p - 2
    C = comb(n_positions, m) if n_positions >= m else 0

    F_vals = compute_all_F(k, p)
    abs_F = np.abs(F_vals[1:])  # excluant t=0

    print(f"  d={d}, C={C}, m={m}")
    print(f"  F(0) = {C}")
    print(f"  |F(t)| stats (t != 0):")
    print(f"    min  = {np.min(abs_F):.6f}")
    print(f"    mean = {np.mean(abs_F):.6f}")
    print(f"    max  = {np.max(abs_F):.6f}")
    print(f"    std  = {np.std(abs_F):.6f}")
    print(f"    median = {np.median(abs_F):.6f}")

    # Deciles
    percentiles = [10, 25, 50, 75, 90, 95, 99]
    print(f"    Percentiles:")
    for pct in percentiles:
        val = np.percentile(abs_F, pct)
        print(f"      {pct}% : {val:.6f} ({val/C:.4f} * C)")

    # Top 5 valeurs de |F(t)|
    top_indices = np.argsort(abs_F)[-5:][::-1]
    print(f"\n  Top 5 |F(t)| :")
    for idx in top_indices:
        t = idx + 1  # +1 car on a exclu t=0
        print(f"    t={t}: |F(t)| = {abs_F[idx]:.6f}, "
              f"F(t) = {F_vals[t].real:.4f} + {F_vals[t].imag:.4f}i, "
              f"|F|/C = {abs_F[idx]/C:.4f}")

    # Verifier si les gros F(t) correspondent a t = d/p pour des petits premiers p
    print(f"\n  Structure des gros |F(t)| :")
    for small_p in [2, 3, 5, 7, 11, 13]:
        if d % small_p == 0:
            t_val = d // small_p
            print(f"    t=d/{small_p}={t_val}: |F(t)| = {np.abs(F_vals[t_val]):.6f} ({np.abs(F_vals[t_val])/C:.4f}*C)")

def experiment4_determinant_structure(k, p=1):
    """
    Tenter de voir G(t) comme un determinant.

    Si alpha_j(q) = omega^{w_j * 2^q}, alors la matrice A a entrees
    A[j][i] = alpha_j(q_i) = omega^{w_j * 2^{q_i}}

    G(t) = Sum sur m-sous-ensembles S de colonnes : Prod_{j=1}^m A[j][S_j]

    Ceci est la "somme sur mineurs" de la matrice A.
    Par le theoreme de Cauchy-Binet, c'est un determinant si A est carree...
    Mais A est m x n (m < n), donc c'est la somme sur C(n,m) mineurs m x m.
    """
    S, d = compute_params(k)

    print(f"\n{'='*60}")
    print(f"EXPERIENCE 4 : Structure determinantale, k={k}")
    print(f"{'='*60}")

    if d > 5000:
        print(f"  d={d} trop grand")
        return

    m = k - 3
    positions = list(range(p + 2, S))
    n = len(positions)

    print(f"  m={m}, n={n} (matrice m x n)")

    omega = np.exp(2j * np.pi / d)

    # Pour t=1 (caractere de base)
    t = 1
    weights = [pow(3, m - j) for j in range(1, m + 1)]

    # Construire la matrice A : A[j][i] = omega^{w_j * 2^{positions[i]} mod d}
    A = np.zeros((m, n), dtype=complex)
    for j in range(m):
        for i in range(n):
            exponent = (t * weights[j] * pow(2, positions[i])) % d
            A[j, i] = omega ** exponent

    # G(t=1) par enumeration directe
    G_direct = 0.0
    for subset in combinations(range(n), m):
        prod = 1.0
        for j, col in enumerate(subset):
            prod *= A[j, col]
        G_direct += prod

    # G(t=1) par la recurrence
    G_recurrence = compute_F_via_recurrence(k, p, 1) / (omega ** ((1 * (9 + 5 * pow(2, p)) * pow(3, k-3)) % d))

    print(f"  G(1) direct = {G_direct:.6f}")
    print(f"  G(1) recurrence = {G_recurrence:.6f}")
    print(f"  Difference = {abs(G_direct - G_recurrence):.2e}")

    # Proprietes de la matrice A
    # SVD
    if m <= n:
        U, sigma, Vh = np.linalg.svd(A)
        print(f"\n  Valeurs singulieres de A :")
        for i, s in enumerate(sigma):
            print(f"    sigma_{i+1} = {s:.6f}")

        # Condition number
        cond = sigma[0] / sigma[-1] if sigma[-1] > 1e-15 else float('inf')
        print(f"  Nombre de condition = {cond:.4f}")

    # Somme de tous les mineurs m x m
    # Par Cauchy-Binet : Sum |det(A_S)|^2 = det(A * A^H)
    B = A @ A.conj().T
    det_B = np.linalg.det(B)
    print(f"\n  det(A * A^H) = {det_B.real:.6f} + {det_B.imag:.6f}i")
    print(f"  |det(A * A^H)| = {abs(det_B):.6f}")
    print(f"  Sum_S |det(A_S)|^2 (Cauchy-Binet) = {det_B.real:.6f}")

    # Borne de Hadamard sur |det(A_S)|
    # |det(A_S)| <= Prod sigma_j (par Hadamard)
    hadamard_bound = np.prod(sigma)
    print(f"  Borne de Hadamard : |det(A_S)| <= {hadamard_bound:.6f}")

def experiment5_weil_bound(k_range=range(5, 10), p=1):
    """
    Borne type Weil sur les sommes de caracteres.

    Prediction naive : |F(t)| ~ sqrt(C) pour t != 0 (comportement aleatoire).
    Si C est le nombre de compositions, on s'attend a |F(t)| ~ O(sqrt(C)).

    Borne de type Weil : |F(t)| <= C^{1/2+epsilon} pour "la plupart" des t.
    """
    print("\n" + "=" * 70)
    print("EXPERIENCE 5 : Comparaison borne de Weil")
    print("=" * 70)

    for k in k_range:
        S, d = compute_params(k)
        if d <= 0 or d > 5000:
            continue

        m = k - 3
        n_positions = S - p - 2
        C = comb(n_positions, m) if n_positions >= m else 0

        if C == 0:
            continue

        F_vals = compute_all_F(k, p)
        abs_F = np.abs(F_vals[1:])

        sqrt_C = np.sqrt(C)

        # Fraction de t avec |F(t)| > sqrt(C)
        frac_above = np.sum(abs_F > sqrt_C) / (d - 1)

        # Fraction de t avec |F(t)| > 2*sqrt(C)
        frac_above_2 = np.sum(abs_F > 2 * sqrt_C) / (d - 1)

        # RMS de |F(t)|
        rms = np.sqrt(np.mean(abs_F**2))

        print(f"\n  k={k}, d={d}, C={C}, sqrt(C)={sqrt_C:.4f}")
        print(f"  RMS |F(t)| = {rms:.4f} (vs sqrt(C) = {sqrt_C:.4f})")
        print(f"  RMS/sqrt(C) = {rms/sqrt_C:.4f}")
        print(f"  Fraction |F(t)| > sqrt(C) : {frac_above:.4f}")
        print(f"  Fraction |F(t)| > 2*sqrt(C) : {frac_above_2:.4f}")
        print(f"  Max |F(t)|/sqrt(C) = {np.max(abs_F)/sqrt_C:.4f}")

        # Parseval-like : Sum |F(t)|^2
        parseval = np.sum(np.abs(F_vals)**2)
        print(f"  Sum |F(t)|^2 = {parseval:.4f}")
        print(f"  Sum |F(t)|^2 / d = {parseval/d:.4f} (vs C = {C})")

def experiment6_cancellation_mechanism(k, p=1):
    """
    Comprendre le mecanisme de cancellation Sum_{t!=0} F(t) = -C.

    Decomposer en parties reelle/imaginaire.
    Identifier les t qui contribuent le plus a la cancellation.
    """
    S, d = compute_params(k)

    print(f"\n{'='*60}")
    print(f"EXPERIENCE 6 : Mecanisme de cancellation, k={k}")
    print(f"{'='*60}")

    if d > 5000:
        print(f"  d={d} trop grand")
        return

    m = k - 3
    n_positions = S - p - 2
    C = comb(n_positions, m) if n_positions >= m else 0

    F_vals = compute_all_F(k, p)

    # Verification
    total = np.sum(F_vals)
    print(f"  d={d}, C={C}")
    print(f"  Sum F(t) = {total.real:.8f} + {total.imag:.8f}i (doit etre 0)")
    rest = total - F_vals[0]
    print(f"  Sum_{{t!=0}} F(t) = {rest.real:.4f} + {rest.imag:.4f}i (doit etre -C=-{C})")

    # Contribution cumulee
    cumsum_real = np.cumsum(F_vals.real)
    cumsum_imag = np.cumsum(F_vals.imag)

    # Ou est-ce que la somme partielle passe par 0 ?
    # Chercher les t ou cumsum_real[1:t] ~ -C + C/d * t (tendance lineaire)
    print(f"\n  Sommes partielles (selection) :")
    checkpoints = [d//10, d//5, d//4, d//3, d//2, 2*d//3, 3*d//4, d-1]
    for cp in checkpoints:
        if 0 < cp < d:
            sr = cumsum_real[cp]
            si = cumsum_imag[cp]
            expected_real = C * (cp + 1) / d  # si uniforme
            print(f"    t=0..{cp}: Sum_real = {sr:.4f}, Sum_imag = {si:.4f}, "
                  f"attendu_real = {expected_real:.4f}")

    # Decomposition en sommes partielles par blocs
    block_size = max(1, d // 10)
    print(f"\n  Sommes par blocs de {block_size} :")
    for start in range(0, d, block_size):
        end = min(start + block_size, d)
        block_sum = np.sum(F_vals[start:end])
        print(f"    t=[{start},{end}): Sum = {block_sum.real:.4f} + {block_sum.imag:.4f}i, "
              f"|Sum| = {abs(block_sum):.4f}")

def main():
    p = 1  # s = 3 + 2^p = 5

    # Exp 1 : Verifier Sum F(t) = 0
    experiment1_verify_sum(range(5, 10), p)

    # Exp 2 : Borne L_1
    experiment2_L1_bound(range(5, 10), p)

    # Exp 3 : Distribution |F(t)|
    for k in [5, 6, 7, 8]:
        experiment3_F_distribution(k, p)

    # Exp 4 : Structure determinantale
    for k in [5, 6, 7]:
        experiment4_determinant_structure(k, p)

    # Exp 5 : Borne de Weil
    experiment5_weil_bound(range(5, 10), p)

    # Exp 6 : Mecanisme de cancellation
    for k in [5, 6, 7]:
        experiment6_cancellation_mechanism(k, p)

if __name__ == "__main__":
    main()
