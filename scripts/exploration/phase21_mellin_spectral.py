#!/usr/bin/env python3
"""phase21_mellin_spectral.py — Analyse spectrale de Mellin pour Collatz.

Implémente le cadre Mater-Mboup (transformée de Mellin discrète via
polynômes de Meixner-Pollaczek) appliqué au problème de Collatz.

Phase 21 du Programme Merle.

Sections :
  1. Polynômes de Meixner-Pollaczek et atomes de Mellin
  2. Transformée de Mellin discrète du signal de Steiner
  3. Spectre du signal exponentiel tronqué δ₂^(S)
  4. Vérification de Parseval dans le domaine de Mellin
  5. Factorisation spectrale de la récurrence de Horner
  6. Expansion de Kuznetsov des sommes M(χ)
  7. Diagnostic comparatif (N₀=0 vs N₀>0)

Auteur : Eric Merle (assisté par Claude)
Date : 28 février 2026
"""

import math
import cmath
import numpy as np
from itertools import combinations
from typing import List, Tuple, Dict
import hashlib
import time

# Compatibilité numpy 2.0+ (trapz -> trapezoid)
if hasattr(np, 'trapezoid'):
    np_trapz = np.trapezoid
else:
    np_trapz = np.trapz

# ═══════════════════════════════════════════════════════════════════════
# Section 1 : Polynômes de Meixner-Pollaczek et atomes de Mellin
# ═══════════════════════════════════════════════════════════════════════

def meixner_pollaczek(n_max: int, s: complex) -> np.ndarray:
    """Calcule P_0(s), P_1(s), ..., P_{n_max}(s) via la récurrence à 3 termes.

    Récurrence (Mater-Mboup) :
        (n+1) P_{n+1}(s) = -2s P_n(s) + n P_{n-1}(s)

    Avec P_0(s) = 1, P_1(s) = -2s.
    """
    P = np.zeros(n_max + 1, dtype=complex)
    P[0] = 1.0
    if n_max >= 1:
        P[1] = -2.0 * s
    for n in range(1, n_max):
        P[n + 1] = (-2.0 * s * P[n] + n * P[n - 1]) / (n + 1)
    return P


def mellin_weight(omega: float) -> float:
    """Poids spectral ρ(iω) = 2π / cosh(πω).

    Note : ρ(s) = 2π/cos(πs) pour s ∈ (-1/2, 1/2).
    Sur l'axe imaginaire s = iω : cos(π·iω) = cosh(πω).
    """
    return 2.0 * np.pi / np.cosh(np.pi * omega)


def mellin_atom(n: int, omega: float, P_cache: np.ndarray = None) -> complex:
    """Atome de Mellin A(n, ω) = √ρ(iω) · P_n(iω).

    Utilise un cache de polynômes si fourni.
    """
    rho = mellin_weight(omega)
    if P_cache is not None and n < len(P_cache):
        return np.sqrt(rho) * P_cache[n]
    else:
        P = meixner_pollaczek(n, 1j * omega)
        return np.sqrt(rho) * P[n]


def compute_atoms_grid(n_max: int, omega_grid: np.ndarray) -> np.ndarray:
    """Calcule la grille complète A(n, ω) pour n=0..n_max, ω dans omega_grid.

    Retourne un tableau (n_max+1) x len(omega_grid) de complexes.
    """
    atoms = np.zeros((n_max + 1, len(omega_grid)), dtype=complex)
    for j, omega in enumerate(omega_grid):
        rho = mellin_weight(omega)
        P = meixner_pollaczek(n_max, 1j * omega)
        atoms[:, j] = np.sqrt(rho) * P
    return atoms


# ═══════════════════════════════════════════════════════════════════════
# Section 2 : Signal de Steiner et sa transformée de Mellin
# ═══════════════════════════════════════════════════════════════════════

def compositions(S: int, k: int) -> List[Tuple[int, ...]]:
    """Génère toutes les compositions de Comp(S, k).

    Comp(S, k) = {(A_0, ..., A_{k-1}) : 0 = A_0 < A_1 < ... < A_{k-1} ≤ S-1}
    """
    if k == 1:
        return [(0,)]
    comps = []
    for rest in combinations(range(1, S), k - 1):
        comps.append((0,) + rest)
    return comps


def steiner_signal(A: Tuple[int, ...], k: int, S: int) -> np.ndarray:
    """Construit le signal de Steiner σ_A : {0, ..., S-1} → ℤ.

    σ_A(n) = 3^{k-1-i} si n = A_i, sinon 0.
    """
    sigma = np.zeros(S, dtype=float)
    for i, a in enumerate(A):
        sigma[a] = 3.0 ** (k - 1 - i)
    return sigma


def corrsum(A: Tuple[int, ...], k: int) -> int:
    """Calcule corrSum(A) = Σ 3^{k-1-i} · 2^{A_i} en arithmétique exacte."""
    s = 0
    for i, a in enumerate(A):
        s += (3 ** (k - 1 - i)) * (2 ** a)
    return s


def mellin_transform_signal(signal: np.ndarray, atoms: np.ndarray) -> np.ndarray:
    """TMD d'un signal : F_M(ω) = Σ_n f(n) · A(n, ω).

    Args:
        signal: vecteur de longueur N
        atoms: matrice N x M d'atomes A(n, ω_j)

    Returns:
        vecteur de longueur M (le spectre de Mellin)
    """
    N = len(signal)
    return signal[:N] @ atoms[:N, :]


# ═══════════════════════════════════════════════════════════════════════
# Section 3 : Spectre du signal exponentiel tronqué
# ═══════════════════════════════════════════════════════════════════════

def exponential_signal(S: int, base: float = 2.0) -> np.ndarray:
    """Signal exponentiel tronqué δ_2^{(S)} : n ↦ base^n pour n=0..S-1."""
    return np.array([base ** n for n in range(S)], dtype=float)


# ═══════════════════════════════════════════════════════════════════════
# Section 4 : Vérification de Parseval
# ═══════════════════════════════════════════════════════════════════════

def verify_parseval(signal: np.ndarray, atoms: np.ndarray,
                    omega_grid: np.ndarray) -> Dict:
    """Vérifie l'identité de Parseval : Σ |f(n)|² ≈ ∫ |F_M(ω)|² dω / ρ(ω).

    Utilise l'intégration par trapèzes sur la grille omega.
    """
    energy_time = np.sum(np.abs(signal) ** 2)

    spectrum = mellin_transform_signal(signal, atoms)
    rho_values = np.array([mellin_weight(w) for w in omega_grid])

    integrand = np.abs(spectrum) ** 2 / rho_values
    energy_freq = np_trapz(integrand, omega_grid)

    return {
        'energy_time': energy_time,
        'energy_freq': energy_freq,
        'ratio': energy_freq / energy_time if energy_time > 0 else float('inf'),
        'relative_error': abs(energy_freq - energy_time) / energy_time if energy_time > 0 else float('inf')
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 5 : Factorisation spectrale de Horner
# ═══════════════════════════════════════════════════════════════════════

def horner_chain(A: Tuple[int, ...], k: int, p: int = None) -> List[int]:
    """Calcule la chaîne de Horner c_0, c_1, ..., c_k.

    c_0 = 0, c_{j+1} = 3*c_j + 2^{A_j}.
    Si p est donné, réduit mod p.
    """
    chain = [0]
    c = 0
    for j in range(k):
        c = 3 * c + (2 ** A[j])
        if p is not None:
            c = c % p
        chain.append(c)
    return chain


def spectral_factor(c_j: int, a_j: int, omega: float, p: int) -> complex:
    """Estime le facteur spectral de l'étape j de Horner.

    L'étape j transforme c_j en c_{j+1} = 3*c_j + 2^{a_j} mod p.

    Le facteur spectral est le rapport des spectres :
    h_j(ω) ≈ F_M[δ_{c_{j+1}}](ω) / F_M[δ_{c_j}](ω)
    """
    c_next = (3 * c_j + 2 ** a_j) % p

    A_cj = mellin_atom(c_j, omega) if c_j < 500 else 0.0
    A_cnext = mellin_atom(c_next, omega) if c_next < 500 else 0.0

    if abs(A_cj) < 1e-15:
        return complex(float('inf'))

    return A_cnext / A_cj


def analyze_horner_factorization(A: Tuple[int, ...], k: int, p: int,
                                  omega_grid: np.ndarray) -> Dict:
    """Analyse la factorisation spectrale de la chaîne de Horner."""
    chain = horner_chain(A, k, p)

    results = {
        'chain': chain,
        'corrsum_mod_p': chain[-1],
        'factors': [],
        'product_magnitude': np.ones(len(omega_grid)),
    }

    for j in range(k):
        factors_j = np.array([
            spectral_factor(chain[j], A[j], omega, p)
            for omega in omega_grid
        ])
        results['factors'].append(factors_j)

        mags = np.abs(factors_j)
        mags[mags == float('inf')] = 1.0
        results['product_magnitude'] *= mags

    return results


# ═══════════════════════════════════════════════════════════════════════
# Section 6 : Sommes de caractères et expansion de Kuznetsov
# ═══════════════════════════════════════════════════════════════════════

def find_primitive_root(p: int) -> int:
    """Trouve la plus petite racine primitive modulo p."""
    if p == 2:
        return 1
    phi = p - 1
    factors = set()
    n = phi
    for d in range(2, int(n**0.5) + 1):
        while n % d == 0:
            factors.add(d)
            n //= d
    if n > 1:
        factors.add(n)

    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in factors):
            return g
    return None


def multiplicative_characters(p: int) -> List[np.ndarray]:
    """Calcule les p-1 caractères multiplicatifs de F_p*.

    Le générateur g de F_p* est trouvé, puis χ_j(g^a) = e(j*a/(p-1)).
    """
    g = find_primitive_root(p)
    if g is None:
        return []

    chars = []
    for j in range(p - 1):
        chi = np.zeros(p, dtype=complex)
        for a in range(p - 1):
            r = pow(g, a, p)
            chi[r] = np.exp(2j * np.pi * j * a / (p - 1))
        chars.append(chi)

    return chars


def compute_mellin_sums(k: int, S: int, p: int,
                        comps: List[Tuple[int, ...]]) -> Dict:
    """Calcule les sommes de Mellin M(χ) pour tous les caractères de F_p*.

    M(χ) = Σ_{A: corrSum(A) ≢ 0 (p)} χ(corrSum(A))
    """
    distribution = np.zeros(p, dtype=int)
    for A in comps:
        cs = corrsum(A, k) % p
        distribution[cs] += 1

    N0 = int(distribution[0])
    C = len(comps)

    chars = multiplicative_characters(p)
    if not chars:
        return {'N0': N0, 'C': C, 'error': 'No primitive root found'}

    M_values = []
    for chi in chars:
        M_chi = sum(distribution[r] * chi[r] for r in range(1, p))
        M_values.append(M_chi)

    T_values = []
    for t in range(p):
        T_t = sum(distribution[r] * np.exp(2j * np.pi * t * r / p)
                  for r in range(p))
        T_values.append(T_t)

    return {
        'N0': N0,
        'C': C,
        'distribution': distribution,
        'M_values': np.array(M_values),
        'T_values': np.array(T_values),
        'M_magnitudes': np.abs(np.array(M_values)),
        'T_magnitudes': np.abs(np.array(T_values)),
        'max_M_over_C': np.max(np.abs(np.array(M_values))) / C if C > 0 else 0,
        'max_T_over_C': np.max(np.abs(np.array(T_values[1:]))) / C if C > 0 and len(T_values) > 1 else 0,
    }


def kuznetsov_expansion(M_values: np.ndarray, p: int,
                         n_max: int = 20) -> np.ndarray:
    """Développe les sommes M(χ) sur la base de Meixner-Pollaczek.

    Pour chaque ordre n, calcule le coefficient :
    c_n = (1/(p-1)) Σ_j M(χ_j) · P_n(j/(p-1))

    (normalisation approchée).
    """
    coeffs = np.zeros(n_max + 1, dtype=complex)
    num_chars = len(M_values)

    for n in range(n_max + 1):
        for j in range(num_chars):
            s_j = j / (p - 1) - 0.5
            P = meixner_pollaczek(n, s_j)
            coeffs[n] += M_values[j] * P[n]
        coeffs[n] /= num_chars

    return coeffs


# ═══════════════════════════════════════════════════════════════════════
# Section 7 : Mesures spectrales
# ═══════════════════════════════════════════════════════════════════════

def spectral_flatness(density: np.ndarray) -> float:
    """Mesure de platitude spectrale : ratio moyenne géométrique / moyenne arithmétique.

    Valeur proche de 1 = spectre plat.
    Valeur proche de 0 = spectre concentré.
    """
    positive = density[density > 0]
    if len(positive) == 0:
        return 0.0
    geo_mean = np.exp(np.mean(np.log(positive)))
    arith_mean = np.mean(positive)
    return geo_mean / arith_mean if arith_mean > 0 else 0.0


def compute_spectral_entropy(density: np.ndarray) -> float:
    """Entropie spectrale normalisée (0 = pur, 1 = uniforme)."""
    total = np.sum(density)
    if total <= 0:
        return 0.0
    d = density / total
    d = d[d > 0]
    if len(d) == 0:
        return 0.0
    H = -np.sum(d * np.log2(d))
    H_max = np.log2(len(density))
    return H / H_max if H_max > 0 else 0.0


# ═══════════════════════════════════════════════════════════════════════
# Section 8 : Analyse complète
# ═══════════════════════════════════════════════════════════════════════

def full_analysis(k: int, p: int, omega_range: float = 3.0,
                  n_omega: int = 200) -> Dict:
    """Analyse complète de Mellin pour un couple (k, p)."""
    S = math.ceil(k * math.log2(3))
    C_val = math.comb(S - 1, k - 1)
    d = (1 << S) - 3**k

    omega_grid = np.linspace(-omega_range, omega_range, n_omega)

    comps = compositions(S, k)
    assert len(comps) == C_val, f"Erreur: {len(comps)} compositions vs C={C_val}"

    atoms = compute_atoms_grid(S, omega_grid)

    delta2 = exponential_signal(S)
    delta2_spectrum = mellin_transform_signal(delta2, atoms)
    parseval_delta2 = verify_parseval(delta2, atoms, omega_grid)

    spectral_density = np.zeros(n_omega)
    corrsum_values = []

    for A in comps:
        sigma = steiner_signal(A, k, S)
        sigma_spectrum = mellin_transform_signal(sigma, atoms)
        spectral_density += np.abs(sigma_spectrum) ** 2
        corrsum_values.append(corrsum(A, k))

    spectral_density /= C_val

    char_sums = compute_mellin_sums(k, S, p, comps)

    kuz_coeffs = np.array([])
    if 'M_values' in char_sums and len(char_sums['M_values']) > 0:
        kuz_coeffs = kuznetsov_expansion(char_sums['M_values'], p,
                                          min(20, p - 2))

    horner_analysis = None
    if len(comps) > 0 and p <= 200:
        horner_analysis = analyze_horner_factorization(
            comps[0], k, p, omega_grid[:20]
        )

    return {
        'k': k, 'S': S, 'p': p, 'C': C_val, 'd': d,
        'N0': char_sums.get('N0', -1),
        'C_over_p': C_val / p,
        'omega_grid': omega_grid,
        'spectral_density': spectral_density,
        'delta2_spectrum': delta2_spectrum,
        'parseval_delta2': parseval_delta2,
        'char_sums': char_sums,
        'kuznetsov_coeffs': kuz_coeffs,
        'horner_analysis': horner_analysis,
        'corrsum_values': corrsum_values,
    }


# ═══════════════════════════════════════════════════════════════════════
# Section 9 : Programme principal
# ═══════════════════════════════════════════════════════════════════════

def main():
    t0 = time.time()

    print("=" * 72)
    print("Phase 21 — Analyse Spectrale de Mellin (Mater-Mboup)")
    print("Programme Merle — Projet Collatz-Junction-Theorem")
    print("=" * 72)
    print()

    # ─── Cas de test ───
    test_cases = [
        (2, 7,   "q2 (N0=1, CYCLE RESIDUEL)", 1),
        (3, 5,   "k=3 (N0=0, exclu CRT)", 0),
        (5, 13,  "q3 (N0=0, exclusion chirurgicale)", 0),
        (7, 83,  "k=7 (N0=0, biais structurel P=0.38%)", 0),
        (8, 7,   "k=8 (N0=120, non exclu par petit p)", 120),
        (8, 233, "k=8 (N0=0, exclu par grand p)", 0),
    ]

    # ─── Section 1 : Polynômes de Meixner-Pollaczek ───
    print("-" * 72)
    print("S1. Polynomes de Meixner-Pollaczek -- verification")
    print("-" * 72)

    n_test = 10
    s_test = 0.3 + 0.2j
    P = meixner_pollaczek(n_test, s_test)
    print(f"P_0({s_test}) = {P[0]:.6f} (attendu: 1)")
    print(f"P_1({s_test}) = {P[1]:.6f} (attendu: {-2*s_test:.6f})")

    omega_grid = np.linspace(-5, 5, 500)
    atoms = compute_atoms_grid(8, omega_grid)

    ortho_00 = np.real(np_trapz(atoms[0, :] * np.conj(atoms[0, :]), omega_grid))
    ortho_01 = np.abs(np_trapz(atoms[0, :] * np.conj(atoms[1, :]), omega_grid))
    ortho_05 = np.abs(np_trapz(atoms[0, :] * np.conj(atoms[5, :]), omega_grid))

    print(f"\nOrthogonalite des atomes (grille w in [-5, 5], 500 pts) :")
    print(f"  <A(0,.), A(0,.)> = {ortho_00:.6f}  (attendu: ~1)")
    print(f"  |<A(0,.), A(1,.)>| = {ortho_01:.6f}  (attendu: ~0)")
    print(f"  |<A(0,.), A(5,.)>| = {ortho_05:.6f}  (attendu: ~0)")
    print()

    # ─── Analyse par cas ───
    all_results = {}

    for k, p, label, N0_exp in test_cases:
        S = math.ceil(k * math.log2(3))
        C = math.comb(S - 1, k - 1)
        d = (1 << S) - 3**k

        if C > 5_000_000:
            print(f"\n{'-' * 72}")
            print(f"SKIP: k={k}, p={p} ({label}) -- C={C:,} trop grand")
            continue

        print(f"\n{'=' * 72}")
        print(f"ANALYSE : k={k}, S={S}, p={p}, C={C}, d={d}")
        print(f"  {label}")
        print(f"  C/p = {C/p:.4f}, C/d = {C/d:.4f}")
        print(f"{'=' * 72}")

        result = full_analysis(k, p, omega_range=4.0, n_omega=300)
        all_results[(k, p)] = result

        N0_calc = result['N0']
        status = "OK" if N0_calc == N0_exp else "INATTENDU"
        print(f"\n  N0(p={p}) = {N0_calc}  [{status}]")

        # Parseval
        pv = result['parseval_delta2']
        print(f"\n  S4. Parseval delta_2^({S}) :")
        print(f"    Energie temporelle = {pv['energy_time']:.4e}")
        print(f"    Energie frequentielle = {pv['energy_freq']:.4e}")
        print(f"    Ratio = {pv['ratio']:.6f}")
        print(f"    Erreur relative = {pv['relative_error']:.4e}")

        # Densite spectrale
        sd = result['spectral_density']
        flatness = spectral_flatness(sd)
        entropy = compute_spectral_entropy(sd)

        print(f"\n  S2. Densite spectrale de Mellin mu_k(w) :")
        print(f"    Platitude spectrale = {flatness:.6f}  (1=plat, 0=concentre)")
        print(f"    Entropie spectrale = {entropy:.6f}  (1=uniforme)")
        print(f"    Max mu_k = {np.max(sd):.4e} a w = {result['omega_grid'][np.argmax(sd)]:.3f}")
        print(f"    Ratio max/mean = {np.max(sd)/np.mean(sd):.4f}")

        # Sommes de caracteres
        cs = result['char_sums']
        print(f"\n  S6. Sommes de caracteres :")
        print(f"    max|M(chi)|/C = {cs['max_M_over_C']:.6f}")
        print(f"    max|T(t)|/C = {cs['max_T_over_C']:.6f}")

        if len(cs.get('M_magnitudes', [])) > 0:
            M_mags = cs['M_magnitudes']
            M_nontrivial = M_mags[1:] if len(M_mags) > 1 else M_mags
            print(f"    |M(chi_0)| = {M_mags[0]:.4f}  (= C - N0 = {C - N0_calc})")
            if len(M_nontrivial) > 0:
                print(f"    max|M(chi)| (non-trivial) = {np.max(M_nontrivial):.4f}")
                print(f"    mean|M(chi)| (non-trivial) = {np.mean(M_nontrivial):.4f}")
                print(f"    |M(chi)|/sqrt(C) = {np.max(M_nontrivial)/np.sqrt(C):.4f}")

        # Expansion de Kuznetsov
        kuz = result['kuznetsov_coeffs']
        if len(kuz) > 0:
            kuz_mags = np.abs(kuz)
            print(f"\n  S6b. Expansion de Kuznetsov (coefficients |c_n|) :")
            max_kuz = np.max(kuz_mags) + 1e-15
            for n in range(min(8, len(kuz))):
                bar_len = int(kuz_mags[n] / max_kuz * 30)
                bar = "#" * bar_len
                print(f"    c_{n:2d} = {kuz_mags[n]:.6f}  {bar}")

            if len(kuz_mags) > 5 and kuz_mags[0] > 1e-15:
                decay_ratio = kuz_mags[5] / kuz_mags[0]
                print(f"    Ratio c_5/c_0 = {decay_ratio:.6f}")

    # ─── Diagnostic comparatif ───
    print(f"\n{'=' * 72}")
    print("DIAGNOSTIC COMPARATIF")
    print(f"{'=' * 72}")

    print(f"\n{'k':>3} {'p':>6} {'N0':>5} {'C/p':>8} {'Platit.':>8} {'Entropie':>8} "
          f"{'max|M|/C':>10} {'|M|/sqrtC':>10}")
    print("-" * 72)

    for (k, p), result in sorted(all_results.items()):
        sd = result['spectral_density']
        flat = spectral_flatness(sd)
        ent = compute_spectral_entropy(sd)
        N0 = result['N0']
        C = result['C']

        cs = result['char_sums']
        max_M = cs['max_M_over_C'] * C if 'max_M_over_C' in cs else 0
        M_over_sqrtC = max_M / np.sqrt(C) if C > 0 else 0

        marker = " <-- ZERO NON EXCLU" if N0 > 0 else ""
        print(f"{k:3d} {p:6d} {N0:5d} {C/p:8.4f} {flat:8.6f} {ent:8.6f} "
              f"{cs.get('max_M_over_C', 0):10.6f} {M_over_sqrtC:10.4f}{marker}")

    # ─── Predictions ───
    print(f"\n{'=' * 72}")
    print("VERIFICATION DES PREDICTIONS")
    print(f"{'=' * 72}")

    cases_N0_zero = [(k, p) for (k, p), r in all_results.items() if r['N0'] == 0]
    cases_N0_pos = [(k, p) for (k, p), r in all_results.items() if r['N0'] > 0]

    if cases_N0_zero and cases_N0_pos:
        flat_zero = np.mean([spectral_flatness(all_results[kp]['spectral_density'])
                            for kp in cases_N0_zero])
        flat_pos = np.mean([spectral_flatness(all_results[kp]['spectral_density'])
                           for kp in cases_N0_pos])

        P1_verdict = "CONFIRMEE" if flat_zero > flat_pos else "INFIRMEE"
        print(f"\nP1 (platitude N0=0 > N0>0) :")
        print(f"  Platitude moyenne N0=0 : {flat_zero:.6f}")
        print(f"  Platitude moyenne N0>0 : {flat_pos:.6f}")
        print(f"  Verdict : {P1_verdict}")

    print(f"\nP4 (decroissance de Kuznetsov) :")
    for (k, p), result in sorted(all_results.items()):
        kuz = result['kuznetsov_coeffs']
        if len(kuz) > 5:
            kuz_mags = np.abs(kuz)
            c0 = kuz_mags[0]
            if c0 > 1e-15:
                decay = kuz_mags[5] / c0
                N0 = result['N0']
                verdict = "decroissance" if decay < 0.5 else "persistance"
                print(f"  k={k}, p={p} (N0={N0}): c_5/c_0 = {decay:.4f} [{verdict}]")

    elapsed = time.time() - t0

    print(f"\n{'=' * 72}")
    print(f"Temps d'execution : {elapsed:.1f}s")

    data_str = str([(k, p, all_results[(k,p)]['N0'])
                    for (k,p) in sorted(all_results.keys())])
    sha = hashlib.sha256(data_str.encode()).hexdigest()[:16]
    print(f"SHA256(resultats)[:16] : {sha}")
    print(f"{'=' * 72}")


if __name__ == "__main__":
    main()
