#!/usr/bin/env python3
"""
SP10 Level 8 — Phase I : Verification du Regime A
=====================================================
Objectif : Verifier que le theoreme de Di Benedetto et al. (2020)
permet de borner k_crit dans le Regime A (p < m^4).

ANTI-HALLUCINATION : Chaque calcul theorique est confronte aux donnees.

Partie 0 : Verifier la borne k_crit <= 389
Partie 1 : Calculer d(k) pour k = 69..K_A
Partie 2 : Factoriser d(k) et verifier (Q)
"""

import math
import sys
from sympy import isprime, factorint, nextprime

print("=" * 70)
print("SP10 L8 — PHASE I : VERIFICATION REGIME A")
print("=" * 70)

# ==========================================================
# PARTIE 0 : Verification theorique de k_crit <= K_A
# ==========================================================
print("\n" + "=" * 70)
print("PARTIE 0 : Verification borne k_crit (Di Benedetto)")
print("=" * 70)

# Di Benedetto et al. (2020), J. Number Theory 215, 261-274
# Theoreme : Pour H sous-groupe multiplicatif de F_p* avec |H| > p^{1/4} :
# max_{(a,p)=1} |Sigma_{x in H} e_p(ax)| <= |H|^{1 - 31/2880 + o(1)}
#
# Notation : epsilon_0 = 31/2880
# rho = |Sigma| / |H| <= |H|^{-epsilon_0 + o(1)} = m^{-epsilon_0 + o(1)}

eps0 = 31 / 2880
print(f"\nepsilon_0 = 31/2880 = {eps0:.6f}")
print(f"1/epsilon_0 = {1/eps0:.2f}")

# Dans le Regime A : p < m^4, donc ln(p-1) < 4*ln(m)
# Avec rho <= C_1 * m^{-eps0}, on a |ln(rho)| >= eps0 * ln(m) - ln(C_1)
#
# k_crit = 17 + ln((p-1)/0.041) / |ln(rho)|
#        <= 17 + (4*ln(m) + ln(1/0.041)) / (eps0*ln(m) - ln(C_1))
#
# Pour m -> infini : k_crit -> 17 + 4/eps0

K_A_asymptotic = 17 + 4 / eps0
print(f"\nBorne asymptotique k_crit (m -> infini) = 17 + 4/eps0 = {K_A_asymptotic:.1f}")

# Mais le o(1) dans le theoreme Di Benedetto affecte C_1.
# Soyons conservateurs : supposons rho <= m^{-eps0/2} pour m assez grand.
# Alors |ln(rho)| >= (eps0/2) * ln(m)
# k_crit <= 17 + (4*ln(m) + 3.2) / ((eps0/2)*ln(m))
#        = 17 + 8/eps0 + 6.4/(eps0*ln(m))

K_A_conservative = 17 + 8 / eps0
print(f"Borne conservative (eps0/2) = 17 + 8/eps0 = {K_A_conservative:.1f}")

# Calculons pour des valeurs concretes de m et p
print(f"\n{'m':>6} {'p=m^4':>12} {'rho(eps0)':>12} {'rho(eps0/2)':>12} "
      f"{'k_crit(eps0)':>14} {'k_crit(eps0/2)':>14}")
print("-" * 85)

for m in [10, 50, 100, 200, 500, 1000, 5000, 10000]:
    p_max = m ** 4  # borne sup de p dans Regime A

    # Borne Di Benedetto (optimiste) : rho = m^{-eps0}
    rho_opt = m ** (-eps0)
    if rho_opt < 1 and rho_opt > 0:
        ln_rho_opt = -math.log(rho_opt)  # = eps0 * ln(m)
        k_crit_opt = 17 + (math.log(p_max - 1) + math.log(1/0.041)) / ln_rho_opt
    else:
        k_crit_opt = float('inf')

    # Borne conservative : rho = m^{-eps0/2}
    rho_cons = m ** (-eps0 / 2)
    if rho_cons < 1 and rho_cons > 0:
        ln_rho_cons = -math.log(rho_cons)
        k_crit_cons = 17 + (math.log(p_max - 1) + math.log(1/0.041)) / ln_rho_cons
    else:
        k_crit_cons = float('inf')

    print(f"{m:>6} {p_max:>12} {rho_opt:>12.6f} {rho_cons:>12.6f} "
          f"{k_crit_opt:>14.1f} {k_crit_cons:>14.1f}")

# ==========================================================
# PARTIE 0b : Confrontation avec les DONNEES REELLES (anti-hallucination)
# ==========================================================
print("\n" + "=" * 70)
print("PARTIE 0b : Confrontation donnees reelles vs borne theorique")
print("=" * 70)

# Recalculons rho pour les premiers connus dans le Regime A (p < m^4)
# en utilisant les valeurs REELLES de L5-L7

def compute_rho(p, m):
    """Calcule rho = max_c |sum_{j=0}^{m-1} omega^{c*2^j}| / m"""
    import cmath
    omega = cmath.exp(2j * cmath.pi / p)
    max_val = 0
    # On scanne c = 1..min(p-1, 5000) pour limiter le temps
    limit = min(p - 1, 5000)
    for c in range(1, limit + 1):
        s = sum(omega ** ((c * pow(2, j, p)) % p) for j in range(m))
        val = abs(s) / m
        if val > max_val:
            max_val = val
    return max_val

# Donnees connues des niveaux precedents (ANTI-REGRESSION)
known_data = [
    # (p, m, rho_connu, source)
    (127, 7, 0.618, "L3"),
    (8191, 13, 0.763, "L4"),
    (257, 16, 0.577, "L3"),
    (2731, 26, 0.573, "L4"),
    (2113, 44, 0.543, "L4"),
    (31, 5, 0.540, "L4"),
    (3, 2, 0.500, "L4"),
]

print(f"\n{'p':>8} {'m':>4} {'p/m^4':>10} {'Regime':>8} {'rho_connu':>10} {'rho_Di_B':>10} {'Compatible?':>12}")
print("-" * 75)

for p, m, rho_known, src in known_data:
    ratio = p / (m ** 4)
    regime = "A" if ratio < 1 else "B"

    # Borne Di Benedetto (si applicable)
    if regime == "A":
        rho_dib = m ** (-eps0)
        compatible = "OUI" if rho_known <= rho_dib * 1.1 else "NON ⚠️"
    else:
        rho_dib = float('nan')
        compatible = "N/A (Reg B)"

    print(f"{p:>8} {m:>4} {ratio:>10.4f} {regime:>8} {rho_known:>10.3f} "
          f"{rho_dib:>10.3f} {compatible:>12}")

# ==========================================================
# PARTIE 0c : Quels premiers sont VRAIMENT dans le Regime A ?
# ==========================================================
print("\n" + "=" * 70)
print("PARTIE 0c : Classification des 318 premiers connus (m <= 200)")
print("=" * 70)

# Chargeons les donnees des niveaux precedents
# Pour les 318 premiers avec m <= 200, classifions en Regime A vs B
# Utilisons les factorisations de 2^m - 1

from sympy import factorint

regime_a_count = 0
regime_b_count = 0
regime_a_dangerous = []  # ceux avec k_crit > 68 dans Regime A

print(f"\nAnalyse pour m = 2..50 (67 premiers connus) :")
print(f"{'m':>4} {'p':>15} {'p/m^4':>12} {'Regime':>8}")
print("-" * 45)

for m in range(2, 51):
    N = (1 << m) - 1  # 2^m - 1
    factors = factorint(N)
    for p_factor, exp in factors.items():
        if isprime(p_factor):
            # Verifier que ord_{p_factor}(2) = m
            # (p_factor | 2^m - 1 implique ord | m, mais pas necessairement = m)
            # On verifie que 2^(m/q) != 1 mod p pour tout premier q | m
            actual_ord = m
            for q in factorint(m):
                if pow(2, m // q, p_factor) == 1:
                    actual_ord = -1  # ord < m
                    break
            if actual_ord != m:
                continue

            ratio = p_factor / (m ** 4)
            regime = "A" if ratio < 1 else "B"

            if regime == "A":
                regime_a_count += 1
            else:
                regime_b_count += 1

            if m <= 15 or ratio < 1.5:  # Afficher les cas interessants
                print(f"{m:>4} {p_factor:>15} {ratio:>12.4f} {regime:>8}")

print(f"\nResume partiel (m <= 50) :")
print(f"  Regime A (p < m^4) : {regime_a_count}")
print(f"  Regime B (p >= m^4) : {regime_b_count}")

# ==========================================================
# PARTIE 0d : Le vrai probleme — La constante C_1
# ==========================================================
print("\n" + "=" * 70)
print("PARTIE 0d : Test de la borne Di Benedetto sur donnees reelles")
print("=" * 70)

# Pour les premiers dans le Regime A, verifions si rho <= m^{-eps0}
# En utilisant les rho calcules dans les niveaux precedents

print(f"\nSi rho <= m^{{-eps0}} = m^{{-0.01076}} :")
print(f"  m=10 : rho_max = {10**(-eps0):.4f}")
print(f"  m=50 : rho_max = {50**(-eps0):.4f}")
print(f"  m=100: rho_max = {100**(-eps0):.4f}")
print(f"  m=500: rho_max = {500**(-eps0):.4f}")

print(f"\n⚠️ ATTENTION : m^{{-0.01076}} decroit TRES lentement !")
print(f"  Pour m=10 : borne = {10**(-eps0):.4f} (mais rho_reel peut etre 0.5+)")
print(f"  Pour m=100 : borne = {100**(-eps0):.4f}")

# La borne Di Benedetto est |Sigma| <= m^{1 - 31/2880 + o(1)}
# Donc rho = |Sigma|/m <= m^{-31/2880 + o(1)}
# Pour m = 10 : rho <= 10^{-0.01076 + o(1)} ≈ 0.975...
# C'est TRES faible comme borne ! Elle ne dit presque rien pour petit m.

print(f"\n{'m':>6} {'rho_borne':>12} {'rho < 1?':>10} {'Utile?':>8}")
print("-" * 45)
for m in [5, 7, 10, 13, 16, 20, 50, 100, 200, 500, 1000]:
    rho_bound = m ** (-eps0)
    useful = "OUI" if rho_bound < 0.99 else "NON"
    lt1 = "OUI" if rho_bound < 1 else "NON"
    print(f"{m:>6} {rho_bound:>12.6f} {lt1:>10} {useful:>8}")

print(f"\n★ DECOUVERTE CRITIQUE : La borne m^{{-31/2880}} est MINUSCULE !")
print(f"  Elle vaut 0.95+ pour m < 10000.")
print(f"  Ce n'est PAS une borne qui rend rho PETIT,")
print(f"  c'est une borne qui rend rho < 1 par un EPSILON.")

# Recalculons k_crit avec la borne REELLE
# Si rho = 1 - delta avec delta = 1 - m^{-eps0}
# Pour m grand : delta ≈ eps0 * ln(m) / m ... NON !
# m^{-eps0} = exp(-eps0 * ln(m)), donc 1 - m^{-eps0} ≈ eps0 * ln(m) pour petit eps0*ln(m)
# NON : 1 - exp(-x) ≈ x pour x petit
# Ici x = eps0 * ln(m), pour m = 10000 : x = 0.01076 * 9.21 = 0.099
# Donc delta ≈ 0.099, |ln(rho)| ≈ 0.099

print(f"\n--- Recalcul correct de k_crit ---")
print(f"{'m':>6} {'p=m^4':>14} {'rho_ub':>10} {'delta':>10} {'|ln(rho)|':>10} {'k_crit':>10}")
print("-" * 70)

for m in [100, 500, 1000, 5000, 10000, 50000, 100000]:
    rho_ub = m ** (-eps0)
    delta = 1 - rho_ub
    ln_rho = -math.log(rho_ub)  # = eps0 * ln(m)
    p_max = m ** 4
    k_crit = 17 + (math.log(p_max) + math.log(1/0.041)) / ln_rho
    E = (k_crit - 68) / (p_max - 1)
    print(f"{m:>6} {p_max:>14.0f} {rho_ub:>10.6f} {delta:>10.6f} {ln_rho:>10.6f} {k_crit:>10.1f}")

print(f"\n★ k_crit converge bien vers 17 + 4/eps0 = {K_A_asymptotic:.1f}")
print(f"  Mais cette convergence est LENTE (k_crit > 400 pour m < 50000)")
print(f"  En pratique, K_A ≈ 500 est plus realiste que 389")

# ==========================================================
# PARTIE 0e : SYNTHESE — Borne corrigee
# ==========================================================
print("\n" + "=" * 70)
print("PARTIE 0e : SYNTHESE — Borne k_crit corrigee")
print("=" * 70)

# Pour m >= M_A, avec p < m^4 :
# rho <= m^{-eps0} (Di Benedetto, en negligeant le o(1))
# |ln(rho)| = eps0 * ln(m)
# k_crit <= 17 + (4*ln(m) + 3.2) / (eps0 * ln(m))
#         = 17 + 4/eps0 + 3.2/(eps0 * ln(m))
#         = 388.6 + 297.4/ln(m)

for m in [100, 500, 1000, 5000, 10000, 100000]:
    K_A_m = 17 + 4/eps0 + 3.2/(eps0 * math.log(m))
    print(f"  m = {m:>6} : K_A = {K_A_m:.1f}")

print(f"\n  K_A = 389 est atteint asymptotiquement.")
print(f"  Pour m >= 1000 : K_A < 453. Prenons K_A = 500 par securite.")

# Mais ATTENTION : le o(1) dans Di Benedetto pourrait modifier C_1
# Si C_1 = 2 (par exemple), alors rho <= 2 * m^{-eps0}
# et rho < 1 seulement si m > 2^{1/eps0} = 2^{93} ≈ 10^{28} !!!
# C'est ENORME.

C1_test = 2
m_min_c1 = C1_test ** (1/eps0)
print(f"\n⚠️ Si C_1 = {C1_test} dans rho <= C_1 * m^{{-eps0}} :")
print(f"   rho < 1 seulement si m > C_1^(1/eps0) = {m_min_c1:.0e}")
print(f"   C'est IMPRATICABLE !")

C1_test = 1.01
m_min_c1 = C1_test ** (1/eps0)
print(f"\n   Si C_1 = {C1_test} : m > {m_min_c1:.0f}")

# La vraie question : quel est C_1 dans le theoreme Di Benedetto ?
# Il faut lire le papier pour le savoir.
# POUR L'INSTANT : on ne peut pas affirmer que K_A = 389 sans connaitre C_1.

print(f"\n{'='*70}")
print(f"VERDICT PARTIE 0 :")
print(f"{'='*70}")
print(f"  1. La formule k_crit -> 17 + 4/eps0 = 389 est CORRECTE asymptotiquement")
print(f"  2. MAIS la constante C_1 dans Di Benedetto est INCONNUE")
print(f"     Si C_1 > 1, la borne ne s'applique qu'a m TRES grand")
print(f"  3. La borne eps0 = 31/2880 = 0.01076 est TRES petite")
print(f"     rho <= m^{{-0.01076}} est proche de 1 pour tout m raisonnable")
print(f"  4. CONCLUSION : Le Regime A est theoriquement fermable MAIS")
print(f"     necessite de connaitre C_1. Sans C_1 explicite, K_A est inconnu.")
print(f"  5. ALTERNATIVE : Utiliser la borne de WEIL (rho <= sqrt(p)/m)")
print(f"     qui est COMPLETEMENT EFFECTIVE et donne rho << 1 quand m > sqrt(p)")
