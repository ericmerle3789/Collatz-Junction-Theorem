#!/usr/bin/env python3
"""
R168 — Analyse Corrigee des Resultats
======================================

PROBLEME IDENTIFIE : Le ratio de Katz E_4/|S|^2 n'est PAS le bon indicateur
quand |Simplex| >> sqrt(p). Dans ce regime, les collisions ALEATOIRES dominent.

Le bon indicateur est E_4 / E_4_random (excess ratio).

REGIME CRITIQUE : Le test de Larsen est informatif SEULEMENT quand |S| ~ sqrt(p).
  - k=3, p=101 : |S|=15, sqrt(p)~10    -> INFORMATIF (|S| ~ sqrt(p))
  - k=4, p=431 : |S|=56, sqrt(p)~21    -> BORDERLINE (|S| ~ 2.7*sqrt(p))
  - k>=5       : |S| >> sqrt(p)         -> NON INFORMATIF (regime de birthday)

Protocole Fail-Closed : on ne valide RIEN sans justification solide.
"""

import json


def analyze():
    with open("R168_results.json") as f:
        results = json.load(f)

    print("=" * 72)
    print("R168 — ANALYSE CORRIGEE (Post-Execution)")
    print("=" * 72)

    # ===== 1. REGIME |S| vs sqrt(p) =====
    print("\n1. CLASSIFICATION PAR REGIME |S| vs sqrt(p)")
    print("-" * 60)

    informative = []
    borderline = []
    uninformative = []

    for r in results["test_A_additive_energy"]:
        N = r["n_compositions"]
        p = r["p"]
        ratio_N_sqrtp = N / (p ** 0.5)
        r["ratio_N_sqrtp"] = ratio_N_sqrtp

        if ratio_N_sqrtp < 2:
            category = "INFORMATIF"
            informative.append(r)
        elif ratio_N_sqrtp < 5:
            category = "BORDERLINE"
            borderline.append(r)
        else:
            category = "NON INFORMATIF (birthday)"
            uninformative.append(r)

        print(f"  k={r['k']}, p={r['p']:>6d} : |S|={N:>6d}, "
              f"|S|/sqrt(p) = {ratio_N_sqrtp:>8.1f}  -> {category}")

    # ===== 2. EXCES DE COLLISIONS (le vrai test) =====
    print("\n2. EXCES DE COLLISIONS : E_4 / E_4_random")
    print("-" * 60)
    print("  Si E_4/E_4_random ~ 1.0 : pas d'exces (bruit uniforme)")
    print("  Si E_4/E_4_random > 1.5 : exces structure -> symetries cachees")
    print()

    for r in results["test_A_additive_energy"]:
        excess = r["excess_ratio"]
        if excess is not None:
            status = "OK (uniforme)" if excess < 1.1 else (
                "EXCES MODERE" if excess < 1.5 else "EXCES FORT")
            print(f"  k={r['k']}, p={r['p']:>6d} : E_4/E_4_random = {excess:.4f}  -> {status}")

    # ===== 3. TEST DE LARSEN (Skewness) - CAS INFORMATIFS SEULEMENT =====
    print("\n3. TEST DE LARSEN (SKEWNESS) — Cas Informatifs")
    print("-" * 60)
    print("  SL_n (maximal, asymetrique) : |skewness| > 0.1")
    print("  Sp/O (auto-dual, symetrique) : |skewness| ~ 0")
    print()

    for r in results["test_B_moment_skewness"]:
        N = r["N"]
        p = r["p"]
        ratio_N_sqrtp = N / (p ** 0.5)
        skew = r["skewness"]

        if ratio_N_sqrtp < 5:  # Informatif ou borderline
            regime = "INFORMATIF" if ratio_N_sqrtp < 2 else "BORDERLINE"
            verdict = "SL_n (asymetrie)" if abs(skew) > 0.1 else "Sp/O (symetrie)"
            print(f"  k={r['k']}, p={r['p']:>6d} : skew={skew:>10.6f}  "
                  f"|S|/sqrt(p)={ratio_N_sqrtp:.1f}  [{regime}]  -> {verdict}")
        else:
            print(f"  k={r['k']}, p={r['p']:>6d} : skew={skew:>10.6f}  "
                  f"|S|/sqrt(p)={ratio_N_sqrtp:.1f}  [NON INFORMATIF — ignore]")

    # ===== 4. EQUIDISTRIBUTION (Test C) =====
    print("\n4. EQUIDISTRIBUTION DES corrSum mod p")
    print("-" * 60)

    for r in results["test_C_collision_structure"]:
        gini = r["gini_coefficient"]
        coverage = r["p_coverage"]
        uniform = r["distribution_uniform"]
        print(f"  k={r['k']}, p={r['p']:>6d} : Gini={gini:.4f}, "
              f"couverture={coverage}%, uniforme={uniform}")

    # ===== VERDICT CORRIGE =====
    print("\n" + "=" * 72)
    print("VERDICT CORRIGE R168")
    print("=" * 72)

    print("""
CONSTATATIONS :

1. E_4/E_4_random ~ 1.0 pour TOUS les (k,p) testes.
   -> Aucun exces structurel de collisions.
   -> Les corrSum mod p se comportent comme du bruit UNIFORME.
   -> PAS de symetries cachees (cascades de retenues).

2. Pour k=3 (p=101, SEUL cas informatif pour Larsen) :
   -> Skewness = 0.198 (NON NULLE) -> Asymetrie DETECTEE.
   -> Compatible avec SL_n (groupe maximal).

3. Pour k=4 (p=431, borderline) :
   -> Skewness = 0.483 (NON NULLE) -> Asymetrie DETECTEE.
   -> Compatible avec SL_n aussi.

4. Pour k >= 5 : |Simplex| >> sqrt(p), le test de Larsen n'est PAS
   informatif (birthday paradox -> distribution trivalement uniforme).

5. Equidistribution confirmee (Gini ~ 0) pour k >= 5.
   C'est COHERENT avec l'equidistribution du Bloc 3, mais ne constitue
   PAS une preuve de monodromie maximale.

DIAGNOSTIC :

Le "Chainon Manquant" du R168 reste PARTIELLEMENT OUVERT :

  a) Les corrSum mod p sont equidistribues (pas de structure cachee) : BON SIGNE.
  b) Pour les petits k informatifs (3,4), l'asymetrie est detectee : BON SIGNE.
  c) MAIS : aucune preuve que l'asymetrie persiste pour les grands k (21-41).
  d) Le test de Larsen tel qu'applique ici n'a PAS la puissance discriminante
     necessaire quand |Simplex| >> sqrt(p), ce qui est EXACTEMENT le regime
     du Bloc 3 (k=22-41).

VERDICT FINAL :

  ** ZONE GRISE — INSUFFISANT **

  - Le R167 n'est PAS detruit (pas d'exces de collisions).
  - Le R167 n'est PAS valide non plus (test non informatif pour grands k).
  - L'equidistribution est un indice positif mais ne remplace pas une preuve.
  - Le chainon manquant MPF -> G_geom = SL_n reste OUVERT.

  Classification : NI MORT NI VIVANT. Le R167/R168 est en SUSPENSION
  dans l'attente d'un test dans le bon regime (|Simplex| ~ sqrt(p)).
""")

    # Sauvegarder le verdict corrige
    corrected_verdict = {
        "status": "GREY",
        "classification": "SUSPENSION — chainon manquant ouvert",
        "equidistribution_confirmed": True,
        "excess_collisions": False,
        "skewness_informative_cases": {
            "k=3 (p=101)": {"skewness": 0.198, "verdict": "SL_n compatible"},
            "k=4 (p=431)": {"skewness": 0.483, "verdict": "SL_n compatible"},
        },
        "skewness_non_informative": "k>=5 (|S| >> sqrt(p), birthday regime)",
        "key_limitation": "Test de Larsen non informatif dans le regime Bloc 3 (k=22-41)",
        "R167_destroyed": False,
        "R167_validated": False,
    }

    with open("R168_results_corrected.json", "w") as f:
        json.dump(corrected_verdict, f, indent=2)
    print("Verdict corrige sauvegarde dans R168_results_corrected.json")


if __name__ == "__main__":
    analyze()
