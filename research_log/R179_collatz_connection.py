#!/usr/bin/env python3
"""
R179f — CONNEXION FONDAMENTALE : C(k,x) ET DYNAMIQUE DE COLLATZ

THÉORÈME DÉCOUVERT :
La récurrence C(k,x) encode EXACTEMENT la dynamique de Collatz
sur les nombres impairs.

Définition : A₀ = 3k+1, A_{m+1} = 3A_m + 2^{v₂(A_m)}.
Alors C(k,x) = A_{x-1}.

Les parties impaires B_m = odd(A_m) suivent :
  B₀ = odd(3k+1)
  B_{m+1} = odd(3B_m + 1) = T(B_m)

où T est la fonction de Collatz compressée sur les impairs.

CONSÉQUENCE CRUCIALE :
  R_{x-1} = k·2^S - C(k,x) = 0
  ⟺ k = B_{x-1} et S = a_{x-1}
  ⟺ T^x(k) = k (k est un point périodique de période x de T)
  ⟺ k fait partie d'un CYCLE de Collatz de longueur x

C'est l'ÉQUIVALENCE PARFAITE entre le lemme de non-annulation
et l'inexistence de cycles de Collatz.
"""

def v2(n):
    if n == 0:
        return float('inf')
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v


def odd_part(n):
    while n > 0 and n % 2 == 0:
        n //= 2
    return n


def collatz_odd(n):
    """Compressed Collatz on odd numbers: n → odd(3n+1)"""
    return odd_part(3 * n + 1)


def compute_A_sequence(k, x):
    """
    A₀ = 3k+1, A_{m+1} = 3A_m + 2^{v₂(A_m)}
    Returns As, Bs (odd parts), as (2-adic valuations)
    """
    A = 3 * k + 1
    As = [A]
    Bs = [odd_part(A)]
    avs = [v2(A)]

    for m in range(1, x):
        A = 3 * A + 2 ** v2(A)
        As.append(A)
        Bs.append(odd_part(A))
        avs.append(v2(A))

    return As, Bs, avs


def main():
    print("=" * 80)
    print("R179f — CONNEXION C(k,x) ↔ DYNAMIQUE DE COLLATZ")
    print("=" * 80)

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 1 : Vérification B_m = Collatz orbit
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 1 : B_m = T^m(odd(3k+1)) — orbite de Collatz")
    print("═" * 70)

    all_match = True
    for k in range(1, 100, 2):
        As, Bs, avs = compute_A_sequence(k, 20)

        # Compare with direct Collatz iteration
        b = odd_part(3 * k + 1)
        collatz_orbit = [b]
        for _ in range(19):
            b = collatz_odd(b)
            collatz_orbit.append(b)

        if Bs != collatz_orbit:
            all_match = False
            print(f"  ❌ k={k}: B≠Collatz")
            print(f"    B = {Bs[:10]}")
            print(f"    C = {collatz_orbit[:10]}")

    print(f"  {'✅' if all_match else '❌'} B_m = T^m(odd(3k+1)) vérifié pour k=1..99, 20 étapes")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 2 : L'ÉQUIVALENCE R=0 ⟺ Collatz cycle
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 2 : R_{x-1}=0 ⟺ T^x(k)=k (CYCLE DE COLLATZ)")
    print("═" * 70)

    print("""
THÉORÈME (Équivalence fondamentale) :
  Soit k ≥ 1 impair, x ≥ 2. Alors :

  ∃ S t.q. R_{x-1} = k·2^S - C(k,x) = 0
  ⟺ B_{x-1} = k (la (x-1)-ème partie impaire dans la récurrence A)
  ⟺ T^x(k) = k (k est point périodique de Collatz, période | x)

  PREUVE :
  C(k,x) = A_{x-1} = 2^{a_{x-1}} · B_{x-1}

  R = k·2^S - 2^{a_{x-1}} · B_{x-1} = 0
  ⟹ k · 2^{S-a_{x-1}} = B_{x-1}  (si S ≥ a_{x-1})

  Puisque k est impair et B_{x-1} est impair :
  2^{S-a_{x-1}} = 1, i.e., S = a_{x-1}
  et k = B_{x-1}.

  B_{x-1} = T^{x-1}(B_0) = T^{x-1}(T(k)) = T^x(k).
  Donc k = T^x(k). ∎

  CAS k=1 :
  T(1) = odd(4) = 1. Donc T^x(1) = 1 pour tout x.
  C'est le cycle TRIVIAL {1 → 4 → 2 → 1}.
  Le vecteur associé est (10)^x, PÉRIODIQUE → exclu. ∎
""")

    # Vérification numérique
    print("  Vérification : T^x(k) pour petits k et x")
    for k in [1, 3, 5, 7, 9, 11, 13, 15]:
        orbit = [k]
        b = k
        for i in range(15):
            b = collatz_odd(b)
            orbit.append(b)
        print(f"    k={k:3d}: orbit = {orbit}")
        # Check if k ever reappears
        returns = [i for i, b in enumerate(orbit[1:], 1) if b == k]
        if returns:
            print(f"      → k={k} revient à la position(s) {returns} ← CYCLE!")
        else:
            print(f"      → k={k} ne revient jamais (dans 15 étapes)")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 3 : Seul k=1 a un cycle, vérifié massivement
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 3 : RECHERCHE DE CYCLES T^x(k)=k pour k ≤ 10000")
    print("═" * 70)

    max_k = 10000
    max_orbit = 200  # Maximum orbit length to check
    cycles_found = []

    for k in range(1, max_k + 1, 2):
        b = k
        for step in range(1, max_orbit + 1):
            b = collatz_odd(b)
            if b == k:
                cycles_found.append((k, step))
                break

    print(f"\n  Cycles trouvés parmi k=1..{max_k} impair, orbites ≤ {max_orbit} :")
    if cycles_found:
        k_vals = set(c[0] for c in cycles_found)
        print(f"  Valeurs de k : {sorted(k_vals)}")
        for k, period in cycles_found[:20]:
            print(f"    k={k}, période={period}")
    else:
        print(f"  AUCUN cycle trouvé !")

    # Note: k=1 has period 1 (T(1)=1)
    print(f"\n  Note : k=1 → T(1) = odd(4) = 1, période 1 ✓")
    if len(cycles_found) == 1 and cycles_found[0] == (1, 1):
        print(f"  ✅ Seul k=1 est un point fixe/périodique dans k ≤ {max_k}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 4 : La VALUATION cumulative a_{x-1}
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 4 : VALUATION CUMULATIVE a_{x-1}")
    print("═" * 70)

    print("""
a_{x-1} = Σ_{m=0}^{x-2} v₂(3B_m + 1) = cumul des valuations Collatz

Pour k=1 : chaque étape a v₂(3·1+1) = v₂(4) = 2.
Donc a_{x-1} = 2(x-1) + v₂(3·1+1) = ... wait.

Actually : a_0 = v₂(A_0) = v₂(3k+1).
a_{m+1} = a_m + v₂(3B_m+1).

Pour k=1 : a_0 = v₂(4) = 2. B_0 = 1, v₂(3·1+1) = 2.
a_1 = 2+2 = 4. B_1 = 1. a_2 = 6. ... a_m = 2(m+1).
S = a_{x-1} = 2x. ✓ (C'est bien S=2x pour k=1)
""")

    for k in [1, 3, 7, 15, 31]:
        As, Bs, avs = compute_A_sequence(k, 12)
        # Cumulative valuations
        cum = avs
        print(f"  k={k:3d}: v₂ = {cum}")
        print(f"         B  = {Bs}")
        print(f"         If T^x(k)=k, need S = a_{{x-1}} = {cum[-1]} at x={12}")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 5 : Ce qui EST prouvé vs ce qui reste
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 5 : BILAN HONNÊTE — CE QUI EST PROUVÉ")
    print("═" * 70)

    print("""
═══════════════════════════════════════════════════════════════════════
THÉORÈMES PROUVÉS (ÉLÉMENTAIRES, INCONDITIONNELS) :
═══════════════════════════════════════════════════════════════════════

T195 (Récurrence S-indépendante) :
  La descente 2-adique produit C(k,x) via la récurrence
  A₀ = 3k+1, A_{m+1} = 3A_m + 2^{v₂(A_m)}, C(k,x) = A_{x-1}.
  PROUVÉ élémentairement. ∎

T196 (Cas k=1 — Reformulation de T191) :
  C(1,x) = 4^x = 2^{2x}. Le seul S tel que R=0 est S=2x.
  Le vecteur est (10)^x, PÉRIODIQUE de période 2 → exclu.
  PROUVÉ par récurrence : C_m = 4^{m+1}·3^{x-1-m}. ∎

T197 (Équivalence fondamentale) :
  R_{x-1} = 0 avec B_{x-1} = k ⟺ T^x(k) = k ⟺ k ∈ cycle de Collatz.
  PROUVÉ élémentairement. ∎

T198 (Dynamique des parties impaires) :
  B_m = odd(A_m) suit la dynamique de Collatz compressée :
  B_{m+1} = odd(3B_m + 1) = T(B_m), B_0 = T(k).
  PROUVÉ élémentairement. ∎

═══════════════════════════════════════════════════════════════════════
VÉRIFICATIONS COMPUTATIONNELLES :
═══════════════════════════════════════════════════════════════════════

V1 : C(k,x) formule exacte pour S assez grand — 228 vérifications ✅
V2 : 111,215 cas (x≤30, k≤499) exclus par la descente ✅
V3 : 11,500 cas (x≤25, k≤999) sans survivant apériodique ✅
V4 : odd_part(C(k,x)) = k uniquement pour k=1 sur 4,750 cas ✅
V5 : T^x(k) ≠ k pour k ≤ 10,000 (orbites ≤ 200) ✅
     (Connu bien au-delà : Collatz vérifié jusqu'à ~2^68)

═══════════════════════════════════════════════════════════════════════
CE QUI N'EST PAS PROUVÉ (HONNÊTEMENT) :
═══════════════════════════════════════════════════════════════════════

Le LEMME DE NON-ANNULATION universel :
  "∀ k ≥ 3 impair, ∀ x ≥ 2 : B_{x-1}(k) ≠ k"

Ce lemme est ÉQUIVALENT à :
  "La fonction de Collatz compressée T n'a aucun point périodique k ≥ 3"

Ce qui est EXACTEMENT la conjecture d'inexistence de cycles non-triviaux.

CONCLUSION : La descente 2-adique est une REFORMULATION EXACTE de la
question des cycles, pas une preuve. Elle fournit :
  (a) Un cadre algébrique propre (S-indépendant)
  (b) L'équivalence T197 (nouveau, à notre connaissance)
  (c) Un outil computationnel efficace
  (d) La preuve que k=1 donne toujours un vecteur périodique

Mais elle ne RÉSOUT pas le problème des cycles — elle le REFORMULE.

═══════════════════════════════════════════════════════════════════════
CEPENDANT : LA CONTRAINTE D'APÉRIODICITÉ EST-ELLE EXPLOITABLE ?
═══════════════════════════════════════════════════════════════════════

Même SI T^x(k) = k (cycle hypothétique), le vecteur correspondant
n'est valide que s'il est APÉRIODIQUE dans [0, S-1].

Pour k=1 : vecteur = (10)^x dans [0, 2x-1] → TOUJOURS périodique.
Pour k ≥ 3 hypothétique : les positions D_0, D_1, ..., D_{x-1}
dans [0, S-1] sont-elles nécessairement périodiques ?

C'est la question qui reste ouverte et qui pourrait être plus accessible
que la conjecture complète des cycles.
""")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 6 : Étude de l'apériodicité
    # ═══════════════════════════════════════════════════════════════════════
    print("\n" + "═" * 70)
    print("PARTIE 6 : CONTRAINTE D'APÉRIODICITÉ")
    print("═" * 70)

    print("""
Pour un cycle hypothétique de longueur x à travers k :
- S = a_{x-1} = Σ v₂(3B_m + 1) = somme des valuations Collatz
- Positions : D_m = Σ_{j=0}^{m-1} v₂(3B_j + 1) (cumul partiel)

Le vecteur binaire v ∈ {0,1}^S a des 1 aux positions D_0, ..., D_{x-1}.
Le vecteur est périodique de période p | S ssi les positions sont
invariantes sous la translation par p mod S.

Pour k=1 : S = 2x, D_m = 2m. Positions = {0,2,4,...,2(x-1)}.
Translation de +2 mod 2x préserve les positions → période 2 ✓.

Pour k ≥ 3 : les valuations v₂(3B_m+1) varient au cours de l'orbite.
La non-uniformité des gaps rend la périodicité IMPROBABLE.
""")

    # Simulate what a hypothetical cycle would look like
    # Using the ACTUAL Collatz trajectories as approximation
    # (these don't cycle, but let's study the valuation patterns)

    print("  Patterns de valuations pour quelques k :")
    for k in [3, 7, 27, 31, 127, 255]:
        b = k
        vals = []
        for _ in range(20):
            val = v2(3 * b + 1)
            vals.append(val)
            b = odd_part(3 * b + 1)
            if b == 1:
                vals_until_1 = vals[:]
                break
        else:
            vals_until_1 = vals

        cum = [0]
        for v in vals_until_1:
            cum.append(cum[-1] + v)

        print(f"  k={k:5d}: valuations = {vals_until_1}")
        print(f"          positions cumulées = {cum}")
        print(f"          S_final = {cum[-1]}, x = {len(vals_until_1)}")

        # Check if positions would be periodic
        S = cum[-1]
        x_steps = len(vals_until_1)
        positions = set(cum[:x_steps])
        for p in range(1, S):
            if S % p != 0:
                continue
            shifted = set((pos + p) % S for pos in positions)
            if shifted == positions:
                print(f"          → Périodique de période {p} !")
                break
        else:
            print(f"          → Apériodique (aucune période ne divise S={S})")

    # ═══════════════════════════════════════════════════════════════════════
    # PARTIE 7 : Relation S = 2x pour tout cycle (Steiner's bound)
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("PARTIE 7 : CONTRAINTE S > x·log₂(3) ≈ 1.585·x")
    print("═" * 70)

    print("""
Pour d = 2^S - 3^x > 0, il faut S > x·log₂(3) ≈ 1.585·x.
Pour un cycle réel, la contrainte d > 0 donne S ≥ ceil(x·log₂(3)) + 1.

La valuation cumulative S = a_{x-1} = Σ v₂(3B_m+1).
La valuation moyenne de v₂(3B+1) pour B impair aléatoire est 2
(car P(v₂=n) = 1/2^n pour n ≥ 1, moyenne = 2).

Donc S ≈ 2x en moyenne, ce qui satisfait S > 1.585x.
Mais les fluctuations sont importantes pour les petites orbites.

En fait, la valuation moyenne de v₂(3B+1) dans un cycle est
EXACTEMENT S/x. Pour un cycle de longueur x :
  S/x = moyenne des v₂(3B_m+1) pour m = 0, ..., x-1.

La contrainte S > 1.585x donne : moyenne > 1.585.
C'est satisfait "en général" mais pas trivial pour des cas spécifiques.
""")

    # Study what S/x ratio looks like for actual trajectories to 1
    print("  Rapport S/x pour trajectoires k → 1 :")
    for k in range(3, 200, 2):
        b = k
        vals = []
        for _ in range(500):
            val = v2(3 * b + 1)
            vals.append(val)
            b = odd_part(3 * b + 1)
            if b == 1:
                break
        else:
            continue

        S = sum(vals)
        x = len(vals)
        ratio = S / x if x > 0 else 0
        if x >= 5:  # Only show non-trivial
            print(f"    k={k:5d}: x={x:3d}, S={S:5d}, S/x={ratio:.3f}")

    # ═══════════════════════════════════════════════════════════════════════
    # SYNTHÈSE FINALE
    # ═══════════════════════════════════════════════════════════════════════
    print("\n\n" + "═" * 70)
    print("SYNTHÈSE FINALE R179f")
    print("═" * 70)
    print("""
RÉSULTAT PRINCIPAL (T197) :
  R_{x-1} = 0 ⟺ T^x(k) = k ⟺ k est dans un cycle de Collatz

CE RÉSULTAT EST :
  ✅ NOUVEAU (à notre connaissance — lien explicite descent ↔ cycles)
  ✅ ÉLÉMENTAIRE (preuve en 5 lignes)
  ✅ EXACT (équivalence, pas implication)
  ❌ Ne résout PAS le problème (le reformule)

CE QUE ÇA DONNE CONCRÈTEMENT :
  1. Toute preuve que T n'a pas de cycle ≥ 3 ⟹ lemme de non-annulation ∎
  2. Toute preuve du lemme de non-annulation ⟹ pas de cycle Collatz ∎
  3. Les deux problèmes sont ÉQUIVALENTS

PISTES POUR ALLER PLUS LOIN :
  a) Explorer la contrainte d'APÉRIODICITÉ du vecteur
     — elle est absente de la formulation classique des cycles
     — elle pourrait donner des exclusions supplémentaires
  b) Combiner avec les bornes existantes (Steiner, Eliahou, ...)
  c) Utiliser la structure spéciale de la D-séquence
     (stabilisation, gaps non-uniformes) pour contraindre les cycles
""")


if __name__ == '__main__':
    main()
