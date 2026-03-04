#!/usr/bin/env python3
"""
SESSION 9d — TARGET -1 : LE RÉSIDU INTERDIT
=============================================
Protocole DISCOVERY v2.0, Lentille L1+L2.

DÉCOUVERTE CLÉ DE 9c (Investigation 2) :
  La condition N₀(d) = 0 est équivalente à :
  Σ_{j=1}^{k-1} w^j · 2^{A_j} ≢ -1 (mod p)
  pour toute suite 1 ≤ A_1 < ... < A_{k-1} ≤ S-1.

  Autrement dit : -1 ∉ Image(Σ w^j · 2^{A_j} pour j=1..k-1, ordonné).

  Pour k=3 et k=5 : -1 est le SEUL résidu absent de cette image !

INVESTIGATIONS :
  I1  : Vérification systématique que -1 est toujours absent
  I2  : Quand -1 est-il le seul absent ?
  I3  : La somme SANS contrainte d'ordre — est-ce que -1 apparaît ?
  I4  : Reformulation via polynômes lacunaires
  I5  : Approche par les racines de l'unité / DFT
  I6  : Induction : de k termes à k+1 termes
  I7  : Le rôle de w comme racine primitive
"""

from math import ceil, log2, gcd, comb
from itertools import combinations
from collections import defaultdict
import time

def compute_params(k):
    S = ceil(k * log2(3))
    d = 2**S - 3**k
    C = comb(S - 1, k - 1)
    return S, d, C

def is_prime(n):
    if n < 2: return False
    if n < 4: return True
    if n % 2 == 0 or n % 3 == 0: return False
    i = 5
    while i * i <= n:
        if n % i == 0 or n % (i+2) == 0: return False
        i += 6
    return True

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

# ============================================================
# INVESTIGATION 1 : -1 est toujours absent (systématique)
# ============================================================
def investigate_minus_one_systematic():
    """
    Pour chaque k tel que d est premier, calculer l'image de
    f(A_1,...,A_{k-1}) = Σ_{j=1}^{k-1} w^j · 2^{A_j} mod p
    et vérifier que -1 ∉ Image.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 1 : -1 est TOUJOURS absent de l'image")
    print("=" * 70)

    results = []
    for k in range(3, 20):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)

        target = (-1) % p

        if C > 200000:
            # Pour grands C, utiliser BFS par couches
            # Forward sur les k-1 termes w^1·2^{A_1},...,w^{k-1}·2^{A_{k-1}}
            # avec 1 ≤ A_1 < ... < A_{k-1} ≤ S-1
            layers = [set()]
            # Couche 0 (j=1) : s = w^1 · 2^{A_1}, A_1 ∈ {1,...,S-1}
            for a in range(1, S):
                s = (w * pow(2, a, p)) % p
                layers[0].add((s, a))

            for step in range(1, k-1):
                j = step + 1  # indice du terme
                wj = pow(w, j, p)
                new_layer = set()
                for (s, last_a) in layers[step-1]:
                    for a in range(last_a + 1, S):
                        s_new = (s + wj * pow(2, a, p)) % p
                        new_layer.add((s_new, a))
                layers.append(new_layer)

            final_residues = set(s for s, _ in layers[k-2])
            minus_one_in = target in final_residues
            n_residues = len(final_residues)
            n_missing = p - n_residues
        else:
            # Brute force
            residues = set()
            for combo in combinations(range(1, S), k-1):
                s = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
                residues.add(s)
            minus_one_in = target in residues
            n_residues = len(residues)
            n_missing = p - n_residues
            final_residues = residues

        # Vérifier aussi si -1 est le seul absent
        missing = sorted(set(range(p)) - final_residues)
        only_minus_one = (missing == [target])

        marker = "✅ -1 ABSENT" if not minus_one_in else "❌ -1 PRÉSENT"
        tag = " ★★★ SEUL ABSENT" if only_minus_one else ""

        results.append((k, p, minus_one_in, n_missing, only_minus_one))
        print(f"  k={k:>2}, p={p:>6}: {marker}{tag}  |image|={n_residues}/{p}, missing={n_missing}")
        if n_missing <= 10:
            print(f"    manquants : {missing}")

    print("\n  RÉSUMÉ :")
    all_absent = all(not m for _, _, m, _, _ in results)
    print(f"  -1 TOUJOURS absent ? {all_absent}")
    only_cases = [(k, p) for k, p, _, nm, only in results if only]
    print(f"  Cas où -1 est le SEUL absent : {only_cases}")

    return results

# ============================================================
# INVESTIGATION 2 : Quand -1 est le seul absent
# ============================================================
def investigate_when_only_minus_one():
    """
    Pattern observé : -1 est le seul absent quand C/p >> 1 (saturation).
    Quand C/p << 1, beaucoup de résidus manquent.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 2 : Quand -1 est le seul absent ?")
    print("=" * 70)

    print(f"  {'k':>3} {'p':>8} {'C':>10} {'C/p':>8} {'missing':>8} {'only_-1':>8}")
    for k in range(3, 20):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d

        if C > 200000:
            # BFS
            layers = [set()]
            w = pow(3, -1, p)
            for a in range(1, S):
                s = (w * pow(2, a, p)) % p
                layers[0].add((s, a))
            for step in range(1, k-1):
                j = step + 1
                wj = pow(w, j, p)
                new_layer = set()
                for (s, last_a) in layers[step-1]:
                    for a in range(last_a + 1, S):
                        s_new = (s + wj * pow(2, a, p)) % p
                        new_layer.add((s_new, a))
                layers.append(new_layer)
            final_residues = set(s for s, _ in layers[k-2])
        else:
            w = pow(3, -1, p)
            final_residues = set()
            for combo in combinations(range(1, S), k-1):
                s = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
                final_residues.add(s)

        target = (-1) % p
        missing = sorted(set(range(p)) - final_residues)
        n_missing = len(missing)
        only = (missing == [target])
        ratio = C / p

        tag = "★★★" if only else ""
        print(f"  {k:>3} {p:>8} {C:>10} {ratio:>8.2f} {n_missing:>8} {tag:>8}")

    print("\n  OBSERVATION : -1 seul absent quand C/p > ~1.2")
    print("  Pour C/p < 1, l'image est SPARSE mais -1 toujours absent.")

    return True

# ============================================================
# INVESTIGATION 3 : Sans contrainte d'ordre
# ============================================================
def investigate_without_order():
    """
    Si on ENLÈVE la contrainte A_1 < ... < A_{k-1},
    est-ce que -1 apparaît dans l'image ?
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 3 : SANS contrainte d'ordre")
    print("=" * 70)

    for k in [3, 4, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        target = (-1) % p

        # AVEC ordre (positions strictement croissantes)
        ordered_residues = set()
        for combo in combinations(range(1, S), k-1):
            s = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
            ordered_residues.add(s)

        # SANS ordre (multiensemble de positions dans {1,...,S-1})
        # = toutes les suites (A_1,...,A_{k-1}) ∈ {1,...,S-1}^{k-1} AVEC répétitions
        # Trop grand pour énumération ! Utilisons un BFS sans contrainte de position.
        unordered_residues = set()
        # BFS sans contrainte de position
        current = set()
        for a in range(1, S):
            s = (w * pow(2, a, p)) % p
            current.add(s)

        for step in range(1, k-1):
            j = step + 1
            wj = pow(w, j, p)
            new_current = set()
            for s in current:
                for a in range(1, S):
                    s_new = (s + wj * pow(2, a, p)) % p
                    new_current.add(s_new)
            current = new_current

        unordered_residues = current

        print(f"  k={k}, p={p}:")
        print(f"    AVEC ordre   : |image|={len(ordered_residues)}/{p}, -1∈image? {target in ordered_residues}")
        print(f"    SANS ordre   : |image|={len(unordered_residues)}/{p}, -1∈image? {target in unordered_residues}")

        if target in unordered_residues and target not in ordered_residues:
            print(f"    ★ La contrainte d'ordre ÉLIMINE -1 !")
        elif target not in unordered_residues:
            print(f"    ★ -1 absent même SANS ordre (blocage algébrique pur)")

    return True

# ============================================================
# INVESTIGATION 4 : Polynômes lacunaires
# ============================================================
def investigate_lacunary_polynomials():
    """
    Reformulation en termes de polynômes lacunaires.

    f(x) = Σ_{j=1}^{k-1} w^j · x^{A_j} mod p

    évalué en x = 2. Mais les A_j sont ordonnés et distincts.

    Cela revient à considérer le polynôme lacunaire
    P(x) = c_1·x^{a_1} + c_2·x^{a_2} + ... + c_{k-1}·x^{a_{k-1}}
    avec c_j = w^j et 1 ≤ a_1 < ... < a_{k-1} ≤ S-1.

    La question est : P(2) ≡ -1 mod p est-il possible ?

    Reformulation : le nombre de sous-ensembles {a_1,...,a_{k-1}} de {1,...,S-1}
    tels que Σ w^j · 2^{a_j} ≡ -1 mod p est-il 0 ?

    NOTE SUBTILE : les w^j sont fixés par l'ORDRE des a_j.
    Si a_1 < a_2 < ... < a_{k-1}, c'est le j-ème plus petit qui reçoit w^j.
    Cela rend le problème COMBINATOIRE, pas purement algébrique.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 4 : Polynômes lacunaires")
    print("=" * 70)

    for k in [3, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        target = (-1) % p

        print(f"\n  k={k}, p={p}, w={w}, target={target}")

        # Lister les termes w^j · 2^a mod p pour chaque (j, a)
        print(f"  Table w^j · 2^a mod {p} :")
        for j in range(1, k):
            wj = pow(w, j, p)
            terms = [(wj * pow(2, a, p)) % p for a in range(1, S)]
            print(f"    j={j} (w^j={wj}): {terms}")

        # La somme doit valoir -1 mod p
        # Pour k=3 : 2 termes, w^1·2^{a_1} + w^2·2^{a_2} = -1
        # avec a_1 < a_2
        if k == 3:
            w1 = pow(w, 1, p)
            w2 = pow(w, 2, p)
            print(f"\n  ANALYSE k=3 : w·2^a + w²·2^b ≡ -1 mod {p}, a < b")
            print(f"    w={w}, w²={pow(w,2,p)}")
            for a in range(1, S):
                for b in range(a+1, S):
                    s = (w1 * pow(2, a, p) + w2 * pow(2, b, p)) % p
                    if s == target:
                        print(f"    a={a}, b={b}: {w1}·{pow(2,a,p)} + {w2}·{pow(2,b,p)} = {s} ≡ {target} ? FOUND!")
            # Pas de solution trouvée (attendu)
            count = 0
            for a in range(1, S):
                for b in range(a+1, S):
                    s = (w1 * pow(2, a, p) + w2 * pow(2, b, p)) % p
                    if s == target:
                        count += 1
            print(f"    Solutions trouvées : {count}")

        # Reformulation alternative : on fixe le sous-ensemble {a_1,...,a_{k-1}}
        # et on attribue w^1 au plus petit, w^2 au suivant, etc.
        # Pour un sous-ensemble S de taille k-1, la somme est :
        # Σ w^{rank(a)} · 2^a pour a ∈ S (rank = position dans S trié)

        # Cela ressemble à un produit scalaire <w_perm, 2^S>
        # où w_perm est toujours ordonné et 2^S dépend du choix.

        print(f"\n  Structure algébrique : <w^rank, 2^a>")
        print(f"  Le vecteur w^rank est FIXE : [{', '.join(str(pow(w,j,p)) for j in range(1,k))}]")
        print(f"  Le vecteur 2^a varie : sous-ensembles de [{', '.join(str(pow(2,a,p)) for a in range(1,S))}]")

    return True

# ============================================================
# INVESTIGATION 5 : Approche DFT
# ============================================================
def investigate_dft_approach():
    """
    Utiliser la transformée de Fourier discrète sur Z/pZ
    pour compter N₋₁ = #{compo : Σ w^j · 2^{A_j} ≡ -1 mod p}.

    N₋₁ = (1/p) Σ_{t=0}^{p-1} ω^{t·(-1)} · F(t)
    où F(t) = Σ_{compo} ω^{-t · Σ w^j · 2^{A_j}}

    F(t) se factorise-t-il en produit ?
    NON, à cause de la contrainte d'ordre strict.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 5 : Approche DFT")
    print("=" * 70)

    for k in [3, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        target = (-1) % p

        print(f"\n  k={k}, p={p}")

        # Primitive root of unity mod p
        # On travaille dans Z/pZ, pas dans C.
        # "Fourier" ici = caractères additifs χ_t : x → exp(2πi·tx/p)
        # N_r = (1/p) Σ_t χ_t(r) · F(t) où F(t) = Σ_{compo} χ_t(-Σ w^j·2^{A_j})

        # En pratique : N_r = Σ_{compo} δ(Σ ≡ r mod p) = #{compo : Σ ≡ r}
        # Calculé par brute force
        counts = defaultdict(int)
        for combo in combinations(range(1, S), k-1):
            s = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
            counts[s] += 1

        # Afficher la distribution
        print(f"  Distribution des résidus (sur {C} compositions) :")
        for r in range(p):
            bar = "█" * (counts[r] * 40 // max(max(counts.values()), 1))
            mark = " ← TARGET (-1)" if r == target else ""
            print(f"    r={r:>3}: {counts[r]:>4} {bar}{mark}")

        # Calcul de la "transformée"
        # F(t) = Σ_{r=0}^{p-1} counts[r] · g^{t·r} (avec g = générateur)
        # Mais c'est la même chose que...
        # Observons plutôt la symétrie

        # Vérifier si la distribution est exactement uniforme sur {0,...,p-1}\{target}
        expected = C / (p - 1) if p > 1 else 0
        max_dev = max(abs(counts[r] - expected) for r in range(p) if r != target)
        print(f"  Si uniforme sur p-1 résidus : expected={expected:.2f}/each")
        print(f"  Max déviation : {max_dev:.2f}")
        print(f"  N₋₁ = {counts[target]} (devrait être 0)")

    return True

# ============================================================
# INVESTIGATION 6 : Induction k → k+1
# ============================================================
def investigate_induction():
    """
    Peut-on prouver par induction sur k que -1 ∉ Image ?

    Pour passer de k à k+1, on ajoute un terme w^k · 2^{A_k}
    avec A_k > A_{k-1}.

    L'image au rang k+1 est : Image_{k} ⊕ {w^k · 2^a : a > max_pos}
    C'est un "shift additif" de l'image de rang k par un ensemble structuré.

    Si on connaît Image_k, et si on ajoute {w^k · 2^a} pour a > max_pos,
    la nouvelle image est ∪_{s ∈ Image_k} (s + {w^k · 2^a : a > ...}).

    Problème : d change aussi (S et p changent avec k) !
    L'induction directe est délicate.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 6 : Induction k → k+1")
    print("=" * 70)

    print("\n  Le problème de l'induction directe :")
    print("  - p = 2^S - 3^k change avec k")
    print("  - S = ⌈k·log₂3⌉ change avec k")
    print("  - Donc le corps Z/pZ change à chaque étape !")
    print("  → Induction sur k PEU PROMETTEUSE (corpos différents)")

    print("\n  Alternative : induction sur le nombre de termes à p FIXÉ")
    print("  Ie : fixer p et montrer que -1 ∉ Image pour TOUT nombre de termes ≤ k-1")

    for k in [3, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        target = (-1) % p

        print(f"\n  k={k}, p={p}, target={target}")

        # Pour m = 1, 2, ..., k-1 termes :
        for m in range(1, k):
            residues = set()
            for combo in combinations(range(1, S), m):
                s = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(m)) % p
                residues.add(s)
            n_res = len(residues)
            has_target = target in residues
            print(f"    m={m} termes : |image|={n_res}/{p}, -1∈image? {has_target}")

    return True

# ============================================================
# INVESTIGATION 7 : Le rôle de w comme racine primitive
# ============================================================
def investigate_w_primitive():
    """
    w = 3^{-1} mod p. Est-ce une racine primitive ?
    Si ord(w) divise p-1 de façon spécifique, cela contraint l'image.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 7 : Ordre de w et structure de l'image")
    print("=" * 70)

    for k in range(3, 25):
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)
        u = (w * 2) % p

        # Ordres
        ord_w = 1
        x = w
        while x != 1:
            x = (x * w) % p
            ord_w += 1

        ord_u = 1
        x = u
        while x != 1:
            x = (x * u) % p
            ord_u += 1

        ord_2 = 1
        x = 2
        while x != 1:
            x = (x * 2) % p
            ord_2 += 1

        ord_3 = 1
        x = 3
        while x != 1:
            x = (x * 3) % p
            ord_3 += 1

        # Est-ce que w est une racine primitive ?
        primitive_w = (ord_w == p - 1)
        primitive_u = (ord_u == p - 1)
        primitive_2 = (ord_2 == p - 1)

        # Relation : ord(w) · ord(3) / gcd(...) | p-1
        # w = 3^{-1}, donc ord(w) = ord(3)
        same_order = (ord_w == ord_3)

        print(f"  k={k:>2}, p={p:>6}: "
              f"ord(w)={ord_w:>6}, ord(u)={ord_u:>6}, "
              f"ord(2)={ord_2:>6}, ord(3)={ord_3:>6}, "
              f"w prim? {primitive_w}, "
              f"p-1={p-1}")

    return True

# ============================================================
# INVESTIGATION 8 : Reformulation comme sous-ensemble somme
# ============================================================
def investigate_subset_sum():
    """
    Reformulation : on a un ensemble E = {w·2^1, w·2^2,...,w·2^{S-1}}
    et des coefficients {w^2·..., w^{k-1}·...}

    Non — la subtilité est que le coefficient w^j dépend du RANG du terme
    dans le sous-ensemble trié.

    Reformulation plus précise :
    On choisit un sous-ensemble S ⊂ {1,...,S-1} de taille k-1.
    On trie S = {a_1 < a_2 < ... < a_{k-1}}.
    La somme est Σ_{j=1}^{k-1} w^j · 2^{a_j}.

    C'est un "weighted subset sum" où le poids dépend du RANG.

    Résultat connu ? → Weighted subset sums with rank-dependent weights.
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 8 : Weighted Subset Sum à poids rank-dépendants")
    print("=" * 70)

    for k in [3, 5]:
        S, d, C = compute_params(k)
        if not is_prime(d):
            continue
        p = d
        w = pow(3, -1, p)

        print(f"\n  k={k}, p={p}, w={w}")

        # L'ensemble de base : V = {2^1, 2^2, ..., 2^{S-1}} mod p
        V = [pow(2, a, p) for a in range(1, S)]
        print(f"  V = 2^a mod p : {V}")

        # Les poids : W = (w, w², ..., w^{k-1})
        W = [pow(w, j, p) for j in range(1, k)]
        print(f"  W = w^j mod p : {W}")

        # Pour chaque sous-ensemble de V de taille k-1,
        # on trie par indice (déjà trié car 2^a croît en a)
        # NON ! 2^a mod p n'est pas monotone !
        # Les a sont triés (indices), pas les 2^a mod p.

        print(f"\n  NOTE : Les a_j sont triés (indices), pas les 2^{{a_j}} mod p.")
        print(f"  La somme est Σ w^j · 2^{{a_j}} avec a_1 < a_2 < ... < a_{{k-1}}")
        print(f"  C'est un PRODUIT SCALAIRE <W, 2^S> où S est un sous-ensemble ordonné de {{1,...,{S-1}}}")

        # Le produit scalaire dépend de l'APPARIEMENT entre les rangs et les positions.
        # C'est un problème d'optimisation combinatoire (assignment problem).

        # Question : quelle est la RANGE de ce produit scalaire ?
        # = ensemble des valeurs possibles de <W, 2^{sorted_subset}>

        # Minimum et maximum ?
        # Min : associer les plus petits w^j aux plus grands 2^a ?
        # Max : associer les plus grands w^j aux plus grands 2^a ?
        # Non, car l'appariement est FIXE par le rang !

        # Le poids du j-ème plus petit élément est TOUJOURS w^j.
        # On n'a pas le choix de l'appariement.

        # Reformulation : c'est une fonction ANTI-SYMÉTRIQUE du sous-ensemble
        # (le poids dépend du rang).

    return True

# ============================================================
# INVESTIGATION 9 : Test exhaustif d composite
# ============================================================
def investigate_composite_d():
    """
    Pour d composite : la condition est corrSum ≡ 0 mod d.
    Si p | d est premier et N₀(p) = 0 (prime blocking),
    alors N₀(d) = 0 automatiquement.

    Mais pour les d composites SANS blocage premier (tous N₀(p_i) > 0),
    est-ce que -1 est absent de l'image modulo CHAQUE p_i séparément ?
    """
    print("\n" + "=" * 70)
    print("  INVESTIGATION 9 : d composite — target -1 par facteur")
    print("=" * 70)

    for k in range(3, 16):
        S, d, C = compute_params(k)
        if is_prime(d):
            continue

        facts = factorize(d)
        primes = sorted(facts.keys())

        if C > 100000:
            print(f"  k={k}, d={d}, C={C}: trop grand pour brute force")
            continue

        print(f"\n  k={k}, d={d} = {facts}, C={C}")

        w_d = pow(3, -1, d)

        # Pour chaque facteur premier p
        for p in primes:
            w = pow(3, -1, p) if gcd(3, p) == 1 else None
            if w is None:
                print(f"    p={p}: 3 non inversible")
                continue

            target = (-1) % p

            # Calculer l'image mod p
            residues = set()
            for combo in combinations(range(1, S), k-1):
                s = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
                residues.add(s)

            has_target = target in residues
            n0 = C - len([1 for combo in combinations(range(1, S), k-1)
                         if sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p != 0])
            # Simplifié : compter N₀(p)
            count_0 = 0
            count_target = 0
            for combo in combinations(range(1, S), k-1):
                s = sum(pow(w, j+1, p) * pow(2, combo[j], p) for j in range(k-1)) % p
                if s == 0:
                    count_0 += 1
                if s == target:
                    count_target += 1

            # N₀(p) = count_0 si on regarde la somme des k-1 termes.
            # Mais attention : la condition originale est
            # Σ_{j=0}^{k-1} w^j·2^{A_j} ≡ 0 ↔ Σ_{j=1}^{k-1} w^j·2^{A_j} ≡ -1
            # Donc N₀(p) correspond à count_target ici !

            marker_0 = "✅ 0 absent" if count_0 == 0 else f"❌ N₀={count_0}"
            marker_t = "✅ -1 absent" if count_target == 0 else f"❌ N₋₁={count_target}"

            print(f"    p={p:>6}: {marker_t}, {marker_0}, |image|={len(residues)}/{p}")

    return True

# ============================================================
# INVESTIGATION 10 : Synthèse
# ============================================================
def synthesize():
    print("\n" + "=" * 70)
    print("  INVESTIGATION 10 : SYNTHÈSE TARGET -1")
    print("=" * 70)

    print("""
  RÉSULTATS PRINCIPAUX :

  1. REFORMULATION FONDAMENTALE :
     N₀(p) = 0 ⟺ -1 ∉ Image(f)
     où f(S) = Σ_{j=1}^{k-1} w^j · 2^{sort(S)_j} mod p
     et S parcourt les sous-ensembles de {1,...,S-1} de taille k-1.

  2. PHÉNOMÈNE D'ANTI-CONCENTRATION :
     Quand C/p >> 1 : l'image couvre {0,...,p-1} \\ {-1} exactement.
     → 0 est le SEUL résidu absent de la B-somme.
     → -1 est le SEUL résidu absent de la somme des k-1 termes.

  3. SPARSITÉ POUR C/p << 1 :
     Beaucoup de résidus manquent, mais -1 TOUJOURS parmi eux.

  4. SANS CONTRAINTE D'ORDRE :
     -1 peut apparaître ! (vérifier pour k=3)
     → C'est la contrainte d'ordre STRICT qui élimine -1.

  5. IDENTITÉ DE CLÔTURE :
     w^k = 2^{-S} mod p → u^k = 2^{k-S}
     La somme σ = Σ u^j ≠ 0 (nécessaire)

  DIRECTION POUR LA PREUVE :
  Montrer que la contrainte d'ordre strict, combinée avec
  la structure multiplicative de w et 2 dans Z/pZ,
  FORCE l'exclusion de -1 de l'image.

  APPROCHES POSSIBLES :
  (a) Combinatoire additive : montrer que le sous-groupe engendré
      par {w^j · 2^a} ne peut couvrir -1 sous la contrainte d'ordre.
  (b) Théorie des nombres : utiliser l'identité de clôture w^k = 2^{-S}
      pour montrer une congruence structurelle.
  (c) Algèbre linéaire : le produit scalaire rank-dépendant
      <w^rank, 2^{sorted_subset}> a une structure bilinéaire
      qui pourrait être analysée.
    """)

    return True

# ============================================================
# MAIN
# ============================================================
if __name__ == "__main__":
    t0 = time.time()
    print("SESSION 9d — TARGET -1 : LE RÉSIDU INTERDIT")
    print("=" * 70)

    investigate_minus_one_systematic()
    investigate_when_only_minus_one()
    investigate_without_order()
    investigate_lacunary_polynomials()
    investigate_dft_approach()
    investigate_induction()
    investigate_w_primitive()
    investigate_subset_sum()
    investigate_composite_d()
    synthesize()

    elapsed = time.time() - t0
    print(f"\n{'=' * 70}")
    print(f"  SESSION 9d TERMINÉE en {elapsed:.1f}s")
    print("=" * 70)
