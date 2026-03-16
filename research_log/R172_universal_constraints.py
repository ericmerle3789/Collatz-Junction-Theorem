#!/usr/bin/env python3
"""
R172 — CONTRAINTES UNIVERSELLES SUR LES f-VALUES
==================================================

Si un k-cycle existe, alors pour un vecteur de parité v :
  f(rot_j) = g(rot_j) / d  est un ENTIER POSITIF pour tout j.

Contraintes connues :
  (C1) 2·f(rot_{j+1}) = 3·f(rot_j) + 1    si v_j = 1
  (C2) 2·f(rot_{j+1}) =   f(rot_j)         si v_j = 0
  (C3) Σ_{v_j=0} f(rot_j) - Σ_{v_j=1} f(rot_j) = x   (E-O identity)
  (C4) Chaque f(rot_j) ≥ 1  (entier positif)
  (C5) f(rot_j) a la parité imposée par la relation

QUESTION CLÉ : Ces contraintes sont-elles SUFFISANTES pour prouver
l'impossibilité ? C'est-à-dire : le système (C1)-(C5) est-il inconsistant
pour tout v de tout (k,x) admissible avec k ≥ 3 ?

APPROCHE : Résoudre le système symboliquement.
La relation de récurrence donne f en fonction de f(rot_0) uniquement.
"""

import math
from itertools import combinations
from fractions import Fraction


def compute_f_chain(v):
    """
    Étant donné v, exprime f(rot_j) en fonction de f_0 = f(rot_0).

    Relation :
      f_{j+1} = (3·f_j + 1)/2  si v_j = 1
      f_{j+1} = f_j / 2        si v_j = 0

    Donc f_j = a_j · f_0 + b_j  où a_j, b_j sont des rationnels.

    Retourne [(a_j, b_j) for j in range(k)] comme Fractions.
    """
    k = len(v)
    a, b = Fraction(1), Fraction(0)  # f_0 = 1·f_0 + 0
    chain = [(a, b)]

    for j in range(k - 1):
        if v[j] == 1:
            a = Fraction(3, 2) * a
            b = Fraction(3, 2) * b + Fraction(1, 2)
        else:
            a = Fraction(1, 2) * a
            b = Fraction(1, 2) * b
        chain.append((a, b))

    return chain


def check_closure(v, chain):
    """
    La condition de fermeture du cycle : f_k = f_0.
    f_k = a_k · f_0 + b_k = f_0
    Donc (a_k - 1) · f_0 = -b_k
    Donc f_0 = -b_k / (a_k - 1) = b_k / (1 - a_k)

    Calcule f_0 et vérifie si c'est un entier positif.
    """
    k = len(v)
    # Calculer f_k en appliquant une dernière étape
    a, b = chain[-1]
    if v[k-1] == 1:
        a_k = Fraction(3, 2) * a
        b_k = Fraction(3, 2) * b + Fraction(1, 2)
    else:
        a_k = Fraction(1, 2) * a
        b_k = Fraction(1, 2) * b

    # f_k = a_k · f_0 + b_k = f_0
    # (a_k - 1) · f_0 = -b_k
    denom = a_k - 1
    if denom == 0:
        return None, a_k, b_k  # Dégénéré

    f0 = -b_k / denom
    return f0, a_k, b_k


def analyze_v_constraints(v):
    """
    Pour un vecteur v, détermine :
    1. La valeur exacte de f_0 (la seule possible)
    2. Si f_0 est un entier positif
    3. Si tous les f_j sont des entiers positifs
    4. Les RAISONS de l'impossibilité
    """
    k = len(v)
    x = sum(v)
    chain = compute_f_chain(v)
    f0, a_k, b_k = check_closure(v, chain)

    result = {
        'v': ''.join(str(b) for b in v),
        'k': k,
        'x': x,
        'f0': f0,
        'a_k': a_k,
        'b_k': b_k,
    }

    if f0 is None:
        result['status'] = 'DEGENERATE'
        return result

    # Vérifier si f0 est un entier positif
    result['f0_is_integer'] = f0.denominator == 1
    result['f0_is_positive'] = f0 > 0

    if not result['f0_is_integer'] or not result['f0_is_positive']:
        result['status'] = 'IMPOSSIBLE_F0'
        # Analyser POURQUOI f0 n'est pas un entier
        # a_k = 3^x / 2^k (toujours)
        # b_k dépend de la structure de v
        result['a_k_simplified'] = f"3^{x}/2^{k} = {a_k}"
        result['denominator_of_f0'] = f0.denominator if f0 > 0 else 'negative'
        return result

    # f0 est un entier positif. Vérifier tous les f_j
    f0_int = int(f0)
    all_positive_integers = True
    f_values = []
    obstruction_j = None

    for j, (a_j, b_j) in enumerate(chain):
        fj = a_j * f0 + b_j
        f_values.append(fj)
        if fj.denominator != 1 or fj <= 0:
            all_positive_integers = False
            if obstruction_j is None:
                obstruction_j = j

    result['f_values'] = f_values
    result['all_positive_integers'] = all_positive_integers

    if all_positive_integers:
        result['status'] = 'CYCLE_EXISTS'
        result['n_min'] = min(int(f) for f in f_values)
    else:
        result['status'] = 'IMPOSSIBLE_CHAIN'
        result['obstruction_at'] = obstruction_j

    return result


def all_parity_vectors(k, x):
    """Génère tous les vecteurs de parité aperiodiques de longueur k avec x uns."""
    for positions in combinations(range(k), x):
        v = tuple(0 if i not in positions else 1 for i in range(k))
        # Vérifier apériodicité
        is_aperiodic = True
        for period in range(1, k):
            if k % period == 0 and period < k:
                if v == v[:period] * (k // period):
                    is_aperiodic = False
                    break
        if is_aperiodic:
            yield v


def compute_S_min(k):
    """Plus petit S tel que 2^S > 3^k."""
    S = math.ceil(k * math.log2(3))
    if 2**S <= 3**k:
        S += 1
    return S


def main():
    print("=" * 72)
    print("R172 — CONTRAINTES UNIVERSELLES SUR LES f-VALUES")
    print("=" * 72)

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 1 : ANALYSE SYMBOLIQUE EXACTE
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "=" * 60)
    print("PARTIE 1 : RÉSOLUTION SYMBOLIQUE EXACTE")
    print("=" * 60)

    print("""
Pour un vecteur v de longueur k avec x uns :
  f_0 = b_k / (1 - a_k)  où a_k = 3^x / 2^k

Donc : f_0 = b_k · 2^k / (2^k - 3^x) = b_k · 2^k / d(k,x,S)

Mais ATTENTION : S dépend de la composition B, pas juste de (k,x).
Pour une composition B = (B_0, ..., B_{k-1}) avec S = B_{k-1} + k :
  d = 2^S - 3^x

La relation de fermeture dans l'espace des f-values est :
  f_0 = (expression en v) · 2^k / (2^k - 3^x)

MAIS CECI N'EST PAS CORRECT car d = 2^S - 3^x avec S > k en général.

Reprenons avec la BONNE formulation :
  g(v) = Σ_{j: v_j=1} 3^{x-1-rank(j)} · 2^{pos(j)}
  f(v) = g(v) / d  doit être un entier positif
""")

    # La formulation correcte est directe via g(v)
    # Mais l'approche par chaîne de récurrence (C1-C2) est aussi valide
    # SEULEMENT si on travaille avec la bonne notion de "cycle"

    # En fait, les relations (C1-C2) sont :
    #   Si n est dans un cycle et n est impair (v_j=1):
    #     le successeur est (3n+1)/2^{s_j} pour un certain s_j ≥ 1
    #   Si s_j = 1 : successeur = (3n+1)/2
    #
    # MAIS les relations (C1-C2) sont la version "compressed" avec s_j=1 toujours
    # Ce n'est correct que si k = S (chaque étape fait exactement une division par 2)
    # C'est le cas k=S uniquement pour k=1 (le point fixe 1→1)

    # La BONNE formulation pour S > k :
    # On doit incorporer les s_j dans la chaîne.
    # f_{j+1} = (3·f_j + 1) / 2^{s_j}  si v_j = 1
    # f_{j+1} = f_j / 2^{s_j}           si v_j = 0
    # Mais les s_j dépendent de la composition B !

    print("CORRECTION IMPORTANTE :")
    print("Les relations (C1-C2) avec divisions par 2 sont la version Shortcut.")
    print("Pour la formulation STRICTE avec S = Σs_j, on doit utiliser :")
    print("  f_{j+1} = (3·f_j + 1) / 2^{s_j}  si v_j = 1")
    print("  f_{j+1} = f_j / 2^{s_j}           si v_j = 0")
    print("avec s_j ≥ 1 et Σ s_j = S.")
    print()

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 2 : FORMULE UNIVERSELLE VIA LA FERMETURE
    # ═══════════════════════════════════════════════════════════════
    print("=" * 60)
    print("PARTIE 2 : FORMULE DE FERMETURE UNIVERSELLE")
    print("=" * 60)

    print("""
Pour un vecteur de parité v = (v_0, ..., v_{k-1}) et une composition
s = (s_0, ..., s_{k-1}) avec s_j ≥ 1, S = Σ s_j :

La récurrence donne :
  f_j = (a_j · f_0 + b_j)  où a_j, b_j dépendent de v et s.

Spécifiquement :
  a_j = ∏_{i<j} c_i / 2^{s_i}  où c_i = 3 si v_i=1, c_i = 1 si v_i=0

Après k étapes : a_k = 3^x / 2^S, b_k = expression complexe.

Fermeture : f_0 = b_k / (1 - 3^x/2^S) = b_k · 2^S / (2^S - 3^x) = b_k · 2^S / d

Pour f_0 ∈ Z⁺ : d | b_k · 2^S. Comme gcd(d, 2) = 1 (d impair) : d | b_k.

Et b_k = Σ_{j: v_j=1} ∏_{i>j, v_i=1} 3 · ∏_{i>j, v_i=0} 1 / 2^{Σ_{i>j} s_i}
       = Σ_{j: v_j=1} 3^{x - 1 - rank(j)} / 2^{S - Σ_{i≤j} s_i}
       = Σ_{j: v_j=1} 3^{x - 1 - rank(j)} / 2^{S - B_j - 1}   (où B_j = Σ_{i<j} s_i + j - ...)

Hmm c'est circulaire. Calculons DIRECTEMENT.
""")

    # Calcul direct avec les bons s_j
    def compute_f0_exact(v, s_list):
        """
        Calcule f_0 exactement pour un vecteur v et composition s.
        """
        k = len(v)
        x = sum(v)
        S = sum(s_list)
        d = 2**S - 3**x

        if d <= 0:
            return None, None, d

        # Construire la chaîne a_j, b_j
        a = Fraction(1)
        b = Fraction(0)

        for j in range(k):
            if v[j] == 1:
                a = Fraction(3, 2**s_list[j]) * a
                b = Fraction(3, 2**s_list[j]) * b + Fraction(1, 2**s_list[j])
            else:
                a = Fraction(1, 2**s_list[j]) * a
                b = Fraction(1, 2**s_list[j]) * b

        # f_0 = b / (1 - a)
        denom = 1 - a
        if denom == 0:
            return None, None, d

        f0 = b / denom
        return f0, d, d

    def check_all_f_positive(v, s_list, f0):
        """Vérifie si tous les f_j sont des entiers positifs."""
        k = len(v)
        f = f0
        f_values = [f]
        for j in range(k):
            if v[j] == 1:
                f = Fraction(3 * f + 1, 2**s_list[j])
            else:
                f = Fraction(f, 2**s_list[j])
            f_values.append(f)

        # f_values[-1] doit être = f_values[0]
        assert f_values[-1] == f_values[0], f"Closure failed: {f_values[-1]} != {f_values[0]}"

        all_ok = all(fj.denominator == 1 and fj > 0 for fj in f_values[:-1])
        return all_ok, f_values[:-1]

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 3 : EXPLORATION SYSTÉMATIQUE
    # ═══════════════════════════════════════════════════════════════
    print("\n" + "=" * 60)
    print("PARTIE 3 : EXPLORATION — QU'EST-CE QUI BLOQUE ?")
    print("=" * 60)

    # Pour chaque (k, x) admissible et S = S_min :
    # Énumérer les compositions s (monotone → strict)
    # Pour chaque (v, s), calculer f_0 et vérifier

    # Compositions strictes : s_j ≥ 1, Σ s_j = S
    def strict_compositions(k, S):
        """Génère toutes les compositions de S en k parts, chaque part ≥ 1."""
        if k == 1:
            yield [S]
            return
        for s0 in range(1, S - k + 2):
            for rest in strict_compositions(k - 1, S - s0):
                yield [s0] + rest

    # Pour petits k et S_min
    for k in range(2, 12):
        for x in range(1, k):
            S = compute_S_min(x)  # Wait, S_min depends on k in our Collatz context
            # Actually S_min is the smallest S such that 2^S > 3^x and S > k
            # For a k-cycle with x odd steps: S must satisfy 2^S > 3^x
            # and S = Σ s_j with each s_j ≥ 1, so S ≥ k
            S_min = max(k, math.ceil(x * math.log2(3)))
            if 2**S_min <= 3**x:
                S_min += 1
            if S_min < k:
                S_min = k

            d = 2**S_min - 3**x
            if d <= 0:
                continue

            # Pour chaque vecteur de parité v avec x uns dans {0,...,k-1}
            # et S = S_min, compter combien ont f_0 ∈ Z⁺

            n_tested = 0
            n_impossible_f0 = 0  # f_0 not a positive integer
            n_impossible_chain = 0  # some f_j not a positive integer
            n_cycle = 0  # actual cycle found
            reasons = {}

            if k > 8:  # Skip large cases for speed
                continue

            # Enumerate all parity vectors
            for positions in combinations(range(k), x):
                v = tuple(1 if i in positions else 0 for i in range(k))

                # For S_min, enumerate compositions
                # For small S-k, this is manageable
                gap = S_min - k  # Each s_j = 1 + gap_j where gap_j ≥ 0 and Σ gap_j = S-k

                if gap > 15:  # Too many compositions
                    continue

                # Compositions of gap into k non-negative parts
                # = C(gap + k - 1, k - 1) ... can be huge
                from math import comb
                n_comp = comb(gap + k - 1, k - 1)
                if n_comp > 1000:
                    continue

                def compositions_nonneg(n, k_parts):
                    if k_parts == 1:
                        yield [n]
                        return
                    for g0 in range(n + 1):
                        for rest in compositions_nonneg(n - g0, k_parts - 1):
                            yield [g0] + rest

                for gaps in compositions_nonneg(gap, k):
                    s_list = [1 + g for g in gaps]
                    n_tested += 1

                    f0, d_val, _ = compute_f0_exact(v, s_list)
                    if f0 is None:
                        continue

                    if f0.denominator != 1 or f0 <= 0:
                        n_impossible_f0 += 1
                        # WHY is f0 not an integer?
                        reason = f"f0={f0}" if f0 > 0 else f"f0={f0} (neg/zero)"
                        if f0 > 0:
                            denom = f0.denominator
                            # Factor the denominator
                            d2 = 0
                            temp = denom
                            while temp % 2 == 0:
                                d2 += 1
                                temp //= 2
                            d3 = 0
                            while temp % 3 == 0:
                                d3 += 1
                                temp //= 3
                            key = f"denom=2^{d2}*3^{d3}*{temp}"
                        else:
                            key = "negative"
                        reasons[key] = reasons.get(key, 0) + 1
                    else:
                        # f0 is a positive integer — check entire chain
                        all_ok, f_vals = check_all_f_positive(v, s_list, f0)
                        if all_ok:
                            n_cycle += 1
                            # This would be a CYCLE!
                            v_str = ''.join(str(b) for b in v)
                            print(f"  ⚠️ CYCLE FOUND? k={k}, x={x}, v={v_str}, "
                                  f"s={s_list}, f_values={[int(f) for f in f_vals]}")
                        else:
                            n_impossible_chain += 1

            if n_tested > 0:
                print(f"  k={k}, x={x}: S={S_min}, d={d}, tested={n_tested}, "
                      f"impossible_f0={n_impossible_f0}, impossible_chain={n_impossible_chain}, "
                      f"CYCLES={n_cycle}")
                if reasons:
                    top_reasons = sorted(reasons.items(), key=lambda x: -x[1])[:5]
                    print(f"    Reasons: {top_reasons}")

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 4 : LA CLÉ — STRUCTURE DU DÉNOMINATEUR
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("PARTIE 4 : STRUCTURE DU DÉNOMINATEUR DE f_0")
    print("=" * 60)

    print("""
f_0 = b_k / (1 - 3^x/2^S) = b_k · 2^S / (2^S - 3^x) = b_k · 2^S / d

Puisque d est impair et gcd(2^S, d) = 1, f_0 ∈ Z ⟺ d | b_k.

La question se réduit à : b_k mod d = ?

b_k = Σ_{j: v_j=1} (contribution du j-ème odd step)

Calculons b_k explicitement.
""")

    # Symbolic computation of b_k
    # For a given v and s, b_k is the "constant term" in f_k = a_k·f_0 + b_k

    def compute_b_k(v, s_list):
        """Compute b_k exactly."""
        k = len(v)
        a = Fraction(1)
        b = Fraction(0)

        for j in range(k):
            if v[j] == 1:
                a = Fraction(3, 2**s_list[j]) * a
                b = Fraction(3, 2**s_list[j]) * b + Fraction(1, 2**s_list[j])
            else:
                a = Fraction(1, 2**s_list[j]) * a
                b = Fraction(1, 2**s_list[j]) * b

        return b

    # For the circuit v_c = (1,1,...,1,0,0,...,0) and s = (1,1,...,1,gap+1) or similar
    print("\nExemple : Circuit v_c = 1^x 0^{k-x}")

    for k in range(2, 8):
        for x in range(1, k):
            S_min = max(k, math.ceil(x * math.log2(3)))
            if 2**S_min <= 3**x:
                S_min += 1
            d = 2**S_min - 3**x
            if d <= 0:
                continue

            # Circuit: v = 1^x 0^{k-x}, s = (1,...,1, S-k+1) i.e. last step gets the extra
            v = tuple([1]*x + [0]*(k-x))
            s_list = [1]*(k-1) + [S_min - k + 1]

            b = compute_b_k(v, s_list)
            # b_k · 2^S / d should be f_0
            f0 = b * 2**S_min / d

            # Also compute g(v)
            # g(v) = d · f(v) where f(v) = n_min of the cycle
            # For circuit: g = sum of 3^{x-1-j} · 2^{B_j}
            # With B_j = j for j < k-1, B_{k-1} = S-k
            B = list(range(k-1)) + [S_min - k]  # Wait, this isn't right
            # For circuit v = 1^x 0^{k-x} and s = (1,...,1,S-k+1):
            # B_0 = 0, B_1 = s_0 = 1, B_2 = s_0+s_1 = 2, ..., B_{k-2} = k-2, B_{k-1} = S-k
            # Wait, B_j = Σ_{i<j} s_i = j for j < k-1, B_{k-1} = (k-2) + (S-k+1) = S-1...
            # No. B_j cumulative sum of gaps. Let me reconsider.

            # In our formulation: positions d_i where v has a 1
            # For v = (1,1,...,1,0,...,0), the 1s are at positions 0,1,...,x-1
            # g(v) = Σ_{i=0}^{x-1} 2^i · 3^{x-1-i} = Σ 2^i · 3^{x-1-i}
            # = 3^{x-1} + 2·3^{x-2} + ... + 2^{x-1} = (3^x - 2^x)/(3-2) = 3^x - 2^x
            g_circuit = 3**x - 2**x
            f_circuit = Fraction(g_circuit, d)

            print(f"  k={k}, x={x}: d={d}, b_k={b}, f_0={f0}, "
                  f"g_circuit={g_circuit}, f_circuit={f_circuit}, "
                  f"f_circuit_int={'YES' if f_circuit.denominator == 1 else 'NO'}")

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 5 : LE THÉORÈME DE FERMETURE
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("PARTIE 5 : VERS LE THÉORÈME UNIVERSEL")
    print("=" * 60)

    print("""
OBSERVATION CLÉ de la Partie 3 :
Le dénominateur de f_0 est TOUJOURS une puissance de d (modulo des facteurs 2).

Plus précisément :
  f_0 = b_k · 2^S / d
  b_k = Σ_{j où v_j=1} 3^{#(uns après j)} / 2^{Σ_{i>j} s_i}
      = (1/2^S) · Σ_{j où v_j=1} 3^{#(uns après j)} · 2^{Σ_{i≤j} s_i}

Donc : f_0 = (1/d) · Σ_{j où v_j=1} 3^{rank_after(j)} · 2^{B_j}

Mais Σ_{j où v_j=1} 3^{rank_after(j)} · 2^{B_j} = g(v) exactement !

Donc f_0 = g(v) / d. Ce qui est la DÉFINITION.

La question est : pourquoi d ne divise JAMAIS g(v) pour k ≥ 3 ?

REFORMULATION FINALE :
  g(v) = Σ_{i=0}^{x-1} 3^{x-1-i} · 2^{d_i}
  d = 2^S - 3^x
  où d_0 < d_1 < ... < d_{x-1}, Σ gaps ≤ S - k

  Prouver : pour tout k ≥ 3, tout x, tout S admissible, tout choix de positions :
    g(v) ≢ 0 mod d
""")

    # Vérifions numériquement la TAILLE de g(v) par rapport à d
    print("\nRAPPORT g(v)/d pour divers vecteurs :")

    for k in range(3, 15):
        x = k  # Dans notre notation k = nombre d'odd steps
        S = compute_S_min(x)
        d = 2**S - 3**x
        if d <= 0:
            continue

        # g pour le circuit
        g_min = 3**x - 2**x  # circuit
        g_max = 3**(x-1) * 2**(S-x) + sum(3**(x-2-i) * 2**(S-x-1+i) for i in range(x-1)) if x > 1 else 2**(S-1)
        # Actually g_max when positions are as spread as possible
        # Max g: positions d_i = S - x + i (i.e., spread as far right as possible)
        positions_max = list(range(S - x, S))
        g_max_actual = sum(3**(x-1-i) * 2**positions_max[i] for i in range(x))

        # Min g: positions d_i = i (i.e., packed left)
        positions_min = list(range(x))
        g_min_actual = sum(3**(x-1-i) * 2**positions_min[i] for i in range(x))

        ratio_min = g_min_actual / d
        ratio_max = g_max_actual / d

        print(f"  k(odd)={x}, S={S}: d={d}, g_min={g_min_actual}, g_max={g_max_actual}, "
              f"ratio=[{ratio_min:.3f}, {ratio_max:.3f}]")

    # ═══════════════════════════════════════════════════════════════
    # PARTIE 6 : TEST DE L'HYPOTHÈSE ARCHIMÉDIENNE
    # ═══════════════════════════════════════════════════════════════
    print("\n\n" + "=" * 60)
    print("PARTIE 6 : BORNE ARCHIMÉDIENNE")
    print("=" * 60)

    print("""
Si g(v)/d doit être un entier ≥ 1, alors g(v) ≥ d.
Mais g_min (circuit) = 3^x - 2^x.
Et d = 2^S - 3^x.

Pour S = S_min = ⌈x·log₂3⌉ + ε :
  d ≈ 2^{x·log₂3} - 3^x ≈ 3^x - 3^x = très petit
  (en fait d < 3^x toujours pour S_min)

Donc g_min = 3^x - 2^x et d = 2^{S_min} - 3^x.
g_min / d = (3^x - 2^x) / (2^{S_min} - 3^x)

Pour le circuit, f_circuit est le SEUL candidat de cycle à tester.
Steiner (1977) a prouvé que f_circuit n'est pas un entier pour k ≥ 2.

Mais il y a d'AUTRES vecteurs de parité ! Le circuit n'est qu'un cas.
""")

    # Calculons le nombre de multiples de d dans [g_min, g_max]
    for x in range(3, 20):
        S = compute_S_min(x)
        d = 2**S - 3**x
        if d <= 0:
            continue

        positions_min = list(range(x))
        g_min_actual = sum(3**(x-1-i) * 2**positions_min[i] for i in range(x))

        positions_max = list(range(S - x, S))
        g_max_actual = sum(3**(x-1-i) * 2**positions_max[i] for i in range(x))

        # Number of multiples of d in [g_min, g_max]
        n_multiples = g_max_actual // d - (g_min_actual - 1) // d

        # Number of valid parity vectors
        from math import comb
        n_vectors = comb(S, x) if S <= 60 else float('inf')

        print(f"  x={x:2d}: S={S:3d}, d={d:>15d}, [g_min,g_max]=[{g_min_actual},{g_max_actual}], "
              f"multiples_of_d={n_multiples}, n_vectors≈C({S},{x})")


if __name__ == '__main__':
    main()
