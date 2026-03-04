#!/usr/bin/env python3
"""
FRONT 1 — MECANISME DE BLOCAGE
===============================
Pourquoi l'etat 0 est-il inatteignable en exactement k-1 pas ?

Trois contraintes interagissent :
  (A) Algebrique : 2^p mod d ne couvre pas tous les residus
  (B) Ordre : positions strictement croissantes p1 < p2 < ... < p_{k-1}
  (C) Frontiere : 1 ≤ p_j ≤ S-1

On trace la propagation dans l'automate et on identifie le point de blocage.
"""

from itertools import combinations
from collections import defaultdict, Counter
import math


def trace_blocking(k_val):
    """Analyse complete du mecanisme de blocage pour un k donne."""
    S = math.ceil(k_val * math.log2(3))
    d = 2**S - 3**k_val
    C = math.comb(S - 1, k_val - 1)

    if d <= 0:
        return None

    print(f"\n{'='*80}")
    print(f"MECANISME DE BLOCAGE : k={k_val}, S={S}, d={d}, C={C}, C/d={C/d:.4f}")
    print(f"{'='*80}")

    # Ordres dans Z/dZ
    def multiplicative_order(base, mod):
        if math.gcd(base, mod) != 1:
            return None
        val, order = base % mod, 1
        while val != 1 and order < mod:
            val = (val * base) % mod
            order += 1
        return order if val == 1 else None

    ord2 = multiplicative_order(2, d)
    ord3 = multiplicative_order(3, d)

    print(f"\nord_{d}(2) = {ord2}, ord_{d}(3) = {ord3}")
    print(f"S-1 = {S-1} positions disponibles (p=1..{S-1})")

    if ord2:
        print(f"Ratio (S-1)/ord(2) = {(S-1)/ord2:.3f}")
        print(f"  → {'TOUTES' if S-1 >= ord2 else 'PAS TOUTES'} les puissances de 2 sont disponibles")

    # Puissances de 2 disponibles (p=1..S-1)
    pow2_available = {p: pow(2, p, d) for p in range(1, S)}
    available_residues = set(pow2_available.values())
    all_nonzero = set(range(1, d)) if math.gcd(2, d) == 1 else set(range(d))
    unreachable = all_nonzero - available_residues - {0}

    print(f"\n--- Puissances de 2 disponibles mod {d} (p=1..{S-1}) ---")
    print(f"  Residus atteints : {sorted(available_residues)}")
    print(f"  Nombre : {len(available_residues)} / {d-1}")
    if unreachable:
        print(f"  Residus NON atteints (gap) : {sorted(unreachable)}")
        print(f"  Taille du gap : {len(unreachable)}")

    # ANALYSE TRANSITION-PAR-TRANSITION DE L'AUTOMATE
    print(f"\n{'='*80}")
    print(f"PROPAGATION DANS L'AUTOMATE")
    print(f"{'='*80}")

    # Layer = dict de (state, last_pos) -> count
    layers = [{(1 % d, 0): 1}]  # Etat initial = 1, position initiale = 0

    for step in range(1, k_val):
        current = layers[-1]
        next_layer = defaultdict(int)
        for (state, last_pos), count in current.items():
            for p in range(last_pos + 1, S):
                next_state = (3 * state + 2**p) % d
                next_layer[(next_state, p)] += count
        layers.append(dict(next_layer))

    # Afficher l'analyse par etape
    for step in range(k_val):
        layer = layers[step]
        states = Counter()
        for (s, p), c in layer.items():
            states[s] += c
        total = sum(states.values())

        # Combien de chemins POURRAIENT atteindre 0 a l'etape suivante ?
        potential_to_zero = 0
        blocked_to_zero = 0

        if step < k_val - 1:
            for (s, p), c in layer.items():
                # Pour aller a 0 : 3s + 2^q ≡ 0 mod d → 2^q ≡ -3s mod d
                target_pow2 = (-3 * s) % d
                if target_pow2 == 0:
                    # Besoin de 2^q ≡ 0 mod d, impossible si gcd(2,d)=1
                    blocked_to_zero += c
                    continue

                # Chercher q > p avec 2^q mod d = target
                found = False
                for q in range(p + 1, S):
                    if pow(2, q, d) == target_pow2:
                        found = True
                        break
                if found:
                    potential_to_zero += c
                else:
                    blocked_to_zero += c

        zero_count = states.get(0, 0)
        print(f"\n  Etape {step} : {total} chemins, {len(states)} etats distincts, "
              f"{zero_count} a l'etat 0")
        if step < k_val - 1:
            print(f"    → {potential_to_zero} chemins POURRAIENT atteindre 0 a l'etape {step+1}")
            print(f"    → {blocked_to_zero} chemins BLOQUES (pas de position valide vers 0)")

    # Distribution finale
    final_layer = layers[-1]
    final_states = Counter()
    for (s, p), c in final_layer.items():
        final_states[s] += c

    N0 = final_states.get(0, 0)
    print(f"\n--- RESULTAT FINAL ---")
    print(f"N₀(d={d}) = {N0}")

    # ANALYSE ARRIERE : pourquoi 0 n'est pas atteint ?
    print(f"\n{'='*80}")
    print(f"ANALYSE ARRIERE : pourquoi 0 n'est pas atteint au pas final ?")
    print(f"{'='*80}")

    # Au dernier pas, pour atteindre 0 depuis (s, p) :
    # 3s + 2^q ≡ 0 mod d, q > p, q ≤ S-1
    penultimate = layers[-2]  # Avant-derniere couche

    print(f"\nEtats a l'etape {k_val-2} et possibilite de transition vers 0 :")
    reasons = Counter()

    for (s, p), c in sorted(penultimate.items()):
        target = (-3 * s) % d
        # Chercher q > p dans {p+1, ..., S-1} avec 2^q ≡ target mod d
        possible_q = [q for q in range(p + 1, S) if pow(2, q, d) == target]

        if target == 0:
            reason = "IMPOSSIBLE (2^q ≢ 0)"
            reasons["2^q cannot be 0"] += c
        elif target not in available_residues:
            reason = f"BLOQUE (besoin 2^q≡{target}, pas dans {{2^1,...,2^{S-1}}} mod {d})"
            reasons["target not in available powers"] += c
        elif not possible_q:
            reason = f"BLOQUE PAR ORDRE (besoin q>{p} avec 2^q≡{target}, q candidats: aucun ≤{S-1})"
            reasons["position constraint (q > p_last)"] += c
        else:
            reason = f"POSSIBLE via q={possible_q} mais chemin non realise"
            reasons["theoretically possible but unrealized"] += c

        if c <= 3 or d <= 50:  # Afficher les details pour les petits cas
            print(f"  (s={s:3d}, p={p}) [{c} chemins] : besoin 2^q≡{target}, {reason}")

    print(f"\n--- SYNTHESE DES RAISONS DE BLOCAGE ---")
    total_paths = sum(reasons.values())
    for reason, count in reasons.most_common():
        pct = count / total_paths * 100
        print(f"  {count:5d} chemins ({pct:5.1f}%) : {reason}")

    # VERIFICATION SPECIFIQUE : 2^S mod d
    print(f"\n--- RELATION CLE ---")
    print(f"2^S mod d = 2^{S} mod {d} = {pow(2, S, d)}")
    print(f"3^k mod d = 3^{k_val} mod {d} = {pow(3, k_val, d)}")
    print(f"2^S - 3^k = d = {d} → 2^S ≡ 3^k ≡ 0 mod d")
    print(f"Donc 2^S ≡ 0 mod d → position p=S donne 2^S ≡ 0 mod d")
    print(f"MAIS p ≤ S-1 = {S-1} donc p=S est INTERDIT !")

    # La position p=0 (A_0) est deja fixee et donne 2^0 = 1
    # La position p=S donnerait 2^S ≡ 0 mod d mais elle n'est pas disponible
    # C'est la CLE : d = 2^S - 3^k signifie exactement que 2^S ≡ 0 mod d
    # Si on POUVAIT utiliser p=S, on pourrait atteindre plus de residus

    return {
        'k': k_val, 'S': S, 'd': d, 'C': C, 'N0': N0,
        'ord2': ord2, 'reasons': dict(reasons),
        'available': available_residues, 'unreachable': unreachable
    }


# ============================================================
# Executer pour plusieurs k
# ============================================================

print("*" * 80)
print("FRONT 1 — ANALYSE DU MECANISME DE BLOCAGE")
print("*" * 80)

# Cas detailles
for k in [3, 5]:
    trace_blocking(k)

# Synthese multi-k
print(f"\n{'='*80}")
print(f"SYNTHESE MULTI-k : MECANISME DE BLOCAGE")
print(f"{'='*80}")

print(f"\n{'k':>3} {'S':>3} {'d':>10} {'C':>8} {'C/d':>7} {'ord2':>5} "
      f"{'|avail|':>8} {'|gap|':>6} {'S-1':>4} {'gap%':>6} {'N0':>4}")
print("-" * 85)

for k in range(3, 18):
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    C = math.comb(S - 1, k - 1)
    if d <= 0:
        continue

    def mord(b, m):
        if math.gcd(b, m) != 1: return None
        v, o = b % m, 1
        while v != 1 and o < m: v, o = (v * b) % m, o + 1
        return o if v == 1 else None

    ord2 = mord(2, d)
    avail = set(pow(2, p, d) for p in range(1, S))
    gap = set(range(1, d)) - avail if math.gcd(2, d) == 1 else set()
    gap_pct = len(gap) / (d - 1) * 100 if d > 1 else 0

    # Calculer N0 pour les k raisonnables
    if C <= 500000:
        cs_mod = []
        for combo in combinations(range(1, S), k - 1):
            A = (0,) + combo
            c = 1
            for j in range(1, k):
                c = 3 * c + 2**A[j]
            cs_mod.append(c % d)
        N0 = sum(1 for r in cs_mod if r == 0)
    else:
        N0 = "?"

    ord2_str = str(ord2) if ord2 else "?"
    print(f"{k:3d} {S:3d} {d:10d} {C:8d} {C/d:7.4f} {ord2_str:>5} "
          f"{len(avail):8d} {len(gap):6d} {S-1:4d} {gap_pct:6.1f} {str(N0):>4}")


# ============================================================
# DECOUVERTE CLE : 2^S ≡ 0 mod d
# ============================================================

print(f"\n{'='*80}")
print(f"DECOUVERTE STRUCTURELLE : LE ROLE DE 2^S ≡ 0 mod d")
print(f"{'='*80}")

print("""
OBSERVATION FONDAMENTALE :
  d = 2^S - 3^k  →  2^S ≡ 3^k (mod d)  →  2^S ≡ 0 (mod d) [car 3^k ≡ 2^S mod d]

  Non ! En fait 2^S - 3^k = d donc 2^S ≡ 3^k mod d, pas 0.
  Mais d | (2^S - 3^k) par definition, donc 2^S ≡ 3^k mod d.

CORRECTION : 2^S mod d = 3^k mod d.
  Pour k=5 : 2^8 mod 13 = 256 mod 13 = 9, et 3^5 mod 13 = 243 mod 13 = 9. ✓

  Donc la position hypothetique p=S donnerait la valeur 2^S ≡ 3^k (mod d).
  Ce n'est PAS 0 (sauf si 3^k ≡ 0 mod d, ce qui n'arrive que si 3|d).

RELECTURE : La question est pourquoi corrSum ≡ 0 mod d est impossible.
  corrSum = Σ 3^{k-1-j} · 2^{A_j}, et corrSum ≡ 0 mod d signifie
  qu'un entier positif n₀ = corrSum/d existe. Cela correspondrait a un cycle
  de Collatz de longueur k.

MECANISME : La combinaison de trois contraintes rend 0 inaccessible :
  1. ALGEBRIQUE : Les puissances 2^p pour p=1..S-1 ne couvrent qu'une
     fraction des residus de Z/dZ* (quand S < ord_d(2)).
  2. ORDRE CROISSANT : Les positions doivent etre strictement croissantes,
     ce qui limite les combinaisons de transitions.
  3. BORNE SUPERIEURE : p ≤ S-1 coupe les grandes puissances de 2,
     creant un "gap" dans les residus accessibles.
""")

# Pour k=5, verifier specifiquement
print(f"Pour k=5, d=13 :")
print(f"  Positions disponibles : 1..7 (S-1=7)")
print(f"  ord_13(2) = 12 > 7 = S-1")
print(f"  Puissances 2^p pour p=1..7 : {sorted(pow(2,p,13) for p in range(1,8))}")
print(f"  Manquent : {sorted(set(range(1,13)) - set(pow(2,p,13) for p in range(1,8)))}")
print(f"  = {{2^0, 2^8, 2^9, 2^10, 2^11}} mod 13 = {{1, 9, 5, 10, 7}}")
print(f"  Ce sont les puissances de 2 aux positions HORS LIMITES !")

# ============================================================
# TEST DE LA CONJECTURE : ord_d(2) > S-1 implique gap
# ============================================================

print(f"\n{'='*80}")
print(f"CONJECTURE : ord_d(2) > S-1 ⟹ gap dans les puissances disponibles")
print(f"{'='*80}")

for k in range(3, 18):
    S = math.ceil(k * math.log2(3))
    d = 2**S - 3**k
    if d <= 0:
        continue

    def mord(b, m):
        if math.gcd(b, m) != 1: return None
        v, o = b % m, 1
        while v != 1 and o < m: v, o = (v * b) % m, o + 1
        return o if v == 1 else None

    ord2 = mord(2, d)
    has_gap = (ord2 is not None and ord2 > S - 1)

    # Pour les facteurs premiers de d
    # Factorisation simple
    factors = []
    n = d
    for p in range(2, min(int(n**0.5) + 1, 100000)):
        while n % p == 0:
            factors.append(p)
            n //= p
    if n > 1:
        factors.append(n)

    factor_str = " × ".join(str(f) for f in factors) if len(factors) > 1 else str(d)
    if len(set(factors)) == 1 and len(factors) > 1:
        factor_str = f"{factors[0]}^{len(factors)}"

    ord2_str = str(ord2) if ord2 else "?"
    print(f"  k={k:2d}: d={d:>10}, d={factor_str}, ord_d(2)={ord2_str:>6}, "
          f"S-1={S-1:3d}, gap={'OUI' if has_gap else 'non'}")
