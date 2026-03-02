#!/usr/bin/env python3
"""
SP9-O4 : Analyse théorique de D26 — Pourquoi p/m² est borné
==============================================================
QUESTION : Peut-on prouver que pour p | d(k), le ratio p/m² est borné ?

APPROCHE 1 : Comptage par ordres
  Pour un ord m donné, combien y a-t-il de primes p telles que :
  (a) ord_p(2) = m
  (b) p | d(k) pour un certain k ∈ [69, K]

APPROCHE 2 : Contrainte de Fermat
  m | (p-1), donc p ≡ 1 mod m. Les primes p ≡ 1 mod m sont espacées
  de ~φ(m)·ln(p) par le théorème de Dirichlet. Pour p > m², le nombre
  de telles primes qui divisent d(k) devrait être "contrôlé".

APPROCHE 3 : Analyse de la contrainte D25
  3^k ∈ ⟨2⟩ mod p signifie que 3^k = 2^r mod p avec r = S mod m.
  Ceci fixe r pour un k donné. Donc p | (2^r - 3^k/2^{S-r·...})...
  Plus précisément : p | (2^r - 3^k) si S = qm + r avec 0 ≤ r < m.
  NON : 2^S = 2^{qm+r} = (2^m)^q · 2^r ≡ 2^r mod p.
  Donc p | (2^r - 3^k).

  Ceci est CRUCIAL : p divise un nombre BIEN PLUS PETIT que d(k) !
  En effet, |2^r - 3^k| << 2^S pour r << S.
"""

from math import log, ceil, gcd
from sympy import factorint, isprime, nextprime

print("=" * 70)
print("SP9-O4 : Analyse de la contrainte D25 sur p | d(k)")
print("=" * 70)
print()

# DÉCOUVERTE CLÉ : p | (2^r - 3^k) où r = S mod m et 0 ≤ r < m
# Puisque m = ord_p(2), on a r < m, donc 2^r < 2^m ≤ 2^{p-1} < p^{p-1}
# Mais surtout : |2^r - 3^k| est beaucoup plus petit que d(k) = 2^S - 3^k

print("APPROCHE A : Réduction de D25")
print("-" * 70)
print()
print("Si p | d(k) et m = ord_p(2), posons r = S mod m.")
print("Alors : p | (2^r - 3^k) car 2^S ≡ 2^r mod p.")
print("De plus : 0 ≤ r < m, donc 2^r < 2^m.")
print()
print("QUESTION : Quelle est la taille de |2^r - 3^k| ?")
print()

# Pour chaque k, calculer r = S mod m pour différents m possibles
# et voir la taille de |2^r - 3^k|

test_cases = []
for k in range(69, 200):
    S = ceil(k * log(3) / log(2))
    dk = pow(2, S) - pow(3, k)
    if dk <= 0:
        continue

    # Factoriser d(k) - trial division rapide
    remaining = abs(dk)
    for p_trial in range(2, min(10**6, remaining)):
        if remaining <= 1:
            break
        if remaining % p_trial == 0:
            while remaining % p_trial == 0:
                remaining //= p_trial

            p = p_trial
            if not isprime(p):
                continue

            # Calculer m
            h = 1
            for m in range(1, p):
                h = (h * 2) % p
                if h == 1:
                    break

            if m <= 100:
                continue

            r = S % m
            reduced = abs(pow(2, r) - pow(3, k))

            # Vérification
            assert dk % p == 0
            assert reduced % p == 0, f"ERREUR: p={p} ne divise pas 2^r - 3^k"

            # Tailles
            log2_dk = S  # ≈ log2(d(k))
            log2_reduced = log(max(1, reduced)) / log(2)
            ratio = log2_reduced / log2_dk if log2_dk > 0 else 0
            pm2 = p / (m * m)

            test_cases.append({
                'k': k, 'p': p, 'm': m, 'r': r, 'S': S,
                'log2_dk': log2_dk, 'log2_reduced': log2_reduced,
                'ratio': ratio, 'pm2': pm2
            })

print(f"Cas trouvés (k ∈ [69, 200], primes < 10^6, ord > 100) : {len(test_cases)}")
print()

if test_cases:
    print("Exemples :")
    print(f"{'k':>4s} {'p':>8s} {'m':>5s} {'r':>5s} {'log2(dk)':>10s} {'log2(red)':>10s} {'ratio':>8s} {'p/m²':>8s}")
    print("-" * 65)
    for e in test_cases[:20]:
        print(f"{e['k']:4d} {e['p']:8d} {e['m']:5d} {e['r']:5d} "
              f"{e['log2_dk']:10.1f} {e['log2_reduced']:10.1f} "
              f"{e['ratio']:8.4f} {e['pm2']:8.4f}")

    print()
    # Statistiques
    ratios = [e['ratio'] for e in test_cases]
    pm2s = [e['pm2'] for e in test_cases]
    print(f"Ratio log2(reduced)/log2(dk) : min={min(ratios):.4f}, max={max(ratios):.4f}, mean={sum(ratios)/len(ratios):.4f}")
    print(f"p/m² : min={min(pm2s):.4f}, max={max(pm2s):.4f}")

print()
print("=" * 70)
print("APPROCHE B : Borne sur p via |2^r - 3^k|")
print("-" * 70)
print()
print("LEMME POTENTIEL (D28) :")
print("  Si p | d(k) et m = ord_p(2) > 100, alors p | (2^r - 3^k)")
print("  où r = S mod m, 0 ≤ r < m.")
print()
print("  Puisque p | (2^r - 3^k) et 2^r - 3^k ≠ 0 (car sinon 2^r = 3^k,")
print("  ce qui est impossible par unicité de la factorisation première"),
print()
print("  on a : p ≤ |2^r - 3^k|.")
print()
print("  Or r < m, donc 2^r < 2^m.")
print("  Et 3^k ≈ 2^{k·log₂(3)} ≈ 2^{1.585·k}.")
print("  Tandis que m > 100 et r = S mod m < m.")
print()
print("  QUESTION CRITIQUE : 3^k est-il toujours >> 2^r ?")
print("  Si oui, alors p ≤ 3^k (trivialement), ce qui ne donne rien d'utile.")
print("  Si 2^r ≈ 3^k mod p est petit, alors p ≤ max(2^r, 3^k).")
print()

# Vérifions : est-ce que 2^r est parfois comparable à 3^k ?
print("Comparaison 2^r vs 3^k :")
if test_cases:
    for e in test_cases[:10]:
        k, r = e['k'], e['r']
        log2_2r = r
        log2_3k = k * log(3) / log(2)
        print(f"  k={k:3d}, r={r:4d}: log₂(2^r)={log2_2r:.1f}, log₂(3^k)={log2_3k:.1f}, "
              f"diff={abs(log2_2r - log2_3k):.1f} bits")

print()
print("=" * 70)
print("APPROCHE C : Comptage — Combien de primes p ≡ 1 mod m avec p | d(k) ?")
print("-" * 70)
print()
print("Par le petit théorème de Fermat, m | (p-1), donc p ≡ 1 mod m.")
print("Par Dirichlet, les primes ≡ 1 mod m ont densité 1/φ(m) ≈ 1/m.")
print()
print("Pour chaque tel p, la probabilité que p | d(k) est 1/p.")
print("La contrainte D25 (3^k ∈ ⟨2⟩) ajoute un filtre : prob ≈ m/(p-1).")
print("Probabilité combinée que p ≡ 1 mod m, p | d(k), et D25 :")
print("  ≈ (1/m) · (1/p) · m/(p-1) ≈ 1/p² pour p dans la classe 1 mod m.")
print()
print("Somme sur p > m² : Σ_{p ≡ 1 mod m, p > m²} 1/p²")
print("  ≈ (1/m) · Σ_{p > m²} 1/p² ≈ (1/m) · 1/m² = 1/m³ → 0")
print()
print("CONCLUSION HEURISTIQUE : Les primes p | d(k) avec p > m² sont")
print("exponentiellement rares. Le nombre attendu est O(1/m), donc")
print("pour m > 100, on attend << 1 telle prime.")
print()
print("MAIS : ceci est un argument probabiliste, PAS une preuve.")
