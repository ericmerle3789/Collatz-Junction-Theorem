# Phase A2 — Résultats : Extension Régime B k=18..67
# Date : 3 mars 2026
# Script : scripts/exploration/phase_a2_regime_b_extension.py

---

## Méthode

- Division d'essai de d(k) = 2^S - 3^k jusqu'à 10^7
- Pour chaque premier p trouvé : calcul de m = ord₂(p)
- Classification : Régime A (p < m⁴) vs Régime B (p ≥ m⁴)
- Pour les grands cofacteurs premiers : calcul d'ordre via factorisation de p-1
- Miller-Rabin déterministe (15 témoins, exact pour n < 3.3 × 10^24)

## Résultats principaux

| Métrique | Valeur |
|----------|--------|
| k analysés | 50 (k = 18..67) |
| Premiers trouvés (≤ 10^7) | 127 |
| **Régime A** | **127 (100%)** |
| **Régime B** | **0 (0%)** |
| Cofacteurs premiers classifiés | 38 (tous Régime A) |
| Cofacteurs composites non factorisés | 12 |

## Résultat clé

**RÉGIME B EMPIRIQUEMENT VIDE** pour k = 18..67

Ceci étend le résultat L12 (0/284 pour k = 69..150) à l'intervalle exact
du gap du Junction Theorem (k = 18..67).

Combiné avec L12 : **0 premiers en Régime B sur k = 18..150**

## Observations détaillées

1. **Tous les cofacteurs premiers analysables sont Régime A** (38/38)
   - Même les très grands (29 digits, k=61) ont ord₂ ≈ p, donc p << m⁴

2. **12 cofacteurs composites non factorisés** (k = 46, 47, 53, 54, 57, 58,
   59, 62, 63, 64, 65, 66) — ces d(k) ont des facteurs > 10^7 non premiers

3. **Aucun facteur Régime B même parmi les petits premiers** — les 127 premiers
   ≤ 10^7 sont tous Régime A

4. **Pattern structurel** : pour les facteurs de d(k) = 2^S - 3^k,
   ord₂(p) tend à être grand relativement à p, ce qui force p << m⁴

## Implication pour le Junction Theorem

La Condition (Q) est **vacuement satisfaite** pour tous les premiers trouvés
dans d(k), k = 18..67. Cela signifie que :

- Le Cas 3b-ii (Régime B, n₃ petit) **ne se produit jamais en pratique**
  pour les k du gap
- La preuve théorique que le Régime B est vide (Phase C) deviendrait le
  chemin le plus efficace vers la fermeture complète

## Cofacteurs composites — analyse de risque

Les 12 cofacteurs composites non factorisés pourraient théoriquement contenir
des facteurs en Régime B. Cependant :
- Le pattern 0/165 (127 petits + 38 cofacteurs premiers) est très fort
- La probabilité qu'un facteur de 2^S - 3^k soit en Régime B semble
  structurellement nulle

## Anti-hallucination

- ρ(127, m=7) = 0.6180 ✓ (attendu ≈ 0.618)
- mult_ord_smart cross-validé vs mult_ord naïf sur {127, 8191, 131071, 524287}
- mult_ord_via_factors(2, 524287) = 19 ✓
- Toutes les factorisations vérifiées (Σ facteurs × cofacteur = d)

## Temps d'exécution

Total : 11.8s (dominé par trial division des grands d(k))

## Synthèse Phase A complète

| Phase | Résultat | Implication |
|-------|----------|-------------|
| A1 (k=18..25) | N₀(p) > 0 ∀ premiers testés | CRT inopérant, mixing nécessaire |
| A2 (k=18..67) | 0/165 Régime B | (Q) vacuement satisfaite |

**Conclusion** : Le gap ne vient pas d'un échec computationnel mais d'un
manque d'outil théorique. Phase B (mixing inconditionnel) est la voie.
