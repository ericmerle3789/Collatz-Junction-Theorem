# SESSION 9 — NOTES DE TRAVAIL
## Date : 4 mars 2026
## Objectif : Formalisation des Mécanismes I et II

---

## RÉSULTATS PRINCIPAUX

### A. PRIME BLOCKING (Mécanisme I) — FORMALISÉ

#### A1. Preuve complète k=3 (d=5)
- 3 solutions algébriques à 2x + 4y ≡ 4 mod 5
- Toutes 3 ont des positions INCOMPATIBLES avec l'ordre strict
- Preuve terminale pour k=3

#### A2. Reformulation TARGET -1
**Théorème-clé** : N₀(d) = 0 ⟺ -1 ∉ Image(f)
où f(S) = Σ_{j=1}^{k-1} w^j · 2^{sort(S)_j} mod p

- Vérifié pour k=3 (p=5), k=4 (p=47), k=5 (p=13), k=13 (p=502829)
- Pour k=3 et k=5 : -1 est le **SEUL** résidu absent (anti-concentration parfaite)
- Pour k=4 et k=13 (C/p < 1) : 29+ résidus absents, dont -1

#### A3. SANS contrainte d'ordre, -1 APPARAÎT
- k=3 : sans ordre → -1 dans image, avec ordre → -1 absent
- k=4, k=5 : idem
- **Conclusion** : c'est UNIQUEMENT la contrainte d'ordre strict qui bloque

#### A4. Substitution B_j = A_j - j
- u = w·2 mod p, B_j non-décroissant dans [0, S-k]
- Pour k=3 : u = -1 mod 5 → paires qui s'annulent
- σ(u) = Σ u^j ≠ 0 pour tout k testé (NÉCESSAIRE)
- u^k = 2^{k-S} mod p (identité universelle)

#### A5. Distribution et anti-concentration
- k=3, k=5 : distribution PARFAITEMENT uniforme sur {1,...,p-1}
- r=0 a le PLUS de compositions (paradoxe apparent — mais c'est la somme
  complète vs les k-1 derniers termes)

### B. CRT ANTI-CORRÉLATION (Mécanisme II) — FORMALISÉ

#### B1. Matrice CRT
- Pour tout d = p₁·p₂ testé (k=6..11) : M[0][0] = 0
- Les événements "≡0 mod p₁" et "≡0 mod p₂" sont parfaitement anti-corrélés

#### B2. Distribution conditionnelle
- P(r₂=0 | r₁=0) = 0 pour k=6..11 (tous les cas d composite sans 3 facteurs)
- k=12 (d=5×59×1753) : P(r₂=0 | r₁=0) > 0 mais P(r₃=0 | r₁=0 ∧ r₂=0) = 0

#### B3. Mécanisme couplé
- Même sous-ensemble de positions doit satisfaire DEUX congruences simultanément
- Poids w₁^j ≠ w₂^j → directions "orthogonales" dans Z/p₁Z × Z/p₂Z
- Les "bons" sous-ensembles pour p₁ sont "mauvais" pour p₂ (et vice versa)

#### B4. Exclusion bi-directionnelle
- compositions ≡ -1 mod p₁ → target₂ (-1 mod p₂) ABSENT des résidus mod p₂
- compositions ≡ -1 mod p₂ → target₁ (-1 mod p₁) ABSENT des résidus mod p₁
- Exclusion SYMÉTRIQUE

### C. Hybride (Mécanisme III)
- k=7 : N₀(p₂=83) = 0 (prime blocking) + CRT
- k=8 : N₀(p₂=233) = 0 (prime blocking) + CRT
- k=11 : N₀(p₂=7727) = 0 (prime blocking) + CRT
- Beaucoup de cas composites sont en fait HYBRIDES

---

## SCRIPTS CRÉÉS

1. `session9_prime_blocking_formal.py` — 9 investigations (w-structure, k=3 proof, Fourier, etc.)
2. `session9_algebraic_vs_positional.py` — 7 investigations (drift, backward, substitution B_j)
3. `session9c_deep_backward_exclusion.py` — 9 investigations (backward systematic, u=-1, σ≠0)
4. `session9d_target_minus_one.py` — 10 investigations (TARGET -1, sans ordre, DFT, induction)
5. `session9e_crt_anticorrelation.py` — 7 investigations (matrice CRT, conditionnel, couplage)

---

## DIRECTION VERS LA PREUVE

### Pour d premier :
Montrer que la contrainte d'ordre strict, combinée avec la structure
multiplicative de w = 3^{-1} et 2 dans Z/pZ, FORCE l'exclusion de -1
de l'image de f(S) = Σ w^j · 2^{sort(S)_j}.

**Approches** :
- (a) Weighted subset sum à poids rank-dépendants
- (b) Identité de clôture w^k = 2^{-S} comme contrainte
- (c) Sommes exponentielles restreintes (type Weil/Deligne)

### Pour d composite sans blocage premier :
Montrer que les morphismes φ₁ et φ₂ vers Z/p₁Z et Z/p₂Z sont
INCOMPATIBLES au point (-1, -1) sous la contrainte d'ordre.

**Approches** :
- (d) Morphisme produit φ = (φ₁, φ₂) et image dans Z/p₁Z × Z/p₂Z
- (e) Incompatibilité des poids w₁^j ≠ w₂^j
- (f) Corrélation des positions (profile d'utilisation différent)

---

## PISTES FERMÉES
- Induction directe sur k : p change à chaque étape (corpos différents)
- Bounds seules sur corrSum : bornes trop larges pour exclure 0
