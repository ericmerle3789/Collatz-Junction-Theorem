# SYNTHÈSE DE TOUS LES CYCLES JEPA — 18 Mars 2026

## Inventaire des outils prouvés

### A. Pour k=3,4 (d premier, gcd(S,k)=1) : PREUVE ALGÉBRIQUE COMPLÈTE
1. X^S - 3^k irréductible sur Q → K = Q(α) corps de nombres
2. N(P_σ(α)) coprime à d pour TOUT σ
3. d premier → (α-2) idéal premier
4. (α-2) ∤ P_σ(α) → P_σ(2) ≢ 0 mod d → N₀=0. **QED**

### B. Pour k=3,5 : ⟨2,3⟩ contient TOUT corrSum mod d
- Preuve : corrSum mod d ∈ (Z/dZ)* pour d=5,13 (et (Z/dZ)* = ⟨2,3⟩)

### C. Pour k=4,7,8,11 : Valuation blocking
- Un premier p | d a v_p(corrSum) = 0 universellement

### D. Pour TOUT k=3..14 : Fait universel vérifié
- N₀(d) = 0 (exhaustif)
- N₀(d²) = 0 (plus fort)
- d est souvent l'UNIQUE diviseur non atteint de gcd(corrSum, d)

### E. Principe du maximum (universel, prouvé)
- P_σ(α) = max_j |P_σ(α·ζ^j)| (inégalité triangulaire + coeffs positifs)
- Le conjugué réel n'est JAMAIS le minimum

### F. Formule REST' (algébrique, prouvée)
- REST' = Σ ρ^i · 2^{δ_i} où ρ = 2/3 mod d
- corrSum ≡ 0 mod d ⟺ REST' ≡ -1 mod d
- 3ρ = 2 dans Z/dZ (identité fondamentale)

## Ce qui manque pour la preuve universelle

**LE GAP** : aucun des outils ci-dessus ne donne une preuve pour TOUT k ≥ 68.

- A. ne marche que quand N(P_σ) est coprime à d (k=3,4 seulement)
- B. ne marche que quand d est petit (⟨2,3⟩ = (Z/dZ)*)
- C. ne marche que pour certains k (existence d'un premier témoin)
- E. ne donne pas P_σ(α) > d (échoue à k=7)
- F. reformule le problème sans le résoudre

## Pistes restantes non explorées

### 1. Argument de HAUTEUR dans le corps de nombres
P_σ(α) est un entier algébrique de K = Q(α).
Sa hauteur de Weil h(P_σ(α)) ≥ quelque chose.
Si h(P_σ(α)) > h(d), alors d ∤ P_σ(2).
Nécessite : théorie des hauteurs de Silverman/Lang.

### 2. Théorie de Galois du groupe Gal(K/Q)
Pour gcd(S,k)=1 : Gal(K/Q) ≅ Z/SZ agit sur les racines.
P_σ(α) et ses conjugués sont liés par cette action.
Le Frobenius en d agit sur P_σ(α) mod d.
Si on peut montrer que le Frobenius fixe P_σ(α) mod (α-2)
dans une direction incompatible avec 0...

### 3. Argument d'ENTROPIE algébrique
Le nombre d'idéaux premiers dans Z[α] au-dessus de (d)
est relié au degré de décomposition f·g = S.
Pour d premier inerte (g=1, f=S) : (d) reste premier dans Z[α],
et P_σ(α) mod d = P_σ(2) mod d. Alors N(P_σ) ≡ P_σ(2)^S mod d.
Si N(P_σ) ≢ 0 mod d : P_σ(2) ≢ 0 mod d.

### 4. Argument COMBINATOIRE direct
Compter les séquences cumulatives dont corrSum = n·d pour chaque n.
Borner ce nombre par C(S-1,k-1)/d · (1 + erreur).
Si erreur < 1 - C/d : N₀ = 0.

## Priorité recommandée
1. **Piste 3 (inertie)** : si d est inerte dans Z[α], la preuve par la norme
   se simplifie énormément. Vérifier pour quels k c'est le cas.
2. **Piste 1 (hauteurs)** : développer un argument de hauteur.
3. **Piste 4 (combinatoire)** : affiner la borne d'erreur avec la structure géométrique.
