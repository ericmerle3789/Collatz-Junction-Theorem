# R174 — L'ARGUMENT DU POIDS DÉSÉQUILIBRÉ
## Pourquoi g(v) ne peut pas être un multiple de d

**Date :** 15 mars 2026
**Objectif :** Formaliser l'obstruction anti-corrélation comme candidat à une preuve universelle.

---

## 1. SETUP

### Notations

- S = nombre total de pas (= k dans les notations antérieures)
- x = nombre de pas impairs, avec x·log₂3 < S ≤ 2x
- d = 2^S - 3^x > 0
- Positions : 0 ≤ e₀ < e₁ < ... < e_{x-1} ≤ S-1 (positions des 1 dans le vecteur de parité)
- g = Σ_{j=0}^{x-1} 3^{x-1-j} · 2^{e_j}

**Objectif :** Montrer d ∤ g pour tout choix de positions.

### Réécriture de g en base 2

```
g = 3^{x-1}·2^{e₀} + 3^{x-2}·2^{e₁} + ... + 3·2^{e_{x-2}} + 2^{e_{x-1}}
```

Factorisons par 2^{e₀} :

```
g = 2^{e₀} · [3^{x-1} + 3^{x-2}·2^{e₁-e₀} + ... + 2^{e_{x-1}-e₀}]
```

Puisque d est impair (2^S est pair, 3^x est impair), d ∤ 2^{e₀}, donc :
- d | g ⟺ d | g' où g' = g/2^{e₀} = Σ 3^{x-1-j} · 2^{e_j - e₀}

**On peut donc supposer e₀ = 0** sans perte de généralité.

### Gaps

Avec e₀ = 0, définissons les gaps : s_j = e_j - e_{j-1} ≥ 1 pour j=1,...,x-1.
Alors e_j = s₁ + s₂ + ... + s_j, et la contrainte est : e_{x-1} ≤ S-1, i.e., Σ s_j ≤ S-1.

## 2. L'ARGUMENT DE DOMINANCE DU PREMIER TERME

### 2.1 Décomposition en terme dominant + reste

```
g = 3^{x-1} + R    où R = Σ_{j=1}^{x-1} 3^{x-1-j} · 2^{e_j}
```

Le terme dominant est 3^{x-1} (car e₀ = 0).

**Borne sur R :** Chaque terme de R satisfait 3^{x-1-j} · 2^{e_j} ≥ 3^{x-1-j} · 2 (car e_j ≥ j ≥ 1).

Le terme MAXIMAL de R est le dernier : 2^{e_{x-1}} ≤ 2^{S-1}.

**Borne supérieure de R :**
R ≤ 3^{x-2}·2^S + 3^{x-3}·2^S + ... + 2^S < 3^{x-1}·2^S/2 (somme géométrique)

En fait, R < (3^{x-1}-1)/2 · 2^S (borne très lâche).

**Borne inférieure de g :**
g ≥ 3^{x-1} + 3^{x-2}·2 + 3^{x-3}·4 + ... + 2^{x-1}
= Σ_{j=0}^{x-1} 3^{x-1-j}·2^j = (3^x - 2^x)/(3-2) = 3^x - 2^x

**Borne supérieure de g :**
g ≤ 3^{x-1}·2^0 + 3^{x-2}·2^{S-x+1} + ... + 2^{S-1}
= 3^{x-1} + 2^{S-x+1}·Σ_{j=0}^{x-2} (3/2)^{x-2-j}·2^j  ... (complexe)

Approximation : g ≤ 2^{S-1} · (3^x - 1) / (3-1) ≈ 3^x · 2^{S-2}

### 2.2 Multiples de d dans l'intervalle

d = 2^S - 3^x. L'intervalle de g est [3^x - 2^x, ≈3^x · 2^{S-2}].

Nombre de multiples de d dans cet intervalle : ≈ 3^x · 2^{S-2} / d.

Pour S ≈ x·log₂3 + 1 (le cas "serré") : d ≈ 2·3^x - 3^x = 3^x, donc le nombre de multiples est ≈ 2^{S-2} ≈ 3^x/4. BEAUCOUP de multiples de d existent dans l'intervalle.

**Conclusion :** Un argument purement basé sur la TAILLE ne suffit pas. Il faut exploiter la STRUCTURE.

## 3. LA STRUCTURE FINE : L'ANTI-CORRÉLATION COMME CONTRAINTE MOD d

### 3.1 L'écriture mod d

Puisque 2^S ≡ 3^x mod d, on a pour tout entier n :

```
2^S · n ≡ 3^x · n mod d
```

Donc les puissances 2^e avec e ≥ S peuvent être "réduites" :
- 2^S ≡ 3^x mod d
- 2^{S+1} ≡ 2·3^x mod d
- 2^{2S} ≡ 3^{2x} mod d

Mais dans g(v) avec e₀=0, tous les e_j ≤ S-1, donc aucune réduction n'est nécessaire.

### 3.2 L'évaluation de g mod d par étapes

Construisons g terme par terme et suivons le résidu mod d :

**Étape 0 :** r₀ = 3^{x-1} mod d

**Étape j :** r_j = r_{j-1} + 3^{x-1-j}·2^{e_j} mod d

Après x étapes : r_{x-1} = g mod d. On veut montrer r_{x-1} ≠ 0.

### 3.3 L'observation de départ

r₀ = 3^{x-1} mod d. Puisque d = 2^S - 3^x :

```
3^x ≡ 2^S mod d, donc 3^{x-1} ≡ 2^S / 3 mod d
```

Plus précisément : 3·3^{x-1} = 3^x = 2^S - d, donc 3^{x-1} = (2^S - d)/3.

Or d mod 3 = (2^S - 3^x) mod 3 = 2^S mod 3 (car 3^x ≡ 0 mod 3).
- Si S pair : 2^S ≡ 1 mod 3, d ≡ 1 mod 3
- Si S impair : 2^S ≡ 2 mod 3, d ≡ 2 mod 3

Dans les deux cas, 3 ∤ d, donc 3 est inversible mod d.

```
r₀ = 3^{x-1} ≡ (2^S - d)·3^{-1} ≡ 2^S · 3^{-1} mod d    [car d ≡ 0 mod d]
```

Mais 2^S ≡ 3^x mod d, donc r₀ ≡ 3^x · 3^{-1} = 3^{x-1} mod d. (Tautologie, bien sûr.)

### 3.4 Le problème du "parcours dans (Z/dZ)"

La question se reformule : en partant de r₀ = 3^{x-1} mod d et en ajoutant successivement les termes 3^{x-1-j}·2^{e_j} pour j=1,...,x-1, peut-on atteindre 0 mod d ?

Les "pas" disponibles sont : {3^{x-1-j}·2^e : e ∈ {j, j+1, ..., S-1}, e > e_{j-1}}

C'est une MARCHE DÉTERMINISTE dans Z/dZ avec des pas choisis dans un ensemble structuré.

**Question reformulée :** Cette marche peut-elle atteindre -r₀ (= -3^{x-1} mod d) en exactement x-1 pas ?

## 4. L'ARGUMENT DU DÉSÉQUILIBRE 3-ADIQUE LOCAL

### 4.1 L'observation pour les petits premiers p | d

Fixons p | d, premier. L'ordre de 2 modulo p est ord_p(2) = o_p.

Les puissances 2^e mod p cyclent avec période o_p :
```
2^0, 2^1, ..., 2^{o_p - 1}, 2^0, 2^1, ...  (mod p)
```

L'ensemble {2^e mod p : e = 0, ..., S-1} contient TOUTES les puissances 2^0,...,2^{o_p-1} car S ≥ o_p (pour p | d = 2^S - 3^x, on a 2^S ≡ 3^x mod p, donc ord_p(2) | S·gcd(p-1,...)).

En fait, 2^S ≡ 3^x mod p, donc 2^S ≡ 3^x (mod p). L'ensemble des 2^e mod p parcourt un sous-groupe de (Z/pZ)*.

### 4.2 La condition g ≡ 0 mod p

```
Σ_{j=0}^{x-1} 3^{x-1-j} · 2^{e_j} ≡ 0 mod p
```

C'est une COMBINAISON LINÉAIRE (sur F_p) des éléments 2^{e_j} avec coefficients 3^{x-1-j}.

Si 3 est inversible mod p (ce qui est le cas si p ≠ 3, et p | d implique p ∤ 3 car gcd(d, 3) = 1 ou 3) :

```
Σ_{j=0}^{x-1} (3^{-1})^j · 2^{e_j} ≡ 0 mod p    (après division par 3^{x-1})
```

Posons α = 3^{-1} mod p et β_j = 2^{e_j} mod p. La condition est :

```
Σ_{j=0}^{x-1} α^j · β_j ≡ 0 mod p
```

avec β_0 = 1 (car e_0 = 0), et β_j ∈ ⟨2⟩ ⊂ (Z/pZ)* pour j ≥ 1.

### 4.3 L'analogue d'une transformée de Fourier discrète

La somme Σ α^j β_j ressemble à l'évaluation d'un polynôme :

Si on pose P(T) = Σ β_j · T^j, alors la condition est P(α) ≡ 0 mod p.

P est un polynôme de degré x-1 en T, avec coefficients β_j ∈ ⟨2⟩ ⊂ F_p*.

**Observation :** P a x termes (coefficients tous non-nuls), donc P a au plus x-1 racines dans F_p. L'élément α = 3^{-1} est une racine ssi g ≡ 0 mod p.

La PROBABILITÉ (heuristique) que α soit une racine de P est ≈ (x-1)/p (si P était "aléatoire").

Mais P n'est PAS aléatoire : ses coefficients β_j = 2^{e_j} sont dans le sous-groupe ⟨2⟩, et les e_j sont ordonnés.

### 4.4 Le sous-groupe ⟨2⟩ et la structure de P

Si ord_p(2) = o est petit par rapport à p, alors les β_j ne prennent que o valeurs distinctes.

Le polynôme P(T) = Σ β_j T^j avec β_j ∈ {1, 2, 4, ..., 2^{o-1}} mod p.

Le nombre de tels polynômes de degré x-1 est o^x (sans la contrainte d'ordre sur les e_j).

Avec la contrainte e_0 < e_1 < ... < e_{x-1} : le nombre est C(S, x) (choix de x positions parmi S).

**Fraction de ces polynômes ayant α comme racine :** ≈ C(S,x)/p ... heuristiquement.

## 5. LE CANDIDAT-THÉORÈME : L'OBSTRUCTION PAR SOMMES DE PUISSANCES PONDÉRÉES

### 5.1 Formulation précise

**Conjecture (Obstruction par déséquilibre pondéré) :**

Pour tout x ≥ 2, S ∈ (x·log₂3, 2x], et positions e₀ = 0 < e₁ < ... < e_{x-1} ≤ S-1 :

```
Σ_{j=0}^{x-1} 3^{x-1-j} · 2^{e_j} ≢ 0   mod (2^S - 3^x)
```

### 5.2 Reformulation comme inégalité archimédienne

Puisque g > 0 et d > 0, la condition g ≡ 0 mod d est équivalente à g = m·d pour un entier m ≥ 1.

```
g = m·(2^S - 3^x) = m·2^S - m·3^x
```

Réarrangeons :

```
m·2^S = g + m·3^x = Σ 3^{x-1-j}·2^{e_j} + m·3^x
= 3^x·(m + 1/3) + Σ_{j=1}^{x-1} 3^{x-1-j}·2^{e_j}
                     ... (pas très éclairant)
```

Essayons autrement. Si g = m·d :

```
Σ 3^{x-1-j}·2^{e_j} = m·(2^S - 3^x)
```

Le côté gauche est une somme de x termes positifs. Le côté droit est m·d.

**Borne sur m :** m = g/d. Avec g ≥ 3^x - 2^x et d = 2^S - 3^x :

m ≥ (3^x - 2^x)/(2^S - 3^x)

Pour S ≈ x·log₂3 + 1 : d ≈ 3^x, donc m ≥ (3^x - 2^x)/3^x ≈ 1 - (2/3)^x → 1.
Donc m ≥ 1 (ce qu'on savait déjà).

Pour S = 2x : d = 4^x - 3^x, et g ≤ ... ≈ (3/2)^x · 2^{2x-1}, donc m ≤ (3/2)^x · 2^{2x-1} / (4^x - 3^x) → 0. Problème : m < 1 pour S proche de 2x, donc PAS DE SOLUTION pour S = 2x (sauf m=0 i.e. g=0, mais g > 0). ✓

### 5.3 L'inégalité de Baker transformée

De la formule du produit :

```
Σ_{i=1}^{x} log(3 + 1/n_i) = S·log 2
```

Chaque terme satisfait log 3 < log(3+1/n_i) ≤ log 4 = 2·log 2.

Donc : x·log 3 < S·log 2 ≤ 2x·log 2, soit x·log₂3 < S ≤ 2x. ✓

L'EXCÈS au-dessus de x·log 3 est :

```
ε = S·log 2 - x·log 3 = log(2^S/3^x) = log(1 + d/3^x)
```

Pour les nᵢ distincts : chaque log(3+1/nᵢ) - log 3 = log(1 + 1/(3nᵢ)) ≈ 1/(3nᵢ).

Donc : ε ≈ Σ 1/(3nᵢ), soit Σ 1/nᵢ ≈ 3ε = 3·log(1+d/3^x).

**Borne de Baker :** Par la théorie des formes linéaires en logarithmes (Baker 1966, 1975), si Σ bᵢ·log(αᵢ) = 0 avec αᵢ algébriques et bᵢ ∈ Z, alors soit la forme est trivialement nulle, soit |Σ bᵢ log αᵢ| > exp(-C·∏ log H(αᵢ)·log B) où B = max|bᵢ|.

Ici : Σ log(3nᵢ+1) - Σ log nᵢ - S·log 2 = 0 est une forme linéaire en les logarithmes de 2, nᵢ, et 3nᵢ+1.

MAIS les nᵢ sont les INCONNUES, pas des paramètres fixés. Baker s'applique une fois les nᵢ fixés, pour borner la taille de S (ou vice versa). C'est l'approche de Steiner et Simons-de Weger pour borner x.

## 6. SYNTHÈSE : LE PAYSAGE DES OBSTRUCTIONS

```
           Petits nᵢ                    Grands nᵢ
         ←─────────────────────────────────────→

Archimédien :  ███████████████░░░░░░░░░░░░░░░░░
               (forte contrainte)  (faible contrainte)

Réseau premiers : ░░░░░░░░░░░░░░███████████████████
                   (peu de premiers)  (beaucoup de premiers)

Baker/Heights :  ██████████████████████████████████
                 (borne universelle sur x, pas sur les nᵢ individuels)

Produit exact :  ████████████████████████████████████
                 (TOUJOURS impossible — c'est ce qu'on veut prouver)
```

Le "crossover" entre la contrainte archimédienne et la contrainte du réseau de premiers est la zone critique. C'est là que se situe l'éventuel cycle non-trivial (s'il existait).

### Ce qui rend le problème DIFFICILE :

1. L'approche archimédienne seule donne des bornes mais pas d'impossibilité
2. L'approche modulaire seule est PROUVABLEMENT insuffisante (ghost cycles)
3. Les deux ensemble donnent des résultats pour x borné (Simons-de Weger)
4. Pour x ARBITRAIRE, aucune méthode connue ne suffit

### Ce qui reste spécifique à Collatz (et non à un problème générique) :

La STRUCTURE des coefficients (puissances de 3 décroissantes × puissances de 2 croissantes) crée une corrélation NÉGATIVE entre les deux facteurs de chaque terme. Cette anti-corrélation est absente des problèmes génériques de sommes d'exponentielles, et pourrait être l'ingrédient manquant.

## 7. PROCHAINE DIRECTION : L'ESPACE-QUOTIENT

L'idée du changement d'espace (JEPA) : au lieu de travailler dans Z et chercher une divisibilité, travailler dans l'ESPACE QUOTIENT Z[2,3] / (2^S = 3^x).

Dans cet espace, les éléments sont des polynômes en 2 et 3 modulo la relation 2^S = 3^x. La structure multiplicative de cet anneau quotient pourrait rendre la non-annulation de g évidente.

**Question clé pour R175 :** Dans l'anneau Z[α, β]/(α^S - β^x) avec α=2, β=3, l'élément

```
g = β^{x-1} + β^{x-2}·α^{e₁} + ... + α^{e_{x-1}}
```

est-il toujours NON-NUL ? Et si oui, est-il toujours une UNITÉ (i.e., inversible) ?

Si g est une unité dans cet anneau, alors g ne peut pas être divisible par d (qui est un non-unité, étant > 1). Cela donnerait l'impossibilité cherchée.

**C'est la REFORMULATION ALGÉBRIQUE de l'obstruction.** L'espace n'est plus Z, c'est Z[α,β]/(α^S - β^x). Le changement d'espace transforme la question arithmétique (divisibilité) en question algébrique (inversibilité dans un anneau quotient).
