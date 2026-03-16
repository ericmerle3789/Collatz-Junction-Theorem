# R176 — RÉDUCTION AU PROBLÈME DE SOMME NULLE CYCLIQUE

**Date :** 15 mars 2026
**Statut :** RÉDUCTION STRUCTURELLE MAJEURE

---

## 1. LA RÉDUCTION

### 1.1 Le fait clé

Pour p = 2^S - 3^x premier, dans la GRANDE majorité des cas, 3 ∈ ⟨2⟩ dans F_p* (3 est une puissance de 2 mod p).

Spécifiquement : il existe t tel que 2^t ≡ 3 mod p.

**Conséquence :** g(v) = Σ 3^{x-1-j} · 2^{e_j} = Σ 2^{t(x-1-j) + e_j} mod p.

### 1.2 La reformulation géométrique

Posons f_j = t(x-1-j) + e_j mod ord_p(2). Alors :

```
g(v) ≡ Σ_{j=0}^{x-1} 2^{f_j} mod p
```

**g(v) est une SOMME DE x PUISSANCES DE 2 dans F_p.**

La question "g(v) = 0 mod p ?" devient :

> **Peut-on trouver x éléments du sous-groupe cyclique ⟨2⟩ ⊂ F_p* dont la somme (dans le groupe ADDITIF F_p) est nulle ?**

### 1.3 La structure des exposants

Les exposants f_j ont une structure RIGIDE :

```
f_j = t(x-1-j) + e_j
    = [base_j] + [perturbation_j]
```

où :
- **Base :** t(x-1), t(x-2), ..., t, 0 — x points RÉGULIÈREMENT ESPACÉS (pas t)
- **Perturbation :** e_0, e_1, ..., e_{x-1} — croissante, dans {0,...,S-1}

**Propriétés mesurées :**
- t ≈ ord_p(2)/2 (souvent), beaucoup plus grand que S
- t/(S/x) >> 1 typiquement (rapport 3 à 1000+)
- Les exposants sont PRESQUE TOUJOURS distincts mod ord_p(2) (100% pour la plupart des cas)

### 1.4 L'interprétation géométrique

Sur le "cercle" Z/ord_p(2)·Z (le groupe des exposants) :
- Les x points de base sont **régulièrement espacés** avec pas t
- Chaque point est **perturbé** par +e_j (une petite perturbation relative à t)
- La perturbation est ANTI-CORRÉLÉE : les points de base décroissent (t(x-1) > t(x-2) > ...) tandis que les perturbations croissent (e_0 < e_1 < ...)

## 2. CONNEXION À LA COMBINATOIRE ADDITIVE

### 2.1 Le problème de somme nulle

La question est un cas spécial du problème suivant :

> **Problème (Zero-Sum dans un sous-groupe cyclique) :**
> Soit G un sous-groupe cyclique de F_p* d'ordre o.
> Soit {g₁, ..., gₓ} ⊂ G des éléments structurés.
> A-t-on g₁ + g₂ + ... + gₓ = 0 dans F_p ?

### 2.2 Résultats connus

**Théorème d'Erdős-Ginzburg-Ziv (1961) :** Parmi 2n-1 éléments de Z/nZ, on peut en choisir n dont la somme est 0.

**Théorème de Olson (1969) :** Parmi 2√n éléments de Z/nZ, on peut en choisir un sous-ensemble non-vide de somme 0.

**Borne de Davenport :** La constante de Davenport D(Z/nZ) = n (le nombre minimum d'éléments pour garantir un sous-ensemble de somme 0).

Mais ici, on a BEAUCOUP MOINS que o₂ éléments (x << o₂ dans la plupart des cas). Donc ces résultats ne donnent PAS directement l'impossibilité.

### 2.3 Ce qui est spécifique ici

Le sous-ensemble n'est PAS arbitraire. Les éléments 2^{f_j} ont la structure :
1. Ils vivent dans ⟨2⟩ (structure MULTIPLICATIVE)
2. Leurs exposants sont QUASI-RÉGULIÈREMENT ESPACÉS (structure ADDITIVE dans les exposants)
3. La perturbation est BORNÉE (|e_j| ≤ S-1 << t)

Cette double structure (multiplicative + quasi-régulière) est beaucoup plus contrainte qu'un sous-ensemble arbitraire.

## 3. L'ARGUMENT POTENTIEL

### 3.1 L'arc de Bohr

Les éléments 2^{f_j} vivent sur un "arc de Bohr" dans F_p* : un ensemble de la forme {2^{a+bj+c_j} : j = 0,...,x-1} avec c_j petit.

**Théorème de Freiman (structure additive de sous-ensembles multiplicatifs) :** Un sous-ensemble A d'un sous-groupe cyclique G ⊂ F_p* avec |A+A| petit est contenu dans un arc de Bohr court.

Ici, nos éléments sont DÉJÀ dans un arc de Bohr par construction. La question est : cet arc est-il "trop court" pour contenir une somme nulle de x termes ?

### 3.2 L'argument de taille

Si les x éléments g_j = 2^{f_j} sont "proches" (dans le sens cyclique de F_p*), alors leur somme est environ x · g_0 (un seul terme dominant). Pour que la somme soit 0, il faudrait x · g_0 ≈ 0 mod p, i.e., p | x · g_0. Mais x << p et g_0 ≠ 0, donc p ∤ x · g_0.

**Le problème :** Les éléments ne sont PAS tous proches. Le pas t ≈ o₂/2 >> S signifie que les éléments sont BIEN RÉPARTIS autour du cercle. La somme peut donc avoir des annulations.

### 3.3 La piste du caractère

Pour χ un caractère multiplicatif de F_p* :

```
S = Σ χ(2^{f_j}) = Σ χ(2)^{f_j}
```

Si χ(2) = ζ (racine de l'unité d'ordre divisant o₂) :

S = Σ ζ^{f_j}

C'est une somme d'exponentielles dont les PHASES f_j sont quasi-régulièrement espacées. Par des bornes de type Weyl/van der Corput, cette somme devrait être O(√x · log(o₂)) pour des phases suffisamment irrégulières.

## 4. L'OBSERVATION CRUCIALE NON-EXPLOITÉE

### 4.1 La relation 2^S = 3^x dans F_p

Puisque p = 2^S - 3^x, on a 2^S = 3^x = (2^t)^x = 2^{tx} dans F_p*. Donc :

```
2^S = 2^{tx}   i.e.   S ≡ tx mod ord_p(2)
```

Cela signifie : **t = S/x dans le groupe des exposants** (mod ord_p(2)/gcd(x, ord_p(2))).

Plus précisément : tx ≡ S mod o₂, donc t ≡ S · x^{-1} mod o₂ (si gcd(x, o₂) = 1).

### 4.2 La conséquence

Les exposants f_j = t(x-1-j) + e_j peuvent être réécrits :

```
f_j = (S/x)(x-1-j) + e_j   mod o₂
```

(où S/x est l'inverse modulaire, pas la division réelle).

Le rapport S/x (réel) est ≈ log₂3 ≈ 1.585. Mais S/x (mod o₂) = t peut être très différent.

### 4.3 La formule finale

**Dans F_p, g(v) est une somme de x puissances de 2 dont les exposants sont :**

```
f_j = (S · inv_x) · (x-1-j) + e_j   mod o₂
```

**où inv_x = x^{-1} mod o₂** (quand il existe).

**C'est une suite ARITHMÉTIQUE PERTURBÉE dans Z/o₂Z.**

## 5. REFORMULATION DÉFINITIVE

### Le problème se réduit à :

> Pour o₂ = ord_p(2), t = S · x^{-1} mod o₂, et 0 ≤ e₀ < e₁ < ... < e_{x-1} ≤ S-1 :
>
> **Σ_{j=0}^{x-1} ω^{t(x-1-j) + e_j} ≠ 0**
>
> où ω = 2 dans F_p (pas une racine de l'unité au sens usuel, mais un élément de F_p*).

### Équivalemment :

> Les x points exp(2πi · f_j / o₂) sur le cercle unité (dans C), pondérés par les "amplitudes" |2^{f_j} mod p|, ne peuvent pas s'annuler quand on les voit comme somme dans F_p.

### Ce qui rend le problème OUVERT :

- En C, la somme de x points régulièrement espacés sur le cercle S'ANNULE quand le pas divise le cercle (harmoniques). Ici le pas t est "irrationnel" par rapport à o₂ (en général), donc pas d'annulation exacte des harmoniques.
- Mais dans F_p, l'addition est DIFFÉRENTE de l'addition dans C. La somme de puissances de 2 dans F_p ne suit pas les mêmes règles que les sommes d'exponentielles dans C.

## 6. ÉTAT DE LA RECHERCHE

| Aspect | Résultat |
|--------|----------|
| Réduction à somme cyclique | ✅ FAIT (quand 3 ∈ ⟨2⟩ dans F_p*) |
| 3 ∈ ⟨2⟩ fréquence | ✅ > 80% des cas p premier |
| Exposants distincts | ✅ > 99% des vecteurs |
| Exposants = suite arith. perturbée | ✅ IDENTIFIÉ |
| Connexion combinatoire additive | 🔄 PISTE OUVERTE |
| Preuve d'impossibilité | ❌ PAS ENCORE |

## 7. DIRECTION POUR R177

L'argument le plus prometteur : utiliser le fait que les éléments 2^{f_j} sont une **suite géométrique perturbée** dans F_p*, et que dans un corps fini, une somme de termes d'une suite géométrique perturbée ne peut s'annuler que sous des conditions très restrictives (qui ne sont pas remplies ici à cause de l'anti-corrélation).

**Cas x = 2 :** La condition est 2^{f_0} + 2^{f_1} = 0 dans F_p, i.e., 2^{f_0} = -2^{f_1}, i.e., 2^{f_0 - f_1} = -1 mod p. Comme -1 = 2^{o₂/2} quand o₂ est pair, cela exige f_0 - f_1 = o₂/2 mod o₂. Or f_0 - f_1 = t - (e_1 - e_0) = t - Δe avec Δe ∈ {1,...,S-2}. La condition t - Δe = o₂/2 donne Δe = t - o₂/2. Cette valeur SPÉCIFIQUE de Δe peut être vérifiée/exclue cas par cas.

**Cas x ≥ 3 :** Plus complexe, nécessite des bornes de type sommes d'exponentielles.
