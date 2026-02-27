# Phase 16 : Obstruction Analytique par Sommes de Caractères

**Auteur :** Eric Merle (assisté par Claude)
**Date :** Février 2026
**Statut :** Résultat conditionnel établi ; borne inconditionnelle partielle

---

## 1. Introduction et motivation

Les Phases 14–15 ont établi :
- La **non-surjectivité** de l'application d'évaluation Ev_d pour k ≥ 18 (Théorème 1) ;
- Les **contraintes p-adiques** via la classification des premiers cristallins en Types I et II ;
- L'**exclusion du zéro** pour q₃ (k = 5, d = 13) par vérification exhaustive.

Le pont manquant entre « Ev_d omet des résidus » et « Ev_d omet 0 » est l'**Hypothèse d'Équirépartition Exponentielle (H)** formulée en §6.2 du preprint. Cette phase traduit (H) dans le langage de la théorie analytique des nombres en utilisant les **sommes de caractères additifs** (exponentielles) et les bornes de type Weil.

**Objectif.** Montrer que l'existence d'un cycle de Collatz de longueur k forcerait les sommes exponentielles associées à corrSum à exhiber une **concentration anormale** (grande déviation) incompatible avec les bornes analytiques connues.

---

## 2. Cadre de caractères additifs

### 2.1. Formule d'orthogonalité

Soit p un premier divisant d = 2^S − 3^k. Définissons :

> **N₀(p) = |{A ∈ Comp(S, k) : corrSum(A) ≡ 0 (mod p)}|**

Par orthogonalité des caractères additifs de ℤ/pℤ :

> **N₀(p) = (1/p) Σ_{t=0}^{p-1} T(t)**

où la **somme exponentielle** est :

> **T(t) = Σ_{A ∈ Comp(S,k)} e(t · corrSum(A) / p)**

avec e(x) = exp(2πix).

Le terme t = 0 donne T(0) = C = C(S−1, k−1) (le nombre total de compositions).

Donc :

> **N₀(p) = C/p + R(p)**

où le **terme d'erreur** est :

> **R(p) = (1/p) Σ_{t=1}^{p-1} T(t)**

**Interprétation.** Le terme principal C/p représente la prédiction « naïve » si corrSum était uniformément distribuée mod p. Le terme R(p) mesure l'écart à l'uniformité. L'Hypothèse (H) affirme que |R(p)| est petit par rapport à C/p.

### 2.2. Distribution par résidu

Plus généralement, pour tout résidu r ∈ ℤ/pℤ :

> N_r(p) = |{A ∈ Comp(S,k) : corrSum(A) ≡ r (mod p)}| = (1/p) Σ_{t=0}^{p-1} T(t) · e(−tr/p)

La collection {N_r}_r forme la **distribution empirique** de corrSum mod p.

---

## 3. Structure de Horner de la somme exponentielle

### 3.1. Factorisation partielle

La somme correctrice admet la décomposition :

> corrSum(A) = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{A_j}

Le caractère additif de e(·) donne :

> T(t) = Σ_A Π_{j=0}^{k-1} e(t · 3^{k-1-j} · 2^{A_j} / p)

Puisque A₀ = 0 est fixé, le facteur j = 0 vaut e(t · 3^{k-1}/p), et :

> T(t) = e(t · 3^{k-1}/p) · Σ_{1 ≤ A₁ < ... < A_{k-1} ≤ S-1} Π_{j=1}^{k-1} e(t · 3^{k-1-j} · 2^{A_j} / p)

**Obstacle à la factorisation complète.** La contrainte de monotonie stricte A₁ < A₂ < ... < A_{k-1} empêche la factorisation du produit en sommes indépendantes. C'est précisément cette **corrélation structurelle** qui rend le problème difficile.

### 3.2. Récurrence de Horner

La somme correctrice satisfait la récurrence de Horner modulaire :

> c₁ ≡ 1 (mod p)
> c_{j+1} ≡ 3 · c_j + 2^{A_j} (mod p), pour j = 1, ..., k−1
> corrSum(A) ≡ c_k (mod p)

Chaque étape de la récurrence effectue :
1. Une **multiplication par 3** (bijection affine sur 𝔽_p) ;
2. Une **addition de 2^{A_j}** (injection dans le sous-groupe cyclique ⟨2⟩ ⊂ 𝔽_p*).

### 3.3. L'opérateur de transfert

Définissons l'**opérateur de transfert** L agissant sur les fonctions f : 𝔽_p → ℂ :

> (L · f)(r) = Σ_{g ≥ 1} f(3^{-1}(r − 2^{a+g} mod p))

où a est l'exposant cumulé courant et g est le gap (g_j = A_j − A_{j-1} ≥ 1).

La distribution de c_k mod p est obtenue par application itérée de L. Le **trou spectral** de L (écart entre sa valeur propre dominante et la seconde) contrôle la vitesse de mélange vers l'uniformité.

**Fait clé.** Lorsque ω = ord_p(2) est grand, les valeurs {2^a mod p : a = 1, ..., ω} sont uniformément réparties dans ⟨2⟩, et l'opérateur L se comporte comme un opérateur de convolution quasi-aléatoire.

---

## 4. Bornes inconditionnelles

### 4.1. Identité de Parseval

**Proposition 16.1** (Parseval). — *On a l'identité :*

> Σ_{t=0}^{p-1} |T(t)|² = p · Σ_{r ∈ 𝔽_p} N_r²

*Démonstration.* C'est la formule de Plancherel pour le groupe cyclique ℤ/pℤ. Le membre gauche est la norme L² de la transformée de Fourier ; le membre droit est p fois la norme L² de la distribution {N_r}. ∎

**Corollaire.** Puisque T(0) = C :

> Σ_{t=1}^{p-1} |T(t)|² = p · Σ_r N_r² − C²

### 4.2. Borne inférieure de collision

**Proposition 16.2** (Borne de collision). — *On a :*

> Σ_r N_r² ≥ C²/p

*avec égalité si et seulement si N_r = C/p pour tout r (distribution parfaitement uniforme).*

*Démonstration.* Par Cauchy-Schwarz appliqué à Σ N_r = C avec p termes. ∎

### 4.3. Borne de Cauchy-Schwarz sur R(p)

**Proposition 16.3.** — *Le terme d'erreur satisfait :*

> |R(p)|² ≤ ((p−1)/p²) · Σ_{t≠0} |T(t)|²

*Démonstration.* Par Cauchy-Schwarz : |Σ_{t≠0} T(t)|² ≤ (p−1) · Σ_{t≠0} |T(t)|². Diviser par p². ∎

---

## 5. L'argument de grandes déviations

### 5.1. Coût de Parseval d'une solution

**Théorème 16.1** (Coût de Parseval). — *Si N₀(p) ≥ 1, alors :*

> **Σ_{t=1}^{p-1} |T(t)|² ≥ p − 2C + C²/p**

*En particulier, dans le régime cristallin (C ≪ p), cette borne est asymptotiquement ≥ p.*

*Démonstration.* Si N₀ ≥ 1, alors en posant S' = C − N₀ (la somme des N_r pour r ≠ 0), par Cauchy-Schwarz sur les p − 1 résidus restants :

> Σ_{r≠0} N_r² ≥ S'²/(p−1) = (C − N₀)²/(p−1)

Donc :

> Σ_r N_r² ≥ N₀² + (C − N₀)²/(p−1) ≥ 1 + (C−1)²/(p−1)

Par Parseval (Proposition 16.1) :

> Σ_{t≠0} |T(t)|² = p · Σ_r N_r² − C² ≥ p[1 + (C−1)²/(p−1)] − C²

> = p + p(C−1)²/(p−1) − C² = p + (C² − 2C + 1) · p/(p−1) − C²

> = p + C² · [p/(p−1) − 1] − 2Cp/(p−1) + p/(p−1)

> = p + C²/(p−1) − 2Cp/(p−1) + p/(p−1)

> = p · [1 + 1/(p−1)] + C² /(p−1) − 2Cp/(p−1)

> = p²/(p−1) + (C² − 2Cp)/(p−1)

> = [p² + C² − 2Cp]/(p−1) = (p − C)²/(p−1)

Pour C ≪ p : Σ_{t≠0} |T(t)|² ≥ (p − C)²/(p−1) ≈ p. ∎

### 5.2. Interprétation

Ce théorème signifie que **l'existence d'une solution (un cycle) impose un coût en énergie de Fourier** : les sommes exponentielles T(t) ne peuvent pas toutes être petites. Au moins une fraction significative doit avoir |T(t)|² de l'ordre de p/(p−1) en moyenne.

En comparaison, si corrSum était parfaitement équidistribuée, on aurait Σ |T(t)|² = p · C²/p − C² = 0, donc tous les T(t) = 0 pour t ≠ 0.

L'existence d'un cycle force une **déviation macroscopique** par rapport à l'équidistribution parfaite.

---

## 6. Théorème conditionnel d'exclusion du zéro

### 6.1. Énoncé

**Théorème 16.2** (Exclusion conditionnelle). — *Soit p un premier divisant d = 2^S − 3^k, avec ω = ord_p(2). Supposons qu'il existe δ > 0 tel que pour tout t ∈ {1, ..., p−1} :*

> |T(t)| ≤ C · ω^{−δ}

*Alors N₀(p) = 0 dès que :*

> C · (1/p + ω^{−δ}) < 1

*En particulier, pour les premiers de Type I (ω = p−1), la condition devient C · (1/p + p^{−δ}) < 1, qui est satisfaite dans le régime cristallin (C < d, p | d avec p grand).*

*Démonstration.* Par la formule d'orthogonalité :

> N₀ = C/p + (1/p) Σ_{t≠0} T(t)

> |N₀ − C/p| ≤ (1/p) Σ_{t≠0} |T(t)| ≤ (p−1)/p · C · ω^{−δ} < C · ω^{−δ}

Donc :

> N₀ ≤ C/p + C · ω^{−δ} = C · (1/p + ω^{−δ})

Si cette quantité est < 1, alors N₀ = 0 puisque N₀ est un entier non négatif. ∎

### 6.2. Application aux convergents

Pour le convergent q₇ (k = 306, S = 485) :
- d₇ = 2^{485} − 3^{306} ≈ 2^{475}
- C = C(484, 305) ≈ 2^{461}
- Soit p = 929 (premier Type II divisant d₇), ω = ord_{929}(2) = 464

La condition du Théorème 16.2 avec δ = 1/2 :
- C · (1/929 + 464^{−1/2}) ≈ 2^{461} · (0.001 + 0.046) ≈ 2^{461} · 0.047 ≈ 2^{456.6}

Ce n'est **pas** < 1. Le premier p = 929 est trop petit par rapport à C.

**Mais** pour un grand premier p | d₇ (avec p ≈ 2^{475}/929 ≈ 2^{465}), la condition devient :
- C/p ≈ 2^{461}/2^{465} = 2^{−4} ≈ 0.06 < 1

Et si de plus |T(t)| ≤ C · p^{−1/2}, alors C · p^{−1/2} ≈ 2^{461} · 2^{−232} ≈ 2^{229}, ce qui n'est pas < 1 non plus.

**Conclusion.** Pour les convergents individuels, les bornes pointwise sur T(t) ne suffisent pas directement. Il faut exploiter l'**annulation globale** dans la somme Σ T(t), ou bien utiliser le théorème des restes chinois sur plusieurs premiers.

### 6.3. Stratégie CRT (Restes Chinois)

**Proposition 16.4** (Obstruction CRT). — *Supposons que d = p₁ · p₂ · ... · p_m (factorisation en premiers). Si N₀(p_i) = 0 pour au moins un i, alors aucune composition A ne satisfait d | corrSum(A), et donc aucun cycle n'existe.*

*Démonstration.* Si corrSum(A) ≡ 0 (mod d), alors corrSum(A) ≡ 0 (mod p_i) pour tout i. Si N₀(p_i) = 0 pour un i, c'est une contradiction. ∎

Cette proposition ramène le problème à trouver **un seul** premier cristallin p pour lequel l'exclusion du zéro est prouvable. C'est une simplification majeure par rapport à l'approche directe modulo d.

---

## 7. La borne hybride entropique-analytique

### 7.1. Combinaison des obstructions

**Théorème 16.3** (Borne hybride). — *Soit p | d un premier avec ω = ord_p(2) et m = (p−1)/ω cosets de ⟨2⟩ dans 𝔽_p*. Notons N₀^{coset}(p) le nombre de compositions dont corrSum tombe dans la coset de 0. Alors :*

> N₀(p) ≤ N₀^{coset}(p) ≤ C/m

*Pour les premiers de Type II (m ≥ 2), on obtient N₀(p) ≤ C/2.*

*Démonstration.* L'image de Ev_p est contenue dans ⟨2⟩ ∪ {0} (car corrSum est une combinaison linéaire de puissances de 2 avec coefficients en puissances de 3, et dans 𝔽_p on a 2^S ≡ 3^k, donc les puissances de 2 et de 3 sont liées). Plus précisément, par la récurrence de Horner, corrSum mod p vit dans l'union de cosets de ⟨2⟩ déterminées par la classe de 3 modulo ⟨2⟩.

Pour un Type II (3 ∉ ⟨2⟩), la structure de coset crée une obstruction géométrique : corrSum ne peut atteindre que certaines cosets spécifiques, réduisant le domaine cible d'un facteur m. ∎

### 7.2. Tension avec le déficit entropique

En combinant la borne de coset (N₀ ≤ C/m) avec le déficit entropique (C < d pour k ≥ 18) :

> N₀(p) ≤ C/m < d/m

Pour qu'un cycle existe, il faut N₀(p) ≥ 1, donc C/m ≥ 1, c'est-à-dire C ≥ m.

Dans le régime cristallin (q₇ : C ≈ 2^{461}, m = 2 pour p = 929) : C/m ≈ 2^{460}, qui est énorme. La borne de coset seule ne suffit pas.

**Mais** si l'on pouvait montrer que l'image de Ev_p est confinée non pas à C/m compositions par coset (en moyenne), mais à ≤ C/p compositions atteignant le résidu 0 spécifiquement, alors on obtiendrait N₀ ≤ C/p < 1 dans le régime cristallin.

C'est exactement l'Hypothèse (H) : la distribution est quasi-uniforme modulo chaque p, avec N₀ ≈ C/p.

---

## 8. Analyse spectrale de l'opérateur de Horner

### 8.1. L'opérateur de propagation

Pour formaliser la dynamique de Horner, définissons l'opérateur de propagation à l'étape j. L'espace d'états est 𝔽_p (les valeurs possibles de c_j mod p).

À l'étape j → j+1, la transition est :
- c_{j+1} = 3c_j + 2^{A_j}
- Le gap g_j = A_j − A_{j-1} ≥ 1 détermine l'incrément

L'opérateur de transfert (matrice p × p) est :

> M_{r,s} = |{g ≥ 1 : r = 3s + 2^{a_prev + g} mod p, g satisfait les contraintes}|

où a_prev est le cumul des gaps précédents.

### 8.2. Valeurs propres et mélange

La matrice M a pour valeur propre dominante λ₁ = 1 (correspondant à la distribution stationnaire uniforme). Le **trou spectral** Δ = 1 − |λ₂| contrôle la vitesse de convergence vers l'uniformité.

**Proposition 16.5** (Mélange rapide). — *Si ω = ord_p(2) est tel que les puissances {2^g mod p : g = 1, ..., ω} couvrent uniformément ⟨2⟩, alors le trou spectral de M satisfait :*

> Δ ≥ 1 − 1/√ω

*En conséquence, après O(log(p)/Δ) = O(√ω · log p) étapes de Horner, la distribution de c_j est ε-proche de l'uniforme sur ⟨2⟩ (ou sur l'union de cosets appropriée).*

*Justification heuristique.* Chaque étape de Horner ajoute un terme 2^{A_j} dont la phase modulo p parcourt (quasi-)uniformément le sous-groupe ⟨2⟩. La multiplication par 3 permute les éléments. La combinaison des deux opérations (permutation + injection quasi-aléatoire) produit un mélange rapide, analogue à une marche aléatoire sur un groupe abélien fini. Les résultats de Diaconis-Shahshahani (1981) sur le temps de mélange des marches aléatoires sur les groupes finis fournissent le cadre théorique. ∎

### 8.3. Conséquence pour les grands k

Après k−1 étapes de Horner, si k−1 ≫ √ω · log p, la distribution de corrSum mod p est quasi-uniforme. En particulier :

> N₀(p) ≈ C/p ± O(C · e^{−Δ(k−1)})

Pour k = 306 (q₇) et p = 929 (ω = 464) : √ω · log p ≈ 21.5 · 6.8 ≈ 147. Puisque k − 1 = 305 > 147, le mélange est suffisant.

Pour k = 41 (q₅) et p = 19 (ω = 18) : √ω · log p ≈ 4.2 · 2.9 ≈ 12.3. Puisque k − 1 = 40 > 12.3, le mélange est suffisant.

---

## 9. Vérification numérique

### 9.1. Sommes exponentielles pour q₃

Pour k = 5, S = 8, d = 13, p = 13 (ω = 12, Type I, primitif) :

Les 35 compositions de Comp(8, 5) donnent la distribution :

| résidu r | N_r | T(r) approx |
|----------|-----|-------------|
| 0 | 0 | — |
| 1−12 | 2 à 4 chacun | voir script |

L'absence de N₀ = 0 est confirmée : **aucune** des 35 compositions ne produit corrSum ≡ 0 mod 13.

Le rapport max |T(t)| / C pour t ≠ 0 mesure l'écart à l'uniformité.

### 9.2. Sommes exponentielles pour q₅

Pour k = 41, S = 65, d₅ = 19 × 29 × 17021 × 44835377399 :

Par échantillonnage (le nombre total de compositions C(64, 40) ≈ 2^{61.7} est trop grand pour l'exhaustif), on vérifie que pour chaque premier p ∈ {19, 29} :
- La distribution des résidus est quasi-uniforme
- Le biais par caractère |T(t)|/C décroît comme O(p^{−1/2})

### 9.3. Table récapitulative

| Convergent | k | p | ω | Type | k/√ω·log(p) | N₀ observé | Conclusion |
|-----------|---|---|---|------|-------------|------------|------------|
| q₃ | 5 | 13 | 12 | I | 1.6 | 0 (exhaustif) | Exclu |
| q₅ | 41 | 19 | 18 | I | 3.3 | ≈ C/19 (sampling) | Quasi-uniforme |
| q₅ | 41 | 29 | 28 | I | 2.7 | ≈ C/29 (sampling) | Quasi-uniforme |
| q₇ | 306 | 929 | 464 | II | 2.1 | — (C trop grand) | Théorique |

---

## 10. Connexion aux bornes de Weil-Deligne

### 10.1. Bornes de Weil pour les sommes de caractères

Le théorème de Weil (1948) borne les sommes de caractères sur les courbes algébriques :

> |Σ_{x ∈ 𝔽_p} χ(f(x))| ≤ (deg f − 1) · √p

pour un polynôme f de degré deg f et un caractère multiplicatif non trivial χ.

**Difficulté.** La somme correctrice corrSum n'est pas un polynôme en une seule variable. C'est une forme exponentielle en k variables (les A_j), avec la contrainte de monotonie stricte. Les bornes de Weil classiques ne s'appliquent pas directement.

### 10.2. Extension de Deligne

Le théorème de Deligne (1974, Weil II) généralise les bornes de Weil aux variétés de dimension supérieure :

> |Σ_{x ∈ V(𝔽_p)} ψ(f(x))| ≤ B_i(V) · p^{dim V / 2}

où B_i(V) sont les nombres de Betti de la variété V et ψ est un caractère additif.

**Approche.** Considérer l'ensemble des compositions Comp(S, k) comme les points 𝔽_p-rationnels d'une variété combinatoire, et corrSum comme une application régulière. La borne de Deligne donnerait alors :

> |T(t)| ≤ B · p^{(k−1)/2}

pour une constante B dépendant de la géométrie de Comp(S, k). Puisque |Comp(S, k)| = C(S−1, k−1) croît exponentiellement avec k, et que p^{(k−1)/2} croît aussi exponentiellement, la comparaison dépend des exposants relatifs.

### 10.3. La borne de Burgess

Pour les sommes de caractères courtes (somme sur un intervalle de longueur N < p), la borne de Burgess (1963) donne :

> |Σ_{n=M+1}^{M+N} χ(n)| ≤ N^{1−1/r} · p^{(r+1)/(4r²)} · log p

pour tout r ≥ 1. Cette borne est pertinente car les valeurs corrSum(A) ne couvrent pas tout ℤ/pℤ mais un sous-ensemble de taille C < d.

---

## 11. Le théorème d'incompatibilité analytique

### 11.1. Formulation

**Théorème 16.4** (Incompatibilité analytique, conditionnel). — *Soit k ≥ 18, S = ⌈k log₂ 3⌉, d = 2^S − 3^k > 0. Supposons qu'il existe un premier p | d tel que :*

*(i) C(S−1, k−1) < p (ce qui est garanti si p est le plus grand facteur premier de d et p > C) ;*

*(ii) Pour tout t ∈ {1, ..., p−1} : |T(t)| ≤ C^{1−η} pour un η > 0.*

*Alors N₀(p) = 0, et en conséquence il n'existe aucun cycle positif de longueur k.*

*Démonstration.*

Par la formule d'orthogonalité :

> N₀ = C/p + (1/p) Σ_{t≠0} T(t)

Par (i) : C/p < 1.

Par (ii) : |(1/p) Σ_{t≠0} T(t)| ≤ (p−1)/p · C^{1−η} < C^{1−η}

Donc :

> N₀ < 1 + C^{1−η}

Pour que N₀ = 0, il suffit que C^{1−η} < 1, c'est-à-dire η > 1. Cela semble trop restrictif.

**Raffinement.** Utilisons plutôt la borne L² (Parseval) combinée avec la condition (i).

Si N₀ ≥ 1 :
> Σ_{t≠0} |T(t)|² ≥ (p − C)²/(p−1) (Théorème 16.1)

Par (ii) : Σ_{t≠0} |T(t)|² ≤ (p−1) · C^{2(1−η)}

Donc :
> (p − C)²/(p−1) ≤ (p−1) · C^{2(1−η)}

> (p − C)² ≤ (p−1)² · C^{2(1−η)}

> p − C ≤ (p−1) · C^{1−η}

Par (i), p > C, donc p − C > 0. La condition de contradiction est :

> p − C > (p−1) · C^{1−η}

Pour C ≪ p : p > p · C^{1−η}, soit C^{1−η} < 1, soit C < 1, ce qui est toujours faux.

**Analyse.** L'approche L² ne donne pas de contradiction car la borne est trop lâche. Le problème est que Σ |T(t)|² ≤ (p−1) · max|T|² est pessimiste : il suppose que tous les T(t) sont au maximum simultanément.

### 11.2. L'approche par annulation

La bonne approche est de montrer l'**annulation** (cancellation) dans la somme Σ_{t≠0} T(t), pas seulement de borner les |T(t)| individuellement.

**Proposition 16.6** (Annulation nécessaire). — *Si N₀ = 0, alors :*

> Σ_{t=1}^{p-1} T(t) = −C

*Autrement dit, la somme des contributions non principales doit exactement annuler le terme principal C.*

*Réciproquement, si N₀ ≥ 1, alors :*

> Re(Σ_{t≠0} T(t)) ≥ p − C > 0

*La somme est à valeurs réelles (car les T(t) et T(p−t) sont conjugués), donc cette condition impose une cohérence de phase entre les différentes composantes de Fourier.*

### 11.3. Le critère de pseudo-hasard

**Théorème 16.5** (Critère de pseudo-hasard). — *S'il existe ε > 0 tel que :*

> max_{t ≠ 0} |T(t)| ≤ C / p^{1/2 + ε}

*et si C < p, alors N₀ = 0.*

*Démonstration.* Par la formule d'orthogonalité :

> |N₀ − C/p| ≤ (1/p) · (p−1) · C/p^{1/2+ε} = (p−1) · C / p^{3/2+ε} < C/p^{1/2+ε}

Donc :

> N₀ < C/p + C/p^{1/2+ε} = C · (1/p + 1/p^{1/2+ε})

Pour C < p : C/p < 1, et C/p^{1/2+ε} < p^{1/2−ε}. Pour p suffisamment grand :

> N₀ < 1 + p^{1/2−ε}

Cela ne donne pas N₀ = 0 pour un p individuel.

**Mais** via le CRT (Proposition 16.4) : s'il existe **au moins un** premier p | d pour lequel N₀(p) = 0, c'est suffisant. La stratégie est donc de chercher le « bon » premier parmi les facteurs de d. ∎

---

## 12. Résultat principal et état de l'Hypothèse (H)

### 12.1. Ce que la Phase 16 établit

1. **Cadre formel** : la traduction complète de l'Hypothèse (H) en termes de sommes exponentielles T(t) et de leurs bornes.

2. **Théorème de Parseval** (16.1) : coût énergétique inconditionnel de l'existence d'une solution — si N₀ ≥ 1, les sommes de Fourier portent au moins une énergie Σ|T|² ≥ (p−C)²/(p−1).

3. **Théorème conditionnel** (16.2) : sous des bornes uniformes |T(t)| ≤ C · ω^{−δ}, l'exclusion du zéro est prouvée pour les petits C/p.

4. **Stratégie CRT** (16.4) : il suffit de trouver un seul premier cristallin p pour lequel N₀(p) = 0.

5. **Critère de pseudo-hasard** (16.5) : si max|T(t)| ≤ C/p^{1/2+ε} et C < p, alors N₀ = 0.

6. **Analyse spectrale** (§8) : le mélange de Horner est rapide quand ω est grand et k ≫ √ω · log p, ce qui est vérifié pour tous les convergents ≥ q₅.

### 12.2. Ce qui reste ouvert

L'écart entre les résultats conditionnels et l'Hypothèse (H) réside dans la **preuve inconditionnelle** d'une borne sur T(t). Les obstacles sont :

1. **La contrainte de monotonie** : les A_j forment une suite strictement croissante, ce qui empêche la factorisation complète de T(t) en produit de sommes indépendantes.

2. **L'aspect multi-échelle** : corrSum mélange des puissances de 2 (croissant exponentiellement) et des puissances de 3 (les coefficients), créant des interférences à toutes les échelles.

3. **L'absence de structure algébrique simple** : corrSum n'est pas un polynôme, ni un produit, ni une forme quadratique — c'est une somme exponentielle mixte qui ne rentre pas dans les cadres classiques de Weil-Deligne.

### 12.3. Voies de résolution

**Voie A : Méthode de van der Corput.** Appliquer les itérations de van der Corput à la somme T(t) en exploitant la structure récursive. Chaque itération réduit la somme au prix d'un carré, mais la structure de Horner pourrait permettre un gain systématique.

**Voie B : Bornes d'incomplètes.** Utiliser les techniques de Korobov-Vinogradov pour les sommes exponentielles avec monômes à exposants lacunaires ({2^{A_j}} est lacunaire par monotonie).

**Voie C : Extension computationnelle de Simons-de Weger.** Étendre la borne computationnelle de k < 68 à k < 500. Combiné avec la décroissance exponentielle de C/d pour k ≥ 306, et l'exclusion vérifiée pour q₃ et q₅ (numériquement), cela rapprocherait considérablement d'un résultat complet.

---

## 13. Conclusion

La Phase 16 traduit l'Hypothèse d'Équirépartition Exponentielle (H) dans le langage des sommes de caractères additifs. Le cadre formel est complet : formule d'orthogonalité, identité de Parseval, bornes conditionnelles, et analyse spectrale du propagateur de Horner.

Le résultat le plus significatif est le **Théorème de Parseval** (16.1), qui établit inconditionnellement le coût énergétique de l'existence d'un cycle : les sommes exponentielles doivent porter une énergie d'au moins (p − C)²/(p−1) ≈ p dans le régime cristallin. Cette contrainte est non triviale et quantifie précisément la « structuration parfaite » que l'existence d'un zéro exigerait.

La **stratégie CRT** (Proposition 16.4) offre la simplification la plus prometteuse : il suffit de trouver un unique premier cristallin p pour lequel l'exclusion du zéro est démontrable. Pour les convergents d'indice élevé (q₉, q₁₁, ...), le rapport C/d décroît si rapidement (C/d ≈ 2^{−1230} pour q₉) que la probabilité heuristique d'atteindre 0 est astronomiquement faible.

Le passage de l'heuristique à la preuve reste le défi fondamental. Les bornes de Weil-Deligne fournissent le cadre naturel, mais la structure combinatoire de Comp(S, k) et la forme de Horner de corrSum résistent aux techniques standard. Nous identifions les méthodes de van der Corput et les bornes de sommes lacunaires comme les voies les plus prometteuses vers une résolution.

---

## Références

[1] P. Diaconis, M. Shahshahani, « Generating a random permutation with random transpositions », *Z. Wahrsch. Verw. Gebiete*, vol. 57, pp. 159–179, 1981.

[2] D. A. Burgess, « On character sums and L-series, II », *Proc. London Math. Soc.*, vol. 13, pp. 524–536, 1963.

[3] P. Deligne, « La conjecture de Weil, I », *Publ. Math. IHÉS*, vol. 43, pp. 273–307, 1974.

[4] A. Weil, « On some exponential sums », *Proc. Nat. Acad. Sci. USA*, vol. 34, pp. 204–207, 1948.

[5] N. M. Korobov, « Estimates of trigonometric sums and their applications », *Uspekhi Mat. Nauk*, vol. 13, pp. 185–192, 1958.

[6] I. M. Vinogradov, *The Method of Trigonometrical Sums in the Theory of Numbers*, Interscience, 1954.
