# Phase 10G — Hauteur de Syracuse : Energie Fractionnaire vs Gap Diophantien

> **Date** : 2026-02-24
> **Statut** : Rapport theorique — distingue rigoureusement PROUVE / PROUVABLE / CONJECTURE
> **Auteur** : E. Merle, assist. Claude Opus 4.6

---

## 1. Motivation et arret de la Phase 63

La Phase 63 tentait de prouver `gap_bound_large_k` pour TOUT k > 1322
via le theoreme de Legendre sur les fractions continues. Cette approche
est une **impasse asymptotique** : la borne O(k^2) de Legendre finit
par depasser la constante fixe 2^71 de Barina pour k > ~5 x 10^10.

Nous changeons de paradigme. Au lieu de chercher a borner n0 par une
constante fixe pour tout k, nous construisons une **theorie structurelle**
qui explique POURQUOI les grands cycles positifs sont impossibles, tout
en autorisant les cycles connus.

---

## 2. L'Equation Maitresse (PROUVEE)

### 2.1 Enonce

**Theoreme (Equation Maitresse Logarithmique)**. Soit {n_0, n_1, ..., n_{k-1}}
les elements impairs d'un cycle de Collatz (positif ou negatif), avec
a_i = v_2(3n_i + 1) et S = sum a_i. Alors :

```
(S - k * log_2(3)) * ln(2)  =  sum_{i=0}^{k-1} log(1 + 1/(3*n_i))
```

pour les cycles positifs (n_i > 0), et

```
(S - k * log_2(3)) * ln(2)  =  sum_{i=0}^{k-1} log(1 - 1/(3*|n_i|))
```

pour les cycles negatifs (n_i < 0).

### 2.2 Preuve (elementaire)

De l'iteration n_{i+1} = (3*n_i + 1) / 2^{a_i}, on prend log|.| :

```
log|n_{i+1}| = log|3*n_i + 1| - a_i * log(2)
```

Pour n_i > 0 : log|3n_i+1| = log(n_i) + log(3 + 1/n_i)
Pour n_i < 0 : log|3n_i+1| = log|n_i| + log(3 - 1/|n_i|)

En sommant sur le cycle (la somme telescopique des log|n_i| s'annule) :

```
0 = k*log(3) + sum log(1 + sigma/(3|n_i|)) - S*log(2)
```

ou sigma = +1 pour les cycles positifs, sigma = -1 pour les negatifs.
En reordonnant, on obtient l'equation maitresse. CQFD.

### 2.3 Statut formel

- **PROUVE** dans le cadre elementaire (algebre de log sur R)
- **FORMALISABLE** en Lean 4 avec Mathlib (Real.log, sum_congr)
- Deja partiellement formalise : la Product Bound (Phase 56) est une
  consequence de cette equation via l'inegalite exp(x) >= 1+x

---

## 3. L'Asymetrie Fondamentale : Pourquoi les cycles positifs et negatifs different

### 3.1 Le role du +1

Dans la map 3n+1 :
- Pour n > 0 : le +1 **augmente** |3n+1| par rapport a 3n.
  L'energie fractionnaire log(1 + 1/(3n)) > 0 est **positive**.
  Le gap Delta = S - k*log_2(3) > 0 est **positif** (2^S > 3^k).

- Pour n < 0 : le +1 **diminue** |3n+1| par rapport a |3n|.
  L'energie fractionnaire log(1 - 1/(3|n|)) < 0 est **negative**.
  Le gap Delta < 0 (2^S < 3^k).

### 3.2 L'analogie thermodynamique

Le +1 est un "quantum d'energie" dont le poids relatif est 1/(3|n_i|).

- **Pres de zero** (|n| petit) : l'energie du +1 est massive.
  Elle peut courber la trajectoire suffisamment pour refermer un cycle.
  C'est ainsi que les cycles {1}, {-1}, {-5}, {-17} existent.

- **Loin de zero** (|n| >> 1) : l'energie du +1 est un "bruit thermique"
  infinitesimal. Elle ne peut plus compenser le gap diophantien,
  qui est borne inferieurement par Baker.

### 3.3 Verification numerique

| Cycle | k | Delta*ln2 | Energie fract. | Match |
|-------|---|-----------|----------------|-------|
| {1}     | 1 | +0.28768  | +0.28768 | Exact |
| {-1}    | 1 | -0.40547  | N/A (k<2) | Baker ne s'applique pas |
| {-5,-7} | 2 | -0.11778  | -0.11778 | Exact |
| {-17,...,-91} | 7 | -0.06567 | -0.06567 | Exact |

Les quatre cycles connus satisfont l'equation maitresse a la precision machine.

---

## 4. Le Pincement (Baker + Energie Fractionnaire)

### 4.1 Borne inferieure sur |Delta| (Baker, HYPOTHESE H1)

Le theoreme de Baker sur les formes lineaires de logarithmes donne,
pour k >= 2 et 2^S =/= 3^k :

```
|2^S - 3^k| * k^6 >= 3^k
```

En posant d = 2^S - 3^k et en utilisant d = 3^k * (2^Delta - 1) :

```
|Delta| >= 1 / (k^6 * ln(2))    pour |Delta| petit
```

Plus precisement (via 2^x - 1 >= x*ln2 pour x >= 0) :

```
|Delta * ln(2)| >= 1/k^6
```

### 4.2 Borne superieure sur l'energie fractionnaire

Pour un cycle positif avec minimum n_0 :

```
sum log(1 + 1/(3n_i)) <= sum 1/(3n_i) <= k/(3*n_0)
```

puisque n_i >= n_0 pour tout i. Meme borne pour les cycles negatifs
(en valeur absolue).

### 4.3 Le pincement

En combinant 4.1 et 4.2 :

```
1/k^6  <=  |Delta * ln(2)|  =  |sum log(...)|  <=  k/(3*n_0)
```

D'ou : **n_0 <= k^7 / 3**.

C'est exactement la **Product Bound** (Phase 56, PROUVEE en Lean 4).

### 4.4 Consequence pour les cycles positifs

Pour k <= 1322 : (k^7 + k)/3 < 2^71 (native_decide, PROUVE).
Donc n_0 < 2^71, et Barina (H2) elimine le cycle.

**Resultat (Phase 58, 0 sorry, 2 hypotheses)** :
Aucun cycle positif non trivial avec k <= 1322 pas impairs.

---

## 5. Au-dela de k = 1322 : les trois voies

### 5.1 Voie A — Legendre (non-convergent)

Pour k tel que S/k n'est PAS un convergent de log_2(3) :
|log_2(3) - S/k| >= 1/(2k^2), d'ou |Delta| >= 1/(2k).
Le pincement donne : n_0 <= 2k^2/(3*ln2) ~ 0.96*k^2.
Valide tant que 0.96*k^2 < 2^71, soit k < ~5 x 10^10.

**Statut** : Prouvable en Lean 4 via Mathlib (Legendre = `Real.exists_rat_eq_convergent`).
MAIS ne couvre pas les k qui SONT des denominateurs de convergents.

### 5.2 Voie B — Rhin (meilleure mesure d'irrationalite)

Rhin (1987) a prouve mu(log_2(3)) <= 5.125 (au lieu de 6 dans Baker generique).
Cela donnerait n_0 <= k^{6.125}/3, ameliorant le seuil a k ~ 1800.
Gain modeste. Non formalisable sans la preuve complete de Rhin.

### 5.3 Voie C — Structure multiplicative de corrSum (recherche/porte2)

La branche `recherche/porte2` a explore l'analyse de Fourier de corrSum
modulo d = 2^S - 3^k. Resultat : N(0) = 0 prouve exactement pour k <= 20.
Pour k >= 21, la cancellation des sommes exponentielles est numeriquement
confirmee mais pas prouvee rigoureusement.

---

## 6. Definition formelle de la Hauteur de Syracuse

### 6.1 Hauteur archimedo-diophantienne

**Definition**. La Hauteur de Syracuse d'ordre (k,S) d'un entier n > 0 est :

```
H_{k,S}(n) = |Delta(k,S) * ln(2)| - sum_{i=0}^{k-1} log(1 + 1/(3*T^i(n)))
```

ou T est la map de Collatz acceleree et T^i(n) designe le i-eme iterate impair.

**Propriete** : n est sur un cycle de parametres (k,S) si et seulement si
H_{k,S}(n) = 0.

### 6.2 Theoreme de non-annulation (objectif)

**Theoreme-cible** : Pour tout n > 2^71 et tout (k,S) admissible :

```
H_{k,S}(n) > 0
```

**Preuve conditionnelle** :
- Si k <= 1322 : Baker + Product Bound donne n_0 <= k^7/3 < 2^71.
  Donc n > 2^71 ne peut pas etre sur un tel cycle. PROUVE.
- Si k > 1322 : Baker donne |Delta*ln2| >= 1/k^6.
  L'energie fractionnaire <= k/(3n_0) <= k/(3 * 2^71).
  Pour H > 0, il faut : 1/k^6 > k/(3*2^71), soit k^7 < 3*2^71.
  C'est vrai pour k <= 1322 mais FAUX au-dela. GAP NON FERME.

### 6.3 Diagnostic honnete

La Hauteur H_{k,S} est une **reformulation elegante** de la Product Bound.
Elle clarifie la structure mais **ne donne pas de borne plus forte**.
La limitation reste la meme : Baker donne |Delta| >= 1/k^6, ce qui
donne n_0 = O(k^7), et O(k^7) depasse 2^71 pour k > 1322.

Pour aller au-dela, il faut SOIT :
(a) Ameliorer la borne de Baker (Rhin, ou mieux)
(b) Exploiter Legendre pour les non-convergents + verification finie des convergents
(c) Trouver une structure dans corrSum qui force N(0) = 0

L'option (b) est **prouvable en Lean** et donnerait couverture k <= ~5 x 10^10.
L'option (c) est le programme de `recherche/porte2`.

---

## 7. Coherence avec les cycles connus

### 7.1 Le cycle trivial 1 -> 4 -> 2 -> 1

k=1, S=2. Delta = 2 - log_2(3) = 0.415.
Energie = log(4/3) = 0.288.
Les deux sont egaux (equation maitresse verifiee).
La theorie l'AUTORISE car n_0=1 << 2^71.

### 7.2 Les cycles negatifs -1, -5, -17

Pour les cycles negatifs, Delta < 0 et l'energie est negative.
La theorie ne PRETEND PAS interdire les cycles negatifs :
elle porte sur les cycles POSITIFS avec n_0 > 2^71.

Les cycles negatifs existent pour la meme raison que le cycle de 1 :
le +1 a un poids relatif suffisant quand |n_i| est petit.

### 7.3 Pas de renommage (reponse a l'auditeur)

H_{k,S}(n) n'est PAS un renommage de corrSum. C'est la difference
entre deux quantites :
- Le gap diophantien |Delta*ln2| (propriete de k et S, pas de n)
- L'energie fractionnaire sum log(1+1/(3n_i)) (propriete de l'orbite)

L'equation maitresse dit que ces deux quantites sont EGALES sur un cycle.
Le pincement dit que pour n grand, l'energie est trop petite pour
compenser le gap, ce qui INTERDIT le cycle.

---

## 8. Le squelette Lean 4

Voir le fichier `Phase10GLeanSkeleton.lean` (a cote de ce document).

### Theoremes a formaliser (par ordre de difficulte)

| # | Theoreme | Difficulte | Dependances |
|---|----------|-----------|-------------|
| 1 | Equation maitresse (log telescopique) | Moyenne | Real.log, Finset.sum |
| 2 | Pincement Baker (n0 <= k^7/3) | Deja fait | Phase 56 |
| 3 | Legendre non-convergent (n0 <= Ck^2) | Elevee | Mathlib DiophantineApproximation |
| 4 | Verification convergents (natif) | Moyenne | native_decide, 25 lemmes |
| 5 | Theorem borne (k <= K_max, 0 sorry) | Combinaison | 2+3+4 |

### Ce qui EST faisable maintenant
- Theoremes 1-2 : reformulation de Phase 56 existante
- Theoreme 3 : Mathlib a `Real.exists_rat_eq_convergent` (Legendre)
- Theoreme 4 : calculs finis par native_decide

### Ce qui est HORS PORTEE
- Prouver l'absence de cycles pour TOUT k > 0 avec seulement Baker + Barina
  (impossible : n0 = O(k^7) depasse toute constante fixe)

---

## 9. Plan d'action

1. **Court terme** (implementable maintenant) :
   - Porter Phase 58 de `sharp-ishizaka` (2 hyp, 0 sorry, k <= 1322)
   - Formaliser l'equation maitresse en Lean 4

2. **Moyen terme** (necessitant travail Mathlib) :
   - Formaliser le pont Legendre (non-convergent -> n0 = O(k^2))
   - Verifier les 25 fenetres convergentes par native_decide
   - Obtenir : 2 hyp, 0 sorry, k <= K_max ~ 5 x 10^10

3. **Long terme** (programme de recherche) :
   - Voie C : analyse de Fourier de corrSum mod d (recherche/porte2)
   - Voie D : analyse 2-adique (Phase 10D, Lagarias/Siegel)
   - Objectif : elimination pour tout k, ou preuve d'impossibilite

---

## Appendice A : Preuve que Product Bound = Pincement

De l'equation maitresse pour un cycle positif :
```
Delta * ln(2) = sum log(1 + 1/(3*n_i))
```

Or Delta * ln(2) = log(2^S/3^k) = log(1 + d/3^k).
Et sum log(1+1/(3n_i)) = log(prod (1+1/(3n_i))).

Donc : 1 + d/3^k = prod (1 + 1/(3n_i)).

De n_0 = min(n_i) : prod(1+1/(3n_i)) <= (1+1/(3n_0))^k.
Donc : 1 + d/3^k <= (1 + 1/(3n_0))^k.
Par Bernoulli : (1+x)^k >= 1+kx, applique a x = d/(3^k*k...) ...

En fait, dans l'autre sens :
(1+1/(3n_0))^k <= exp(k/(3n_0))   [Weierstrass]
Donc : d/3^k <= exp(k/(3n_0)) - 1.
Si k/(3n_0) <= 1 : exp(k/(3n_0)) - 1 <= 2k/(3n_0).
Et Baker : d/3^k >= 1/k^6.
D'ou : 1/k^6 <= 2k/(3n_0), soit n_0 <= 2k^7/3.

La constante 2 (vs 1) vient de l'approximation exp(x)-1 <= 2x.
La Product Bound exacte (Phase 56) est plus fine car elle passe
par l'inegalite de Bernoulli directement sur l'equation de Steiner.
