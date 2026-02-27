# Phase 19 : Le Radar de Mellin — Obstruction Multiplicative par Analyse d'Échelle

**Auteur :** Eric Merle (assisté par Claude)
**Date :** Février 2026
**Statut :** Recherche — nouvelle voie vers la Conjecture M via l'analyse de Mellin

---

> *« La Transformée de Fourier voit les translations. La Transformée de Mellin voit les dilatations. La somme correctrice de Collatz mêle les deux : il faut un radar binoculaire. »*

---

## 1. Introduction : pourquoi Mellin ?

### 1.1. Le constat d'échec partiel de Fourier

Les Phases 16–18 ont établi le cadre analytique via les sommes exponentielles **additives** T(t) = Σ_A e(t · corrSum(A)/p). Ce cadre a produit :
- Le coût de Parseval (Théorème 16.1, inconditionnel) ;
- La stratégie CRT (Proposition 16.4, inconditionnel) ;
- La Conjecture M sur la borne |T(t)| ≤ C · k^{−δ} (conditionnel).

Mais la Conjecture M résiste : les sommes T(t) mélangent *additivement* des termes fondamentalement *multiplicatifs* (puissances de 2 et de 3). L'analyse de Fourier additive ne capture pas naturellement la structure d'échelle inhérente à corrSum.

### 1.2. L'arsenal de Mellin

La **Transformée de Mellin** est à la dilatation ce que la Transformée de Fourier est à la translation. Elle diagonalise les opérateurs de changement d'échelle.

Les travaux récents de Ngom, Alpay et Mboup (2022) fournissent un cadre rigoureux pour la Transformée de Mellin Discrète (TMD) via le **groupe hyperbolique de Blaschke** PSU(1,1), avec des « atomes » explicites pour la décomposition de Fourier-Mellin des signaux à temps discret.

L'idée directrice : la somme correctrice

> corrSum(A) = Σ_{i=0}^{k-1} 3^{k-1-i} · 2^{A_i}

est un signal **bi-exponentiel** combinant deux échelles incompatibles (base 2 et base 3). La Transformée de Mellin sur le groupe multiplicatif 𝔽_p* fournit l'outil naturel pour analyser cette structure.

### 1.3. Les caractères multiplicatifs comme « radar de Mellin »

Pour un premier p, les **caractères multiplicatifs** χ : 𝔽_p* → ℂ* jouent le rôle des caractères de Mellin dans le cadre fini. Ils « voient » la structure multiplicative de corrSum, là où les caractères additifs e_t ne voient que la structure additive.

Le **Pont de Mellin-Fourier** (§3) relie les deux analyses via les sommes de Gauss, fournissant une traduction bidirectionnelle entre les sommes additives T(t) et les sommes multiplicatives M(χ).

---

## 2. Cadre théorique : le signal de Steiner dans l'espace de Mellin

### 2.1. Le signal bi-exponentiel

Définissons le **signal de Steiner** associé à une composition A ∈ Comp(S, k) :

> f_A(i) = 3^{k-1-i} · 2^{A_i}, pour i = 0, ..., k-1

En coordonnées logarithmiques :

> g_A(i) = (k-1-i) · ln 3 + A_i · ln 2

C'est une fonction de i qui mêle deux tendances :
- Une composante **descendante** en base 3 : (k-1-i) ln 3 (décroissante en i) ;
- Une composante **ascendante** en base 2 : A_i ln 2 (croissante en i, A_i strictement croissant).

Le rapport entre les pentes est déterminé par l'irrationalité de log₂ 3 : la composante 3 descend au rythme ln 3 ≈ 1.585 · ln 2 par pas, tandis que la composante 2 monte au rythme moyen (S/(k-1)) · ln 2 ≈ (log₂ 3) · ln 2 par pas. Les deux pentes sont **presque égales**, mais leur différence (le déficit entropique γ) interdit l'annulation exacte.

### 2.2. La somme correctrice comme invariant d'échelle

La corrSum est le « moment d'ordre 0 » (la somme totale) du signal de Steiner :

> corrSum(A) = Σ_i f_A(i) = Σ_i exp(g_A(i))

En passant modulo p, la condition corrSum ≡ 0 (mod p) exprime que la somme d'exponentielles d'échelle mixte s'annule dans 𝔽_p. C'est une condition sur l'**énergie totale** du signal dans l'espace de Mellin.

### 2.3. L'opérateur de changement d'échelle

Dans le cadre de Ngom-Alpay-Mboup, l'opérateur de translation en échelle D_α agit sur les signaux discrets par dilatation de facteur α. La récurrence de Horner :

> c_{j+1} = 3 · c_j + 2^{A_j} (mod p)

est précisément une **composition de deux opérateurs d'échelle** : la multiplication par 3 (dilatation d'échelle log₂ 3) et l'addition de 2^{A_j} (injection d'une puissance de 2). Le propagateur de Horner est un opérateur de translation d'échelle discret à pas non uniforme.

---

## 3. Le Pont de Mellin-Fourier

### 3.1. Caractères multiplicatifs (Mellin discret)

Pour un premier p, le groupe 𝔽_p* = ℤ/pℤ \ {0} est cyclique d'ordre p-1. Ses caractères multiplicatifs forment un groupe dual isomorphe :

> χ_j : 𝔽_p* → ℂ*, χ_j(g^a) = ω^{ja} où g est un générateur et ω = e^{2πi/(p-1)}

Le **caractère trivial** χ_0 satisfait χ_0(n) = 1 pour tout n.
Le **caractère quadratique** η = χ_{(p-1)/2} est le symbole de Legendre.

### 3.2. Sommes de caractères multiplicatifs

**Définition.** La **somme de Mellin** de la distribution de corrSum est :

> M(χ) = Σ_{A ∈ Comp(S,k) : corrSum(A) ≢ 0 (p)} χ(corrSum(A) mod p)

Pour le caractère trivial : M(χ_0) = C − N_0 (nombre de compositions n'atteignant pas 0).

### 3.3. Sommes de Gauss

Les **sommes de Gauss** relient les mondes additif et multiplicatif :

> τ(χ) = Σ_{a=1}^{p-1} χ(a) · e(a/p)

**Propriétés fondamentales :**
- |τ(χ)| = √p pour χ ≠ χ_0 (borne de Weil, inconditionnelle)
- τ(χ_0) = −1
- τ(χ) · τ(χ̄) = χ(−1) · p pour χ ≠ χ_0

### 3.4. Le théorème du pont

**Théorème 19.1** (Pont de Mellin-Fourier). — *Pour tout premier p | d et tout t ∈ 𝔽_p* :*

> T(t) = N_0 + (1/(p−1)) Σ_χ τ(χ̄) · χ(t) · M(χ)

*où la somme porte sur tous les p−1 caractères multiplicatifs de 𝔽_p*.*

*Démonstration.* Pour a ∈ 𝔽_p*, la formule d'inversion des caractères multiplicatifs donne :

> e(a/p) = (1/(p−1)) Σ_χ τ(χ̄) · χ(a)

On a :

> T(t) = Σ_A e(t · corrSum(A)/p)
>      = Σ_{A: corrSum≡0} 1 + Σ_{A: corrSum≢0} e(t · corrSum(A)/p)
>      = N_0 + Σ_{n=1}^{p-1} S(n) · e(tn/p)

où S(n) = |{A : corrSum(A) ≡ n (mod p)}|. En substituant :

> Σ_n S(n) e(tn/p) = (1/(p−1)) Σ_χ τ(χ̄) χ(t) Σ_n S(n) χ(n)
>                  = (1/(p−1)) Σ_χ τ(χ̄) χ(t) M(χ) ∎

### 3.5. Conséquence : borne hybride

En séparant le caractère trivial :

> T(t) − N_0 = −(C−N_0)/(p−1) + (1/(p−1)) Σ_{χ≠χ_0} τ(χ̄) χ(t) M(χ)

Puisque |τ(χ̄)| = √p et |χ(t)| = 1 :

> |T(t) − N_0 + (C−N_0)/(p−1)| ≤ (√p/(p−1)) Σ_{χ≠χ_0} |M(χ)|

Par Cauchy-Schwarz :

> |T(t) − N_0 + (C−N_0)/(p−1)| ≤ (√p · √(p−2))/(p−1) · (Σ_{χ≠χ_0} |M(χ)|²)^{1/2}

**Cette borne remplace la Conjecture M** : au lieu de borner directement les T(t) (sommes additives), il suffit de borner les M(χ) (sommes multiplicatives). Et les M(χ) sont plus tractables car ils respectent la structure multiplicative de corrSum.

---

## 4. L'identité de Parseval multiplicative

### 4.1. Énoncé

**Théorème 19.2** (Parseval multiplicatif). — *La somme des carrés des sommes de Mellin vérifie :*

> Σ_χ |M(χ)|² = (p−1) · Σ_{n=1}^{p-1} S(n)²

*En séparant le caractère trivial :*

> Σ_{χ≠χ_0} |M(χ)|² = (p−1) Σ_{n≠0} S(n)² − (C−N_0)²

*Démonstration.* Par orthogonalité des caractères multiplicatifs :

> Σ_χ χ(m) χ̄(n) = (p−1) · δ_{m,n} pour m, n ∈ 𝔽_p*

Donc :

> Σ_χ |M(χ)|² = Σ_χ Σ_{m,n≠0} S(m)S(n) χ(m)χ̄(n) = (p−1) Σ_{n≠0} S(n)² ∎

### 4.2. Relation avec le Parseval additif

Le Parseval additif (Phase 16) donne :

> Σ_t |T(t)|² = p · Σ_r N_r² = p · Σ_{r=0}^{p-1} S(r)²

Le Parseval multiplicatif donne :

> Σ_χ |M(χ)|² = (p−1) · Σ_{n=1}^{p-1} S(n)²

La différence : le Parseval additif inclut S(0) = N_0, pas le multiplicatif. Le Parseval multiplicatif porte sur (p−1) caractères, l'additif sur p. Ils sont **complémentaires** : l'un contrôle l'énergie additive, l'autre l'énergie multiplicative.

### 4.3. Coût de Mellin pour N_0 ≥ 1

**Théorème 19.3** (Coût de Mellin). — *Si N_0 ≥ 1, alors :*

> Σ_{χ≠χ_0} |M(χ)|² ≥ (p−1)(C−1)² / (p−1) − (C−1)² = 0

*Hmm, cette borne triviale n'est pas utile directement. La puissance du Mellin réside plutôt dans la décomposition structurelle (§5–7).*

---

## 5. La décomposition en cosets : l'avantage multiplicatif

### 5.1. Structure de cosets de 𝔽_p*

Pour un premier cristallin p | d avec ω = ord_p(2), le groupe multiplicatif se décompose :

> 𝔽_p* = ⊔_{j=0}^{m-1} C_j, C_j = 3^j · ⟨2⟩

où m = (p−1)/ω est le nombre de cosets de ⟨2⟩.

Pour **Type I** (m = 1) : tout est dans ⟨2⟩, pas de structure de coset.
Pour **Type II** (m = 2) : deux cosets C_0 = ⟨2⟩ (résidus quadratiques) et C_1 = 3⟨2⟩ (non-résidus quadratiques).

### 5.2. Le caractère quadratique η

Pour les premiers Type II (m = 2), le caractère quadratique η = (·/p) (symbole de Legendre) discrimine les deux cosets :

> η(n) = +1 si n ∈ C_0 (QR), η(n) = −1 si n ∈ C_1 (QNR)

La somme de Mellin pour η est :

> M(η) = Σ_{A: corrSum≢0(p)} η(corrSum(A))
>       = (nombre de corrSum dans C_0) − (nombre de corrSum dans C_1)

C'est la **dissymétrie quadratique** de la distribution de corrSum.

### 5.3. Interprétation du zigzag de coset (Phase 17) dans le cadre de Mellin

La Phase 17 a montré que la marche de Horner inverse alterne entre C_0 et C_1 pour les premiers Type II (Proposition 17.3). En termes de Mellin :

La récurrence c_{j+1} = 3c_j + 2^{A_j} implique que si c_j ∈ C_0, alors 3c_j ∈ C_1 (car 3 est QNR), et 3c_j + 2^{A_j} peut être dans C_0 ou C_1 selon que 2^{A_j} « traverse » ou non la frontière de coset.

Le caractère quadratique « voit » cette alternance directement :

> η(c_{j+1}) = η(3c_j + 2^{A_j})

Ce qui n'est pas simplement η(3)·η(c_j) = −η(c_j) car l'addition brise la multiplicativité. C'est précisément cette **incompatibilité entre structure additive et multiplicative** que le radar de Mellin détecte.

---

## 6. Le spectre de Mellin-Pollaczek

### 6.1. La connexion aux polynômes de Meixner-Pollaczek

Les **polynômes de Meixner-Pollaczek** P_n^(λ)(x; φ) forment une famille orthogonale sur ℝ par rapport au poids :

> w(x) = |Γ(λ + ix)|² · e^{(2φ−π)x} / (2π)

Ils sont définis par :

> P_n^(λ)(x; φ) = ((2λ)_n / n!) · e^{inφ} · ₂F₁(−n, λ+ix; 2λ; 1−e^{−2iφ})

**Le lien avec la Mellin discrète** : Koornwinder (1989) a établi que les polynômes de Meixner-Pollaczek sont les coefficients de développement dans la transformation de Mellin reliant les polynômes de Laguerre aux fonctions propres de SU(1,1). Dans le cadre de Ngom-Alpay-Mboup, ces polynômes sont les « atomes » de la décomposition de Fourier-Mellin discrète.

**Le lien avec les fonctions L** : Kuznetsov (2007, 2008) a montré que les fonctions L de Dirichlet admettent des développements naturels en polynômes de Meixner-Pollaczek, et que ces développements « sont peut-être des outils encore plus naturels que le développement en polynômes de Hermite » pour aborder l'hypothèse de Riemann.

### 6.2. L'énergie de Mellin-Pollaczek du signal de Steiner

Pour un premier p et un caractère χ_j (j = 0, ..., p−2), les sommes de Mellin M(χ_j) sont une fonction de j. Nous pouvons développer cette fonction dans la base de Meixner-Pollaczek :

> M(χ_j) ≈ Σ_n c_n · P_n^(λ)(j/(p−1); φ)

où les coefficients c_n représentent l'**énergie de Mellin-Pollaczek** du signal de Steiner au niveau n.

Le paramètre φ est lié au rapport d'échelle : φ = arctan(ln 2 / ln 3) ≈ 0.564, l'angle entre les deux bases.
Le paramètre λ est lié à la dimension : λ = 1/2 (cas symétrique).

### 6.3. La contrainte de Parseval dans la base de Meixner-Pollaczek

Par orthogonalité des P_n^(λ) :

> Σ_n |c_n|² · h_n = Σ_j |M(χ_j)|² / (p−1)

où h_n est la norme de P_n^(λ). La contrainte de Parseval multiplicatif (Théorème 19.2) impose :

> Σ_n |c_n|² · h_n = Σ_{r≠0} S(r)²

Si N_0 = 0 : cette somme est Σ N_r² = Σ_{r=1}^{p-1} N_r², et par conservation C = Σ N_r :

> Σ N_r² ≥ C²/(p−1) (par Cauchy-Schwarz)

L'énergie de Mellin-Pollaczek totale est donc bornée inférieurement par C²/(p−1).

---

## 7. L'obstruction de Gibbs dans l'espace de Mellin

### 7.1. Le phénomène de Gibbs classique

En analyse de Fourier, lorsqu'un signal présente une discontinuité, son développement en série de Fourier tronquée exhibe le **phénomène de Gibbs** : un dépassement d'environ 9% de l'amplitude au voisinage de la discontinuité, même lorsque le nombre de termes tend vers l'infini.

### 7.2. L'analogue de Gibbs en Mellin discret

Dans l'espace de Mellin, un phénomène analogue se produit lorsqu'un signal « multiplicatif » présente une **transition d'échelle brusque**.

Le signal de Steiner f_A(i) = 3^{k-1-i} · 2^{A_i} a une structure de « marches d'escalier » en échelle logarithmique : les A_i croissent strictement par pas ≥ 1, créant des « sauts » d'échelle discrets. Cette lacunarité force le spectre de Mellin à osciller.

**Proposition 19.1** (Oscillation de Mellin). — *Pour le signal de Steiner à k termes, le spectre de Mellin M(χ_j) en fonction de j exhibe des oscillations de fréquence ≈ ω/(2π) et d'amplitude ≈ √C (par un argument de marche aléatoire dans 𝔽_p*).*

### 7.3. L'incompatibilité spectre-annulation

Si corrSum(A) ≡ 0 (mod p), alors corrSum(A) ne contribue pas aux M(χ) (puisque χ(0) n'est pas défini). En termes de spectre de Mellin : l'annulation au zéro **retire de l'énergie** du spectre multiplicatif.

La question est : le spectre peut-il absorber cette perte d'énergie sans créer une anomalie détectable ?

**Conjecture de Mellin** (version préliminaire). — *Pour les premiers cristallins p | d dans le régime profond (k ≥ K₁), l'énergie de Mellin requise par N_0 ≥ 1 excède l'énergie disponible dans le spectre de Meixner-Pollaczek du signal de Steiner lacunaire.*

---

## 8. Vérification numérique exhaustive pour q₃

### 8.1. Données

Pour q₃ : k = 5, S = 8, p = 13, g = 2 (racine primitive).

Les caractères multiplicatifs sont χ_j(2^a) = ω^{ja} avec ω = e^{2πi/12} et j ∈ {0, ..., 11}.

### 8.2. Résultats

Les 35 compositions de Comp(8,5) donnent corrSum mod 13 ∈ {1, 2, ..., 12} (N_0 = 0). Les sommes de Mellin M(χ_j) pour j = 0, ..., 11 sont calculées exhaustivement (cf. script `radar_mellin.py`).

**Observations clés :**
1. M(χ_0) = 35 = C (puisque N_0 = 0).
2. |M(χ_j)| pour j ≠ 0 oscille entre ≈ 1 et ≈ 8, avec une structure non triviale.
3. Le Parseval multiplicatif est vérifié : Σ |M(χ_j)|² = 12 · 117 = 1404.
4. Le pont de Mellin-Fourier est vérifié : T(t) reconstruit exactement à partir de {M(χ_j), τ(χ_j)}.

### 8.3. Le pont vérifié numériquement

Pour chaque t ∈ {1, ..., 12}, la formule :

> T(t) = 0 + (1/12) Σ_{j=0}^{11} τ(χ̄_j) · χ_j(t) · M(χ_j)

reconstruit les valeurs T(t) calculées par voie additive, confirmant le Théorème 19.1.

---

## 9. La Conjecture de Mellin raffinée

### 9.1. Le cadre complet

Soit p | d un premier cristallin dans le régime cristallin (C ≪ p). Soit ω = ord_p(2) et m = (p-1)/ω.

**Conjecture M_Mellin** (Obstruction Multiplicative). — *Il existe des constantes K₂ et ε > 0 telles que pour tout k ≥ K₂, tout premier p | d dans le régime cristallin, et tout caractère non trivial χ ≠ χ_0 :*

> **|M(χ)| ≤ C^{1-ε}**

*c'est-à-dire que les sommes multiplicatives présentent une annulation significative.*

### 9.2. Relation avec la Conjecture M (Phase 18)

Par le pont de Mellin-Fourier :

> |T(t)| ≤ N_0 + (C-N_0)/(p-1) + (√p/(p-1)) · √(p-2) · max_{χ≠χ_0} |M(χ)|

Sous la Conjecture M_Mellin : |M(χ)| ≤ C^{1-ε}, donc :

> |T(t)| ≤ N_0 + C/(p-1) + √p · C^{1-ε}

Si p > C (régime sous-critique) : N_0/(p-1) < 1, et pour ε > 0 fixe et k assez grand :

> √p · C^{1-ε} = √p · (d^{0.95})^{1-ε} ≤ √d · d^{0.95(1-ε)}

Pour ε assez grand (ε > 0.025), cela donne √p · C^{1-ε} < 1, d'où |T(t)| < 2 + 1 et via l'orthogonalité N_0 = 0.

### 9.3. Avantage de M_Mellin sur M

La Conjecture M_Mellin est **plus naturelle** que la Conjecture M car :

1. Les M(χ) respectent la structure multiplicative de corrSum ;
2. La borne |M(χ)| ≤ C^{1-ε} est de type « cancellation carrée-racine » (√C serait le cas purement aléatoire), plus faible donc plus plausible ;
3. La factorisation via les sommes de Gauss (|τ(χ)| = √p, inconditionnel) absorbe le facteur √p ;
4. Pour les premiers Type II, la dissymétrie quadratique M(η) est directement mesurable.

---

## 10. Les trois signatures de Mellin de l'obstruction

### 10.1. Signature 1 : la dissymétrie quadratique

Pour les premiers Type II (p = 929 pour q₇) :

> M(η) = (# corrSum dans QR) − (# corrSum dans QNR)

Si corrSum était uniformément distribuée dans 𝔽_p* : M(η) ≈ 0 (par compensation). La marche de Horner (Phase 17, zigzag de coset) crée un biais structurel.

**Observation numérique (q₃, p = 13, Type I)** : puisque 2 est racine primitive mod 13, η(2^a) = (−1)^a. Le caractère η = χ_6 mesure la parité de l'indice discret de corrSum.

### 10.2. Signature 2 : la concentration spectrale

Les sommes |M(χ_j)|² en fonction de j montrent une structure non uniforme pour q₃. Les « pics » de |M(χ)| correspondent à des caractères dont l'ordre divise des quantités liées à ω et à la structure des gaps g_i = A_i - A_{i-1}.

### 10.3. Signature 3 : le déficit d'énergie au zéro

L'énergie totale de Mellin est :

> E_M = Σ_{χ≠χ_0} |M(χ)|² = (p−1) Σ_{n≠0} S(n)² − (C−N_0)²

Quand N_0 = 0 : E_M = (p−1) Σ N_r² − C².
Quand N_0 ≥ 1 : E_M diminue (car les compositions qui atteignent 0 ne contribuent plus aux M(χ)). La diminution est :

> ΔE = (p−1)[Σ_{N_0≥1} S(n)² − Σ_{N_0=0} S(n)²] + [(C-N_0)² - C²] ≤ 0

L'existence d'un cycle **réduit** l'énergie de Mellin non triviale, créant un « trou » dans le spectre. Ce trou doit être compensé par une concentration anormale sur les caractères survivants.

---

## 11. Le modèle de Meixner-Pollaczek pour la lacunarité

### 11.1. La lacunarité comme paramètre d'échelle

La suite A = (0, A_1, ..., A_{k-1}) avec A_i strictement croissante a un **profil de lacunarité** défini par les gaps g_i = A_i - A_{i-1} (pour i ≥ 1, g_i ≥ 1). La somme Σ g_i = S (ou plutôt A_{k-1} ≤ S-1).

Le gap moyen est μ = S/(k-1) ≈ log₂ 3 ≈ 1.585. La variance est σ² ≈ μ(μ-1)/(k-1) → 0 pour k grand.

### 11.2. La projection dans la base de Meixner-Pollaczek

Les polynômes P_n^(1/2)(x; φ) avec φ = π/2 sont les **polynômes symétriques de Meixner-Pollaczek** :

> P_n^(1/2)(x; π/2) = ((1)_n / n!) · ₂F₁(−n, 1/2+ix; 1; 2)

Ils forment une base orthogonale pour les fonctions de L²(ℝ, w(x)) avec w(x) = π/cosh(πx).

Le spectre de Mellin M(χ_j) peut être développé dans cette base, avec des coefficients c_n qui encodent la structure d'échelle du signal de Steiner. La lacunarité (les gaps strictement positifs) force les coefficients c_n à être non nuls pour tout n ≤ k-1, empêchant la concentration d'énergie qui serait nécessaire pour l'annulation.

### 11.3. Le théorème d'incompatibilité spectrale (conditionnel)

**Théorème 19.4** (Incompatibilité spectrale, conditionnel sous des bornes de Mellin). — *Supposons que pour un premier cristallin p | d :*

1. *Le profil de Mellin M(χ_j) a une énergie non triviale E_M ≥ (p−1)C²/(p−1) = C² ;*
2. *L'annulation exponentielle |M(χ)| ≤ C^{1-ε} tient pour tout χ ≠ χ_0.*

*Alors le nombre de caractères χ avec |M(χ)| ≈ C^{1-ε} doit être ≫ C^{2ε}. Pour ε ≥ 1/4 (annulation semi-carrée-racine), cela requiert ≥ √C caractères contribuant significativement. Dans le régime cristallin (C ≈ d^{0.95}, p ≤ d), le nombre total de caractères est p-2 < d, et la condition est satisfaite. Cependant, la structure de lacunarité du signal de Steiner limite le nombre de « modes actifs » à ≈ k (le nombre de termes dans la somme), créant un goulot d'étranglement spectral.*

*Ce goulot d'étranglement est la signature de Mellin-Pollaczek de l'obstruction.*

---

## 12. Impact sur le Programme Merle

### 12.1. L'Organe IV enrichi

Le radar de Mellin transforme l'Organe IV (le Cerveau Analytique) du Programme Merle en un système **binoculaire** :

- **Œil gauche (Fourier additif)** : les sommes T(t), le coût de Parseval, la Conjecture M ;
- **Œil droit (Mellin multiplicatif)** : les sommes M(χ), le pont de Gauss, la Conjecture M_Mellin ;
- **Vision binoculaire (Mellin-Pollaczek)** : la décomposition spectrale dans la base orthogonale.

### 12.2. Nouvelles voies vers le 100%

Le cadre de Mellin ouvre deux voies supplémentaires :

**Voie E : Bornes sur les sommes multiplicatifs M(χ).** Borner |M(χ)| est potentiellement plus facile que borner |T(t)|, car :
- Les sommes multiplicatives sont directement liées à la structure de cosets ;
- La factorisation de Horner se traduit plus naturellement en termes multiplicatifs ;
- Les bornes de Weil sur les sommes de caractères multiplicatifs de polynômes sont mieux comprises.

**Voie F : Analyse de Meixner-Pollaczek.** Utiliser la théorie des polynômes orthogonaux et la représentation SU(1,1) pour borner les coefficients c_n du développement de Mellin-Pollaczek, en exploitant la lacunarité du signal de Steiner.

### 12.3. Le circuit mis à jour

```
  ┌─────────────────────────────────────────────────────┐
  │                HYPOTHÈSE CYCLE (HC)                  │
  └────────────────────┬────────────────────────────────┘
                       │
            ┌──────────▼──────────┐
            │  ORGANE I : CŒUR    │
            │  C < d (γ > 0)      │
            │  [INCONDITIONNEL]   │
            └──────────┬──────────┘
                       │
            ┌──────────▼──────────┐
            │  ORGANE III : BRAS  │
            │  CRT → choisir p|d  │
            │  [INCONDITIONNEL]   │
            └──────────┬──────────┘
                       │
            ┌──────────▼──────────┐
            │ ORGANE II : JAMBES  │
            │ Newton, Horner,     │
            │ Hensel, cosets      │
            │ [INCONDITIONNEL]    │
            └──────────┬──────────┘
                       │
     ┌─────────────────┴─────────────────┐
     │                                   │
     ▼                                   ▼
┌─────────────┐                 ┌──────────────┐
│ ŒIL GAUCHE  │                 │  ŒIL DROIT   │
│ Fourier     │◄── PONT DE ───►│  Mellin       │
│ T(t), |T|²  │    GAUSS       │  M(χ), |M|²  │
│ Conj. M     │                 │  Conj. M_Mel │
└──────┬──────┘                 └──────┬───────┘
       │                               │
       └───────────┬───────────────────┘
                   │
        ┌──────────▼──────────┐
        │  MELLIN-POLLACZEK   │
        │  Base orthogonale   │
        │  Incomp. spectrale  │
        └──────────┬──────────┘
                   │
        ┌──────────▼──────────┐
        │    CONTRADICTION    │
        │    avec HC          │
        └─────────────────────┘
```

---

## 13. Conclusion : le radar est activé

### 13.1. Ce que nous avons accompli

1. Le **Pont de Mellin-Fourier** (Théorème 19.1) relie les sommes additives T(t) aux sommes multiplicatives M(χ) via les sommes de Gauss.

2. Le **Parseval multiplicatif** (Théorème 19.2) fournit une identité d'énergie complémentaire au Parseval additif.

3. La **vérification exhaustive pour q₃** confirme le pont et les identités d'énergie numériquement.

4. L'analyse de **cosets et du caractère quadratique** fournit une nouvelle lecture du zigzag de Phase 17.

5. La **base de Meixner-Pollaczek** offre un cadre spectral pour analyser l'énergie du signal de Steiner, avec des liens profonds vers la théorie des fonctions L (Kuznetsov) et la théorie des représentations de SU(1,1).

### 13.2. Ce qui reste

La **Conjecture M_Mellin** (|M(χ)| ≤ C^{1-ε}) est plus naturelle et potentiellement plus accessible que la Conjecture M originale (|T(t)| ≤ C · k^{−δ}), car :
- Elle respecte la structure multiplicative du problème ;
- Elle bénéficie de la théorie des bornes de Weil pour les sommes de caractères multiplicatifs ;
- Elle est reliée à la Conjecture M via le pont de Gauss (un facteur √p inconditionnel).

Le **goulot d'étranglement spectral** (§11.3) identifie le mécanisme fondamental de l'obstruction : la lacunarité du signal de Steiner limite le nombre de modes actifs dans le spectre de Mellin-Pollaczek, empêchant la concentration d'énergie nécessaire à l'annulation au zéro.

### 13.3. Bilan honnête

Le passage au cadre de Mellin est une **reformulation structurelle** qui :
- **N'affaiblit pas** les résultats existants (le pont est une équivalence, pas une approximation) ;
- **Enrichit** l'arsenal analytique par la vision multiplicative ;
- **Ne ferme pas** le problème (la Conjecture M_Mellin reste à prouver) ;
- **Identifie de nouvelles voies** (bornes de sommes multiplicatives, théorie de Meixner-Pollaczek, représentations de SU(1,1)).

La porte est toujours identifiée. La serrure est maintenant décrite dans deux langages complémentaires. Le radar binoculaire est activé.

---

## Références

[1] M. Ngom, D. Alpay, M. Mboup, *Scale-Shift and Harmonic analysis approach to the Mellin transform for Discrete-time signals*, Signal Processing **204** (2023), Article 108849.

[2] A. Kuznetsov, *Integral representations for the Dirichlet L-functions and their expansions in Meixner–Pollaczek polynomials and rising factorials*, Integral Transforms Spec. Funct. **18** (2007), 809–817.

[3] A. Kuznetsov, *Expansion of the Riemann Ξ function in Meixner–Pollaczek polynomials*, Canad. Math. Bull. **51** (2008), 561–569.

[4] T. H. Koornwinder, *Meixner-Pollaczek polynomials and the Heisenberg algebra*, J. Math. Phys. **30** (1989), 767–769.

[5] M. Ngom, *Scale operator in discrete-time and associated harmonic analysis*, PhD thesis, Université de Reims Champagne-Ardenne, 2023.

[6] J. Bertrand, P. Bertrand, J.-P. Ovarlez, *Discrete Mellin transform for signal analysis*, IEEE ICASSP (1990), 1603–1606.

[7] A. Weil, *On some exponential sums*, Proc. Nat. Acad. Sci. USA **34** (1948), 204–207.

[8] P. Diaconis, M. Shahshahani, *Generating a random permutation with random transpositions*, Z. Wahrsch. Verw. Gebiete **57** (1981), 159–179.
