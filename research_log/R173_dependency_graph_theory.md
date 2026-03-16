# R173 — LE GRAPHE DE DÉPENDANCE MULTIPLICATIF
## Vers une obstruction universelle par changement d'espace

**Date :** 15 mars 2026
**Philosophie :** Ne pas chercher un OUTIL pour prouver g(v) ≢ 0 mod d, mais changer l'ESPACE.

---

## 1. REFORMULATION MULTIPLICATIVE

### 1.1 L'équation fondamentale du cycle

Pour un cycle de longueur x visitant les impairs n₁ < n₂ < ... < nₓ :

```
3nᵢ + 1 = 2^{aᵢ} · n_{π(i)}     pour tout i = 1,...,x
```

où π est un cycle de longueur x sur {1,...,x}, et aᵢ = v₂(3nᵢ+1) ≥ 1.

**Contraintes automatiques :**
- Σ aᵢ = S (nombre total de pas)
- ∏(3nᵢ+1) = 2^S · ∏nᵢ (formule du produit)
- gcd(nᵢ, 6) = 1 pour tout i (les nᵢ sont impairs et non-divisibles par 3)

### 1.2 La contrainte 3-adique oubliée

**Lemme :** 3 ∤ nᵢ pour tout i.

*Preuve :* Si 3 | n_{π(i)}, alors 3 | (3nᵢ+1), mais 3nᵢ+1 ≡ 1 mod 3. Contradiction. ∎

C'est classique, mais CRUCIAL : tous les nᵢ vivent dans (Z/6Z)* = {1, 5} mod 6.

### 1.3 Le graphe de dépendance premier (GDF)

Pour chaque premier impair p ≥ 5, l'équation 3nᵢ+1 = 2^{aᵢ}·n_{π(i)} impose :

```
v_p(3nᵢ+1) = v_p(n_{π(i)})     (*)
```

car gcd(nᵢ, 3nᵢ+1) = gcd(nᵢ, 1) = 1, donc aucune puissance de p ne peut se compenser entre les deux côtés du même indice.

**Définition (GDF):** Le graphe de dépendance premier G_p a pour sommets {1,...,x} et une arête orientée i → π(i) étiquetée p chaque fois que p | 3nᵢ+1 (ce qui force p | n_{π(i)}).

**Propriété clé :** L'équation (*) crée un TRANSFERT de facteurs premiers le long du cycle π. Si p | n_{π(i)}, alors le facteur p vient UNIQUEMENT de 3nᵢ+1 (pas de nᵢ, car gcd(nᵢ, 3nᵢ+1) = 1).

## 2. L'OBSTRUCTION DE FERMETURE

### 2.1 Le circuit des facteurs premiers

Suivons un premier p à travers le cycle. Supposons p | nⱼ pour un certain j. Alors :
- p ∤ 3nⱼ+1 (car gcd(nⱼ, 3nⱼ+1)=1)
- Mais il faut p | n_{π(j)} pour "absorber" le p. D'où vient-il ?
- Il faut qu'il existe i tel que π(i) = j et p | 3nᵢ+1.
- 3nᵢ+1 ≡ 0 mod p signifie nᵢ ≡ -3⁻¹ mod p.

**Circuit de p :** p | nⱼ → il existe i=π⁻¹(j) avec nᵢ ≡ -3⁻¹ mod p → p | 3nᵢ+1 → p | n_{π(i)}=nⱼ ✓ (circuit fermé).

MAIS : d'où vient le facteur p dans nⱼ ?
- Il faut i'=π⁻¹(j) tel que p | 3n_{i'}+1, i.e., n_{i'} ≡ -3⁻¹ mod p.
- Et v_p(3n_{i'}+1) = v_p(nⱼ).

### 2.2 La contrainte de résidu

Pour chaque premier p | nⱼ :
- nⱼ ≡ 0 mod p
- n_{π⁻¹(j)} ≡ -3⁻¹ mod p (= (p-1)/3 · ... mod p, résidu fixé)

Donc les résidus mod p des nᵢ sont CONTRAINTS par le cycle π :
- Si p "entre" au sommet j (i.e., p | nⱼ), alors le sommet π⁻¹(j) doit avoir résidu -3⁻¹ mod p.
- Si p "sort" au sommet j (i.e., p | 3nⱼ+1), alors nⱼ ≡ -3⁻¹ mod p.

**Observation cruciale :** Un même nⱼ peut être divisible par PLUSIEURS premiers p₁, p₂, .... Chacun impose des contraintes CRT sur d'autres nᵢ.

### 2.3 La contrainte de taille couplée aux résidus

Voici où l'anti-corrélation intervient. Pour un cycle :
- n₁ < n₂ < ... < nₓ, tous impairs, copremiers à 3
- nᵢ ≡ rᵢ mod M (résidus déterminés par le réseau de premiers pour un certain module M)
- Σ log(3+1/nᵢ) = S·log 2 (contrainte archimédienne)

La clé : les résidus rᵢ mod M FIXENT les nᵢ à des progressions arithmétiques. Les nᵢ sont de la forme nᵢ = M·qᵢ + rᵢ avec qᵢ ≥ 0.

Pour x impairs DISTINCTS dans ces progressions satisfaisant la contrainte archimédienne : est-ce possible ?

## 3. L'ESPACE-PRODUIT : LA FIBRE ADÉLIQUE

### 3.1 Le changement d'espace

Au lieu de travailler dans Z (espace "plat"), travaillons dans l'espace-produit :

```
E = R × ∏_{p premier impair} Z_p
```

restreint aux éléments de Z (plongement diagonal). C'est l'approche ADÉLIQUE.

Un cycle (n₁,...,nₓ) est un point de Eˣ satisfaisant :
- **Composante archimédienne :** Σ log(3+1/nᵢ) = S·log 2
- **Composante p-adique (pour tout p ≥ 5) :** Σ v_p(3nᵢ+1) = Σ v_p(nᵢ)
- **Composante 2-adique :** Σ v₂(3nᵢ+1) = S
- **Composante 3-adique :** v₃(nᵢ) = 0 pour tout i
- **Intégrité :** nᵢ ∈ Z⁺ impair distinct

**Thèse :** Aucune de ces composantes n'est suffisante seule. Les ghost cycles montrent que les composantes p-adiques seules sont insuffisantes. Les bornes archimédiennes seules donnent des estimations mais pas de preuve. C'est la FIBRE — l'intersection de TOUTES les composantes — qui est vide.

### 3.2 Pourquoi la fibre est vide (argument heuristique)

Comptons les "degrés de liberté" vs les "contraintes" :

**Degrés de liberté :** x entiers nᵢ → x paramètres.

**Contraintes :**
1. La contrainte archimédienne (1 équation réelle)
2. Pour CHAQUE premier p divisant l'un des nᵢ ou l'un des 3nᵢ+1 : une relation de transfert
3. La permutation π doit être un cycle
4. Chaque nᵢ doit suivre la bonne branche du Collatz

Le nombre de contraintes (2) croît avec la TAILLE des nᵢ. Plus les nᵢ sont grands, plus ils ont de facteurs premiers, plus il y a de contraintes de transfert. Le système devient SUR-DÉTERMINÉ.

Pour les PETITS nᵢ : peu de facteurs premiers, peu de contraintes, mais la contrainte archimédienne est plus serrée (les termes log(3+1/nᵢ) sont plus grands, moins de flexibilité pour atteindre exactement S·log 2).

**C'est l'obstruction fondamentale :** les petits nᵢ sont bloqués par l'archimédien, les grands nᵢ sont bloqués par le réseau de dépendances premières. Il n'y a PAS de "zone Goldilocks".

### 3.3 Formalisation : le défaut de produit

Définissons le DÉFAUT de la fibre comme :

```
δ(n₁,...,nₓ) = |Σ log(3+1/nᵢ) - S·log 2| + Σ_p |v_p(∏(3nᵢ+1)) - v_p(2^S·∏nᵢ)|
```

Pour un cycle : δ = 0. La question est : δ > 0 pour tout (n₁,...,nₓ) avec x ≥ 2 ?

La première composante (archimédienne) est une fonction CONTINUE des nᵢ, donc elle peut être rendue aussi petite qu'on veut par un choix approprié de nᵢ réels. Mais la deuxième composante (p-adique) impose des contraintes DISCRÈTES.

L'interaction entre le continu et le discret est le cœur de la difficulté.

## 4. LA PISTE DU POLYNÔME CREUX

### 4.1 Reformulation polynomiale

L'équation g(v) ≡ 0 mod d se reformule comme : F(2) ≡ 0 mod (2^S - 3^x) où

```
F(X) = Σ_{j=0}^{x-1} 3^{x-1-j} · X^{e_j}
```

est un polynôme avec **exactement x termes non-nuls** de degré ≤ S-1.

### 4.2 La sparsité comme obstruction

F(X) a x termes mais vit dans un espace de polynômes de degré S-1 (dimension S). Le rapport x/S est BORNÉ :

```
x/S ∈ (1/2, 1/log₂3) ≈ (0.5, 0.63)
```

Donc F utilise entre 50% et 63% des "slots" possibles. Ce n'est PAS ultra-creux comme dans les résultats de Descartes/Khovanski (qui traitent x << degré).

MAIS : les termes non-nuls ont des COEFFICIENTS très structurés : ce sont les puissances de 3 en ordre décroissant, multipliées par des puissances de X croissantes.

### 4.3 Le résultant

Considérons le résultant :

```
R = Res_X(F(X), X^S - 3^x)
```

Si F(α) = 0 pour une racine α de X^S - 3^x, alors R = 0.

Or α = 3^{x/S} · ζ où ζ^S = 1 (racine S-ième de l'unité, complexe). L'évaluation en α :

```
F(α) = Σ 3^{x-1-j} · (3^{x/S} · ζ)^{e_j} = Σ 3^{x-1-j+x·e_j/S} · ζ^{e_j}
```

Pour F(α) = 0 : Σ 3^{x-1-j+x·e_j/S} · ζ^{e_j} = 0.

C'est une somme trigonométrique PONDÉRÉE. Les poids 3^{x-1-j+x·e_j/S} sont TOUS POSITIFS et d'ordres de grandeur très différents. Pour que la somme s'annule, il faut des annulations entre termes de même ordre de grandeur, ce qui est contraint par le fait que les poids forment une suite quasi-géométrique.

### 4.4 La conjecture du résultant

**Conjecture :** Pour tout x ≥ 2 et tout choix de positions e₀ < e₁ < ... < e_{x-1} avec S ∈ (x·log₂3, 2x] :

```
gcd(F(2), 2^S - 3^x) < 2^S - 3^x
```

Autrement dit, F(2) n'est JAMAIS divisible par d = 2^S - 3^x.

**Ce qui est connu :**
- Vérifié pour tout S ≤ 15 (computationnellement, R172)
- Pour x ≤ 68 (Simons-de Weger 2003, par bornes sur les nᵢ)
- Pour les mots de Christoffel (Knight 2025)

**Ce qui manque :** Un argument universel exploitant la STRUCTURE de F (anti-corrélation + sparsité).

## 5. NOUVELLE PISTE : L'ESPACE DES VALUATIONS

### 5.1 Le profil de valuation

Pour chaque premier p ≥ 5, définissons le PROFIL de valuation d'un x-uplet (n₁,...,nₓ) :

```
VP_p = (v_p(n₁), ..., v_p(nₓ), v_p(3n₁+1), ..., v_p(3nₓ+1))  ∈ Z_≥0^{2x}
```

**Contrainte de cycle :** Σ v_p(3nᵢ+1) = Σ v_p(nᵢ) (car ∏(3nᵢ+1) = 2^S · ∏nᵢ et p ∤ 2).

**Contrainte de coprimarité :** v_p(nᵢ) · v_p(3nᵢ+1) = 0 pour tout i (car gcd(nᵢ, 3nᵢ+1) = 1).

Donc VP_p vit sur l'UNION des faces de coordonnées de Z_≥0^{2x} (chaque paire (v_p(nᵢ), v_p(3nᵢ+1)) a au moins un zéro).

### 5.2 Le tenseur de contraintes

L'espace de tous les profils de valuation SIMULTANÉS pour tous les premiers est :

```
V = ∏_p VP_p  ⊂  ∏_p Z_≥0^{2x}
```

soumis à la contrainte que les (nᵢ) soient des entiers COHÉRENTS : les résidus mod p doivent être compatibles via le CRT.

**Observation :** La contrainte CRT n'est PAS un simple produit. Si nᵢ ≡ 0 mod p et nᵢ ≡ -3⁻¹ mod q, ces conditions sont compatibles (par CRT) mais fixent nᵢ mod pq. Plus il y a de premiers impliqués, plus nᵢ est contraint.

### 5.3 L'argument de sur-détermination

**Proposition (heuristique) :** Pour x ≥ 2 et S suffisamment grand, le système est sur-déterminé.

*Argument :* Chaque nᵢ a environ log(nᵢ)/log(log(nᵢ)) facteurs premiers. Pour un cycle, nᵢ ≥ 1 et nᵢ ≤ 3^x/4 (borne archimédienne). Pour le cycle hypothétique le plus petit :

- Les nᵢ sont O(3^x), donc ont O(x) facteurs premiers.
- Chaque facteur premier p de nᵢ crée une contrainte de transfert.
- Le nombre total de contraintes est O(x²) (x valeurs × O(x) facteurs chacune).
- Le nombre de degrés de liberté est x (les nᵢ eux-mêmes).

Pour x ≥ 2 : x² > x, donc le système est sur-déterminé. ∎ (heuristique)

**Le GAP :** Transformer cet argument heuristique en preuve rigoureuse.

## 6. LE CANDIDAT-FORMULE : L'INCOMPATIBILITÉ DU TRANSFERT

### 6.1 Énoncé

**Théorème visé :** Pour tout x ≥ 2, tout S ∈ (x·log₂3, 2x], et toute permutation cyclique π sur {1,...,x}, il n'existe pas de x-uplet (n₁,...,nₓ) d'entiers impairs distincts copremiers à 3 tels que :

```
3nᵢ + 1 = 2^{aᵢ} · n_{π(i)}     pour tout i, avec Σ aᵢ = S.
```

### 6.2 Preuve partielle par le "graphe de Steiner"

Pour x = 2 : 3n₁+1 = 2^{a₁}·n₂ et 3n₂+1 = 2^{a₂}·n₁.

Éliminant : 3(3n₁+1)/2^{a₁} + 1 = 2^{a₂}·n₁, donc 3(3n₁+1) + 2^{a₁} = 2^{a₁+a₂}·n₁.

9n₁ + 3 + 2^{a₁} = 2^S · n₁, donc n₁(2^S - 9) = 3 + 2^{a₁}.

Pour S ≥ 4 : 2^S - 9 > 0, donc n₁ = (3 + 2^{a₁})/(2^S - 9).

Avec a₁ + a₂ = S et a₁ ≥ 1, a₂ ≥ 1 : a₁ ∈ {1,...,S-1}.

Pour chaque a₁ : n₁ = (3 + 2^{a₁})/(2^S - 9).

On vérifie que pour S=4 : d=7, n₁ = (3+2^{a₁})/7. a₁=1: 5/7 ✗. a₁=2: 7/7=1, n₂=(3+1)/2^2 = 1. MAIS n₁=n₂=1 → non distinct !

Pour S=5 : d=23. n₁=(3+2^{a₁})/23. a₁=1:5/23 ✗, a₂=2:7/23 ✗, a₃=3:11/23 ✗, a₄=4:19/23 ✗.

Aucune solution entière. On peut montrer que (3+2^{a₁}) < 2^S - 9 pour a₁ ≤ S-2 (car 2^{a₁} ≤ 2^{S-2} < 2^S - 9 pour S ≥ 5), et pour a₁=S-1 : 3+2^{S-1} vs 2^S-9 = 2·2^{S-1}-9, donc n₁ = (3+2^{S-1})/(2·2^{S-1}-9) < 1 pour S ≥ 5. Donc n₁ < 1, pas un entier positif.

**Ceci prouve x=2 est impossible pour S ≥ 5.** Et S=4 donne seulement la solution dégénérée n₁=n₂=1. Et S=3 est impossible car 2^3=8 < 9=3^2. ✓

### 6.3 Pour x = 3 et au-delà

Le système devient :
```
3n₁+1 = 2^{a₁}·n_{π(1)}
3n₂+1 = 2^{a₂}·n_{π(2)}
3n₃+1 = 2^{a₃}·n_{π(3)}
```

L'élimination donne une équation en n₁ seul :
n₁·(2^S - 3^3) = expression en (a₁, a₂, a₃)

Plus précisément, en itérant la substitution :

n_{π(1)} = (3n₁+1)/2^{a₁}
n_{π²(1)} = (3·(3n₁+1)/2^{a₁}+1)/2^{a₂} = (9n₁+3+2^{a₁})/(2^{a₁+a₂})
n₁ = n_{π³(1)} = (3·(9n₁+3+2^{a₁})/(2^{a₁+a₂})+1)/2^{a₃}
= (27n₁ + 9 + 3·2^{a₁} + 2^{a₁+a₂}) / 2^S

Donc : 2^S · n₁ = 27n₁ + 9 + 3·2^{a₁} + 2^{a₁+a₂}

n₁ · (2^S - 27) = 9 + 3·2^{a₁} + 2^{a₁+a₂} = g(v)

C'est exactement n₁ = g(v)/d avec d = 2^S - 3^3 ! On retrouve la formule standard.

**Le numérateur g(v) = 3^{x-1}·2^0 + 3^{x-2}·2^{a₁} + ... + 3^0·2^{a₁+...+a_{x-1}}** (pour la permutation cyclique canonique π = (1 2 ... x)).

## 7. L'IDÉE UNIFICATRICE : LE PRODUIT TENSORIEL DES CONTRAINTES

### 7.1 Chaque premier p fournit un quotient

Pour chaque premier p ≥ 5 divisant d = 2^S - 3^x :

L'équation g(v) ≡ 0 mod p est une condition sur les positions (e₀,...,e_{x-1}).

Dans F_p[X] : F(X) = Σ 3^{x-1-j} X^{e_j} doit satisfaire F(2) ≡ 0 mod p.

Puisque 2^S ≡ 3^x mod p (car p | d), le sous-groupe ⟨2⟩ dans F_p* a un ordre ord_p(2) divisant lcm(S, ord_p(3)).

### 7.2 L'obstruction de compatibilité CRT

Pour que g(v) ≡ 0 mod d, il faut g(v) ≡ 0 mod p pour TOUT p | d.

Chaque condition g(v) ≡ 0 mod p restreint les positions (e₀,...,e_{x-1}) à un sous-ensemble de C(S,x).

**La question :** L'INTERSECTION de tous ces sous-ensembles (pour tous p | d) est-elle vide ?

C'est le CRT sur l'espace des mots ! L'espace n'est pas Z (un anneau), c'est l'ensemble des mots binaires — un objet COMBINATOIRE.

### 7.3 La sparsité du CRT combinatoire

Pour un premier p typique divisant d : environ C(S,x)/p des vecteurs satisfont g(v) ≡ 0 mod p (si g est "bien répartie" mod p).

Le nombre de premiers divisant d est environ ω(d) ~ log d / log log d.

La probabilité qu'un vecteur satisfasse TOUTES les conditions mod p est environ 1/d (par CRT).

Puisque C(S,x)/d ~ C(S,x)/(2^S - 3^x), et C(S,x) ≈ 2^{S·H(x/S)} (entropie binaire) :

Si H(x/S) > (S-log₂3^x)/S = 1 - x·log₂3/S, alors "beaucoup" de multiples de d sont attendus par l'heuristique probabiliste.

Or x/S ∈ (1/2, 1/log₂3), et H(x/S) ∈ (0.97, 1) pour ces valeurs. Et 1 - x·log₂3/S est petit (puisque S ≈ x·log₂3). Donc C(S,x) >> d, et l'heuristique prédit de NOMBREUSES solutions.

**MAIS l'heuristique échoue** parce que g n'est PAS uniformément distribuée mod d ! C'est PRÉCISÉMENT l'anti-corrélation qui biaise la distribution.

## 8. CONCLUSION ET GAP IDENTIFIÉ

### 8.1 Ce qui est prouvé

1. x = 1 : seul cycle trivial {1} (Steiner 1977)
2. x = 2 : impossible (§6.2 ci-dessus, classique)
3. x ≤ 68 : impossible (Simons-de Weger 2003, bornes computationnelles)
4. Mots de Christoffel : impossible (Knight 2025)

### 8.2 Ce qui manque pour une preuve universelle

**Le gap précis :** Montrer que pour x ≥ 3 et S ∈ (x·log₂3, 2x], le numérateur

```
g(v) = Σ_{j=0}^{x-1} 3^{x-1-j} · 2^{e_j}     (e₀ < e₁ < ... < e_{x-1})
```

n'est JAMAIS un multiple de d = 2^S - 3^x.

### 8.3 La piste la plus prometteuse

**L'argument du "poids déséquilibré" :**

Dans g(v) mod d, le terme j=0 contribue 3^{x-1}·2^{e₀}. Pour e₀ = 0 : c'est 3^{x-1} ≡ 3^{x-1} mod d. Pour ce terme seul d'être un multiple de d, il faudrait d | 3^{x-1}, impossible car d = 2^S - 3^x > 3^{x-1} pour S ≥ x·log₂3 + 1.

Les termes suivants ajoutent des quantités de PLUS EN PLUS PETITES (en puissances de 3) mais de plus en plus grandes (en puissances de 2). L'anti-corrélation fait que ces ajouts ne peuvent PAS compenser le terme dominant pour atteindre un multiple de d.

**Formaliser ceci est LE défi restant.** Il faut montrer que la "cascade" des termes 3^{x-1-j}·2^{e_j} ne peut pas construire un multiple de d, malgré la richesse combinatoire des choix de positions.

### 8.4 Direction de travail R174

Développer l'argument du poids déséquilibré via la VALUATION 3-adique de g(v) :

```
v₃(g(v)) = min_j v₃(3^{x-1-j} · 2^{e_j}) = min_j (x-1-j)  [car v₃(2^{e_j}) = 0]
```

Donc v₃(g(v)) = 0 (le terme j=x-1 a v₃ = 0).

Pour g(v) ≡ 0 mod d : il faut d | g(v). Or v₃(d) = v₃(2^S - 3^x) = 0 (car 2^S ≡ 2^S mod 3, et 3^x ≡ 0 mod 3, donc d ≡ 2^S mod 3 ≡ ±1 mod 3). ✓ Pas de contradiction 3-adique.

Mais pour les premiers p | d : la condition g(v) ≡ 0 mod p COUPLÉE à la structure anti-corrélée de g pourrait donner une obstruction.

**Idée clé pour R174 :** Étudier F(X) mod (X^S - 3^x) dans F_p[X] pour les premiers p | d. Montrer que l'évaluation F(2) mod p est BIAISÉE (non-uniformément distribuée) à cause de la structure multiplicative de F.
