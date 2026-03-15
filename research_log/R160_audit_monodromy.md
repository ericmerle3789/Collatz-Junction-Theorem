# R160 — AUDIT LOGIQUE ULTRA-COURT : CONSÉQUENCES QUANTITATIVES EXACTES DE LA GRANDE MONODROMIE

**Date** : 15 mars 2026
**Type** : Audit logique — rigueur mathématique absolue
**Question** : G_geom = SL(r-1) (supposé prouvé) => quelles conséquences quantitatives EXACTES pour le verrou ?

---

## AXE 1 : LA CHAÎNE LOGIQUE G_geom → Deligne → borne

### 1.1 Quel objet géométrique exactement ?

Le rapport Agent 3 (R159) définit un "faisceau local F de rang n = r-1 sur G_m/F_p" associé à la famille de sommes de caractères :

$$T(\chi) = \sum_{a=1}^{r-1} \chi(1 - 2^a \bmod p)$$

où chi parcourt les caractères multiplicatifs de F_p*.

**Problème critique** : cette définition est INFORMELLE. Pour parler de monodromie géométrique, il faut un faisceau l-adique sur une courbe (ou un schéma) sur un corps fini. L'objet standard serait :
- une variété de base (typiquement G_m = Spec(F_p[t, t^{-1}]))
- un faisceau l-adique F sur cette base
- dont les traces de Frobenius aux points fermés reproduisent T(chi)

**Le pont précis** : Pour un caractère chi de F_p* d'ordre m, on peut l'identifier au point t = zeta_m (racine primitive m-ème de l'unité) d'un faisceau de Kloosterman généralisé sur G_m. Mais la somme T(chi) n'est PAS une somme de Kloosterman standard. C'est une somme de la forme :

$$T(\chi) = \sum_{a=1}^{r-1} \chi(c_a), \quad c_a = 1 - 2^a \bmod p$$

où les points c_a sont FIXÉS (dépendent de p, pas d'un paramètre continu). Ceci est la trace de chi sur un ensemble fini de r-1 points de F_p*. Ce n'est pas la trace de Frobenius d'un faisceau au sens standard de Katz.

**VERDICT AXE 1.1** : L'objet géométrique sous-jacent n'est PAS clairement défini. Le rapport Agent 3 affirme "F est un local system de rang r-1 sur G_m" sans construire ce faisceau. Pour que la monodromie ait un sens, il faudrait identifier F comme un faisceau l-adique sur une courbe avec un paramètre CONTINU, pas une collection discrète de valeurs.

### 1.2 Le théorème d'équidistribution de Deligne

Le théorème de Deligne (SGA 4½, Théorème des coefficients) dit : soit F un faisceau l-adique lisse de rang n sur une courbe lisse U/F_q, pur de poids w. Alors les Frobenius conjugacy classes {Frob_x : x point fermé de degré 1} s'équidistribuent dans le groupe compact maximal de G_geom selon la mesure de Haar, quand q -> infini.

**Ce que cela implique** : les valeurs propres normalisées de Frob_x (divisées par q^{w/2}) s'équidistribuent selon la mesure de Sato-Tate du groupe G_geom.

**Ce que cela N'implique PAS** : une borne uniforme sur les traces individuelles. L'équidistribution est un énoncé ASYMPTOTIQUE (q -> infini) et STATISTIQUE (la plupart des traces, pas toutes).

### 1.3 La borne de Deligne pour les traces

La borne de Deligne (Weil II) pour un faisceau pur de poids w et rang n donne :
$$|Tr(Frob_x, F)| \leq n \cdot q^{w/2}$$

C'est une borne par le RANG du faisceau. Si F a rang r-1, on obtient |Tr| ≤ (r-1) · q^{1/2}. Or dans notre contexte, si on pouvait identifier T(chi) comme une trace de Frobenius, q = p, et la borne serait :
$$|T(\chi)| \leq (r-1) \cdot \sqrt{p}$$

C'est PIRE que la borne triviale |T(chi)| ≤ r-1 (puisque sqrt(p) >> 1). La borne de Deligne individuelle est INUTILE ici.

### 1.4 Pont entre monodromie et bornes sur S_H(t) ?

**Question** : existe-t-il un théorème publié qui déduit, de G_geom = SL(n) pour un faisceau, une borne uniforme sur les sommes de caractères restreintes à un sous-groupe multiplicatif de taille log p ?

**Réponse** : NON. La littérature de Katz (ESDE, Gauss Sums, Moments, Monodromy, Convolution and Equidistribution) traite de :
- Bornes pour les sommes COMPLÈTES (sur tout F_p) via Weil II
- Équidistribution des traces de Frobenius quand p varie (famille verticale) ou quand le caractère varie (famille horizontale)
- Moments de familles de sommes de caractères

Aucun de ces résultats ne fournit une borne POINTWISE pour une somme sur un sous-groupe de taille logarithmique.

Le résultat le plus proche est Katz, ESDE 8.14.4 ("Big Monodromy") : si G_geom = SL(n) ou Sp(n), alors les moments de la famille {Tr(Frob_chi, F)} convergent vers ceux de la mesure de Sato-Tate correspondante. Ceci donne des bornes sur les MOMENTS MOYENNÉS (sur chi), pas sur les valeurs individuelles.

**VERDICT AXE 1** : La chaîne G_geom = SL(r-1) => |S_H(t)| ≤ C·sqrt(r) est **BRISÉE à chaque maillon** :
1. L'objet géométrique n'est pas rigoureusement construit
2. Même construit, Deligne donne une borne (r-1)·sqrt(p), inutile
3. L'équidistribution est asymptotique/statistique, pas pointwise
4. Aucun théorème publié ne fait le pont vers des bornes sur sous-groupes de taille log p

---

## AXE 2 : LA NATURE EXACTE DE S_H(t)

### 2.1 Définition

Le rapport R159 utilise DEUX sommes :

- **S_H(t)** (rapport R159_report.txt) : $S_H(t) = \sum_{h \in H} e_p(t \cdot (h-1))$, somme d'exponentielles ADDITIVES sur le sous-groupe multiplicatif H = <2>.

- **T(chi)** (rapport Agent 3) : $T(\chi) = \sum_{a=1}^{r-1} \chi(1-2^a)$, somme de caractères MULTIPLICATIFS évaluée sur l'ensemble {1-2^a}.

Ce sont deux objets DIFFÉRENTS, liés par la dualité de Fourier. S_H(t) est une somme additive sur H (sous-groupe multiplicatif). T(chi) est une somme multiplicative sur un ensemble de translations.

### 2.2 S_H(t) est-elle une trace de Frobenius ?

**NON**, pas au sens standard. Une trace de Frobenius d'un faisceau l-adique F au point x d'une courbe U/F_q est :
$$Tr(Frob_x, F_{\bar{x}})$$

La somme S_H(t) = sum_{h in H} e_p(t(h-1)) est une somme partielle de la transformation de Fourier additive, restreinte au sous-groupe H. Ce n'est pas la somme complète sum_{x in F_p} e_p(t*f(x)) qui apparaît dans les sommes de Weil.

Pour les sommes COMPLÈTES sum_{x in F_p*} chi(x) e_p(tx), on obtient des sommes de Gauss, et celles-ci SONT des traces de Frobenius du faisceau de Kloosterman. Mais la restriction à H = <2> brise cette identification.

### 2.3 Rapport avec les faisceaux de Katz

Les faisceaux étudiés par Katz dans ESDE incluent :
- Faisceaux de Kloosterman Kl_n(psi; chi_1, ..., chi_n) : sommes sur n variables
- Faisceaux hypergeométriques Hyp(psi; chi_1,...,chi_n; rho_1,...,rho_m)
- Convolutions de faisceaux de rang 1

Notre somme S_H(t) ne rentre dans AUCUNE de ces familles. La restriction à un sous-groupe multiplicatif de taille r = ord_p(2) est une opération qui n'a PAS d'analogue naturel dans le formalisme des faisceaux l-adiques. On peut écrire :

$$S_H(t) = \sum_{j=0}^{r-1} e_p(t(2^j - 1)) = \sum_{j=0}^{r-1} \psi(t \cdot 2^j) \cdot \psi(-t)$$

où psi(x) = e_p(x). Ceci est une somme de r termes d'un faisceau d'Artin-Schreier L_psi(tx) évalué aux r points 2^0, 2^1, ..., 2^{r-1}. C'est une SOMME FINIE DE SECTIONS, pas une trace de Frobenius.

### 2.4 La littérature sur les sommes exponentielles restreintes aux sous-groupes

Les résultats connus pour $\sum_{x \in H} e_p(x)$ où H est un sous-groupe multiplicatif de F_p* :

- **Si |H| > p^{1/2+epsilon}** : borne non-triviale par Pólya-Vinogradov / Weil (somme complète - reste)
- **Si |H| > p^{1/4+epsilon}** : borne non-triviale par Burgess (1963)
- **Si |H| > p^{delta}, delta > 0 fixé** : borne non-triviale par Bourgain-Glibichuk-Konyagin (2006) sum-product
- **Si |H| = O(log p)** : AUCUNE borne non-triviale connue

Ce gap est FONDAMENTAL et bien connu dans la communauté. Il n'existe pas de résultat publié qui franchit la barrière |H| = p^{o(1)}.

**VERDICT AXE 2** : S_H(t) n'est PAS une trace de Frobenius d'un faisceau l-adique standard. C'est une somme partielle d'exponentielles additives restreinte à un sous-groupe multiplicatif de taille logarithmique. Cette classe de sommes se situe SOUS tous les seuils connus de la littérature. Le formalisme de la monodromie géométrique ne s'y applique pas directement.

---

## AXE 3 : CE QUE LA MONODROMIE DONNE VRAIMENT

### 3.1 Borne individuelle

Même si G_geom = SL(r-1) pour un faisceau F de rang r-1, Deligne (Weil II) donne :
$$|Tr(Frob_p, F)| \leq (r-1) \cdot p^{w/2}$$

Pour poids w = 0 (si F est pur de poids 0) : |Tr| ≤ r-1. C'est la borne triviale.
Pour poids w = 1 : |Tr| ≤ (r-1) · sqrt(p). C'est PIRE que trivial pour notre usage.

En AUCUN cas la monodromie ne donne |Tr| ≤ C·sqrt(r).

### 3.2 Équidistribution et Sato-Tate

Si G_geom = SL(r-1), l'équidistribution de Deligne dit que les TRACES NORMALISÉES Tr(Frob)/sqrt(r-1) s'équidistribuent selon la mesure de Sato-Tate de SL(r-1) quand le paramètre varie.

Pour SL(n), la mesure de Sato-Tate est celle des traces de matrices aléatoires unitaires de déterminant 1. Les traces normalisées ont :
- Variance 1
- Kurtosis M4/M2^2 = 2 (gaussien complexe)

Cela signifie que la PLUPART des traces sont de taille O(sqrt(r)). Mais le MAXIMUM sur p traces peut atteindre sqrt(r · log p). L'équidistribution ne donne PAS de borne sur le max.

### 3.3 Bornes sur les moments (Katz, ESDE 8.14.4)

Le théorème de Katz sur la "Big Monodromy" (ESDE, Chapitre 8) dit :

**Théorème** (informel) : Soit F un faisceau lisse sur U/F_q, pur de poids w, avec G_geom = SL(n) (resp. Sp(n)). Alors pour tout entier k >= 1 :
$$\frac{1}{|U(F_q)|} \sum_{x \in U(F_q)} |Tr(Frob_x, F)|^{2k} = M_{2k}(SL(n)) \cdot (r-1)^k + O(q^{-1/2})$$

où M_{2k} est le 2k-ème moment de la distribution de Sato-Tate.

**Ce que cela donne** :
- Le second moment : (1/|U|) sum |Tr|^2 = (r-1) + O(q^{-1/2}). C'est Plancherel.
- Le quatrième moment : (1/|U|) sum |Tr|^4 = 2(r-1)^2 + O(q^{-1/2}). Cela confirme le kurtosis = 2.
- Tous les moments PAIRS convergent vers ceux de la distribution gaussienne complexe de variance r-1.

**Ce que cela NE donne PAS** : une borne sur max_x |Tr(Frob_x, F)|. Les moments ne contrôlent pas le maximum. Par Markov, le k-ème moment donne :

$$\Pr[|Tr| > \lambda \sqrt{r}] \leq M_{2k} / \lambda^{2k}$$

Mais optimiser sur k ne donne qu'une borne sous-gaussienne, pas une borne DÉTERMINISTE.

### 3.4 Résumé : ce que la monodromie donne exactement

En supposant G_geom = SL(r-1) PROUVÉ :

| Résultat | Type | Utile pour le verrou ? |
|----------|------|:----------------------:|
| E[|T(chi)|^2] = r-1 | Moyenne exacte | NON (déjà connu par Plancherel) |
| E[|T(chi)|^4] = 2(r-1)^2 | 4ème moment | NON (ne borne pas le max) |
| Distribution Sato-Tate | Asymptotique en p | NON (ne borne pas le max) |
| |T(chi)| ≤ (r-1)·sqrt(p) | Borne individuelle Deligne | NON (pire que trivial) |
| |T(chi)| ≤ C·sqrt(r) pour tout chi | Borne pointwise | **NON DÉDUIT** |

**VERDICT AXE 3** : La monodromie G_geom = SL(r-1), même prouvée, donne des résultats MOYENNÉS (moments, équidistribution) mais AUCUNE borne pointwise exploitable. La borne individuelle de Deligne est pire que triviale. Le passage de la distribution à une borne max nécessite un outil SUPPLÉMENTAIRE que la monodromie seule ne fournit pas.

---

## AXE 4 : LA QUESTION sqrt(r) VS sqrt(r · log p)

### 4.1 Ce que le programme NÉCESSITE

Pour le verrou Bloc 3 (k=22..41), le programme a besoin que N_0(d) = 0, ce qui se réduit (via les rounds R85-R98) à borner des PRODUITS de sommes de la forme :

$$\prod_{j} S_H(s \cdot 3^j)$$

Pour que le produit soit petit, il faut que CHAQUE facteur soit petit SIMULTANÉMENT. Si on a k facteurs et que chacun est borné par B, le produit est borné par B^k.

Pour que la contribution totale soit < 1, il faut (grossièrement) :
$$B^k \cdot (\text{nombre de termes}) < d/C$$

Le programme vise |S_H(s)| ≤ C_0 · sqrt(r) pour une constante universelle C_0.

### 4.2 Ce qui est observé

Le rapport R159 (731 premiers) montre :
- max|S_H(t)|/sqrt(r) = 4.67 (pour p=14449, r=84, index=172)
- Le ratio CROÎT comme sqrt(2 · log((p-1)/r))
- Pour p ~ 2^r (notre régime), cela donne max|S_H|/sqrt(r) ~ sqrt(2r) => max|S_H| ~ r

### 4.3 Le facteur sqrt(log p) est-il éliminable ?

**Par un argument de monodromie ?** NON. Comme établi en Axe 3, la monodromie donne les moments mais pas le max. Le facteur sqrt(log p) est le facteur de MAXIMUM de ~p/r variables gaussiennes, et c'est un phénomène de probabilités extrêmes, pas de géométrie algébrique.

**Par un argument de moments ?** NON. Les moments de la distribution gaussienne complexe NE bornent PAS le maximum. Par la borne de Markov optimisée :
$$\max |T| \lesssim \sqrt{r \cdot \log(p/r)}$$
Ce qui est exactement la borne observée. Le facteur log est OPTIMAL pour des variables gaussiennes.

**Par un large sieve ?** Le grand crible donne :
$$\sum_{t} |S_H(t)|^2 \leq (p + r - 1) \cdot r$$
Ceci est une borne L^2, pas L^infini. Le passage L^2 -> L^infini introduit un facteur sqrt(p/r), qui est PIRE.

### 4.4 sqrt(r · log p) suffit-il pour le verrou ?

Calcul explicite pour k=22, p typique :
- d(22) a un plus grand facteur premier p = 425,525,537
- r = ord_p(2) (typiquement r ~ log_2(p) ~ 29)
- La borne sqrt(r · log p) ~ sqrt(29 · 29) ~ 29 ~ r

Donc |S_H(t)| ~ r, et le "cancellation" est NULLE : |S_H|/r ~ 1.

Pour le produit de k = 22 facteurs :
$$\prod_{j=0}^{k-1} |S_H(s \cdot 3^j)| \sim r^k$$

Or on a besoin que cette quantité soit BIEN PLUS PETITE que p (pour obtenir N_0 = 0 après sommation). Puisque r ~ log p, on a r^k = (log p)^k, et pour k = 22 :
$$(log p)^{22} \sim 29^{22} \sim 10^{32}$$

Ceci doit être comparé à p ~ 4 · 10^8. Le produit EXPLOSE par rapport à p.

**Même avec la borne C · sqrt(r)** (C constante), le produit serait :
$$(C \sqrt{r})^{22} = C^{22} \cdot r^{11} \sim C^{22} \cdot 29^{11} \sim C^{22} \cdot 10^{16}$$

Pour C = 1 : 10^{16} >> 4 · 10^8 = p. TOUJOURS trop grand.

**Observation critique** : Même la borne IDÉALE |S_H(t)| ≤ sqrt(r) est INSUFFISANTE pour le produit. Il faudrait |S_H(t)| ≤ r^{1/2 - epsilon} avec epsilon > 1/(2k) pour que le produit soit borné par r^{k(1/2-epsilon)} = r^{k/2 - k·epsilon} et que k·epsilon > 1/2 assure une puissance de r qui compense.

Non -- recalculons plus soigneusement. Le verrou tel que formulé dans les rounds antérieurs demande |S_H(s)| ≤ C·sqrt(r) dans le contexte d'une SOMMATION sur s (pas un produit pur). Revoyons :

La formule de N_0 implique (d'après R85-R87) :
$$N_0(p) = \frac{1}{p} \sum_{s=0}^{p-1} \prod_{j=0}^{k-1} \sigma_j(s)$$

où sigma_j(s) sont des sommes liées à S_H. Le terme s=0 donne la contribution principale C/p, et les termes s != 0 doivent être bornés en valeur absolue. La borne sur |sum_{s!=0}| requiert que les produits prod sigma_j(s) se cancellent en sommant sur s.

Donc la question n'est pas "chaque produit est petit" mais "la SOMME des produits est petite". C'est ici que la monodromie pourrait contribuer si elle assurait la décorrélation entre les sigma_j pour différents j. Mais la monodromie contrôle le comportement quand chi ou p VARIE, pas quand le twist 3^j varie.

**VERDICT AXE 4** : Le facteur sqrt(log p) n'est PAS éliminable par les outils connus. De plus, même la borne sqrt(r) est probablement insuffisante pour le verrou car le produit de k facteurs de taille sqrt(r) dépasse p. La structure réelle du verrou est une SOMME de produits corrélés, et ni la borne pointwise ni la monodromie ne suffisent pour la traiter.

---

## AXE 5 : L'IDENTITÉ PRODUIT

### 5.1 L'identité

Observée numériquement (tous les premiers testés) :
$$\prod_{a=1}^{r-1} (1 - 2^a) \equiv r \pmod{p}$$

où r = ord_p(2).

### 5.2 Vérification théorique

Considérons le polynôme :
$$P(x) = \prod_{a=0}^{r-1} (x - 2^a) = x^r - 1 \quad \text{(dans } F_p[x] \text{)}$$

Non -- ce n'est pas correct. Le polynôme dont les racines sont les éléments de H = {2^0, 2^1, ..., 2^{r-1}} est le polynôme minimal du sous-groupe cyclique d'ordre r dans F_p*. Puisque H est le noyau de l'application x -> x^{(p-1)/r} - 1 quand (p-1)/r est entier (ce qui est le cas car r | p-1), on a :

$$\prod_{a=0}^{r-1} (x - 2^a) = \frac{x^{p-1} - 1}{\prod_{g \notin H} (x - g)}$$

Plus simplement, les éléments de H sont les racines de $x^r - 1 = 0$ dans F_p (puisque pour h in H, h^r = (2^a)^r = 2^{ar} = 1 mod p). Donc :
$$\prod_{a=0}^{r-1} (x - 2^a) = x^r - 1$$

Vérifions : le polynôme $x^r - 1$ a exactement r racines dans F_p, qui sont les éléments d'ordre divisant r dans F_p*. Si le sous-groupe d'ordre r dans F_p* est exactement H = <2>, alors oui, les racines de x^r - 1 sont précisément {2^0, 2^1, ..., 2^{r-1}}.

Maintenant, calculons le produit demandé :
$$\prod_{a=1}^{r-1} (1 - 2^a)$$

En posant x = 1 dans $x^r - 1 = \prod_{a=0}^{r-1}(x - 2^a)$ :
$$1^r - 1 = \prod_{a=0}^{r-1} (1 - 2^a)$$
$$0 = (1 - 2^0) \cdot \prod_{a=1}^{r-1} (1 - 2^a) = (1 - 1) \cdot \prod_{a=1}^{r-1}(1 - 2^a) = 0$$

C'est une tautologie (0 = 0). On ne peut pas extraire le produit car le facteur a=0 est nul.

Pour contourner cela, prenons la dérivée. On a $f(x) = x^r - 1 = \prod_{a=0}^{r-1}(x - 2^a)$, donc :
$$f'(x) = r \cdot x^{r-1} = \sum_{a=0}^{r-1} \prod_{b \neq a} (x - 2^b)$$

En évaluant à x = 1 = 2^0 :
$$r \cdot 1^{r-1} = \prod_{b=1}^{r-1} (1 - 2^b)$$

Donc :
$$\boxed{\prod_{a=1}^{r-1} (1 - 2^a) = r \pmod{p}}$$

**L'identité est PROUVÉE**. C'est une conséquence directe de la dérivée du polynôme cyclotomique x^r - 1 évaluée à la racine x = 1.

### 5.3 Conséquences pour S_H ou le verrou

L'identité $\prod(1 - 2^a) = r \bmod p$ donne le DÉTERMINANT de l'ensemble des points {c_a = 1 - 2^a}. En termes du faisceau hypothétique F, cela fixe det(F).

Conséquence pour le verrou : **AUCUNE directe**. L'identité est une propriété du PRODUIT des c_a, alors que S_H concerne une SOMME de e_p(t·c_a). Le produit et la somme sont des objets algébriquement indépendants. L'identité ne contraint ni |S_H(t)|, ni la distribution de S_H.

**Intérêt mathématique** : l'identité est élégante et potentiellement utile pour d'autres questions (par exemple, le déterminant du faisceau, ou des identités de type résultant). Mais elle ne mord pas sur le verrou.

**VERDICT AXE 5** : L'identité $\prod_{a=1}^{r-1}(1-2^a) \equiv r \pmod{p}$ est PROUVÉE (triviale via la dérivée de x^r - 1). Elle n'a AUCUNE conséquence pour le verrou V_SQRT_CANCEL.

---

## AXE 6 : VERDICT — CE QUI EST RÉELLEMENT EXPLOITABLE

### 6.1 G_geom = SL(r-1) implique-t-il |S_H(t)| ≤ C·sqrt(r) ?

**NON.**

Raisons :
1. L'objet géométrique n'est pas rigoureusement construit (S_H n'est pas une trace de Frobenius standard)
2. Même si un faisceau F existait avec G_geom = SL(r-1), la borne de Deligne donne |Tr(Frob)| ≤ (r-1)·q^{w/2}, pas C·sqrt(r)
3. L'équidistribution donne la distribution ASYMPTOTIQUE des traces, pas une borne déterministe
4. Le maximum de ~p/r traces gaussiennes de variance r croît comme sqrt(r·log(p/r)), et aucun outil de monodromie n'élimine le facteur log
5. Numériquement, max|S_H|/sqrt(r) = 4.67 et CROÎT, confirmant que la borne sqrt(r) est fausse

### 6.2 G_geom implique-t-il une borne MOYENNÉE utile ?

**OUI, mais elle est DÉJÀ CONNUE sans la monodromie.**

La borne moyennée est :
$$\frac{1}{p-1} \sum_{t=1}^{p-1} |S_H(t)|^2 = r - \frac{r(r-1)}{p-1} \approx r$$

Ceci est l'identité de Plancherel / orthogonalité des caractères. Elle est prouvable de manière élémentaire (2 lignes), sans aucune monodromie.

La monodromie ajoute les MOMENTS SUPÉRIEURS :
$$\frac{1}{p-1} \sum |S_H(t)|^{2k} \approx M_{2k}(CUE) \cdot r^k$$

Ce sont des informations intéressantes sur la DISTRIBUTION mais pas sur le MAXIMUM, et elles ne sont pas nécessaires au programme.

### 6.3 La borne moyennée suffit-elle pour le verrou ?

**NON.**

Le verrou nécessite de borner :
$$\left| \sum_{s=1}^{p-1} \prod_{j=0}^{k-1} \sigma_j(s) \right|$$

La borne de Cauchy-Schwarz donne :
$$\left| \sum_s \prod_j \sigma_j(s) \right|^2 \leq (p-1) \sum_s \left| \prod_j \sigma_j(s) \right|^2$$

Pour borner le membre droit, il faudrait connaître la corrélation entre les sigma_j pour des twists géométriques 3^j différents. C'est exactement le problème du PRODUIT CORRÉLÉ (R85-R87, PO-R87), qui est un problème ouvert de théorie analytique des nombres.

La borne moyennée donne sum |S_H|^2 ~ r·p, mais le produit de k termes produit (r·p)^{k/2} / p = r^{k/2} · p^{k/2 - 1}, qui DIVERGE pour k >= 3.

### 6.4 Résultat théorique publié donnant |S_H| ≤ sqrt(r) ?

**IL N'EN EXISTE PAS.**

Pour les sommes exponentielles sur des sous-groupes multiplicatifs de taille |H| ~ log p :
- Aucun résultat dans Katz (1988, 2001, 2012)
- Aucun résultat dans Bourgain-Glibichuk-Konyagin (2006) — seuil p^delta
- Aucun résultat dans les surveys de Shparlinski (2013, 2019)
- Aucun résultat dans Kowalski (2024)
- Le problème est reconnu comme OUVERT dans la communauté

La raison fondamentale : les outils existants (Weil, Burgess, sum-product, monodromie) nécessitent tous que |H| soit une PUISSANCE POSITIVE de p, pas logarithmique.

### 6.5 Valeur RÉELLE de la piste monodromie

| Apport | Valeur | Impact sur le verrou |
|--------|--------|:--------------------:|
| Confirmation numérique que S_H "se comporte bien en moyenne" | Informatif | NUL (Plancherel suffit) |
| Conjecture G_geom = SL(r-1) | Informatif | NUL (ne donne pas de borne pointwise) |
| Distribution gaussienne de S_H | Informatif | NÉGATIF (confirme que max ~ sqrt(r·log p)) |
| Identité produit Prod(1-2^a) = r | Prouvé | NUL (ne concerne pas S_H) |
| Exclusion de G_geom petit (SU(2), fini) | Informatif | INFORMATIF (confirme l'absence de structure cachée exploitable) |

---

## VERDICT FINAL

### Classification : INFORMATIF MAIS NON EXPLOITABLE

La piste monodromie géométrique est **MORTE comme outil de preuve** pour le verrou V_SQRT_CANCEL.

**Raisons** :
1. **Gap formel** : S_H(t) n'est pas la trace d'un Frobenius. Le pont entre la monodromie et les bornes sur S_H n'existe pas dans la littérature et ne peut pas être construit avec les outils actuels.
2. **Gap quantitatif** : même si le pont existait, la monodromie donne des bornes MOYENNÉES, pas POINTWISE. Le facteur sqrt(log p) est inhérent au maximum de variables gaussiennes.
3. **Gap structurel** : le verrou ne se réduit pas à borner |S_H| individuellement mais à borner une SOMME de PRODUITS CORRÉLÉS. La monodromie ne traite pas la corrélation entre twists géométriques 3^j.
4. **Réfutation numérique** : max|S_H|/sqrt(r) croît empiriquement, confirmant que sqrt(r) est faux.

**Ce qui est acquis (informatif)** :
- La distribution de S_H est bien comprise numériquement (quasi-gaussienne, variance r)
- L'identité produit est prouvée (intérêt mathématique indépendant)
- L'espace des groupes de monodromie possibles est cartographié (SL(r-1) maximal)
- Confirmation que le problème est FONDAMENTALEMENT DUR (pas de structure cachée)

**Kill switches définitifs** :
1. max|S_H|/sqrt(r) CROÎT — la borne sqrt(r) est FAUSSE
2. S_H n'est pas un Frobenius — le formalisme de Deligne/Katz ne s'applique pas directement
3. Même les bornes moyennées sont insuffisantes pour le produit corrélé
4. |H| = O(log p) est SOUS TOUS les seuils de la littérature

**Recommandation** : Classer la piste monodromie géométrique comme FERMÉE dans le registre fail-closed. Elle ne peut pas contribuer au verrou. Les seules voies qui restent ouvertes nécessitent un outil QUALITATIVEMENT NOUVEAU pour les sommes sur sous-groupes de taille logarithmique, ou une reformulation du verrou qui évite les bornes pointwise sur S_H.

---

## REGISTRE FAIL-CLOSED (ajouts R160)

| Objet | Statut | Kill | Round |
|-------|--------|------|-------|
| G_geom = SL(r-1) → borne pointwise | **[MORT]** | Monodromie donne moyennes, pas max | R160 |
| S_H comme trace de Frobenius | **[MORT]** | Somme partielle sur sous-groupe, pas Frobenius | R160 |
| Deligne/Weil II pour borner S_H | **[MORT]** | Borne (r-1)·sqrt(p), pire que triviale | R160 |
| Monodromie pour éliminer sqrt(log p) | **[MORT]** | Maximum de gaussiennes, pas géométrie algébrique | R160 |
| Borne sqrt(r) stricte | **[PROUVÉE FAUSSE]** | max/sqrt(r) = 4.67 et croissant | R159-R160 |
| Identité produit comme levier | **[SANS IMPACT]** | Concerne det, pas S_H | R160 |

---

*R160 — Audit logique terminé. Classification : INFORMATIF MAIS NON EXPLOITABLE.*
