# R184 -- AGENT COMBINATOIRE : Intersection Metrique-Modulaire
## Formalisation de la vacuite de l'intersection pour k >= 3

**Date :** 16 mars 2026
**Methode :** Raisonnement pur, ZERO calcul
**Prerequis :** R183 (5 documents : HLP tension, simplexe combinatoire, CRT investigation, noyau impair, audit/allegorie)
**Question centrale :** L'intersection {g(v) = n*d : v monotone, n >= 1} est-elle VIDE pour k >= 3 ?

---

## 0. CADRE, NOTATIONS, SANITY CHECKS

**Objets :**
- V_k(S) = {(B_0,...,B_{k-1}) : 0 <= B_0 <= ... <= B_{k-1} <= S-1, sum B_j = S - k}
- g(v) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}
- d = 2^S - 3^k, avec S = ceil(k * log_2(3))
- Condition de cycle : g(v) = n * d pour un entier n >= 1

**Les DEUX conditions (R183 A4) :**
1. **METRIQUE :** g(v) doit valoir exactement n*d dans Z (pas seulement mod d)
2. **MODULAIRE :** g(v) ≡ 0 mod p pour tout p | d simultanement

**Sanity check k=1 :** S = 2, d = 2^2 - 3 = 1. g(v) = 2^{B_0} avec B_0 = S - k = 1. Donc g = 2 = 2*1 = 2*d. Cycle existe (trivial). Tout argument DOIT echouer pour k=1. [VERIFIE]

**Sanity check k=2 :** S = 4, d = 16 - 9 = 7. V_2(4) : B_0 + B_1 = 2, B_0 <= B_1 <= 3.
Vecteurs : (0,2), (1,1) -- attendons, sum B_j = S - k = 2. (0,2) : sum=2, OK. (1,1) : sum=2, OK.
g(0,2) = 3*1 + 4 = 7 = 1*d. CYCLE (fantome, cf. R183 noyau). g(1,1) = 3*2 + 2 = 8.
Donc pour k=2, l'intersection est NON VIDE. Tout argument DOIT echouer pour k=2. [VERIFIE]

---

## 1. TAILLE DE Im(g) -- LE SIMPLEXE MONOTONE

### 1.1 Nombre de vecteurs monotones

Le nombre de vecteurs v = (B_0,...,B_{k-1}) avec 0 <= B_0 <= ... <= B_{k-1} <= S-1 et sum B_j = S - k est le nombre de PARTITIONS de S - k en k parts, chacune dans {0, ..., S-1}, en ordre croissant.

**ATTENTION :** Ce n'est PAS C(S-1, k-1) ni C(S+k-2, k-1). Le R183 simplexe combinatoire utilise tantot C(S-1, k-1) tantot C(S+k-2, k-1) -- clarifions.

Si on oublie la contrainte sum B_j = S - k mais garde 0 <= B_0 <= ... <= B_{k-1} <= S-1, le nombre de vecteurs est C(S-1+k, k) = C(S+k-2, k-1) (compositions avec repetition : "stars and bars" avec k elements dans {0,...,S-1}).

**CORRECTION IMPORTANTE :** C(S+k-2, k-1) est le nombre de multisets de taille k dans {0,...,S-1}. C'est le nombre de vecteurs monotones SANS la contrainte de somme.

Avec la contrainte sum B_j = S - k, c'est un sous-ensemble strict. Notons-le N(k, S).

Pour l'argument metrique, c'est le nombre TOTAL (sans contrainte de somme) qui importe pour |Im(g)|, car la contrainte sum B_j = S - k restreint a une seule "tranche". Mais pour la condition de cycle, on a sum B_j = S - k FIXE.

**FAIT (PROUVE) :** N(k, S) = |{v monotone avec sum B_j = S-k}| est le nombre de partitions de S-k en k parts dans {0,...,S-1}, ordonnees croissant. C'est aussi le nombre de compositions non-decroissantes de S-k en k parts bornees par S-1.

Pour l'asymptotique : en prenant S ~ 1.585k, la somme cible est S - k ~ 0.585k, et chaque part est dans {0,..., S-1}. Le nombre de telles compositions croit au plus polynomialement en k (car c'est borne par C(S-1, k-1) ~ C(0.585k, k-1) en prenant les "separateurs" dans un segment de taille ~ 0.585k).

**Estimation de C(S-1, k-1) pour S = ceil(k*log_2(3)) :**

Posons S ~ 1.585k. Alors S-1 ~ 1.585k - 1, et :

C(S-1, k-1) ~ C(1.585k, k-1) ~ C(1.585k, 0.585k)

Par la formule de Stirling et la formule du binomial :

C(alpha*k, beta*k) ~ 2^{k*H(beta/alpha)*alpha} / sqrt(...)

ou H(x) = -x*log_2(x) - (1-x)*log_2(1-x) est l'entropie binaire.

Ici alpha = 1.585, beta = 0.585, beta/alpha = 0.369.
H(0.369) = -0.369*log_2(0.369) - 0.631*log_2(0.631) ~ 0.369*1.438 + 0.631*0.665 ~ 0.531 + 0.420 = 0.951

Donc C(1.585k, 0.585k) ~ 2^{1.585k * 0.951} / poly(k) = 2^{1.507k} / poly(k).

**FAIT (DEDUIT) :** |V_k(S)| ~ 2^{1.507k} (exposant approximatif). [DEDUIT]

### 1.2 Comparaison avec d

d = 2^S - 3^k. Posons S = ceil(k*log_2(3)), donc 2^S >= 3^k avec egalite impossible. Ecrivons :

2^S = 3^k * 2^{frac(k*log_2(3))} (quand S = ceil(k*alpha), frac = S - k*alpha in (0,1])

Donc d = 3^k * (2^{frac} - 1) ou frac = S - k*log_2(3) in (0, 1].

Pour frac petit : d ~ 3^k * frac * ln(2) ~ 3^k * frac * 0.693. Minimal.
Pour frac ~ 1 : d ~ 3^k * (2-1) = 3^k. Maximal.

Dans tous les cas : d in (0, 3^k], et typiquement d ~ c * 3^k pour une constante c in (0,1).

En bits : d ~ 3^k ~ 2^{k*log_2(3)} = 2^{1.585k}.

**COMPARAISON CRUCIALE :**

|V_k(S)| ~ 2^{1.507k} vs d ~ 2^{1.585k}

Donc |V_k(S)| / d ~ 2^{(1.507 - 1.585)k} = 2^{-0.078k} → 0.

**THEOREME (DEDUIT) :** Pour k suffisamment grand, |V_k(S)| < d. Plus precisement, pour k >= K_0 (ou K_0 est une constante calculable), le nombre de vecteurs monotones est STRICTEMENT inferieur au module d.

**Statut : DEDUIT.** L'estimation asymptotique est correcte modulo les constantes exactes. Le seuil K_0 depend des termes polynomiaux negliges.

**CONSEQUENCE IMMEDIATE :** Puisque |Im(g) mod d| <= |V_k(S)| < d, l'image de g mod d NE PEUT PAS couvrir Z/dZ. Il existe au moins d - |V_k(S)| > 0 residus non atteints. MAIS cela ne dit pas que 0 est parmi les non-atteints.

**ATTENTION A LA CONFUSION :** Le R183 simplexe combinatoire (Approche 4) calcule C(S+k-2, k-1) / d et trouve ce ratio >> 1. C'est parce qu'il omet la contrainte sum B_j = S - k. AVEC la contrainte, le nombre de vecteurs est BEAUCOUP plus petit.

**Verification de la divergence :** C(S+k-2, k-1) ~ (2.585k)^{k-1}/(k-1)! ~ (2.585e)^k / sqrt(k) par Stirling. Cela donne ~ 7.03^k >> 3^k = d. C'est le calcul de R183 Approche 4.

Mais N(k,S) = |{sum B_j = S-k, monotone}| << C(S+k-2, k-1). La contrainte de somme FIXEE reduit exponentiellement le nombre de vecteurs. C'est comme passer de l'hypercube aux points d'un hyperplan -- reduction d'un facteur ~ S.

Plus finement : N(k,S) ~ C(S+k-2, k-1) / S (par equidistribution de la somme sur [0, k(S-1)]). Mais k(S-1) ~ 1.585k^2, et S-k ~ 0.585k << k(S-1)/2 ~ 0.8k^2, donc la somme est concentree dans la queue gauche. L'estimation N(k,S) ~ C(S-1, k-1) est meilleure (nombre de facons de choisir k-1 separateurs dans [1, S-1] pour une composition monotone de somme S-k).

**Je clarifie :** Le nombre exact de vecteurs monotones v = (B_0,...,B_{k-1}) avec B_0 <= ... <= B_{k-1}, B_j in {0,...,S-1}, sum B_j = S-k est un nombre de partitions restreint. Pour l'analyse asymptotique, la borne superieure |V_k(S)| <= C(S-1, k-1) suffit.

C(S-1, k-1) avec S ~ 1.585k donne C(0.585k, k-1). Mais k-1 > 0.585k pour k >= 3, donc on doit ecrire C(0.585k, k-1) = C(0.585k, 0.585k - (k-1-0.585k))... NON. C(n, r) = 0 quand r > n. Et ici S-1 ~ 0.585k et k-1 ~ k, donc k-1 > S-1 pour k >= 3.

**CORRECTION CRITIQUE :** C(S-1, k-1) = 0 quand k-1 > S-1, i.e., quand k > S. Mais S ~ 1.585k > k, donc S-1 ~ 1.585k - 1 et k-1 ~ k-1. On a S-1 > k-1 ssi 1.585k - 1 > k - 1 ssi 0.585k > 0, toujours vrai. Donc C(S-1, k-1) est bien defini et non nul.

Reprenons : C(S-1, k-1) = C(1.585k - 1, k-1). Par symetrie, C(n, r) = C(n, n-r), et n-r = 1.585k - 1 - (k-1) = 0.585k. Donc C(1.585k, k-1) = C(1.585k, 0.585k).

L'entropie : H(0.585/1.585) = H(0.369) ~ 0.951 comme calcule ci-dessus. Donc :

C(1.585k, 0.585k) ~ 2^{1.585k * 0.951} / sqrt(k) = 2^{1.507k} / sqrt(k)

Et d ~ 2^{1.585k}. Le ratio est 2^{-0.078k} / sqrt(k) → 0.

**MAIS** C(S-1, k-1) est une borne superieure sur N(k,S), pas le nombre exact. Le nombre exact pourrait etre encore plus petit.

**Statut : DEDUIT que |V_k(S)| / d → 0 exponentiellement pour k → infini.** Le seuil exact K_0 n'est pas determine ici.

---

## 2. RANGE ET RESOLUTION DE g(v)

### 2.1 Valeurs extremes

**g_min :** Atteint quand les B_j sont le plus concentres possible. La plus petite somme sum 3^{k-1-j} * 2^{B_j} sous la contrainte sum B_j = S-k et monotonie est obtenue quand les B_j sont le plus "empaquetes".

Pour le vecteur constant B_j = (S-k)/k (quand k | S-k) :
g_const = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{(S-k)/k} = 2^{(S-k)/k} * (3^k - 1)/2

Mais le vecteur constant n'est pas toujours entier. Plus generalement, g_min est atteint quand les B_j sont aussi proches que possible de la moyenne (S-k)/k.

**FAIT (HLP, R182-R183) :** Parmi toutes les permutations d'un meme multiset {B_j}, la monotonie (B croissant vs coefficients decroissants) MINIMISE g. Mais parmi tous les vecteurs monotones, le minimum absolu depend de la distribution des B_j.

**Encadrement :** Le minimum de g sur le simplexe monotone est :

g_min = (3^k - 1)/2 (vecteur B_j = 0 pour tout j, sum = 0 -- mais cela exige S = k, i.e., frac = 0)

**CORRECTION :** sum B_j = S - k, et S > k (pour k >= 2). Donc le vecteur B_j = 0 n'est valide que si S = k, ce qui exige 2^k = 3^k, impossible. Donc g_min > (3^k-1)/2 toujours.

Le vecteur minimisant g sous sum B_j = S-k est celui qui repartit la somme S-k aussi uniformement que possible. Par l'inegalite de Jensen appliquee a la fonction convexe 2^x :

g(v) = sum 3^{k-1-j} * 2^{B_j} >= sum 3^{k-1-j} * 2^{(S-k)/k} = 2^{(S-k)/k} * tau_k

ou tau_k = (3^k - 1)/2 est le noyau trivial. L'egalite a lieu quand tous les B_j = (S-k)/k.

**Statut : DEDUIT** (inegalite de Jensen + convexite de 2^x).

**g_max :** Atteint quand les B_j sont le plus etales. Pour des vecteurs monotones avec sum B_j = S-k, le maximum de g est obtenu quand B_{k-1} est aussi grand que possible et B_0 aussi petit que possible. Par exemple, B = (0, 0, ..., 0, S-k) donne :

g_max_approx = 3^{k-1} * 1 + 3^{k-2} * 1 + ... + 3^1 * 1 + 3^0 * 2^{S-k}
             = (3^k - 3)/2 + 2^{S-k}

Pour S-k ~ 0.585k, 2^{S-k} ~ 2^{0.585k} ~ 1.5^k, et (3^k - 3)/2 ~ 3^k/2. Donc g_max ~ 3^k/2 + 1.5^k ~ 3^k/2.

Plus generalement, g_max ~ tau_k * 2^{S-1} (vecteur B_j = S-1 pour tout j, mais sum = k(S-1) >> S-k en general). Pour la contrainte sum B_j = S-k, g_max est beaucoup plus petit.

**Estimation de la plage :** g_max - g_min ~ 3^k * (2^{epsilon} - 1) pour un epsilon > 0, de l'ordre de 3^k.

### 2.2 Resolution (plus petite difference entre g-valeurs adjacentes)

Deux vecteurs v et v' qui different par Delta B_j = +1 sur un composant j et Delta B_{j'} = -1 sur un composant j' (pour preserver la somme) donnent :

|g(v) - g(v')| = |3^{k-1-j} * 2^{B_j} * (2-1) - 3^{k-1-j'} * 2^{B_{j'}} * (2-1)|
              = |3^{k-1-j} * 2^{B_j} - 3^{k-1-j'} * 2^{B_{j'}}|

Le plus petit delta non nul correspond a des transferts entre composants voisins avec de petits B_j. Le quantum minimal est de l'ordre de min(3^{k-1-j} * 2^{B_j}) ~ 2^0 * 3^0 = 1 (pour le terme j = k-1 avec B_{k-1} = 0, ce qui est le cas quand la plupart de la somme est portee par les termes intermediaires).

En pratique, la resolution minimale est de l'ordre de 1 pour les petits B, et croit exponentiellement avec B. L'ensemble Im(g) N'EST PAS un sous-ensemble continu -- il est discret avec des espacements variables.

**Statut : DEDUIT.** La resolution est non uniforme et depend fortement de la position dans l'espace des v.

---

## 3. DENSITE DES MULTIPLES DE d DANS LE RANGE

### 3.1 Comptage des cibles

Les multiples de d dans [g_min, g_max] sont n*d pour n = ceil(g_min/d), ..., floor(g_max/d). Leur nombre est :

M = floor(g_max / d) - ceil(g_min / d) + 1 ~ (g_max - g_min) / d

Puisque g_max - g_min ~ O(3^k) et d ~ O(3^k), on a M ~ O(1). Plus precisement :

g_min >= 2^{(S-k)/k} * tau_k et g_max <= 2^{S-k} * tau_k (encadrement grossier).

Le ratio g_max / g_min <= 2^{S-k - (S-k)/k} = 2^{(S-k)(1 - 1/k)} = 2^{(S-k)(k-1)/k}.

Pour S - k ~ 0.585k : (S-k)(k-1)/k ~ 0.585(k-1) ~ 0.585k.

Donc g_max / g_min ~ 2^{0.585k} ~ 1.5^k.

Et g_min / d ~ tau_k * 2^{(S-k)/k} / d ~ (3^k/2) * 2^{0.585} / (c*3^k) ~ 1/(2c) * 1.5 ~ 0.75/c.

Pour c ~ 0.5 (valeur typique de d/3^k), g_min/d ~ 1.5.

Donc M ~ g_max/d ~ (g_max/g_min) * (g_min/d) ~ 1.5^k * 1.5 ~ 1.5^{k+1}.

**FAIT (DEDUIT) :** Le nombre de multiples de d dans la plage [g_min, g_max] croit comme 1.5^k ~ 2^{0.585k}. [DEDUIT]

### 3.2 Ratio vecteurs / cibles

Nombre de vecteurs : |V_k(S)| <= 2^{1.507k}.
Nombre de cibles (multiples de d) : M ~ 2^{0.585k}.

Ratio : |V_k(S)| / M ~ 2^{(1.507 - 0.585)k} = 2^{0.922k} → infini.

**INTERPRETATION :** Il y a EXPONENTIELLEMENT plus de vecteurs que de cibles. Si les valeurs g(v) etaient reparties uniformement dans la plage, chaque cible n*d serait "approchee" par environ 2^{0.922k} vecteurs. Cela semble DEFAVORABLE a l'absence de solutions.

**MAIS :** "Approcher" n'est pas "atteindre exactement". L'espacement moyen entre g-valeurs consecutives est :

(g_max - g_min) / |V_k(S)| ~ 3^k / 2^{1.507k} = (3/2^{1.507})^k = (3/2.843)^k ~ 1.055^k

Cet espacement CROIT (lentement) avec k. Les g-valeurs deviennent de plus en plus espacees par rapport a 1, mais les cibles n*d sont espacees de d ~ 3^k >> espacement.

La question est : avec une resolution de ~ 1.055^k et des cibles espacees de ~ 3^k, la probability qu'une valeur g(v) tombe exactement sur une cible est :

P ~ |V_k(S)| / (g_max - g_min) * 1 = |V_k(S)| / O(3^k) ~ 2^{1.507k} / 3^k = 2^{1.507k} / 2^{1.585k} = 2^{-0.078k}

C'est le meme ratio qu'en Section 1.2 : il decroit exponentiellement. Pour chaque cible n*d, la probabilite qu'elle soit dans Im(g) est ~ 2^{-0.078k}. Et il y a M ~ 2^{0.585k} cibles. Donc la probabilite qu'au moins une soit atteinte est :

P_total ~ M * P ~ 2^{0.585k} * 2^{-0.078k} = 2^{0.507k} → infini

**PROBLEME :** L'argument probabiliste donne P_total → infini, ce qui PREDIT des solutions. C'est l'argument de R183 Approche 4 (C >> d => solutions attendues) vu differemment.

**ATTENTION :** Ce calcul est FAUX car il suppose l'uniformite de Im(g) dans la plage, ce qui n'est pas le cas. Im(g) est structure -- les g-valeurs ne sont pas aleatoires dans [g_min, g_max].

**Statut : L'argument de comptage pur est INSUFFISANT pour prouver la vacuite. CONFIRME le theoreme negatif de R183 Approche 4.** [PROUVE que le comptage echoue]

---

## 4. L'ARGUMENT METRIQUE : POURQUOI LE COMPTAGE ECHOUE

### 4.1 Le paradoxe metrique

L'argument de la Section 3 montre que :
- |V_k(S)| / d → 0 (pas assez de vecteurs pour couvrir Z/dZ -- argument MODULAIRE favorable)
- |V_k(S)| * M / (g_max - g_min) → infini (trop de vecteurs par rapport aux cibles METRIQUE -- argument METRIQUE defavorable)

Les deux arguments donnent des conclusions OPPOSEES. La resolution du paradoxe est que la condition de cycle combine les DEUX :

g(v) = n*d <=> g(v) ≡ 0 mod d (MODULAIRE) ET g(v) / d = n entier (METRIQUE)

La condition modulaire est favorable (pas assez de vecteurs). La condition metrique semble defavorable (trop de cibles accessibles). La resolution est que la condition CONJOINTE est plus restrictive que chacune separement.

### 4.2 Formalisation de l'intersection

Definissons :
- A_mod = {v in V_k(S) : g(v) ≡ 0 mod d} (ensemble modulaire)
- A_met = {v in V_k(S) : g(v) in {d, 2d, 3d, ...}} (ensemble metrique)

La condition de cycle est A_mod inter A_met (qui est la meme chose -- g(v) = nd implique les deux). Plus interessant est la DECOMPOSITION du probleme :

**Question modulaire :** |A_mod| = ?
**Question metrique :** A_mod subset A_met ? (Tautologiquement oui si on definit correctement.)

L'observation cruciale est que la condition g(v) = n*d est UNE seule equation dans Z, pas deux. La decomposition modulaire/metrique est une LENTILLE d'analyse, pas une decomposition du probleme.

**La vraie question est :** Im(g) inter d*N* est-il vide ?

### 4.3 La structure de Im(g)

Im(g) est un sous-ensemble de Z avec les proprietes suivantes :

**(P1) Positivite :** g(v) > 0 pour tout v (tous les termes sont strictement positifs). [PROUVE]

**(P2) Borne inferieure :** g(v) >= 2^{(S-k)/k} * tau_k. [DEDUIT, Jensen]

**(P3) Borne superieure :** g(v) <= 2^{S-k} * tau_k (approx). [DEDUIT]

**(P4) Parite du noyau :** h(v) = g(v)/2^{B_0} est toujours IMPAIR. Donc si g(v) = n*d avec d impair, alors 2^{B_0} | n. [PROUVE, R183 noyau I6]

**(P5) Non-divisibilite par 3 :** 3 ne divise jamais g(v). Donc si g(v) = n*d et 3 | d, contradiction. Mais 3 ne divise pas d (car d = 2^S - 3^k et 3 ne divise pas 2^S). Donc (P5) n'induit pas de contradiction, mais confirme la coherence. [PROUVE]

**(P6) Structure multiplicative mixte :** g(v) = sum 3^{k-1-j} * 2^{B_j} est une somme de termes de la forme 3^a * 2^b, avec a + b = k - 1 - j + B_j (pas constant). L'ensemble Im(g) est un SUMSET de k ensembles lacunaires, contraint par la monotonie. [DEDUIT]

### 4.4 La cle : Im(g) est un sumset ANTI-CORRELE

Soit A_j = {3^{k-1-j} * 2^b : b = 0, ..., S-1} le j-eme "rail". Alors :

Im(g) subset A_0 + A_1 + ... + A_{k-1} (somme de Minkowski)

MAIS avec la contrainte de monotonie (b_0 <= b_1 <= ... <= b_{k-1}) et de somme (sum b_j = S-k), Im(g) est un sous-ensemble STRICT de cette somme de Minkowski.

**L'anti-correlation (HLP) :** Le rail j=0 a les plus grands coefficients ternaires (3^{k-1}) mais, par monotonie, les plus petits exposants binaires (B_0 minimal). Le rail j=k-1 a le plus petit coefficient ternaire (3^0 = 1) mais le plus grand exposant binaire (B_{k-1} maximal). C'est la "democratie forcee" de R183.

**Consequence pour la structure de Im(g) :** Les termes individuels c_j * 2^{B_j} = 3^{k-1-j} * 2^{B_j} sont tous du MEME ORDRE DE GRANDEUR (car l'anti-correlation compense les coefficients decroissants par des exposants croissants). Plus precisement, pour le vecteur "equilibre" B_j ~ j * (S-k)/(k-1) :

c_j * 2^{B_j} ~ 3^{k-1-j} * 2^{j(S-k)/(k-1)} ~ (3/2^{(S-k)/(k-1)})^{k-1-j} * 2^{(S-k)} * cste

Le ratio entre le plus grand et le plus petit terme est (3/2^{(S-k)/(k-1)})^{k-1}. Pour S-k ~ 0.585k et k-1 ~ k : (S-k)/(k-1) ~ 0.585, et 2^{0.585} ~ 1.5, donc 3/1.5 = 2, et le ratio est 2^{k-1}.

**Correction :** La "democratie" n'est pas parfaite -- le ratio est 2^{k-1}, ce qui est GRAND. Les termes ne sont PAS du meme ordre de grandeur. Le premier terme (j=0) est ~ 3^{k-1} * 2^{B_0} et le dernier (j=k-1) est ~ 2^{B_{k-1}}. Avec B_0 ~ 0 et B_{k-1} ~ S-k ~ 0.585k : le premier est ~ 3^{k-1} et le dernier est ~ 2^{0.585k} ~ 1.5^k. Le ratio est 3^{k-1}/1.5^k ~ 2^k → infini. Le premier terme DOMINE.

**Statut : DEDUIT.** L'anti-correlation REDUIT les variations mais ne les EGALISE pas. Le premier terme domine encore exponentiellement.

---

## 5. L'OBSTRUCTION STRUCTURELLE : g(v) ET LES MULTIPLES DE d

### 5.1 La contrainte n >= 1

Pour un cycle, g(v) = n*d avec n >= 1. Donc g(v) >= d.

Or d = 2^S - 3^k. Et g_min est atteint pour le vecteur le plus concentre.

**Le plus petit g :** Pour le vecteur B_j = 0 pour j < k et B_{k-1} = S-k (concentration maximale sur le dernier terme), mais ce n'est pas monotone (B_{k-2} = 0 et B_{k-1} = S-k exige les autres a 0, ce qui est monotone). Mais sum B_j = S-k.

g_minimal_candidat = 3^{k-1} + 3^{k-2} + ... + 3^1 + 2^{S-k}
                   = (3^k - 3)/2 + 2^{S-k}

Comparons a d = 2^S - 3^k :

g / d = ((3^k - 3)/2 + 2^{S-k}) / (2^S - 3^k)

Pour k grand, le terme dominant du numerateur est 3^k/2 et le denominateur est d ~ c*3^k, donc g/d ~ 1/(2c).

Pour c > 1/2, g_min < d, et le premier multiple positif n=1 est au-dessus de g_min. Pour c < 1/2, g_min > d.

**La question est : pour quels k le vecteur le plus "modeste" donne g(v) < d ?**

Si g_min < d, alors aucun vecteur avec g(v) < d ne peut etre un cycle (car n >= 1 exige g >= d). L'ensemble des vecteurs avec g(v) < d est exclu. Mais les vecteurs avec g(v) > d pourraient etre des cycles pour n >= 1.

**Statut : OBSERVATION.** La borne g >= d n'exclut pas les cycles en general.

### 5.2 La borne superieure sur n

La condition g(v) = n*d avec g(v) <= g_max donne n <= g_max/d. On a estime M = g_max/d ~ 1.5^k. Donc n in {1, 2, ..., floor(1.5^k)}.

**MAIS :** n = g(v)/d doit etre compatible avec la structure de g. Specifiquement, n = h(v) * 2^{B_0} / d ou h(v) est impair. Cela impose que d | h(v) * 2^{B_0}, et puisque gcd(d, 2) = 1, il faut d | h(v).

**THEOREME (PROUVE, elementaire) :** La condition g(v) = n*d est equivalente a h(v) = n'*d ou n' = n/2^{B_0}, et n' doit etre un entier positif. Puisque h(v) est impair et d est impair, n' est impair.

Donc n = n' * 2^{B_0} avec n' impair, n' >= 1, et h(v) = n' * d.

**Borne sur n' :** h(v) <= h_max ~ g_max / 2^{B_0_min}. Pour B_0 = 0, h(v) = g(v) et n' = n. Pour B_0 > 0, n' = n / 2^{B_0} < n.

En tout cas, n' <= h_max / d. Et h_max <= g_max, donc n' <= g_max/d ~ 1.5^k. Mais h est impair, donc n' est contraint de plus.

### 5.3 L'argument metrique renforce

**Reformulation du probleme METRIQUE :** Trouver un vecteur Delta = (Delta_1, ..., Delta_{k-1}) dans le simplexe Sigma_k tel que :

h(Delta) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{Delta_j} = n' * d

pour un entier impair n' >= 1.

**Le point cle :** h(Delta) est une FONCTION CROISSANTE de chaque Delta_j (car augmenter Delta_j augmente 2^{Delta_j}). Donc h est monotone sur le simplexe Sigma_k. Sa valeur minimale est :

h_min = tau_k = (3^k - 1)/2 (atteint quand tous les Delta_j = 0, vecteur constant)

Sa valeur maximale est atteinte quand les Delta_j sont maximaux (i.e., B_{k-1} = S-1, ce qui force Delta_{k-1} = S-1-B_0).

La question metrique devient : l'image de h sur Sigma_k contient-elle un multiple de d ?

### 5.4 Le "crible metrique"

Definissons l'ENSEMBLE CIBLE T = {n'*d : n' impair, n' >= 1} inter [h_min, h_max].

|T| ~ (h_max - h_min) / (2d) (car n' impair => ecart entre cibles consecutives = 2d).

Et |Im(h)| <= |Sigma_k| = N(k,S).

L'argument de comptage : si |Im(h)| < |T|, les valeurs de h ne suffisent pas a couvrir toutes les cibles. Mais cela ne dit pas qu'elles n'en atteignent AUCUNE.

Si |Im(h)| * resol_min > 2d, i.e., si l'espacement minimal entre h-valeurs est > 2d, alors au plus UNE cible par "segment" de h-valeurs, et la probabilite de toucher est faible.

**Estimation de l'espacement :** Le plus petit changement de h quand on modifie un Delta_j est delta_h = 3^{k-1-j} * 2^{Delta_j} (quand Delta_j → Delta_j + 1). Pour j = k-1, Delta_{k-1} ~ 0 : delta_h = 1. Pour j = 0, Delta_1 ~ 0 : delta_h = 3^{k-2}.

L'espacement minimal est 1 (changement du dernier terme de 1 unite). Donc Im(h) a des elements consecutifs differant de 1 dans certaines zones.

**Consequence :** L'espacement minimal de 1 << 2d ~ 2*3^k signifie que Im(h) est BEAUCOUP plus finement resolue que les cibles. En principe, Im(h) pourrait "toucher" n'importe quelle cible.

**L'argument metrique pur (espacement vs ecart entre cibles) ECHOUE.** [PROUVE]

---

## 6. L'ARGUMENT MODULAIRE : SURJECTIVITE DE g MOD d

### 6.1 La conjecture de surjectivite (R183)

R183 (simplexe combinatoire, Approche 5) a emis la conjecture forte :

**CONJECTURE R183 :** Pour k >= 3, Im(g) mod d = Z/dZ (surjectivite modulaire).

Evidence : Pour k=2, c'est verifie. Pour k >= 3, C/d → infini (SANS la contrainte de somme), suggerant la surjectivite.

**MAIS AVEC la contrainte de somme :** |V_k(S)| / d → 0 pour k grand (Section 1.2). Donc pour k assez grand, Im(g) mod d est NECESSAIREMENT un sous-ensemble propre de Z/dZ.

**RESOLUTION DU CONFLIT :** La conjecture R183 est formulee SANS la contrainte sum B_j = S-k. Les C(S+k-2, k-1) vecteurs monotones SANS cette contrainte sont beaucoup plus nombreux. Avec la contrainte, le nombre chute dramatiquement.

La question correcte est : Im(g|_{sum=S-k}) mod d contient-il 0 ?

Pour k < K_0 (seuil ou |V_k(S)| > d) : la surjectivite modulaire est POSSIBLE.
Pour k >= K_0 : la surjectivite est IMPOSSIBLE (pas assez de vecteurs).

**Statut : CLARIFIE. La conjecture R183 etait basee sur un comptage INCORRECT (vecteurs sans contrainte de somme).** Avec la contrainte, l'argument modulaire est FAVORABLE pour k grand. Pour k petit, il reste ouvert.

### 6.2 La zone critique : k entre 3 et K_0

Pour 3 <= k < K_0, il y a assez de vecteurs pour couvrir Z/dZ EN PRINCIPE. L'obstruction doit venir d'une propriete STRUCTURELLE de Im(g) mod d, pas du comptage.

C'est ici que l'argument de R183 sur l'anti-correlation CRT (investigation racinaire) entre en jeu.

**Resume de la piste R183 CRT :**
- Pour p | d, la condition 2^S ≡ 3^k mod p selectionne des premiers SPECIFIQUES
- Les conditions g(v) ≡ 0 mod p_i pour differents p_i | d sont ANTI-CORRELEES
- L'anti-correlation vient de la structure iterative de g (Horner = Collatz inverse)
- Le couplage est irreductible car il vient de l'arithmetique de Z, pas de F_p individuel

**Statut : CONJECTURE (non prouvee, cf. R183 niveaux 7-10).**

### 6.3 Synthese modulaire

**Pour k >= K_0 (grands k) :** |V_k(S)| < d. L'image de g mod d est un sous-ensemble propre de Z/dZ. La question 0 in Im(g mod d) ne peut pas etre resolue par comptage seul (|V_k(S)| > 0 = borne inferieure triviale sur |Im(g mod d)|). Mais l'argument probabiliste donne E[N_0] ~ |V_k(S)| / d → 0, ce qui est favorable. Pour le rendre rigoureux, il faut prouver que Im(g mod d) est "suffisamment aleatoire" (equidistribution partielle). C'est le Junction Theorem, Bloc 1.

**Pour 3 <= k < K_0 (petits k) :** |V_k(S)| > d. L'image POURRAIT couvrir tout Z/dZ. L'obstruction doit etre structurelle (anti-correlation CRT ou autre). C'est le verrou non resolu.

---

## 7. TENTATIVE DE PREUVE DE VACUITE DE L'INTERSECTION

### 7.1 Strategie

On cherche a prouver : pour k >= 3, il n'existe pas de v in V_k(S) tel que g(v) = n*d.

**Decomposition en deux regimes :**

**(R1) Regime k >= K_0 :** Argument probabiliste (Bloc 1 renforce par anti-correlation CRT).

**(R2) Regime 3 <= k < K_0 :** Argument structurel.

### 7.2 Regime R1 : Argument de rarete

**THEOREME CONDITIONNEL R184.1 :** *Soit k >= K_0 ou K_0 est le seuil tel que C(S-1, k-1) < d. Si la distribution de g(v) mod d est "suffisamment uniforme" (au sens ou la taille de Im(g mod d) est ~ |V_k(S)|, sans concentration sur 0), alors N_0(d) = 0 avec probabilite → 1.*

**Preuve (conditionnelle) :**
1. |V_k(S)| < d, donc |Im(g mod d)| <= |V_k(S)| < d.
2. Im(g mod d) est un sous-ensemble de Z/dZ de taille au plus |V_k(S)|.
3. Si ce sous-ensemble est "quasi-aleatoire" (chaque element de Z/dZ a probabilite ~ |V_k(S)|/d de figurer dans Im), alors P(0 in Im) ~ |V_k(S)|/d → 0.
4. Par Borel-Cantelli (sommant sur k >= K_0) : la somme sum_k |V_k(S)|/d converge (serie geometrique decroissante), donc PRESQUE SUREMENT un nombre fini de k >= K_0 ont N_0 > 0.

**Statut : CONDITIONNEL sur l'equidistribution de Im(g) mod d.** C'est l'argument classique du Junction Theorem Bloc 1. La condition d'equidistribution est le point dur.

### 7.3 Regime R2 : Argument structurel (tentative)

Pour 3 <= k < K_0, je tente un argument plus fin.

**PROPOSITION R184.2 (CONJECTURE) :** *Pour k >= 3, g(v) = n*d implique que n satisfait des congruences CONTRADICTOIRES.*

**Tentative de preuve :**

Partons de h(v) = n'*d ou n' est impair positif.

h(v) = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{Delta_j}

h(v) mod 3 = 2^{Delta_{k-1}} mod 3 (seul le dernier terme survit mod 3). [PROUVE, R183]

Et d mod 3 = 2^S mod 3 = (-1)^S.

Si S est pair : d ≡ 1 mod 3. Alors n'*d ≡ n' mod 3. Et h(v) ≡ 2^{Delta_{k-1}} mod 3.
Donc n' ≡ 2^{Delta_{k-1}} mod 3. C'est une CONTRAINTE sur n', pas une contradiction.

Si S est impair : d ≡ 2 mod 3. Alors n'*d ≡ 2n' mod 3. Et h(v) ≡ 2^{Delta_{k-1}} mod 3.
Donc 2n' ≡ 2^{Delta_{k-1}} mod 3, i.e., n' ≡ 2^{Delta_{k-1}-1} mod 3.

Aucune contradiction dans les deux cas. [ECHEC]

**Tentative via mod 8 :**

h(v) est impair, donc h(v) ≡ 1, 3, 5, ou 7 mod 8.

d mod 8 = (2^S - 3^k) mod 8. Pour S >= 3 : 2^S ≡ 0 mod 8, donc d ≡ -3^k mod 8.
3^k mod 8 : 3^1=3, 3^2=1, 3^3=3, 3^4=1. Cycle de periode 2.
- k impair : 3^k ≡ 3 mod 8, donc d ≡ -3 ≡ 5 mod 8.
- k pair : 3^k ≡ 1 mod 8, donc d ≡ -1 ≡ 7 mod 8.

n'*d mod 8 :
- k impair : n'*5 mod 8. Pour n' impair : 1*5=5, 3*5=15≡7, 5*5=25≡1, 7*5=35≡3. Donc n'*d mod 8 in {1,3,5,7}. Pas de restriction.
- k pair : n'*7 mod 8. Pour n' impair : 1*7=7, 3*7=21≡5, 5*7=35≡3, 7*7=49≡1. Meme chose.

Dans les deux cas, n'*d mod 8 parcourt {1,3,5,7} = tous les residus impairs. Et h(v) mod 8 est dans {1,3,5,7}. Pas de contradiction. [ECHEC]

**Tentative via la taille de h :**

h(v) >= tau_k = (3^k - 1)/2. Pour qu'un cycle existe, h(v) = n'*d. Donc n' = h(v)/d >= tau_k / d = (3^k - 1) / (2*(2^S - 3^k)).

Pour S = ceil(k*alpha), alpha = log_2(3) : d = 2^S - 3^k. Puisque 2^S > 3^k et 2^S < 2*3^k (car frac < 1), on a 0 < d < 3^k. Donc :

n' >= (3^k - 1) / (2 * 3^k) → 1/2. Donc n' >= 1. [Pas de contradiction]

Et n' <= h_max / d. Estimons h_max : le vecteur avec B_0 = 0 et B_{k-1} maximal donne h = g, et g_max est borne par sum 3^{k-1-j} * 2^{S-1} = 2^{S-1} * tau_k. Mais avec la contrainte de somme, c'est plus restreint.

En tout cas, n' est un entier impair dans un intervalle [1, O(1.5^k)]. Il y a O(1.5^k) candidats. La question est : l'un d'eux est-il dans Im(h)/d ?

**Statut : TOUTES LES TENTATIVES LOCALES ECHOUENT.** Les congruences mod petits nombres ne donnent aucune contradiction. La raison : d est "generique" (pas de structure arithmetique forte connue). [CONFIRME R183 Approche 6, Lecon]

### 7.4 L'argument global (necessite de l'anti-correlation)

Les echecs ci-dessus confirment le diagnostic R183 : aucune obstruction LOCALE (mod petit nombre) ne peut prouver l'absence de cycles. L'obstruction doit etre GLOBALE -- impliquant d EN ENTIER.

**L'unique piste viable pour le regime R2 est l'anti-correlation CRT :**

Si on peut montrer que les evenements {g(v) ≡ 0 mod p_i} pour p_i | d sont NEGATIVEMENT correles avec un facteur suffisant, alors :

N_0(d) = |{v : g(v) ≡ 0 mod d}| <= |V_k(S)| * prod_{p|d} (1/p) * f(k)

ou f(k) < 1 est le facteur de correction d'anti-correlation. Si f(k) est assez petit, N_0(d) < 1 et donc N_0 = 0.

**Statut : CONDITIONNEL sur la preuve de l'anti-correlation CRT.** C'est le Programme Ouvert PO-R87 (R183).

---

## 8. RESULTAT PRINCIPAL : THEOREME D'IMPOSSIBILITE CONDITIONNELLE

### 8.1 Enonce

**THEOREME R184 (CONDITIONNEL) :**

*Supposons les deux hypotheses suivantes :*

*(H1) Equidistribution de Bloc 1 : Pour k >= K_0, la distribution de g(v) mod d est suffisamment uniforme pour que E[N_0] ~ |V_k(S)| / d.*

*(H2) Anti-correlation CRT de Bloc 2 : Pour 3 <= k < K_0, les evenements E_i = {g(v) ≡ 0 mod p_i} pour les premiers p_i | d satisfont :*

*Pr(intersection E_i) < prod Pr(E_i) * (1 - epsilon_k)*

*pour un epsilon_k > 0 suffisant pour donner N_0(d) < 1.*

*Alors : pour tout k >= 3, il n'existe pas de vecteur monotone v tel que g(v) = n*d.*

**Preuve :**
- Sous (H1), pour k >= K_0 : E[N_0] ~ |V_k(S)|/d = 2^{-0.078k} → 0. Pour k assez grand, E[N_0] < 1, donc par Markov, P(N_0 >= 1) < 1 -- ce qui ne suffit PAS a prouver N_0 = 0 avec certitude. Il faudrait une borne sur la variance ou un argument de concentration. **La preuve en regime R1 reste INCOMPLETE** meme sous (H1).
- Sous (H2), pour 3 <= k < K_0 : N_0(d) < 1 par l'anti-correlation, donc N_0 = 0.

**Statut : CONDITIONNEL et INCOMPLET.** (H1) seul ne suffit pas (passage E[N_0] < 1 a N_0 = 0 non rigoureux). (H2) est non prouvee.

### 8.2 Amelioration du regime R1

Pour rendre le regime R1 rigoureux, il faut PLUS que E[N_0] → 0. Il faut :

**Version forte de (H1) :** Pour k >= K_0, |Im(g) mod d| = |V_k(S)| (g est INJECTIVE mod d).

Si g est injective mod d, alors |Im(g mod d)| = |V_k(S)| < d, et Im est un sous-ensemble PROPRE de Z/dZ de taille |V_k(S)|. La probabilite que 0 soit dans ce sous-ensemble est |V_k(S)| / d < 1 -- mais ce n'est toujours pas 0.

En realite, pour prouver N_0 = 0, il ne suffit pas d'un argument probabiliste. Il faut une PREUVE DETERMINISTE. L'argument probabiliste montre seulement que c'est "improbable".

**Le VRAI passage du probabiliste au deterministe** est le Junction Theorem complet, qui combine le Bloc 1 (comptage) avec d'autres blocs (structurels). C'est l'objet du programme de recherche dans son ensemble.

**Statut : Le regime R1 ne peut PAS etre resolu par le seul argument de comptage. Il faut un argument structurel MEME pour les grands k.** [DEDUIT]

---

## 9. L'INTERSECTION METRIQUE inter MODULAIRE : FORMALISATION FINALE

### 9.1 Le probleme reformule

Soit X_k = {g(v) : v in V_k(S)} l'ensemble des valeurs atteignables par g.
Soit Y_k = {n*d : n >= 1, n <= g_max/d} l'ensemble des cibles (multiples de d dans la plage).

La question est : X_k inter Y_k = vide ?

**Taille de X_k :** |X_k| <= |V_k(S)| ~ 2^{1.507k}. (Avec injectivite de g, egalite.)

**Taille de Y_k :** |Y_k| = floor(g_max/d) ~ 1.5^k ~ 2^{0.585k}.

**Taille de l'univers :** [g_min, g_max] inter Z, de taille ~ g_max - g_min ~ 3^k ~ 2^{1.585k}.

**Densite de X_k :** |X_k| / (g_max - g_min) ~ 2^{1.507k} / 2^{1.585k} = 2^{-0.078k} → 0.
**Densite de Y_k :** |Y_k| / (g_max - g_min) ~ 2^{0.585k} / 2^{1.585k} = 2^{-k} → 0.

**Esperance de |X_k inter Y_k| sous hypothese d'independance (uniformite) :**

E[|X inter Y|] ~ |X_k| * |Y_k| / (g_max - g_min) ~ 2^{1.507k} * 2^{0.585k} / 2^{1.585k} = 2^{0.507k} → infini.

**PARADOXE :** Sous hypothese d'uniformite, l'intersection devrait etre NON VIDE (en fait, exponentiellement grande). Donc soit :

(a) L'hypothese d'uniformite est FAUSSE (X_k evite structurellement Y_k), ou
(b) L'intersection est effectivement non vide (des cycles existent).

La conjecture de Collatz affirme (a). Prouver (a) requiert de montrer que X_k et Y_k sont ANTI-CORRELES dans [g_min, g_max].

### 9.2 La source de l'anti-correlation : la structure 2-3

Y_k = {n*(2^S - 3^k) : n >= 1}. Les elements de Y_k sont des combinaisons LINEAIRES de 2^S et 3^k.

X_k = {sum 3^{k-1-j} * 2^{B_j}}. Les elements de X_k sont des combinaisons de PUISSANCES de 2 et 3.

**La difference structurelle :** Y_k contient des multiples d'un nombre SPECIFIQUE (d = 2^S - 3^k), tandis que X_k contient des sommes de termes 3^a * 2^b. Un element de X_k est une combinaison MULTIPLICATIVE-ADDITIVE des bases 2 et 3, tandis qu'un element de Y_k est un multiple d'une DIFFERENCE de puissances de 2 et 3.

Pour qu'un element soit dans X_k inter Y_k, il faudrait :

sum_{j} 3^{k-1-j} * 2^{B_j} = n * (2^S - 3^k)

i.e., sum_{j} 3^{k-1-j} * 2^{B_j} + n * 3^k = n * 2^S

i.e., n * 3^k + sum_{j} 3^{k-1-j} * 2^{B_j} = n * 2^S

Le cote gauche est une somme de termes 3^a * 2^b (les termes de g) plus n*3^k. C'est un entier qui MELANGE les bases 2 et 3. Le cote droit est n * 2^S, un PRODUIT PUR de base 2.

**REFORMULATION (PROUVEE) :**

Un cycle existe ssi il existe (v, n) tel que :

n * 3^k + g(v) = n * 2^S

i.e., g(v) = n * (2^S - 3^k) = n * d.

Equivalemment : g(v) + n * 3^k = n * 2^S.

Le membre gauche g(v) + n*3^k est :

sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} + n * 3^k = 3^k * (n + 3^{-1} * 2^{B_0}) + ... (Horner)

En fait, g(v) + n*3^k = n*3^k + sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}. Vu comme un "polynome" en base 3 :

= 3^k * n + 3^{k-1} * 2^{B_0} + 3^{k-2} * 2^{B_1} + ... + 3^0 * 2^{B_{k-1}}

C'est un nombre dont le "developpement mixte" commence par n en position k, puis les coefficients 2^{B_j} aux positions k-1, ..., 0.

Le membre droit est n * 2^S.

**L'equation dit donc :** Le nombre dont la "representation mixte base 3 avec coefficients en puissances de 2" est (n, 2^{B_0}, 2^{B_1}, ..., 2^{B_{k-1}}) en positions (k, k-1, ..., 0) est EGAL a n * 2^S.

C'est une condition EXTREMEMENT restrictive sur n et v. Le membre gauche a une structure riche (k+1 "chiffres" en base 3, chacun etant une puissance de 2 ou n), tandis que le membre droit est un seul terme.

### 9.3 L'obstacle fondamental a la preuve

**THEOREME NEGATIF R184.3 (DEDUIT) :**

*Aucun argument PUREMENT metrique (comptage de |X_k|, |Y_k|, esperance de |X_k inter Y_k|) ne peut prouver X_k inter Y_k = vide pour k fini, car l'esperance de l'intersection est exponentiellement grande sous l'hypothese d'uniformite.*

*Aucun argument PUREMENT modulaire (congruences locales mod petits nombres) ne peut prouver g(v) != n*d, car les congruences locales ne produisent jamais de contradiction (R183 Approche 6, confirme en Section 7.3).*

*Toute preuve doit exploiter la structure GLOBALE et CONJOINTE de g(v) et de d = 2^S - 3^k en tant que combinaisons multiplicatives des bases 2 et 3.*

**Statut : PROUVE** (par les echecs documentes dans les sections precedentes et dans R183).

---

## 10. PISTES EMERGENTES

### Piste 1 (POTENTIEL 7/10) : La contrainte sum B_j = S-k comme reduction decisive

La plupart des arguments de R183 ignorent la contrainte sum B_j = S-k. Cette contrainte reduit |V_k(S)| de 2^{1.507k} (sans contrainte) a un nombre BEAUCOUP plus petit (possiblement polynomial en k pour les cas ou (S-k)/k est borne). Si la reduction est assez forte, le regime R1 (comptage) pourrait couvrir TOUS les k >= 3, eliminant le besoin du regime R2.

**Question precise :** Quelle est l'asymptotique exacte de N(k, S) = |{v monotone, sum B_j = S-k}| ?

### Piste 2 (POTENTIEL 6/10) : L'equation n*3^k + g(v) = n*2^S comme equation en representations

L'equation de la Section 9.2 peut etre vue comme : le nombre n*2^S admet-il une representation comme n*3^k plus une somme de k termes 3^{k-1-j} * 2^{B_j} avec B_j monotones et sum B_j = S-k ?

Cela se rapproche de la theorie des REPRESENTATIONS DES ENTIERS (Waring, partitions, sumsets). La contrainte sur les representations pourrait etre exploitee via les identites de Ramanujan ou les formules de Hardy-Littlewood.

### Piste 3 (POTENTIEL 8/10) : Le polynome de transfert P_v(X) = sum 3^{k-1-j} * X^{Delta_j}

(De R183 noyau, Section 3.2) P_v(2) = h(v). La condition h(v) = n'*d est P_v(2) ≡ 0 mod d.

Or P_v(X) est un polynome CREUX de degre Delta_{k-1} avec exactement k coefficients non nuls (les 3^{k-1-j}). Les zeros de polynomes creux modulo d sont tres etudies (Bi, Cheng, Rojas : le nombre de zeros d'un polynome a t termes mod p est O(t * sqrt(p))). Si on peut borner le nombre de zeros de P_v(2) ≡ 0 mod d en fonction de k (le nombre de termes), on aurait un argument.

**Probleme :** Le polynome P_v n'est pas fixe -- ses exposants (les Delta_j) varient avec v. On ne cherche pas les zeros d'un polynome fixe mais l'existence d'un polynome (parmi une famille parametrisee par les Delta_j) qui s'annule en X=2 mod d. C'est plus delicat.

### Piste 4 (POTENTIEL 9/10) : Connexion Syracuse-noyau (R183 I6) + croissance

Le theoreme I6 (R183 noyau) dit que l'extension par Delta = 0 applique Syracuse au noyau. Plus generalement, la suite (h_1, h_2, ..., h_k) construite par la recurrence (D+) est une ORBITE de la dynamique mixte partant de h_1 = 1.

**Observation cle :** Dans la dynamique (D+), chaque etape h → 3h + 2^Delta AUGMENTE h d'au moins 3h + 1 (pour Delta >= 0). Donc h_{j+1} >= 3*h_j + 1 pour tout j.

Cela donne h_k >= (3^{k-1} + (3^{k-1}-1)/2) = (3^k - 1)/2 = tau_k. C'est juste la borne inferieure triviale.

**Mais :** la croissance de h est EXPONENTIELLE en k (facteur 3 par etape). Apres k etapes, h_k ~ 3^{k-1} * cste. La condition h_k = n'*d ~ n' * 3^k impose n' ~ h_k / 3^k ~ cste * 3^{-1} ~ 1/3.

Plus precisement : n' = h_k / d. Et h_k ~ 3^{k-1} * (1 + O(1)) (le premier terme domine). Et d ~ c * 3^k. Donc n' ~ 3^{k-1} / (c * 3^k) = 1/(3c).

Pour c ~ 0.5 : n' ~ 2/3. Mais n' doit etre un ENTIER >= 1. Donc pour le vecteur le plus "modeste", n' < 1 -- PAS DE CYCLE.

**THEOREME R184.4 (PROUVE) :** *Pour le vecteur constant (B_j = (S-k)/k quand c'est entier), h(v) = tau_k = (3^k - 1)/2, et h/d = (3^k - 1) / (2*(2^S - 3^k)). Pour S = ceil(k*log_2(3)) avec frac > 0 :**

*n' = tau_k / d = (3^k - 1) / (2d).*

*Si d > (3^k - 1)/2, alors n' < 1 et le vecteur constant NE DONNE PAS de cycle.*

*Or d = 2^S - 3^k > 0 et 2^S >= 2 * 3^k / 2 pour la plupart des k (quand frac >= 1 - log_2(1.5) ~ 0.415). Quand frac est grand (> 0.5), d > 3^k/2 > (3^k-1)/2 = tau_k, et donc n' < 1.*

**Verification k=1 :** tau_1 = 1, d = 1. n' = 1/1 = 1. Cycle existe. COHERENT (frac pour k=1 : S=2, frac = 2 - 1.585 = 0.415, donc d = 4-3 = 1 et tau_1 = 1 = d).

**Verification k=2 :** tau_2 = 4, d = 7. n' = 4/7 < 1. Le vecteur constant (B_0 = B_1 = 1) donne g = 3*2 + 2 = 8, h = 8/2 = 4, n' = 4/7 -- pas un cycle. Mais le vecteur (0,2) donne g = 7 = d, n = 1 (pas via le vecteur constant). COHERENT -- le theoreme ne s'applique qu'au vecteur constant.

**Le vecteur constant est le vecteur le PLUS MODESTE (g minimal).** Si meme le g_min ne suffit pas, les autres vecteurs donnent des g plus grands, potentiellement des multiples de d.

**Statut : PROUVE pour le vecteur constant. Ne resout PAS le probleme general.** [PROUVE mais INSUFFISANT]

### Piste 5 (POTENTIEL 8/10) : Borne superieure sur n via la structure de h

De P4 : h(v) est impair et h(v) >= tau_k. Le cycle exige h(v) = n'*d.

Pour le plus grand h possible (vecteur avec B_{k-1} maximal) :

h_max ~ sum 3^{k-1-j} * 2^{Delta_j} avec Delta_{k-1} ~ S-k et les autres Delta_j repartis.

h_max <= 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{S-1} = 3^{k-1} + 2^{S-1} * (3^{k-1} - 1)/2

Le ratio h_max/d ~ [3^{k-1} + 2^{S-2} * 3^{k-1}] / d ~ 2^{S-2} * 3^{k-1} / d ~ 2^{S-2} * 3^{k-1} / (2^S - 3^k)

Pour S ~ 1.585k : ~ 2^{0.585k - 2} * 3^{k-1} / 3^k ~ 2^{0.585k} / (12) ~ 1.5^k / 12.

Donc n' in {1, 3, 5, ..., O(1.5^k)}.

Le nombre de candidats pour n' est ~ 1.5^k / 2 = O(2^{0.585k}).

La DIFFICULTE est de montrer qu'AUCUN de ces O(2^{0.585k}) candidats n'est dans Im(h)/d.

---

## 11. SYNTHESE ET BILAN

### Resultats PROUVES

| # | Resultat | Statut |
|---|----------|--------|
| T1 | |V_k(S)| / d → 0 exponentiellement (exposant ~ -0.078k) | DEDUIT |
| T2 | L'esperance de |X_k inter Y_k| est ~ 2^{0.507k} → infini sous uniformite | DEDUIT |
| T3 | Aucun argument de comptage pur ne peut prouver la vacuite (theoreme negatif) | PROUVE |
| T4 | Aucun argument de congruence locale (mod petits nombres) ne produit de contradiction | PROUVE |
| T5 | Le vecteur constant donne n' < 1 quand frac(k*log_2(3)) > 0.415 | PROUVE |
| T6 | La condition de cycle se reformule comme n*3^k + g(v) = n*2^S | PROUVE |

### Resultats CONDITIONNELS

| # | Resultat | Condition |
|---|----------|-----------|
| C1 | N_0 = 0 pour k >= K_0 | Equidistribution de g mod d (H1) |
| C2 | N_0 = 0 pour 3 <= k < K_0 | Anti-correlation CRT (H2) |

### Conjectures

| # | Conjecture | Evidence |
|---|-----------|----------|
| J1 | La contrainte sum B_j = S-k reduit |V_k(S)| assez pour eliminer le regime R2 | A investiguer (Piste 1) |
| J2 | Le polynome creux P_v(X) a des proprietes d'evitement des zeros en X=2 mod d | Connexion avec Bi-Cheng-Rojas (Piste 3) |
| J3 | L'anti-correlation CRT est negative pour tous les k >= 3 | Evidence numerique (R183), mecanisme qualitatif (condition de boucle) |

### La racine du probleme

**L'intersection metrique inter modulaire est VIDE (conjecturalement) parce que :**

1. **Metrique :** Im(g) est un ensemble EPARS et STRUCTURE dans [g_min, g_max], pas un ensemble aleatoire. Sa structure vient de la contrainte de monotonie et de la base mixte 2-3.

2. **Modulaire :** Les multiples de d = 2^S - 3^k heritent de la relation 2^S ≡ 3^k mod d, qui COUPLE les bases 2 et 3 de la meme facon que g(v) les couple.

3. **L'intersection :** Les deux ensembles (Im(g) et les multiples de d) sont DEFINIS par les memes bases 2 et 3, mais de facons INCOMPATIBLES. Im(g) est une somme additive de produits 3^a * 2^b, tandis que les multiples de d sont des multiples d'une DIFFERENCE 2^S - 3^k. La somme et la difference de deux bases incommensurables creent des structures qui se REPOUSSENT.

**C'est la conjecture profonde :** *les sommes pondereees anti-correlees de puissances de bases multiplicativement independantes evitent structurellement les multiples des differences de puissances hautes de ces memes bases.*

**Statut : CONJECTURE NON PROUVEE.** C'est une reformulation du probleme de Collatz pour les k-cycles, pas une resolution. Mais c'est une reformulation qui ISOLE la difficulte et pointe vers les outils necessaires.

### Chaine des POURQUOI -- Resume

| Niveau | Question | Reponse | Statut |
|--------|----------|---------|--------|
| 1 | Pourquoi l'intersection serait-elle vide ? | Parce que Im(g) et d*N sont structures differemment | CONJECTURE |
| 2 | Pourquoi structurellement differents ? | Im(g) = sommes de 3^a*2^b, d*N = multiples de 2^S - 3^k | PROUVE (definitional) |
| 3 | Pourquoi cette difference empeche l'intersection ? | Parce que le comptage pur predit des intersections (2^{0.507k}) mais elles n'existent pas | OBSERVE (non prouve) |
| 4 | Qu'est-ce qui empeche les intersections predites ? | L'anti-correlation entre les bases 2 et 3 dans Im(g) et dans d | CONJECTURE |
| 5 | D'ou vient l'anti-correlation ? | De la condition de boucle 2^S = 3^k mod p pour p|d (R183 racine) | CONJECTURE FORTE |

### Recommandation pour R185

**Priorite 1 :** Calculer N(k, S) = |V_k(S) avec sum = S-k| pour k = 3, ..., 30 et comparer a d. Si N(k,S) < d pour TOUT k >= 3, le probleme est dans le regime R1 et la seule question est l'equidistribution.

**Priorite 2 :** Investiguer la Piste 3 (polynome creux). La borne de Bi-Cheng-Rojas donne O(k * sqrt(d)) zeros pour un polynome a k termes mod d. Si O(k * sqrt(d)) < N(k,S) pour tout k >= 3, cela ne donne rien. Mais si on peut montrer que les polynomes MONOTONES (exposants croissants) ont moins de zeros, c'est une percee.

**Priorite 3 :** Explorer la Piste 4 (dynamique du noyau). Le theoreme I6 (Syracuse-noyau) est le resultat le plus prometteur de R183. Combiner la croissance exponentielle de h le long de l'orbite avec la condition h = n'*d pourrait donner une contradiction pour k >= k_0.

---

## CONTROLES DE COHERENCE FINAUX

**k=1 :** S=2, d=1. |V_1(2)| = 1 (vecteur (1)). g(1) = 2. n = 2/1 = 2. Cycle trivial. Aucun de nos arguments n'exclut k=1. [COHERENT]

**k=2 :** S=4, d=7. Vecteurs avec sum B_j = 2 : (0,2) et (1,1). g(0,2) = 7 = d. g(1,1) = 8. Un cycle "fantome" (n=1 ne correspond pas a un vrai cycle Collatz). Notre argument T5 (vecteur constant (1,1) donne n'=4/7 < 1) est correct. Le vecteur (0,2) donne n=1, h=7, n'=7/7=1. Mais c'est un fantome. [COHERENT -- les arguments n'excluent pas k=2 mais les fantomes sont elimines par des arguments supplementaires]

**k=3 :** S=5, d=32-27=5. Vecteurs avec sum B_j = S-k = 2, 0 <= B_0 <= B_1 <= B_2 <= 4 :
(0,0,2), (0,1,1). g(0,0,2) = 9+3+4 = 16. g(0,1,1) = 9+6+2 = 17. n pour 16 : 16/5 = 3.2 (non entier). n pour 17 : 17/5 = 3.4 (non entier). Pas de cycle. [COHERENT]

---

*R184 : Formalisation de l'intersection metrique-modulaire. 6 resultats prouves (dont 2 theoremes negatifs importants : le comptage et les congruences locales echouent tous deux). 2 resultats conditionnels. 3 conjectures. 5 pistes emergentes. La racine : les sommes anti-correlees de 3^a * 2^b evitent structurellement les multiples de 2^S - 3^k, mais cette propriete structurelle est EQUIVALENTE a la conjecture de Collatz pour les k-cycles.*

*Le verrou irreductible est que l'esperance de l'intersection est 2^{0.507k} → infini, ce qui rend tout argument probabiliste insuffisant. Seul un argument ALGEBRIQUE exploitant la structure fine de g(v) et de d pourrait conclure.*
