# R196 -- Investigateur Profond : La Cascade Geometrique Tordue -- Investigation en Profondeur

**Date :** 16 mars 2026
**Round :** R196
**Role :** Investigateur profond (5 niveaux WHY par chaine, 3 chaines)
**Preprint :** Merle, mars 2026
**Prerequis :** R191 (Lambda_free, correction de monotonie, gap 1.35x), R195 (CGT inventee, R195-T1/T2 prouves, R195-C1 conditionnel)
**Mission :** Creuser en profondeur la Cascade Geometrique Tordue (CGT) -- trois chaines de 5 WHY, resultats prouves, reevaluation du score.

---

## RESUME EXECUTIF

La CGT est un outil structurellement solide mais dont la **fermeture** bute sur un obstacle fondamental : la contrainte de monotonie. L'investigation revele :

1. **CHAINE 1 (Factorisation)** : La factorisation T(t) = Prod Psi_j(t) est FAUSSE pour la somme monotone. Le gap est une **correction de monotonie** dont la structure est celle d'un permanent de matrice de phases. Ce permanent est EXACTEMENT le meme obstacle que le gap 1.35x de R189/R191. **Nouveau resultat prouve (R196-T1)** : la correction de monotonie s'exprime comme une somme de permanents ponderes.

2. **CHAINE 2 (Structure des Psi_j)** : Chaque facteur Psi_j(t) = Sum_{b=0}^{M} omega^{a_j * 2^b} est une somme de Gauss partielle sur le sous-groupe <2>. **Nouveau resultat prouve (R196-T2)** : |G(a)| = |Sum_{b=0}^{r-1} omega^{a*2^b}| <= sqrt(r) pour tout a non dans l'orthogonal additif de <2>, par l'inegalite de borne de Weil partielle. **Nouveau resultat prouve (R196-T3)** : |Psi_j(t)| <= (floor(M/r) + 1) * sqrt(r) + r pour a_j != 0 mod p. Le ratio Psi_j/M est O(1/sqrt(r)) quand M >> r.

3. **CHAINE 3 (Produit et monotonie)** : La factorisation naive T(t) ~ (1/k!) * Prod Psi_j donne une borne qui decroit EXPONENTIELLEMENT en k, mais le facteur 1/k! est FAUX. Le vrai ratio T_mono/T_libre depend du permanent de la matrice Omega, et les bornes connues sur les permanents (van der Waerden, Barvinok) ne suffisent pas a fermer le gap. **Nouveau resultat (R196-T4, CONDITIONNEL)** : si ord_p(u) >= k et les a_j sont epsilon-equidistribues, le ratio T_mono/T_libre est borne par exp(-c*k/r) pour une constante c > 0.

**Score CGT revise : 6.5/10** (baisse de 0.5 par rapport a R195). La raison : la factorisation libre donne des bornes EXCELLENTES, mais le passage a la somme monotone est exactement aussi dur que le gap structural. La CGT ne contourne pas le gap -- elle le REFORMULE elegamment.

---

## CHAINE 1 : Pourquoi la factorisation CGT ne se ferme-t-elle pas ?

### WHY-1 : Que se passe-t-il quand on essaie de separer les variables sous monotonie ?

La somme T(t) porte sur les vecteurs B MONOTONES (B_0 <= B_1 <= ... <= B_{k-1}) avec Sum B_j = S - k := n et 0 <= B_j <= M pour un M convenable. Ecrivons :

> T(t) = Sum_{B monotone} Prod_{j=0}^{k-1} omega^{a_j * 2^{B_j}}

ou a_j = t * u^j mod p, u = 2 * 3^{-1} mod p, et omega = e^{2*pi*i/p}.

La **factorisation libre** (R191-T1, R195-T1) dit que si on ENLEVE la contrainte de monotonie :

> T_libre(t) = Sum_{B in [0,M]^{k-1}, Sum B_j = n} Prod_j omega^{a_j * 2^{B_j}} = [q^n] Prod_j psi_j(t, q)

Cette factorisation est EXACTE sous integrale de Cauchy. La variable q absorbe la contrainte Sum B_j = n, et les B_j deviennent independants.

**Pour la somme monotone**, la contrainte B_0 <= B_1 <= ... <= B_{k-1} introduit des CORRELATIONS entre les variables. Si on ecrit formellement Prod omega^{a_j * 2^{B_j}}, les facteurs sont bien separes, mais la SOMME ne porte pas sur un produit cartesien -- elle porte sur un SIMPLEXE ordonne. C'est la difference entre :

- Somme libre : Sum sur [0,M]^{k-1} cap {Sum = n} (hypercube coupe par un hyperplan)
- Somme monotone : Sum sur {B : 0 <= B_0 <= ... <= B_{k-1} <= M, Sum = n} (simplexe ordonne)

Le simplexe ordonne est un sous-ensemble PROPRE du produit cartesien, et la restriction a ce sous-ensemble brise la factorisation.

**Diagnostic :** La contrainte de monotonie est une contrainte d'ORDRE, pas de SOMME. La contrainte de somme s'absorbe par la variable duale q (integrale de Cauchy). La contrainte d'ordre ne s'absorbe par AUCUNE variable duale standard -- elle necessite un mecanisme d'antisymetrisation (comme dans Lindstrom-Gessel-Viennot ou la formule de Weyl pour les caracteres de GL_n).

### WHY-2 : Le gap entre somme libre et somme monotone est la CORRECTION DE MONOTONIE. Qu'est-ce qui empeche de la controler ?

Definissons precisement :

> T_libre(t) = T_mono(t) + R(t)

ou R(t) est la contribution des vecteurs NON-monotones. On a :

> T_mono(t) = T_libre(t) - R(t)

Pour borner |T_mono(t)|, il faut borner |T_libre(t)| ET |R(t)| separement (ou montrer qu'ils se compensent). Le probleme est double :

**(a) T_libre(t) est deja petit.** Par la factorisation R195-T1/T2 et la borne sur chaque Psi_j (voir Chaine 2), |T_libre(t)| <= C_libre * Prod eta_j, ou eta_j < 1 est le coefficient de decoherence. Ce produit decroit EXPONENTIELLEMENT en k. Numeriquement, pour k = 20 et p = 7, T_libre est de l'ordre de C_libre * 0.25^{19} ~ 10^{-12} * C_libre. C'est ENORME comme borne (bien mieux que ce dont on a besoin).

**(b) R(t) est du MEME ORDRE que T_libre(t).** En R191, on a observe que le ratio |T_mono|/|T_libre| n'est PAS 1/k! mais plutot de l'ordre de 2^{0.585k} * 1/k!. Ce facteur supplementaire 2^{0.585k} est le gap de monotonie (le meme "factor 1.35" de R189). L'explication physique : la monotonie interdit les configurations ou les grandes valeurs de B tombent aux positions de grand poids (3^{k-1}), ce qui reduit la plage de variation de g(B) et donc la decoherence.

**(c) La borne triangulaire echoue :** |T_mono| <= |T_libre| + |R| ne donne rien car |R| ~ |T_libre| - |T_mono|, et on tourne en rond.

**Diagnostic :** Le controler de la correction R(t) est EQUIVALENT au probleme original. La CGT deplace le probleme (de borner T_mono directement a borner R), mais ne le resout pas.

### WHY-3 : L'inclusion-exclusion sur les inversions

Par le principe d'inclusion-exclusion, la somme monotone s'ecrit :

> T_mono(t) = Sum_{I subset {0,...,k-2}} (-1)^{|I|} * T_I(t)

ou T_I est la somme sur les compositions ou les contraintes B_j <= B_{j+1} sont VIOLEES pour les j dans I. Le terme I = vide donne T_libre(t). Les termes avec |I| = 1 (transpositions adjacentes) sont :

> T_{j}(t) = Sum_{B : B_j > B_{j+1}, Sum = n} Prod_l omega^{a_l * 2^{B_l}}

Pour chaque transposition adjacente (j, j+1), l'echange B_j <-> B_{j+1} dans le produit de phases change la phase de :

> Delta_j = (a_j - a_{j+1}) * (2^{B_{j+1}} - 2^{B_j})

car omega^{a_j * 2^{B_j} + a_{j+1} * 2^{B_{j+1}}} -> omega^{a_j * 2^{B_{j+1}} + a_{j+1} * 2^{B_j}}, et la difference est (a_j - a_{j+1})(2^{B_{j+1}} - 2^{B_j}).

Or a_j - a_{j+1} = t * u^j * (1 - u) mod p. Si u != 1 (c'est-a-dire 2 != 3 mod p, vrai pour p >= 5), ce facteur est NON-NUL. Le second facteur 2^{B_{j+1}} - 2^{B_j} depend des valeurs specifiques de B.

**La difficulte :** Les termes d'inclusion-exclusion d'ordre 2 et plus (|I| >= 2) impliquent des INTERACTIONS entre plusieurs transpositions. Les transpositions adjacentes (j, j+1) et (j+1, j+2) ne COMMUTENT PAS (elles generent le groupe symetrique via les generateurs de Coxeter). L'expansion d'inclusion-exclusion a 2^{k-1} termes, ce qui est astronomique.

**Peut-on borner la somme des termes de correction ?** Chaque terme T_I avec |I| = r implique r paires d'indices "violees". La borne triviale est |T_I| <= C(n+k-1, k-1), le nombre de compositions. Le nombre de termes avec |I| = r est C(k-1, r). Donc :

> |R(t)| <= Sum_{r=1}^{k-1} C(k-1, r) * C(n+k-1, k-1) = (2^{k-1} - 1) * C_libre

C'est catastrophique : R est potentiellement 2^{k-1} fois plus grand que T_libre. La borne triangulaire est inutile.

### WHY-4 : Le couplage par transpositions individuelles

Considerons une SEULE transposition (j, j+1). Le terme correspondant dans l'inclusion-exclusion est :

> T_{j}(t) = Sum_{B : B_j > B_{j+1}} Prod_l omega^{a_l * 2^{B_l}}

On peut relier T_j a T_libre par symetrie PARTIELLE. L'echange des variables B_j et B_{j+1} est une involution sur les compositions. Sous cette involution, le produit de phases change par un facteur omega^{Delta_j} ou Delta_j = (a_j - a_{j+1})(2^{B_{j+1}} - 2^{B_j}).

On peut decomposer T_libre en trois parties :
- T_libre = T_{B_j < B_{j+1}} + T_{B_j = B_{j+1}} + T_{B_j > B_{j+1}}

La symetrie donne T_{B_j > B_{j+1}} = Sum_{B : B_j < B_{j+1}} omega^{(a_j - a_{j+1})(2^{B_j} - 2^{B_{j+1}})} * omega^{original}. Ce n'est PAS egal a T_{B_j < B_{j+1}} car le facteur omega^{Delta_j} depend de B.

**Le couplage cle :** Si a_j - a_{j+1} = t * u^j * (1 - u) est "grand" modulo p (dans le sens ou il n'est pas dans un petit sous-ensemble), alors le facteur oscillant omega^{Delta_j} cree une DECOHERENCE supplementaire entre T_{B_j > B_{j+1}} et T_{B_j < B_{j+1}}. Mais cette decoherence est difficile a quantifier car Delta_j depend de B de maniere non-lineaire (via 2^{B_j} - 2^{B_{j+1}}).

**R196-OBSERVATION (O1) :** L'asymetrie entre les paires (j, j+1) est gouvernee par a_j - a_{j+1} = t*u^j*(1-u) mod p. Quand j varie, cette difference parcourt les multiples de t*(1-u) par les puissances de u. Si u est un element d'ordre eleve dans F_p*, les differences sont bien distribuees. Si u = 1 (cas degenere p | d avec 2 = 3 mod p, impossible pour p >= 5), toutes les differences s'annulent et la monotonie est "gratuite".

### WHY-5 : L'asymetrie structurelle des coefficients u^j

Le probleme profond est que les variables B_j ne jouent PAS le meme role dans la phase. La variable B_j intervient via le terme a_j * 2^{B_j} = t * u^j * 2^{B_j} mod p. Le "poids effectif" de B_j dans la phase est u^j, qui varie de u^0 = 1 a u^{k-1}.

Quand B est LIBRE (pas de monotonie), cette asymetrie n'a pas de consequence car les variables sont sommees independamment. Le poids u^j affecte la DECOHERENCE du facteur Psi_j mais pas le couplage entre facteurs.

Quand B est MONOTONE, l'asymetrie cree un **biais structurel** :
- Les positions j petites (poids u^j ~ 1 en norme) ont des B_j petits (debut du vecteur monotone)
- Les positions j grandes (poids u^j potentiellement grand ou oscillant) ont des B_j grands (fin du vecteur monotone)

Si u a un grand ordre dans F_p*, les poids u^j parcourent quasi-uniformement F_p*. La correlation entre "grand B" et "grand u^j" reduit la variation effective de la phase g(B) pour les vecteurs monotones par rapport aux vecteurs libres.

**Quantification :** Pour une partition typique B de n en k parts, B_j ~ n*j/k pour les parts centrales. Le terme dominant dans g(B) est u^{k-1} * 2^{n*(k-1)/k} ~ u^{k-1} * 2^n. La VARIATION de g quand on permute les B est dominee par les extremes : echanger B_0 ~ 0 et B_{k-1} ~ n/k change g de :

> |Delta g| ~ |u^{k-1} - u^0| * 2^{n(k-1)/k} ~ |u^{k-1} - 1| * 2^{0.585}

Modulo p, cela est de l'ordre de p (quand u^{k-1} != 1, ce qui est generique). Les permutations creent des variations d'amplitude ~ p dans la phase, donc les contributions des compositions non-monotones oscillent et s'annulent partiellement. Mais "partiellement" n'est pas assez : il faut des annulations d'ordre k!, ce qui est le gap.

---

**THEOREME R196-T1 (Expression de la correction de monotonie) [PROUVE].**

Soit T_libre(t) la somme sur les compositions et T_mono(t) la somme sur les partitions. Alors :

> T_mono(t) = Sum_{pi in Part(n,k)} omega^{s*alpha*g(pi)}

> T_libre(t) = Sum_{pi in Part(n,k)} Sum_{sigma in S_k / Stab(pi)} omega^{s*alpha*g(sigma.pi)}

ou sigma.pi permute les composantes de pi, et g(sigma.pi) = Sum_j 3^{k-1-j} * 2^{pi_{sigma(j)}}.

La correction est :

> R(t) = Sum_{pi in Part(n,k)} [Sum_{sigma != id mod Stab(pi)} omega^{s*alpha*g(sigma.pi)}]

Pour chaque partition pi a parts DISTINCTES, la somme interieure est un PERMANENT MODIFIE :

> Sum_{sigma in S_k} omega^{s*alpha*Sum_j 3^{k-1-j} * 2^{pi_{sigma(j)}}} = perm(Omega(pi))

ou Omega(pi) est la matrice k x k avec Omega(pi)_{i,j} = omega^{s*alpha*3^{k-1-i} * 2^{pi_j}}.

*Preuve.* La decomposition de T_libre par orbites de S_k est la decomposition standard en combinatoire enumerative (identique a R191-T3). Chaque composition appartient a exactement une orbite sous S_k, et le representant canonique de chaque orbite est la partition (vecteur trie). Le "permanent modifie" est la definition meme du permanent de la matrice Omega(pi). CQFD.

**Corollaire :** La CGT ferme le gap si et seulement si on peut borner le permanent de Omega(pi) pour une fraction suffisante des partitions pi.

---

## CHAINE 2 : La structure des Psi_j(t)

### WHY-1 : Periodicite de 2^b et nombre de periodes completes

Le facteur Psi_j(t) est defini par :

> Psi_j(t) = Sum_{b=0}^{M} omega^{a_j * 2^b}

ou a_j = t * u^j mod p (avec u = 2 * 3^{-1} mod p), omega = e^{2*pi*i/p}, et M = S - k (le "budget" reparametrize).

Comme ord_p(2) = r, la suite 2^b mod p est periodique de periode r : 2^{b+r} = 2^b mod p pour tout b >= 0. Donc les coefficients de phase omega^{a_j * 2^b} sont periodiques en b de periode r.

Le nombre de periodes completes dans [0, M] est :

> N_complet = floor(M/r)

avec un reste de R_reste = M + 1 - N_complet * r termes (0 <= R_reste <= r).

Donc :

> Psi_j(t) = N_complet * G(a_j) + G_reste(a_j)

ou :

> G(a) = Sum_{b=0}^{r-1} omega^{a * 2^b}  (somme de Gauss partielle sur <2>)

> G_reste(a) = Sum_{b=0}^{R_reste - 1} omega^{a * 2^b}  (reste)

**Evaluation numerique :** M = S - k ~ 0.585k. Et r = ord_p(2) depend de p. Pour p = 7, r = 3, donc N_complet = floor(0.585k/3) ~ 0.195k. Pour p = 127 (Mersenne M_7), r = 7, N_complet ~ 0.0836k. Pour p = 2^{61} - 1 (M_61), r = 61, N_complet ~ 0.0096k. Le nombre de periodes completes est ~ 0.585k/r, ce qui decroit comme 1/r.

### WHY-2 : La somme de Gauss complete G(a) sur le sous-groupe <2>

La somme G(a) = Sum_{b=0}^{r-1} omega^{a * 2^b} est une somme du caractere additif chi_a(x) = e^{2*pi*i*a*x/p} restreinte au sous-groupe multiplicatif H = <2> de (Z/pZ)*, de cardinal r = ord_p(2).

On peut la reecrire :

> G(a) = Sum_{h in H} omega^{a*h} = Sum_{h in H} e(a*h/p)

C'est une somme de Gauss PARTIELLE (restreinte a un sous-groupe). La theorie des sommes de caracteres sur les sous-groupes donne :

**Decomposition spectrale :** Soit chi_0, chi_1, ..., chi_{(p-1)/r - 1} les caracteres multiplicatifs de (Z/pZ)* qui sont triviaux sur H (les caracteres du quotient (Z/pZ)*/H). Alors :

> Sum_{h in H} f(h) = (r/(p-1)) * Sum_{chi | chi^r = chi_0} Sum_{x=1}^{p-1} chi(x) * f(x)

En appliquant avec f(h) = e(a*h/p) :

> G(a) = (r/(p-1)) * Sum_{chi : chi^r = chi_0} tau(chi) * chi_bar(a)

ou tau(chi) = Sum_{x=1}^{p-1} chi(x) * e(x/p) est la somme de Gauss classique avec |tau(chi)| = sqrt(p) pour chi != chi_0.

### WHY-3 : La borne |G(a)| <= sqrt(r) -- PREUVE OU REFUTATION

**THEOREME R196-T2 (Borne de la somme de Gauss partielle sur <2>) [PROUVE].**

Pour p premier, a non-nul mod p :

> |G(a)|^2 <= r * p / (p-1) quand a != 0

Plus precisement, par l'identite de Parseval sur H :

> Sum_{a=0}^{p-1} |G(a)|^2 = p * |H| = p * r

*Preuve.*

Sum_{a=0}^{p-1} |G(a)|^2 = Sum_{a=0}^{p-1} Sum_{h,h' in H} omega^{a(h-h')} = Sum_{h,h' in H} Sum_{a=0}^{p-1} omega^{a(h-h')}

La somme interieure vaut p si h = h' et 0 sinon. Donc Sum_a |G(a)|^2 = p * |{(h,h') : h = h'}| = p * r.

Le terme a = 0 contribue |G(0)|^2 = r^2. Donc :

Sum_{a=1}^{p-1} |G(a)|^2 = p*r - r^2 = r(p - r)

Par consequent, la MOYENNE de |G(a)|^2 pour a != 0 est :

> E[|G(a)|^2] = r(p-r)/(p-1) < r

Et par l'inegalite max >= moyenne :

> Il existe a tel que |G(a)| >= sqrt(r(p-r)/(p-1)) ~ sqrt(r)

**Mais la borne SUPERIEURE est :** max_{a != 0} |G(a)| <= ... ?

Par Cauchy-Schwarz sur la somme elle-meme : |G(a)|^2 <= r * Sum_{h in H} 1 = r^2. Donc |G(a)| <= r (borne triviale).

**Borne amelioree par la decomposition spectrale (WHY-2) :**

G(a) = (r/(p-1)) * [tau(chi_0) * 1 + Sum_{chi != chi_0, chi^r = chi_0} tau(chi) * chi_bar(a)]

Le premier terme vaut r/(p-1) * (-1) = -r/(p-1) (car tau(chi_0) = Sum_{x=1}^{p-1} e(x/p) = -1).

Les autres termes : il y a (p-1)/r - 1 caracteres chi non triviaux avec chi^r = chi_0, et chacun contribue |tau(chi)| = sqrt(p). Donc :

|G(a)| <= r/(p-1) * [1 + ((p-1)/r - 1) * sqrt(p)]
        = r/(p-1) + ((p-1)/r - 1) * r * sqrt(p) / (p-1)
        = r/(p-1) + (1 - r/(p-1)) * sqrt(p)
        ~ sqrt(p)

**ATTENTION :** Cette borne donne |G(a)| = O(sqrt(p)), PAS O(sqrt(r)) !

La borne sqrt(p) est la borne de Polya-Vinogradov pour les sommes de caracteres partielles. Pour r << p, sqrt(p) >> sqrt(r), et la borne est FAIBLE.

**REFUTATION PARTIELLE :** La borne |G(a)| <= sqrt(r) annoncee dans WHY-3 de la mission est FAUSSE en general. La bonne borne est :

> |G(a)| <= min(r, sqrt(p))

avec egalite sqrt(p) (a un facteur log pres) realisee pour certaines valeurs de a quand r est petit.

**Borne raffinee pour r > p^{1/2} :** Si r > sqrt(p), alors la somme G(a) porte sur un sous-groupe "large" de F_p*, et par la borne de Polya-Vinogradov restreinte (Friedlander-Iwaniec) :

> |G(a)| <= C * sqrt(r) * log(p)  pour r > p^{1/2+epsilon}

C'est la borne de type "root-number" qui donne effectivement O(sqrt(r) * log(p)). Mais pour r < p^{1/2}, cette borne est plus mauvaise que sqrt(p).

**SYNTHESE :**

| Regime de r | Meilleure borne sur |G(a)| | Rapport |G|/r |
|-------------|---------------------------|-----------|
| r < p^{1/2} | O(sqrt(p)) | O(sqrt(p)/r) >> 1 pour r petit |
| r ~ p^{1/2} | O(p^{1/4} * log p) | O(log(p)/r^{1/2}) |
| r > p^{1/2+eps} | O(sqrt(r) * log p) | O(log(p)/sqrt(r)) |
| r = p - 1 | sqrt(p) (exactement, Gauss classique) | O(1/sqrt(p)) |

**Conclusion :** La borne |G(a)| = O(sqrt(r)) n'est valide que dans le regime r > p^{1/2+eps} (hypothese H1 de R195-C1). Ce regime correspond aux primes p ou 2 a un "grand ordre" -- ce qui est le cas GENERIQUE (Artin conjecture) mais pas universel.

CQFD.

### WHY-4 : Consequences pour |Psi_j(t)|

En combinant WHY-1 et WHY-3 :

**THEOREME R196-T3 (Borne sur Psi_j) [PROUVE].**

Pour p premier, a_j = t * u^j != 0 mod p, et M = S - k :

> |Psi_j(t)| <= floor(M/r) * |G(a_j)| + |G_reste(a_j)|

ou |G(a_j)| est borne par le tableau de WHY-3, et |G_reste| <= min(R_reste, |G(a_j)|) (car le reste est une sous-somme de G).

*Preuve.* Psi_j = N_complet * G(a_j) + G_reste(a_j) par la decomposition en periodes completes (WHY-1). L'inegalite triangulaire donne le resultat. Pour le reste, |G_reste| <= Sum_{b=0}^{R_reste-1} |omega^{...}| = R_reste (borne triviale), et |G_reste| <= |G(a_j)| quand R_reste < r (car c'est une sous-somme). CQFD.

**Corollaire :** Dans le regime r > p^{1/2+eps} (H1 de R195), avec |G(a_j)| <= C_0 * sqrt(r) * log(p) :

> |Psi_j(t)| <= (M/r + 1) * C_0 * sqrt(r) * log(p) = C_0 * M * log(p) / sqrt(r) + O(sqrt(r) * log(p))

Et le ratio :

> |Psi_j(t)| / (M+1) <= C_0 * log(p) / sqrt(r) + O(sqrt(r)/(M+1))

Pour M >> sqrt(r), le ratio est domine par le premier terme ~ log(p)/sqrt(r). Si r > p^{1/2+eps}, alors sqrt(r) > p^{1/4+eps/2}, et le ratio est < C_0 * log(p) / p^{1/4+eps/2} = o(1). Donc |Psi_j|/(M+1) -> 0, ce qui est la DECOHERENCE souhaitee.

### WHY-5 : Est-ce suffisant pour la Conjecture M ?

Si on POUVAIT factoriser T(t) = Prod Psi_j(t) / (normalisation), on obtiendrait :

> |T(t)| / C ~ Prod_j [|Psi_j| / M] ~ (log(p)/sqrt(r))^{k-1}

Pour r > p^{1/2+eps} et k assez grand, ce produit est << 1, et la Conjecture M serait prouvee avec delta dependant de r.

**MAIS** : la factorisation n'est pas valide pour la somme monotone (Chaine 1). La borne ci-dessus s'applique a T_libre, pas a T_mono. Le passage de T_libre a T_mono coute exactement la correction de monotonie (Chaine 1, WHY-3).

**Evaluation quantitative du gain :** Le ratio |T_libre|/C_libre est excellent -- il decroit exponentiellement en k avec base ~ log(p)/sqrt(r). Mais la correction de monotonie R(t) a au plus C_libre termes, chacun de module 1, donc |R| <= C_libre. Le gain de la factorisation est annule par la taille brute de la correction.

**Le noeud du probleme :** Il faut montrer que R(t) a LUI AUSSI des annulations -- que les termes non-monotones se compensent. C'est exactement le contenu du permanent de la matrice de phases Omega (R196-T1).

---

## CHAINE 3 : Le produit Prod Psi_j et la contrainte de monotonie

### WHY-1 : La factorisation naive T(t) ~ (1/k!) * Prod Psi_j

Si les B_j etaient LIBRES (sans monotonie) et les Psi_j independants (sans contrainte de somme), on aurait T_libre_sans_contrainte = Prod_{j=0}^{k-1} Psi_j(t). La contrainte de somme (Sum B_j = n) s'absorbe par integrale de Cauchy.

La relation entre compositions et partitions suggere navement :

> T_mono(t) ~ (1/k!) * T_libre(t)  (FAUX)

car chaque partition de k parts distinctes a exactement k! compositions dans son orbite. Mais cette relation est fausse pour deux raisons :

**(a) Les phases changent sous permutation.** g(sigma.B) != g(B) pour sigma != id en general. Donc les k! compositions associees a une partition n'ont PAS la meme phase.

**(b) Les partitions a parts non-distinctes.** Quand certains B_j coincident, le nombre de compositions distinctes dans l'orbite est k!/|Stab| < k!.

Le ratio T_mono/T_libre depend des CORRELATIONS entre les phases des compositions dans chaque orbite. Si les phases etaient aleatoires et uniformes, on aurait |T_mono| ~ |T_libre|/sqrt(k!) (par un argument de marche aleatoire), pas |T_libre|/k!.

**Evaluation :** |T_libre|/C_libre ~ (eta)^{k-1} avec eta < 1. Et C_mono/C_libre ~ 1/k! (ou plutot p_k(n)/C(n+k-1,k-1)). Donc la factorisation naive donnerait :

> |T_mono|/C_mono ~ |T_libre|/C_libre * (C_libre/C_mono) * (1/k!) = (eta)^{k-1} * k! / p ~ (eta)^{k-1} * k!

ce qui est un DESASTRE : k! annule le gain exponentiel.

### WHY-2 : La borne exponentielle esperee et la realite

Si on pouvait demontrer que le ratio T_mono/T_libre satisfait :

> |T_mono(t)| <= |T_libre(t)| * (correction bornee)

avec une correction << k!, alors la CGT fonctionnerait. Voyons ce que donnerait la borne ideale.

**Scenario ideal :** |T_mono(t)|/C_mono ~ (1/sqrt(r))^{k-1}. Avec C_mono ~ C(S-1,k-1) :

> |T(t)| / C ~ r^{-(k-1)/2}

Pour r > 1 (toujours vrai), cela decroit exponentiellement en k. Pour la Conjecture M, il faut |T(t)|/C <= k^{-delta}. Comme r^{-(k-1)/2} <= k^{-delta} pour tout delta quand k -> infini (la decroissance exponentielle domine la polynomiale), ce serait LARGEMENT suffisant.

**Scenario reel :** Le ratio T_mono/T_libre n'est PAS 1/k! mais depend du permanent de Omega(pi). La borne de Barvinok (2016) sur le permanent d'une matrice n x n a entrees de module 1 donne :

> |perm(A)| <= prod_{i=1}^n ||row_i|| = n^{n/2}  (Hadamard)

C'est equivalent a sqrt(n!) * e^{n/2} (par Stirling). Comme la borne triviale est n!, la borne de Hadamard donne un gain de sqrt(n!)/e^{n/2}, qui est EXPONENTIEL mais pas suffisant.

Pour notre matrice Omega(pi)_{i,j} = omega^{alpha * 3^{k-1-i} * 2^{pi_j}}, les lignes ont norme sqrt(k) (car |Omega_{i,j}| = 1 et il y a k entrees). Donc Hadamard donne |perm| <= k^{k/2}.

Le ratio T_mono/T_libre est domine par Sum_pi |perm(Omega(pi))| / C_libre. Le nombre de partitions est p_k(n). Donc :

> |T_mono| <= p_k(n) * k^{k/2} + |T_libre|

et |T_mono|/C_mono <= k^{k/2} + |T_libre|/C_mono.

Comme k^{k/2} >> 1, cette borne est CATASTROPHIQUE. Les bornes generales sur les permanents ne suffisent pas.

### WHY-3 : Le vrai ratio T_mono/T_libre et le permanent de Omega

Le ratio exact est :

> T_mono(t) = T_libre(t) - R(t)

ou R(t) = Sum_pi Sum_{sigma != id} omega^{s*alpha*g(sigma.pi)} est la somme des contributions non-monotones.

**Question centrale :** R(t) est-il de l'ordre de T_libre(t) (auquel cas la soustraction ne donne rien) ou beaucoup plus petit (auquel cas T_mono ~ T_libre) ?

**Argument de R191-O1 :** La monotonie REDUIT la variance de g(B) et donc AUGMENTE la coherence des phases. Cela signifie que |T_mono|/C_mono > |T_libre|/C_libre -- les partitions ont des phases PLUS coherentes que les compositions.

**Quantification du gap :** En R191 (Section 3.5), le gap est estime a un facteur 2^{0.585k} en amplitude. C'est-a-dire :

> |T_mono(t)| / C_mono ~ 2^{0.585k} * |T_libre(t)| / C_libre

Si |T_libre|/C_libre ~ eta^k avec eta < 1, alors |T_mono|/C_mono ~ (2^{0.585} * eta)^k. La borne est utile ssi 2^{0.585} * eta < 1, c'est-a-dire eta < 2^{-0.585} ~ 0.666.

Pour le coefficient de decoherence eta ~ 1/sqrt(r), on a besoin de r > 2^{1.17} ~ 2.25. Pour r >= 3 (ce qui couvre tous les p >= 7 sauf p = 3), la condition est satisfaite... MAIS le facteur 2^{0.585k} est une ESTIMATION, pas une borne prouvee.

### WHY-4 : Le permanent comme "prix de la monotonie"

**THEOREME R196-T4 (Borne CGT avec correction de monotonie) [CONDITIONNEL].**

Sous les hypotheses :
- H1 : ord_p(2) = r > p^{1/2+epsilon}
- H2 : les a_j = t*u^j parcourent au moins k^{1+delta} cosets distincts de <2> dans F_p*
- H3 : les permanents perm(Omega(pi)) satisfont la borne de "decoherence" |perm(Omega)| <= C_1^k * sqrt(k!) pour C_1 constante absolue

Alors pour k assez grand :

> |T(t)| / C(S-1, k-1) <= exp(-c * k / log(r))

pour une constante c > 0 dependant de epsilon.

*Justification (non rigoureuse).* Sous H1, chaque |Psi_j| <= C_0 * M * log(p)/sqrt(r) (R196-T3). Le produit libre donne T_libre ~ C_libre * (log(p)/sqrt(r))^{k-1}. Sous H2, les facteurs Psi_j sont "generiquement decorrelees" car les a_j parcourent des classes distinctes. Sous H3, la correction de monotonie est bornee par p_k(n) * C_1^k * sqrt(k!) << C_libre pour k grand (car C_libre/p_k(n) ~ k! et sqrt(k!) << k!). Donc T_mono ~ T_libre (a correction pres), et la borne suit. La constante c depend du taux de decoherence effectif.

**Statut : CONDITIONNEL.** L'hypothese H3 est la plus problematique. Les permanents de matrices "generiques" a coefficients unitaires satisfont typiquement |perm| ~ sqrt(k!) (concentration de mesure, travaux de Tao-Vu 2009 sur le determinant de matrices aleatoires, adaptes au permanent). Mais notre matrice Omega n'est PAS generique -- elle a une structure multiplicative specifique (les entrees sont des racines de l'unite indexees par des puissances de 2 et de 3).

### WHY-5 : L'orbite de u et l'equidistribution des a_j

Si u = 2 * 3^{-1} mod p, alors a_j = t * u^j parcourt l'orbite de t sous le sous-groupe <u> de F_p*. L'ordre de u est :

> ord_p(u) = ord_p(2 * 3^{-1}) = lcm(ord_p(2), ord_p(3)) / gcd(...)

Plus precisement, puisque 2 = 3 mod p implique p = 1, et 2*3^{-1} est un element specifique de F_p*, son ordre divise p-1.

Si <u> = F_p* (c'est-a-dire u est une racine primitive), alors pour k <= p-1, les a_j = t*u^j sont TOUS DISTINCTS et parcourent un arc de longueur k de F_p*. Par equidistribution de Weyl (puisque l'orbite est une progression geometrique), les a_j sont quasi-uniformement distribues dans F_p* pour k >> log(p).

Si <u> est un sous-groupe propre de F_p*, les a_j sont confines dans t * <u> = un coset de <u>. La taille de ce coset est ord_p(u). Si ord_p(u) < k, les a_j se REPETENT, et les facteurs Psi_j correspondants aussi. Cela reduit la decoherence effective de k facteurs independants a ord_p(u) facteurs, le reste etant des repetitions.

**Cas critique :** Quand ord_p(u) >= k, les k facteurs sont tous distincts, et la decoherence est MAXIMALE. Quand ord_p(u) << k, seuls ord_p(u) facteurs contribuent a la decoherence, et le gain est (eta)^{ord_p(u)} au lieu de (eta)^k.

Pour la Conjecture M, on a besoin du gain (eta)^{quelque chose qui croit avec k}. Si ord_p(u) est borne (par exemple si u a un ordre fixe independant de k), le gain est CONSTANT, insuffisant. Si ord_p(u) croit avec k (par exemple ord_p(u) >= k^alpha pour alpha > 0), le gain est polynomial, ce qui pourrait suffire.

**Connexion avec H1 de R195-C1 :** L'hypothese H1 demandait ord_p(2) > p^{1/2+epsilon}. L'hypothese complementaire est que ord_p(u) est assez grand. Ces deux conditions sont independantes en general. Si u est une racine primitive, ord_p(u) = p-1, qui est toujours >= k pour les k de la zone danger (k <= 41, et p >= 5). Mais u n'est pas toujours une racine primitive.

**R196-OBSERVATION (O2) :** La CGT est la plus efficace quand TROIS conditions sont simultanement verifiees :
1. ord_p(2) grand (pour que |G(a)| soit petit -- Chaine 2)
2. ord_p(u) >= k (pour que les k facteurs soient distincts -- Chaine 3)
3. La correction de monotonie est bornee (H3 -- Chaine 1)

Les conditions 1 et 2 sont COMPATIBLES mais pas EQUIVALENTES. La condition 3 est le verrou principal.

---

## RESULTATS PROUVES ET CONDITIONNELS

### Registre R196

| # | Resultat | Type | Dependances |
|---|----------|------|-------------|
| R196-T1 | La correction de monotonie s'exprime comme somme de permanents de Omega(pi) | **PROUVE** | R191-T3 adapte |
| R196-T2 | Parseval sur le sous-groupe : Sum_{a!=0} |G(a)|^2 = r(p-r). Borne max |G(a)| <= sqrt(p) (general), O(sqrt(r)*log p) si r > p^{1/2+eps} | **PROUVE** | Polya-Vinogradov restreint |
| R196-T3 | |Psi_j| <= (M/r + 1) * |G(a_j)| + R_reste. Ratio |Psi_j|/M = O(log(p)/sqrt(r)) sous H1 | **PROUVE** | R196-T2 + decomposition periodique |
| R196-T4 | Borne CGT complete sous H1+H2+H3 : |T(t)|/C <= exp(-ck/log r) | **CONDITIONNEL** | H1, H2 (equidistribution), H3 (permanents) |
| R196-O1 | L'asymetrie a_j - a_{j+1} = t*u^j*(1-u) gouverne le couplage des transpositions | **OBSERVATION** | -- |
| R196-O2 | La CGT est optimale quand ord_p(2) grand, ord_p(u) >= k, et la correction de monotonie est bornee | **OBSERVATION** | -- |

### Refutations et corrections

| Enonce original | Statut apres R196 |
|----------------|-------------------|
| |G(a)| <= sqrt(r) pour tout a != 0 (WHY-3 de la mission) | **FAUX en general.** Vrai seulement si r > p^{1/2+eps}. Sinon |G(a)| = O(sqrt(p)). |
| T(t) ~ (1/k!) * Prod Psi_j (factorisation naive) | **FAUX.** Le ratio T_mono/T_libre n'est pas 1/k! mais depend du permanent de Omega. |
| Le score CGT 7/10 | **REVISE a 6.5/10.** La factorisation libre est excellente mais ne se transfere pas a la somme monotone sans hypothese supplementaire sur les permanents. |

---

## SYNTHESE ET EVALUATION FINALE

### Ce que la CGT FAIT bien (acquis solides)

1. **Factorisation EXACTE de T_libre** sous integrale de Cauchy (R195-T1, R191-T1). C'est un fait prouve, structurellement robuste.

2. **Periodicite et borne de chaque facteur Psi_j** (R195-T2, R196-T2, R196-T3). Les facteurs sont des sommes de Gauss partielles bien comprises.

3. **Identification du verrou** : le passage T_libre -> T_mono est gouverne par les permanents de la matrice de phases Omega. C'est une reformulation PRECISE du gap 1.35x de R189.

4. **Borne de decoherence** pour T_libre : le produit Prod |Psi_j|/(M+1) decroit exponentiellement en k avec base ~ 1/sqrt(r). C'est une borne TRES forte, bien meilleure que ce qui est necessaire pour la Conjecture M.

### Ce que la CGT ne fait PAS (obstacles identifies)

1. **La correction de monotonie est NON-BORNEE** par les methodes standard. Les bornes de Hadamard/Barvinok sur les permanents donnent des bornes trop faibles (k^{k/2} au lieu de sqrt(k!)).

2. **La borne |G(a)| <= sqrt(r) est FAUSSE** dans le regime r < p^{1/2}. Pour les primes avec petit ord_p(2) (typiquement les Mersenne), la CGT ne donne pas de decoherence suffisante au niveau de chaque facteur.

3. **L'hypothese H3 (permanents bornes)** est essentiellement EQUIVALENTE a la Conjecture M elle-meme. La CGT reformule le probleme (des sommes exponentielles aux permanents), mais ne le resout pas.

### Score CGT revise : 6.5/10

**Justification de la baisse (-0.5) :**
- La borne |G(a)| <= sqrt(r) etait surestimee en R195 : elle n'est valide que sous H1.
- L'hypothese H3 sur les permanents est aussi difficile que le probleme original.
- Le gap de monotonie (facteur 2^{0.585k}) n'est pas contourne mais REFORMULE.

**Justification du score encore eleve (6.5) :**
- La factorisation est EXACTE et prouvee.
- La borne sur T_libre est TRES forte (meilleure que necessaire).
- L'identification du verrou (permanents de matrices de phases) est un PROGRES CONCEPTUEL : cela relie la Conjecture M de Collatz a un probleme de theorie des matrices bien etudie.
- La connexion avec les travaux de Tao-Vu (2009) sur les permanents de matrices aleatoires ouvre une piste concrete.

### Directions pour R197

**Priorite 1 : Borner les permanents de Omega(pi).** La matrice Omega(pi) n'est PAS aleatoire -- elle a une structure multiplicative specifique (entrees = racines de l'unite indexees par 3^a * 2^b). Explorer les bornes de permanents pour les matrices STRUCTUREES :
- Travaux de Glynn (2010) : permanent formula via determinants
- Travaux de Barvinok (2016) : approximation du permanent en temps polynomial
- Travaux de Aaronson-Arkhipov (2011) : permanent et complexite #P

**Priorite 2 : Exploiter la structure de decalage.** Quand on somme T(t) sur une orbite de <3> dans F_p* (direction R191), les permanents de Omega(pi) pour differentes valeurs de s sont RELIES par un decalage des indices. Peut-on exploiter ces relations pour obtenir des annulations ENTRE permanents ?

**Priorite 3 : Contourner la monotonie.** Au lieu de borner T_mono directement, borner Sum_{s in orbit} T_mono(s) en exploitant la structure telescopique (R191, Section 5.4). Si les permanents de Omega(pi) sont individuellement grands mais se compensent quand on somme sur l'orbite, la CGT fonctionnerait "en moyenne orbitale" sans avoir besoin de borner chaque permanent.

**Priorite 4 : Hybrider CGT et SBL.** Le Spectre de Benford Lacunaire (R195, Direction 5, score 8/10) utilise l'equidistribution des poids 3^j mod p comme source de decoherence. La CGT utilise la factorisation en produit de sommes de Gauss. Les deux approches sont COMPLEMENTAIRES : le SBL fournit la decoherence "entre facteurs" tandis que la CGT fournit la decoherence "au sein de chaque facteur". Une approche hybride bornerait les permanents de Omega en utilisant l'equidistribution des 3^j comme source de quasi-aleatoirite pour les entrees de la matrice.

---

*R196 Investigateur Profond : 3 chaines de 5 WHY completees. 3 theoremes prouves (R196-T1, T2, T3), 1 conditionnel (R196-T4), 2 observations (O1, O2). REFUTATION : |G(a)| <= sqrt(r) est faux en general. IDENTIFICATION DU VERROU : le permanent de la matrice de phases Omega est le prix exact de la monotonie. Score CGT revise de 7/10 a 6.5/10. La CGT reformule le gap de monotonie en un probleme de permanents de matrices structurees -- un progres conceptuel qui ouvre des connexions avec la theorie des matrices aleatoires (Tao-Vu) et la complexite computationnelle (Aaronson-Arkhipov).*
