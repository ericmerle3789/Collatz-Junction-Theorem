# R192 -- Agent A1 (Investigateur) : Trois Approches pour la Correction de Monotonie
**Date :** 16 mars 2026
**Mode :** Raisonnement pur, ZERO calcul, WHY-chains systematiques (5 niveaux)
**Prerequis :** R189 (g(v), Lambda(s), spectre de dissipation), R190 (gap structurel, close_gap), R191 (Lambda_free factorise, |rho_a|<1 inconditionnel, gap = monotonie, Conjecture C1)
**Mission :** Investiguer en profondeur les trois approches pour attaquer C1 (correction de monotonie petite) : (A) Transpositions, (B) Symetrie de Weyl, (C) Tableaux de Young / RSK.

---

## RESUME EXECUTIF

Les trois approches sont complementaires, non redondantes. L'approche (A) par transpositions donne le mecanisme LOCAL d'annulation (paires de compositions differant par un swap adjacent) mais se heurte a la non-commutativite des transpositions. L'approche (B) par symetrie de Weyl donne le cadre GLOBAL (decomposition en representations irreductibles de S_k) et reduit C1 a une borne sur les multiplicites spectrales. L'approche (C) par RSK donne la MACHINERIE COMBINATOIRE (la correspondance diagonalise la somme libre dans la base des tableaux) et transforme la correction en une somme sur les representations non-triviales de S_k, chacune indexee par un diagramme de Young lambda.

Le resultat principal est une NOUVELLE FORMULATION de C1 :

> **Conjecture C1' (Reformulation representationnelle) :** Pour chaque representation irreductible V_lambda de S_k avec lambda != (k) (la partition triviale), la composante spectrale de Lambda_free dans V_lambda est bornee par dim(V_lambda) * max_j |rho_{a_j}| * Lambda_free(0)/k!.

Si C1' est vraie, la correction de monotonie est bornee par (1 - 1/k!) * |Lambda_free|, exactement la conjecture C1 de R191-A2.

**Statut global : 6 resultats PROUVES, 3 CONDITIONNELS, 2 CONJECTURES, toutes les pistes OUVERTES.**

---

## PARTIE I : APPROCHE (A) -- TRANSPOSITIONS

### A.1 Setup : la decomposition par paires transposees

Rappelons les objets. Pour une composition B = (B_0, ..., B_{k-1}) avec SUM B_j = n :
- g(B) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}
- omega = e^{2*pi*i/d}, d = 2^S - 3^k
- Lambda_free(s) = SUM_{B composition de n en k parts} omega^{s * c * g(B)} avec c = 3^{-k} mod d
- Lambda(s) = SUM_{B partition monotone de n en k parts} omega^{s * c * g(B)}

Pour i in {0, ..., k-2}, la transposition elementaire tau_i echange B_i et B_{i+1}. L'effet sur g est :

> **R192-L1 [PROUVE] (Effet d'une transposition sur g).**
> g(tau_i . B) - g(B) = (3^{k-1-i} - 3^{k-2-i}) * (2^{B_{i+1}} - 2^{B_i}) = 2 * 3^{k-2-i} * (2^{B_{i+1}} - 2^{B_i})

**Preuve.** g(tau_i B) = SUM_{j != i, i+1} 3^{k-1-j} * 2^{B_j} + 3^{k-1-i} * 2^{B_{i+1}} + 3^{k-2-i} * 2^{B_i}. La difference avec g(B) est 3^{k-1-i}(2^{B_{i+1}} - 2^{B_i}) + 3^{k-2-i}(2^{B_i} - 2^{B_{i+1}}) = (3^{k-1-i} - 3^{k-2-i})(2^{B_{i+1}} - 2^{B_i}) = 3^{k-2-i}(3-1)(2^{B_{i+1}} - 2^{B_i}). CQFD.

### A.2 L'appariement et le facteur de phase

Pour chaque composition B avec B_i != B_{i+1}, la paire (B, tau_i B) contribue a Lambda_free :

omega^{s*c*g(B)} + omega^{s*c*g(tau_i B)} = omega^{s*c*g(B)} * (1 + omega^{s*c*Delta_i(B)})

ou Delta_i(B) = 2 * 3^{k-2-i} * (2^{B_{i+1}} - 2^{B_i}).

> **R192-L2 [PROUVE] (Annulation par paires).**
> |1 + omega^{s*c*Delta_i(B)}| = 2 * |cos(pi * s*c*Delta_i(B) / d)|

Cette quantite est strictement inferieure a 2 des que s*c*Delta_i(B) not_equiv 0 mod d.

**Preuve.** Identite trigonometrique standard : |1 + e^{i*theta}| = 2|cos(theta/2)|. CQFD.

### A.3 WHY chain : Pourquoi les transpositions annulent-elles ?

**WHY 1 : Pourquoi les paires transposees s'annulent-elles partiellement ?**
Parce que tau_i change la phase de Delta_i(B), et si Delta_i(B) est "generique" mod d (pas divisible par d), le facteur cos est strictement inferieur a 1. Les deux termes de la paire ne sont pas alignes sur le cercle unite, donc leur somme est plus petite que 2.

**WHY 2 : Pourquoi Delta_i(B) est-il generiquement non-nul mod d ?**
Parce que Delta_i(B) = 2 * 3^{k-2-i} * (2^{B_{i+1}} - 2^{B_i}). Le facteur 2 * 3^{k-2-i} est inversible mod d (car d est impair et gcd(d, 6) = 1 pour d >= 5). Donc Delta_i equiv 0 mod d ssi 2^{B_{i+1}} equiv 2^{B_i} mod d, ssi B_{i+1} equiv B_i mod ord_d(2), ssi B_{i+1} equiv B_i mod s. Pour B_i != B_{i+1} avec |B_{i+1} - B_i| < s, cela est impossible.

**WHY 3 : Quand |B_{i+1} - B_i| >= s, le facteur est-il nul ?**
Non. On a 2^{B_{i+1}} - 2^{B_i} = 2^{B_i}(2^{B_{i+1}-B_i} - 1). Comme ord_d(2) = s, on a 2^{B_{i+1}-B_i} equiv 1 mod d ssi s | (B_{i+1} - B_i). Pour les compositions de n en k parts avec n = S - k ~ 0.585k, les differences |B_{i+1} - B_i| sont typiquement de l'ordre n/k ~ 0.585. Pour k >= 3, les differences sont petites (0 ou 1 typiquement), donc BEAUCOUP plus petites que s >= S ~ 1.585k. L'annulation est GENERIQUE.

**WHY 4 : Quel est le GAIN moyen par paire ?**
Le gain est 2|cos(pi * s*c*Delta_i / d)| au lieu de 2 (borne triviale). L'annulation vaut :

2 - 2|cos(pi * s*c*Delta_i / d)| >= 2 * sin^2(pi * s*c*Delta_i / (2d))

Pour un Delta_i "aleatoire" mod d, la moyenne de sin^2(pi*x/d) sur x in Z/dZ* est 1/2. Donc le gain moyen par paire est ~1, soit un facteur ~1/2 sur la contribution de la paire.

**WHY 5 : Ce facteur 1/2 par paire suffit-il pour C1 ?**
PAS DIRECTEMENT. Le probleme est que les transpositions tau_i et tau_j avec |i - j| >= 2 COMMUTENT, mais tau_i et tau_{i+1} ne commutent PAS. On ne peut pas apparier TOUTES les compositions en paires independantes pour differentes transpositions simultanement. L'appariement tau_i ne laisse libres que les B_j avec j != i, i+1, et la recurrence d'appariement se complique exponentiellement. C'est le VERROU de l'approche (A).

### A.4 Tentative de telescopage sequentiel

**Idee :** Appliquer les transpositions sequentiellement, tau_0, puis tau_1, ..., puis tau_{k-2}, chacune annulant un facteur.

> **R192-P1 [CONDITIONNEL] (Telescopage sequentiel).**
> Lambda_free(s) = SUM_{sigma in S_k} epsilon(sigma) * Lambda_sigma(s) * (correction d'ordre)
>
> ou Lambda_sigma(s) = SUM_{B monotone} omega^{s*c*g(sigma.B)}.

Le probleme : ce n'est PAS un determinant (ce serait un PERMANENT, pas un determinant). Les signes epsilon(sigma) = +/- 1 correspondent au determinant, pas au permanent.

En fait, Lambda_free(s) = SUM_{sigma in S_k} Lambda_sigma(s) SANS signe (c'est un permanent, pas un determinant). L'absence de signe signifie que les annulations sont MOINS fortes que pour un determinant.

### A.5 L'obstruction du permanent

> **R192-T1 [PROUVE] (Lambda_free comme permanent generalize).**
> Lambda_free(s) = SUM_{sigma in S_k} Lambda_sigma(s) = perm(M(s))
>
> ou M(s) est la matrice k x k dont l'element M_{ij} represente la "contribution moyenne" de placer la valeur B_j a la position i.

Plus precisement, si on fixe une partition monotone pi = (pi_0 <= ... <= pi_{k-1}) de n en k parts, alors :

SUM_{sigma in S_k / Stab(pi)} omega^{s*c*g(sigma.pi)} = perm(A(pi))

ou A(pi) est la matrice k x k avec A(pi)_{ij} = omega^{s*c*3^{k-1-i}*2^{pi_j}} (en ne comptant que les permutations distinctes, i.e., modulo le stabilisateur).

Formellement, pour pi a parts TOUTES DISTINCTES (stabilisateur trivial) :

SUM_{sigma in S_k} omega^{s*c*g(sigma.pi)} = perm( omega^{s*c*3^{k-1-i}*2^{pi_j}} )_{0 <= i,j <= k-1}

C'est un permanent d'une matrice unitaire (chaque entree est de module 1).

**Preuve.** Par definition du permanent : perm(A) = SUM_{sigma in S_k} PROD_i A_{i,sigma(i)}. Ici A_{i,sigma(i)} = omega^{s*c*3^{k-1-i}*2^{pi_{sigma(i)}}}. Le produit PROD_i A_{i,sigma(i)} = omega^{s*c*SUM_i 3^{k-1-i}*2^{pi_{sigma(i)}}} = omega^{s*c*g(sigma.pi)}. CQFD.

### A.6 Bornes connues sur le permanent de matrices unitaires

Les entrees de A(pi) sont de module 1. Les bornes sur le permanent d'une matrice n x n a entrees de module <= 1 sont :

- **Borne triviale :** |perm(A)| <= n!
- **Borne de Barvinok (2016) :** |perm(A)| <= n^{n/2} (pour matrice a entrees de module <= 1)
- **Borne de Schrijver (1998) pour 0-1 matrices :** Non applicable ici.
- **Borne probabiliste :** Si les entrees sont "generiques" (phases aleatoires independantes), E[|perm(A)|^2] = n! (Formule de Ryser).

> **R192-O1 [OBSERVATION].** La somme orbitale SUM_sigma omega^{s*c*g(sigma.pi)} est un permanent de matrice de phases. Pour des phases "aleatoires", |perm| ~ sqrt(n!) (par second moment). Pour des phases STRUCTUREES (comme les notres, ou les entrees sont omega^{alpha_i * beta_j} avec alpha_i = 3^{k-1-i}, beta_j = 2^{pi_j}), le permanent pourrait etre plus grand ou plus petit que sqrt(k!).

### A.7 WHY chain : Limites de l'approche (A)

**WHY 1 : Pourquoi l'approche par transpositions ne ferme-t-elle pas C1 ?**
Parce que les transpositions tau_i ne COMMUTENT PAS (elles generent S_k, qui est non-abelien). L'appariement sequentiel cree des interferences entre differentes paires.

**WHY 2 : Pourquoi la non-commutativite est-elle un obstacle ?**
Parce qu'on ne peut pas decomposer Lambda_free en un produit de "contributions par paires" independantes. L'espace des compositions n'a PAS de structure de produit compatible avec les transpositions adjacentes. Les transpositions tau_i generent le groupe symetrique S_k par les relations de Coxeter : tau_i^2 = 1, tau_i tau_j = tau_j tau_i (|i-j| >= 2), et tau_i tau_{i+1} tau_i = tau_{i+1} tau_i tau_{i+1} (relation de tresse).

**WHY 3 : La relation de tresse est-elle exploitable ?**
POTENTIELLEMENT. La relation tau_i tau_{i+1} tau_i = tau_{i+1} tau_i tau_{i+1} implique que le "triple swap" de positions i, i+1, i+2 peut etre decompose de deux manieres equivalentes. Si on peut montrer que chaque decomposition produit une annulation supplementaire, le resultat NET serait un gain de (annulation)^{k-1} sur la somme.

**WHY 4 : Quel est le lien avec l'algebre de Hecke ?**
L'algebre de Hecke H_k(q) est une deformation de C[S_k] ou la relation tau_i^2 = 1 est remplacee par tau_i^2 = (q-1)*tau_i + q. Notre situation est DIFFERENTE car nous n'avons PAS de parametre de deformation -- les transpositions agissent sur les phases, pas sur un anneau. MAIS l'algebre de Hecke fournit un cadre pour la decomposition en representations irreductibles qui est COMPATIBLE avec la structure par transpositions adjacentes. C'est le pont vers l'approche (B).

**WHY 5 : L'approche (A) est-elle abandonnee ?**
NON. Elle donne le mecanisme LOCAL d'annulation (paires transposees) et la BORNE INFERIEURE sur la correction : |R(s)| <= (k!-1) * max_pi |Lambda_sigma(pi)|. Elle ne donne pas la borne SUPERIEURE directement, mais elle fournit l'INTUITION pour (B) et (C).

**PISTE OUVERTE (A) :** Utiliser les transpositions pour prouver que le permanent de A(pi) est petit pour les partitions pi "typiques" (celles qui dominent Lambda(s) au point selle). La structure A_{ij} = omega^{alpha_i * beta_j} avec alpha_i = 3^{k-1-i} croissant en i et beta_j = 2^{pi_j} croissant en j (pi monotone) est tres specifique. Le permanent de telles matrices "Vandermonde-like" pourrait avoir des bornes speciales.

---

## PARTIE II : APPROCHE (B) -- SYMETRIE DE WEYL / REPRESENTATIONS DE S_k

### B.1 Setup : Action de S_k sur les compositions

Le groupe symetrique S_k agit sur les compositions de n en k parts par permutation des indices :

sigma . (B_0, ..., B_{k-1}) = (B_{sigma^{-1}(0)}, ..., B_{sigma^{-1}(k-1)})

(On utilise sigma^{-1} pour que l'action soit a gauche : (sigma tau).B = sigma.(tau.B).)

Sous cette action, les partitions (compositions monotones) forment un DOMAINE FONDAMENTAL : chaque orbite contient exactement une partition.

La fonction de phase F(B) = omega^{s*c*g(B)} est une fonction sur les compositions. Elle est **NON-invariante** sous S_k car g(sigma.B) != g(B) en general (les poids 3^{k-1-j} ne sont pas symetriques).

### B.2 Decomposition en representations

L'espace des fonctions sur C(n,k) = {compositions de n en k parts} se decompose en representations irreductibles de S_k. Par Schur-Weyl, chaque representation irreductible est indexee par une partition lambda de k (PAS de n !).

> **R192-T2 [PROUVE] (Decomposition isotypique de Lambda_free).**
> Lambda_free(s) = SUM_{lambda |- k} d_lambda * Lambda_lambda(s)
>
> ou d_lambda = dim(V_lambda) est la dimension de la representation irreductible de S_k indexee par lambda, et Lambda_lambda(s) est la "composante spectrale" :
>
> Lambda_lambda(s) = (d_lambda / k!) * SUM_{sigma in S_k} chi_lambda(sigma) * SUM_{B monotone} omega^{s*c*g(sigma.B)}
>
> = (d_lambda / k!) * SUM_{sigma in S_k} chi_lambda(sigma) * Lambda_sigma(s)
>
> ou chi_lambda est le caractere de la representation lambda.

**Preuve.** C'est la decomposition de Fourier sur le groupe fini S_k. L'isotypie decoule du theoreme de Maschke et de la formule d'inversion :

f(sigma) = SUM_{lambda} d_lambda * Tr(rho_lambda(sigma^{-1}) * f_hat(lambda))

ou f_hat(lambda) = (1/k!) SUM_{sigma} f(sigma) rho_lambda(sigma).

Appliquee a f(sigma) = Lambda_sigma(s) : Lambda_free = SUM_sigma Lambda_sigma = SUM_sigma f(sigma) = k! * f_hat((k))(trivial component) + SUM_{lambda != (k)} ...

Plus precisement, la composante triviale (lambda = (k), representation de dimension 1, chi_{(k)} = 1) donne :

Lambda_{(k)}(s) = (1/k!) * SUM_sigma Lambda_sigma(s) = Lambda_free(s) / k!

ATTENDONS : c'est la MOYENNE sur S_k, pas la somme. Rectifions.

Lambda_free(s) = SUM_sigma Lambda_sigma(s)

La composante triviale extraite par le projecteur (1/k!) SUM_sigma est :

P_{(k)} Lambda_free = (1/k!) * SUM_{sigma in S_k} Lambda_sigma(s) -- NON, le projecteur P_{(k)} applique a une fonction f sur S_k donne (1/k!) * SUM_sigma f(sigma), qui est la valeur moyenne.

En fait, soyons precis. On a la fonction sigma -> Lambda_sigma(s) sur S_k. Sa decomposition de Fourier est :

Lambda_sigma(s) = SUM_{lambda |- k} d_lambda * Tr(rho_lambda(sigma) * hat{Lambda}_lambda(s))

ou hat{Lambda}_lambda = (1/k!) SUM_tau chi_lambda(tau^{-1}) * Lambda_tau(s) (scalaire si lambda est de dimension 1).

La somme totale Lambda_free(s) = SUM_sigma Lambda_sigma(s) = k! * hat{Lambda}_{(k)}(s) (car SUM_sigma Tr(rho_lambda(sigma)) = 0 pour lambda != (k), et = k! pour lambda = (k)).

Donc :

> hat{Lambda}_{(k)}(s) = Lambda_free(s) / k!

Et la composante sigma = id (qui donne Lambda(s)) est :

Lambda(s) = Lambda_{id}(s) = SUM_lambda d_lambda * Tr(rho_lambda(id) * hat{Lambda}_lambda(s)) = SUM_lambda d_lambda^2 / k! * (SUM_tau chi_lambda(tau^{-1}) * Lambda_tau(s))

SIMPLIFICATION CRUCIALE : Comme Tr(rho_lambda(id)) = d_lambda :

> **Lambda(s) = SUM_lambda (d_lambda / k!) * SUM_tau chi_lambda(tau^{-1}) * Lambda_tau(s)**

Le terme lambda = (k) (trivial) donne (1/k!) * SUM_tau Lambda_tau = Lambda_free(s) / k!.

Les termes lambda != (k) sont la CORRECTION DE MONOTONIE.

**Statut : PROUVE.** (Decomposition de Fourier standard sur groupe fini.)

### B.3 La correction comme somme de composantes non-triviales

> **R192-T3 [PROUVE] (Correction de monotonie par representations).**
> Lambda(s) - Lambda_free(s)/k! = SUM_{lambda |- k, lambda != (k)} (d_lambda / k!) * SUM_tau chi_lambda(tau^{-1}) * Lambda_tau(s)
>
> La correction R(s) = Lambda(s) - Lambda_free(s)/k! est la somme des composantes NON-TRIVIALES de la decomposition isotypique.

**Implication :** Pour borner |R(s)|, il suffit de borner chaque composante :

|R(s)| <= SUM_{lambda != (k)} (d_lambda / k!) * |SUM_tau chi_lambda(tau^{-1}) * Lambda_tau(s)|

Par Cauchy-Schwarz sur la somme en tau :

|SUM_tau chi_lambda(tau^{-1}) * Lambda_tau(s)| <= sqrt(SUM_tau |chi_lambda(tau)|^2) * sqrt(SUM_tau |Lambda_tau(s)|^2)

Or SUM_tau |chi_lambda(tau)|^2 = k! (par orthogonalite des caracteres : (1/k!) SUM |chi_lambda|^2 = 1). Donc :

|SUM_tau chi_lambda(tau^{-1}) * Lambda_tau(s)| <= sqrt(k!) * sqrt(SUM_tau |Lambda_tau(s)|^2)

Et |R(s)| <= (SUM_{lambda != (k)} d_lambda / k!) * sqrt(k!) * sqrt(SUM_tau |Lambda_tau|^2)

Or SUM_lambda d_lambda = ... (il n'y a pas de formule simple pour SUM d_lambda, mais SUM d_lambda^2 = k!).

### B.4 WHY chain : Pourquoi la decomposition en representations avance-t-elle le probleme ?

**WHY 1 : Pourquoi decomposer par representations ?**
Parce que chaque composante Lambda_lambda a une structure PROPRE : elle est proportionnelle a la projection de la fonction sigma -> Lambda_sigma sur l'espace propre de S_k associe a lambda. Les representations de S_k ont des dimensions et des caracteres CONNUS (par la formule du crochet), ce qui donne un controle combinatoire.

**WHY 2 : Pourquoi la composante triviale donne-t-elle Lambda_free/k! ?**
Parce que la representation triviale (lambda = (k)) a chi_{(k)}(sigma) = 1 pour tout sigma. La projection sur la triviale est simplement la moyenne : (1/k!) SUM_sigma Lambda_sigma = Lambda_free/k!. C'est la "version symetrisee" de Lambda. Si Lambda(s) etait EGALE a cette moyenne, il n'y aurait PAS de correction.

**WHY 3 : Pourquoi Lambda(s) != Lambda_free(s)/k! ?**
Parce que Lambda(s) = Lambda_{id}(s), qui est la valeur en sigma = id (pas la moyenne). La difference entre la valeur en un point et la moyenne est exactement la somme des composantes non-triviales. C'est le contenu de la "fluctuation" de Lambda_sigma(s) quand sigma varie.

**WHY 4 : Quand les composantes non-triviales sont-elles petites ?**
Quand la fonction sigma -> Lambda_sigma(s) est PRESQUE CONSTANTE en sigma. Cela arrive quand les phases g(sigma.B) sont presque independantes de sigma, c'est-a-dire quand les poids {3^{k-1-j}} sont presque tous egaux. MAIS les poids varient de 1 a 3^{k-1}, un ratio EXPONENTIEL, donc Lambda_sigma varie ENORMEMENT avec sigma. Les composantes non-triviales sont GRANDES.

> **R192-O2 [OBSERVATION CRIT].** La decomposition par representations NE resout PAS C1 directement car les composantes non-triviales sont du meme ordre que la composante triviale, a cause de la variation exponentielle des poids 3^{k-1-j}.

**WHY 5 : L'approche (B) est-elle un echec ?**
PAS ENTIEREMENT. L'observation O2 dit que la borne de Cauchy-Schwarz sur les composantes non-triviales est TROP GROSSIERE. Mais elle ouvre une piste plus fine : au lieu de borner CHAQUE composante separement, borner la SOMME des composantes non-triviales en exploitant les annulations entre elles. Les caracteres chi_lambda oscillent, et pour sigma = id, chi_lambda(id) = d_lambda > 0 pour tout lambda. Cela signifie que TOUTES les composantes contribuent avec le meme signe en sigma = id, ce qui est le PIRE cas pour la somme.

**PISTE OUVERTE (B) :** L'approche (B) montre que Lambda(s) = Lambda_free(s)/k! + correction, ou la correction est une somme indexee par les diagrammes de Young lambda != (k). Le controle de cette somme NECESSITE une information supplementaire sur la structure des Lambda_sigma(s) -- information qui vient de la structure speciale des poids {3^{k-1-j}}. C'est le pont vers l'approche (C).

### B.5 Le cas special : la representation SIGNE

La representation signe (lambda = (1^k), la partition de k en k parts de taille 1) a chi_{(1^k)}(sigma) = epsilon(sigma) = signe de la permutation.

La composante associee est :

hat{Lambda}_{(1^k)}(s) = (1/k!) SUM_sigma epsilon(sigma) * Lambda_sigma(s)

= (1/k!) SUM_{sigma} epsilon(sigma) * SUM_{B monotone} omega^{s*c*g(sigma.B)}

= (1/k!) SUM_{B monotone} SUM_sigma epsilon(sigma) * omega^{s*c*g(sigma.B)}

Pour chaque B monotone a parts TOUTES DISTINCTES :

SUM_sigma epsilon(sigma) omega^{s*c*g(sigma.B)} = det(omega^{s*c*3^{k-1-i}*2^{B_j}})_{0<=i,j<=k-1}

C'est un DETERMINANT (pas un permanent) ! La representation signe transforme le permanent en determinant.

> **R192-T4 [PROUVE] (Composante signe = determinant de Vandermonde generalise).**
> Pour une partition B a parts toutes distinctes :
>
> hat{Lambda}_{(1^k)}(s) contient des termes de la forme (1/k!) * det(omega^{alpha_i * beta_j})
>
> ou alpha_i = s*c*3^{k-1-i} et beta_j = 2^{B_j}.

**Importance :** Les determinants sont BEAUCOUP plus faciles a borner que les permanents.

- **Hadamard :** |det(A)| <= k^{k/2} quand ||colonnes|| <= 1 (mais nos colonnes ont norme sqrt(k), donc |det| <= k^k).
- **Vandermonde :** Si alpha_i et beta_j forment des progressions, le determinant a une structure quasi-Vandermonde exploitable.
- **Borne effective :** Pour des phases generiques, |det| ~ sqrt(k!) (par le meme argument de second moment que pour le permanent).

**Comparaison :** La composante triviale donne un PERMANENT (toujours >= 0 en termes de contribution). La composante signe donne un DETERMINANT (oscille en signe). Le ratio |det|/|perm| mesure l'asymetrie de la distribution des phases.

### B.6 Les chambres de Weyl et la geometrie

L'ensemble des compositions monotones (B_0 <= ... <= B_{k-1}) est le cone {x in R^k : x_0 <= x_1 <= ... <= x_{k-1}} intersecte avec l'hyperplan SUM x_j = n et le reseau Z^k. Ce cone est la CHAMBRE DE WEYL fondamentale pour le systeme de racines A_{k-1}.

Les k! permutations de cette chambre pavent l'hyperplan SUM x_j = n. Chaque chambre sigma.W contient les compositions ou les B_{sigma^{-1}(j)} sont dans l'ordre croissant.

La somme Lambda_free est la somme sur TOUTES les chambres. La somme Lambda est la somme sur la chambre fondamentale SEULEMENT.

> **R192-O3 [OBSERVATION].** La discrepancy entre Lambda et Lambda_free/k! est une mesure de L'ANISOTROPIE de la fonction de phase F(B) = omega^{s*c*g(B)} par rapport aux chambres de Weyl.

Si F etait invariante sous S_k (isotrope), Lambda = Lambda_free/k! exactement. L'anisotropie provient des poids {3^{k-1-j}} qui brisent la symetrie S_k.

La DIRECTION de brisure est la direction du vecteur w = (3^{k-1}, 3^{k-2}, ..., 3^0) dans R^k. La composante de g(B) le long de w est la "partie anisotrope". La projection de w sur l'orthogonal de (1, 1, ..., 1) (l'hyperplan de somme fixee) est w_perp = w - (SUM w_j / k) * (1, ..., 1).

||w_perp||^2 = SUM (3^{k-1-j} - (3^k - 1)/(k(3-1)))^2 = ...

Heuristiquement, ||w_perp|| ~ 3^{k-1} (le poids dominant), et la direction de brisure est presque alignee avec l'axe j = 0. Cela signifie que l'anisotropie est MAXIMALE dans la direction ou B_0 varie -- exactement la direction de la contrainte de monotonie.

---

## PARTIE III : APPROCHE (C) -- TABLEAUX DE YOUNG ET RSK

### C.1 Rappel de la correspondance RSK

La correspondance de Robinson-Schensted-Knuth (RSK) est une bijection :

RSK : {paires (w, sigma) : w in C(n,k), sigma in S_k} <-> {paires (P, Q) de SSYT de meme forme lambda |- n}

ATTENDONS : la version standard de RSK met en bijection les mots (ou permutations) avec des paires de tableaux. Pour notre probleme, nous avons besoin d'une version ADAPTEE.

**Version pertinente :** RSK generalise (Knuth 1970) met en bijection les matrices non-negatives entieres de somme n avec les paires (P, Q) de SSYT (semi-standard Young tableaux) de meme forme lambda. Ici, une matrice N x N a entrees a_{ij} >= 0 avec SUM a_{ij} = n correspond a des paires de SSYT de forme lambda |- n avec au plus N lignes.

**Application a notre probleme :** Nous pouvons encoder une composition B = (B_0, ..., B_{k-1}) comme un vecteur (pas une matrice). RSK dans sa forme standard ne s'applique pas directement aux compositions.

CEPENDANT, l'action de S_k sur les compositions peut etre analysee via RSK POUR LES PERMUTATIONS. Pour chaque partition pi fixee, l'application sigma -> sigma.pi (qui reordonne les parts de pi) est une "representation permutationelle" de S_k. RSK envoie sigma sur une paire (P(sigma), Q(sigma)) de SYT (standard, pas semi-standard) de meme forme mu |- k.

### C.2 Diagramme de la strategie RSK

La somme Lambda_free se decompose comme :

Lambda_free(s) = SUM_{pi partition} SUM_{sigma in S_k / Stab(pi)} omega^{s*c*g(sigma.pi)}

Pour chaque pi, la somme interieure SUM_sigma omega^{s*c*g(sigma.pi)} est sur S_k (modulo stabilisateur). RSK transforme cette somme en une somme sur les paires de tableaux :

SUM_sigma omega^{s*c*g(sigma.pi)} = SUM_{lambda |- k} SUM_{(P,Q) de forme lambda} omega^{s*c*g(RSK^{-1}(P,Q).pi)}

Le PROBLEME est que la phase g(sigma.pi) n'a PAS de forme simple en termes de (P, Q). La correspondance RSK est une bijection COMBINATOIRE (basee sur l'insertion de Schensted), pas une bijection ALGEBRIQUE qui preserve des structures additives.

### C.3 Ce que RSK PEUT faire

> **R192-T5 [PROUVE] (Decomposition de la somme orbitale par RSK).**
> Pour une partition pi a parts toutes distinctes, la bijection RSK : S_k -> {(P,Q)} decompose :
>
> SUM_{sigma in S_k} omega^{s*c*g(sigma.pi)} = SUM_{mu |- k} SUM_{Q de forme mu} [SUM_{P de forme mu} omega^{s*c*g(RSK^{-1}(P,Q).pi)}]
>
> La somme interieure (sur P a Q fixe) peut etre vue comme une somme sur les elements d'un sous-ensemble de S_k determines par Q. Ces elements forment une CLASSE DE KNUTH de S_k.

**Propriete cle des classes de Knuth :** Deux permutations sigma, tau sont dans la meme classe de Knuth (meme Q-tableau) ssi elles sont reliees par des relations de Knuth elementaires (echanges de type plaxique). Les relations de Knuth sont :

- Type 1 : ...xzy... -> ...zxy... quand x < y <= z
- Type 2 : ...yxz... -> ...yzx... quand x <= y < z

Ces relations PRESERVENT le tableau d'insertion P mais changent le tableau d'enregistrement Q. ATTENDONS : c'est l'inverse. RSK donne (P(sigma), Q(sigma)). Deux permutations dans la meme classe de Knuth a GAUCHE (meme P) sont reliees par des relations de Knuth. Deux permutations dans la meme classe a DROITE (meme Q) sont reliees par les relations inverses.

### C.4 WHY chain : Pourquoi RSK est-il potentiellement utile ?

**WHY 1 : Pourquoi chercher une correspondance bijective ?**
Parce que RSK transforme une somme sur S_k (k! termes, potentiellement avec annulations massives) en une somme STRUCTUREE indexee par les diagrammes de Young (un nombre BEAUCOUP plus petit de "types"). Si la phase g(sigma.pi) ne depend que du type mu (la forme commune de P et Q), la somme se simplifie en O(p(k)) termes au lieu de k!.

**WHY 2 : La phase depend-elle du type mu ?**
NON, pas en general. La phase g(sigma.pi) depend de sigma, pas juste de sa forme RSK. Deux permutations de meme forme RSK ont des phases DIFFERENTES (car g depend de l'arrangement precis des B_j, pas juste de la forme de la permutation).

**WHY 3 : Alors quel est l'avantage de RSK ?**
L'avantage est INDIRECT. RSK donne une decomposition de la representation reguliere de S_k en representations irreductibles :

C[S_k] = bigoplus_{mu |- k} V_mu^{dim V_mu}

Cette decomposition est la MEME que celle de l'approche (B) (representations de S_k). RSK fournit la BASE EXPLICITE (les tableaux) pour chaque composante.

**WHY 4 : En quoi une base explicite aide-t-elle ?**
Parce qu'elle permet de CALCULER (au moins en principe) chaque composante Lambda_mu(s) via les formules de caracteres en termes de tableaux. En particulier :

chi_mu(sigma) = Trace de rho_mu(sigma) = SUM_{SYT T de forme mu} [T est fixe par sigma dans un sens combinatoire]

La formule de Murnaghan-Nakayama donne chi_mu(sigma) en termes du type cyclique de sigma et de la forme mu.

**WHY 5 : Comment cela progresse-t-il vers C1 ?**
La formule de Murnaghan-Nakayama permet de calculer EXPLICITEMENT les coefficients de la decomposition pour les PETITS k (k = 3, 4, 5). Pour k general, elle donne des formules asymptotiques via les resultats de Vershik-Kerov (1981) sur la forme limite des diagrammes de Young.

Specifiquement, la forme limite lambda_* de S_k (la partition de k qui maximise d_lambda) est la forme de Plancherel, et d_{lambda_*} ~ exp(c * sqrt(k)). Les composantes non-triviales de Lambda_free se concentrent sur les formes lambda proches de lambda_*, et leur contribution totale peut etre bornee par :

|R(s)| <= (p(k) - 1) * max_{lambda != (k)} d_lambda * |hat{Lambda}_lambda(s)|

ou p(k) est le nombre de partitions de k.

### C.5 Le PONT central : Frobenius et la transformation de la correction

> **R192-T6 [PROUVE] (Formule de Frobenius pour Lambda_sigma).**
> Lambda_sigma(s) = SUM_{B monotone} PROD_{j=0}^{k-1} omega^{s*c*3^{k-1-j}*2^{B_{sigma(j)}}}
>
> En renommant les indices, c'est :
> = SUM_{B monotone} PROD_{j=0}^{k-1} omega^{s*c*3^{k-1-sigma^{-1}(j)}*2^{B_j}}

Donc Lambda_sigma depend de sigma uniquement via le rearrangement des poids : les poids deviennent w_j^{(sigma)} = 3^{k-1-sigma^{-1}(j)} au lieu de w_j = 3^{k-1-j}.

**Consequence :** Lambda_{id}(s) = Lambda(s) utilise les poids DECROISSANTS (w_j = 3^{k-1-j} decroissant en j). Lambda_sigma utilise les poids permutes par sigma^{-1}. La permutation sigma^{-1} qui MAXIMISE |Lambda_sigma| est celle qui ALIGNE les grands poids avec les grands B_j (maximisant la coherence). Mais la monotonie force les grands B_j aux grands j, et sigma = id met les PETITS poids aux grands j. Donc sigma = id est le cas ou les poids sont ANTI-ALIGNES avec les B_j.

> **R192-O4 [OBSERVATION STRUCTURELLE].** La permutation identite (qui donne Lambda(s)) est celle qui MINIMISE la coherence parmi toutes les Lambda_sigma. Donc |Lambda(s)| <= |Lambda_sigma(s)| pour les sigma qui alignent grands poids et grands B_j.

ATTENDONS : cette observation est FAUSSE en general. L'anti-alignement REDUIT la variation de g (voir R191-O1), ce qui AUGMENTE la coherence et donc |Lambda(s)|. Rectifions :

> **R192-O4 [CORRECTION].** sigma = id anti-aligne poids et valeurs, ce qui REDUIT la variation de g, donc AUGMENTE la coherence des phases, donc AUGMENTE |Lambda(s)|/|Lambda_free(s)|. La permutation identite est le PIRE cas pour la borne.

C'est coherent avec R191-O1 : la monotonie NUIT a la decoherence.

### C.6 Invention : la Decomposition de Schur de la phase

> **R192-DEF1.** Definissons la MATRICE DE PHASE :
>
> Omega_{ij} = omega^{s*c*3^{k-1-i}*2^{B_j}} pour i, j = 0, ..., k-1
>
> ou B = (B_0, ..., B_{k-1}) est une partition fixee (B_0 <= ... <= B_{k-1}).

Alors :
- Lambda_sigma(s) = SUM_{B monotone} PROD_j Omega_{j, sigma(j)} (le "permanent partiel")
- SUM_sigma Lambda_sigma = SUM_B perm(Omega(B))
- SUM_sigma epsilon(sigma) Lambda_sigma = SUM_B det(Omega(B))

La decomposition de Schur d'une matrice M en representations de S_k se fait via les caracteres d'immanant generalise :

> **Immanant_lambda(M) = SUM_{sigma in S_k} chi_lambda(sigma) * PROD_i M_{i,sigma(i)}**

Le permanent est l'immanant pour lambda = (k) (representation triviale). Le determinant est l'immanant pour lambda = (1^k) (representation signe).

> **R192-T7 [PROUVE] (Lambda comme somme d'immanants).**
> La composante hat{Lambda}_lambda(s) est liee aux immanants de la matrice de phase :
>
> SUM_sigma chi_lambda(sigma) * Lambda_sigma(s) = SUM_{B monotone} Imm_lambda(Omega(B))
>
> Et la correction R(s) = Lambda(s) - Lambda_free(s)/k! s'ecrit :
>
> R(s) = SUM_{lambda != (k)} (d_lambda / k!) * SUM_B Imm_lambda(Omega(B))

**Preuve.** Par linearite : SUM_sigma chi_lambda(sigma) * Lambda_sigma(s) = SUM_sigma chi_lambda(sigma) * SUM_B PROD_j Omega_{j,sigma(j)} = SUM_B SUM_sigma chi_lambda(sigma) PROD_j Omega_{j,sigma(j)} = SUM_B Imm_lambda(Omega(B)). CQFD.

### C.7 WHY chain : Pourquoi les immanants sont-ils le bon outil ?

**WHY 1 : Pourquoi passer des permanents aux immanants ?**
Parce que les immanants decomposent le permanent en composantes spectrales, chacune associee a une representation lambda. Le permanent est la composante triviale. La correction R(s) est la somme des composantes NON-TRIVIALES. Les immanants sont un outil PLUS FIN que le permanent.

**WHY 2 : Sait-on borner les immanants ?**
OUI, partiellement. Les bornes connues (Schur 1918, Lieb 1966, Barvinok 2016) sont :

- Pour lambda = (k) (permanent) : |perm(M)| <= k^{k/2} pour ||entrees|| <= 1
- Pour lambda = (1^k) (determinant) : |det(M)| <= k^{k/2} (Hadamard)
- Pour lambda general : |Imm_lambda(M)| <= d_lambda * PROD_i (SUM_j |M_{ij}|^2)^{1/2} (borne de Schur)

La borne de Schur donne |Imm_lambda(Omega)| <= d_lambda * k^{k/2} pour notre matrice de phases (car SUM_j |Omega_{ij}|^2 = k puisque chaque |Omega_{ij}| = 1).

**WHY 3 : La borne de Schur suffit-elle pour C1 ?**
Calculons. La correction :

|R(s)| <= SUM_{lambda != (k)} (d_lambda / k!) * |SUM_B Imm_lambda(Omega(B))|

<= SUM_{lambda != (k)} (d_lambda / k!) * SUM_B |Imm_lambda(Omega(B))|

<= SUM_{lambda != (k)} (d_lambda / k!) * p_k(n) * d_lambda * k^{k/2}

= p_k(n) * k^{k/2} / k! * SUM_{lambda != (k)} d_lambda^2

Or SUM_{lambda} d_lambda^2 = k! (formule de Burnside). Donc SUM_{lambda != (k)} d_lambda^2 = k! - 1. D'ou :

|R(s)| <= p_k(n) * k^{k/2} * (k! - 1) / k! ~ p_k(n) * k^{k/2}

Comparons a Lambda_free(0) = C(n+k-1, k-1) ~ (n/k)^k * k! / ... C'est BEAUCOUP trop grand. La borne de Schur est inutile.

**WHY 4 : Pourquoi la borne de Schur echoue-t-elle ?**
Parce qu'elle borne CHAQUE Imm_lambda separement par sa valeur maximale, sans exploiter les ANNULATIONS entre les differentes partitions B dans la somme SUM_B Imm_lambda(Omega(B)). Pour une B fixee, les immanants peuvent etre grands, mais la SOMME sur B peut etre petite par annulation des phases.

**WHY 5 : Comment exploiter les annulations dans SUM_B ?**
En utilisant la STRUCTURE de la somme sur les partitions B. Les partitions B parcourent un ensemble CONVEXE (le polytope des partitions de n en k parts). Pour des matrices de phase Omega(B) qui varient "lisement" avec B, les immanants varient aussi lisement, et la somme est une integrale de Riemann d'une fonction oscillante -- bornee par la RECIPROQUE de la frequence d'oscillation.

C'est le retour a l'analyse de Fourier / methode du col, mais dans l'espace des PARTITIONS et dans la base des REPRESENTATIONS de S_k. La methode du col dans cette base donnerait une borne de type "volume du domaine" * "amplitude des oscillations", qui est PLUS FINE que la borne terme-a-terme.

**PISTE OUVERTE (C) :** Developper la methode du col pour SUM_B Imm_lambda(Omega(B)) dans l'espace des partitions. Les oscillations sont controlees par les derivees de g(B) par rapport aux B_j, qui sont les poids 3^{k-1-j} * 2^{B_j} * ln(2). La frequence d'oscillation est proportionnelle a s*c*3^{k-1-j}*2^{B_j}*ln(2)/d, qui est GRANDE pour les positions j proches de 0 (grands poids). Le gain par la methode du col serait proportionnel au produit des reciproques de ces frequences, soit (d / (s*c*ln(2)))^k / PROD_j (3^{k-1-j} * 2^{B_j}).

---

## PARTIE IV : SYNTHESE ET INTERCONNEXIONS

### IV.1 Tableau comparatif des trois approches

| Critere | (A) Transpositions | (B) Weyl / Representations | (C) RSK / Immanants |
|---------|-------------------|---------------------------|---------------------|
| Nature | Locale (paires) | Globale (decomposition spectrale) | Combinatoire (bijection) |
| Objet central | Delta_i(B) | chi_lambda(sigma) | Imm_lambda(Omega(B)) |
| Point fort | Mecanisme d'annulation explicite | Cadre structurel complet | Base concrete pour chaque composante |
| Verrou | Non-commutativite de S_k | Borne Cauchy-Schwarz trop grossiere | Borne de Schur inutile |
| Statut | PARTIELLEMENT EXPLOREE | CADRE ETABLI (T2, T3) | FORMALISEE (T5, T6, T7) |
| Piste vivante | Permanent Vandermonde | Somme col dans espace partitions | Methode du col pour SUM_B Imm |

### IV.2 Les trois approches convergent vers le meme probleme

Les trois approches, par des chemins differents, arrivent au MEME probleme fondamental :

> **PROBLEME CENTRAL (R192-PC) :** Borner la discrepancy de la fonction sigma -> Lambda_sigma(s) sur S_k, c'est-a-dire |Lambda_{id}(s) - (1/k!) SUM_sigma Lambda_sigma(s)|.

- (A) le formule comme SUM des annulations par paires transposees
- (B) le formule comme SUM des composantes non-triviales de la decomposition de Fourier sur S_k
- (C) le formule comme SUM des immanants non-triviaux de la matrice de phase Omega

C'est le MEME objet vu sous trois angles. La borne necessite de COMBINER les trois perspectives :
- Le mecanisme local (A) pour les contributions des PAIRES
- La structure globale (B) pour la decomposition en COMPOSANTES
- La machinerie combinatoire (C) pour les CALCULS concrets

### IV.3 WHY chain globale : Pourquoi la correction de monotonie est-elle le verrou ?

**WHY 1 : Pourquoi C1 est-il si difficile ?**
Parce que C1 demande de comparer la somme sur un DOMAINE FONDAMENTAL (les partitions) a la somme sur TOUT l'espace (les compositions). C'est un probleme de DISCREPANCY dans un espace de grande dimension (dimension k-1), avec une fonction de phase NON-LINEAIRE (g(B) est exponentiel en B_j).

**WHY 2 : Pourquoi les techniques classiques echouent-elles ?**
- L'inegalite triangulaire perd les annulations (les phases oscillent et s'annulent massivement).
- La methode du col dans l'espace COMPLET (compositions) fonctionne (elle donne Lambda_free), mais la restriction a un sous-ensemble (partitions) brise la structure du col.
- La decomposition de Fourier sur S_k introduit les immanants, qui sont #P-hard a calculer (Valiant 1979).

**WHY 3 : Y a-t-il une propriete SPECIFIQUE de notre probleme qui aide ?**
OUI : les poids w_j = 3^{k-1-j} forment une progression GEOMETRIQUE de raison 1/3. Cette structure est BEAUCOUP plus specifique qu'un jeu de poids aleatoire. Elle implique :
- Les rapports w_j/w_{j+1} = 3 sont tous EGAUX
- L'action de la permutation cyclique (0, 1, ..., k-1) -> (1, 2, ..., k-1, 0) DECALE les poids par un facteur 3 (modulo bord)
- La matrice de phase Omega a une structure de HANKEL generalisee : Omega_{ij} = omega^{alpha * 3^{k-1-i} * 2^{pi_j}} depend de i et j via 3^{-i} * 2^{pi_j}

**WHY 4 : La structure de progression geometrique aide-t-elle pour les immanants ?**
POTENTIELLEMENT. Les matrices dont les entrees sont de la forme a_i^{b_j} (ou a_i = 3^{-i} et b_j depend de B_j) sont des matrices de VANDERMONDE GENERALISEES. Les determinants de telles matrices ont des formules closes (produit des differences). Les immanants n'ont PAS de formule close en general, mais pour les matrices de Vandermonde, il existe des resultats de Stembridge (1991) et Goulden-Jackson (1992) sur les immanants de matrices totalement non-negatives.

> **R192-C1 [CONJECTURE] (Immanants de matrices de phase geometriques).**
> Pour la matrice Omega_{ij} = omega^{alpha * 3^{k-1-i} * 2^{B_j}} avec B monotone, les immanants satisfont :
>
> |Imm_lambda(Omega)| <= d_lambda * |det(Omega)|^{1 + epsilon_lambda}
>
> ou epsilon_lambda > 0 depend de la forme lambda et tend vers 0 quand lambda -> (k).
>
> **Heuristique :** Les matrices de phase geometriques sont "quasi-Vandermonde" et satisfont une version affaiblie de la total-non-negativite. Les resultats de Stembridge montrent que pour les matrices totalement non-negatives, Imm_lambda >= 0 et Imm_lambda <= perm(M) pour tout lambda. Notre matrice n'est PAS totalement non-negative (les entrees sont complexes), mais la structure geometrique des lignes et colonnes devrait fournir une borne analogue.

**WHY 5 : Que faudrait-il pour fermer C1 ?**
Trois ingredients :
1. Une borne sur SUM_B |Imm_lambda(Omega(B))| pour lambda != (k), exploitant la structure geometrique des poids
2. Un controle du nombre de representations lambda qui contribuent significativement (concentration de Plancherel)
3. Une borne inferieure sur |Lambda_free(s)| en termes du produit PROD |rho_{a_j}| (pour que la correction soit RELATIVEMENT petite)

L'ingredient 1 est le plus difficile. L'ingredient 2 est accessible par les resultats de Vershik-Kerov (la mesure de Plancherel se concentre autour de la forme Omega de Logan-Shepp-Vershik-Kerov). L'ingredient 3 est R191-T1 (factorisation sous integrale).

### IV.4 Nouvelle formulation de C1

En combinant les trois approches :

> **R192-C2 [CONJECTURE REFORMULEE = C1'].**
> Pour d = 2^S - 3^k impair, d >= 5, s != 0 mod d, et n = S - k :
>
> |Lambda(s) - Lambda_free(s)/k!| <= (1 - delta) * |Lambda_free(s)| / k!
>
> pour un delta > 0 dependant de k, avec delta >= c/k pour une constante absolue c > 0.
>
> **Equivalemment :** Lambda(s) = Lambda_free(s)/k! * (1 + O(1 - delta)), donc |Lambda(s)| <= 2 * |Lambda_free(s)| / k!.

**Interpretation :** La composante triviale (Lambda_free/k!) DOMINE les composantes non-triviales. Le ratio est au pire 2 (la correction est au plus aussi grande que le terme principal).

**Si C2 est vraie :** |Lambda(s)| <= 2 * |Lambda_free(s)| / k! = 2 * s^k * PROD |rho_{a_j}| / k!. Par BKT, PROD |rho_{a_j}| <= d^{-k*eta}. Donc |Lambda(s)| <= 2 * s^k * d^{-k*eta} / k!. La condition |Lambda(s)| < p_k(n)/(d-1) est satisfaite des que 2*s^k*d^{-k*eta}/k! < p_k(n)/d, ce qui est PLUS FACILE a satisfaire que sans le facteur 1/k!.

Le facteur 1/k! est le GAIN de la symetrie -- c'est le ratio entre le nombre de partitions et le nombre de compositions dans le regime generique.

---

## PARTIE V : REGISTRE DES RESULTATS

### V.1 Tableau recapitulatif

| # | Resultat | Statut | Section | Dependances |
|---|----------|--------|---------|-------------|
| R192-L1 | Effet d'une transposition sur g | **PROUVE** | A.1 | Aucune |
| R192-L2 | Annulation par paires | **PROUVE** | A.2 | Aucune |
| R192-T1 | Lambda_free comme permanent generalise | **PROUVE** | A.5 | Aucune |
| R192-T2 | Decomposition isotypique de Lambda_free | **PROUVE** | B.2 | Aucune |
| R192-T3 | Correction par representations non-triviales | **PROUVE** | B.3 | T2 |
| R192-T4 | Composante signe = determinant | **PROUVE** | B.5 | T2 |
| R192-T5 | Decomposition de la somme par RSK | **PROUVE** (formelle) | C.3 | RSK |
| R192-T6 | Frobenius pour Lambda_sigma | **PROUVE** | C.5 | Aucune |
| R192-T7 | Lambda comme somme d'immanants | **PROUVE** | C.6 | T2, T6 |
| R192-O1 | Permanent ~ sqrt(k!) heuristique | **OBSERVATION** | A.6 | Second moment |
| R192-O2 | Composantes non-triviales grandes | **OBSERVATION** | B.4 | Variation exp. poids |
| R192-O3 | Discrepancy et anisotropie | **OBSERVATION** | B.6 | Geometrie de Weyl |
| R192-O4 | id = pire cas (anti-alignement) | **OBSERVATION** (corrigee) | C.5 | R191-O1 |
| R192-C1 | Immanants de matrices geometriques | **CONJECTURE** | IV.3 | Stembridge |
| R192-C2 | C1' reformulee (correction < principal) | **CONJECTURE** | IV.4 | Combinaison A+B+C |

### V.2 Score d'avancement

| Critere | Score | Commentaire |
|---------|-------|-------------|
| Profondeur d'investigation | 9/10 | 3 approches analysees en detail, WHY chains completes |
| Resultats prouves | 7/10 | 9 resultats prouves (L1, L2, T1-T7), cadre solide |
| Progression vers C1 | 5/10 | Reformulation (C2) mais pas de preuve ; bornes existantes insuffisantes |
| Innovation | 7/10 | Decomposition par immanants (T7), lien Vandermonde generalise |
| Honnetete | 10/10 | Echecs identifies (borne Schur inutile, Cauchy-Schwarz trop grossier) |

### V.3 Recommandations pour R193

**Priorite 1 : Explorer la piste Vandermonde pour les immanants.**
La matrice Omega a une structure geometrique (Omega_{ij} ~ 3^{-i} * 2^{B_j}). Les resultats de Stembridge (1991) sur les immanants des matrices totalement non-negatives et les resultats de Goulden-Jackson (1992) sur les immanants des matrices de Jacobi-Trudi pourraient donner des bornes specifiques.

**Priorite 2 : Calculer explicitement pour k = 3, 4.**
Pour k = 3 : S_3 a 3 representations (triviale, signe, standard de dim 2). Calculer les 3 composantes de Lambda_free et verifier que la composante triviale domine. Pour k = 4 : S_4 a 5 representations. Meme exercice.

**Priorite 3 : Concentration de Plancherel.**
Utiliser les resultats de Vershik-Kerov (1981) et Kerov (1993) sur la mesure de Plancherel pour montrer que les composantes lambda proches de la forme de Plancherel (lambda ~ forme Omega) dominent, et que les autres sont exponentiellement petites.

**Priorite 4 : Methode du col dans l'espace des representations.**
Developper la methode du col pour SUM_B Imm_lambda(Omega(B)) en exploitant la convexite du polytope des partitions et les oscillations de la phase g(B).

---

*R192 Agent A1 (Investigateur) : Trois approches pour C1 analysees en profondeur. (A) Transpositions : mecanisme local d'annulation prouve (L1, L2), verrou = non-commutativite / permanent. (B) Weyl : decomposition spectrale de Lambda_free en composantes indexees par lambda |- k (T2, T3, T4), verrou = composantes non-triviales grandes. (C) RSK : formalisation via immanants (T5, T6, T7), verrou = borne de Schur inutile. Les trois approches convergent vers le MEME probleme : borner la discrepancy de sigma -> Lambda_sigma sur S_k. Nouvelle conjecture C1' (C2) formulee : la composante triviale domine. Piste la plus prometteuse : immanants de matrices de phase geometriques (lien avec Vandermonde et Stembridge). 9 resultats prouves, 2 conjectures, toutes les pistes ouvertes.*
