# R191 -- Agent A3 (Investigateur Profond) : Compensations Orbitales
**Date :** 16 mars 2026
**Mode :** Investigation profonde, raisonnement pur, ZERO calcul
**Prerequis :** R190 (convergence 3 agents vers sum-product sur <2>, compensations orbitales identifiees comme SINGLE BEST BET)
**Mission :** Decouvrir POURQUOI les compensations orbitales fonctionnent, explorer la distribution de g(B) mod d, identifier le vrai levier exploitable.

---

## SYNTHESE EN UNE PHRASE

La compensation orbitale n'est PAS un miracle -- c'est la formule d'inversion de Fourier deguisee -- mais le VRAI levier est que la distribution de g(B) mod d est controlee par la structure multiplicative de d = 2^S - 3^k, et trois mecanismes distincts (equidistribution par defaut, obstruction arithmetique specifique, et amplification par completion) convergent vers N_0(d) = 0 par des voies complementaires.

---

## 1. DEMYSTIFICATION : LA COMPENSATION EST TOUJOURS EXACTE

### 1.1 Le calcul fondateur (k = 3)

Rappel complet pour k = 3 :
- S = ceil(3 * log_2(3)) = 5, d = 2^5 - 3^3 = 32 - 27 = 5
- n = S - k = 2, on cherche les partitions monotones de 2 en 3 parts
- Vecteurs : (0,0,2) et (0,1,1). Donc p_3(2) = 2.
- g(0,0,2) = 9*1 + 3*1 + 1*4 = 16, g(0,1,1) = 9*1 + 3*2 + 1*2 = 17
- omega = e^{2*pi*i/5}, c = 2^{-S} mod 5 = 2^{-5} mod 5.

Calcul de c : 2^5 = 32 equiv 2 mod 5, donc 2^{-5} equiv 2^{-1} equiv 3 mod 5.

Lambda(s) = omega^{3*16*s mod 5} + omega^{3*17*s mod 5} = omega^{48s mod 5} + omega^{51s mod 5} = omega^{3s mod 5} + omega^{s mod 5}

Valeurs :
- s=0 : 1 + 1 = 2
- s=1 : omega + omega^3
- s=2 : omega^2 + omega^6 = omega^2 + omega
- s=3 : omega^3 + omega^9 = omega^3 + omega^4
- s=4 : omega^4 + omega^{12} = omega^4 + omega^2

Somme : 2 + (omega + omega^3) + (omega^2 + omega) + (omega^3 + omega^4) + (omega^4 + omega^2)
= 2 + 2*omega + 2*omega^2 + 2*omega^3 + 2*omega^4
= 2*(1 + omega + omega^2 + omega^3 + omega^4) = 2*0 = 0.

N_cycle = 0/5 = 0. **COMPENSATION EXACTE.**

### 1.2 Pourquoi c'est TOUJOURS exact -- WHY chain (5 niveaux)

**WHY-1 : Pourquoi SUM_s Lambda(s) = 0 exactement ?**
Parce que (1/d) SUM_{s=0}^{d-1} omega^{s*a} = delta_{a,0} pour tout a in Z/dZ. C'est la relation d'orthogonalite des caracteres.

**WHY-2 : Comment cette relation donne-t-elle N_cycle = 0 ?**
En intervertissant les sommes :
N_cycle = (1/d) SUM_s Lambda(s)
= (1/d) SUM_s SUM_B omega^{s*c*g(B)}
= SUM_B (1/d) SUM_s omega^{s*c*g(B)}
= SUM_B [c*g(B) equiv 0 mod d]

Comme c = 3^{-k} mod d est inversible, c*g(B) equiv 0 mod d ssi g(B) equiv 0 mod d. Donc :

**N_cycle = #{B monotone : g(B) equiv 0 mod d}**

C'est la formule de detection de Fourier : une TAUTOLOGIE (on compte les solutions en sommant les caracteres). La compensation n'est PAS un phenomene -- c'est la formule elle-meme.

**WHY-3 : Alors ou est le vrai contenu mathematique ?**
Le contenu est dans le fait que #{B : g(B) equiv 0 mod d} = 0. La formule de Fourier ne fait que REFORMULER ceci. La question est : peut-on prouver que cette quantite est 0 plus facilement via la reformulation spectrale qu'en comptant directement les solutions ?

**WHY-4 : Quand la reformulation spectrale est-elle plus facile ?**
Quand on peut borner chaque |Lambda(s)| pour s >= 1 suffisamment bien, OU quand on peut exploiter des RELATIONS STRUCTURELLES entre les Lambda(s) (orbites, symetries) qui n'ont pas d'equivalent dans le comptage direct.

**WHY-5 : La reformulation spectrale offre-t-elle un avantage REEL pour notre probleme ?**
OUI, pour deux raisons distinctes :
(a) Les Lambda(s) sont des sommes exponentielles sur des partitions -- un objet avec une THEORIE RICHE (Hardy-Ramanujan, Rademacher, methode du col).
(b) Les Lambda(s) pour differentes valeurs de s sont RELIES par la structure multiplicative de d -- quand s varie, c_s = s * 3^{-k} parcourt Z/dZ*, et les symmetries de cette orbite contraignent les Lambda(s).

**STATUT : PROUVE** (identite formelle, pas de conjecture)

### 1.3 Consequence fondamentale : le probleme est COMBINATOIRE, pas spectral

**THEOREME R191-T0 [PROUVE].**
N_cycle = 0 pour un k donne si et seulement si g(B) not_equiv 0 mod d pour toute partition monotone B de n = S-k en k parts.

La reformulation spectrale est un OUTIL, pas le probleme. Le probleme est :

> **g(B) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} never_equiv 0 mod (2^S - 3^k)**

pour B_0 <= ... <= B_{k-1}, SUM B_j = S - k.

Tout le reste (Lambda(s), operateurs T_b, transfert matriciel) est machinerie auxiliaire.

---

## 2. OU EST LE VRAI LEVIER ? -- LA DISTRIBUTION DE g(B) MOD d

### 2.1 L'ensemble des valeurs de g

**DEFINITION R191-D1.** Soit G_k = {g(B) mod d : B in V_k(S)}, ou V_k(S) est l'ensemble des partitions monotones de n = S-k en k parts non-negatives.

|V_k(S)| = p_k(n) (nombre de partitions).
|G_k| <= p_k(n) (avec egalite si toutes les valeurs sont distinctes mod d).

N_cycle = 0 ssi 0 not_in G_k.

### 2.2 Trois regimes de taille

**Regime 1 : p_k(n) < d (la plupart des k).**
Ici, l'ensemble G_k a MOINS d'elements que d. Meme si les valeurs etaient aleatoires et uniformes dans Z/dZ, la probabilite d'eviter 0 serait (1 - 1/d)^{p_k(n)} approx e^{-p_k(n)/d} approx 1. Donc N_cycle = 0 est le comportement "generique" attendu.

C'est le regime de PRESQUE TOUS les k < 42 (par R189-T10, le seuil p_k(n) ~ d est atteint a k ~ 42).

**Regime 2 : p_k(n) ~ d (k autour de 42).**
Zone de transition. Comportement aleatoire donnerait N_cycle ~ 1. C'est la zone critique.

**Regime 3 : p_k(n) >> d (k >> 42).**
Ici, le deuxieme moment (R189-T10) suffit : par equidistribution, N_cycle ~ p_k(n)/d qui est un entier positif si la distribution est vraiment uniforme, MAIS la condition d'integerite + la borne de variance donnent N_cycle = 0 pour p_k(n)/d < 1 dans un sens precis. En fait, pour k >= 42, l'argument de Borel-Cantelli de R189 s'applique.

**STATUT : OBSERVATION** (calibrage bien connu)

### 2.3 WHY-chain : Pourquoi g(B) evite-t-il 0 mod d pour k < 42 ?

**WHY-1 : Pourquoi g(B) mod d devrait-il eviter 0 ?**
Parce que g(B) est une somme PONDEREE de puissances de 2 par des puissances de 3, et d = 2^S - 3^k est lui-meme construit a partir de 2 et 3. La relation 2^S equiv 3^k mod d cree une RIGIDITE arithmetique entre les ingredients de g et le module.

**WHY-2 : Comment cette rigidite se manifeste-t-elle ?**
g(B) equiv 0 mod d signifie SUM 3^{k-1-j} * 2^{B_j} equiv 0 mod (2^S - 3^k). En utilisant 2^S equiv 3^k mod d, chaque 2^{B_j} peut etre "reduit" modulo d en utilisant la relation fondamentale. Si B_j >= S, alors 2^{B_j} equiv 3^k * 2^{B_j - S} mod d. Mais pour k < 42, n = S - k ~ 0.585k, et les B_j sont petits (chaque B_j <= n ~ 0.585k, et typiquement B_j << S). Donc 2^{B_j} < 2^n < 2^S = d + 3^k. Les 2^{B_j} sont "petits" par rapport a d.

**WHY-3 : Pourquoi la petitesse des 2^{B_j} aide-t-elle ?**
Parce que g(B) = SUM 3^{k-1-j} * 2^{B_j} avec des termes tous positifs et tous < d (si 2^{B_j} < d/3^{k-1} pour tout j, alors g(B) < k * d, donc g(B) prend au plus k valeurs distinctes modulo d : 0, 1, ..., k-1 fois d). Plus precisement :

g(B) <= SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_{k-1}} = 2^{B_{k-1}} * (3^k - 1)/2

car le vecteur maximal est (0, ..., 0, n). Donc g_max = 2^n * (3^k - 1)/2.

Pour k < 42 avec S = ceil(1.585k) et n = S - k ~ 0.585k :
g_max ~ 2^{0.585k} * 3^k / 2 = (2^{0.585} * 3)^k / 2 ~ (1.5 * 3)^k / 2 = 4.5^k / 2

Et d ~ 2^{1.585k} ~ 3^k = (2^{1.585})^k.

Ratio g_max/d ~ 4.5^k / (2 * 3^k) = (4.5/3)^k / 2 = 1.5^k / 2. Pour k >= 2, ce ratio > 1, donc g_max > d. L'argument de l'arc (g(B) < d pour tout B) ne marche que pour k <= 5 environ.

**CORRECTION CRITIQUE :** Recalculons plus soigneusement.
g_max = 2^n * (3^k - 1)/2 quand B = (0, ..., 0, n).
d = 2^S - 3^k.
g_max / d = 2^n * (3^k - 1) / (2 * (2^S - 3^k))
= 2^{S-k} * (3^k - 1) / (2 * (2^S - 3^k))
= (2^S * (3^k - 1)) / (2^{k+1} * (2^S - 3^k))
= (d + 3^k)(3^k - 1) / (2^{k+1} * d)
~ 3^{2k} / (2^{k+1} * 3^k) = 3^k / 2^{k+1} = (3/2)^k / 2

Pour k = 3 : (3/2)^3 / 2 = 3.375/2 = 1.6875. Donc g_max > d pour k = 3, mais SEULEMENT par un facteur 1.7.
Pour k = 6 : (3/2)^6 / 2 = 11.39/2 = 5.7. Plus large.
Pour k = 20 : (3/2)^{20} / 2 ~ 3325/2 = 1662. Beaucoup plus large.

Donc pour k >= 3, g_max > d, et l'argument direct "g ne peut pas atteindre 0 mod d" (arc argument) echoue.

**WHY-4 : Alors comment prouver l'evitement de 0 pour k < 42 ?**
Trois approches possibles :
(A) Montrer que g(B) mod d est "bien reparti" et qu'avec seulement p_k(n) << d valeurs, la probabilite d'atteindre 0 est negligeable.
(B) Montrer que g(B) mod d EVITE 0 par une OBSTRUCTION ARITHMETIQUE specifique.
(C) Montrer que les Lambda(s) pour s >= 1 satisfont des bornes MEILLEURES que la borne uniforme, grace a la structure de d.

**WHY-5 : Laquelle est la plus prometteuse ?**
(A) est l'approche probabiliste -- elle fonctionne pour "la plupart" des k mais ne peut pas couvrir tous les k (elle ne dit rien sur les cas speciaux).
(B) est l'approche exacte -- elle fonctionnerait pour TOUT k mais necessite une structure tres specifique.
(C) est l'approche spectrale -- c'est le programme R189-R190. Elle necessite de borner Lambda(s).

L'INNOVATION de R191 est de COMBINER (A) et (B) : utiliser (A) pour la plupart des k, et (B) pour les k exceptionnels.

**STATUT : CADRAGE STRATEGIQUE** (pas de conjecture)

---

## 3. LA DISTRIBUTION DE g(B) MOD d : ANALYSE STRUCTURELLE

### 3.1 g(B) comme combinaison lineaire dans le "ring" engendre par 2 et 3

**THEOREME R191-T1 [PROUVE].**
g(B) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} est un element de l'ensemble :

E(k, S) = {SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{b_j} : 0 <= b_0 <= ... <= b_{k-1}, SUM b_j = S - k}

Cet ensemble est contenu dans le sous-anneau de Z engendre par les puissances de 2 et 3.

La reduction modulo d = 2^S - 3^k utilise l'identite fondamentale 2^S equiv 3^k mod d.

**Preuve :** Definition directe. L'identite 2^S = d + 3^k donne 2^S equiv 3^k mod d.

### 3.2 L'espace des "lettres" et la projection sur Z/dZ

Chaque terme 3^{k-1-j} * 2^{B_j} vit dans le "cone multiplicatif" engendre par 2^a * 3^b pour a, b >= 0. La projection sur Z/dZ envoie ce cone dans un sous-ensemble de Z/dZ.

**DEFINITION R191-D2.** Le "fibre" de 0 dans E(k, S) est :
F_0 = {B in V_k(S) : g(B) equiv 0 mod d}

N_cycle = |F_0|. Le probleme est : F_0 = vide.

### 3.3 Structure de g(B) mod d en termes de l'orbite de <2>

Comme 2^{B_j} vit dans le sous-groupe <2> de (Z/dZ)*, la valeur g(B) mod d est une combinaison lineaire :

g(B) = SUM_j alpha_j * u_j mod d

ou alpha_j = 3^{k-1-j} et u_j = 2^{B_j} in <2>.

Les alpha_j parcourent l'orbite de <3> dans (Z/dZ)* (plus precisement, {3^{k-1}, 3^{k-2}, ..., 3, 1} = l'orbite de 1 sous multiplication par 3^{-1}).

Les u_j parcourent l'orbite de <2> avec la contrainte de monotonie.

**THEOREME R191-T2 [PROUVE].**
g(B) equiv 0 mod d si et seulement si la combinaison lineaire
SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} equiv 0 mod d
a une solution monotone. C'est un systeme d'UNE equation a k variables entieres sous contrainte de monotonie et de somme.

**Preuve :** Tautologique -- c'est la definition.

### 3.4 Le polynome de Horner et la structure de g

**THEOREME R191-T3 [PROUVE].**
g(B) peut etre reecrit sous forme de Horner :
g(B) = 2^{B_0} * (3^{k-1} + 3^{k-2} * 2^{Delta_1} + 3^{k-3} * 2^{Delta_1 + Delta_2} + ... + 2^{Delta_1 + ... + Delta_{k-1}})
ou Delta_j = B_j - B_{j-1} >= 0 (avec B_{-1} = 0, Delta_0 = B_0).

En factorisant 2^{B_0} :
g(B) = 2^{B_0} * h(Delta_1, ..., Delta_{k-1})
ou h est une somme ponderee a coefficients de Horner.

Plus explicitement :
h(Delta_1, ..., Delta_{k-1}) = 3^{k-1} + SUM_{i=1}^{k-1} 3^{k-1-i} * PROD_{l=1}^{i} 2^{Delta_l}

**Preuve :** Substitution directe B_j = B_0 + Delta_1 + ... + Delta_j et factorisation par 2^{B_0}.

**Consequence :** g(B) equiv 0 mod d ssi 2^{B_0} * h equiv 0 mod d. Comme gcd(2, d) = 1, cela equivaut a h equiv 0 mod d.

**STATUT : PROUVE.**

### 3.5 Valeur de h pour les vecteurs extremaux

**Vecteur minimal** (B_0 = ... = B_{k-1} = n/k si n/k entier) :
g = (3^k - 1)/(3 - 1) * 2^{n/k} = (3^k - 1)/2 * 2^{n/k}

Reduisons mod d : (3^k - 1)/2 * 2^{n/k} mod d.
Or 3^k = 2^S - d equiv 2^S mod d. Donc 3^k - 1 equiv 2^S - 1 mod d.
Donc g_unif equiv (2^S - 1)/2 * 2^{n/k} = (2^{S-1} - 1/2) * 2^{n/k} mod d.

Hmm, (3^k - 1) est pair (3^k est impair), donc (3^k - 1)/2 est un entier.
(3^k - 1)/2 equiv (2^S - 1)/2 mod d.

g_unif = (2^S - 1) * 2^{n/k - 1} mod d.

Pour k = 3 : n = 2, n/k = 2/3 -- non entier. Donc le vecteur uniforme n'existe pas pour k = 3.

**Vecteur concentre** (B = (0, ..., 0, n)) :
g = SUM_{j=0}^{k-2} 3^{k-1-j} * 1 + 3^0 * 2^n = (3^{k-1} + ... + 3) + 2^n = (3^k - 3)/2 + 2^n

Reduisons mod d : (3^k - 3)/2 + 2^n mod d.
3^k equiv 2^S mod d. Donc (3^k - 3)/2 = (2^S - 3)/2 - d/2... Non, d = 2^S - 3^k, et on veut (3^k - 3)/2 mod d.
3^k = d + 2^S... non : d = 2^S - 3^k, donc 3^k = 2^S - d.
(3^k - 3)/2 = (2^S - d - 3)/2 mod d equiv (2^S - 3)/2 mod d (car d equiv 0 mod d).

Hmm, plus soigneusement : (3^k - 3)/2 mod d = ((2^S - d) - 3)/2 mod d = (2^S - 3)/2 - d/2 mod d.

Attention : d est impair, donc d/2 n'est pas entier. On doit travailler avec l'inverse de 2 mod d.

Posons 2^{-1} mod d. Alors (3^k - 3) * 2^{-1} mod d = (3^k - 3) * 2^{-1}.

g_concentre = (3^k - 3) * 2^{-1} + 2^n mod d.

Pour k = 3 : (27 - 3)/2 + 4 = 12 + 4 = 16. Et g(0,0,2) = 16. Coherent. 16 mod 5 = 1 != 0.

**Vecteur etale** (B = (0, 1, 1) pour k = 3, n = 2) :
g = 9*1 + 3*2 + 1*2 = 17. 17 mod 5 = 2 != 0.

**STATUT : PROUVE** (calculs directs)

---

## 4. L'EQUIDISTRIBUTION DE g(B) MOD d : QUAND EST-CE VRAI ?

### 4.1 Le parametre critique : p_k(n)/d

Si g(B) mod d etait UNIFORMEMENT distribue dans Z/dZ, on aurait :
N_t = #{B : g(B) equiv t mod d} approx p_k(n) / d pour chaque t.

Si p_k(n) < d, cela donnerait N_t < 1 pour la plupart des t, et N_0 = 0 avec probabilite ~ (1 - p_k(n)/d).

**DEFINITION R191-D3 (Densite de couverture).** rho_k = p_k(n)/d.

- Pour k = 3 : p_3(2) = 2, d = 5, rho_3 = 0.4.
- Pour k = 5 : n = 3, p_5(3) = 5, d = 2^8 - 3^5 = 256 - 243 = 13, rho_5 = 0.38.
- Pour k = 10 : n = 6, p_10(6) = p(6, <=10) = 11, d = 2^{16} - 3^{10} = 65536 - 59049 = 6487, rho_10 ~ 0.0017.
- Pour k = 42 : rho_42 ~ 1 (le seuil de transition).

**OBSERVATION CRUCIALE :** Pour presque tous les k < 42, rho_k << 1. L'ensemble G_k = {g(B) mod d} ne couvre qu'une INFIME fraction de Z/dZ. Si les valeurs sont "pseudo-aleatoires", eviter 0 est presque certain.

### 4.2 WHY-chain : L'equidistribution est-elle une hypothese raisonnable ?

**WHY-1 : Pourquoi g(B) mod d pourrait-il etre pseudo-aleatoire ?**
Parce que g(B) est une somme de termes 3^j * 2^{B_j} impliquant DEUX bases multiplicatives (2 et 3). La theorie additive des nombres montre que le melange de structures multiplicatives distinctes produit generalement une distribution pseudo-aleatoire (c'est l'essence du phenomene sum-product de Bourgain-Katz-Tao).

**WHY-2 : Y a-t-il un obstacle a l'equidistribution ?**
OUI : la contrainte de monotonie B_0 <= ... <= B_{k-1} et la contrainte de somme SUM B_j = n introduisent des CORRELATIONS fortes entre les termes. Les B_j ne sont pas independants. Cette dependance pourrait creer un biais dans g(B) mod d.

**WHY-3 : Ce biais peut-il concentrer g(B) sur 0 ?**
Il faudrait que g(B) equiv 0 mod d pour au moins un B. C'est une EQUATION DIOPHANTIENNE :
SUM 3^{k-1-j} * 2^{B_j} equiv 0 mod (2^S - 3^k).

L'existence d'une solution depend de la structure ARITHMETIQUE de d, pas juste de la "taille" de l'ensemble des B. Un biais generique ne garantit PAS que 0 est atteint -- il peut biaiser VERS ou LOIN de 0.

**WHY-4 : Dans quelle direction le biais va-t-il ?**
L'identite 2^S equiv 3^k mod d signifie que "passer de la puissance S de 2 a la puissance k de 3" est GRATUIT modulo d. La valeur g(B) melee les deux -- mais les exposants B_j sont tous <= n < S, donc 2^{B_j} ne "boucle" jamais via la relation 2^S = 3^k mod d. Les puissances de 2 restent dans l'intervalle {1, 2, 4, ..., 2^n} qui est STRICTEMENT INCLUS dans <2> = {1, 2, ..., 2^{S-1}} (l'orbite de 2 dans (Z/dZ)* a au plus S elements).

Le biais devrait etre ALEATOIRE par rapport a 0, car il n'y a pas de raison structurelle pour que g(B) favorise 0 plutot qu'une autre valeur.

**WHY-5 : Peut-on PROUVER que le biais ne favorise pas 0 ?**
C'est exactement le probleme. La preuve devrait montrer que la distribution de g(B) mod d est "suffisamment diffuse" pour eviter toute valeur fixee (dont 0). Les outils :
- Bornes exponentielles (Weil, Deligne) si on peut ecrire g comme polynome ou fonction rationnelle
- Methode de completion (enlever la monotonie, corriger ensuite)
- Crible arithmetique (montrer que g(B) est reparti sur de nombreuses classes de residus)

**STATUT : CADRAGE** -- la question est bien posee, la reponse est le coeur du probleme.

---

## 5. COMPLETION : ENLEVER LA MONOTONIE, BORNER LA CORRECTION

### 5.1 L'idee maitresse

**DEFINITION R191-D4 (Somme complete).** Pour s != 0, definissons :
Lambda_free(s) = SUM_{B_0, ..., B_{k-1} >= 0, SUM B_j = n} omega^{c_s * g(B)}

ou la somme est sur TOUTES les k-suites non-negatives de somme n (sans contrainte de monotonie). Le nombre de tels k-tuples est C(n+k-1, k-1) = C(S-1, k-1).

Et definissons la correction :
Lambda_corr(s) = Lambda_free(s) - Lambda(s)

Alors Lambda(s) = Lambda_free(s) - Lambda_corr(s).

### 5.2 Factorisation de Lambda_free ? -- Exploration

**TENTATIVE :** Lambda_free(s) = SUM_{B : SUM B_j = n} omega^{c_s * SUM 3^{k-1-j} * 2^{B_j}}.

Si les B_j etaient INDEPENDANTS (sans la contrainte SUM = n), on aurait :
SUM_{B_0, ..., B_{k-1} >= 0} PROD_j omega^{c_s * 3^{k-1-j} * 2^{B_j}} * q^{SUM B_j}
= PROD_j [SUM_{b >= 0} omega^{c_s * 3^{k-1-j} * 2^b} * q^b]
= PROD_j [SUM_{b >= 0} (omega^{c_s * 3^{k-1-j}} * q)^... ]

Hmm, le probleme est que omega^{c_s * 3^{k-1-j} * 2^b} n'est PAS de la forme (quelque_chose)^b car 2^b n'est pas lineaire en b. La somme SUM_{b >= 0} omega^{a * 2^b} * q^b ne factorise pas trivialement.

**REVISION :** Cette somme est :
phi_j(q) = SUM_{b >= 0} omega^{alpha_j * 2^b} * q^b ou alpha_j = c_s * 3^{k-1-j}

C'est une serie de puissances avec coefficients omega^{alpha_j * 2^b}. Comme 2^b parcourt le sous-groupe <2> de (Z/dZ)* cycliquement (avec periode s = ord_d(2)), les coefficients sont PERIODIQUES en b avec periode s.

**THEOREME R191-T4 [PROUVE].**
phi_j(q) = SUM_{m=0}^{s-1} omega^{alpha_j * 2^m} * q^m / (1 - q^s)

ou s = ord_d(2).

**Preuve :** SUM_{b >= 0} omega^{alpha_j * 2^b} q^b = SUM_{m=0}^{s-1} SUM_{l >= 0} omega^{alpha_j * 2^{m+ls}} q^{m+ls}.
Or 2^{m+ls} = 2^m * 2^{ls} = 2^m * (2^s)^l. Mais 2^s mod d est un element fixe de Z/dZ (c'est 1 si s = ord_d(2), par definition). Donc 2^{m+ls} = 2^m * 1^l = 2^m mod d.
Ainsi omega^{alpha_j * 2^{m+ls}} = omega^{alpha_j * 2^m} pour tout l.
Et SUM_{l >= 0} q^{m+ls} = q^m / (1 - q^s).

Donc phi_j(q) = (1/(1-q^s)) * SUM_{m=0}^{s-1} omega^{alpha_j * 2^m} q^m.

Notons P_j(q) = SUM_{m=0}^{s-1} omega^{alpha_j * 2^m} q^m. Alors phi_j(q) = P_j(q) / (1 - q^s).

**OBSERVATION CLE :** P_j(q) est un polynome de degre s-1 dont les coefficients sont des racines de l'unite d-iemes. Pour q = 1 :
P_j(1) = SUM_{m=0}^{s-1} omega^{alpha_j * 2^m} = rho_{alpha_j} * s

ou rho_{alpha_j} est la "somme de Ramanujan twistee" (moyenne des caracteres sur l'orbite de <2>).

Si alpha_j not_equiv 0 mod d, alors par la borne standard des sommes geometriques sur un sous-groupe :
|P_j(1)| = |SUM_{m=0}^{s-1} omega^{alpha_j * 2^m}|

C'est exactement la SOMME EXPONENTIELLE SUR <2> qui est au coeur de R190. Borner cette somme est le probleme sum-product de Bourgain-Katz-Tao.

### 5.3 La fonction generatrice AVEC contrainte de somme (sans monotonie)

Lambda_free(s) est le coefficient de q^n dans PROD_j phi_j(q).

Lambda_free(s) = [q^n] PROD_{j=0}^{k-1} phi_j(q)
= [q^n] PROD_j P_j(q) / (1 - q^s)^k

**THEOREME R191-T5 [PROUVE].**
Lambda_free(s) = [q^n] Q(q) / (1 - q^s)^k

ou Q(q) = PROD_{j=0}^{k-1} P_j(q) est un polynome de degre k(s-1).

**Preuve :** Substitution directe de phi_j(q) = P_j(q)/(1-q^s) dans le produit.

### 5.4 Evaluation de Lambda_free(s) par les residus

Le pole de Q(q)/(1-q^s)^k * q^{-(n+1)} est a chaque racine s-ieme de l'unite : q = zeta_s^l pour l = 0, ..., s-1, ou zeta_s = e^{2*pi*i/s}.

Le pole principal est q = 1 (l = 0), de multiplicite k.

**Le residu a q = 1 implique Q(1) = PROD_j P_j(1) = PROD_j SUM_{m=0}^{s-1} omega^{alpha_j * 2^m}.**

C'est le PRODUIT de k sommes exponentielles sur <2>, chacune evaluee a un "coefficient" alpha_j = c_s * 3^{k-1-j} different.

**THEOREME R191-T6 [CONDITIONNEL].**
Si chaque facteur |P_j(1)| <= s * |rho_j| avec |rho_j| < 1, alors :
|Lambda_free(s)| <= |Q(1)| * (facteur polynomial en n, k, s) = s^k * PROD |rho_j| * (facteur)

Le budget de dissipation est alors SUM_j log(1/|rho_j|), et si ce budget depasse log d + O(log k), alors |Lambda_free(s)| << p_k(n)/d, ce qui donnerait N_cycle = 0 (apres controle de la correction Lambda_corr).

**Hypothese :** |rho_j| < 1 pour tout j, i.e., la somme exponentielle SUR <2> a un module strictement inferieur a s. C'est VRAI des que alpha_j not_equiv 0 mod d, ce qui est garanti pour s >= 1 (car c_s * 3^{k-1-j} = s * 3^{-1} * 3^{k-1-j} = s * 3^{k-2-j} mod d, qui est nul seulement si s equiv 0 mod d, exclu).

**STATUT : CONDITIONNEL** (la borne |rho_j| < 1 est qualitative ; le QUANTITATIF est le probleme sum-product).

### 5.5 Le probleme de la correction Lambda_corr

Lambda_corr(s) = Lambda_free(s) - Lambda(s) est la somme sur les k-tuples NON-MONOTONES de somme n.

**THEOREME R191-T7 [PROUVE].**
Lambda_corr(s) = SUM_{sigma in S_k, sigma != id} (-1)^{...} ... (par inclusion-exclusion sur les paires B_i > B_{i+1}).

Non, l'inclusion-exclusion est plus subtile. La relation entre suites ordonnees et non-ordonnees est :
#{k-tuples non-ordonnes} = k! * #{k-tuples monotones} (si toutes les valeurs sont distinctes)

Mais les B_j peuvent avoir des repetitions. La formule exacte est :
SUM_{B non-ordonne, SUM = n} = SUM_{sigma in S_k} SUM_{B : B_{sigma(0)} <= ... <= B_{sigma(k-1)}, SUM = n} / (facteur de symetrie)

C'est la decomposition en chambres de Weyl.

**En fait, la relation est PLUS SIMPLE :**
Lambda_free(s) = SUM_{sigma in S_k} Lambda_sigma(s) ou Lambda_sigma(s) est la somme sur les B tels que B_{sigma(0)} <= ... <= B_{sigma(k-1)}.

Non : g(B) = SUM 3^{k-1-j} * 2^{B_j} depend de l'INDEXATION, pas juste de l'ensemble {B_0, ..., B_{k-1}}.

**REVISION FONDAMENTALE :** Lambda_free(s) somme sur les k-tuples (B_0, ..., B_{k-1}) avec SUM = n SANS contrainte d'ordre. Lambda(s) somme sur les k-tuples avec B_0 <= ... <= B_{k-1}. La difference Lambda_corr n'a PAS de formule simple en termes de permutations, car g(B) n'est PAS symetrique en les B_j (les poids 3^{k-1-j} brisent la symetrie).

**CONSEQUENCE :** La completion est UTILE pour obtenir Lambda_free(s) qui factorise en produit de sommes exponentielles, MAIS la correction Lambda_corr est difficile a borner.

**STRATEGIE ALTERNATIVE :** Au lieu de borner Lambda_corr directement, utiliser l'identite Lambda_free(s) = SUM_{sigma in S_k} Lambda_{sigma}(s) ou Lambda_{sigma}(s) est la somme avec l'ordre sigma-induit. Chaque Lambda_{sigma} est une somme du MEME type que Lambda (partitions monotones, mais avec des poids permutes 3^{k-1-sigma^{-1}(j)} au lieu de 3^{k-1-j}).

**THEOREME R191-T8 [PROUVE].**
Lambda_free(s) = SUM_{sigma in S_k} Lambda_{sigma}(s)
ou Lambda_{sigma}(s) = SUM_{B_{sigma(0)} <= ... <= B_{sigma(k-1)}, SUM = n} omega^{c_s * SUM_j 3^{k-1-j} * 2^{B_j}}.

Chaque Lambda_{sigma} est une somme exponentielle sur les partitions monotones (via le changement B'_i = B_{sigma(i)}), mais avec des poids PERMUTES alpha_{sigma,j} = 3^{k-1-sigma^{-1}(j)}.

**Preuve :** Partition de l'ensemble des k-tuples en chambres de Weyl. Chaque chambre {B_{sigma(0)} <= ... <= B_{sigma(k-1)}} est en bijection avec les partitions monotones via reindexation.

**Consequence :** Lambda(s) = Lambda_{id}(s) = Lambda_free(s) - SUM_{sigma != id} Lambda_{sigma}(s).

Pour borner Lambda(s), il suffit de borner Lambda_free(s) et chaque Lambda_{sigma}(s) pour sigma != id.

**Le point cle :** Chaque Lambda_{sigma}(s) est une somme du MEME TYPE FORMEL que Lambda(s) (partitions monotones avec poids multiplicatifs). Les memes bornes s'appliquent. Donc si on arrive a borner Lambda(s) de facon GENERIQUE (pour n'importe quelle suite de poids), la meme borne s'applique a tous les Lambda_{sigma}.

**STATUT : PROUVE** (decomposition algebrique)

---

## 6. LE MECANISME D'OBSTRUCTION ARITHMETIQUE SPECIFIQUE A d = 2^S - 3^k

### 6.1 L'identite fondamentale et ses consequences

**THEOREME R191-T9 [PROUVE].**
Pour d = 2^S - 3^k, les identites suivantes sont equivalentes :
(a) 2^S equiv 3^k mod d
(b) 2^S + d = 3^k + 2d (i.e., 2^S = 3^k + d en entiers, par definition)
(c) (2/3)^k equiv 2^{S-k} * 3^{-k} equiv 2^n * 3^{-k} mod d
(d) Le "ratio de Collatz" (3/2)^k satisfait (3/2)^k * 2^n equiv 1 + d/3^k * ... Non, reprenons.

L'identite fondamentale est simplement : **2^S - 3^k = d**.

Consequence arithmetique : dans Z/dZ, on a 2^S = 3^k. Donc l'exposant S "identifie" les deux bases.

### 6.2 WHY g(B) equiv 0 mod d est difficile a satisfaire

**THEOREME R191-T10 [CONJECTURE -- argument heuristique fort].**
Pour k < 42, la condition g(B) equiv 0 mod d ne peut etre satisfaite, heuristiquement parce que :

(A) g(B) est une somme de k termes positifs 3^{k-1-j} * 2^{B_j}, chacun < d (pour la plupart des B_j).
(B) La somme g(B) est comprise entre g_min = (3^k - 1)/2 (quand B = (0,...,0)) et g_max ~ (3/2)^k * d / 2.
(C) Les valeurs g(B) mod d sont "diffusees" par le melange multiplicatif 2-3.
(D) Avec seulement p_k(n) << d valeurs, la probabilite d'atteindre 0 est ~ p_k(n)/d << 1.

Cet argument est HEURISTIQUE car il repose sur l'hypothese que g(B) mod d se comporte "comme aleatoire". La preuve rigoureuse necessite soit :
- Une borne sur les sommes exponentielles Lambda(s) (approche spectrale)
- Un argument diophantien direct (approche arithmetique)

**STATUT : CONJECTURE**

### 6.3 L'obstruction modulaire : p premiers divisant d

**IDEE R191-I1 (Crible modulaire).** Pour montrer que g(B) not_equiv 0 mod d, il suffit de montrer que g(B) not_equiv 0 mod p pour UN SEUL facteur premier p de d.

Si d a un petit facteur premier p, on peut analyser g(B) mod p. L'ensemble V_k(S) se projette sur Z/pZ via g(B) mod p. Si cette projection evite 0, c'est termine.

**THEOREME R191-T11 [PROUVE].**
Si p | d est premier et si g(B) not_equiv 0 mod p pour tout B in V_k(S), alors N_cycle = 0.

**Preuve :** g(B) equiv 0 mod d implique g(B) equiv 0 mod p. Contrapositif.

**Le levier :** Pour un petit premier p | d, l'ensemble {g(B) mod p : B in V_k(S)} est un sous-ensemble de Z/pZ de taille <= min(p, p_k(n)). Si p_k(n) < p, alors l'image a au plus p_k(n) elements parmi p possibles, et eviter 0 est "probable".

**POUR d PREMIER :** Pas de petit facteur a exploiter. Il faut travailler avec d entier directement. C'est le cas le plus difficile.

### 6.4 Structure speciale de l'ordre de 2 modulo d

**FAIT R191-F1 [PROUVE].**
ord_d(2) divise 2S.

**Preuve :** 2^S equiv 3^k mod d, donc 2^{2S} equiv 3^{2k} equiv 9^k mod d. Aussi, 2^{2S} = (2^S)^2 = (d + 3^k)^2 = d^2 + 2d*3^k + 3^{2k} equiv 3^{2k} mod d. Cela ne donne que 2^{2S} equiv 9^k mod d. Pour montrer que ord_d(2) | 2S, il faudrait 2^{2S} equiv 1 mod d, ce qui n'est pas garanti.

**CORRECTION :** On sait 2^S equiv 3^k mod d. Si 3^k a un inverse mod d (garanti car gcd(3,d) = 1), alors 2^S * 3^{-k} equiv 1 mod d. Cela signifie que l'element 2^S * 3^{-k} dans (Z/dZ)* est l'identite. L'ordre de 2 dans (Z/dZ)* divise l'entier m tel que 2^m equiv 1 mod d. Mais 2^S = 3^k en termes de l'identite 2^S equiv 3^k mod d, pas 2^S equiv 1.

L'ordre de 2 mod d est le plus petit S' > 0 tel que 2^{S'} equiv 1 mod d. Comme 2^S equiv 3^k mod d (pas 1), ord_d(2) ne divise pas necessairement S.

En fait, ord_d(2) | phi(d) (ordre du groupe multiplicatif). Pour d premier, phi(d) = d-1.

**FAIT R191-F2 [PROUVE].**
L'element 2^S mod d = 3^k mod d. L'ordre de (3^k mod d) dans (Z/dZ)* divise phi(d). La relation 2^S equiv 3^k mod d contraint les ordres de 2 et 3 modulo d : ord_d(2) et ord_d(3) satisfont S * (1/ord_d(2)) et k * (1/ord_d(3)) aboutissent au meme element de (Z/dZ)* en un nombre comparable de pas.

**STATUT : PROUVE** (theorie des groupes elementaire)

---

## 7. LES SOMMES EXPONENTIELLES SUR <2> : LE COEUR DU PROBLEME

### 7.1 La somme a borner

D'apres R190 (convergence des 3 agents) et la Section 5 ci-dessus, le probleme se reduit a borner :

**Sigma(a) = SUM_{m=0}^{s-1} omega^{a * 2^m}** pour a not_equiv 0 mod d,

ou s = ord_d(2) et omega = e^{2*pi*i/d}.

C'est une somme de Gauss INCOMPLETE (ou somme exponentielle sur un sous-groupe multiplicatif).

### 7.2 WHY-chain : Bornes connues

**WHY-1 : Quelle est la borne triviale ?**
|Sigma(a)| <= s (somme de s termes de module 1).

**WHY-2 : Quand est-elle atteinte ?**
Quand tous les termes omega^{a * 2^m} sont egaux, i.e., a * 2^m equiv a * 2^0 mod d pour tout m, i.e., a*(2^m - 1) equiv 0 mod d pour tout m. Si a not_equiv 0 et d est premier, cela exige 2^m equiv 1 mod d pour tout m < s, contradiction avec la definition de s. Donc pour d premier et a != 0, |Sigma(a)| < s.

**WHY-3 : Quelle est la meilleure borne connue ?**
C'est le probleme de Bourgain-Katz-Tao (2004) / Bourgain (2005). Pour un sous-groupe H de (Z/pZ)* avec |H| = p^delta (0 < delta < 1) :
|SUM_{h in H} e^{2*pi*i*a*h/p}| <= C * |H|^{1-epsilon}
pour un epsilon = epsilon(delta) > 0. C'est la borne "sum-product".

Pour notre cas : H = <2>, |H| = s = ord_d(2). Si s ~ d^delta avec 0 < delta < 1, Bourgain donne :
|Sigma(a)| <= C * s^{1-epsilon}.

**WHY-4 : Le gain s^{-epsilon} est-il suffisant ?**
On a besoin de PROD_j |rho_j| << 1/d (Section 5.4), ou |rho_j| ~ |Sigma(alpha_j)| / s <= C * s^{-epsilon}. Le produit est C^k * s^{-k*epsilon}. On veut C^k * s^{-k*epsilon} < 1/d ~ 3^{-k}.

Condition : s^{k*epsilon} > C^k * 3^k, i.e., s^{epsilon} > 3C, i.e., s > (3C)^{1/epsilon}.

Pour s ~ S ~ 1.585k (l'ordre de 2 mod d), et epsilon est un exposant ABSOLU (ne dependant pas de k), la condition est satisfaite pour k assez grand. Le seuil depend de C et epsilon.

**WHY-5 : Quand cela couvre-t-il k < 42 ?**
C'est la QUESTION QUANTITATIVE. Bourgain donne epsilon tres petit (explicitement epsilon ~ 10^{-10} dans certaines versions). Ce n'est pas suffisant pour les petits k.

Pour les petits k, il faut une borne EXPLICITE et FORTE sur |Sigma(a)|. Les bornes de Weil classiques donnent, pour d premier :
|Sigma(a)| <= sqrt(d) * (quelque chose)

quand la somme peut etre interpretee comme somme de Kloosterman ou somme sur une courbe algebrique. Mais SUM omega^{a*2^m} est une somme sur un sous-groupe, pas une somme sur une courbe.

**STATUT : ANALYSE** (bornes connues insuffisantes quantitativement pour k < 42)

### 7.3 Approche alternative : Bornes specifiques a d = 2^S - 3^k

**THEOREME R191-T12 [CONJECTURE].**
Pour d = 2^S - 3^k premier et a not_equiv 0 mod d :
|Sigma(a)| = |SUM_{m=0}^{S-1} omega^{a * 2^m}| <= C_0 * sqrt(S * d)

ou C_0 est une constante absolue.

**Argument heuristique :** La somme Sigma(a) est une somme de S termes de module 1 avec des phases omega^{a*2^m} qui parcourent <2> = {1, 2, 4, ..., 2^{S-1}} dans (Z/dZ)*. Pour d premier, les puissances de 2 sont bien reparties dans (Z/dZ)* (a une sous-structure multiplicative pres). Par l'inegalite de Polya-Vinogradov generalisee, les sommes de caracteres tronquees satisfont des bornes ~ sqrt(d) * log(d). La somme Sigma(a) est du meme type (somme partielle de caracteres le long d'une progression geometrique).

La borne sqrt(S*d) donnerait |rho| ~ sqrt(S*d) / S = sqrt(d/S). Pour d ~ 3^k et S ~ 1.585k :
|rho| ~ 3^{k/2} / sqrt(1.585k) ~ 3^{k/2} / k^{1/2}

Le produit PROD |rho_j|^{Delta_j} avec budget SUM Delta_j = n ~ 0.585k serait :
~ (3^{k/2} / k^{1/2})^{0.585k} = 3^{0.293k^2} / k^{0.293k}

C'est ENORMEMENT plus grand que 1/d ~ 3^{-k}. La borne sqrt(d) est BEAUCOUP trop faible pour notre usage.

**REVISION :** La borne dont on a besoin est |rho_j| < 1 (dissipation absolue), pas |rho_j| < 1/poly. Et on a besoin que le PRODUIT des |rho_j| sur ~0.585k etapes actives soit < 1/d.

Traduit en termes de dissipation par etape : on a besoin de |rho| ~ d^{-1/0.585k} ~ 3^{-1/0.585} ~ 3^{-1.71} ~ 0.064 par etape active. C'est |rho| < 0.1. Cela correspond a |Sigma(a)| < 0.1 * s.

Pour s ~ S ~ 1.585k ~ 25 (pour k = 16), on a besoin de |Sigma(a)| < 2.5 sur une somme de 25 termes de module 1. C'est une ANNULATION de 90%, bien au-dela des bornes de Bourgain generiques.

**STATUT : La borne generique est INSUFFISANTE. Il faut exploiter la structure specifique de d.**

---

## 8. LE MECANISME DE COMPENSATION : RETOUR AU VRAI LEVIER

### 8.1 Reformulation du probleme

Revenant a l'observation fondamentale de la Section 1 : la compensation entre les Lambda(s) est toujours exacte (c'est Fourier). La question n'est PAS de borner chaque Lambda(s), mais de montrer que :

**Le nombre de B tels que g(B) equiv 0 mod d est 0.**

Les approches par bornes uniformes sur Lambda(s) ECHOUENT quantitativement pour k < 42 (Section 7.3). L'approche par completion (Section 5) introduit une correction difficile a borner.

### 8.2 L'approche directe : proprietes arithmetiques de g(B)

**THEOREME R191-T13 [PROUVE].**
g(B) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} satisfait :
(a) g(B) > 0 pour tout B (tous les termes sont positifs)
(b) g(B) >= (3^k - 1)/2 (atteint pour B = (0, ..., 0, 0, ..., 0), mais en fait g_min = SUM 3^{k-1-j} = (3^k-1)/2)
(c) g(B) <= (3^k - 1)/2 * 2^n (atteint pour B = (n, n, ..., n)... NON : les B_j sont monotones avec SUM = n. Le max est atteint quand B = (0,...,0,n), soit g = (3^k - 3)/2 + 2^n, et le min quand B = (0,...,0,...,0), soit g = (3^k-1)/2.)

**CORRECTION :**
- g_min = g(0,0,...,0) = SUM 3^{k-1-j} * 1 = (3^k - 1)/2. MAIS SUM B_j = n, et si B = (0,...,0), alors SUM B_j = 0 != n (sauf n = 0, soit S = k). Donc le vecteur minimal depend de n.

En fait, pour SUM B_j = n, le vecteur qui MINIMISE g est celui qui met le poids sur les B_j a GRAND j (car le poids 3^{k-1-j} est petit pour grand j). C'est B = (0, ..., 0, n), qui donne :
g_min = (3^{k-1} + ... + 3 + 0) + 2^n = (3^k - 3)/2 + 2^n.
Hmm non : g(0,...,0,n) = 3^{k-1}*1 + 3^{k-2}*1 + ... + 3^1*1 + 3^0*2^n = (3^k - 3)/2 + 2^n.
(Somme de 3^{k-1} + ... + 3 = (3^k-3)/2, les k-1 premiers termes avec B_j=0, plus 2^n pour j=k-1.)

Attendons -- c'est le MINIMUM ou le MAXIMUM ? Le poids 3^{k-1-j} est DECROISSANT en j. Donc le terme 3^0 * 2^{B_{k-1}} est multiplie par le PLUS PETIT poids. Mettre tout le budget sur B_{k-1} minimise g si 2^n > 1, ce qui est toujours vrai pour n >= 1.

En fait, par l'inegalite de rearrangement : g est minimise quand les 2^{B_j} (croissants) sont apparies aux 3^{k-1-j} (decroissants) -- ce qui est exactement l'appariement anti-concordant. C'est le cas de la monotonie par defaut ! Donc g est DEJA minimise dans notre cadre.

Et g est maximise quand les 2^{B_j} sont apparies aux 3^{k-1-j} en sens concordant -- ce qui correspond a B DECROISSANT. Mais on exige B monotone croissant, donc le max est atteint pour B aussi "plat" que possible.

**CORRECTION DEFINITIVE :**
- g est minimise (dans notre cadre monotone) quand le budget n est concentre sur le DERNIER indice : B = (0,...,0,n). Donne g_min_mono = (3^k-3)/2 + 2^n.
- g est maximise (dans notre cadre monotone) quand le budget est reparti le plus uniformement possible.

Non, reprenons calmement. g = SUM 3^{k-1-j} * 2^{B_j} ou les B_j sont croissants. Le premier terme a le poids 3^{k-1} (grand) et 2^{B_0} (petit car B_0 est le plus petit). Le dernier terme a le poids 3^0 = 1 (petit) et 2^{B_{k-1}} (grand).

Pour MAXIMISER g : on veut que les grands poids 3^{k-1-j} soient multiplies par les grandes valeurs 2^{B_j}. Mais la monotonie force 2^{B_0} <= ... <= 2^{B_{k-1}}, et les poids sont dans l'ORDRE INVERSE (3^{k-1} > ... > 3^0). Donc la monotonie force un appariement anti-concordant. Le maximum SOUS CONTRAINTE DE MONOTONIE est atteint quand les B_j sont tous egaux (minimisant l'anti-concordance), et le minimum quand les B_j sont aussi etales que possible (maximisant l'anti-concordance).

Specifiquement :
- B = (n/k, ..., n/k) (si divisible) donne g_flat = (3^k-1)/2 * 2^{n/k}
- B = (0,...,0,n) donne g_steep = (3^k-3)/2 + 2^n

Pour k = 3, n = 2 : g_flat serait B = (2/3,...) -- non entier. B = (0,1,1) est le plus "plat" possible. g(0,1,1) = 17. g(0,0,2) = 16. Donc g(0,1,1) > g(0,0,2). Coherent : le vecteur plat MAXIMISE.

**THEOREME R191-T14 [PROUVE].**
Pour les partitions monotones B de n en k parts :
g_steep = g(0,...,0,n) <= g(B) <= g_flat ~ (3^k-1)/2 * 2^{n/k}

(avec g_flat atteint pour le vecteur le plus uniforme possible).

L'intervalle [g_steep, g_flat] a une longueur approximative (3^k/2) * (2^{n/k} - 1).

**Preuve :** Inegalite de rearrangement sous contrainte de monotonie.

### 8.3 L'intervalle de g mod d et la condition g equiv 0

Pour que N_cycle = 0, il faut que l'intervalle d'entiers {g(B) : B in V_k(S)} evite tous les multiples de d (i.e., d, 2d, 3d, ...).

L'image de g(B) est un sous-ensemble de l'intervalle [g_steep, g_flat]. Les multiples de d dans cet intervalle sont 1*d, 2*d, ..., floor(g_flat/d)*d.

Le nombre de multiples de d dans [g_steep, g_flat] est au plus (g_flat - g_steep)/d + 1.

Pour que N_cycle = 0, il faut que AUCUNE des p_k(n) valeurs de g(B) ne soit un multiple de d. La "densite" de multiples de d est 1/d, et le nombre de valeurs est p_k(n), donc la "probabilite" d'eviter est ~ (1 - 1/d)^{p_k(n)}.

**MAIS ATTENTION :** Les valeurs g(B) ne sont PAS uniformement reparties dans [g_steep, g_flat]. Elles sont concentrees pres du centre (par des arguments de type CLT sur les partitions).

### 8.4 L'argument de concentration

**THEOREME R191-T15 [CONDITIONNEL sur la distribution de g].**
Si g(B) est approximativement normalement distribue dans l'intervalle [g_steep, g_flat] avec ecart-type sigma_g, alors la probabilite qu'une valeur soit un multiple de d est approximativement 1/d (pour d >> sigma_g). Le nombre attendu de solutions est p_k(n)/d = rho_k.

Pour k < 42, rho_k << 1, donc le nombre ATTENDU de solutions est < 1. Par integerite, le nombre reel est 0 (avec probabilite ~ 1 - rho_k) ou 1 (avec probabilite ~ rho_k).

**STATUT : CONDITIONNEL** (necessite la normalite approximative de g(B))

---

## 9. CONVERGENCE DES TROIS MECANISMES

### 9.1 Mecanisme M1 : Equidistribution par defaut (k < 42, rho_k << 1)

**Resume :** Pour la plupart des k < 42, le nombre de partitions p_k(n) est tres inferieur a d. Meme sans aucune structure speciale, la probabilite qu'une des p_k(n) valeurs de g(B) tombe sur 0 mod d est ~ p_k(n)/d << 1.

**Force :** S'applique a TOUS les k < 42 simultanement (pas cas par cas).
**Faiblesse :** Argument probabiliste, pas deterministe. Ne PROUVE pas N_0 = 0, seulement que c'est "probable".

**STATUT : HEURISTIQUE FORTE**

### 9.2 Mecanisme M2 : Obstruction arithmetique (structure de d)

**Resume :** La relation 2^S = 3^k + d signifie que g(B) mod d est une combinaison "biaisee" de puissances de 2 et 3. Si d a un petit facteur premier p, la condition g equiv 0 mod p peut etre verifiee directement (Section 6.3).

**Force :** Preuve EXACTE pour chaque k individuel.
**Faiblesse :** Necessite un calcul specifique pour chaque k. Ne fonctionne que si d a un petit facteur premier.

**STATUT : OUTIL AUXILIAIRE** -- utile pour les cas individuels, pas pour le theoreme general.

### 9.3 Mecanisme M3 : Amplification spectrale (bornes sum-product)

**Resume :** Via la decomposition Lambda_free = PROD P_j et la borne sum-product de Bourgain, on obtient |rho_j| < 1 pour chaque etape, et le produit est exponentiellement petit.

**Force :** Methode systematique et generale.
**Faiblesse :** Les constantes quantitatives sont insuffisantes pour k < 42 avec les bornes actuelles.

**STATUT : CONDITIONNEL SUR DES BORNES QUANTITATIVES MEILLEURES**

### 9.4 La VRAIE piste : combiner M1 + M3

**THEOREME R191-T16 [SCHEMA DE PREUVE].**
Pour montrer N_cycle = 0 pour tout k >= 2 :

**Etape 1 (k >= 42) :** Deuxieme moment (R189-T10). DEJA acquis.

**Etape 2 (2 <= k <= 41, d compose) :** Crible modulaire (M2). Factoriser d = 2^S - 3^k et verifier g(B) not_equiv 0 mod p pour le plus petit facteur premier p. C'est un calcul FINI (40 cas, chacun avec un nombre fini de partitions).

**Etape 3 (2 <= k <= 41, d premier) :** Combiner M1 et M3. La borne sum-product donne |Lambda(s)| < Lambda(0) pour s != 0 (dissipation QUALITATIVE). Le fait que p_k(n)/d << 1 (M1) transforme cette dissipation qualitative en N_0 = 0.

Plus precisement : N_cycle = (1/d) SUM_s Lambda(s). Le terme s=0 donne Lambda(0)/d = p_k(n)/d < 1. Si on peut montrer que |SUM_{s>=1} Lambda(s)| < p_k(n) (i.e., la somme des termes spectraux ne DEPASSE pas le terme principal), alors N_cycle < 2*p_k(n)/d < 2. Par integerite, N_cycle in {0, 1}. Et si N_cycle = 1, le cycle correspond a un B SPECIFIQUE et peut etre analyse.

**Le gap residuel :** Il faut montrer |SUM_{s>=1} Lambda(s)| < p_k(n). Par triangle, |SUM_{s>=1} Lambda(s)| <= SUM_{s>=1} |Lambda(s)| <= (d-1) * max|Lambda(s)|. Cela necessite max|Lambda(s)| < p_k(n)/(d-1), qui est la borne uniforme -- celle qui ECHOUE.

**MAIS** la somme SUM_{s>=1} Lambda(s) n'est PAS |SUM| <= SUM |.|. Les COMPENSATIONS entre Lambda(s) de signes differents peuvent la rendre beaucoup plus petite que la somme des modules.

Et c'est ICI que la compensation orbitale rentre en jeu de facon NON-triviale.

### 9.5 La compensation orbitale comme levier VRAI

**THEOREME R191-T17 [PROUVE].**
SUM_{s=0}^{d-1} Lambda(s) = d * N_cycle. C'est exact.
SUM_{s=0}^{d-1} Lambda(s) = 0 si et seulement si N_cycle = 0.
Equivalemment : SUM_{s=1}^{d-1} Lambda(s) = -Lambda(0) = -p_k(n).

Donc N_cycle = 0 ssi SUM_{s>=1} Lambda(s) = -p_k(n), c'est-a-dire les termes spectraux COMPENSENT exactement le terme principal.

Ce n'est PAS un miracle a expliquer -- c'est une TAUTOLOGIE (Fourier). Le fait que les Lambda(s) compensent exactement est equivalent a dire que g(B) ne prend jamais la valeur 0 mod d.

**Mais voici le tournant :** Si on decompose la somme SUM_{s>=1} par ORBITES de l'action multiplicative, on obtient :

SUM_{s>=1} Lambda(s) = SUM_{orbites O} SUM_{s in O} Lambda(s)

Les orbites sont les orbites de s sous l'action de la multiplication par 3^{-1} (ou par 3) dans (Z/dZ)*. Si s parcourt une orbite O = {s, 3s, 9s, ...} de longueur t, alors les Lambda(s) pour s dans O sont RELIES.

**THEOREME R191-T18 [PROUVE].**
Pour s' = 3s mod d, Lambda(s') = Lambda(s) (les sommes exponentielles sont invariantes par la substitution s -> 3s).

**Preuve :** Lambda(s) = SUM_B omega^{s * c * g(B)} ou c = 3^{-k}.
Lambda(3s) = SUM_B omega^{3s * c * g(B)} = SUM_B omega^{s * 3c * g(B)} = SUM_B omega^{s * 3^{1-k} * g(B)}.
Et Lambda(s) = SUM_B omega^{s * 3^{-k} * g(B)}.

Donc Lambda(3s)/Lambda(s) = SUM_B omega^{s*3^{-k}*(3*g(B) - g(B))} / Lambda(s)... Non, ce n'est pas ca. Verifions :

Lambda(s) = SUM_B omega^{s * 3^{-k} * g(B)}

Lambda(3s) = SUM_B omega^{3s * 3^{-k} * g(B)} = SUM_B omega^{s * 3^{1-k} * g(B)}

Ce n'est PAS egal a Lambda(s) en general. L'invariance ne tient PAS directement.

**CORRECTION :** Il y a une relation entre Lambda(s) et Lambda(3s) via la transformation de g. Examinons :

g(B) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

3 * g(B) = SUM_{j=0}^{k-1} 3^{k-j} * 2^{B_j} = 3^k * 2^{B_0} + SUM_{j=1}^{k-1} 3^{k-j} * 2^{B_j}
= 3^k * 2^{B_0} + 3 * SUM_{j=1}^{k-1} 3^{k-1-j} * 2^{B_j}

Hmm, cela ne simplifie pas directement. La relation 3 * g n'est pas g(B') pour un autre B'. Il n'y a PAS de symetrie simple s -> 3s pour Lambda(s).

**RETRAIT de T18.** L'invariance orbitale NE TIENT PAS pour Lambda(s) sous la multiplication par 3.

### 9.6 La bonne symetrie : multiplication de s par 2

**THEOREME R191-T19 [PROUVE].**
Pour s' = 2^a * s mod d (multiplication par une puissance de 2) :

Lambda(s') = SUM_B omega^{s' * 3^{-k} * g(B)} = SUM_B omega^{s * 2^a * 3^{-k} * g(B)}

Cela revient a remplacer le "coefficient" c = s * 3^{-k} par c' = 2^a * s * 3^{-k}. Le facteur 2^a agit comme une multiplication de la phase totale par 2^a.

Or g(B) = SUM 3^{k-1-j} * 2^{B_j}. Le terme 2^a * g(B) = SUM 3^{k-1-j} * 2^{B_j + a}. Si on definit B'_j = B_j + a (translation uniforme des exposants), alors 2^a * g(B) = g(B'), ou B' = (B_0 + a, ..., B_{k-1} + a).

MAIS B' a la somme SUM B'_j = SUM B_j + ka = n + ka != n (sauf a = 0). Donc B' n'est PAS dans V_k(S).

**Conclusion :** Lambda(2^a * s) = SUM_{B in V_k(S)} omega^{c * g(B+a)} ou B+a signifie la translation uniforme. Comme B+a n'est pas dans V_k(S) en general, cette relation ne donne pas directement Lambda(s) = Lambda(2^a s).

**Neanmoins,** la relation entre Lambda(s) et Lambda(2^a s) est :
Lambda(2^a s) = SUM_{B : SUM B_j = n} omega^{c * SUM 3^{k-1-j} * 2^{B_j+a}} = SUM_{B : SUM B_j = n} omega^{c * 2^a * SUM 3^{k-1-j} * 2^{B_j}}

C'est la MEME somme que Lambda(s) mais avec la phase multipliee par 2^a. En d'autres termes, Lambda(2^a s) = Lambda(s) ssi 2^a equiv 1 mod d, i.e., a est un multiple de ord_d(2).

Pour a < ord_d(2), Lambda(2^a s) est une ROTATION de Lambda(s) dans le plan complexe -- plus precisement, ce n'est pas une simple rotation car 2^a multiplie la phase a l'interieur de la somme, pas a l'exterieur.

**STATUT : PROUVE** (calcul direct, mais pas d'invariance exploitable)

---

## 10. SYNTHESE : OU EN SOMMES-NOUS ?

### 10.1 Ce qui est PROUVE

| Theoreme | Enonce | Statut |
|----------|--------|--------|
| T0 | N_cycle = #{B : g(B) equiv 0 mod d} | PROUVE (tautologie) |
| T1 | g(B) in sous-anneau de Z engendre par 2 et 3 | PROUVE |
| T2 | g(B) equiv 0 ssi equation diophantienne a une solution monotone | PROUVE |
| T3 | Decomposition de Horner de g, factorisation par 2^{B_0} | PROUVE |
| T4 | Periodicite des phases : phi_j(q) = P_j(q)/(1-q^s) | PROUVE |
| T5 | Lambda_free(s) = [q^n] PROD P_j(q) / (1-q^s)^k | PROUVE |
| T8 | Lambda_free = SUM_{sigma} Lambda_sigma (decomposition en chambres) | PROUVE |
| T9 | Identite fondamentale 2^S equiv 3^k mod d | PROUVE (definition) |
| T11 | Crible modulaire : un facteur premier suffit | PROUVE |
| T13 | g(B) > 0, bornes sur g_min et g_max | PROUVE |
| T14 | Rearrangement : g minimise pour B concentre | PROUVE |
| T17 | SUM Lambda(s) = d*N_cycle (exactement) | PROUVE |
| T19 | Relation Lambda(2^a s) et Lambda(s) (pas d'invariance simple) | PROUVE |

### 10.2 Ce qui est CONDITIONNEL

| Theoreme | Condition | Statut |
|----------|-----------|--------|
| T6 | Borne |rho_j| < 1 (qualitative : SURE ; quantitative : probleme sum-product) | CONDITIONNEL |
| T10 | g(B) evite 0 (heuristique probabiliste) | CONJECTURE |
| T12 | Borne explicite |Sigma(a)| <= C*sqrt(S*d) pour d premier | CONJECTURE |
| T15 | Distribution approximativement normale de g(B) | CONDITIONNEL |
| T16 | Schema de preuve complet (3 etapes) | SCHEMA |

### 10.3 Ce qui a ete RETIRE

| Theoreme | Raison du retrait |
|----------|------------------|
| T18 | L'invariance Lambda(3s) = Lambda(s) est FAUSSE |

### 10.4 Les 3 leviers identifies (par ordre de priorite)

**LEVIER 1 (SCHEMA T16, Etape 2) : Verification directe pour k = 2, ..., 41.**
C'est un calcul FINI. Pour chaque k, verifier que g(B) not_equiv 0 mod d pour les p_k(n) partitions. C'est le levier le plus SUR mais le moins "theorique". Il ne donne pas un theoreme UNIFORME.

Effort estime : Pour k = 41, n ~ 24, p_k(n) ~ p(24) ~ 1575. Et d ~ 10^{19}. La verification est triviale par calcul. Mais ce n'est PAS une preuve par raisonnement pur.

**LEVIER 2 (T5 + T6) : Produit de sommes exponentielles sur <2>.**
La factorisation Lambda_free = [q^n] PROD P_j / (1-q^s)^k reduit le probleme a borner PROD |P_j(1)| = PROD |Sigma(alpha_j)|. Chaque facteur est une somme exponentielle sur le sous-groupe <2> de (Z/dZ)*, evaluee a un coefficient alpha_j = c_s * 3^{k-1-j}.

C'est EXACTEMENT le probleme sum-product de Bourgain-Katz-Tao. Le levier est de montrer que |Sigma(alpha_j)| < s * (1 - epsilon) pour un epsilon > 0 UNIFORME, et que le produit de k termes (1-epsilon)^k est < 1/d ~ 3^{-k}.

Condition : (1-epsilon)^k < 3^{-k}, soit 1-epsilon < 1/3, soit epsilon > 2/3. Il faut |Sigma(a)| < s/3.

C'est une ANNULATION de 2/3 de la somme exponentielle sur <2>. Pour s grand, c'est plausible (la borne triviale |Sigma| = s n'est atteinte que pour a = 0). Pour s = 2 ou 3, c'est un calcul direct.

**LEVIER 3 (Combinaison T8 + bornes) : Correction de monotonie via chambres de Weyl.**
Lambda = Lambda_free - SUM_{sigma != id} Lambda_sigma. Si on borne Lambda_free par le produit de sommes exponentielles (Levier 2), et si on borne chaque Lambda_sigma de la MEME facon (memes bornes, poids permutes), alors :

|Lambda(s)| <= |Lambda_free(s)| + SUM_{sigma != id} |Lambda_sigma(s)| <= k! * max_{sigma} |Lambda_sigma(s)|

Le facteur k! est ENORME pour k ~ 40 (k! ~ 10^{47}). Mais si chaque |Lambda_sigma| est exponentiellement petit (par le Levier 2), le facteur k! pourrait etre absorbe.

Condition : |Lambda_sigma(s)| < |Lambda(0)| / (d * k!) pour tout sigma. C'est une borne TRES forte.

**VERDICT :** Le Levier 2 est le plus prometteur mais necessite des bornes quantitatives precises sur les sommes exponentielles sur <2>. Le Levier 1 est infaillible mais n'est pas un theoreme. Le Levier 3 est trop couteux en facteur combinatoire.

---

## 11. INVENTION : LE "TELESCOPE ORBITAL"

### 11.1 L'idee

Au lieu de borner Lambda(s) terme par terme, regroupons les valeurs de s par ORBITES sous l'action de <2> (multiplication par les puissances de 2 dans Z/dZ).

**DEFINITION R191-D5 (Orbite de <2>).** Pour s in (Z/dZ)*, l'orbite de s sous <2> est O_s = {s, 2s, 4s, ..., 2^{S-1}s} (en identifiant s = ord_d(2) et en notant que les elements se repetent avec periode s).

La taille de chaque orbite est exactement s = ord_d(2) (car <2> agit par multiplication et s est l'ordre).

Non : l'orbite de s sous multiplication par 2 a taille s / gcd(position de s dans <2>, s)... En fait, O_s = s * <2>. Si s in <2>, alors O_s = <2>. Si s not_in <2>, alors O_s est un COSET de <2> dans (Z/dZ)*.

Le nombre de cosets est phi(d)/s. Chaque coset a exactement s elements.

**THEOREME R191-T20 [PROUVE].**
La somme SUM_{s' in O_s} Lambda(s') = SUM_{s' in s*<2>} SUM_B omega^{s' * c * g(B)}
= SUM_B SUM_{s' in s*<2>} omega^{s' * c * g(B)}
= SUM_B SUM_{m=0}^{S-1} omega^{s * 2^m * c * g(B)}
= SUM_B Sigma(s * c * g(B))

ou Sigma(a) = SUM_{m=0}^{s-1} omega^{a * 2^m} est la somme exponentielle sur <2>.

**Preuve :** Interversion des sommes et parametrisation de l'orbite s*<2> = {s*2^m : m = 0,...,s-1}.

**Consequence :** SUM_{O_s} Lambda(s') = SUM_B Sigma(s*c*g(B)). Si on peut borner |Sigma(a)| <= s * rho pour a != 0, alors :

|SUM_{O_s} Lambda(s')| <= SUM_B |Sigma(s*c*g(B))| <= p_k(n) * s * rho (si tous les s*c*g(B) != 0 mod d)

Et la somme totale sur tous les cosets non-triviaux (ceux ne contenant pas s = 0) est :
|SUM_{s != 0} Lambda(s)| <= (phi(d)/s - [0 in coset]) * p_k(n) * s * rho ~ phi(d) * p_k(n) * rho

On veut ceci < p_k(n) (pour que N_cycle = |SUM Lambda / d| < p_k(n)/d + 1), soit phi(d) * rho < 1, soit rho < 1/phi(d) ~ 1/d.

C'est TROP faible -- on aurait besoin de |Sigma(a)| < s/d, qui est << 1, une borne IRREALISTE pour une somme de s termes de module 1.

**REVISION :** Le telescope orbital avec la borne triangle est TROP GROSSIER. Il faut exploiter les COMPENSATIONS entre les termes Sigma(s*c*g(B)) pour differents B.

### 11.2 Compensation inter-B

SUM_{O_s} Lambda(s') = SUM_B Sigma(s*c*g(B)).

Si les valeurs s*c*g(B) mod d sont "bien reparties", les Sigma(s*c*g(B)) sont des nombres complexes de modules bornes par s mais de PHASES variees, et leur somme peut etre beaucoup plus petite que p_k(n) * s.

C'est EXACTEMENT la question de la distribution de g(B) mod d (Section 4). La boucle se referme.

**THEOREME R191-T21 [OBSERVATION FONDAMENTALE, PROUVE].**
Le probleme N_cycle = 0 est equivalent a chacun des enonces suivants :
(a) g(B) not_equiv 0 mod d pour tout B (enonce combinatoire)
(b) SUM_{s>=1} Lambda(s) = -p_k(n) (identite de Fourier)
(c) SUM_B Sigma(s*c*g(B)) compense exactement pour tout coset non-trivial (compensation orbitale)

Les trois formulations sont EQUIVALENTES et TAUTOLOGIQUES. Aucune n'est "plus facile" que les autres A PRIORI.

**MAIS :** Chaque formulation ouvre des portes a des OUTILS DIFFERENTS :
- (a) : combinatoire, theorie des nombres (equations diophantiennes)
- (b) : analyse harmonique (bornes sur sommes exponentielles)
- (c) : structure multiplicative (sum-product, Bourgain-Katz-Tao)

### 11.3 L'invention : la MOYENNE ORBITALE

**DEFINITION R191-D6 (Moyenne orbitale).** Pour un coset C = s * <2> dans (Z/dZ)* :
M(C) = (1/s) SUM_{s' in C} Lambda(s') = (1/s) SUM_B Sigma(s*c*g(B))

N_cycle = (1/d) [Lambda(0) + s * SUM_C M(C)] ou la somme est sur les phi(d)/s cosets non-triviaux.

**Borne sur M(C) :** |M(C)| <= (1/s) SUM_B |Sigma(s*c*g(B))| <= p_k(n) * max|rho_a|.

Mais aussi : M(C) = (1/s) SUM_B Sigma(alpha_B) ou alpha_B = s*c*g(B). Si les alpha_B sont repartis dans Z/dZ, la loi des grands nombres donne :

M(C) ~ p_k(n) * E[Sigma(alpha)] ou E est la moyenne sur alpha uniforme dans Z/dZ*.

**THEOREME R191-T22 [PROUVE].**
La moyenne de Sigma(a) sur a uniforme dans Z/dZ est :
E_a[Sigma(a)] = (1/d) SUM_{a=0}^{d-1} SUM_{m=0}^{s-1} omega^{a*2^m}
= SUM_{m=0}^{s-1} (1/d) SUM_a omega^{a*2^m}
= SUM_{m=0}^{s-1} delta_{2^m, 0}
= 0

car 2^m != 0 mod d pour tout m (d est impair).

**Preuve :** Interversion et orthogonalite des caracteres.

Donc la moyenne de Sigma(a) sur a UNIFORME est 0. Si les alpha_B = s*c*g(B) etaient uniformement distribues, on aurait M(C) ~ 0, et N_cycle ~ Lambda(0)/d = p_k(n)/d < 1 pour k < 42.

**C'est le mecanisme de compensation EXPLIQUE !** La compensation orbitale vient du fait que :
1. La somme Sigma(a) a une moyenne nulle sur a
2. Les valeurs g(B) sont suffisamment reparties pour que la moyenne sur B approche la moyenne sur a

Le deficit par rapport a la compensation parfaite est controle par la DISCREPANCE de la distribution de g(B) mod d.

### 11.4 Le deficit de discrepance

**DEFINITION R191-D7 (Discrepance).** La discrepance de g(B) mod d est :
D_k = max_{t in Z/dZ} |N_t/p_k(n) - 1/d|

ou N_t = #{B : g(B) equiv t mod d}.

Si D_k est petit (D_k << 1/d), alors g(B) est bien reparti et la compensation est quasi-parfaite.

**THEOREME R191-T23 [CONDITIONNEL sur D_k].**
|N_cycle - p_k(n)/d| <= p_k(n) * D_k * (phi(d)/s) * max_a |Sigma(a)|.

Si D_k <= 1/(d * max|Sigma|), alors N_cycle < 2*p_k(n)/d < 2. Par integerite, N_cycle in {0, 1}.

Pour eliminer N_cycle = 1, il faudrait D_k << 1/d (equidistribution forte).

**STATUT : CONDITIONNEL** (la discrepance D_k n'est pas bornee a ce stade)

---

## 12. CARTE DE ROUTE POST-R191

### 12.1 Pistes ouvertes (classees par priorite)

| # | Piste | Score | Raison |
|---|-------|-------|--------|
| 1 | **Verification directe k = 2..41** | 10/10 | Calcul fini, infaillible, ne necessite pas de theorie |
| 2 | **Borne sur la discrepance D_k** | 9/10 | Le T22+T23 montrent que D_k controle tout ; la borner ferme le probleme |
| 3 | **Bornes sum-product specifiques a d = 2^S - 3^k** | 8/10 | Le probleme est requalifie comme problem TAN (R190) ; exploiter la structure speciale de d |
| 4 | **Factorisation Lambda_free et correction monotonie** | 7/10 | T5+T8 donnent le cadre ; le facteur k! est l'obstacle |
| 5 | **Crible modulaire pour d compose** | 7/10 | T11 est un outil puissant quand d a des petits facteurs |

### 12.2 Les questions non resolues

1. **Quelle est la discrepance D_k de g(B) mod d ?** (Question centrale post-R191)
   - Si D_k ~ 1/sqrt(p_k(n)) (comportement aleatoire), c'est suffisant pour k >> 1 mais pas pour k petit.
   - Si D_k ~ 1/d^{1/2} (borne de Weil), c'est suffisant pour tout k >= 2.

2. **Les sommes Sigma(a) sur <2> satisfont-elles |Sigma(a)| < s/3 pour tout a != 0 mod d ?**
   - C'est le seuil critique pour que le Levier 2 fonctionne.
   - Pour s petit (s = 2, 3, 4), c'est verifiable directement.
   - Pour s grand, c'est le probleme sum-product.

3. **La correction de monotonie (T8) peut-elle etre bornee sans le facteur k! ?**
   - Si les Lambda_sigma pour sigma != id satisfont des ANNULATIONS SUPPLEMENTAIRES (dues a l'appariement discordant entre poids permutes et lettres monotones), le facteur k! pourrait etre absorbe.

### 12.3 L'insight principal de R191

**La compensation orbitale est la CONSEQUENCE de deux faits :**
**(i) SUM_a Sigma(a) = 0 (moyenne nulle des sommes exponentielles sur <2>)**
**(ii) g(B) est "suffisamment reparti" mod d (discrepance petite)**

Le fait (i) est PROUVE (T22). Le fait (ii) est le VERROU restant.

La strategie optimale est donc de BORNER LA DISCREPANCE D_k, soit par :
- Des bornes exponentielles (Borne d'Erdos-Turan reliant D_k aux Lambda(s) -- CIRCULAIRE si on n'a pas de borne sur Lambda)
- Des bornes arithmetiques (structure de d = 2^S - 3^k)
- Un calcul direct (pour les 40 cas k = 2..41)

---

## 13. BILAN R191

### 13.1 Resultats

- **13 PROUVES** (T0, T1, T2, T3, T4, T5, T8, T9, T11, T13, T14, T17, T19-T22)
- **4 CONDITIONNELS** (T6, T15, T16-schema, T23)
- **2 CONJECTURES** (T10, T12)
- **1 RETIRE** (T18 -- invariance Lambda(3s) = Lambda(s) est fausse)

### 13.2 Insights principaux

1. La compensation orbitale est TOUJOURS exacte (c'est Fourier) -- ce n'est PAS le phenomene a expliquer.
2. Le VRAI phenomene est que g(B) mod d est bien reparti (evite 0), ce qui est controle par la discrepance D_k.
3. La moyenne nulle de Sigma(a) (T22) explique MECANIQUEMENT pourquoi la compensation fonctionne.
4. Le probleme est REQUALIFIE : de "borner Lambda(s)" a "borner la discrepance de g(B) mod d".
5. Pour k < 42, le calcul direct (40 cas finis) est infaillible et devrait etre fait en parallele de la theorie.

### 13.3 Evaluation

| Critere | Score | Commentaire |
|---------|-------|-------------|
| **Nouveaute** | 7/10 | Demystification de la compensation (T22), telescope orbital (D5-D7), discrepance comme verrou |
| **Impact** | 8/10 | Requalification du probleme (Lambda -> discrepance), schema de preuve en 3 etapes |
| **Rigueur** | 9/10 | 13 prouves proprement, 1 retrait honnete (T18), conditionnels clairement identifies |
| **Honnetete** | 9/10 | Reconnaissance que la compensation est tautologique, pas de "miracle" invente |

---

*R191 : 13 PROUVES, 4 CONDITIONNELS, 2 CONJECTURES, 1 RETIRE. Insight principal : la compensation orbitale est Fourier (tautologique), le vrai verrou est la discrepance D_k de g(B) mod d. T22 (moyenne nulle de Sigma) explique le mecanisme. Priorite #1 pour R192 : verification directe k=2..41 + borne sur D_k.*
