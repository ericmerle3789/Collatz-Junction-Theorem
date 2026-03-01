# Phase 23b — Assemblage : Tentative de Construction de LA FORMULE
# Date : 28 fevrier 2026
# Auteur : Eric Merle (assiste par Claude, directeur de recherche)

---

## 0. Objectif

Assembler TOUS les ingredients disponibles pour construire un SEUL theoreme
prouvant H. Pas d'inventaire — de la CONSTRUCTION.

---

## 1. La Factorisation-Cle : T* en produit

### 1.1. Relaxation de la contrainte de monotonie

La somme avec contrainte d'ordre :

  T(t) = sum_{0=a_0 < a_1 < ... < a_{k-1} <= S-1} e(t * corrSum(A) / p)

La somme SANS contrainte (k-uplets quelconques dans {0,...,S-1}^k) :

  T*(t) = sum_{(a_0,...,a_{k-1}) in {0,...,S-1}^k} e(t * sum_i 3^{k-1-i} * 2^{a_i} / p)

T* FACTORISE en produit :

  T*(t) = prod_{j=0}^{k-1} G(t * 3^j mod p)

ou G(u) = sum_{a=0}^{S-1} e(u * 2^a / p) est la somme de Gauss geometrique.

### 1.2. Les arguments t*3^j sont equidistribues

Posons omega = 2/3 mod p. Les arguments de G dans T* sont t*3^j pour j=0,...,k-1.
Si ord_p(3) = T_3, les k arguments sont k elements du sous-groupe <3> de F_p*,
translated par t.

Pour p typique divisant d = 2^S - 3^k : ord_p(3) est grand (souvent p-1).
Les k points {t*3^j mod p : j=0,...,k-1} sont equidistribues dans F_p*
(discrepance D_k = O(k*log p / (p-1) + 1/k) = O(log^2 p / p) << 1).

### 1.3. Borne sur |T*| par Parseval

Par equidistribution des arguments :

  (1/k) sum_j |G(t*3^j)|^2 ~= (1/(p-1)) sum_{u != 0} |G(u)|^2

Par Parseval sur G :

  sum_{u=0}^{p-1} |G(u)|^2 = p * S    (car les 2^a sont distincts si ord_p(2) >= S)

Donc (1/(p-1)) sum_{u != 0} |G(u)|^2 = (pS - S^2)/(p-1) ~= S  (pour p >> S).

Par Jensen (concavite du log) :

  log|T*| = sum_j log|G(t*3^j)| <= k * log((1/k) sum_j |G(t*3^j)|)

Et par Cauchy-Schwarz : (1/k)sum|G_j| <= sqrt((1/k)sum|G_j|^2) ~= sqrt(S).

Donc :   |T*(t)| <= (sqrt(S))^k = S^{k/2}

Comparaison : |T*(t)| <= S^{k/2} tandis que la borne triviale est S^k.
C'est un gain de RACINE CARREE — le gain de Parseval.

---

## 2. Passage de T* a T : l'obstacle central

### 2.1. Pourquoi T* != k! * T

T* somme sur TOUS les k-uplets. T somme sur les k-uplets STRICTEMENT CROISSANTS.
Si la fonction e(t*corrSum/p) etait SYMETRIQUE en les a_i, on aurait
T = T*/k! (chaque sous-ensemble de taille k contribue k! fois).

MAIS : les poids 3^{k-1-i} dependent de la POSITION i, pas seulement de la
VALEUR a_i. Donc le poids change quand on permute les a_i.

On a : T*(t) = sum_{sigma in S_k} T_sigma(t)

ou T_sigma(t) = sum_{a_0<...<a_{k-1}} prod_i e(t * 3^{k-1-sigma(i)} * 2^{a_i} / p).

T(t) = T_id(t) (permutation identite).

### 2.2. Borne par le triangle

|T(t)| = |T_id(t)| <= ... on ne peut PAS borner T par T*/k! car les phases
different. Le mieux qu'on puisse dire :

  |T(t)| <= C = C(S-1, k-1)   (borne triviale)

Le passage T* -> T est le MUR. La factorisation en produit est PERDUE
des qu'on impose l'ordre.

### 2.3. Tentative via fonctions de Schur

Posons x_a = e(t*2^a/p) pour a = 0,...,S-1. Alors :

  T(t) = sum_{I in C(S,k)} prod_{(a,i) in I sorted} x_a^{3^{k-1-rank(a)}}

Avec les exposants lambda = (3^{k-1}, 3^{k-2}, ..., 3, 1), c'est une somme
de type "fonction de Schur generalisee" s_lambda(x_0,...,x_{S-1}).

Pour la partition standard rho = (k-1, k-2, ..., 1, 0), la fonction de Schur
est s_rho = det(x_a^{rho_j}) / det(x_a^{j}). Mais nos exposants
lambda = (3^{k-1},...,1) ne sont PAS de la forme rho + decalage, donc
AUCUNE formule determinantale connue ne s'applique.

**Verdict** : La structure de Schur est la BONNE structure, mais les
exposants lacunaires (puissances de 3) empechent toute factorisation.

---

## 3. Approche Alternative : Le Theoreme 22.2 (CRT multiplicatif)

### 3.1. L'idee : eviter la borne sur |T(t)|

Le Theoreme 22.2 (Phase 22) contourne le probleme de Fourier :

Si pour chaque premier p_i | d :
  N_0(p_i) / C <= (1 + epsilon) / p_i

et si (C/d) * (1+epsilon)^m < 1, alors N_0(d) = 0.

Autrement dit : il SUFFIT de prouver la quasi-uniformite de corrSum mod p
pour chaque premier, SANS borne pointwise sur |T(t)|.

### 3.2. Ce qu'il faut prouver (Conjecture 22.3 reformulee)

Pour tout k >= 18 et tout premier p | d(k) :

  |N_0(p) - C/p| <= epsilon_k * C/p

avec epsilon_k -> 0 quand k -> infini, et assez petit pour que
(C/d)*(1+epsilon)^m < 1.

Phase 22 montre epsilon_k <= 0.07 pour k=3..17 et epsilon_k <= 0.03 pour k >= 18.
Le nombre de facteurs premiers m de d(k) est m = O(log d / log log d) = O(S).

Il faut : (1+epsilon)^m < d/C = d/C. Avec d/C >= 1/0.937^k (Phase 22) :
  m * ln(1+epsilon) < k * ln(1/0.937) = 0.065 * k
  m * epsilon < 0.065 * k  (pour petit epsilon)

Avec m = O(S) = O(1.585k) : epsilon < 0.065/1.585 = 0.041.

**CONDITION** : epsilon < 4.1% suffit. Phase 22 mesure epsilon < 3% pour k >= 18.

### 3.3. Ce qui manque pour une preuve

Il manque la preuve que epsilon_k < 4.1% pour TOUT k >= 18 et TOUT p | d.

C'est une forme AFFAIBLIE de la Conjecture 22.3 :
au lieu de |N_0(p) - C/p| <= C * p^{-1/2-delta}, on ne demande que
|N_0(p) - C/p| <= 0.041 * C/p.

En termes de sommes exponentielles (via Fourier) :
  |(1/p) sum_{t=1}^{p-1} T(t)| <= 0.041 * C/p
  |sum_{t=1}^{p-1} T(t)| <= 0.041 * C

C'est une borne sur la SOMME des T(t), pas sur chaque |T(t)| individuellement.

---

## 4. La Tentative d'Assemblage : LE THEOREME

### 4.1. Ingredients disponibles

(A) Parseval : sum_{t=1}^{p-1} |T(t)|^2 = p * sum_r f(r)^2 - C^2

(B) Factorisation : T*(t) = prod_j G(t*3^j), |T*| <= S^{k/2}

(C) Quasi-uniformite empirique : f(r) = N_r(p) satisfait sum f(r)^2 ~= C^2/p + C
    (quasi-injection quand p > C)

(D) Trou spectral : Delta >= 0.48 (Markov chain, Phase 22)

(E) Decroissance C/d ~= 0.937^k (Theoreme 1)

(F) CRT multiplicatif : N_0(d) <= C * prod_i N_0(p_i)/C (Theoreme 22.2)

### 4.2. Assemblage

**Theoreme (Tentative).** Pour tout k >= 18, N_0(d(k)) = 0.

*Preuve (esquisse, avec gap identifie) :*

Etape 1. Par le Theoreme 1, C/d < 1, donc C < d.

Etape 2. Par le Theoreme 22.2, il suffit de montrer que pour chaque
premier p | d : N_0(p)/C <= (1+epsilon)/p avec epsilon < 0.041.

Etape 3. Par la formule de Fourier :
  N_0(p) = C/p + (1/p) * sum_{t=1}^{p-1} T(t)

Donc N_0(p)/C - 1/p = (1/(pC)) * sum_{t=1}^{p-1} T(t).

Il faut : |sum T(t)| <= 0.041 * C.

Etape 4. Par Cauchy-Schwarz :
  |sum_{t=1}^{p-1} T(t)|^2 <= (p-1) * sum |T(t)|^2

Etape 5. Par Parseval :
  sum |T(t)|^2 = p * sum_r f(r)^2 - C^2

Etape 6. **[GAP]** Il faut borner sum_r f(r)^2.

  Si f est quasi-uniforme : sum f(r)^2 ~= C^2/p + C  (p > C)
  Alors : sum |T(t)|^2 ~= p*(C^2/p + C) - C^2 = pC
  Et : |sum T(t)| <= sqrt((p-1)*pC) ~= p * sqrt(C)
  Donc : |sum T(t)| / C ~= p * sqrt(C) / C = p / sqrt(C)

  Pour epsilon < 0.041 : p/sqrt(C) < 0.041, soit p < 0.041*sqrt(C).

  Avec C ~ 2^{1.5k} : sqrt(C) ~ 2^{0.75k}, et p <= d ~ 2^{1.585k}.
  Condition : 2^{1.585k} < 0.041 * 2^{0.75k}, soit 2^{0.835k} < 0.041.
  C'est FAUX pour tout k >= 1.

**Le Cauchy-Schwarz + Parseval donne une borne trop faible d'un facteur 2^{0.835k}.**

### 4.3. Diagnostic du gap

La BARRIERE DE LA RACINE CARREE :

| Borne necessaire | Borne Parseval/CS | Ratio |
|------------------|--------------------|-------|
| |sum T(t)| <= 0.041*C | |sum T(t)| <= p*sqrt(C) | p*sqrt(C)/(0.041*C) = 24*p/sqrt(C) |

Pour k = 68 : p ~ 2^{108}, C ~ 2^{102}, ratio ~ 24*2^{108}/2^{51} ~ 2^{62}.

Le Cauchy-Schwarz est trop faible de 62 ordres de grandeur binaires.

Ceci est la **barriere sqrt** : les methodes du second moment (Parseval + CS)
ne peuvent pas detecter l'exclusion de 0 car elles ne "voient" que la
variance de f, pas la position de f(0).

---

## 5. Au-Dela de Parseval : Quatrieme Moment

### 5.1. L'idee

Au lieu du second moment, utiliser le QUATRIEME moment :

  sum_{t=0}^{p-1} |T(t)|^4 = p * sum_r f(r)^3 * ... non.

En fait : sum |T(t)|^4 = p^2 * #{(A,B,C,D) : corrSum(A)+corrSum(B) = corrSum(C)+corrSum(D) mod p}

C'est le nombre de "collisions additives" de corrSum. Si corrSum est bien distribue,
cette quantite est ~= C^4/p + C^2 (terme principal + diagonale).

### 5.2. L'inegalite de Holder

Au lieu de Cauchy-Schwarz, utilisons Holder avec exposant 4 :

  |sum T(t)| <= (p-1)^{3/4} * (sum |T(t)|^4)^{1/4}

Et si sum |T(t)|^4 ~= C^4/p + C^2 :

  |sum T(t)| <= p^{3/4} * (C^4/p + C^2)^{1/4}
             ~= p^{3/4} * C * (C^2/p + 1)^{1/4}

Pour p > C (regime cristallin) : C^2/p < C < p, donc :
  ~= p^{3/4} * C * (C/p)^{1/2}     (si C^2/p domine)
  = p^{3/4} * C^{3/2} / p^{1/2}
  = p^{1/4} * C^{3/2}

Pour epsilon < 0.041 : p^{1/4} * C^{3/2} / C < 0.041, soit p^{1/4} * C^{1/2} < 0.041.
Avec p ~ 2^{1.585k}, C ~ 2^{1.5k} :
  2^{0.396k} * 2^{0.75k} = 2^{1.146k} < 0.041
TOUJOURS FAUX.

Le quatrieme moment ne suffit pas non plus. Le gain est marginal.

### 5.3. Limite des moments

Pour que le r-ieme moment donne une borne utile, il faudrait :

  p^{1-1/r} * C^{1-1/r} < epsilon * C
  p^{1-1/r} < epsilon * C^{1/r}

Avec p ~ C^{1.06} (ratio typique) :
  C^{1.06*(1-1/r)} < epsilon * C^{1/r}
  C^{1.06 - 1.06/r - 1/r} < epsilon
  C^{1.06 - 2.06/r} < epsilon

Pour que l'exposant soit negatif : 1.06 - 2.06/r < 0, soit r < 2.06/1.06 = 1.94.

Il faut r < 2 — mais le MINIMUM est r = 1 (pas de moment, borne triviale) ou
r = 2 (Parseval). **Pour r >= 2, l'exposant est TOUJOURS positif** car
1.06 - 2.06/r >= 1.06 - 1.03 = 0.03 > 0.

CONCLUSION : **Aucune methode des moments (Parseval, Holder, hyper-norme)
ne peut prouver N_0(p) = 0 dans le regime p ~ C^{1+eta} avec eta = 0.06.**

La barriere est FONDAMENTALE : elle vient du fait que p et C sont du meme
ordre de grandeur (a une puissance 0.06 pres).

---

## 6. La Voie de Sortie : Argument Non-Fourier

### 6.1. Ce que la barriere sqrt signifie

La barriere sqrt dit : ON NE PEUT PAS prouver N_0(p) = 0 en bornant |T(t)|
ou ses moments. La raison est que p ~ C^{1.06}, et les bornes de Fourier
generiques ne peuvent pas distinguer f(0) = 0 de f(0) = C/p quand C/p ~ 1.

Il faut un argument STRUCTUREL, pas un argument de taille.

### 6.2. Retour au mecanisme de troncature (Phase 22)

Le mecanisme qui FONCTIONNE computationnellement est la TRONCATURE :
quand omega_2(p) > S, les compositions sont contraintes a utiliser un
sous-ensemble STRICT de <2> mod p.

Formalisons : soit H = {2^0, 2^1, ..., 2^{S-1}} mod p. Si omega_2(p) > S,
alors |H| = S < omega_2(p) = |<2>|. L'image de corrSum mod p est un
sous-ensemble de :

  Im(corrSum) = {sum_i 3^{k-1-i} * h_i : h_i in H, h_0=1, h_i distincts, ordonnes}

C'est un sous-ensemble de la somme de Minkowski 3^{k-1}*H + 3^{k-2}*H + ... + H
(avec contrainte d'ordre et h_0 = 1).

### 6.3. Borne sur |Im(corrSum)|

La somme de Minkowski sans contrainte a |sum 3^i*H| <= min(p, S^k) = min(p, S^k).
Avec la contrainte d'ordre et d'injectivite : |Im| <= C = C(S-1, k-1).

Pour que 0 ne soit PAS dans Im, il suffit que |Im| < p, soit C < p.
C'est DEJA garanti par le Lemme A' (existence de p > C).

Mais |Im| < p ne garantit PAS 0 notin Im. Il faut savoir QUELS residus
sont dans Im.

### 6.4. L'argument de Steiner generalise

Observation cruciale de la Phase 22 (Section 2.1) : pour les premiers p
avec omega_2(p) >> S, le "grand premier excluant", on a TOUJOURS N_0(p) = 0.

Pourquoi ? Parce que les elements de H = {2^0,...,2^{S-1}} mod p forment un
ARC de la progression geometrique <2>. Le rapport S/omega_2(p) << 1 signifie
que cet arc est une PETITE FRACTION du cercle.

La somme de Horner sum 3^i * h_i avec h_i dans cet arc est une combinaison
lineaire a COEFFICIENTS POSITIFS (3^i > 0) de valeurs dans un arc COURT.
Le resultat est confine dans un sous-ensemble "convexe" de F_p.

Si l'arc est assez court (S/omega < 1/k environ), le resultat ne peut pas
envelopper tout F_p, et certains residus (dont 0) sont exclus.

### 6.5. Tentative de formalisation (ARGUMENT CONVEXE)

**Proposition (tentative).** Soit p premier, omega = ord_p(2), et S < omega.
Identifions F_p avec {0, 1, ..., p-1}. Si on ordonne les elements de H par
la progression geometrique 2^0 < 2^1 < ... < 2^{S-1} dans Z, leur reduction
mod p forme un arc de <2> dans F_p*.

Pour les sommes de Horner :
  sigma = sum_{i=0}^{k-1} 3^{k-1-i} * 2^{a_i}     (dans Z)

AVANT reduction mod p, sigma est un entier positif dans l'intervalle :
  [sigma_min, sigma_max] = [3^k - 2^k, 2^{S-k}*(3^k - 2^k)]

Et d = 2^S - 3^k divise sigma si et seulement si sigma = n_0 * d pour un entier n_0.

Le nombre de multiples de d dans [sigma_min, sigma_max] est :
  |{n_0 : sigma_min <= n_0*d <= sigma_max}|
  = floor(sigma_max/d) - ceil(sigma_min/d) + 1

Calculons :
  sigma_min/d = (3^k - 2^k)/(2^S - 3^k)

Notons alpha = {k*log_2(3)} la partie fractionnaire. Alors :
  2^S = 2^{ceil(k*log_2(3))} = 3^k * 2^alpha  (a des termes d'ordre inferieur)
  d = 3^k*(2^alpha - 1)
  sigma_min = 3^k*(1 - (2/3)^k) ~= 3^k
  sigma_min/d ~= 1/(2^alpha - 1)

Pour alpha = 1/2 (typique) : sigma_min/d ~= 1/(sqrt(2)-1) ~= 2.41.
Pour alpha proche de 0 (convergents) : sigma_min/d -> +infini.

sigma_max/d = 2^{S-k}*(3^k - 2^k)/(2^S - 3^k) ~= 2^{S-k}*3^k/d ~= 2^{S-k}/(2^alpha - 1)

Le nombre de multiples de d dans [sigma_min, sigma_max] est ~= sigma_max/d - sigma_min/d
= (2^{S-k} - 1)/(2^alpha - 1) ~= 2^{S-k}/(2^alpha - 1).

Pour k = 20 : S = 32, 2^{S-k} = 2^12 = 4096, alpha ~= 0.7. Nombre ~= 4096/0.62 ~= 6606.
Et C(31,19) = 44352. Donc C/nb_multiples ~= 6.7.

Chaque multiple de d correspond a un TARGET n_0. Il faut que AUCUNE composition
n'atteigne AUCUN de ces targets. C'est plus facile quand il y a MOINS de targets
(grands k) et MOINS de compositions par target (C/(nb_multiples) petit).

### 6.6. L'argument combinatoire

Reformulons : N_0(d) = #{A : corrSum(A) = n_0 * d, n_0 entier} = sum_{n_0} f(n_0*d)

ou f(sigma) = 1 si sigma = corrSum(A) pour un A, 0 sinon (modele injective)
ou f(sigma) = #{A : corrSum(A) = sigma} (modele general).

Le nombre de n_0 possibles est N_targets ~= 2^{S-k}/(2^alpha - 1).
Pour chaque target sigma = n_0*d, la "probabilite" que f(sigma) > 0 est
~= C/Range ou Range = sigma_max - sigma_min ~= 2^{S-k}*3^k.

Donc : E[N_0(d)] ~= N_targets * C / Range ~= C / d = C/d.

Pour k >= 18 : C/d < 1, donc E[N_0] < 1. Ceci est l'argument HEURISTIQUE
standard. Mais pour le rendre RIGOUREUX, il faut controler les correlations.

---

## 7. L'Ingredient Manquant Unique : Anti-Concentration Structurelle

### 7.1. Reformulation finale

Apres assemblage complet, le probleme se reduit a :

> **Prouver que corrSum(A) ne peut pas etre un multiple de d(k) pour A in Comp(S,k).**

Equivalemment :

> **Pour tout entier n_0 >= 1, l'equation**
>
>   3^{k-1} * 2^0 + 3^{k-2} * 2^{a_1} + ... + 2^{a_{k-1}} = n_0 * (2^S - 3^k)
>
> **n'a pas de solution avec 0 < a_1 < ... < a_{k-1} <= S-1.**

Rearrangeons :

  3^{k-1} + sum_{i=1}^{k-1} 3^{k-1-i} * 2^{a_i} = n_0 * 2^S - n_0 * 3^k

  sum_{i=0}^{k-1} 3^{k-1-i} * 2^{a_i} + n_0 * 3^k = n_0 * 2^S

  3^k * n_0 + sum_{i=0}^{k-1} 3^{k-1-i} * 2^{a_i} = n_0 * 2^S

Factorisons le cote gauche :
  3^{k-1} * (3*n_0 + 2^{a_0}) + 3^{k-2} * 2^{a_1} + ... = n_0 * 2^S

Avec a_0 = 0 : 3*n_0 + 1 est le "premier coefficient effectif".

C'est l'equation de STEINER : la somme de Horner egale n_0*d.

### 7.2. L'anti-concentration par valuation 2-adique

Idee : examiner l'equation mod des puissances de 2.

corrSum(A) = sum 3^{k-1-i} * 2^{a_i} = 3^{k-1} + termes avec facteur 2^{a_1} ou plus.

v_2(corrSum(A)) = 0  (car le premier terme 3^{k-1} est IMPAIR).

Donc corrSum(A) est TOUJOURS IMPAIR.

Et v_2(d) = v_2(2^S - 3^k) = v_2(2^S - 3^k).
Si k est impair : 3^k est impair et ≡ 3 mod 4. 2^S ≡ 0 mod 4 (S >= 2).
  Donc d ≡ -3 ≡ 1 mod 4. v_2(d) = 0. d est impair.
Si k est pair : 3^k ≡ 1 mod 8 (car 3^2 = 9 ≡ 1). 2^S ≡ 0 mod 8.
  Donc d ≡ -1 mod 8. v_2(d) = 0. d est impair.

Conclusion : d est TOUJOURS impair, et corrSum est TOUJOURS impair.
Pas de contradiction par valuation 2-adique.

### 7.3. L'anti-concentration par valuation 3-adique

v_3(corrSum(A)) : le premier terme est 3^{k-1} (v_3 = k-1).
Le deuxieme terme est 3^{k-2} * 2^{a_1} (v_3 = k-2).
Par la formule de la somme : v_3(corrSum) = k-2 (car le terme de plus
petite valuation 3-adique DOMINE pour k >= 2).

Wait — c'est plus subtil. corrSum = 3^{k-1} + 3^{k-2}*2^{a_1} + ... + 2^{a_{k-1}}.
Le dernier terme a v_3 = 0. Donc v_3(corrSum) = 0 (le dernier terme domine).

Sauf si 2^{a_{k-1}} ≡ 0 mod 3, ce qui est impossible (2^a est JAMAIS multiple de 3).

Donc v_3(corrSum) = 0, i.e., 3 ne divise JAMAIS corrSum(A).

Et v_3(d) = v_3(2^S - 3^k) = 0 sauf si 2^S ≡ 0 mod 3, impossible.
Donc v_3(d) = 0 (car 2^S ≡ (-1)^S mod 3, et 3^k ≡ 0 mod 3, donc d ≡ (-1)^S mod 3).
Si S pair : d ≡ 1 mod 3. Si S impair : d ≡ -1 ≡ 2 mod 3.
Dans les deux cas v_3(d) = 0.

Pas de contradiction par valuation 3-adique non plus.

### 7.4. Congruence mod petits nombres

corrSum(A) mod 2 : = 1 (toujours impair) ✓ (d impair aussi)
corrSum(A) mod 3 : = 2^{a_{k-1}} mod 3 = (-1)^{a_{k-1}} mod 3 (soit 1 ou 2)

d mod 3 : = (-1)^S mod 3 (soit 1 ou 2).

Pour corrSum = n_0*d mod 3 : (-1)^{a_{k-1}} ≡ n_0*(-1)^S mod 3.
Ce n'est pas impossible (il existe des n_0 satisfaisant ceci).

Les petites congruences ne donnent pas de contradiction.

---

## 8. Verdict d'Assemblage

### 8.1. Ce qui a ete tente

| Approche | Resultat | Pourquoi ca echoue |
|----------|----------|-------------------|
| Parseval + CS (2e moment) | |sum T| <= p*sqrt(C) | Trop faible de 2^{62} pour k=68 |
| Holder (4e moment) | Gain marginal | Meme barriere fondamentale |
| Moments d'ordre r | Impossible pour r >= 2 | Exposant 1.06 - 2.06/r > 0 |
| Factorisation T* = prod G | S^{k/2} | Non transferable a T (poids asymetriques) |
| Fonctions de Schur | Structure correcte | Exposants lacunaires (3^i) sans formule |
| Valuation 2-adique | v_2(corrSum) = 0, v_2(d) = 0 | Pas de contradiction |
| Valuation 3-adique | v_3(corrSum) = 0, v_3(d) = 0 | Pas de contradiction |
| Congruences mod petits | Pas de contradiction | Pas assez de contraintes |
| Argument convexe/arc | Intuition correcte | Pas formalisable (F_p non ordonne) |
| CRT multiplicatif | Reduit a epsilon < 4.1% | Mais prouver epsilon < 4.1% = prouver H |

### 8.2. La barriere fondamentale

**THEOREME NEGATIF (informel).** Soit E la classe des methodes utilisant :
- L'inversion de Fourier sur F_p
- Les normes L^r de T(t) pour r >= 2
- La factorisation de T* en produit de sommes geometriques
- Les congruences mod petites puissances de 2 et 3
- Le theoreme des restes chinois multiplicatif

Alors AUCUNE methode dans E ne peut prouver N_0(p) = 0 dans le regime
p ~ C^{1+eta} avec eta < 1 (ce qui est TOUJOURS le cas pour p | d(k)).

Raison : ces methodes donnent au mieux une borne |N_0(p) - C/p| >= C^{1-1/r}/p^{1/r},
qui n'est < C/p que si C^{1-1/r} < C*p^{-1+1/r}, soit C < p^{r/(r-1)},
soit p > C^{1-1/r}. Pour r -> infini : p > C. Mais dans le regime
p ~ C^{1.06}, ceci requiert r -> infini, et la convergence est trop lente.

### 8.3. Ce qui est necessaire

Il faut un argument qui exploite la STRUCTURE SPECIFIQUE de corrSum, pas
seulement ses proprietes de taille. Concretement :

1. **La relation 2^S ≡ 3^k mod p** — la congruence definissant d
2. **La monotonie des exposants** — la contrainte a_0 < a_1 < ... < a_{k-1}
3. **La lacunarite des poids** — les coefficients sont 3^0, 3^1, ..., 3^{k-1}

Ces trois proprietes ensemble creent une RIGIDITE structurelle que
les arguments de Fourier generiques ne peuvent pas capturer.

---

## 9. Formulation du Probleme Ouvert Precis

### 9.1. Enonce minimal

**Probleme (Sommes de Horner Lacunaires).** Soit p premier, et soit
lambda = 2/3 mod p. Pour S, k entiers avec 1 <= k <= S et 2^S ≡ 3^k mod p,
montrer que :

  sum_{j=0}^{k-1} lambda^j * 2^{g_j} ≠ 0    (dans F_p)

pour tout vecteur de gaps 0 = g_0 <= g_1 <= ... <= g_{k-1} <= S-k.

### 9.2. Reformulation geometrique

L'ensemble des vecteurs (g_0,...,g_{k-1}) avec 0 = g_0 <= ... <= g_{k-1} <= L
(ou L = S-k) est un SIMPLEXE ENTIER de dimension k-1.

La fonction phi(g) = sum lambda^j * 2^{g_j} est une application de ce simplexe
dans F_p.

Le probleme est : montrer que 0 notin Im(phi).

La taille du simplexe est C = C(L+k-1, k-1) = C(S-1, k-1) ~ 2^{0.95S}.
La taille de F_p est p > C (pour le bon premier).

La "fraction" C/p < 1. Mais montrer que 0 specifiquement est evite
requiert un argument non-generique.

### 9.3. Propriete speciale de 0

Pourquoi 0 est-il special ? Parce que phi(g) = 0 equivaut a
  sum 3^{k-1-j} * 2^{j+g_j} ≡ 0 mod p

Avec 2^S ≡ 3^k mod p, le "0" est relie a la relation fondamentale entre 2 et 3.
C'est cette relation qui rend 0 special parmi les residus de F_p.

Un argument exploitant cette specificite devrait utiliser la structure
ARITHMETIQUE de p (le fait que p | 2^S - 3^k), pas seulement p comme
premier generique.

---

## 10. Conclusion : LA FORMULE et l'Etat des Lieux

### 10.1. LA FORMULE (forme conjecturale)

La formule universelle, si elle existe, est :

  **Pour tout k >= 3, pour tout (g_0,...,g_{k-1}) dans le simplexe
  {0 <= g_0 <= ... <= g_{k-1} <= S-k} :**

  sum_{j=0}^{k-1} (2/3)^j * 2^{g_j} ≢ 0    (mod p)

  **pour au moins un premier p | (2^S - 3^k) avec p > C(S-1,k-1).**

### 10.2. Les 3 niveaux de certitude

| Niveau | Enonce | Statut |
|--------|--------|--------|
| **Verifie** | N_0(d) = 0 pour k = 3..17 | PROUVE (exhaustif) |
| **Tres probable** | N_0(d) = 0 pour k = 18..41 | MC 10^6, 0 hits |
| **Conjectural** | N_0(d) = 0 pour tout k >= 3 | Conjecture H |

### 10.3. Ce qui bloque

**UN SEUL obstacle** : la BARRIERE DE LA RACINE CARREE.

Toutes les methodes spectrales/Fourier/moments donnent au mieux
|N_0(p) - C/p| = O(sqrt(C)), ce qui ne suffit pas quand C/p ~ 1.

La traversee de cette barriere requiert un argument STRUCTUREL
exploitant la triple relation (2^S ≡ 3^k mod p, monotonie, lacunarite).

Cet argument n'existe pas dans la litterature de 2026.
Sa decouverte constituerait une avancee majeure en theorie analytique
des nombres, comparable aux percees de Bourgain (2005) et
Lindenstrauss-Varju (2016).

### 10.4. En une phrase

> **La barriere de la racine carree interdit toute preuve de H par
> methodes de Fourier generiques. Il faut un argument structurel
> exploitant la triple contrainte (congruence 2^S ≡ 3^k, monotonie,
> poids lacunaires 3^j), et cet argument n'existe pas encore.**

---

## Appendice : Constantes numeriques cles

| Symbole | Valeur | Signification |
|---------|--------|---------------|
| gamma | 0.05004... | Deficit entropique |
| C/d | ~0.937^k | Decroissance exp. |
| Delta | >= 0.48 | Trou spectral min |
| epsilon_CRT | < 0.041 | Seuil pour Thm 22.2 |
| p/C | ~ C^{0.06} | Ratio premier/compositions |
| Barriere | 2^{0.835k} | Facteur manquant (CS vs besoin) |
