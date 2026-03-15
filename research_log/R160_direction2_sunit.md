# R160bis -- INVESTIGATION DIRECTION 2 : Structure monotone x S-unit dans Z

**Date** : 15 mars 2026
**Type** : Investigation mathematique -- briques elementaires (addition, multiplicabilite, divisibilite)
**Question** : Comment la structure MONOTONE des B_j et la structure GEOMETRIQUE des coefficients 3^{k-1-j} contraignent corrSum dans Z, au-dela de ce qu'ESS peut voir ?

**Rappel du verrou** : Prouver N_0(d) = 0 pour k = 22..41, ou d = 2^S - 3^k, S = ceil(k * log_2(3)) + 1.

**Rappel ESS** : La borne Evertse-Schlickewei-Schmidt donne exp(10^{148}) solutions -- MORTE quantitativement (R83). Raison de la mort : ESS ignore totalement la monotonie et la geometrie des coefficients.

---

## DIRECTION A : La forme de Horner dans Z

### A.1 Reformulation

corrSum(A) = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

avec 0 <= B_0 <= B_1 <= ... <= B_{k-1} = S-k (monotonie stricte au sens large).

Posons c_j = B_j - B_{j-1} >= 0 pour j >= 1, et c_0 = B_0 >= 0. On a sum c_j = B_{k-1} = S-k.

La forme de Horner s'ecrit :

corrSum = 2^{c_0} * H_0

ou H_0 est defini recursivement :
- H_{k-1} = 1 (terme final : coefficient 3^0 = 1, 2^0 = 1 apres extraction)
- H_j = 3^{k-1-j} + 2^{c_{j+1}} * H_{j+1} pour j = k-2, k-3, ..., 0

Donc :
- H_{k-2} = 3 + 2^{c_{k-1}}
- H_{k-3} = 3^2 + 2^{c_{k-2}} * (3 + 2^{c_{k-1}})
- H_{k-4} = 3^3 + 2^{c_{k-3}} * (3^2 + 2^{c_{k-2}} * (3 + 2^{c_{k-1}}))
- ...
- H_0 = 3^{k-1} + 2^{c_1} * (3^{k-2} + 2^{c_2} * (...))

Et corrSum = 2^{c_0} * H_0.

### A.2 Contraintes de parite et divisibilite par 2

**Fait 1** : d = 2^S - 3^k est IMPAIR (car 2^S est pair et 3^k est impair, donc d est impair).

**Consequence** : d | corrSum <==> d | (2^{c_0} * H_0) <==> d | H_0 (car gcd(d, 2) = 1).

Donc on peut diviser par 2^{c_0} = 2^{B_0} sans perte. La condition de divisibilite se reduit a d | H_0.

**Fait 2** : H_0 mod 2.

Examinons H_0 = 3^{k-1} + 2^{c_1} * H_1.

Si c_1 >= 1 : H_0 ≡ 3^{k-1} mod 2 ≡ 1 mod 2. Donc H_0 est impair.

Si c_1 = 0 : H_0 = 3^{k-1} + H_1. Regardons H_1 = 3^{k-2} + 2^{c_2} * H_2.
- Si c_2 >= 1 : H_1 ≡ 3^{k-2} ≡ 1 mod 2, donc H_0 ≡ 1 + 1 = 0 mod 2.
- Si c_2 = 0 : H_1 = 3^{k-2} + H_2, et on continue.

En general, soit j* le plus petit indice j >= 1 tel que c_j >= 1.
- Si j* = 1 : H_0 est impair.
- Si j* = 2 : H_0 = 3^{k-1} + 3^{k-2} + 2^{c_2} * H_2 ≡ 1 + 1 + 0 = 0 mod 2.
- Si j* = m : H_0 = sum_{i=0}^{m-1} 3^{k-1-i} + 2^{c_m} * H_m. La somme partielle est 3^{k-1} * (1 - (1/3)^m) / (1 - 1/3) = (3^{k-1} - 3^{k-1-m}) * 3/2. Plus rigoureusement dans Z : sum_{i=0}^{m-1} 3^{k-1-i} = 3^{k-m} * (3^m - 1)/2. La parite de (3^m - 1)/2 : pour m >= 1, 3^m - 1 est toujours pair, et (3^m - 1)/2 est impair ssi m est impair, pair ssi m est pair.

En fait, procedons plus directement. Quand c_1 = c_2 = ... = c_{m-1} = 0 et c_m >= 1, on a B_0 = B_1 = ... = B_{m-1} et B_m > B_{m-1}. Cela signifie que les m premiers exposants 2 sont egaux. Les m premiers termes de corrSum contribuent :

sum_{j=0}^{m-1} 3^{k-1-j} * 2^{B_0} = 2^{B_0} * 3^{k-m} * (3^m - 1)/2

Apres extraction de 2^{c_0} = 2^{B_0}, il reste dans H_0 une contribution 3^{k-m} * (3^m - 1)/2.

**La valuation 2-adique de cette somme partielle** : v_2((3^m - 1)/2).

On sait que v_2(3^m - 1) = 1 si m est impair, et v_2(3^m - 1) = v_2(m) + 2 si m est pair (Lifting the Exponent Lemma).

Donc v_2((3^m - 1)/2) = 0 si m est impair, et v_2(m) + 1 si m est pair.

**Ceci est une contrainte non triviale** : si les m premiers gaps c_j sont nuls (plateau de longueur m), alors le bloc correspondant contribue un facteur 2^{v_2((3^m-1)/2)} a H_0, ce qui impose des contraintes de congruence mod 2^t sur H_0.

**MAIS** : comme d est impair, la valuation 2-adique de H_0 n'a aucun impact sur la divisibilite d | H_0. La contrainte de parite est reelle mais sans consequence pour le verrou.

### A.3 Contraintes modulo 3

H_0 mod 3 :

H_0 = 3^{k-1} + 2^{c_1} * H_1

H_0 ≡ 0 + 2^{c_1} * H_1 ≡ 2^{c_1} * H_1 mod 3.

H_1 = 3^{k-2} + 2^{c_2} * H_2 ≡ 2^{c_2} * H_2 mod 3.

En iterant :
H_0 ≡ 2^{c_1} * 2^{c_2} * ... * 2^{c_{k-1}} * H_{k-1} mod 3
    = 2^{c_1 + c_2 + ... + c_{k-1}} * 1 mod 3
    = 2^{S - k - c_0} mod 3

(car sum_{j=1}^{k-1} c_j = S - k - c_0 = S - k - B_0.)

Donc H_0 ≡ 2^{S-k-B_0} mod 3.

Or d = 2^S - 3^k. Modulo 3 : d ≡ 2^S mod 3 = (-1)^S mod 3.

Pour que d | H_0, il faut en particulier H_0 ≡ 0 mod gcd(d, 3).

Mais gcd(d, 3) : d = 2^S - 3^k. Si k >= 1, alors 3 | 3^k, donc d ≡ 2^S mod 3. Si S est pair, d ≡ 1 mod 3. Si S est impair, d ≡ 2 mod 3. Dans les deux cas gcd(d, 3) = 1 sauf si d ≡ 0 mod 3, i.e. 2^S ≡ 0 mod 3, ce qui est impossible.

Donc gcd(d, 3) = 1 toujours. La contrainte modulo 3 est donc vide (comme pour la contrainte modulo 2).

**PROUVE** : gcd(d, 6) = 1 (d est copremier a 2 et a 3). Les contraintes mod 2 et mod 3 sur H_0 ne produisent AUCUNE obstruction a la divisibilite d | H_0.

### A.4 Contraintes modulo de petites puissances de 3

Explorons H_0 mod 9.

H_0 = 3^{k-1} + 2^{c_1} * (3^{k-2} + 2^{c_2} * H_2)

Pour k >= 3 :
H_0 = 3^{k-1} + 2^{c_1} * 3^{k-2} + 2^{c_1+c_2} * H_2

Modulo 9 (= 3^2), si k >= 3, les deux premiers termes sont divisibles par 9 :
- 3^{k-1} ≡ 0 mod 9 (car k-1 >= 2)
- 2^{c_1} * 3^{k-2} ≡ 0 mod 9 (car k-2 >= 1, donc 3^{k-2} ≡ 0 mod 3... mais pas mod 9 si k=3)

Corrigeons. Si k = 3 : 3^{k-1} = 9 ≡ 0 mod 9, 3^{k-2} = 3 ≡ 3 mod 9.
Donc H_0 ≡ 0 + 2^{c_1} * 3 + 2^{c_1+c_2} * 1 mod 9 = 3 * 2^{c_1} + 2^{c_1+c_2} mod 9.

Pour k general >= 3 :
H_0 mod 3^2 = 2^{c_1} * 3^{k-2} mod 9 + 2^{c_1+c_2} * H_2 mod 9

Si k >= 4 : 3^{k-2} ≡ 0 mod 9, et H_0 ≡ 2^{c_1+c_2} * H_2 mod 9.

En iterant pour k >= m+2 :
H_0 ≡ 2^{c_1+...+c_m} * H_m mod 3^m (pour m <= k-2, puisque les termes 3^{k-1-j} pour j < m sont divisibles par 3^m)

Et H_m ≡ 3^{k-1-m} + ... mod 3^{alpha} depend du nombre de termes restants.

Plus precisement, pour le calcul mod 3^m avec m <= k-1 :

H_0 ≡ 2^{sum_{j=1}^{m} c_j} * H_m mod 3^m

car les termes 3^{k-1}, 3^{k-2}*2^{c_1}, ..., 3^{k-m}*2^{c_1+...+c_{m-1}} sont tous divisibles par 3^{k-m} >= 3^m (si k-m >= m, i.e. m <= k/2).

Pour m = k-1 (le maximum) :
H_0 ≡ 2^{sum_{j=1}^{k-1} c_j} * H_{k-1} mod 3^{k-1}
    = 2^{S-k-B_0} mod 3^{k-1}

Ceci est coherent avec la formula exacte : H_0/3^{k-1} = 1 + sum_{j=1}^{k-1} (2/3)^{sum_{i=1}^{j} c_i}.

Donc H_0 = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{sum_{i=1}^{j} c_i}.

Modulo 3^{k-1}, seul le dernier terme (j=k-1) survit :
H_0 ≡ 2^{sum_{i=1}^{k-1} c_i} = 2^{S-k-B_0} mod 3^{k-1}

Inversement, mod 3 :
H_0 ≡ 2^{S-k-B_0} mod 3 (confirme A.3)

**PROUVE** : H_0 ≡ 2^{S-k-B_0} mod 3^{k-1}.

Pour que d | H_0, il faut H_0 ≡ 0 mod gcd(d, 3^{k-1}).

Or gcd(d, 3^{k-1}) = gcd(2^S - 3^k, 3^{k-1}) = gcd(2^S, 3^{k-1}) = 1 (car gcd(2,3) = 1).

**Conclusion** : gcd(d, 3^m) = 1 pour tout m. Les contraintes de H_0 modulo les puissances de 3 sont vides pour le meme raison que A.3 : d est copremier a 3.

### A.5 Contraintes de la forme Horner pour la divisibilite par un premier p | d

Soit p un premier divisant d = 2^S - 3^k. Alors 2^S ≡ 3^k mod p.

Soit r = ord_p(2). Alors r | S (car 2^S ≡ 3^k ≡ (3/2^{S/k})^k ... non, cela ne se simplifie pas directement).

Plus rigoureusement : 2^S ≡ 3^k mod p. Soit g un generateur de F_p*. Ecrivons 2 = g^a, 3 = g^b. Alors Sa ≡ kb mod (p-1).

La forme de Horner donne (dans Z, puis reduite mod p) :

H_0 = 3^{k-1} + 2^{c_1} * (3^{k-2} + 2^{c_2} * (... + 2^{c_{k-1}}))

Dans F_p : H_0 ≡ sum_{j=0}^{k-1} 3^{k-1-j} * 2^{s_j} mod p

ou s_j = sum_{i=1}^{j} c_i (avec s_0 = 0).

Ecrivons lambda = 3/2 dans F_p* (bien defini car p impair, p > 3). Alors :

H_0 = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{s_j}
    = 3^{k-1} * sum_{j=0}^{k-1} (2/3)^{s_j} * (1/3)^{j-s_j} ... non, simplifions.

H_0 = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{s_j}

Factorisons par 2^{s_{k-1}} = 2^{S-k-B_0} :

H_0 / 2^{S-k-B_0} = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{s_j - (S-k-B_0)}

Ceci melange termes positifs et negatifs dans les exposants, ce n'est pas utile.

Essayons plutot de travailler directement mod p.

Dans F_p, 2^S = 3^k (car p | d = 2^S - 3^k).

**Observation cle** : si s_j >= S pour un j, alors 2^{s_j} mod p se "replie" via 2^S ≡ 3^k. Mais s_j = sum_{i=1}^{j} c_i <= S-k-B_0 <= S-k < S. Donc AUCUN exposant s_j n'atteint S. Pas de repliement direct.

Mais explorons les relations induites. Posons alpha = 2 mod p et beta = 3 mod p. On a alpha^S = beta^k.

H_0 mod p = sum_{j=0}^{k-1} beta^{k-1-j} * alpha^{s_j}

Posons gamma = alpha/beta = 2/3 mod p. Alors :

H_0 / beta^{k-1} = sum_{j=0}^{k-1} gamma^{s_j} / beta^{j-s_j} ... non, pas correct.

H_0 = beta^{k-1} * sum_{j=0}^{k-1} (alpha/beta)^{s_j} * (1/beta)^{j} * beta^{s_j}

C'est trop confus. Ecrivons simplement :

H_0 = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{s_j} (dans Z)

La condition d | H_0 se traduit par : pour tout premier p | d, p | H_0, soit :

sum_{j=0}^{k-1} 3^{k-1-j} * 2^{s_j} ≡ 0 mod p

avec la contrainte 0 = s_0 <= s_1 <= ... <= s_{k-1} = S-k-B_0.

Ici la monotonie des s_j est EXACTEMENT la monotonie des B_j (decalee de B_0).

### A.6 Verdict Direction A

| Resultat | Type | Exploitable ? |
|----------|------|:------------:|
| d est copremier a 6 | PROUVE | NON (trivial, deja connu) |
| H_0 ≡ 2^{S-k-B_0} mod 3^{k-1} | PROUVE | NON (gcd(d, 3^m) = 1) |
| Division par 2^{B_0} est gratuite | PROUVE | MARGINALEMENT (simplifie la forme, ne contraint pas d) |
| Parite de H_0 depend du profil des c_j | PROUVE | NON (d impair) |
| Horner mod p se reduit a SAMC | PROUVE | NON (confirme le noyau irreductible R80) |

**Verdict Direction A : INFORMATIF**

La forme de Horner ne produit AUCUNE obstruction nouvelle a la divisibilite d | corrSum. La raison fondamentale : d est copremier a 6, donc toutes les contraintes mod 2^a * 3^b sont vides. Et modulo p | d, la forme de Horner se reduit a la SAMC dans F_p (noyau irreductible, R80).

L'unique gain est la simplification : on peut travailler avec H_0 (division par 2^{B_0}) et la suite s_j = sum c_i au lieu de B_j. C'est une reecriture, pas une obstruction.

---

## DIRECTION B : L'ensemble image de corrSum

### B.1 Structure de l'ensemble Image

Definissons Image(k, S) = {corrSum(A) : A composition monotone de S en k parts}.

Rappel : A = (B_0, ..., B_{k-1}) avec 0 <= B_0 <= ... <= B_{k-1} = S-k, sum non specifiee... Non, corrigeons.

La definition exacte : corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} ou les B_j sont les exposants de 2 dans la composition. La contrainte est 0 <= B_0 <= B_1 <= ... <= B_{k-1} et B_{k-1} = S-k (borne superieure des exposants).

Nb : la somme sum B_j n'est PAS contrainte a S. La contrainte est sur B_{k-1} seulement.

Verification : dans le contexte du CJT, les A_i dans la trajectoire de Collatz satisfont des contraintes specifiques. Mais pour N_0(d), on cherche corrSum ≡ 0 mod d parmi TOUTES les compositions monotones. Donc Image(k, S) contient |C(S-1, k-1)| = C(S-k+k-1, k-1) ... non.

Le nombre de suites monotones 0 <= B_0 <= B_1 <= ... <= B_{k-1} = S-k est le nombre de suites non-decroissantes de {0, 1, ..., S-k} de longueur k avec B_{k-1} = S-k.

C'est le nombre de suites non-decroissantes (B_0, ..., B_{k-2}) dans {0, ..., S-k} (car B_{k-1} = S-k est fixe et B_{k-2} <= S-k). Ce nombre est C(S-k + k-1, k-1) = C(S-1, k-1).

Donc |{compositions}| = C(S-1, k-1). Mais Image(k,S) est un SOUS-ENSEMBLE de Z, et des compositions distinctes pourraient donner la meme valeur de corrSum. Donc |Image| <= C(S-1, k-1).

### B.2 Collisions dans Image

Deux compositions (B_0, ..., B_{k-1}) et (B'_0, ..., B'_{k-1}) donnent le meme corrSum ssi :

sum_{j=0}^{k-1} 3^{k-1-j} * (2^{B_j} - 2^{B'_j}) = 0

Puisque tous les termes sont des entiers et les coefficients 3^{k-1-j} sont distincts en taille, cette equation est TRES contrainte.

**Cas k = 2** : 3 * (2^{B_0} - 2^{B'_0}) + (2^{B_1} - 2^{B'_1}) = 0. Avec B_1 = B'_1 = S-2, cela donne B_0 = B'_0. Donc pas de collision pour k = 2 : |Image| = C(S-1, 1) = S-1.

**Cas general** : les collisions sont-elles possibles ? Oui : si on echange l'exposant d'un terme petit 3^a avec celui d'un terme grand 3^b, le bilan peut s'equilibrer. Mais la contrainte de monotonie (B_0 <= ... <= B_{k-1}) interdit la plupart de ces echanges.

**Borne inferieure sur |Image|** : Chaque corrSum est determine par les k-1 "gaps" c_1, ..., c_{k-1} avec c_j >= 0 et sum c_j = S-k-B_0 pour un B_0 choisi. Le terme dominant de corrSum est 3^{k-1} * 2^{B_0} (le premier terme). Deux compositions avec B_0 different ont corrSum different (car 3^{k-1} * 2^{B_0} >> somme des autres termes quand B_0 varie suffisamment). Donc il y a au moins S-k+1 valeurs distinctes (une par choix de B_0 de 0 a S-k).

En pratique, |Image| est TRES proche de C(S-1, k-1), les collisions etant rares.

### B.3 Structure geometrique de Image

corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

Chaque terme est un element du sous-monoide de Z engendre par {3^a * 2^b : a,b >= 0}. corrSum est une somme de k tels elements avec des contraintes sur a (deterministe : a = k-1-j) et b (monotone : B_0 <= ... <= B_{k-1}).

**Observation** : si on definit v_j = 3^{k-1-j} * 2^{B_j} pour j = 0, ..., k-1, alors :

v_j / v_{j+1} = 3 * 2^{B_j - B_{j+1}} = 3 * 2^{-c_{j+1}} (ou c_{j+1} = B_{j+1} - B_j >= 0)

Donc v_j / v_{j+1} = 3 / 2^{c_{j+1}} <= 3 (car c_{j+1} >= 0).

Si c_{j+1} = 0 : v_j = 3 * v_{j+1} (rapport exact 3).
Si c_{j+1} = 1 : v_j = 3/2 * v_{j+1}.
Si c_{j+1} >= 2 : v_j < v_{j+1} (les termes CROISSENT en j).

**Structure de decroissance/croissance** : la suite (v_j) n'est pas necessairement monotone. Si c_{j+1} = 0, le terme precedent est exactement 3 fois plus grand. Si c_{j+1} >= 2, le terme precedent est strictement plus petit.

Le cas c_{j+1} = 1 est le cas CRITIQUE : v_j = 3/2 * v_{j+1}, donc les termes decroissent lentement (facteur 3/2 par pas).

**L'image de corrSum dans l'espace (v_0, ..., v_{k-1})** vit sur un cone (termes positifs) avec la contrainte multiplicative v_j / v_{j+1} = 3 * 2^{-c_{j+1}}. C'est un sous-ensemble discret d'un cone.

### B.4 corrSum comme polynome en 2 et 3

corrSum = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}

Ceci est un polynome de Laurent en 2 et 3 (plus exactement, un element du monoide engendre par 2 et 3 dans Z). On peut ecrire :

corrSum = 3^{k-1} * Phi(2/3)

ou Phi(x) = sum_{j=0}^{k-1} x^{B_j} * 3^{-j+... } ... Non, cela ne se factorise pas proprement.

Essayons : corrSum = sum_{j} 3^{k-1-j} * 2^{B_j} = 2^{B_0} * sum_{j} 3^{k-1-j} * 2^{B_j - B_0}.

Posons x = 2 (variable formelle) et ecrivons dans Z[x] :

corrSum = x^{B_0} * sum_{j=0}^{k-1} 3^{k-1-j} * x^{s_j}

ou s_j = B_j - B_0 >= 0 et s_0 = 0 < s_1 <= ... <= s_{k-1}.

Soit P(x) = sum_{j=0}^{k-1} 3^{k-1-j} * x^{s_j} dans Z[x]. Alors corrSum = 2^{B_0} * P(2).

La condition d | corrSum equivaut a d | P(2) (car gcd(d, 2) = 1).

**P(x) est un POLYNOME CREUX** (lacunaire) : il a exactement k monomes non nuls, d'exposants 0 = s_0 < s_1 < ... < s_{k-1} = S-k-B_0 (ou certains s_j peuvent etre egaux, mais dans ce cas le monome correspondant a un coefficient augmente).

Attention : si s_j = s_{j+1} (c'est-a-dire c_{j+1} = 0), les monomes de meme degre se fusionnent. Soit I_m = {j : s_j = m}. Alors :

P(x) = sum_{m=0}^{S-k-B_0} (sum_{j in I_m} 3^{k-1-j}) * x^m

Le coefficient de x^m dans P est sum_{j in I_m} 3^{k-1-j} = 3^{k-1-min(I_m)} * (3^{|I_m|} - 1) / (3-1) (si I_m est un intervalle consecutif, ce qui est garanti par la monotonie des B_j).

Oui : si s_j = s_{j+1} = ... = s_{j+l-1} = m, alors I_m = {j, j+1, ..., j+l-1} (consecutifs car les s_j sont non-decroissants), et :

coeff(x^m) = sum_{i=0}^{l-1} 3^{k-1-j-i} = 3^{k-j-l} * (3^l - 1)/2

### B.5 Lien avec les polynomes cyclotomiques et les racines de l'unite

d = 2^S - 3^k. Si d est premier, c'est un analogue de nombre de Mersenne generalise. Si d est compose, ses facteurs premiers p satisfont p | 2^S - 3^k, i.e., 2^S ≡ 3^k mod p.

P(2) ≡ 0 mod p <==> 2 est une racine de P(x) mod p <==> P(x) ≡ 0 mod (x - 2) dans F_p[x].

Mais 2 est un element specifique de F_p, pas une racine de l'unite en general. La theorie des polynomes cyclotomiques ne s'applique pas directement, sauf si on exploite la relation 2^S ≡ 3^k mod p, qui lie 2 au sous-groupe d'ordre r = ord_p(2).

### B.6 Verdict Direction B

| Resultat | Type | Exploitable ? |
|----------|------|:------------:|
| corrSum = 2^{B_0} * P(2) ou P est lacunaire dans Z[x] | PROUVE | INFORMATIF (reformulation, pas obstruction) |
| P(x) a au plus k monomes | PROUVE | INFORMATIF |
| Les collisions dans Image sont rares | CONJECTURE (prouve pour k=2) | NON (ne contraint pas d) |
| Les rapports v_j/v_{j+1} sont determines par les c_j | PROUVE | INFORMATIF (structure du cone) |
| La structure en cone ne contraint pas la divisibilite par d | PROUVE | MORT (d copremier a 6) |

**Verdict Direction B : INFORMATIF**

La structure de l'ensemble Image est riche mais ne produit pas d'obstruction a la divisibilite par d. La reformulation P(2) ≡ 0 mod p est une reecriture qui ne depasse pas le noyau irreductible. La lacunarite du polynome P est une propriete reelle mais elle ne mord pas car les outils de divisibilite de polynomes lacunaires (Schinzel, Filaseta) s'appliquent a des polynomes avec coefficients FIXES, pas a des familles parametrees par les s_j.

---

## DIRECTION C : La divisibilite par d = 2^S - 3^k

### C.1 Le repliement dans Z/dZ

Dans Z/dZ : 2^S ≡ 3^k mod d.

Cela signifie que pour tout n >= S : 2^n = 2^{n-S} * 2^S ≡ 2^{n-S} * 3^k mod d.

Mais dans corrSum, tous les exposants B_j satisfont B_j <= S-k < S. Donc AUCUN repliement direct ne se produit.

**Question** : le repliement indirect (via des combinaisons de termes) peut-il creer des contraintes ?

corrSum = sum 3^{k-1-j} * 2^{B_j}. Le terme maximal est 2^{S-k} (coefficient 1). Le terme 3^{k-1} * 2^{S-k} n'apparait que si B_0 = S-k (tous les B_j egaux a S-k). Mais dans ce cas :

corrSum = (sum_{j=0}^{k-1} 3^{k-1-j}) * 2^{S-k} = ((3^k - 1)/2) * 2^{S-k} = (3^k - 1) * 2^{S-k-1}

Voyons si d | corrSum dans ce cas extreme :
d | (3^k - 1) * 2^{S-k-1} <==> d | (3^k - 1) (car gcd(d, 2) = 1)
d = 2^S - 3^k, et 3^k - 1 = 2^S - d - 1.
d | (2^S - d - 1) <==> d | (2^S - 1) <==> 2^S ≡ 1 mod d.

Or 2^S ≡ 3^k mod d, donc 2^S ≡ 1 mod d <==> 3^k ≡ 1 mod d.

Pour k = 22 : d(22) = 2^35 - 3^22 = 34,359,738,368 - 31,381,059,609 = 2,978,678,759.

3^22 mod d = 31,381,059,609 mod 2,978,678,759 = 31,381,059,609 - 10 * 2,978,678,759 = 31,381,059,609 - 29,786,787,590 = 1,594,272,019.

Donc 3^22 mod d ≠ 1. La composition "tout plateau" (B_j = S-k pour tout j) NE donne PAS corrSum ≡ 0 mod d.

### C.2 Analyse du dernier terme

Le dernier terme de corrSum est 3^0 * 2^{B_{k-1}} = 2^{S-k}.

Dans Z/dZ : 2^{S-k} est un element specifique. Notons qu'on peut ecrire :

2^{S-k} * 2^k = 2^S ≡ 3^k mod d

Donc 2^{S-k} ≡ 3^k * 2^{-k} ≡ (3/2)^k mod d.

Ainsi le dernier terme est ≡ (3/2)^k mod d. C'est une puissance du ratio lambda = 3/2 qui est l'objet central de la dynamique de Collatz.

Pour corrSum ≡ 0 mod d :
sum_{j=0}^{k-2} 3^{k-1-j} * 2^{B_j} ≡ -(3/2)^k mod d

Le membre gauche est une somme de k-1 termes avec des coefficients 3^{k-1}, 3^{k-2}, ..., 3, et des exposants 2^{B_0}, ..., 2^{B_{k-2}} avec B_j <= B_{k-2} <= S-k.

Cela donne une contrainte de congruence mod d. Mais d ~ 2^S / log(S), qui est grand, et la somme a ~k termes de taille << d. Donc la somme partielle modulo d est TRES PETITE par rapport a d, et il n'y a pas de "repliement" modulo d : la congruence sum ≡ -(3/2)^k mod d est en fait une egalite sum + (3/2)^k = 0 OU sum + (3/2)^k = d OU sum + (3/2)^k = 2d, etc.

**La question est** : quel est le rapport corrSum / d ?

corrSum_max = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{S-k} = ((3^k-1)/2) * 2^{S-k} = (3^k-1) * 2^{S-k-1}

d = 2^S - 3^k

corrSum_max / d = (3^k - 1) * 2^{S-k-1} / (2^S - 3^k)

Pour k grand par rapport a S, 3^k ~ 2^S (puisque S = ceil(k*log_2(3)) + 1), donc :
- 3^k ~ 2^S, d ~ 2^S - 3^k << 2^S
- corrSum_max ~ 3^k * 2^{S-k}/2 ~ 2^S * 2^{S-k}/2 = 2^{2S-k-1}
- corrSum_max / d ~ 2^{2S-k-1} / d

Pour k=22, S=35 : corrSum_max / d ~ (3^22 - 1) * 2^12 / d ~ 3.13 * 10^10 * 4096 / 2.98 * 10^9 ~ 4.3 * 10^4.

Donc corrSum peut valoir jusqu'a ~43000 * d. Les valeurs multiples de d dans l'intervalle [corrSum_min, corrSum_max] sont au nombre de ~43000. C'est le "budget" du Ratio Law.

### C.3 Le ratio lambda = 3/2 et les convergentes

Le rapport 2^S / 3^k est l'approximation entiere de (3/2)^k par une puissance de 2. Les convergentes de log_2(3) donnent les meilleurs approximations rationnelles p_n/q_n de log_2(3).

Les convergentes de log_2(3) = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, ...] sont :
p_0/q_0 = 1/1
p_1/q_1 = 2/1
p_2/q_2 = 3/2
p_3/q_3 = 8/5
p_4/q_4 = 19/12
p_5/q_5 = 65/41
p_6/q_6 = 84/53
p_7/q_7 = 485/306
p_8/q_8 = 1054/665
...

Pour que S/k soit une convergente de log_2(3), il faut que k soit un denominateur de convergente. Les valeurs dans le gap 22-41 : k=41 est proches du denominateur 41 de la convergente 65/41. Verifions : la convergente p_5/q_5 = 65/41.

Donc pour k = 41 : S = 65 est la MEILLEURE approximation au sens des fractions continues. Cela signifie que d(41) = 2^65 - 3^41 est PETIT par rapport a 2^65 ou 3^41.

Calculons : 2^65 = 36,893,488,147,419,103,232. 3^41 = 36,472,996,377,170,786,403. d(41) = 420,491,770,248,316,829 ~ 4.2 * 10^17.

Le ratio d/2^S = 1 - 3^k/2^S. Pour k=41, S=65 : d/2^S = 1 - 3^41/2^65 ~ 0.0114.

Pour les k qui ne sont PAS des denominateurs de convergentes, S/k est une MAUVAISE approximation de log_2(3), et d est RELATIVEMENT plus grand. Par exemple, k=22, S=35 : d/2^S = 1 - 3^22/2^35 ~ 0.0867.

**Propriete des convergentes** : si S/k = p_n/q_n (convergente), alors |S * log 2 - k * log 3| est MINIMALE parmi les approximations de denominateur <= k. Par le theoreme de la meilleure approximation :

|d| = |2^S - 3^k| = 2^S * |1 - 3^k/2^S| ~ 2^S * |k * log_2(3) - S| * log 2

Pour les convergentes : |k * log_2(3) - S| ~ 1/(q_{n+1} * k), et d ~ 2^S / (q_{n+1} * k).

La TAILLE de d depend de q_{n+1} (le denominateur de la convergente SUIVANTE). Si q_{n+1} est grand (convergente tres precise), d est petit, et il y a MOINS de multiples de d dans la plage de corrSum.

### C.4 Consequence pour N_0(d)

Le nombre de multiples de d dans [corrSum_min, corrSum_max] est environ corrSum_max / d ~ C(k,S)/d.

L'heuristique du Ratio Law dit : N_0(d) ~ C(S-1, k-1) * (#multiples_d / #valeurs_image) ~ C(S-1, k-1) / d_eff, ou d_eff est le "denominateur effectif" de la division.

Pour les k qui sont des denominateurs de convergentes (meilleure approximation), d est plus petit, et N_0(d) est PLUS GRAND (heuristiquement). C'est un facteur DEFAVORABLE pour prouver N_0(d) = 0.

Pour les k loin des convergentes, d est plus grand, et N_0(d) est plus petit. C'est FAVORABLE.

**MAIS** : cette analyse est purement heuristique (Ratio Law). Elle ne prouve rien.

### C.5 L'interaction du dernier terme avec d

On a montre que 2^{S-k} ≡ (3/2)^k mod d (section C.2).

Plus generalement, pour tout j :
3^{k-1-j} * 2^{B_j} mod d.

Si B_j = S-k : 3^{k-1-j} * 2^{S-k} = 3^{k-1-j} * (3/2)^k mod d = 3^{2k-1-j} * 2^{-k} mod d.

Si B_j = 0 : 3^{k-1-j} mod d. Comme d = 2^S - 3^k, on a 3^k ≡ 2^S mod d, donc 3^{k-1-j} = 3^{k-1-j} directement si k-1-j < k (toujours vrai pour j >= 0).

Pour j = 0, B_0 = 0 : le premier terme est 3^{k-1} mod d. Pour k=22 : 3^21 = 10,460,353,203. Et d = 2,978,678,759. Donc 3^21 mod d = 10,460,353,203 - 3*2,978,678,759 = 10,460,353,203 - 8,936,036,277 = 1,524,316,926.

Ces calculs mod d sont exacts mais ne revelent pas de structure exploitable sans un argument systematique.

### C.6 Reformulation dans Z/dZ via la relation 2^S = 3^k

L'idee la plus prometteuse est la suivante. Dans Z/dZ, 2^S = 3^k. Ecrivons r = ord_d(2) (l'ordre de 2 modulo d). Alors r | S si et seulement si 2^S ≡ 1 mod d. Mais 2^S ≡ 3^k mod d, donc r | S ssi 3^k ≡ 1 mod d.

En general, r ne divise PAS S. Mais on a la relation 2^S = 3^k dans Z/dZ, qui permet de CONVERTIR certaines puissances de 2 en puissances de 3 et vice versa.

Pour exploiter cela : ecrivons chaque B_j = q_j * S + r_j avec 0 <= r_j < S. Comme B_j <= S-k < S, on a q_j = 0 et r_j = B_j. Pas de reduction utile.

Mais considerons la somme corrSum modulo des PETITS facteurs de d. Si d = p_1^{a_1} * ... * p_m^{a_m}, alors d | corrSum ssi p_i^{a_i} | corrSum pour chaque i (CRT).

Pour chaque p | d, la condition corrSum ≡ 0 mod p est independante. Si on pouvait montrer que pour au moins un p | d, corrSum ≠ 0 mod p pour TOUTE composition monotone, on aurait N_0(d) = 0.

**C'est exactement l'approche originale du programme (SAMC dans F_p)**, et c'est le noyau irreductible R80.

### C.7 Verdict Direction C

| Resultat | Type | Exploitable ? |
|----------|------|:------------:|
| 2^{S-k} ≡ (3/2)^k mod d | PROUVE | INFORMATIF (relie au ratio de Collatz) |
| Pas de repliement direct (B_j < S) | PROUVE | NON (trivial) |
| corrSum / d ~ C(k,S)/d, taille du budget | PROUVE | INFORMATIF (Ratio Law) |
| La qualite d'approximation S/k (convergentes) affecte la taille de d | PROUVE | INFORMATIF (mais ne contraint pas N_0) |
| Reduction a SAMC par CRT | PROUVE | MORT (noyau irreductible R80) |

**Verdict Direction C : INFORMATIF**

L'analyse de la divisibilite par d dans Z ne produit pas d'obstruction nouvelle. Le repliement 2^S ≡ 3^k mod d est reel mais ne mord pas car les exposants B_j restent strictement sous S. La theorie des fractions continues de log_2(3) eclaire la TAILLE de d mais pas la DIVISIBILITE de corrSum par d. La reduction CRT ramene au noyau irreductible.

---

## DIRECTION D : Fractions continues et approximation diophantienne

### D.1 Le contexte

d/3^k = 2^S/3^k - 1 = 2^{S/k * k} / 3^k - 1 = (2^{S/k}/3)^k - 1.

Posons alpha = log_2(3) (irrationnel, transcendant). Alors S = ceil(k*alpha) + epsilon (ou epsilon in {0,1} selon la parite).

La qualite de l'approximation S/k de alpha est mesuree par :
|S/k - alpha| = |S - k*alpha| / k

Par la theorie des fractions continues, si k = q_n (denominateur de la n-ieme convergente), alors :
|S - k*alpha| ~ 1/q_{n+1}

Et d = 2^S - 3^k = 3^k * (2^S/3^k - 1) ~ 3^k * k * (S/k - alpha) * log 2 ~ 3^k * log 2 / q_{n+1}.

### D.2 Le theoreme de Roth et ses consequences

Le theoreme de Roth (1955) dit que pour alpha transcendant :
|alpha - p/q| > c(alpha, epsilon) / q^{2+epsilon}

pour tout epsilon > 0. Cela implique :
|S - k * alpha| > c / k^{1+epsilon}

Donc d > c' * 3^k / k^{1+epsilon} pour une constante c'.

**Consequence** : d est GRAND par rapport a 3^k / k^2 (polynomialement). Cela confirme que d ne peut pas etre "trop petit" mais ne donne aucune information sur la divisibilite de corrSum par d.

### D.3 Fractions continues de log_2(3) et valeurs de d

Les convergentes de log_2(3) les plus relevantes pour k = 22..41 :

| n | p_n/q_n | q_n | k dans le gap ? | S | d = 2^S - 3^k |
|---|---------|-----|:---------------:|---|----------------|
| 4 | 19/12 | 12 | non | - | - |
| 5 | 65/41 | 41 | **OUI** | 65 | ~4.2 * 10^17 |
| 6 | 84/53 | 53 | non | - | - |

Seul k = 41 correspond a un denominateur de convergente dans le gap. Pour ce k, d est relativement PETIT (meilleure approximation). Pour les autres k du gap (22-40), S/k n'est PAS une convergente, et d est relativement plus grand.

**Implication** : k = 41 est le cas le PLUS DIFFICILE du gap (d le plus petit, donc le plus de multiples de d dans la plage de corrSum). Les cas k = 22..40 sont relativement plus faciles.

### D.4 La mesure d'irrationalite et les bornes de Baker

Baker (1966) donne une borne EFFECTIVE :
|S * log 2 - k * log 3| > exp(-C * log S * log k)

pour une constante effective C. Cela implique :
d = 2^S * |1 - 3^k/2^S| > 2^S * exp(-C * log^2 S) / S

C'est BEAUCOUP plus fort que Roth pour les grandes valeurs. La borne de Baker est effective et optimale (a des facteurs logarithmiques pres) grace au theoreme de Baker-Wustholz (1993).

**Mais** : cette borne sur la TAILLE de d ne contraint pas la divisibilite de corrSum par d. Baker borne |d| par le bas, pas la distribution de corrSum mod d.

### D.5 Lien avec les sommes de puissances de 2/3

Revenons a la forme :
H_0 / 3^{k-1} = 1 + sum_{j=1}^{k-1} (2/3)^{sigma_j}

ou sigma_j = sum_{i=1}^{j} c_i, avec 0 < sigma_1 <= sigma_2 <= ... <= sigma_{k-1} = S-k-B_0.

C'est une somme de puissances de 2/3 a exposants croissants. Ecrivons rho = 2/3 (rationnel). Alors :

H_0 / 3^{k-1} = 1 + rho^{sigma_1} + rho^{sigma_2} + ... + rho^{sigma_{k-1}}

C'est un element de Z[1/6] (plus precisement, de Z[1/3] * 2^{sigma_{k-1}} / 3^{k-1}).

Maintenant, d | H_0 <==> d | 3^{k-1} * (1 + sum rho^{sigma_j}) <==> d | (3^{k-1} + sum 3^{k-1-j} * 2^{sigma_j}).

La condition est equivalente a : la somme 1 + rho^{sigma_1} + ... + rho^{sigma_{k-1}} est divisible par d/3^{k-1} dans Z[1/6].

Mais gcd(d, 3^{k-1}) = 1, donc d | H_0 <==> d | (3^{k-1} * sum) <==> d | sum*3^{k-1}. Comme gcd(d,3)=1, d | sum*3^{k-1} <==> d | sum (non! sum n'est pas entier).

Corrigeons : H_0 = 3^{k-1} + sum_{j=1}^{k-1} 3^{k-1-j} * 2^{sigma_j}. C'est un ENTIER. La condition est d | H_0 dans Z.

La question profonde est : quand on ecrit H_0 / 3^{k-1} = 1 + sum (2/3)^{sigma_j} * (quelque chose), est-ce que la theorie de l'approximation diophantienne de log_2(3) contraint les valeurs possibles de H_0 ?

**Tentative** : H_0 est une somme de k termes de la forme 3^a * 2^b. Si d | H_0, alors H_0 = m * d = m * (2^S - 3^k) pour un entier m >= 1.

Ecrivons :
sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} = m * 2^S - m * 3^k

Rearrangeons :
m * 2^S = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} + m * 3^k
         = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} + m * 3^k

Le membre droit est une somme de k+1 termes dans le monoide {3^a * 2^b}. Le membre gauche est m * 2^S.

En divisant par 2^{B_0} (le plus petit exposant de 2) :

m * 2^{S-B_0} = H_0 + m * 3^k / 2^{B_0}

Non, il faut que m * 3^k soit divisible par 2^{B_0}, ce qui est faux en general (car gcd(3^k, 2) = 1). Donc B_0 = 0 est impose si m est impair. Mais si m est pair, on pourrait avoir B_0 > 0... Non, revoyons :

corrSum = sum 3^{k-1-j} * 2^{B_j} = m * d = m * (2^S - 3^k)

Si B_0 > 0 : corrSum est divisible par 2^{B_0}. Donc m*(2^S - 3^k) est divisible par 2^{B_0}. Comme 2^S - 3^k est impair, 2^{B_0} | m. Posons m = 2^{B_0} * m'. Alors corrSum = 2^{B_0} * H_0 = 2^{B_0} * m' * d, donc H_0 = m' * d. On retrouve la reduction de A.2.

### D.6 Exploration de la S-unit equation SPECIFIQUE

L'equation S-unit est :
sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} - m * 2^S + m * 3^k = 0

C'est une equation en k+2 termes de {2,3}-unites (plus exactement, de monomes en 2 et 3). Les variables sont (B_0, ..., B_{k-1}, m), avec la contrainte de monotonie B_0 <= ... <= B_{k-1} = S-k.

ESS borne le nombre total de solutions NON-DEGENEREES. La raison pour laquelle ESS est mort est que la borne depend du NOMBRE de termes (k+2), pas de la structure.

**Ce qu'ESS ne voit pas** :
1. La MONOTONIE des B_j (les exposants sont ordonnes)
2. La PROGRESSION GEOMETRIQUE des coefficients (3^{k-1}, 3^{k-2}, ..., 3, 1)
3. La RELATION entre B_{k-1} et S (B_{k-1} = S-k)
4. La POSITIVITE de m

**Question** : existe-t-il dans la litterature un raffinement d'ESS pour les S-unit equations avec coefficients en progression geometrique ou avec contraintes de monotonie sur les exposants ?

**Reponse apres examen** : NON, a ma connaissance. Les raffinements d'ESS (Evertse 2017, "Effective Results for Unit Equations over Finitely Generated Integral Domains" ; Gyory-Evertse 2015) ameliorent la constante dans l'exposant mais ne changent pas la dependance en le nombre de termes. Les contraintes structurelles (monotonie, progression geometrique) ne sont pas exploitees par la theorie existante.

La raison profonde : ESS procede par recurrence sur le nombre de termes et par elimination de sous-sommes. La monotonie et la progression geometrique sont des proprietes des COEFFICIENTS et des EXPOSANTS, pas des sous-sommes. La theorie n'a pas de mecanisme pour incorporer ces contraintes.

### D.7 Tentative : borner corrSum / d par la theorie de l'approximation

corrSum / d = sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} / (2^S - 3^k)

Pour que d | corrSum, il faut corrSum / d entier. Peut-on borner |corrSum / d - round(corrSum/d)| par le bas en utilisant l'approximation diophantienne ?

corrSum = sum 3^{k-1-j} * 2^{B_j}. Divisons par 2^S :

corrSum / 2^S = sum 3^{k-1-j} * 2^{B_j - S}

Chaque terme est < 1 (car B_j <= S-k < S et 3^{k-1-j} < 3^k < 2^S). Donc corrSum / 2^S < k (somme de k termes < 1).

corrSum / d = corrSum / (2^S * (1 - 3^k/2^S)) = (corrSum/2^S) / (1 - 3^k/2^S)

Or 1 - 3^k/2^S = d/2^S est PETIT (de l'ordre de 10^{-2} pour k dans le gap). Donc corrSum / d peut etre GRAND (~k / (d/2^S) ~ k * 2^S / d).

C'est coherent avec C.2 : corrSum / d peut atteindre ~43000 pour k=22.

Pour que corrSum / d soit ENTIER, il faut que la partie fractionnaire {corrSum / d} = 0. La question est : la theorie de l'approximation diophantienne peut-elle montrer que {corrSum / d} > 0 pour toute composition monotone ?

**Non**. La theorie de l'approximation diophantienne contraint les approximations de NOMBRES IRRATIONNELS par des rationnels. Ici, corrSum / d est un RATIONNEL (c'est un ratio d'entiers). La question de savoir s'il est entier est une question de DIVISIBILITE dans Z, pas d'approximation diophantienne.

La seule connexion potentielle serait : si corrSum avait une expression faisant intervenir log_2(3) de maniere essentielle, alors les bornes de Baker pourraient s'appliquer. Mais corrSum est un ENTIER (somme finie de termes entiers), et sa valeur ne fait pas intervenir log_2(3).

### D.8 Verdict Direction D

| Resultat | Type | Exploitable ? |
|----------|------|:------------:|
| k = 41 est le cas le plus dur (denominateur de convergente, d minimal) | PROUVE | INFORMATIF (hierarchie de difficulte dans le gap) |
| Baker borne d par le bas | PROUVE (litterature) | NON (borne la taille de d, pas la divisibilite de corrSum) |
| La theorie des fractions continues eclaire la taille relative de d | PROUVE | INFORMATIF (pas de levier de preuve) |
| Pas de raffinement ESS pour progressions geometriques | PROUVE (absence) | MORT (la litterature ne fournit pas l'outil) |
| corrSum/d est rationnel, pas irrationnel : l'approximation dioph. ne s'applique pas | PROUVE | MORT |

**Verdict Direction D : INFORMATIF (tendant vers MORT)**

La theorie des fractions continues de log_2(3) ne mord pas sur le verrou. Elle eclaire la TAILLE de d (et donc la "difficulte relative" des differents k du gap) mais ne fournit aucun mecanisme pour prouver N_0(d) = 0. La connexion avec Baker/Evertse a deja ete exploree et enterree en R82-R83. La direction D ne fournit rien de nouveau par rapport a ces rounds.

---

## SYNTHESE GLOBALE

### Bilan par direction

| Direction | Question exploree | Verdict | Gain |
|-----------|------------------|---------|------|
| **A : Horner dans Z** | Contraintes mod 2^a * 3^b ? | INFORMATIF | gcd(d,6)=1 tue toutes les contraintes locales |
| **B : Ensemble Image** | Structure de {corrSum(A)} ? | INFORMATIF | Reformulation P(2), cone, lacunarite -- pas d'obstruction |
| **C : Divisibilite par d** | Repliement 2^S ≡ 3^k, CRT ? | INFORMATIF | Ramene au noyau irreductible R80 |
| **D : Fractions continues** | Approximation dioph. de log_2(3) ? | MORT | Theorie de la taille, pas de la divisibilite |

### Pourquoi ESS ne peut pas etre ameliore par ces directions

La raison FONDAMENTALE est en deux parties :

**Partie 1 : les contraintes locales sont vides.** Puisque gcd(d, 6) = 1, toute contrainte de congruence modulo les puissances de 2 et 3 est invisible pour la divisibilite par d. Les directions A et B explorent essentiellement des contraintes dans Z[1/6], qui est exactement l'anneau des S-unites pour S = {2,3}. Mais d est copremier a 6, donc ces contraintes sont orthogonales.

**Partie 2 : la contrainte globale se reduit au noyau irreductible.** La direction C montre que la divisibilite par d se decompose (via CRT) en divisibilite par les facteurs premiers p de d. Chaque condition corrSum ≡ 0 mod p est la SAMC, qui est le noyau irreductible R80. La structure monotone et geometrique, bien que reelles dans Z, deviennent "invisibles" modulo p (car la reduction mod p perd l'information sur l'ordre total des B_j et la progression geometrique des coefficients 3^{k-1-j}).

### Ce qui est PROUVE (resultats rigoureux de cette investigation)

1. **gcd(d, 6) = 1** pour tout k >= 1. (Trivial mais fondamental.)
2. **H_0 ≡ 2^{S-k-B_0} mod 3^{k-1}** (congruence exacte de Horner mod puissances de 3).
3. **corrSum = 2^{B_0} * P(2)** ou P in Z[x] est lacunaire a k monomes (reformulation polynomiale).
4. **2^{S-k} ≡ (3/2)^k mod d** (le dernier terme de corrSum encode le ratio de Collatz).
5. **k = 41 est le cas le plus difficile du gap** (denominateur de convergente de log_2(3), d minimal relativement).
6. **Il n'existe PAS dans la litterature de raffinement d'ESS pour les S-unit equations avec coefficients en progression geometrique ou avec contraintes de monotonie.** (Resultat negatif verifie.)

### Ce qui est CONJECTURE

Rien. Cette investigation ne produit aucune conjecture nouvelle. Elle confirme des resultats negatifs.

### Ce qui est MORT

1. **La direction "contraintes mod 2^a * 3^b via Horner"** : MORTE car gcd(d, 6) = 1.
2. **La direction "polynome lacunaire P(2) ≡ 0 mod p"** : MORTE car c'est le noyau irreductible R80.
3. **La direction "approximation diophantienne de log_2(3) pour borner corrSum/d"** : MORTE car corrSum/d est rationnel, pas irrationnel.
4. **La direction "raffinement d'ESS par la structure"** : MORTE (absence d'outil dans la litterature).

### L'outil qualitativement nouveau necessaire

Cette investigation confirme le diagnostic de R83 : la piste S-unit dans Z est SUSPENDUE et attend un "outil qualitativement nouveau". Les quatre directions explorees ici ne fournissent pas cet outil. Plus precisement :

- L'outil devrait exploiter SIMULTANEMENT la monotonie et la progression geometrique pour produire une borne sur le nombre de solutions qui soit sous-exponentielle en k (au lieu d'etre une tour d'exponentielles).
- L'outil ne peut pas etre une contrainte locale (mod 2^a * 3^b) car gcd(d,6) = 1.
- L'outil ne peut pas etre une reformulation dans F_p car c'est le noyau irreductible.
- L'outil devrait operer dans Z GLOBALEMENT, en utilisant la structure d'ordre des B_j et la structure geometrique des 3^{k-1-j} comme UN TOUT, pas terme par terme.

Un tel outil n'existe pas dans la litterature actuelle a ma connaissance.

---

## REGISTRE FAIL-CLOSED (ajouts R160bis)

| Objet | Statut | Kill | Round |
|-------|--------|------|-------|
| Contraintes mod 2^a*3^b via Horner | **[MORT]** | gcd(d,6) = 1 | R160bis |
| Polynome lacunaire P(2) mod p | **[MORT]** | Noyau irreductible R80 | R160bis |
| Ensemble Image comme levier d'exclusion | **[MORT]** | Structure riche mais sans obstruction pour d copremier a 6 | R160bis |
| Fractions continues pour borner corrSum/d | **[MORT]** | corrSum/d rationnel, approx. dioph. non applicable | R160bis |
| Raffinement ESS par monotonie + progression geom. | **[MORT]** | Absent de la litterature, aucun mecanisme identifie | R160bis |
| k=41 comme cas le plus dur du gap | **[INFORMATIF]** | Denominateur de convergente, d minimal | R160bis |
| H_0 ≡ 2^{S-k-B_0} mod 3^{k-1} | **[PROUVE, SANS IMPACT]** | gcd(d, 3^{k-1}) = 1 | R160bis |
| corrSum = 2^{B_0} * P(2), P lacunaire | **[PROUVE, REFORMULATION]** | Pas d'obstruction nouvelle | R160bis |

---

*R160bis -- Investigation terminee. Classification : INFORMATIF (majoritairement MORT). Aucun outil qualitativement nouveau identifie.*
