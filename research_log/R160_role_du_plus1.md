# R160ter — INVESTIGATION : LE ROLE DU "+1" DANS 3x+1

**Date** : 15 mars 2026
**Type** : Investigation structurelle — rigueur mathematique absolue
**Question** : Quel est le role structurel du "+1" dans la conjecture de Collatz ?
**Script** : `R160_plus1_numerics.py`

---

## SYNTHESE EXECUTIVE

Le "+1" joue **trois roles distincts**, de natures differentes :

1. **Role existentiel** (trivial) : Sans le +1, les seuls cycles sont n=0. Le +1 cree corrSum != 0, rendant les cycles non-triviaux possibles.
2. **Role de minimalite** (PROUVE, nouveau) : Pour 3x+c, n = c * corrSum_1/d. Le +1 (c=1) donne le plus petit n possible par vecteur compatible. Mais N_0(d) est *independant* de c.
3. **Role spectral** (PROUVE, deja connu en substance) : Le "+1" se manifeste comme l'involution phi: x -> 1-x dans F_p, qui connecte H a son translate 1-H. L'element 2^{-1} = (p+1)/2 est un point fixe universel de cette involution dans H.

**Impact sur le verrou** : AUCUN NOUVEAU LEVIER. Les identites Sum = Prod = r mod p sont elementaires (geometrie + derivee cyclotomique). L'intersection H cap (1-H) ne fournit pas de nouvelle obstruction. Le "+1" n'est pas un objet autonome exploitable pour le gap k=22..41.

---

## AXE A : L'INVOLUTION phi: x -> 1-x DANS F_p

### A.1 Definition et proprietes

L'application phi(x) = 1-x est une involution du groupe additif (Z/pZ, +). Elle echange le sous-groupe multiplicatif H = <2> avec son translate 1-H = {1-h : h in H}.

**Probleme** : Quand H cap (1-H) est-il non-vide, et de quelle taille ?

### A.2 Point fixe universel — PROUVE

**Theoreme** : L'element 2^{-1} mod p = (p+1)/2 est TOUJOURS dans H cap (1-H).

*Preuve* :
- 2^{-1} = 2^{r-1} in H (car 2^r = 1 mod p).
- 1 - 2^{-1} = (2 - 1) * 2^{-1} = 2^{-1}.
- Donc 2^{-1} est un point fixe de phi dans H. QED.

**Statut** : PROUVE. Elementaire.

### A.3 Taille de l'intersection — CALCUL NUMERIQUE

| p | r | g | |H cap (1-H)| | ratio |
|---|---|---|---|---|
| 5 | 4 | 1 | 3 | 0.750 |
| 7 | 3 | 2 | 1 | 0.333 |
| 11 | 10 | 1 | 9 | 0.900 |
| 31 | 5 | 6 | 1 | 0.200 |
| 89 | 11 | 8 | 1 | 0.091 |
| 127 | 7 | 18 | 1 | 0.143 |
| 271 | 135 | 2 | 67 | 0.496 |
| 433 | 72 | 6 | 11 | 0.153 |
| 1753 | 146 | 12 | 15 | 0.103 |

**Patterns observes** :
- Si 2 est racine primitive (r = p-1, g = 1) : |H cap (1-H)| = r-1 (trivial, H = F_p*).
- Si g = 2 : |H cap (1-H)| ~ (r-1)/2 (environ la moitie).
- Si g grand : |H cap (1-H)| peut etre aussi petit que 1 (le point fixe 2^{-1} seul).

**Interpretation** : h in H cap (1-H) signifie h + h' = 1 avec h, h' in H. C'est un cas du probleme somme-produit : l'intersection (H+H) cap {1}. Quand H est petit (g grand), cette intersection est minimale (generiquement 1 element). Ceci est COHERENT avec les bornes somme-produit de Bourgain-Katz-Tao (2004) : si H est un sous-groupe de taille |H| = p^delta avec delta < 1, alors |H+H| >> |H|^{1+epsilon}, ce qui rend H+H "gros" et 1 in H+H "generique" mais avec peu de representations.

**Statut** : OBSERVE. Pas de lien direct avec le verrou.

### A.4 Lien avec le probleme somme-produit

Les paires (h, h') in H x H avec h + h' = 1 comptent les representations de 1 comme somme de deux elements de H. Le nombre de telles paires est exactement |H cap (1-H)| (par la bijection h -> (h, 1-h)).

Ce nombre est lie a l'energie additive restreinte E^+(H, {1}) = |{(h1, h2) in H^2 : h1 + h2 = 1}|.

Pour le verrou : ceci ne fournit pas de borne exploitable sur N_0(d), car la question de divisibilite d | corrSum est INDEPENDANTE de la structure de H cap (1-H).

---

## AXE B : LA DECOMPOSITION corrSum VIA LE +1

### B.1 Sans le +1 : cycles triviaux uniquement

Pour la map 3x (sans +1), l'equation de cycle serait :
n * (2^S - 3^k) = 0, donc n = 0 (car d = 2^S - 3^k != 0 pour k >= 1).

Le "+1" cree corrSum = Sum_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j} > 0.

**Statut** : TRIVIAL. Connu.

### B.2 corrSum_c = c * corrSum_1 — PROUVE

Pour la map generalisee 3x+c (c impair) :

L'equation de cycle est n * d = c * corrSum_1.

*Preuve* : L'iteration de 3x+c sur k pas donne :
n_0 = 3^k * n_0 / 2^S + c * Sum_{j=0}^{k-1} 3^{k-1-j} / 2^{S_j}

En multipliant par 2^S : n_0 * (2^S - 3^k) = c * corrSum_1.

**Consequence 1** : d | corrSum_c ssi d | corrSum_1 (car gcd(c, d) = 1 quand c est impair et premier a 3, et d est impair).

**Consequence 2** : N_0(d) est INDEPENDANT de c. Le "+1" n'a aucun role special pour le comptage des vecteurs cycle-compatibles. Tout c impair premier a 3 donne le meme N_0(d).

**Consequence 3** : n = c * corrSum_1 / d. Pour c = 1, on obtient le plus petit |n| possible. C'est le role de MINIMALITE du +1.

**Statut** : PROUVE. Impact sur le verrou : AUCUN (N_0(d) inchange).

### B.3 Le +1 comme unique source de n

corrSum/d = n est la SEULE source du nombre dans le cycle. Chaque "+1" a l'etape j est amplifie par le facteur 3^{k-1-j} (triplements restants) et divise par 2^{Sum_{i>j} a_i} (halvings restants). La contribution de l'etape j au total est donc 3^{k-1-j} * 2^{B_j}, ou B_j encode l'histoire des divisions par 2.

C'est exactement la structure de Horner etudiee en R160bis (direction 2 S-unit). Pas de nouveau contenu ici.

---

## AXE C : LE "+1" COMME PONT ADDITIF/MULTIPLICATIF

### C.1 La translation par 3^{-1}

3n + 1 = 3(n + 3^{-1}) dans Q. En modulaire : 3n + 1 = 3(n + 3^{-1}) mod p, ou 3^{-1} = (p+1)/3 si p = 2 mod 3.

La translation par 3^{-1} dans (Z/pZ, +) est "interne" a H si et seulement si 3^{-1} in H, ce qui equivaut a 3 in H.

### C.2 Dichotomie 3 in H / 3 not in H

Deja etudiee en T163 (R101). Resultats :
- Si 3 in H : la map 3x+1 preserve la structure coset de H (translation interne).
- Si 3 not in H : la map melange les cosets (translation externe).

Les donnees numeriques confirment : pour les premiers p | d(k), k=22..25, la repartition 3 in H / 3 not in H est mixte.

**Statut** : DEJA CONNU (T163, R101). Pas de nouveau contenu.

### C.3 Lien avec le +1

Le fait que 3n+1 = 3(n + 3^{-1}) montre que le "+1" est une translation par 3^{-1} APRES multiplication par 3. La dichotomie 3 in H / 3 not in H determine si cette translation est "visible" dans la structure de H ou non. Mais ceci est deja capture par T163.

**Impact sur le verrou** : AUCUN NOUVEAU LEVIER.

---

## AXE D : POURQUOI "+1" ET PAS "+c" ?

### D.1 Resultat central

**PROUVE** (Axe B.2) : N_0(d) ne depend pas de c. Pour la question "existe-t-il un cycle de longueur k ?", le +1 est interchangeable avec tout +c (c impair, gcd(c,3)=1).

### D.2 Ce qui change avec c

- La VALEUR de n dans le cycle : n = c * corrSum_1 / d.
- L'EXISTENCE de n > 0 est automatique (corrSum_1 > 0 pour tout vecteur valide).
- L'INTEGERITE n in Z : d | (c * corrSum_1), equivalente a d | corrSum_1 (car gcd(c,d)=1).
- La TAILLE de n : proportionnelle a c.

### D.3 Le +1 est optimal pour la minimalite

Parmi les maps 3x+c, c=1 minimise |n| pour chaque vecteur compatible. C'est le seul sens dans lequel le "+1" est "special" : il produit les plus petits cycles possibles.

Pour la conjecture (absence de cycles non-triviaux avec k >= 2), la minimalite de n n'aide pas directement : il faut prouver N_0(d) = 0, ce qui est independant de c.

**Statut** : PROUVE. Pas d'impact sur le verrou.

---

## AXE E : LE "+1" DANS L'IDENTITE PRODUIT

### E.1 L'identite Prod(1-2^a) = r mod p — PROUVE (elementaire)

**Theoreme** : Prod_{a=1}^{r-1} (1 - 2^a) = r mod p.

*Preuve* : H = {x in F_p* : x^r = 1}, donc x^r - 1 = Prod_{h in H} (x - h) dans F_p[x].

Derivee : r * x^{r-1} = Sum_{h in H} Prod_{h' != h} (x - h').

Evaluer en x = 1 (racine de x^r - 1) :
r * 1^{r-1} = Prod_{h in H, h != 1} (1 - h) = Prod_{a=1}^{r-1} (1 - 2^a). QED.

C'est un cas particulier de l'**identite de la derivee cyclotomique** : pour tout sous-groupe cyclique G d'ordre n dans F_p*, et tout g in G, Prod_{h in G, h != g} (g - h) = n * g^{n-1}.

**Statut** : PROUVE. Elementaire (calcul de derivee d'un polynome scinde).

### E.2 L'identite Sum(1-2^a) = r mod p — PROUVE (elementaire)

**Theoreme** : Sum_{a=1}^{r-1} (1 - 2^a) = r mod p.

*Preuve* :
Sum = (r-1) - Sum_{a=1}^{r-1} 2^a = (r-1) - (2^r - 2)/(2 - 1) = (r-1) - (1 - 2) = r mod p.

(On utilise 2^r = 1 mod p et la formule de la somme geometrique.) QED.

**Statut** : PROUVE. Elementaire (somme geometrique).

### E.3 Coincidence Sum = Prod = r — PAS UNE STRUCTURE PROFONDE

Les deux identites Sum = r et Prod = r sont prouvees par des arguments INDEPENDANTS :
- Sum = r : somme geometrique + definition de l'ordre.
- Prod = r : derivee du polynome cyclotomique.

La coincidence n'est pas un signe de structure profonde. Elle est verifiee pour les 44/44 premiers testes (p < 200) et pour tous les premiers p | d(k), k=22..25.

**Statut** : PROUVE. Coincidence elementaire, pas de profondeur.

### E.4 Sommes de puissances — PROUVE (trivial pour k < r)

**Theoreme** : Sum_{a=1}^{r-1} (1 - 2^a)^k = r mod p pour tout 1 <= k < r.

*Preuve* : Par expansion binomiale :
Sum_{h in H} (1-h)^k = Sum_{j=0}^{k} C(k,j)(-1)^j Sum_{h in H} h^j.

L'identite d'orthogonalite sur le groupe cyclique H donne :
Sum_{h in H} h^j = r si r | j, 0 sinon.

Pour 1 <= k < r, le seul j avec r | j et 0 <= j <= k est j = 0. Donc :
Sum_{h in H} (1-h)^k = r * C(k,0) * 1 = r.

En retirant le terme h = 1 (qui contribue 0^k = 0) : Sum_{a=1}^{r-1} (1-2^a)^k = r. QED.

Pour k >= r, des termes supplementaires apparaissent :
Sum = r * Sum_{m >= 0, mr <= k} C(k, mr) * (-1)^{mr}.

**Verification numerique** : Pour p = 5, r = 4, k = 4 : la somme donne 3 (pas 4), confirmant la deviation pour k = r.

**Statut** : PROUVE. Consequence triviale de l'orthogonalite des caracteres sur un groupe cyclique.

### E.5 Polynomes symetriques elementaires — Newton's identities

Les identites de Newton connectent les sommes de puissances p_k = Sum x_i^k aux polynomes symetriques elementaires e_j des elements {1 - 2^a}.

Faits verifies numeriquement :
- e_1 = Sum(1-2^a) = r mod p (= p_1).
- e_n = Prod(1-2^a) = r mod p (ou n = r-1).
- p_k = r pour tout 1 <= k < r.

Les polynomes symetriques e_j pour j intermediate ne suivent pas de pattern simple (e.g., pour p=31 : e_1=5, e_2=21, e_3=35, e_4=5 — les coefficients binomiaux C(r-1, j) mod p).

En fait, pour p = 2^r - 1 (premiers de Mersenne), les elements {1-2^a} mod p = {-2^a + 1} = {p + 1 - 2^a} = {2^r - 2^a}, et les polynomes symetriques elementaires de {2^r - 2^a : a=1..r-1} suivent les coefficients binomiaux. Ceci est un artifact des premiers de Mersenne, pas une structure generale.

**Statut** : PROUVE (Newton's identities). Pas de structure nouvelle exploitable.

---

## AXE F : DONNEES NUMERIQUES POUR p | d(k), k=22..25

### F.1 Resultats complets

| k | p | r | g | |H cap (1-H)| | Prod=r | Sum=r | 3 in H |
|---|---|---|---|---|---|---|---|
| 22 | 11 | 10 | 1 | 9 | OUI | OUI | OUI |
| 22 | 271 | 135 | 2 | 67 | OUI | OUI | NON |
| 22 | 1621 | 1620 | 1 | 1619 | OUI | OUI | OUI |
| 22 | 7727 | 3863 | 2 | 1931 | OUI | OUI | OUI |
| 23 | 3623 | 1811 | 2 | 905 | OUI | OUI | OUI |
| 24 | 5 | 4 | 1 | 3 | OUI | OUI | OUI |
| 24 | 41 | 20 | 2 | 9 | OUI | OUI | NON |
| 24 | 59 | 58 | 1 | 57 | OUI | OUI | OUI |
| 24 | 89 | 11 | 8 | 1 | OUI | OUI | NON |
| 24 | 433 | 72 | 6 | 11 | OUI | OUI | NON |
| 24 | 1753 | 146 | 12 | 15 | OUI | OUI | NON |
| 25 | 29 | 28 | 1 | 27 | OUI | OUI | OUI |

### F.2 Observations

1. **Sum = Prod = r mod p** : verifie 100% (44/44 premiers < 200, + tous p | d(k)).
2. **|H cap (1-H)|** : varie enormement. Quand g = 1 (racine primitive), |H cap (1-H)| = r-1. Quand g >> 1, peut descendre a 1.
3. **3 in H** : mixte. Pour p = 89 (r=11, g=8), 3 not in H et |H cap (1-H)| = 1. C'est le cas le plus "rigide" — l'intersection minimale avec la translation externe.
4. **Toutes les sommes de puissances p_k = r** pour k = 1..4, ce qui est coherent avec k < r dans tous les cas testes (r >= 3 > 4 est faux pour r=3 seulement, mais p=7 avec r=3 et k=4>r est hors du tableau Part 1).

---

## BILAN : IMPACT SUR LE VERROU

### Ce qui est PROUVE et NOUVEAU

1. **corrSum_c = c * corrSum_1** : N_0(d) ne depend pas du "+1" (independant de c).
2. **Point fixe universel** : 2^{-1} in H cap (1-H) toujours. L'involution phi a un point fixe dans H.
3. **Coincidence Sum = Prod = r expliquee** : deux identites elementaires independantes (geometrie + derivee cyclotomique).
4. **Sommes de puissances = r pour k < r** : consequence triviale de l'orthogonalite.

### Ce qui est MORT

1. L'intersection H cap (1-H) ne donne pas de nouvelle obstruction sur N_0(d).
2. Les identites Sum = Prod = r sont elementaires, pas exploitables.
3. La translation par 3^{-1} retombe sur T163 (deja connu).
4. Le role du "+1" dans corrSum est purement lineaire (facteur c), sans contenu structurel nouveau.

### Ce qui est DEJA CONNU et redecouvert

- T163 (dichotomie 3 in H / 3 not in H) — R101.
- E^x(H-1) energie multiplicative du translate — T171, R132.
- Transport W_1(H, H-1) = r — R158 (MORT).
- Orthogonalite des caracteres sur groupe cyclique — standard.
- Derivee cyclotomique — standard (cf. Lang, Algebra).

### Verdict

Le "+1" dans 3x+1 est un **objet transparent** : son role est entierement capture par des identites elementaires (linearite de corrSum en c, derivee cyclotomique, orthogonalite). Il ne recele pas de structure cachee exploitable pour le verrou k=22..41.

La seule "surprise" (qui n'en est pas une) est la coincidence Sum = Prod = r, qui est expliquee par deux raisons independantes.

**PISTE FERMEE.** Le "+1" n'est pas un objet autonome strategiquement utile.

---

## REFERENCES

- Lang, S. *Algebra* (derivee cyclotomique, Ch. VI).
- Bourgain, J., Katz, N., Tao, T. (2004) *A sum-product estimate in finite fields* (somme-produit).
- T163 (R101) : dichotomie 3 in H / 3 not in H.
- T171 (R132) : energie multiplicative E^x(H-1).
- R158 : transport optimal W_1(H, H-1) = r (MORT).
- R160bis : structure de Horner de corrSum dans Z.
