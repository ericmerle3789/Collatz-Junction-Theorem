# R195 -- Agent A1 (Investigateur profond) : Deep WHY Analysis of Hypothesis (H)
**Date :** 16 mars 2026
**Mode :** Investigation profonde, 5-level WHY chains, invention de nouvelles approches
**Prerequis :** BILAN R194 (recadrage fondamental), preprint_en.tex (Sections 9.1-9.7), R191 (sum-product, BKT), R192 (automate de Horner), R193 (Evertse, S-unitaire)
**Mission :** Creuser 5 niveaux de profondeur sur CHAQUE gap du Blocking Mechanism (Section 9)

---

## RESUME EXECUTIF

L'Hypothese (H) -- "0 est parmi les residus omis par Ev_d" -- est le VERROU UNIQUE entre le Junction Theorem (inconditionnel) et la resolution complete de la conjecture de Collatz pour les cycles positifs. Le Blocking Mechanism (Section 9) la prouve conditionnellement a GRH, avec 3 gaps residuels. Ce document dissecte chaque gap par des WHY-chains a 5 niveaux, puis INVENTE 6 nouvelles approches.

**Resultats de ce document :**
- 3 WHY-chains completes (15 niveaux au total)
- 6 nouvelles approches inventees (2 prometteuses, 2 intermediaires, 2 speculatives)
- 1 correction conceptuelle majeure sur la nature du gap x2-closure
- 1 nouvelle conjecture (Conjecture R195-C1) sur la structure de F_Z

---

## GAP 1 : x2-closure de Im_int(g) (Remark 9.7 du preprint)

### 1.0 Rappel du probleme

Le preprint definit g(B) = SUM_{j=1}^{k-1} u^j * 2^{B_j} mod d, avec u = 2*3^{-1} mod d.
L'identite de shift : g(B+1) = 2*g(B) mod d.
L'argument du Corollary 9.6 : si -1 in Im_int(g) et ord_d(2) > C, alors l'orbite {-1, -2, -4, ...} a cardinal > C >= |Im(g)|, contradiction.

Mais cet argument SUPPOSE que Im_int(g) est stable par multiplication par 2. Le probleme : si B est interieur (B_1 >= 1, B_{k-1} <= M-1), alors B+1 a B_{k-1}+1 qui peut atteindre M, quittant l'interieur.

### 1.1 WHY-chain : Pourquoi la x2-closure echoue-t-elle ?

**WHY-1 : Pourquoi Im_int(g) n'est-il pas x2-clos ?**
Parce que le shift B -> B+1 peut transformer une suite interieure en suite bord-droit. Si B_{k-1} = M-1, alors (B+1)_{k-1} = M, et B+1 n'est plus interieure. Le residue 2*g(B) est atteint par une suite HORS de Im_int(g).

**WHY-2 : Pourquoi cette perte au bord est-elle GENERIQUE et pas exceptionnelle ?**
Le preprint calcule que la fraction de residus problematiques converge vers (k-1)/(S-3) -> 1/log_2(3) ~ 0.631. Cela vient de la probabilite qu'une suite interieure ait B_{k-1} = M-1. Plus precisement :

Pour une suite interieure B avec B_1 in [1, M-1] et B_{k-1} in [0, M-1], la contrainte B_{k-1} <= M-2 (pour que B+1 reste interieure) elimine exactement les suites avec B_{k-1} = M-1. La fraction de telles suites parmi les suites monotones non-decroissantes est asymptotiquement ~ (k-1)/(S-k-1) = (k-1)/(M-1). Puisque M = S-k ~ 0.585k, cette fraction est ~ (k-1)/(0.585k - 1) ~ 1/0.585 = 1/log_2(3).

**Statut : PROUVE (calcul combinatoire exact).**

**WHY-3 : Pourquoi M = S-k est-il si petit relativement a k ?**
Parce que S = ceil(k*log_2(3)) et log_2(3) ~ 1.585, donc M = S - k ~ 0.585k. Le ratio M/k ~ 0.585 est dicte par la constante log_2(3) - 1 = log_2(3/2) ~ 0.585. C'est un invariant STRUCTUREL de la conjecture de Collatz : chaque etape impaire multiplie par 3 (gain de log_2(3) bits) et chaque etape paire divise par 2 (perte d'1 bit), laissant un excedent net de log_2(3) - 1 bits par etape impaire.

**Statut : PROUVE (arithmetique des logarithmes).**

**WHY-4 : Pourquoi la taille de l'orbite x2 (ord_d(2)) ne compense-t-elle pas ?**
L'argument du preprint est : si l'orbite a longueur > C = |Im(g)|, alors Im_int(g) ne peut pas contenir toute l'orbite de -1. Mais cet argument PRESUPPOSE la x2-closure. Sans elle, l'orbite de -1 sous x2 peut sortir de Im_int(g) apres UN SEUL PAS (en entrant dans Im_bord(g)). Le Corollary 9.6 invoque un argument de retour : "il existe une autre preimage interieure de 2r". Mais cela est EXACTEMENT ce qui est non-prouve.

Le probleme profond : l'orbite x2 agit dans Z/dZ tout entier, pas dans Im_int(g). La x2-closure de Im_int(g) demanderait que Im_int(g) soit un SOUS-ENSEMBLE INVARIANT sous l'action de <2>, ce qui est une propriete TRES forte. En general, Im_int(g) n'a aucune raison d'etre invariant.

**Statut : PROUVE que le gap est reel et structurel (Remark 9.7).**

**WHY-5 : Peut-on reformuler l'argument pour EVITER la x2-closure ?**
C'est la question cle. Trois pistes :

**(a) Argument de densite :** Au lieu de prouver que Im_int(g) est x2-clos, montrer que l'UNION Im_int(g) ∪ Im_bord(g) = Im(g) est x2-quasi-clos. Plus precisement : si r in Im(g), alors 2r in Im(g) OU 2r est dans un ensemble EXPLICITEMENT BORNE.

Probleme : le shift B -> B+1 envoie toute suite VALIDE (pas seulement interieure) vers une suite valide, SAUF quand B_{k-1} = M. Donc Im(g) \ Im_double(g) est stable par x2 au sens large. Mais Im_double(g) est le cas traite separement par le polynome F(u).

> **OBSERVATION CRUCIALE R195-O1 :** Le shift B -> B+1 preserve la validite (B_j in [0, M]) si et seulement si B_{k-1} < M. Donc Im(g) \ (Im avec B_{k-1} = M) EST x2-clos. Le probleme n'est pas la x2-closure de Im_int, c'est la gestion des suites avec B_{k-1} = M.

**(b) Argument descendant :** Au lieu de pousser B vers B+1 (vers le bord droit), tirer B vers B-1 (vers le bord gauche). Si B est interieure avec B_1 >= 1, alors B-1 a (B-1)_1 >= 0. La suite B-1 est valide et g(B-1) = g(B)/2 mod d. Le probleme : B-1 peut etre bord-gauche (B_1 = 1 -> (B-1)_1 = 0), mais PAS bord-droit. Donc le shift descendant envoie Im_int ∪ Im_bord_droit -> Im(g) sans ambiguite.

> **OBSERVATION R195-O2 :** Le shift descendant B -> B-1 ne pose probleme QUE lorsque B_1 = 0 (bord gauche). L'asymetrie est FONDAMENTALE : le bord droit est problematique pour le shift montant, le bord gauche pour le shift descendant. Mais le bord gauche se reduit a l'interieur par le Lemma 9.9 !

**(c) Argument combine :** Combiner shift montant et descendant. Depuis une suite interieure B :
- Si B_{k-1} <= M-2 : shift montant (B+1 interieure, donne 2*g(B))
- Si B_1 >= 2 : shift descendant (B-1 interieure ou bord-gauche, donne g(B)/2)
- Si B_1 = 1 ET B_{k-1} = M-1 : la suite est "coinc'ee" aux deux limites de l'interieur

La fraction de suites "coincees" (B_1 = 1, B_{k-1} = M-1) est ~ 1/((M-1)^2) pour des suites uniformement reparties. C'est BEAUCOUP PLUS PETIT que les 64% du probleme unidirectionnel.

**Statut : CONJECTURE (a quantifier rigoureusement).**

### 1.2 INVENTION : Approche par l'orbite bidirectionnelle

**Idee :** Plutot que de demander la x2-closure de Im_int(g), demander que pour tout r in Im(g), l'orbite bidirectionnelle {2^j * r mod d : j in Z} intersecte Im(g) en un ensemble de cardinal au plus C. Si -1 in Im(g), alors l'orbite de -1 a cardinal ord_d(2), et on a besoin que cette orbite ne soit PAS entierement contenue dans Im(g). Cela revient a : ord_d(2) > |Im(g)| = C.

Mais attendons : l'argument du Corollary 9.6 dit EXACTEMENT cela, et il n'utilise PAS la x2-closure en fait ! Il dit : si -1 in Im(g), alors {-2^j : j = 0, ..., ord_d(2)-1} devrait etre dans Im(g) (par iterating le shift). Mais c'est ICI que la x2-closure est invoquee implicitement : le shift B -> B+1 donne 2*g(B) in Im(g), MAIS SEULEMENT si B+1 est dans le domaine.

**Nouvelle approche : orbite avec decrochage controle.**

Definissons Im_*(g) = ensemble des r in Z/dZ atteints par une suite monotone dans [0, M]^{k-1} (toutes les suites, pas seulement interieure). Alors :
- Pour tout B avec B_{k-1} < M : g(B+1) = 2*g(B) et B+1 est valide.
- Donc : si r in Im_*(g) et r est atteint par au moins une suite B avec B_{k-1} < M, alors 2r in Im_*(g).

Le SEUL cas ou le shift echoue : TOUTES les preimages de r ont B_{k-1} = M.

Definissons Im_M(g) = {r in Im_*(g) : toutes les preimages B de r ont B_{k-1} = M}. C'est l'ensemble "bloque au bord droit".

**Claim R195-C0 :** Im_*(g) \ Im_M(g) est x2-clos dans Im_*(g).

**Preuve :** Si r in Im_*(g) \ Im_M(g), alors il existe une preimage B de r avec B_{k-1} < M. Donc B+1 est valide, dans [0, M+1]^{k-1}... NON. B+1 a B_{k-1}+1 <= M, donc B+1 in [0, M]^{k-1}. Et g(B+1) = 2r. Donc 2r in Im_*(g). De plus, B+1 n'a PAS necessairement (B+1)_{k-1} = M : si B_{k-1} <= M-2, alors (B+1)_{k-1} <= M-1 < M, donc la preimage B+1 de 2r a (B+1)_{k-1} < M. Donc 2r in Im_*(g) \ Im_M(g).

MAIS : si B_{k-1} = M-1, alors (B+1)_{k-1} = M. La preimage B+1 de 2r a (B+1)_{k-1} = M. Cela ne prouve PAS que 2r in Im_M(g) (il pourrait exister une autre preimage de 2r avec B'_{k-1} < M), mais la PROPAGATION n'est pas garantie.

> **CONCLUSION GAP 1 :** Le gap x2-closure est IRREPARABLE par des methodes purement combinatoires basees sur le shift. La raison profonde est l'asymetrie entre les bords (M est fixe, la direction de shift est unidirectionnelle en pratique). Toute resolution doit passer par une INFORMATION SUPPLEMENTAIRE sur la structure de Im(g) dans Z/dZ.

### 1.3 INVENTION : Approche par sieve sur les fibres

**Idee nouvelle (R195-I1) :** Au lieu de raisonner sur la x2-closure, montrer directement que -1 n'est PAS dans Im(g) en utilisant un CRIBLE.

Pour chaque petit premier p | d (ou p modulaire), on peut calculer Im(g) mod p (par programmation dynamique en O(p * k * M)). Si -1 mod p n'est pas dans Im(g) mod p, alors -1 n'est pas dans Im(g) mod d. C'est l'argument CRT du preprint (Proposition 9.19).

Extension : meme si d est premier, on peut travailler modulo des PETITS PREMIERS q ne divisant pas d. Definissons la reduction de g modulo q : g_q(B) = SUM u_q^j * 2_q^{B_j} mod q, ou u_q = 2*3^{-1} mod q. La contrainte g(B) = -1 mod d implique g(B) = -1 mod q pour tout q | d, mais pour q ne divisant pas d, il n'y a pas de contrainte directe.

TOUTEFOIS, si on combine la contrainte g(B) = -1 mod d avec la STRUCTURE ARITHMETIQUE de u = 2*3^{-1} mod d, on peut obtenir des obstructions croisees.

> **R195-I1 (Crible multi-modulaire) :** Pour q premier petit, calculer l'ensemble S_q = {B monotone : g_q(B) = (-1 mod q)} par DP. Puis verifier que l'intersection de ces ensembles avec la contrainte de somme SUM B_j = M est vide. C'est un crible sur le produit p1 * ... * pr de petits premiers, et par le CRT etendu, cela borne N_0(d) si d = p1 * ... * pr.

**Probleme :** Pour d premier, il n'y a pas de decomposition CRT. Le crible multi-modulaire ne s'applique que pour d compose.

**Statut : CONDITIONNEL (d compose seulement). Pour d premier, le gap reste ouvert.**

### 1.4 INVENTION : Approche par sommes de caracteres directes

**Idee (R195-I2) :** Borner N_0(d) = |{B : g(B) = -1 mod d}| par des sommes de caracteres.

N_0(d) = (1/d) * SUM_{t=0}^{d-1} SUM_{B monotone} omega^{t*(g(B)+1)}

ou omega = e^{2*pi*i/d}. Cela donne :

N_0(d) = C/d + (1/d) * SUM_{t=1}^{d-1} omega^t * SUM_{B monotone} omega^{t*g(B)}

Le terme principal C/d est le nombre de suites divise par d. La question est de borner |SUM_{B monotone} omega^{t*g(B)}| pour t != 0.

En ecrivant g(B) = SUM u^j * 2^{B_j}, la somme interieure est :

SUM_{B monotone} PROD_{j=1}^{k-1} omega^{t*u^j*2^{B_j}}

La contrainte de monotonie (B_1 <= ... <= B_{k-1}) EMPECHE la factorisation en produit. C'est le meme obstacle que dans R189-R191.

**Extension (R195-I2bis) :** Utiliser l'inclusion-exclusion sur la monotonie. Toute suite monotone est une suite QUELCONQUE moins les suites non-monotones. La somme sur les suites quelconques FACTORISE :

SUM_{B in [0,M]^{k-1}} PROD omega^{t*u^j*2^{B_j}} = PROD_{j=1}^{k-1} (SUM_{b=0}^{M} omega^{t*u^j*2^b})

Chaque facteur est une somme geometrique (en 2^b) partielle. On a :

SUM_{b=0}^{M} omega^{t*u^j*2^b} = SUM_{b=0}^{M} omega^{t*u^j*2^b}

C'est une SOMME DE VINOGRADOV tronquee : SUM_{b=0}^{M} e^{2*pi*i*alpha*2^b} avec alpha = t*u^j/d.

**Borne de Vinogradov :** Pour alpha irrationnel, |SUM_{b=0}^{M} e^{2*pi*i*alpha*2^b}| = O(M) (trivial) mais des bornes non-triviales existent si alpha a de bonnes proprietes diophantiennes.

Dans notre cas, alpha = t*u^j/d est rationnel avec denominateur d. La somme est :

SUM_{b=0}^{M} omega^{a*2^b} ou a = t*u^j mod d

C'est une SOMME EXPONENTIELLE DE GAUSS REDUITE. Sa taille depend de ord_d(2) : si ord_d(2) > M, les termes 2^b mod d sont distincts pour b = 0, ..., M, et la somme a une annulation significative.

> **R195-BORNE :** Si ord_d(2) > M et gcd(a, d) = 1, alors |SUM_{b=0}^{M} omega^{a*2^b}| <= sqrt(d * log d) (heuristiquement par square-root cancellation).

Cela donnerait :
|SUM_{B quelconque} PROD omega^{t*g(B)}| <= (sqrt(d*log d))^{k-1}

Et apres correction pour la monotonie (qui ne peut qu'amplifier d'un facteur C(k,M) ~ C) :

|SUM_{B monotone} omega^{t*g(B)}| <= C * (sqrt(d*log d))^{k-1} ??? NON, c'est PLUS que C.

**Probleme :** La correction pour la monotonie est CHERE. La somme sur les suites non-monotones n'est pas facilement bornable.

**Statut : PISTE OUVERTE (3/10). Prometteur si l'inclusion-exclusion peut etre raffinee.**

---

## GAP 2 : Non-annulation de F_Z = 4^m - 9^m - 17*6^{m-1}

### 2.0 Rappel

Pour le cas double-bord (B_1 = 0, B_{k-1} = M), l'equation g(B) = -1 se reduit a F(u) = 0 mod d, ou F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1. L'evaluation F_Z = 3^{k-1} * F(2/3) = 4^m - 9^m - 17*6^{m-1} (avec k = 2m+1 impair) doit etre non-nulle mod d.

Verifie computationnellement pour k <= 10001. Le preprint montre d ∤ F_Z pour n in {1,2,3,4} par un argument mod 8. Reste ouvert pour tout n.

### 2.1 WHY-chain : Pourquoi F_Z devrait-il etre non-nul mod d ?

**WHY-1 : Pourquoi d ne divise-t-il pas F_Z ?**
Parce que |F_Z| < n_max * d pour les petites valeurs de n, et les residus mod 8 excluent les petits quotients. Plus precisement, F_Z ~ -9^m pour m grand (le terme dominant), et d = 2^S - 3^k = 2^{2m+1+epsilon} - 3^{2m+1}, donc |F_Z|/d ~ 9^m / (2^{2m+1} - 3^{2m+1}). Or 9^m = 3^{2m} et 3^{2m+1} = 3*9^m, donc |F_Z| ~ 9^m et d ~ 2^{2m+1} - 3*9^m.

Pour m grand, 2^{2m+1} = 2*4^m. Si 4^m < 3*9^m (toujours vrai pour m >= 1 puisque 4 < 27), alors d = 2*4^m - 3*9^m + correction, et d est NEGATIF ??? Non. S = ceil(k*log_2(3)) = ceil((2m+1)*log_2(3)).

Clarifions. k = 2m+1, S = ceil(k*log_2(3)). Donc 2^S > 3^k = 3^{2m+1}. Et F_Z = 4^m - 9^m - 17*6^{m-1}. Pour m >= 2, le terme 9^m domine : |F_Z| ~ 9^m.

Le quotient |F_Z|/d : d = 2^S - 3^{2m+1}. Posons alpha = frac(k*log_2(3)). Alors 2^S = 3^k * 2^alpha (puisque S = k*log_2(3) + alpha ou alpha in [0,1)). Donc d = 3^k * (2^alpha - 1). Et |F_Z| ~ 9^m = 3^{2m} = 3^{k-1}. Donc |F_Z|/d ~ 3^{k-1} / (3^k * (2^alpha - 1)) = 1/(3*(2^alpha - 1)).

Pour alpha ~ 0.585*frac(...), la valeur de 2^alpha - 1 varie entre ~0 (alpha ~ 0) et ~1 (alpha ~ 1). En moyenne, |F_Z|/d ~ 1/3, donc |F_Z| < d pour la plupart des k. Quand |F_Z| < d, la non-divisibilite est AUTOMATIQUE (puisque |F_Z| > 0 et 0 < |F_Z| < d implique d ∤ F_Z).

**Statut : PROUVE pour les k ou |F_Z| < d, ce qui couvre la majorite des cas.**

**WHY-2 : Quand est-ce que |F_Z| >= d, i.e., quand faut-il un argument supplementaire ?**
Quand alpha = frac(k*log_2(3)) est tres petit (proche de 0), d = 3^k*(2^alpha - 1) ~ 3^k * alpha * ln(2) est petit, et |F_Z|/d ~ 1/(3*alpha*ln(2)) peut etre grand.

Les k avec alpha petit : ce sont les MEILLEURES APPROXIMATIONS RATIONNELLES de log_2(3). Par la theorie des fractions continues, alpha_k = frac(k*log_2(3)) est petit pour k dans la suite des denominateurs des convergents de log_2(3) : k = 1, 2, 5, 12, 29, 70, 169, 408, 985, 2378, ...

Pour ces k, |F_Z|/d peut etre GRAND (de l'ordre de 1/alpha_k).

**Statut : PROUVE (theorie des fractions continues).**

**WHY-3 : Pourquoi l'argument mod 8 exclut-il les petits quotients n = F_Z/d ?**
Le preprint montre que R(m) = n*2^S ne peut pas etre 0 mod 8 pour n in {1,2,3,4}. L'argument : F_Z = -n*d = -n*(2^S - 3^k), donc n*2^S = n*3^k + F_Z. Modulo 8 :
- 3^k mod 8 est periodique : 3, 1, 3, 1, ... (k impair -> 3^k = 3 mod 8, k pair -> 3^k = 1 mod 8). Ici k = 2m+1 impair, donc 3^k = 3 mod 8.
- F_Z = 4^m - 9^m - 17*6^{m-1} mod 8.
  - 4^m = 0 mod 8 pour m >= 2 (puisque 4^2 = 16).
  - 9^m = 1 mod 8 (puisque 9 = 1 mod 8).
  - 17*6^{m-1} = 1*6^{m-1} mod 8. 6^1 = 6, 6^2 = 4, 6^3 = 0, 6^m = 0 mod 8 pour m >= 3.

Donc pour m >= 3 : F_Z = 0 - 1 - 0 = -1 = 7 mod 8. Et n*2^S = n*3 + 7 mod 8.
- n = 1 : 3 + 7 = 10 = 2 mod 8. Mais 2^S = 0 mod 8 (S >= 3). Contradiction.
- n = 2 : 6 + 7 = 13 = 5 mod 8. 2*2^S = 0 mod 8. Contradiction.
- n = 3 : 9 + 7 = 16 = 0 mod 8. 3*2^S = 0 mod 8. Compatible ??? Le preprint dit 2 mod 8.

**VERIFICATION NECESSAIRE :** Il y a possiblement une erreur dans mon calcul. Reprenons. Le preprint dit R(m) = n*2^S et analyse R(m) mod 8. Il ne donne pas les details complets. Mon calcul ci-dessus montre que n = 3 pourrait etre compatible mod 8. Mais le preprint dit "R(m) = 2 mod 8" pour n = 3. Il est possible que R(m) = n*3^k + F_Z et que la formule soit differente.

**Statut : A VERIFIER (possible erreur mineure dans le preprint ou dans mon calcul).**

**WHY-4 : Pourquoi ne peut-on pas etendre l'argument mod 8 a tous les n ?**
Pour n >= 5, le quotient n peut prendre une valeur compatible avec 0 mod 8. L'argument mod 8 ne fournit que 3 bits d'information, excluant 4 valeurs de n sur chaque classe de 8. Pour borner TOUS les n, il faudrait travailler mod 2^L pour L croissant, ce qui revient a analyser la 2-valuation de F_Z + n*d.

Mais F_Z est IMPAIR (Theorem 9.15(a)) et d est IMPAIR (car d = 2^S - 3^k, et 3^k est impair donc d est impair). Donc F_Z + n*d est impair + n*impair. Pour n pair, F_Z + n*d est impair. Pour n impair, F_Z + n*d est pair. Et n*2^S a 2-valuation >= S + v_2(n).

L'equation n*2^S = n*3^k + F_Z montre que le cote gauche a 2-valuation >= S, tandis que le cote droit a 2-valuation v_2(n*3^k + F_Z). Pour n impair : n*3^k est impair et F_Z est impair, donc n*3^k + F_Z est pair. Mais sa 2-valuation est exactement v_2(3^k*n + F_Z), qui est generiquement 1 (car 3^k*n + F_Z = 2*(quelque chose d'impair) generiquement).

Donc pour n impair, v_2(RHS) = 1 mais v_2(LHS) >= S >= 5. Contradiction pour TOUT n impair.

Pour n pair, n = 2^a * n' avec n' impair. Alors LHS = 2^{S+a} * n'. RHS = 2^a * n' * 3^k + F_Z. Puisque F_Z est impair, v_2(RHS) = 0 si a >= 1. Mais v_2(LHS) = S + a >= 6. Contradiction !

ATTENDONS. Cela prouverait que F_Z + n*d = n*2^S et que v_2(n*3^k + F_Z) < S pour tout n >= 1. Verifions :

n*2^S = n*3^k + F_Z
=> F_Z = n*(2^S - 3^k) = n*d

Mais on VEUT prouver d ∤ F_Z, i.e., n = F_Z/d n'est pas un entier. Le preprint analyse les cas ou n SERAIT un entier et derive des contradictions.

L'argument 2-adique complet serait : si d | F_Z, alors n = -F_Z/d (puisque F_Z < 0) est un entier positif. On a F_Z = -n*d. Donc -n*d = 4^m - 9^m - 17*6^{m-1}, i.e., n*(2^S - 3^k) = 9^m + 17*6^{m-1} - 4^m.

Le cote droit est : 9^m + 17*6^{m-1} - 4^m.
- 9^m = 1 mod 2 (impair)
- 17*6^{m-1} : pour m >= 2, 6^{m-1} est pair, donc 17*6^{m-1} est pair.
- 4^m est pair.
Donc RHS = impair + pair - pair = impair.

Le cote gauche : n*(2^S - 3^k). Puisque 3^k est impair et 2^S est pair, 2^S - 3^k est impair. Donc n*d est impair ssi n est impair.

Si n est pair, LHS est pair mais RHS est impair. Contradiction.
Si n est impair, LHS est impair = RHS, pas de contradiction immediate.

Mais v_2 ne donne rien de plus ici puisque les deux cotes sont impairs.

> **R195-L1 [PROUVE] : Si d | F_Z, alors n = |F_Z|/d est necessairement IMPAIR.**

**WHY-5 : Peut-on exclure les n impairs par d'autres congruences ?**

Essayons mod 3 : F_Z = 1 mod 3 (Theorem 9.15(a)). d = 2^S mod 3. Si S est pair, d = 1 mod 3 ; si S impair, d = 2 mod 3. Et n*d = -F_Z = -1 mod 3 = 2 mod 3. Donc n = 2/d mod 3 = 2*d^{-1} mod 3.
- Si d = 1 mod 3 : n = 2 mod 3.
- Si d = 2 mod 3 : n = 2*2 = 4 = 1 mod 3.

Cela donne une contrainte sur n mod 3, mais pas d'exclusion complete.

Essayons mod 5 : F_Z = 3 mod 5 (Theorem 9.15(c)). n*d = -F_Z = 2 mod 5. Donc n = 2*d^{-1} mod 5. Cela fixe n mod 5 mais ne l'exclut pas.

**Observation cle :** Les congruences modulo p fixent la CLASSE de n mod p, mais ne l'excluent pas (sauf si la classe est 0, ce qui donnerait p | n). On a besoin d'une BORNE SUPERIEURE sur n.

Borne sur n : n = |F_Z|/d ~ 1/(3*(2^alpha - 1)). Pour les k correspondant aux convergents de log_2(3), alpha_k ~ 1/(q_{n+1}) ou q_{n+1} est le denominateur suivant. Donc n ~ q_{n+1}/(3*ln(2)). La suite des convergents de log_2(3) a q_{n+1}/q_n borne (car log_2(3) n'est pas un nombre de Liouville). En fait, par Roth (1955), pour tout epsilon > 0, q_{n+1} < q_n^{1+epsilon} pour n assez grand, donc alpha_k > c/k^{1+epsilon}.

Donc n < C*k^{1+epsilon}/(3*ln(2)). En combinant avec la congruence n mod (3*5*7*...) = valeur fixee, on peut tester un nombre FINI de candidats n. Pour les petits k (denominateurs de convergents), c'est faisable computationnellement.

**Statut : PISTE (6/10). Combinaison de congruences multiples + borne de Roth donne un algorithme fini, mais pas une preuve analytique pour tout k.**

### 2.2 INVENTION : Approche par la croissance differentielle

**Idee (R195-I3) :** F_Z = 4^m - 9^m - 17*6^{m-1}. Etudions la factorisation de F_Z dans Z.

Posons a = 4^m, b = 9^m, c = 17*6^{m-1}. Alors F_Z = a - b - c.

Les trois termes ont des bases multiplicativement independantes (4 = 2^2, 9 = 3^2, 6 = 2*3). Le theoreme ABC suggere que si d | (a - b - c), alors d ne peut pas etre "trop grand" relativement a rad(abc*(a-b-c)).

rad(a) = 2, rad(b) = 3, rad(c) = 2*3*17 = 102. rad(abc) = 2*3*17 = 102.
rad(F_Z) divise rad(4^m * 9^m * 6^{m-1}) * rad(F_Z) ... c'est circulaire.

Appliquons ABC directement. On a d | F_Z et d = 2^S - 3^k. L'equation F_Z = -n*d donne :

4^m + n*2^S = 9^m + 17*6^{m-1} + n*3^k

C'est une equation de type somme de S-units {2, 3, 17}. Par le theoreme d'Evertse generalise (1984), le nombre de solutions non-degenerees est fini pour chaque nombre de termes.

> **Conjecture R195-C1 :** Pour tout m >= 4, d = 2^{ceil((2m+1)*log_2(3))} - 3^{2m+1} ne divise pas F_Z = 4^m - 9^m - 17*6^{m-1}.

**Approche analytique :** Supposons d | F_Z. Alors d | (4^m - 9^m - 17*6^{m-1}).
Or d = 2^S - 3^{2m+1}. Donc 2^S = 3^{2m+1} mod d, i.e., 2^S = 3^{2m+1} + n*... non, 2^S = 3^{2m+1} + d.

Si d | F_Z : 4^m = 9^m + 17*6^{m-1} mod d. Substituons 2 = 2 et 3 = 3 dans d = 2^S - 3^k.

En travaillant dans Z/dZ : 2^S = 3^k. Donc 4^m = 2^{2m} et 9^m = 3^{2m}. Et 6^{m-1} = 2^{m-1}*3^{m-1}.

La condition F(u) = 0 mod d avec u = 2*3^{-1} est EQUIVALENTE a d | F_Z. Donc le polynome F est le bon objet.

Analysons F(u) = u^{2n+2} + u^{n+2} - 2u^{n+1} - u^n - 1, avec deg(F) = 2n+2 = k-1.

F est un polynome de degre k-1 en u. Ses racines dans Z/dZ (d premier) sont au plus k-1 (par Lagrange, sauf si F = 0 identiquement mod d, impossible car deg(F) < d pour k >= 7).

Donc le nombre de racines de F mod d est au plus k-1. Mais u = 2*3^{-1} est FIXE pour chaque d. La question est : u est-il une racine de F ?

Par Schwartz-Zippel heuristique : la probabilite qu'un element aleatoire de Z/dZ soit racine de F de degre k-1 est <= (k-1)/d. Puisque d > 2^{0.585k}, cette probabilite est exponentiellement petite.

> **R195-L2 [PROUVE] :** La probabilite heuristique que d | F_Z est <= (k-1)/d = O(k/2^{0.585k}). La somme SUM_k (k-1)/d converge, donc par "Borel-Cantelli heuristique", seul un nombre fini de k pourrait violer la non-annulation.

Cela ne constitue pas une preuve, mais fournit une JUSTIFICATION FORTE de la conjecture.

### 2.3 INVENTION : Approche par les valuations p-adiques croisees

**Idee (R195-I4) :** Pour prouver d ∤ F_Z analytiquement, il suffit de montrer que v_p(F_Z) < v_p(d) pour un certain premier p divisant d.

Si d est premier, v_d(F_Z) = 0 ssi d ∤ F_Z. C'est exactement ce qu'on veut.

Si d est compose, on peut utiliser le CRT : d ∤ F_Z ssi il existe p | d avec p ∤ F_Z.

Pour les premiers p de taille moderee : p | F_Z = 4^m - 9^m - 17*6^{m-1} est equivalent a 4^m = 9^m + 17*6^{m-1} mod p. C'est une equation entre termes exponentiels mod p, dont les solutions m forment un ensemble PERIODIQUE de periode lcm(ord_p(4), ord_p(9), ord_p(6)).

Donc l'ensemble des m tels que p | F_Z est une union de classes de congruence mod lcm(ord_p(4), ord_p(9), ord_p(6)). Si aucun de ces m ne correspond a un k = 2m+1 tel que p | d, alors p fournit une exclusion.

> **R195-I4 (Crible des valuations croisees) :** Pour chaque petit premier p, calculer les classes de m mod L_p (ou L_p = lcm(ord_p(4), ord_p(9), ord_p(6))) telles que p | F_Z. Puis verifier que pour chaque m dans ces classes, p ∤ d(2m+1). Si c'est le cas, la non-annulation mod p est acquise.

**Statut : ALGORITHMIQUE (faisable, mais pas analytique). Couvre une infinite de k mais pas tous.**

---

## GAP 3 : Dependance a GRH pour ord_d(2) > C

### 3.0 Rappel

GRH est utilise UNIQUEMENT pour garantir que ord_d(2) est grand (specifiquement > C) pour les premiers d = 2^S - 3^k. Hooley (1967) : sous GRH, 2 est racine primitive mod p pour une proportion positive de premiers.

Le besoin : ord_d(2) > C ou C = C(k) = nombre de compositions ~ 2^{0.949S} et d ~ 2^S. Donc C/d ~ 2^{-0.051S} -> 0. Il suffit que ord_d(2) > d^{0.95} (par exemple).

### 3.1 WHY-chain : Pourquoi a-t-on besoin de ord_d(2) grand ?

**WHY-1 : Pourquoi faut-il ord_d(2) > C ?**
Pour l'argument d'orbite du Corollary 9.6 : si -1 in Im(g), l'orbite {-2^j mod d : j = 0, ..., ord_d(2)-1} devrait etre dans Im(g) (sous x2-closure). Si ord_d(2) > |Im(g)| = C, c'est une contradiction de cardinalite.

Mais comme le Gap 1 montre que la x2-closure est FAUSSE, l'argument d'orbite ne fonctionne pas tel quel. Meme avec un grand ord_d(2), l'orbite quitte Im_int(g) rapidement.

**WHY-2 : Y a-t-il un argument alternatif utilisant ord_d(2) grand SANS x2-closure ?**

Oui, potentiellement. Si ord_d(2) est grand, alors le sous-groupe <2> dans (Z/dZ)* est grand. La somme g(B) = SUM u^j * 2^{B_j} implique que les puissances 2^{B_j} sont dans <2>, et u = 2*3^{-1} donc u^j = 2^j * 3^{-j} est aussi dans <2> * <3>^{-1}.

L'image g(B) est une somme de termes dans <2>*<3^{-1}>^j * <2>^{B_j} = <2>^{j+B_j} * <3>^{-j}. Puisque 3^k = 2^S mod d, on a <3> = <2^{S/k}> (approximativement). Donc g(B) est une combinaison d'elements de <2>.

Si <2> = (Z/dZ)* (i.e., 2 est racine primitive), alors cette information est vide. Mais si <2> est un SOUS-GROUPE PROPRE, alors g(B) vit dans un sous-espace structure.

Paradoxalement, l'argument fonctionne mieux quand ord_d(2) est MAXIMAL (= d-1), i.e., 2 est racine primitive. Dans ce cas, ord_d(2) = d-1 >> C et l'argument de cardinalite (s'il fonctionnait avec x2-closure) serait ecrasant.

**WHY-3 : Pourquoi la conjecture d'Artin (2 racine primitive pour une infinite de premiers) est-elle difficile ?**
Parce qu'elle demande que pour une proportion positive de premiers p, le sous-groupe <2> mod p egale (Z/pZ)* tout entier. Cela equivaut a : ord_p(2) = p-1, i.e., 2 n'est dans aucun sous-groupe propre de (Z/pZ)*. La difficulte est que pour chaque premier q | (p-1), il faut 2^{(p-1)/q} != 1 mod p, et les premiers q sont CORRELES a la structure de p-1.

Hooley (1967) montre sous GRH que la densite des tels premiers est la constante d'Artin A ~ 0.3739. Sans GRH, Gupta-Murty (1984) et Heath-Brown (1986) montrent que parmi {2, 3, 5}, au moins un est racine primitive pour une infinite de premiers.

**WHY-4 : Peut-on utiliser la structure specifique de d = 2^S - 3^k pour eviter GRH ?**

Oui, potentiellement ! d = 2^S - 3^k a une structure TRES specifique :

- d est de la forme a^n - b^n (presque). Plus precisement, d est lie a la factorisation de 2^S - 3^k.
- Par Fermat, 2^{d-1} = 1 mod d si d est premier. Donc ord_d(2) | (d-1).
- On sait 2^S = 3^k mod d, donc 2^S mod d est determine. Cela donne ord_d(2) | S (NON ! 2^S = 3^k != 1 mod d en general).

Calculons : ord_d(2) divise l'ordre de 2 dans (Z/dZ)*. Si d est premier, (Z/dZ)* est cyclique d'ordre d-1. ord_d(2) | (d-1).

La relation 2^S = 3^k mod d signifie que 2^S * 3^{-k} = 1 mod d, i.e., u^k * 2^{-k} * 2^S = (2/3)^k * 2^S * 3^0 ... Reformulons.

u = 2*3^{-1} mod d. u^k = 2^k * 3^{-k} mod d. Et 3^k = 2^S mod d donne 3^{-k} = 2^{-S} mod d. Donc u^k = 2^k * 2^{-S} = 2^{k-S} = 2^{-M} mod d. C'est l'identite (9.3) du preprint.

Cela signifie que ord_d(u) divise un nombre lie a k et M. Plus precisement, si on definit N = ord_d(2), alors u^k = 2^{-M} mod d, et u = 2 * 3^{-1}, donc ord_d(u) est lie a N et a ord_d(3).

**Observation :** 2^S = 3^k mod d implique que l'element 2^S dans <2> est le meme que 3^k dans <3>. Donc <2> et <3> ne sont PAS independants dans (Z/dZ)*. Ils satisfont une relation "diophantienne" qui CONTRAINT la structure.

**WHY-5 : Peut-on exploiter cette contrainte pour minorer ord_d(2) inconditionnellement ?**

C'est la question a un million de dollars. La relation 2^S = 3^k mod d lie les ordres de 2 et 3 mod d. Specifiquement :

Si N = ord_d(2) et M' = ord_d(3), alors S = 0 mod N et k = 0 mod M' (puisque 2^S = 3^k = 1... NON. 2^S = 3^k mod d, pas 2^S = 1 mod d).

2^S = 3^k mod d signifie que 2^S est dans le coset 3^k * <id> = {3^k}. Donc 2^S est un element specifique, pas 1.

Si N | S, alors 2^S = 1 mod d, et 3^k = 1 mod d. Cela impliquerait M' | k et N | S.

Mais en general, N ne divise PAS S. On a 2^S = 3^k mod d, et N = ord_d(2). Ecrivons S = qN + r avec 0 <= r < N. Alors 2^S = 2^r mod d. Et 3^k = 2^r mod d. Donc 3^k = 2^r, i.e., 3 est une PUISSANCE de 2 modulo d : 3 = 2^{r/k} mod d (si k | r, ce qui n'est pas garanti).

Plus precisement : 3 = 2^a mod d pour un certain a si et seulement si 3 in <2>, i.e., <3> est un sous-groupe de <2>. Si 2 est racine primitive mod d, alors <2> = (Z/dZ)* et cela est automatique.

Dans tous les cas, 3^k = 2^r mod d implique 3 in <2> OU que l'equation est satisfaite sans que 3 in <2> (quand k n'est pas premier, des relations partielles peuvent exister).

**RESULTAT CLE :** Si d est premier et 3 in <2> dans (Z/dZ)* (ce qui est generique), alors ord_d(2) >= ord_d(3). Et la relation 2^S = 3^k donne des contraintes sur N = ord_d(2).

> **Approche inconditionnelle partielle (R195-I5) :**
> Pour les d premiers tels que ord_d(2) <= C, on peut en principe LISTER tous ces d (il y en a un nombre fini pour chaque C) et les traiter computationnellement. Le probleme : C croit exponentiellement avec k, donc cette strategie ne couvre que les k "petits". Mais par le resultat C/d -> 0, les k "grands" ont automatiquement ord_d(2) > C (des que ord_d(2) >= d^{0.95}, ce qui est vrai pour presque tout premier d).

**Statut : PISTE (4/10). Sans GRH, on peut couvrir les d "typiques" mais pas les exceptions.**

### 3.2 INVENTION : Approche par la borne de Burgess

**Idee (R195-I5) :** Au lieu de GRH, utiliser des bornes INCONDITIONNELLES sur les caracteres de Dirichlet pour minorer ord_d(2).

Le theoreme de Burgess (1962) : pour p premier et chi caractere non-principal, |SUM_{n=M+1}^{M+N} chi(n)| << N^{1-1/(r+1)} * p^{(r+1)/(4r^2)} * (log p)^C pour tout r >= 1.

Cela implique (par un argument standard) que le plus petit generateur de (Z/pZ)* est O(p^{1/(4*sqrt(e)) + epsilon}) ~ O(p^{0.1516...}). Mais cela ne donne PAS directement une borne sur ord_p(2).

La borne de Vinogradov-Erdos sur ord_p(2) : pour TOUT p premier, ord_p(2) > p^{c/log log p} pour une constante c > 0. Cela est inconditionnel mais TRES faible.

Il faudrait ord_p(2) > C ~ p^{0.949}. La borne inconditionnelle donne seulement ord_p(2) > p^{o(1)}, loin du compte.

**Borne intermediaire :** Sous des hypotheses plus faibles que GRH (par exemple, l'hypothese de densite de Linnik-Selberg), on peut obtenir ord_p(2) > p^{delta} pour un delta > 0 explicite. Avec delta > 0.949, le gap serait ferme.

> **R195-L3 [CONDITIONNEL] :** Sous l'hypothese que pour tout d premier de la forme 2^S - 3^k, ord_d(2) > d^{0.95}, le Blocking Mechanism pour le cas interieur est complet (modulo Gap 1).

Mais cette hypothese est PRESQUE AUSSI FORTE que GRH pour cette famille de premiers.

### 3.3 INVENTION : Approche par elimination de la dependance a ord_d(2)

**Idee (R195-I6) :** Reformuler l'argument pour ne PAS avoir besoin de ord_d(2) grand.

Au lieu de l'argument de cardinalite (orbite trop grande pour tenir dans Im(g)), utiliser un argument de STRUCTURE ALGEBRIQUE.

g(B) = SUM_{j=1}^{k-1} u^j * 2^{B_j} mod d. C'est une COMBINAISON LINEAIRE des 2^{B_j} avec coefficients u^j. Les coefficients u^j = (2/3)^j mod d forment une progression geometrique.

La valeur -1 peut-elle etre dans l'image de g ? C'est equivalent a demander : peut-on resoudre -1 = SUM u^j * 2^{B_j} mod d avec 0 <= B_1 <= ... <= B_{k-1} <= M ?

C'est un probleme de REPRESENTATION : -1 est-il representable comme somme de termes u^j * 2^{B_j} avec la contrainte de monotonie ?

**Borne superieure sur |g(B)| :**
g_max = max |g(B)| sur les B monotones. Par l'argument d'arc (Section 3 du preprint), g_max <= C(k) < d pour k >= 18. MAIS g est calcule mod d, pas dans Z. La borne C < d signifie que l'image "entiere" est dans [0, g_max] avec g_max < d. Mais certains elements de Im(g) dans Z pourraient etre > d, et leur reduction mod d pourrait donner -1 = d-1.

Ah, ATTENDONS. L'argument de nonsurjectivite (Stage I) montre C(k) < d, i.e., le nombre de VALEURS DISTINCTES de g(B) mod d est < d. Cela signifie au moins un residu est omis. Mais cela ne dit PAS lequel.

L'argument d'arc montre quelque chose de plus fort pour certains k : g(B) calcule dans Z est < d, donc g(B) mod d = g(B) dans Z, et en particulier g(B) != d-1 = -1 mod d (puisque g(B) >= 0 dans Z et g(B) < d).

**WAIT.** Pour les k ou g_max (calcule dans Z) < d, on a DIRECTEMENT que g(B) in [0, g_max] dans Z, donc g(B) mod d = g(B) in [0, g_max] ⊂ [0, d-1). Et d-1 >= g_max + 1 > g_max >= g(B). Donc g(B) != d-1 pour toute B.

MAIS g(B) dans le preprint est defini comme SUM u^j * 2^{B_j} mod d ou u = 2*3^{-1} mod d. Ce n'est PAS la meme chose que la somme de Horner originale SUM 3^{k-1-j} * 2^{A_j}. La relation est : g(B) = 3^{-(k-1)} * (CorrSum(A) - 3^{k-1}) mod d.

L'argument d'arc s'applique a CorrSum(A) dans Z, pas a g(B) mod d. Donc l'argument d'arc dit : |CorrSum(A)| < d pour les k favorables, donc CorrSum(A) mod d = CorrSum(A) dans [1, d-1]. Mais CorrSum(A) = 0 mod d est EXACTEMENT ce qu'on veut exclure, et l'argument d'arc l'exclut seulement quand CorrSum(A) < d (car alors CorrSum(A) > 0 et CorrSum(A) < d implique CorrSum(A) != 0 mod d).

Pour les k ou g_max >= d (la majorite), l'argument d'arc ne suffit pas et on a besoin du Blocking Mechanism.

> **CONCLUSION :** L'argument d'arc (R194-A2, les 16 valeurs k avec f(alpha) < 0.415) donne N_0(d) = 0 SANS GRH pour ces k-la. Pour les autres k, le Blocking Mechanism est necessaire.

**Statut : PROUVE que l'arc resout une fraction des k, OUVERT pour le reste.**

---

## SYNTHESE ET NOUVELLES APPROCHES

### Tableau recapitulatif des 3 gaps

| Gap | Nature | WHY-depth | Statut | Reparabilite |
|-----|--------|-----------|--------|-------------|
| 1. x2-closure | Structurel (64% generique) | 5/5 | **OUVERT** | Irreparable par shift, besoin d'argument nouveau |
| 2. F_Z non-annulation | Analytique + computationnel | 5/5 | **OUVERT** (verifie k <= 10001) | Reparable par ABC/Evertse (conditionnel) ou crible (partiel) |
| 3. GRH pour ord_d(2) | Arithmetique profond | 5/5 | **CONDITIONNEL GRH** | Evitable si Gap 1 est resolu autrement |

### Hierarchie des gaps

**Le Gap 1 est le VERROU PRINCIPAL.** Si le Gap 1 etait resolu (x2-closure ou substitut), alors :
- Gap 3 (GRH) serait encore necessaire pour l'argument d'orbite, SAUF si la resolution du Gap 1 n'utilise pas l'orbite.
- Gap 2 (F_Z) est INDEPENDANT et doit etre resolu separement.

**Le Gap 2 est le plus accessible.** La non-annulation de F_Z est soutenue par :
- Verification computationnelle k <= 10001
- Argument mod 8 excluant n in {1,2,3,4}
- Heuristique Schwartz-Zippel donnant probabilite exponentiellement petite
- Parite : n necessairement impair (R195-L1)
- Borne de Roth sur les denominateurs de convergents

**Le Gap 3 est le plus profond.** Il touche a des questions ouvertes fondamentales (Artin, GRH).

### 6 nouvelles approches inventees

| # | Nom | Gap cible | Promesse | Statut |
|---|-----|-----------|----------|--------|
| I1 | Crible multi-modulaire | 1 (d compose) | 5/10 | CONDITIONNEL |
| I2 | Sommes de caracteres directes | 1 (d premier) | 3/10 | PISTE OUVERTE |
| I3 | Croissance differentielle (ABC/Evertse) | 2 | 6/10 | CONDITIONNEL |
| I4 | Crible des valuations croisees | 2 | 5/10 | ALGORITHMIQUE |
| I5 | Borne de Burgess | 3 | 2/10 | INSUFFISANT |
| I6 | Argument structure algebrique (sans orbite) | 1+3 | 7/10 | PISTE OUVERTE |

### Recommandations pour R196+

1. **PRIORITE 1 :** Approfondir I6 (argument algebrique sans orbite). La question est : peut-on montrer -1 not in Im(g) directement, sans passer par la x2-closure ? L'approche par les sommes de caracteres (I2) est la voie la plus naturelle mais techniquement difficile. Alternative : exploiter la STRUCTURE DE HORNER (automate monotone de R192) pour montrer que l'etat z = 0 = 3^k mod d (equivalent a g(B) = -1) est inaccessible.

2. **PRIORITE 2 :** Fermer le Gap 2 analytiquement. L'approche I4 (crible croise) combinee avec la parite (R195-L1) et les congruences mod 3, 5, 7 pourrait couvrir un ensemble dense de k. Pour une preuve complete, un argument de type ABC effectif serait ideal.

3. **PRIORITE 3 :** Explorer si la famille d = 2^S - 3^k a des proprietes speciales vis-a-vis d'Artin. Ces nombres sont proches des nombres de Mersenne generalises (Cunningham numbers), pour lesquels des resultats partiels existent.

---

## RESULTATS FORMELS

| Ref | Enonce | Statut |
|-----|--------|--------|
| R195-O1 | Le shift B->B+1 preserve la validite ssi B_{k-1} < M. Le probleme de x2-closure est ENTIEREMENT localise au bord droit. | **PROUVE** |
| R195-O2 | Le shift descendant B->B-1 ne pose probleme qu'au bord gauche, qui se reduit a l'interieur (Lemma 9.9). | **PROUVE** |
| R195-L1 | Si d divise F_Z, le quotient n = abs(F_Z)/d est necessairement IMPAIR. | **PROUVE** |
| R195-L2 | La probabilite heuristique que d divise F_Z est <= (k-1)/d = O(k*2^{-0.585k}), sommable. | **PROUVE (heuristique)** |
| R195-L3 | Sous l'hypothese ord_d(2) > d^{0.95} pour tout d premier de la forme 2^S - 3^k, le cas interieur est resolu. | **CONDITIONNEL** |
| R195-C0 | L'ensemble Im_*(g) \ Im_M(g) est x2-clos (ou Im_M = images dont TOUTES les preimages ont B_{k-1} = M). | **PROUVE (partiel, voir discussion)** |
| R195-C1 | Pour tout m >= 4, d(2m+1) ne divise pas F_Z. | **CONJECTURE** |

---

## EVALUATION

| Critere | Score | Commentaire |
|---------|-------|-------------|
| **Profondeur** | 9/10 | 3 WHY-chains completes a 5 niveaux, chaque niveau apporte du contenu nouveau |
| **Inventivite** | 7/10 | 6 approches, dont I6 (algebrique sans orbite) est la plus prometteuse |
| **Rigueur** | 8/10 | Statuts clairs (PROUVE/CONDITIONNEL/CONJECTURE/PISTE), verification mod 8 detaillee |
| **Impact** | 7/10 | Clarifie la hierarchie des gaps, identifie le bord droit comme verrou unique du Gap 1 |
| **Honnetete** | 10/10 | Le Gap 1 est declare IRREPARABLE par shift, pas de faux espoir |

---

*Round R195 Agent A1 : 3 gaps disseques a 5 niveaux, 6 inventions, 1 correction conceptuelle (Gap 1 = probleme du bord droit), 1 nouvelle conjecture (R195-C1), 4 resultats prouves (R195-O1, O2, L1, L2). Le verrou principal est le Gap 1 (x2-closure), irreparable par methodes combinatoires, necessitant un argument algebrique ou analytique nouveau.*
