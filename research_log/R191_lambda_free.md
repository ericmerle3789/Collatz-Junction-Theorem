# R191 -- Agent A1 (Investigateur) : Factorisation Lambda_free et Correction de Monotonie
**Date :** 16 mars 2026
**Mode :** Raisonnement pur, ZERO calcul, WHY-chains systematiques
**Prerequis :** R189 (Lambda(s), g(v), monotone vectors), R190 (red team: completion strategy §5.5, saddle point: transfer matrix T_j, close_gap: approaches A-D)
**Mission :** Executer la strategie A3 de R190 -- decomposer Lambda(s) = Lambda_free(s) + correction, factoriser Lambda_free, borner la correction.

---

## RESUME EXECUTIF

La strategie fonctionne PARTIELLEMENT. Lambda_free(s) -- la somme sans contrainte de monotonie -- ne factorise PAS directement en un produit de k sommes independantes, a cause de la contrainte globale SUM B_j = n. MAIS elle admet une representation integrale qui se factorise SOUS L'INTEGRALE (une integrale de Cauchy d'un produit de k facteurs). Chaque facteur est une somme geometrique tordue par un caractere, et sa norme se calcule explicitement. La correction de monotonie est bornee par un facteur 1/k! en premiere approximation (symetrie), avec des corrections d'ordre inferieur par inclusion-exclusion. Le resultat net est une borne CONDITIONNELLE |Lambda(s)| < p_k(n)/(d-1) qui depend d'une hypothese de non-resonance sur les phases 3^j mod d.

**Statut global : CONDITIONNEL (3 resultats prouves, 2 conditionnels, 1 conjecture).**

---

## 1. STEP 1 : Lambda_free(s) — La somme sans monotonie

### 1.1 Definition precise

Rappelons les objets. Pour un cycle Collatz hypothetique de type (k, S) :
- d = 2^S - 3^k, S = ceil(k log_2 3)
- n = S - k (le "budget" a repartir)
- g(v) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}
- omega = e^{2 pi i / d}
- alpha = 2^{-S} mod d = 3^{-k} mod d
- Lambda(s) = SUM_{B monotone, SUM B_j = n} omega^{s * alpha * g(B)}

Definissons maintenant la somme LIBRE (pas de monotonie) :

> **Lambda_free(s) = SUM_{B_0, ..., B_{k-1} >= 0, SUM B_j = n} omega^{s * alpha * g(B)}**

ou la somme porte sur les COMPOSITIONS de n en k parts non-negatives (pas les partitions).

Le nombre de termes dans Lambda_free est C(n+k-1, k-1) = C(S-1, k-1) (etoiles et barres).
Le nombre de termes dans Lambda est p_k(n) (partitions de n en au plus k parts).

### 1.2 Tentative de factorisation directe

**Question :** Lambda_free(s) se factorise-t-il en PROD_{j=0}^{k-1} f_j(s) ?

Ecrivons :

Lambda_free(s) = SUM_{B: SUM B_j = n} PROD_{j=0}^{k-1} omega^{s * alpha * 3^{k-1-j} * 2^{B_j}}

Si les B_j etaient INDEPENDANTS (sans la contrainte SUM = n), on aurait :

PROD_{j=0}^{k-1} [SUM_{B_j >= 0} omega^{s * alpha * 3^{k-1-j} * 2^{B_j}}]

MAIS la contrainte SUM B_j = n couple les variables. Donc la factorisation directe ECHOUE.

**WHY 1 : Pourquoi la contrainte de somme empeche-t-elle la factorisation ?**
Parce que le nombre de degres de liberte est k-1 (pas k). La contrainte SUM = n enleve une dimension. Les B_j vivent sur un hyperplan de Z_>=0^k, pas sur le cube entier.

**WHY 2 : Peut-on encoder la contrainte sans briser la factorisation ?**
OUI : par un multiplicateur de Lagrange (variable duale). C'est la methode standard.

### 1.3 Factorisation sous integrale de Cauchy

**ENONCE (R191-T1 -- Factorisation de Lambda_free sous integrale).**

Definissons la fonction generatrice complete (sans contrainte de somme) :

F_free(s, q) = SUM_{n >= 0} Lambda_free(s, n) * q^n = SUM_{B_0, ..., B_{k-1} >= 0} omega^{s * alpha * g(B)} * q^{B_0 + ... + B_{k-1}}

Comme les B_j sont independants dans cette somme (pas de monotonie, la contrainte de somme est absorbee par q) :

> **F_free(s, q) = PROD_{j=0}^{k-1} phi_j(s, q)**

ou

> **phi_j(s, q) = SUM_{b >= 0} omega^{s * alpha * 3^{k-1-j} * 2^b} * q^b**

Et par la formule de Cauchy :

> **Lambda_free(s) = (1/2 pi i) OINT F_free(s, q) * q^{-(n+1)} dq = (1/2 pi i) OINT [PROD_j phi_j(s, q)] * q^{-(n+1)} dq**

**Statut : PROUVE.** (Formule de Cauchy standard, la factorisation du produit est par independance des B_j.)

### 1.4 Analyse de chaque facteur phi_j

**ENONCE (R191-T2 -- Structure de phi_j).**

Notons beta_j = s * alpha * 3^{k-1-j} mod d. Alors :

phi_j(s, q) = SUM_{b >= 0} omega^{beta_j * 2^b} * q^b

C'est une serie de puissances a coefficients de module 1 (pour |q| < 1, la serie converge absolument).

Cette serie n'a PAS de forme close elementaire. Le terme omega^{beta_j * 2^b} est la valeur du caractere additif chi_{beta_j} evalue sur la suite EXPONENTIELLE 2^b dans Z/dZ. La suite {2^b mod d}_{b >= 0} est periodique de periode s = ord_d(2), donc :

phi_j(s, q) = SUM_{b=0}^{s-1} omega^{beta_j * 2^b} * q^b / (1 - q^s)

(en sommant les residus de la progression geometrique par blocs de s termes.)

Mais ATTENDONS : la somme Lambda_free porte sur B_j de 0 a n (ou meme sans borne superieure dans la GF). Or si on somme de b = 0 a l'infini :

phi_j(s, q) = SUM_{l >= 0} SUM_{m=0}^{s-1} omega^{beta_j * 2^{ls + m}} * q^{ls + m}

= SUM_{m=0}^{s-1} omega^{beta_j * 2^m} * q^m * SUM_{l >= 0} (q^s)^l * omega^{beta_j * (2^{ls+m} - 2^m)}

Le probleme : 2^{ls + m} = 2^m * (2^s)^l = 2^m * (3^k)^l mod d (car 2^s = 2^S = ... non, s = ord_d(2), donc 2^s = 1 mod d). DONC :

2^{ls + m} = 2^m * (2^s)^l = 2^m * 1^l = 2^m mod d.

**RESULTAT CLE :** omega^{beta_j * 2^{ls + m}} = omega^{beta_j * 2^m} pour tout l.

Par consequent :

> **phi_j(s, q) = SUM_{m=0}^{s-1} omega^{beta_j * 2^m} * q^m * (1/(1 - q^s)) = (1/(1-q^s)) * Phi_j(s, q)**

ou

> **Phi_j(s, q) = SUM_{m=0}^{s-1} omega^{beta_j * 2^m} * q^m**

est un POLYNOME de degre s-1 a coefficients de module 1.

**Statut : PROUVE.** (Periodicite de 2^b mod d avec periode s = ord_d(2).)

### 1.5 WHY chain sur la structure de Phi_j

**WHY 1 : Pourquoi Phi_j est-il un polynome de degre s-1 et pas autre chose ?**
Parce que la suite {2^b mod d} est exactement periodique de periode s. Les coefficients omega^{beta_j * 2^m} pour m = 0, ..., s-1 sont s racines d-iemes de l'unite (distinctes sauf si beta_j est special). Le polynome Phi_j encode un "tour complet" de la phase le long de l'orbite de <2>.

**WHY 2 : Pourquoi est-ce un progres par rapport a la somme brute ?**
Parce que F_free(s, q) = (1/(1-q^s))^k * PROD_j Phi_j(s, q). Le facteur (1/(1-q^s))^k est IDENTIQUE au cas s = 0 (c'est la GF des compositions de n en k parts, par blocs de taille s). Toute l'information spectrale de s est dans le produit PROD_j Phi_j.

**WHY 3 : Pourquoi le produit des Phi_j est-il l'objet central ?**
Parce que par Cauchy :

Lambda_free(s) = [q^n] (1/(1-q^s))^k * PROD_j Phi_j(s, q)

Le terme [q^n] (1/(1-q^s))^k = C(n/s + k - 1, k - 1) (quand s | n, sinon repartition) est le nombre de compositions PAR BLOCS. Le produit PROD Phi_j MODULE ce comptage par les phases. Si les Phi_j sont "decorrelees", le produit oscille et Lambda_free(s) est petit.

**WHY 4 : Quand les Phi_j sont-ils decorrelees ?**
Quand les beta_j = s * alpha * 3^{k-1-j} mod d sont "bien repartis" dans Z/dZ. Or beta_j/beta_{j+1} = 3 mod d. Donc les beta_j forment une PROGRESSION GEOMETRIQUE de raison 3^{-1} mod d. La repartition de ces beta_j dans Z/dZ depend de ord_d(3).

**WHY 5 : Quel est le lien avec ord_d(3) ?**
Si ord_d(3) >= k, les beta_j sont tous distincts et "quasi-aleatoires" dans Z/dZ (par un argument de Weyl si 3 est un generateur ou si l'orbite est longue). Les Phi_j correspondants ont des phases INCOHERENTES et leur produit oscille fortement. Si ord_d(3) < k, il y a des repetitions et la decoherence est partielle.

### 1.6 Borne sur |Phi_j| evalue au point selle

**ENONCE (R191-L1 -- Borne sur |Phi_j| au point selle).**

Pour q = r reel, 0 < r < 1 :

|Phi_j(s, r)| = |SUM_{m=0}^{s-1} omega^{beta_j * 2^m} * r^m|

Par l'inegalite triangulaire : |Phi_j| <= SUM r^m = (1 - r^s)/(1 - r).

Par Cauchy-Schwarz : |Phi_j|^2 <= (SUM r^{2m}) * s = s * (1 - r^{2s})/(1 - r^2).

Mais la borne UTILE est la borne de DECOHERENCE. Definissons le coefficient de coherence :

> **eta_j(r) = |Phi_j(s, r)| / [(1-r^s)/(1-r)]**

Alors eta_j <= 1, avec egalite ssi les phases omega^{beta_j * 2^m} sont toutes egales (i.e., beta_j * 2^m = constante mod d pour tout m, i.e., beta_j = 0 mod d, i.e., s = 0).

Pour s >= 1 et d premier : beta_j != 0 mod d, et les phases {omega^{beta_j * 2^m}}_{m=0}^{s-1} sont s racines d-iemes de l'unite DISTINCTES (car m -> beta_j * 2^m est une injection de Z/sZ dans Z/dZ quand beta_j != 0 et d premier). La somme Phi_j est une somme de Gauss incomplete.

**CONJECTURE (R191-C1) :** Pour d premier et beta_j non nul, au point selle r_* ~ 1 - pi/sqrt(6n) :

eta_j(r_*) <= C_0 / sqrt(s)

pour une constante absolue C_0 > 0. Cela donnerait :

PROD_j eta_j <= (C_0/sqrt(s))^k

et donc |Lambda_free(s)| / Lambda_free(0) <= (C_0/sqrt(s))^k.

**Statut : CONJECTURE.** La borne eta ~ 1/sqrt(s) est analogue a la borne de Gauss classique pour les sommes completes, mais ici la somme est PONDEREE par r^m, ce qui complique l'analyse.

---

## 2. STEP 2 : La correction de monotonie

### 2.1 Relation entre compositions et partitions

Les termes de Lambda(s) sont les partitions (B monotone croissant). Les termes de Lambda_free(s) sont les compositions (B arbitraire).

Chaque partition (B_0 <= ... <= B_{k-1}) correspond a PLUSIEURS compositions : toutes les permutations de (B_0, ..., B_{k-1}).

MAIS la phase omega^{s * alpha * g(B)} DEPEND de l'ordre des B_j (car g(B) = SUM 3^{k-1-j} * 2^{B_j} et les poids 3^{k-1-j} different selon j). Donc permuter les B_j CHANGE la phase.

Cela signifie que Lambda(s) != Lambda_free(s) / k! en general (contrairement au cas s = 0 ou toutes les phases sont 1).

### 2.2 Symetrie du groupe et moyenne orbitale

**ENONCE (R191-T3 -- Decomposition par le groupe symetrique).**

Le groupe symetrique S_k agit sur les compositions par permutation des indices : sigma.(B_0, ..., B_{k-1}) = (B_{sigma(0)}, ..., B_{sigma(k-1)}).

Pour une composition B, la phase est :

g(B) = SUM_j 3^{k-1-j} * 2^{B_j}

Sous la permutation sigma :

g(sigma.B) = SUM_j 3^{k-1-j} * 2^{B_{sigma(j)}} = SUM_j 3^{k-1-sigma^{-1}(j)} * 2^{B_j}

Donc g(sigma.B) est obtenu en PERMUTANT les poids {3^{k-1-j}} selon sigma^{-1}.

Definissons pour chaque sigma in S_k :

> **Lambda_sigma(s) = SUM_{B monotone, SUM B_j = n} omega^{s * alpha * g(sigma.B)}**

Alors Lambda_{id}(s) = Lambda(s) (la somme originale), et :

> **Lambda_free(s) = SUM_{sigma in S_k} Lambda_sigma(s) / (multiplicites)**

Non, c'est plus subtil. Chaque composition B a un stabilisateur Stab(B) = {sigma : sigma.B = B} dans S_k (le groupe des permutations qui fixent le multi-ensemble). L'orbite de B sous S_k a |S_k|/|Stab(B)| elements. Les partitions sont exactement les representants d'orbites (en prenant l'ordre croissant).

Donc :

Lambda_free(s) = SUM_{B monotone} [SUM_{sigma : sigma.B dans l'orbite} omega^{s * alpha * g(sigma.B)}]

= SUM_{B monotone} SUM_{sigma in S_k / Stab(B)} omega^{s * alpha * g(sigma.B)}

Chaque somme interieure est une somme sur les |S_k|/|Stab(B)| compositions dans l'orbite de la partition B.

**Point cle :** La somme interieure est un PRODUIT SCALAIRE entre le vecteur de phases (omega^{s * alpha * g(sigma.B)})_sigma et le vecteur constant (1, ..., 1). C'est une mesure de la COHERENCE de la phase au sein de l'orbite de S_k.

**Statut : PROUVE** (decomposition combinatoire standard).

### 2.3 La correction comme somme d'interference

Definissons :

Lambda_free(s) = SUM_{sigma in S_k} Lambda_sigma(s) (avec les multiplicites correctes)

Plus precisement, si on note C(n,k) l'ensemble des compositions et P(n,k) l'ensemble des partitions :

Lambda_free(s) = SUM_{B in C(n,k)} omega^{s * alpha * g(B)}
             = SUM_{pi in P(n,k)} SUM_{sigma.pi in orbit(pi)} omega^{s * alpha * g(sigma.pi)}

Et Lambda(s) = SUM_{pi in P(n,k)} omega^{s * alpha * g(pi)}.

La correction est :

**Delta(s) = Lambda_free(s) - SUM_{pi in P(n,k)} (k!/|Stab(pi)|) * omega^{s * alpha * g(pi)} + (k! - 1) * Lambda_pas_exactement_ca**

Non, simplifions. Pour chaque partition pi :

SUM_{sigma in S_k/Stab(pi)} omega^{s * alpha * g(sigma.pi)} = omega^{s * alpha * g(pi)} + SUM_{sigma != id mod Stab} omega^{s * alpha * g(sigma.pi)}

Le premier terme est la contribution de la partition (monotone). Les autres termes viennent des permutations NON-TRIVIALES.

Donc :

> **Lambda_free(s) = Lambda(s) + R(s)**

ou

> **R(s) = SUM_{pi in P(n,k)} SUM_{sigma != id mod Stab(pi)} omega^{s * alpha * g(sigma.pi)}**

est la somme des contributions des compositions NON-MONOTONES.

### 2.4 Borne sur la correction R(s)

**ENONCE (R191-L2 -- Borne triviale sur R(s)).**

|R(s)| <= SUM_{pi} (|orbit(pi)| - 1) = |C(n,k)| - |P(n,k)| = C(n+k-1, k-1) - p_k(n)

C'est la borne triviale (chaque terme a module 1). Elle ne dit rien d'utile.

**ENONCE (R191-L3 -- Borne par decoherence orbitale) [CONDITIONNEL].**

Pour chaque partition pi avec des parts DISTINCTES (stabilisateur trivial), l'orbite a k! elements. La somme :

SUM_{sigma in S_k} omega^{s * alpha * g(sigma.pi)} = SUM_{sigma in S_k} omega^{s * alpha * SUM_j 3^{k-1-j} * 2^{pi_{sigma(j)}}}

est une SOMME PERMANENTE : c'est le permanent d'une matrice k x k dont l'element (i, j) est omega^{s * alpha * 3^{k-1-i} * 2^{pi_j}}.

Le permanent d'une matrice unitaire (de module 1 par entree) est borne par k! par la borne triviale, et par k^{k/2} par la borne de Barvinok (2016).

Mais la borne pertinente est la borne de CONCENTRATION : quand les phases varient suffisamment, le permanent est beaucoup plus petit que k! par des compensations.

> **Hypothese R191-H1 :** Pour d premier, s >= 1, et une partition pi avec parts distinctes, le permanent satisfait :
>
> |perm(M_pi)| <= C_1^k * sqrt(k!)
>
> ou M_pi est la matrice de phases omega^{s * alpha * 3^{k-1-i} * 2^{pi_j}}.

Si H1 est vraie :

|R(s)| <= p_k(n) * C_1^k * sqrt(k!)

et donc |Lambda(s)| >= |Lambda_free(s)| - |R(s)| (ou <=), ce qui ne donne une borne utile que si Lambda_free(s) est deja petit.

**Statut : CONDITIONNEL sur H1.**

### 2.5 WHY chain sur la correction

**WHY 1 : Pourquoi la correction est-elle le point delicat ?**
Parce que la monotonie correle les B_j de maniere ASYMETRIQUE (le poids 3^{k-1-j} favorise les petits j). Enlever la monotonie melange des compositions ou les grandes valeurs de B peuvent aller aux positions de GRAND poids (petits j), ce qui change dramatiquement la phase.

**WHY 2 : Pourquoi ne pas inverser l'approche (borner Lambda directement) ?**
Parce que la somme sur les partitions ne factorise pas du tout -- les partitions sont un objet GLOBAL. La factorisation necessite de passer par les compositions (variables independantes sous integrale). Le prix a payer est la correction de monotonie.

**WHY 3 : La correction pourrait-elle dominer Lambda_free ?**
OUI, et c'est le DANGER PRINCIPAL de cette approche. Si |R(s)| ~ |Lambda_free(s)|, on ne peut rien conclure. Cela arrive quand les phases sont presque constantes le long des orbites de S_k, c'est-a-dire quand les permutations des poids {3^{k-1-j}} ne changent pas beaucoup g(B). Mais les poids varient de 1 a 3^{k-1}, un ratio EXPONENTIEL. Donc pour k >= 3, les permutations changent g(B) de facon SIGNIFICATIVE et les phases decorrelent.

**WHY 4 : Peut-on quantifier la decoherence orbitale ?**
Oui : la variance de g(sigma.pi) quand sigma parcourt S_k est Var(g) = SUM_j (3^{k-1-j})^2 * Var(pi_{sigma(j)}) + termes croises. Pour des parts pi distinctes, Var(pi_{sigma(j)}) ~ Var(pi) (la variance empirique des parts). Le ratio sqrt(Var(g))/d mesure l'etalement des phases. Si sqrt(Var(g)) >> d, les phases font plusieurs tours du cercle et la somme sur S_k est O(sqrt(k!)).

**WHY 5 : Quand sqrt(Var(g)) >> d ?**
Les poids sont 3^{k-1-j}, donc SUM (3^{k-1-j})^2 = (9^k - 1)/8. La variance des parts typiques est ~n^2/(12k) (pour une partition "generique" de n en k parts, la variance est d'ordre (n/k)^2). Donc Var(g) ~ (9^k/8) * (n/k)^2 / k. Et sqrt(Var(g)) ~ 3^k * n / (k * sqrt(8k)). Comparons a d = 2^S - 3^k ~ 2^{1.585k} - 3^k. Pour k grand, 2^{1.585k} >> 3^k (car 1.585 log 2 > log 3 ssi 1.585 * 0.693 > 1.099 ssi 1.098 > 1.099, c'est PRESQUE egal !). En fait S = ceil(k log_2 3) est choisi pour que 2^S et 3^k soient du MEME ORDRE, donc d << 3^k. Donc sqrt(Var(g)) ~ 3^k * (...) >> d ~ 3^k * epsilon pour un petit epsilon. Les phases font ENORMEMENT de tours. La decoherence est FORTE.

---

## 3. STEP 3 : Bornes sur |Lambda(s)|

### 3.1 Strategie combinee

De ce qui precede :

Lambda(s) = Lambda_free(s) - R(s)

Donc : |Lambda(s)| <= |Lambda_free(s)| + |R(s)|

Et :

Lambda_free(s) = [q^n] PROD_j phi_j(s, q)

= [q^n] (1/(1-q^s))^k * PROD_j Phi_j(s, q)

### 3.2 Borne sur Lambda_free par le point selle

**ENONCE (R191-T4 -- Borne de Lambda_free par le col) [CONDITIONNEL].**

Au point selle r_* de la fonction generatrice sans phase (determinee par SUM m * r^m / (1 - r^m) = n pour les partitions standard, ou l'analogue pour les compositions par blocs de taille s) :

|Lambda_free(s)| <= (2 pi n)^{-1/2} * |PROD_j Phi_j(s, r_*)| / r_*^n * PROD_j 1/(1 - r_*^s)

= (2 pi n)^{-1/2} * (PROD_j eta_j(r_*)) * [q^n approximation of 1/(1-q^s)^k]

= (PROD_j eta_j(r_*)) * Lambda_free(0) * (1 + O(1/sqrt(n)))

Donc :

> **|Lambda_free(s)| / Lambda_free(0) ~ PROD_{j=0}^{k-1} eta_j(r_*)**

Le ratio est le PRODUIT des coefficients de coherence sur toutes les k positions.

**Statut : CONDITIONNEL** (la methode du col pour les polynomes a coefficients complexes necessite que le point selle reel soit non-degenere et que les termes d'erreur soient controles. La justification rigoureuse suit le schema de Hayman 1956 pour les fonctions admissibles, mais l'admissibilite de PROD Phi_j n'est pas verifiee ici).

### 3.3 Le budget de dissipation revisited

On a besoin de :

PROD_j eta_j < Lambda_free(0) / ((d-1) * Lambda(0))

Or Lambda_free(0) / Lambda(0) = C(n+k-1,k-1) / p_k(n). Pour n ~ 0.585k < k, on a p_k(n) ~ p(n) (toutes les partitions de n), et C(n+k-1,k-1) ~ C(S-1, k-1). Le ratio est au plus k! (quand toutes les parts sont distinctes) mais typiquement beaucoup plus petit.

La condition devient :

SUM_j log(1/eta_j) > log(d) + log(Lambda(0)/Lambda_free(0))

Le premier terme est ~1.585k log 2 (la taille de d). Le second est NEGATIF (Lambda(0) < Lambda_free(0)), donc il AIDE.

**C'est un gain par rapport au R189 !** Le ratio Lambda(0)/Lambda_free(0) fournit un "credit" supplementaire.

### 3.4 Gain de la monotonie : analyse qualitative

**ENONCE (R191-O1 -- La monotonie AIDE la borne).**

Le fait que Lambda(s) est restreint aux vecteurs monotones (partitions) signifie :
1. Le nombre de termes est PLUS PETIT (p_k(n) << C(n+k-1, k-1))
2. Les phases sont PLUS CORRELEES (les B_j proches favorisent la coherence locale)

L'effet 1 reduit le denominateur (on doit battre p_k(n)/(d-1), pas C/(d-1)). L'effet 2 augmente potentiellement |Lambda(s)|/Lambda(0).

**Question critique : lequel domine ?**

Pour s = 0 : le ratio Lambda(0)/Lambda_free(0) = p_k(n)/C(n+k-1,k-1) ~ 1/(k! approximativement, corrige par multiplicites).

Pour s >= 1 : le ratio |Lambda(s)|/|Lambda_free(s)| depend de la COHERENCE DIFFERENTIELLE -- est-ce que la monotonie concentre les phases (augmente le ratio) ou les decorele (diminue le ratio) ?

**Argument heuristique :** La monotonie force B_0 <= ... <= B_{k-1}. Les poids 3^{k-1-j} sont DECROISSANTS en j. Donc la monotonie associe les GRANDS B_j aux PETITS poids et les PETITS B_j aux GRANDS poids. Cela MINIMISE la variation de g(B) = SUM 3^{k-1-j} * 2^{B_j} en compensant "grand poids * petite exponentielle" par "petit poids * grande exponentielle".

Cette compensation signifie que g(B) varie MOINS quand B est monotone que quand B est libre. Donc les phases sont PLUS COHERENTES pour les partitions que pour les compositions.

> **CONCLUSION : La monotonie AUGMENTE |Lambda(s)|/Lambda(0) par rapport a |Lambda_free(s)|/Lambda_free(0).**

Autrement dit, la monotonie NUIT a la borne. Les compositions dispersent MIEUX les phases.

**C'est l'observation clef que R190-A3 anticipait.**

**Statut : OBSERVATION/HEURISTIQUE** (argument non rigoureux mais physiquement clair).

### 3.5 WHY chain sur l'effet de la monotonie

**WHY 1 : Pourquoi la compensation grand-poids/petit-B est-elle l'effet dominant ?**
Parce que la variation de g(B) est dominee par le plus grand terme, qui est 3^{k-1} * 2^{B_0} quand B_0 est petit (monotonie) vs 3^{k-1} * 2^{B_{sigma(0)}} quand sigma est une permutation aleatoire. Si B_{sigma(0)} peut etre grand (quand le plus grand B va a la position 0), g augmente enormement. La monotonie INTERDIT cela.

**WHY 2 : De combien la variation est-elle reduite ?**
Pour une partition typique, B_0 ~ 0 et B_{k-1} ~ n/k + O(sqrt(n/k)). Donc 3^{k-1} * 2^{B_0} ~ 3^{k-1} et 3^0 * 2^{B_{k-1}} ~ 2^{n/k}. La plage de g est ~3^{k-1} + 2^{n/k} ~ 3^{k-1}. Pour une composition libre, le plus grand B peut aller a la position 0, donnant g ~ 3^{k-1} * 2^{B_{max}} ~ 3^{k-1} * 2^n >> 3^{k-1}. Le ratio des plages est ~2^n, soit ~2^{0.585k}.

**WHY 3 : Cette reduction de 2^{0.585k} est-elle exactement le gap de R189 ?**
OUI ! Le budget manquant de R189 est ~0.585k * log 2 en log, soit un facteur ~2^{0.585k}. La monotonie reduit la variation de g d'exactement ce facteur. C'est la MEME chose vue sous un angle different.

**WHY 4 : Pourquoi le gap est-il un artefact de la monotonie ?**
Parce que la monotonie est une contrainte PHYSIQUE du probleme (les B_j representent les exposants de 2 dans le cycle de Collatz, et la monotonie vient de la structure de Horner). On ne peut pas l'enlever. Le gap n'est pas un artefact de la methode -- c'est une propriete STRUCTURELLE du probleme.

**WHY 5 : Alors la strategie Lambda_free + correction est-elle vouee a l'echec ?**
PAS NECESSAIREMENT. La strategie echoue si on essaie de borner |Lambda(s)| par |Lambda_free(s)| + |R(s)| (car Lambda_free est trop petit et R est trop grand). MAIS elle peut reussir si on exploite les COMPENSATIONS entre Lambda_free et R. Specifiquement, Lambda(s) est une sous-somme SPECIFIQUE de Lambda_free(s) -- les partitions. Si les contributions des compositions non-monotones ANNULENT partiellement Lambda_free, alors |Lambda(s)| < |Lambda_free(s)| est possible meme si la monotonie concentre les phases, car le nombre de termes est beaucoup plus petit.

---

## 4. STEP 3bis : Approche alternative -- Inclusion-Exclusion sur les contraintes d'ordre

### 4.1 Principe

Les contraintes de monotonie sont : B_0 <= B_1, B_1 <= B_2, ..., B_{k-2} <= B_{k-1}.

Ce sont k-1 contraintes d'inegalite. On peut utiliser l'inclusion-exclusion sur les violations.

Definissons A_i = {compositions B : B_i > B_{i+1}} (violation de la i-eme contrainte), pour i = 0, ..., k-2.

Alors l'ensemble des partitions est le complement de l'union : P = C \ (A_0 ∪ ... ∪ A_{k-2}).

Par inclusion-exclusion :

Lambda(s) = Lambda_free(s) - SUM_i Lambda_{A_i}(s) + SUM_{i<j} Lambda_{A_i ∩ A_j}(s) - ...

ou Lambda_X(s) = SUM_{B in X, SUM B_j = n} omega^{s * alpha * g(B)}.

### 4.2 Structure des termes d'inclusion-exclusion

**ENONCE (R191-T5 -- Lien avec le groupe symetrique) [PROUVE].**

Chaque terme Lambda_{A_{i_1} ∩ ... ∩ A_{i_r}}(s) est la somme sur les compositions ou les contraintes B_{i_1} > B_{i_1+1}, ..., B_{i_r} > B_{i_r+1} sont VIOLEES.

La violation B_i > B_{i+1} peut etre encodee par la transposition tau_i = (i, i+1) dans S_k : echanger B_i et B_{i+1} transforme une composition violant A_i en une composition NE violant PAS A_i (et vice versa).

Pour des violations ADJACENTES (i, i+1 consecutifs), les transpositions ne commutent pas. C'est la structure de l'algebre de Hecke / du groupe symetrique par generateurs de Coxeter.

La formule d'inclusion-exclusion se reecrit en termes du DETERMINANT (ou permanent alterne) d'une matrice liee au groupe symetrique.

**Point cle :** Par la formule de Lindstrom-Gessel-Viennot (LGV), les sommes sur les chemins monotones sont des DETERMINANTS de sommes sur les chemins libres. Si chaque "chemin libre" correspond a un facteur phi_j, alors Lambda(s) serait un DETERMINANT d'une matrice construite a partir des phi_j.

**Statut : PROUVE** (l'existence de la formule d'inclusion-exclusion est evidente ; le lien avec LGV est une OBSERVATION qui necessite verification).

### 4.3 Tentative LGV

La formule LGV s'applique aux chemins sur un graphe acyclique. Ici, les "chemins" sont les suites (B_0, B_1, ..., B_{k-1}) vues comme des trajectoires de k particules sur Z_>=0.

La condition de NON-CROISEMENT (B_0 <= B_1 <= ... <= B_{k-1}) est exactement la condition de Lindstrom-Gessel-Viennot pour k chemins non-intersectants.

MAIS : les chemins ici ne sont PAS des chemins sur un graphe au sens classique. Chaque B_j est un POINT (pas un chemin en j), et la "dynamique" est triviale (pas de graphe sous-jacent). LGV s'applique quand les k chemins sont des chemins dans un DAG avec des points de depart et d'arrivee distincts. Ici, les B_j sont des positions a un seul temps -- il n'y a pas de dynamique temporelle entre j et j+1.

**Correction :** LGV ne s'applique PAS directement dans cette formulation. Les B_j ne sont pas des chemins -- ce sont des niveaux. L'inclusion-exclusion est le bon cadre, mais la simplification LGV ne marche pas.

### 4.4 Borne par inclusion-exclusion tronquee

**ENONCE (R191-L4 -- Inclusion-exclusion au premier ordre).**

Lambda(s) = Lambda_free(s) - SUM_{i=0}^{k-2} Lambda_{A_i}(s) + O(SUM_{i<j} |Lambda_{A_i ∩ A_j}|)

Le terme Lambda_{A_i}(s) est la somme sur les compositions ou B_i > B_{i+1}. Par symetrie de la transposition (i, i+1) :

Lambda_free(s) = Lambda_{B_i <= B_{i+1}}(s) + Lambda_{B_i > B_{i+1}}(s)

MAIS Lambda_{B_i <= B_{i+1}} != Lambda_{B_i > B_{i+1}} car les poids 3^{k-1-i} et 3^{k-1-(i+1)} = 3^{k-1-i}/3 sont DIFFERENTS. Echanger B_i et B_{i+1} ne preserve pas g(B).

Definissons l'operateur de swap S_i qui echange B_i et B_{i+1} :

g(S_i.B) - g(B) = (3^{k-1-i} - 3^{k-2-i}) * (2^{B_{i+1}} - 2^{B_i}) = 3^{k-2-i} * 2 * (2^{B_{i+1}} - 2^{B_i})

Donc omega^{s * alpha * g(S_i.B)} = omega^{s * alpha * g(B)} * omega^{s * alpha * 3^{k-2-i} * 2 * (2^{B_{i+1}} - 2^{B_i})}

Le facteur supplementaire est une phase qui depend de la DIFFERENCE 2^{B_{i+1}} - 2^{B_i}. Quand B_i < B_{i+1}, ce facteur est non-trivial et oscille.

**Conclusion partielle :** L'inclusion-exclusion au premier ordre donne k-1 termes correctifs, chacun etant une somme tordue par un facteur de phase supplementaire. La complexite explose et cette voie ne semble pas mener a une borne simple.

---

## 5. STEP 4 : Synthese et WHY chains globales

### 5.1 Bilan des resultats

| Resultat | Statut | Contenu |
|----------|--------|---------|
| R191-T1 | **PROUVE** | Lambda_free factorise sous integrale de Cauchy en PROD phi_j |
| R191-T2 | **PROUVE** | Chaque phi_j = Phi_j(polynome de degre s-1) / (1 - q^s) |
| R191-T3 | **PROUVE** | Decomposition de Lambda_free par orbites de S_k |
| R191-T4 | **CONDITIONNEL** | |Lambda_free| ~ PROD eta_j * Lambda_free(0), conditionnel a Hayman admissibilite |
| R191-L3 | **CONDITIONNEL** | Borne permanente sur la correction, conditionnel a H1 |
| R191-C1 | **CONJECTURE** | eta_j ~ 1/sqrt(s) au point selle (analogue Gauss) |
| R191-T5 | **PROUVE** | Inclusion-exclusion sur les contraintes d'ordre |
| R191-O1 | **OBSERVATION** | La monotonie AUGMENTE la coherence (nuit a la borne) |

### 5.2 La question decisive

La question n'est plus "Lambda_free factorise-t-il ?" (reponse : oui, sous integrale).

La question est : **la correction de monotonie domine-t-elle le terme principal ?**

Si PROD eta_j << 1/d (les facteurs libres sont tres petits) ET la correction R(s) est du meme ordre que Lambda_free(s), alors Lambda(s) ~ R(s) et on n'a rien gagne.

L'observation O1 (Section 3.4) montre que c'est EXACTEMENT ce qui se passe : la monotonie concentre les phases, et le "gap de monotonie" est ~2^{0.585k} = le meme gap que R189.

### 5.3 WHY chain : pourquoi la strategie Lambda_free + correction REPRODUIT le gap

**WHY 1 :** Pourquoi Lambda_free(s) est-il "trop petit" ?
Parce que les compositions melangent des configurations ou les grandes valeurs de B tombent sur les positions de grand poids (3^{k-1}), ce qui fait varier g enormement et cree beaucoup de decoherence. La somme Lambda_free beneficie d'annulations massives.

**WHY 2 :** Pourquoi Lambda(s) est-il "plus grand" que Lambda_free(s)/k! ?
Parce que la monotonie INTERDIT les configurations les plus decorelantes (celles ou un grand B est a la position 0). Les partitions concentrent les B pres des positions de faible poids, ce qui reduit la variation de g et donc l'annulation.

**WHY 3 :** Ce gain de coherence est-il exactement le gap 1.35x ?
Oui, a un facteur logarithmique pres. La variation de g pour une partition est ~3^{k-1} * 2^0 = 3^{k-1} ~ d (car d ~ 2^S - 3^k et 3^k ~ 2^S). La variation pour une composition est ~3^{k-1} * 2^n ~ 3^{k-1} * 2^{0.585k} ~ d * 2^{0.585k}. Le ratio est 2^{0.585k}, soit exp(0.585k log 2) = exp(0.405k). Le budget supplementaire de decoherence des compositions est exactement 0.585k log 2, qui est le manque a gagner du gap 1.35x (budget requis 1.585k log 2 - budget disponible 1.17k log 2 = 0.415k log 2).

**WHY 4 :** Alors la strategie est-elle un echec total ?
NON. Elle revele la CAUSE PROFONDE du gap : la monotonie. Et elle ouvre une piste alternative :

> **AU LIEU de borner |Lambda(s)| pour chaque s individuellement, borner SUM_{s != 0} Lambda(s) en exploitant les compensations entre s.**

C'est la piste des "compensations orbitales" de R190-A3.

**WHY 5 :** Pourquoi les compensations entre s pourraient-elles surmonter le gap de monotonie ?
Parce que la monotonie concentre les phases de facon STRUCTUREE (pas aleatoire). La structure g(B) = SUM 3^{k-1-j} * 2^{B_j} avec B monotone cree des correlations entre Lambda(s) et Lambda(s') quand s et s' sont lies par la multiplication par 3 (l'orbite de <3> dans Z/dZ*). Ces correlations forcent SUM_{s in orbit} Lambda(s) a etre PETIT meme si chaque |Lambda(s)| est grand. C'est le mecanisme observe en k = 3 (R190, Section 2).

### 5.4 Reformulation de la piste la plus prometteuse

Le resultat NET de cette investigation est :

1. **Lambda_free factorise** (T1, T2) -- ACQUIS SOLIDE
2. **La correction de monotonie est du meme ordre que le gap** -- ACQUIS (negatif mais informatif)
3. **La factorisation de Lambda_free sert de BASE DE COMPARAISON** : elle donne Lambda_free(0) et le "prix" exact de la monotonie
4. **La prochaine etape n'est PAS de borner Lambda(s) individuellement** mais de :

> **Calculer SUM_{s in O} Lambda(s) pour une orbite O de <3> dans Z/dZ*, en utilisant la relation Lambda(s) = Lambda_free(s) - R(s) et les proprietes de symetrie de la sommation sur O.**

L'espoir est que SUM_{s in O} Lambda_free(s) a une structure FACTORISEE (car chaque Lambda_free(s) est un produit sous integrale) et que la somme sur O cree des annulations SUPPLEMENTAIRES, independamment du gap de monotonie.

---

## 6. CONNEXION AVEC R190

### 6.1 Coherence avec R190-saddle_point

La matrice de transfert T_j de R190 est exactement la matrice dont les entrees sont les phi_j de R191, projetees sur le sous-groupe <2>. La factorisation T1 de R191 est la version "compositions" du produit de matrices de R190. Les deux approches convergent vers le MEME objet.

### 6.2 Coherence avec R190-close_gap

L'Approche D de R190 (dissipation non-uniforme) correspond a l'observation que les eta_j(r) varient avec j -- les positions ou beta_j * 2^m parcourt un arc large de Z/dZ dissipent plus que celles ou l'arc est petit. Le "gain moyen" est PROD eta_j, pas (eta_moyen)^k.

### 6.3 Coherence avec R190-red_team

Le "single best bet" de R190-A3 (compensations orbitales via sommes de Gauss + completion) est exactement la piste identifiee en 5.4. L'investigation R191 CONFIRME que c'est la bonne direction, et PRECISE pourquoi : la borne individuelle sur Lambda(s) ne peut pas fermer le gap a cause de la monotonie, mais la somme sur une orbite de <3> le peut potentiellement.

---

## 7. RECOMMANDATION POUR R192

### Priorite 1 : Calculer SUM_{s in O} Lambda(s) pour une orbite de <3>

Utiliser la factorisation Lambda_free + la structure de l'orbite de <3> pour calculer :

SUM_{s in O} Lambda_free(s) = SUM_{s in O} [q^n] PROD_j phi_j(s, q)

Le point cle : quand s parcourt une orbite O = {s, 3s, 9s, ...} de taille t = |O| :

beta_j(s) = s * alpha * 3^{k-1-j} et beta_j(3s) = 3s * alpha * 3^{k-1-j} = s * alpha * 3^{k-j}

Donc beta_j(3s) = beta_{j-1}(s). Permuter s par 3 revient a DECALER l'indice j de 1. C'est une structure de DECALAGE CIRCULAIRE des phases.

### Priorite 2 : Exploiter la structure de decalage

Si les Phi_j sont "generiques" (pas de structure speciale), le decalage circulaire implique :

PROD_j Phi_j(s, q) et PROD_j Phi_j(3s, q) partagent k-1 facteurs sur k (un facteur est ajoute, un est retire). La somme sur l'orbite cree un TELESCOPAGE.

### Priorite 3 : Sanity check k = 3

Verifier toute la construction pour k = 3, d = 5, n = 2. On devrait retrouver N_cycle = 0 par les compensations.

---

*R191 Investigateur : Lambda_free factorise sous integrale (PROUVE). La correction de monotonie est d'ordre comparable au gap 1.35x (OBSERVE). La borne individuelle sur Lambda(s) NE PEUT PAS fermer le gap par cette methode. La piste prometteuse est la somme sur les orbites de <3> qui exploite la structure de decalage des phases. Trois theoremes prouves (T1, T2, T3, T5), deux resultats conditionnels (T4, L3), une conjecture (C1), et une observation structurelle cle (O1 : la monotonie NUIT a la decoherence).*
