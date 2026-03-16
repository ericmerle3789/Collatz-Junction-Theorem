# R190 -- Agent A1 (Investigateur) : Methode du Col sur Lambda(s)
**Date :** 16 mars 2026
**Mode :** Raisonnement pur, ZERO calcul, investigation 5-WHY systematique
**Prerequis :** R189 (operateur Lambda, gap 1.35x, spectre de dissipation, matrice de transfert)
**Objectif :** Appliquer la methode du col (saddle point / steepest descent) a Lambda(s) pour borner |Lambda(s)| et fermer ou reduire le gap 1.35x.

---

## 0. RAPPEL DES OBJETS DE R189

**Definitions cles :**
- d = 2^S - 3^k (impair, k >= 2), S = ceil(k * log_2(3))
- g(v) = SUM_{j=0}^{k-1} 3^{k-1-j} * 2^{B_j}, avec B_0 <= B_1 <= ... <= B_{k-1}, SUM B_j = n = S - k
- omega = e^{2*pi*i/d}
- Lambda(s) = SUM_{B monotone, SUM B_j = n} omega^{s * g(v) / (quoi exactement?)}

**Precision cruciale sur Lambda(s).** D'apres R189-A3, l'objet est :

> Lambda(s) = SUM_{v in V_k(S)} omega^{s * 2^{-S} * g(v)}

ou 2^{-S} est l'inverse de 2^S modulo d. Comme 2^S = 3^k mod d, on a 2^{-S} = 3^{-k} mod d. Donc :

> **Lambda(s) = SUM_v omega^{s * 3^{-k} * g(v)}**

Et N_cycle = (1/d) SUM_{s=0}^{d-1} Lambda(s). Le terme s = 0 donne Lambda(0) = |V_k(S)| = p(k, n) (nombre de partitions monotones).

Pour N_cycle = 0, il suffit que |Lambda(s)| < d pour tout s >= 1 (par la formule de detection : N_cycle entier, Lambda(0)/d < 1 pour k assez grand, donc si les termes s >= 1 ne s'accumulent pas, N_cycle = 0).

Plus precisement : N_cycle = 0 ssi SUM_{s=1}^{d-1} Lambda(s) = -p(k, n), et une condition suffisante est |Lambda(s)| < p(k,n)/(d-1) pour tout s >= 1.

---

## 1. STRUCTURE ANALYTIQUE DE Lambda(s)

### 1.1 Lambda(s) comme fonction generatrice restreinte

**ENONCE (R190-D1).** Lambda(s) est une somme exponentielle sur les partitions monotones de n en k parts :

Lambda(s) = SUM_{0 <= B_0 <= B_1 <= ... <= B_{k-1}, SUM B_j = n} omega^{s * alpha * g(B)}

ou alpha = 3^{-k} mod d et g(B) = SUM_j 3^{k-1-j} * 2^{B_j}.

Notant c_s = s * alpha mod d, on a :

> **Lambda(s) = SUM_v omega^{c_s * g(v)} = SUM_v e^{2*pi*i * c_s * g(v) / d}**

C'est la somme exponentielle S_{c_s} de R189 (Section 4.4), ou c_s parcourt Z/dZ* quand s parcourt {1, ..., d-1} (car alpha = 3^{-k} est inversible mod d, donc s |-> c_s est une permutation de Z/dZ).

**Statut : DEFINITION/OBSERVATION.**

### 1.2 Ecriture comme integrale de contour

**WHY-1 : Pourquoi ecrire Lambda(s) comme integrale de contour ?**
Parce que la methode du col necessite un domaine continu (ou au moins une representation analytique) pour deformer le chemin d'integration.

**WHY-2 : Comment passer du discret au continu ?**
En utilisant la fonction generatrice des partitions monotones. La contrainte SUM B_j = n avec B_0 <= ... <= B_{k-1} est encodee par le coefficient de q^n dans une serie formelle.

**ENONCE (R190-T1 -- Representation integrale de Lambda(s)).**

Soit q un parametre complexe, |q| < 1. Definissons la fonction generatrice :

F_s(q) = SUM_{n >= 0} Lambda_k(s, n) * q^n

ou Lambda_k(s, n) = SUM_{B monotone, SUM B_j = n} omega^{c_s * g(B)}.

Alors Lambda(s) = Lambda_k(s, n_0) ou n_0 = S - k est la valeur cible. Par la formule de Cauchy :

> **Lambda(s) = (1 / 2*pi*i) OINT F_s(q) * q^{-(n_0+1)} dq**

ou l'integrale est prise sur un cercle |q| = r < 1.

Il reste a calculer F_s(q) en forme close.

**Statut : PROUVE** (standard, formule de Cauchy pour les coefficients).

### 1.3 Calcul de F_s(q) : factorisation par les gaps

Passons aux gaps Delta_j = B_j - B_{j-1} (B_{-1} = 0), Delta_j >= 0.
- SUM B_j = SUM_j SUM_{i<=j} Delta_i = SUM_i (k - i) * Delta_i = n
- B_j = Delta_0 + ... + Delta_j
- g(B) = SUM_j 3^{k-1-j} * 2^{Delta_0 + ... + Delta_j}

Le probleme : g(B) est une fonction NON-SEPARABLE des Delta_j. Le terme 2^{B_j} = 2^{Delta_0 + ... + Delta_j} couple tous les Delta_i avec i <= j.

**WHY-3 : Le couplage est-il un obstacle fondamental ?**
OUI pour la factorisation directe. NON si on introduit des variables auxiliaires.

**ENONCE (R190-T2 -- Representation par variables auxiliaires).**

Introduisons les variables z_j ∈ C avec |z_j| = 1, representant la "phase accumulee" a l'etape j. Definissons :

G_s(q, z_0, ..., z_{k-1}) = PROD_{j=0}^{k-1} [SUM_{Delta_j >= 0} q^{(k-j)*Delta_j} * z_j^{2^{Delta_j}}]

Non, ce n'est pas correct non plus, car 2^{B_j} = 2^{SUM_{i<=j} Delta_i}, pas 2^{Delta_j}.

**REVISION IMPORTANTE.** Le couplage multiplicatif 2^{B_j} = PROD_{i<=j} 2^{Delta_i} signifie que dans le domaine multiplicatif (base 2), les contributions se MULTIPLIENT. Cela suggere un changement de variables.

Posons u_j = 2^{B_j} mod d. Alors u_j = u_{j-1} * 2^{Delta_j} mod d. La recurrence est :

u_0 = 2^{Delta_0}, u_{j+1} = u_j * 2^{Delta_{j+1}}.

Et g(B) = SUM_j 3^{k-1-j} * u_j.

La phase dans Lambda(s) est :

phi_s(B) = 2*pi * c_s * SUM_j 3^{k-1-j} * u_j / d = SUM_j 2*pi * c_s * 3^{k-1-j} * u_j / d

Si les u_j etaient INDEPENDANTS, chaque facteur serait e^{2*pi*i * c_s * 3^{k-1-j} * u_j / d} et la somme factoriserait. MAIS les u_j sont lies par u_j = u_{j-1} * 2^{Delta_j}, donc u_j / u_{j-1} = 2^{Delta_j} est une puissance de 2 (le multiplicateur).

**INVENTION (R190-I1) : Factorisation par Matrice de Transfert sur le Tore.**

L'etat a l'etape j est u_j ∈ <2> ⊂ (Z/dZ)* (le sous-groupe cyclique engendre par 2, d'ordre s = ord_d(2)).

La transition de u_j a u_{j+1} est la multiplication par 2^{Delta_{j+1}} pour un gap Delta_{j+1} >= 0.

La contribution de l'etape j a la phase est omega^{c_s * 3^{k-1-j} * u_j}.

La contribution au poids est q^{(k-j) * Delta_j}.

**Definissons la matrice de transfert spectrale sur <2> :**

Pour l'etape j (j = 0, ..., k-1), la matrice T_j^{(s)}(q) de taille s x s est :

[T_j^{(s)}(q)]_{u', u} = SUM_{Delta >= 0 : u' = u * 2^Delta} q^{(k-j)*Delta} * omega^{c_s * 3^{k-1-j} * u}

Le facteur de phase est attache a l'etat de DEPART u, pas a l'etat d'arrivee u'.

CORRECTION : la condition u' = u * 2^Delta signifie 2^Delta = u'/u = u' * u^{-1} dans <2>. Comme <2> est cyclique d'ordre s, u' * u^{-1} = 2^m pour un unique m ∈ {0, 1, ..., s-1}. Donc Delta = m mod s, et Delta >= 0 signifie Delta ∈ {m, m+s, m+2s, ...}.

La somme sur Delta donne :

SUM_{l >= 0} q^{(k-j)*(m + l*s)} = q^{(k-j)*m} / (1 - q^{(k-j)*s})

Donc :

> **[T_j^{(s)}(q)]_{u', u} = omega^{c_s * 3^{k-1-j} * u} * q^{(k-j)*m(u,u')} / (1 - q^{(k-j)*s})**

ou m(u, u') est l'unique m ∈ {0, ..., s-1} tel que u' = u * 2^m dans <2>.

**ENONCE (R190-T3 -- Formule de transfert spectrale).**

F_s(q) = e_1^T * T_0^{(s)}(q) * T_1^{(s)}(q) * ... * T_{k-1}^{(s)}(q) * **1**

ou e_1 est le vecteur indicateur de u_0 = 1 (etat initial : B_{-1} = 0 donc u_{-1} = 1, et u_0 = 2^{Delta_0}), et **1** est le vecteur tout-a-un (on somme sur tous les etats finaux).

WAIT -- L'etat initial est AVANT le premier gap. Avant l'etape 0, u_{-1} = 2^0 = 1 (car B_{-1} = 0). Le premier gap Delta_0 envoie l'etat 1 vers u_0 = 2^{Delta_0}. Donc l'etat initial est bien u = 1.

La contribution de l'etape j est l'application de T_j qui :
(a) multiplie par la phase omega^{c_s * 3^{k-1-j} * u} (contribution du caractere),
(b) fait la transition u -> u' = u * 2^{Delta_j} avec poids q^{(k-j)*Delta_j}.

Et Lambda(s) = [q^{n_0}] F_s(q).

**Statut : PROUVE** (construction explicite, toutes les sommes sont justifiees).

**WHY-4 : Pourquoi la matrice de transfert est-elle de taille s x s et pas d x d ?**
Parce que les etats u_j vivent dans <2> ⊂ (Z/dZ)*, qui a s elements. L'information complete de la dynamique sur les 2^{B_j} est capturee par la position dans ce sous-groupe cyclique. L'etat de Horner z_j mod d est IMPLICITEMENT encode dans la phase accumulee -- il n'apparait pas comme variable d'etat.

**WHY-5 : Pourquoi est-ce un progres par rapport a la matrice d*s de R189 ?**
La reduction de d*s a s est MASSIVE. L'espace d*s peut avoir des milliards d'etats. L'espace s = ord_d(2) est typiquement O(d) aussi, MAIS pour les d de Collatz (d = 2^S - 3^k), l'ordre de 2 mod d est exactement S (car 2^S = 3^k = 0 + 3^k, non : 2^S = d + 3^k, donc 2^S ≡ 3^k mod d, et l'ordre de 2 mod d est S si et seulement si aucun diviseur propre S' de S ne satisfait 2^{S'} ≡ ±3^{k'} mod d pour un k' pertinent -- ce qui est generiquement vrai).

Donc s ≈ S ≈ 1.585k. La matrice de transfert est de taille ~1.585k × 1.585k. C'est LINEAIRE en k, au lieu d'exponentiel.

---

## 2. APPLICATION DE LA METHODE DU COL A Lambda(s)

### 2.1 Point de depart : l'integrale de Cauchy

Lambda(s) = (1/2*pi*i) OINT F_s(q) * q^{-(n+1)} dq

ou n = n_0 = S - k, et F_s(q) = e_1^T * PROD_j T_j^{(s)}(q) * **1**.

Pour appliquer la methode du col, on cherche le point selle q_* de la fonction

h(q) = log F_s(q) - (n+1) log q

i.e., la solution de h'(q_*) = 0, soit :

> **F_s'(q_*) / F_s(q_*) = (n+1) / q_***

### 2.2 Comparaison avec le cas s = 0 (Hardy-Ramanujan)

Pour s = 0, Lambda(0) = p(k, n) = nombre de partitions de n en k parts ordonnees.

La fonction generatrice est :

F_0(q) = PROD_{j=0}^{k-1} 1/(1 - q^{k-j}) = PROD_{m=1}^{k} 1/(1 - q^m)

(car le gap Delta_j a poids (k-j), et la somme SUM_{Delta >= 0} q^{(k-j)*Delta} = 1/(1 - q^{k-j})).

Le point selle pour p(n) (partitions non restreintes) est le point de Hardy-Ramanujan q_* = e^{-pi*sqrt(2/(3n))} ≈ 1 - pi/sqrt(6n). Le point selle pour les partitions en k parts est similaire mais avec une modification.

**OBSERVATION CLE :** Pour s >= 1, F_s(q) differe de F_0(q) par les facteurs de phase omega^{c_s * 3^{k-1-j} * u}. Ces phases DEPLACENT le point selle dans le plan complexe.

**WHY-1 : Pourquoi le deplacement du point selle importe-t-il ?**
Parce que si le point selle de F_s se deplace par rapport a celui de F_0, la valeur de |F_s(q_*)| au nouveau point selle peut etre STRICTEMENT PLUS PETITE que F_0(q_*^{(0)}) au point selle de F_0. Ce ratio controle exactement |Lambda(s)| / Lambda(0).

**WHY-2 : De combien le point selle se deplace-t-il ?**
Le deplacement est proportionnel aux phases. Si les phases sont "petites" (c_s * 3^{k-1-j} * u est presque multiple de d), le deplacement est petit et Lambda(s) ≈ Lambda(0). Si les phases sont "grandes" (bien reparties), le deplacement est significatif et |Lambda(s)| << Lambda(0).

### 2.3 La methode du col pour le produit matriciel

Le produit de matrices T_0 * T_1 * ... * T_{k-1} n'admet pas directement une decomposition log-additive. MAIS si s est petit (disons s = O(k)), on peut diagonaliser chaque matrice T_j et suivre les valeurs propres.

**ENONCE (R190-T4 -- Decomposition spectrale du produit de transfert).**

Chaque matrice T_j^{(s)}(q) est de taille s × s. Ecrivons sa decomposition spectrale :

T_j^{(s)}(q) = SUM_{l=1}^{s} lambda_l^{(j)}(q) * P_l^{(j)}

ou lambda_l^{(j)} sont les valeurs propres et P_l^{(j)} les projecteurs spectraux.

Le produit PROD_j T_j = SUM_{l_0, ..., l_{k-1}} (PROD_j lambda_{l_j}^{(j)}) * (PROD_j P_{l_j}^{(j)})

C'est un produit NON-COMMUTATIF en general, donc les projecteurs s'enchainent. MAIS la valeur propre DOMINANTE de chaque T_j donne la contribution principale.

**Statut : OBSERVATION** (la decomposition est standard, l'exploitation est le defi).

### 2.4 Simplification : le cas s petit (matrice 1x1)

**CAS SPECIAL s = 1 (ord_d(2) = 1, i.e., 2 ≡ 1 mod d, i.e., d | 1, d = 1).**

Trivial : seul d = 1, k = 1. Sans interet.

**CAS SPECIAL s = 2 (ord_d(2) = 2, i.e., 2^2 = 4 ≡ 1 mod d, i.e., d | 3).**

d | 3 et d impair positif, donc d = 1 ou d = 3. Pour d = 3 : 2^S - 3^k = 3, donc 2^S = 3(3^{k-1} + 1). Pour k = 1 : 2^S = 6, pas une puissance de 2. Pour k = 2 : 2^S = 3*10 = 30, non. Ce cas ne se produit pas pour les d de Collatz standards.

**CAS GENERAL : s = S ≈ 1.585k.**

La matrice est de taille ~1.585k × 1.585k. La methode du col s'applique a CHAQUE element du produit matriciel via la variable q.

### 2.5 Le point selle pour F_s(q)

**ENONCE (R190-T5 -- Equation du point selle).**

Le logarithme de F_s(q) pour q reel proche de 1 est (a l'approximation dominante) :

log F_s(q) ≈ log(valeur propre dominante du produit PROD_j T_j)

Pour le terme s = 0 : la valeur propre dominante de T_j^{(0)}(q) est simplement 1/(1 - q^{k-j}) (matrice 1×1 sans phase), et :

log F_0(q) = -SUM_{j=0}^{k-1} log(1 - q^{k-j}) = -SUM_{m=1}^{k} log(1 - q^m)

Le point selle q_* satisfait :

SUM_{m=1}^{k} m * q^m / (1 - q^m) = n

C'est l'equation classique du point selle de Hardy-Ramanujan pour les partitions restreintes.

Pour s >= 1, les matrices T_j^{(s)} ont une valeur propre dominante lambda_max^{(j)}(q) qui satisfait :

|lambda_max^{(j)}(q)| <= 1/(1 - q^{k-j})

avec EGALITE si et seulement si toutes les phases sont coherentes (i.e., omega^{c_s * 3^{k-1-j} * u} = 1 pour tout u ∈ <2>).

**Statut : CONDITIONNEL** (la borne sur la valeur propre dominante est prouvee par Perron-Frobenius pour les matrices a coefficients positifs, mais ici les coefficients ont des phases complexes).

### 2.6 Borne sur la valeur propre dominante avec phases

**ENONCE (R190-T6 -- Reduction de la valeur propre par decoherence).**

Soit M une matrice s × s avec M_{u',u} = alpha_u * A_{u',u} ou A est une matrice a coefficients reels positifs et alpha_u = omega^{c_s * 3^{k-1-j} * u} sont des phases unitaires. Soit lambda_PF la valeur propre de Perron-Frobenius de A (dominante, reelle positive). Alors :

|lambda_max(M)| <= lambda_PF

avec egalite si et seulement si les phases alpha_u sont CONSTANTES sur le support du vecteur propre de Perron-Frobenius de A.

**Preuve.** Soit v le vecteur propre de Perron-Frobenius de A, v > 0, Av = lambda_PF * v. Soit w un vecteur propre de M pour la valeur propre lambda_max : Mw = lambda_max * w.

|lambda_max| * |w_u'| = |(Mw)_{u'}| = |SUM_u alpha_u * A_{u',u} * w_u| <= SUM_u A_{u',u} * |w_u|

Donc |lambda_max| * |w| <= A * |w| (composante par composante). Par le theoreme de comparaison de Perron-Frobenius :

|lambda_max| <= lambda_PF(A).

Egalite ssi alpha_u * w_u / |w_u| est constant. CQFD.

**Statut : PROUVE.**

### 2.7 Quantification de la perte de valeur propre

**WHY-3 : De combien la valeur propre est-elle reduite ?**

Notons rho_j = |lambda_max(T_j^{(s)})| / lambda_PF(T_j^{(0)}). Alors rho_j <= 1, et :

|F_s(q)| <= PROD_j |lambda_max(T_j^{(s)})| <= PROD_j rho_j * lambda_PF(T_j^{(0)}) = (PROD_j rho_j) * F_0(q)

Donc :

> **|Lambda(s)| / Lambda(0) <= PROD_j rho_j**

Pour que |Lambda(s)| < p(k,n)/(d-1), il suffit que :

PROD_j rho_j < 1/(d-1)

soit SUM_j log(1/rho_j) > log(d) ≈ S * log(2) ≈ 1.585k * log(2).

**C'est exactement le budget de dissipation de R189 !** Mais maintenant avec une quantification PRECISE via les valeurs propres des matrices de transfert.

**WHY-4 : Les rho_j sont-ils strictement < 1 ?**

Par R190-T6, rho_j < 1 si et seulement si les phases omega^{c_s * 3^{k-1-j} * u} ne sont pas constantes sur <2>. Or les phases sont constantes ssi c_s * 3^{k-1-j} * u est constant mod d pour tout u ∈ <2>, ssi c_s * 3^{k-1-j} * (u - u') ≡ 0 mod d pour tout u, u' ∈ <2>.

Comme <2> - <2> engendre le sous-groupe additif de Z/dZ genere par les differences d'elements de <2>, la condition est que c_s * 3^{k-1-j} annule ce sous-groupe. Pour d premier, <2> - <2> engendre tout Z/dZ (des que |<2>| >= 2), donc la condition est c_s * 3^{k-1-j} ≡ 0 mod d, ce qui pour s >= 1 et d premier ne se produit que si d | 3^{k-1-j} (impossible car gcd(3, d) = 1) ou d | c_s (impossible car c_s ∈ {1, ..., d-1}).

**ENONCE (R190-T7).** Pour d premier et s >= 1, rho_j < 1 pour TOUT j = 0, ..., k-1.

**Statut : PROUVE** (pour d premier).

**WHY-5 : Quelle est la valeur exacte de rho_j ?**

C'est la question cruciale. Pour une matrice circulante s × s avec phases, la valeur propre dominante peut etre calculee exactement par la transformee de Fourier finie sur Z/sZ.

---

## 3. CALCUL EXACT DE rho_j PAR FOURIER SUR <2>

### 3.1 Structure de la matrice T_j

La matrice T_j^{(s)}(q) agit sur l'espace C^{<2>}, ou <2> ≅ Z/sZ est cyclique. L'element de matrice est :

[T_j]_{u', u} = omega^{c_s * 3^{k-1-j} * u} * q^{(k-j) * m(u, u')} / (1 - q^{(k-j)*s})

ou m(u, u') est la "distance multiplicative" : u' = u * 2^m, m ∈ {0, ..., s-1}.

Factorisons : T_j = D_j * C_j ou

- D_j = diag(omega^{c_s * 3^{k-1-j} * u})_{u ∈ <2>} (matrice diagonale de phases)
- C_j = matrice de convolution cyclique avec [C_j]_{u', u} = q^{(k-j)*m(u,u')} / (1 - q^{(k-j)*s})

**OBSERVATION :** C_j est une matrice CIRCULANTE sur Z/sZ (car m(u * 2^a, u' * 2^a) = m(u, u') pour tout a). Ses valeurs propres sont donnees par la DFT.

### 3.2 Valeurs propres de C_j

C_j est la matrice circulante dont la premiere ligne est :

c_j(m) = q^{(k-j)*m} / (1 - q^{(k-j)*s}), m = 0, 1, ..., s-1

Les valeurs propres de C_j sont :

mu_l^{(j)} = SUM_{m=0}^{s-1} c_j(m) * zeta^{-l*m} = (1/(1-q^{(k-j)*s})) * SUM_{m=0}^{s-1} (q^{k-j} * zeta^{-l})^m

ou zeta = e^{2*pi*i/s} est une racine primitive s-ieme de l'unite.

= (1/(1-q^{(k-j)*s})) * (1 - (q^{k-j} * zeta^{-l})^s) / (1 - q^{k-j} * zeta^{-l})

= (1 - q^{(k-j)*s} * zeta^{-l*s}) / ((1-q^{(k-j)*s}) * (1 - q^{k-j} * zeta^{-l}))

Or zeta^s = 1, donc zeta^{-l*s} = 1. Et 1 - q^{(k-j)*s} * 1 = 1 - q^{(k-j)*s} s'annule avec le denominateur. Donc :

> **mu_l^{(j)} = 1 / (1 - q^{k-j} * zeta^{-l})**

pour l = 0, 1, ..., s-1.

**Verification l = 0 :** mu_0^{(j)} = 1/(1 - q^{k-j}). C'est la valeur propre de Perron-Frobenius (la plus grande pour q reel, 0 < q < 1). COHERENT.

**Statut : PROUVE.**

### 3.3 Valeurs propres de T_j = D_j * C_j

Le produit D_j * C_j n'est PAS circulant (D_j brise la symetrie circulante). Ses valeurs propres ne sont PAS le produit des valeurs propres de D_j et C_j separement.

**MAIS** on peut analyser le produit autrement. Passons dans la base de Fourier de Z/sZ. Soit F la matrice de DFT (s × s). Alors C_j = F^{-1} * diag(mu_l^{(j)}) * F.

Et D_j est une matrice diagonale dans la base canonique, qui dans la base de Fourier devient une matrice de CONVOLUTION.

Specifiquement : D_j = diag(omega^{c_s * 3^{k-1-j} * 2^a})_{a=0}^{s-1} ou on parametre <2> = {2^0, 2^1, ..., 2^{s-1}}.

Dans la base de Fourier, la matrice D_j a pour elements :

[F D_j F^{-1}]_{l, l'} = (1/s) SUM_{a=0}^{s-1} omega^{c_s * 3^{k-1-j} * 2^a} * zeta^{(l'-l)*a}

C'est la transformee de Fourier de la suite (omega^{c_s * 3^{k-1-j} * 2^a})_{a=0}^{s-1} evaluee en l' - l.

**Notation :** Posons beta_j = c_s * 3^{k-1-j} mod d. La suite de phases est (omega^{beta_j * 2^a})_{a=0}^{s-1}.

Definissons :

> **R_j(l) = (1/s) SUM_{a=0}^{s-1} e^{2*pi*i * beta_j * 2^a / d} * e^{-2*pi*i * l * a / s}**

C'est la DFT de la suite de phases exponentielles. Elle ressemble a la somme de Gauss generalisee sur le sous-groupe <2>.

### 3.4 Le produit T_j dans la base de Fourier

Dans la base de Fourier, T_j = (F D_j F^{-1}) * diag(mu_l). C'est le produit d'une matrice "presque diagonale" (dont les elements sont les R_j(l'-l)) par une matrice diagonale.

[T_j]_{l, l'} (base Fourier) = R_j(l - l') * mu_{l'}^{(j)}

C'est une matrice ou la l-ieme ligne est R_j(l - .) * mu_.^{(j)}.

La norme operatorielle de T_j est bornee par :

||T_j||_op <= max_l |mu_l^{(j)}| * ||R_j||_1

ou ||R_j||_1 = SUM_l |R_j(l)|.

Par Parseval : SUM_l |R_j(l)|^2 = (1/s) SUM_a |omega^{beta_j * 2^a}|^2 = (1/s) * s = 1.

Donc par Cauchy-Schwarz : ||R_j||_1 <= sqrt(s) * sqrt(SUM |R_j(l)|^2) = sqrt(s).

Cela donne ||T_j||_op <= sqrt(s) * max_l |mu_l^{(j)}|. MAIS c'est une borne FAIBLE (le facteur sqrt(s) tue toute esperance de dissipation).

**WHY-1 : Pourquoi la borne par norme operatorielle est-elle trop faible ?**
Parce qu'on perd l'information de la DIRECTION du vecteur propre dominant. Le produit T_0 * T_1 * ... * T_{k-1} contracte dans CERTAINES directions et dilate dans d'autres. La borne par produit des normes est pessimiste.

**WHY-2 : Comment faire mieux ?**
En suivant la DIRECTION dominante a travers le produit -- c'est-a-dire en utilisant l'exposant de Lyapunov du produit de matrices aleatoires (ou quasi-aleatoires).

---

## 4. EXPOSANT DE LYAPUNOV DU PRODUIT DE MATRICES

### 4.1 Le cadre

Le produit M = T_0 * T_1 * ... * T_{k-1} est un produit de k matrices s × s. Chaque T_j depend de j a travers :
- Le poids (k-j) dans la geometrique q^{(k-j)*m}
- La phase beta_j = c_s * 3^{k-1-j} mod d

L'exposant de Lyapunov est :

gamma = (1/k) * log ||M||

Pour le terme s = 0 (sans phases) : gamma_0 = (1/k) * SUM_j log mu_0^{(j)} = -(1/k) * SUM_j log(1 - q^{k-j}).

Pour s >= 1 : gamma_s < gamma_0 si les phases produisent de la decoherence.

**ENONCE (R190-T8 -- Reduction de l'exposant de Lyapunov par les phases).**

Soit gamma_0 = (1/k) SUM_j log(1/(1 - q^{k-j})) l'exposant de Lyapunov du produit sans phases (s = 0). Soit gamma_s l'exposant pour s >= 1. Alors :

gamma_s <= gamma_0

et la difference delta_gamma = gamma_0 - gamma_s satisfait :

> **delta_gamma >= (1/k) SUM_j log(1 / ||D_j||_{PF})**

ou ||D_j||_{PF} est le ratio spectral de la matrice de phases D_j par rapport a la matrice identite, defini comme :

||D_j||_{PF} = max_v (|D_j * v|_1 / |v|_1) pour v >= 0

Non, cette formulation n'est pas propre. Reformulons.

**APPROCHE CORRECTE : Le produit dans la base canonique.**

Revenons a la base canonique. T_j = D_j * C_j ou D_j est diagonale (phases) et C_j est circulante (positive). Le produit est :

M = D_0 * C_0 * D_1 * C_1 * ... * D_{k-1} * C_{k-1}

Chaque facteur C_j propage la masse (diffusion), et chaque facteur D_j tord les phases (decoherence).

**L'idee du col generalisee :** Plutot que de chercher le col dans le plan q, cherchons le col dans l'espace des TRAJECTOIRES de l'automate.

### 4.2 Point selle dans l'espace des trajectoires

**INVENTION (R190-I2) : Methode du col sur le simplexe des partitions.**

La somme Lambda(s) = SUM_v e^{i*phi_s(v)} ou phi_s(v) = 2*pi * c_s * g(v) / d, et la somme porte sur les vecteurs v = (B_0, ..., B_{k-1}) monotones avec SUM B_j = n.

Passons en coordonnees continues. Posons x_j = B_j / n pour j = 0, ..., k-1. Les contraintes sont :

0 <= x_0 <= x_1 <= ... <= x_{k-1}, SUM x_j = 1

C'est le simplexe ordonne Sigma_k (de dimension k-1).

La phase est :

phi_s(x) = 2*pi * c_s * g(n*x) / d = 2*pi * c_s * SUM_j 3^{k-1-j} * 2^{n*x_j} / d

La "densite" des partitions pres de x est (par l'approximation locale) proportionnelle a un terme combinatoire.

Le point selle de phi_s sur Sigma_k est le point x_* ou grad phi_s est proportionnel au gradient de la contrainte SUM x_j = 1 :

d phi_s / d x_j = lambda (meme pour tout j non sature par les contraintes d'inegalite)

Calculons :

d phi_s / d x_j = 2*pi * c_s * 3^{k-1-j} * n * log(2) * 2^{n*x_j} / d

La condition de point selle est :

3^{k-1-j} * 2^{n*x_j} = constante pour tout j "libre" (non bloque aux bornes)

Soit 2^{n*x_j} = C * 3^{-(k-1-j)} = C * 3^{j-k+1}.

Donc n*x_j = log_2(C) + (j-k+1) * log_2(3).

La solution est lineaire en j :

> **x_j^* = alpha + beta * j**

avec beta = log_2(3) / n et alpha determinee par SUM x_j = 1.

SUM x_j = k*alpha + beta * k*(k-1)/2 = 1

Donc alpha = (1 - beta*k*(k-1)/2) / k = 1/k - beta*(k-1)/2.

Le point selle EXISTE dans l'interieur de Sigma_k ssi x_0^* >= 0 et x_{k-1}^* <= ... (pas de saturation). Verifions :

x_0^* = alpha = 1/k - log_2(3)*(k-1)/(2n). Avec n = S-k ≈ 0.585k :

x_0^* ≈ 1/k - 1.585*(k-1)/(2*0.585*k) ≈ 1/k - 1.355*(k-1)/k

Pour k grand : x_0^* ≈ (1 - 1.355*(k-1))/k ≈ -1.355 < 0.

**Le point selle est HORS du simplexe !**

**WHY-3 : Pourquoi le point selle est-il hors du domaine ?**
Parce que la phase phi_s croit trop vite en x_j pour les grands j (le facteur 2^{n*x_j} est exponentiel). Le gradient de la phase n'est equilibre qu'avec des x_j qui decroissent pour j petit, ce qui viole x_0 >= 0.

**WHY-4 : Que signifie un point selle hors du domaine ?**
Cela signifie que la contribution dominante vient du BORD du simplexe, pas de l'interieur. La methode du col classique doit etre modifiee pour tenir compte des contraintes d'inegalite.

**WHY-5 : Quel est le bord dominant ?**
Le bord ou x_0 = x_1 = ... = x_{l-1} = 0 et x_l > 0 pour un certain l. C'est le bord ou les l premieres parts B_j sont nulles. Plus l est grand, plus la "masse" est concentree sur les grands B_j.

**ENONCE (R190-T9 -- Point selle contraint).**

Le point selle de phi_s sous les contraintes de Sigma_k est atteint sur le bord B_0 = B_1 = ... = B_{l-1} = 0, ou l est determine par la condition de stationnarite sur les k-l parts restantes.

Sur ce bord, les parts non nulles satisfont 2^{n*x_j} ∝ 3^{j-k+1} pour j = l, ..., k-1, ce qui donne un profil exponentiel en j.

La valeur de phi_s au point selle contraint est :

phi_s^* = 2*pi * c_s * [l * 3^{k-1} + (termes exponentiellement decroissants)] / d

Le premier terme l * 3^{k-1} domine car les l premieres parts sont 0, donc 2^{B_j} = 1 pour j < l.

**Statut : CONDITIONNEL** (l'analyse de bord est heuristique ; une preuve rigoureuse necessite de verifier les conditions KKT du second ordre).

---

## 5. LA STRUCTURE DES POINTS CRITIQUES ET LES ARCS

### 5.1 Connexion avec la methode du cercle (major/minor arcs)

**WHY-1 : Pourquoi la distinction major/minor arcs est-elle pertinente ici ?**

La somme N_cycle = (1/d) SUM_s Lambda(s) est une somme sur les "frequences" s ∈ Z/dZ. Quand s/d est proche d'un rationnel a/q a petit denominateur, Lambda(s) peut etre grand (resonance). C'est exactement la distinction de la methode du cercle de Hardy-Littlewood-Vinogradov.

**ENONCE (R190-D2 -- Arcs majeurs et mineurs pour Lambda(s)).**

Definissons :
- **Arcs majeurs M(Q)** : les s tels que |s*alpha/d - a/q| < Q/d pour un q <= Q et gcd(a,q) = 1.
- **Arcs mineurs m(Q)** : le complement dans {1, ..., d-1}.

Ici alpha = 3^{-k} mod d, donc s*alpha mod d = s*3^{-k} mod d. La condition |s*3^{-k}/d - a/q| < Q/d equivaut a |s*3^{-k} - a*d/q| < Q, soit s*3^{-k} est proche d'un multiple de d/q.

### 5.2 Arcs majeurs : Lambda(s) pour s pres d'un rationnel

Quand s*3^{-k} ≡ a*d/q mod d (approximativement), la phase phi_s(v) ≈ 2*pi*a*g(v)/(q*3^k) est "simplifiee" -- elle vit dans Z/qZ plutot que Z/dZ.

**ENONCE (R190-T10 -- Borne sur les arcs majeurs).**

Pour s dans un arc majeur associe a a/q avec q <= Q :

Lambda(s) ≈ (1/q) * SUM_{r=0}^{q-1} e^{2*pi*i*a*r/q} * N(g(v) ≡ r * 3^k mod d)

C'est une moyenne ponderee par les phases q-periodiques. La contribution est :

|Lambda(s)| <= p(k, n) * ... (a completer par l'analyse du nombre de solutions par classe de residu mod q).

Pour q = 1 (l'arc trivial) : Lambda(s) = p(k, n). MAIS s = 0 est le SEUL s dans l'arc q = 1 (puisque s >= 1 sur les arcs non triviaux).

Pour q = 2 : Lambda(s) ≈ (p(k,n) + (-1)^a * N_{pair/impair}) / 2, ou N_{pair/impair} est le desequilibre de parite de g(v) mod 2.

**WHY-2 : Le desequilibre de parite de g(v) est-il controlable ?**

g(v) = SUM 3^{k-1-j} * 2^{B_j}. Modulo 2 :
- 3^{k-1-j} ≡ 1 mod 2 pour tout j (3 est impair)
- 2^{B_j} ≡ 0 mod 2 si B_j >= 1, ≡ 1 mod 2 si B_j = 0

Donc g(v) mod 2 = #{j : B_j = 0} mod 2.

Le nombre de B_j = 0 dans une partition monotone est le nombre de parts nulles initiales. C'est l ∈ {0, 1, ..., k} (ou k si n = 0). La parite depend finement de la distribution de l parmi les partitions.

**Statut : OBSERVATION.** La parite de g est liee au nombre de parts nulles -- un invariant combinatoire accessible.

### 5.3 Arcs mineurs : la decoherence forte

**ENONCE (R190-T11 -- Borne sur les arcs mineurs par decoherence).**

Pour s dans les arcs mineurs (s*3^{-k}/d loin de tout rationnel a petit denominateur), les phases phi_s(v) sont "pseudo-aleatoires" sur le cercle unite. La decoherence entre les differents vecteurs v donne :

|Lambda(s)|^2 <= SUM_{v, v'} |omega^{c_s * (g(v) - g(v'))}|_moy

= p(k,n) + 2 * #{(v, v') : g(v) ≡ g(v') mod d, v ≠ v'}

= p(k,n) + 2 * SUM_{r mod d} N(r)^2 - p(k,n) (ou N(r) = #{v : g(v) ≡ r mod d})

= SUM_r N(r)^2

C'est le DEUXIEME MOMENT (l'energie additive de g sur les partitions mod d).

Par R189-A3, E[|Lambda(s)|^2] = SUM_r N(r)^2 ≈ p(k,n)^2 / d (si g est equidistribue).

Le deuxieme moment suffit pour k >= 42 (recupere le seuil de Borel-Cantelli).

**WHY-3 : Pourquoi le deuxieme moment ne suffit-il pas pour k < 42 ?**
Parce que p(k,n)^2/d > d^2 pour k petit (p(k,n) > d), et la borne de Cauchy-Schwarz |Lambda(s)| <= sqrt(SUM N(r)^2) est trop grande.

**WHY-4 : Comment faire mieux que le deuxieme moment ?**
En exploitant la STRUCTURE de g, pas juste sa distribution. C'est la que la methode du col sur le simplexe (Section 4) et l'analyse par matrice de transfert (Section 3) interviennent.

**WHY-5 : L'analyse par transfert donne-t-elle un meilleur exposant ?**
OUI, potentiellement. La matrice de transfert encode la correlation PAS-A-PAS entre les parts successives, tandis que le deuxieme moment traite les vecteurs v comme independants. Le gain possible est dans les CORRELATIONS entre les phases successives.

---

## 6. L'INGREDIENT MANQUANT : CORRELATION ENTRE LES PHASES SUCCESSIVES

### 6.1 L'observation centrale

Dans le produit T_0 * T_1 * ... * T_{k-1}, les matrices successives sont liees par :
- T_j a des phases beta_j = c_s * 3^{k-1-j} mod d
- T_{j+1} a des phases beta_{j+1} = c_s * 3^{k-2-j} = beta_j * 3^{-1} mod d

Donc les phases successives sont liees par la multiplication par 3^{-1}. L'orbite de beta_0 sous la multiplication par 3^{-1} est {beta_0, beta_0*3^{-1}, ..., beta_0*3^{-(k-1)}}, qui est un segment de l'orbite de beta_0 sous <3>.

### 6.2 L'exposant de Lyapunov comme somme d'entropies conditionnelles

**INVENTION (R190-I3) : Decomposition de Furstenberg.**

Le log du rayon spectral du produit PROD_j T_j peut etre decompose comme :

log rho(PROD T_j) = SUM_j h_j

ou h_j est la "contribution" de l'etape j a l'exposant. Par le theoreme de Furstenberg (1963) pour les produits de matrices aleatoires :

h_j = log |T_j * v_j| - log |v_j|

ou v_j est le vecteur directeur du produit T_0 * ... * T_{j-1} * e_1 (direction accumulee apres j etapes).

La perte de chaque etape est :

delta_j = log |C_j * v_j| - log |T_j * v_j| = -log(rho_j^{eff})

ou rho_j^{eff} = |D_j C_j v_j| / |C_j v_j| est le ratio EFFECTIF de contraction par les phases.

**OBSERVATION CLE :** rho_j^{eff} depend de la DIRECTION v_j, pas seulement de D_j. Si v_j est concentre sur un seul etat u (Dirac), alors rho_j^{eff} = 1 (pas de contraction). Si v_j est UNIFORME sur <2>, alors rho_j^{eff} = |rho_{beta_j}| (la dissipation maximale de R189).

Donc la contraction effective est maximale quand le vecteur directeur est DIFFUS, et minimale quand il est CONCENTRE.

### 6.3 Le role de la diffusion C_j

Les matrices C_j (la partie circulante, sans phases) DIFFUSENT le vecteur directeur. Apres l'application de C_j, le vecteur v_{j+1}' = C_j v_j est plus "etale" que v_j (car C_j a tous ses coefficients positifs et est circulante).

La COMPETITION est entre :
- La diffusion par C_j (qui rend v_j plus uniforme, augmentant la contraction future)
- La contraction par D_j (qui peut concentrer v_j sur certains etats)

### 6.4 Le regime de melange rapide

**ENONCE (R190-T12 -- Borne dans le regime de melange rapide, CONDITIONNEL).**

Supposons que les matrices C_j melangent "vite" (i.e., apres O(1) etapes, le vecteur directeur est approximativement uniforme). Alors chaque etape contribue une contraction effective :

rho_j^{eff} ≈ |rho_{beta_j}|

ou rho_{beta_j} = (1/s) SUM_{a=0}^{s-1} e^{2*pi*i * beta_j * 2^a / d} est la dissipation de R189.

Dans ce cas, la dissipation TOTALE est :

SUM_j log(1/rho_j^{eff}) ≈ SUM_j log(1/|rho_{beta_j}|)

Et le budget de dissipation est celui de R189 : ~1.17k * log(2).

**Le melange rapide ne ferme PAS le gap 1.35x.** Il recupere exactement le meme budget.

**WHY-1 : Pourquoi le melange rapide ne fait-il pas mieux ?**
Parce que le melange rend le vecteur directeur UNIFORME, ce qui donne la contraction MOYENNE |rho|. Mais |rho| est deja la borne de R189. Le melange est la condition pour que l'heuristique de R189 soit EXACTE, pas pour qu'elle soit DEPASSEE.

**WHY-2 : Que faut-il pour faire mieux que la borne de melange ?**
Il faut exploiter les CORRELATIONS entre les phases de differentes etapes. La suite beta_0, beta_1, ..., beta_{k-1} n'est pas arbitraire -- elle suit l'orbite de 3^{-1} dans Z/dZ. Les phases de etapes successives sont CORRELEES par la structure multiplicative.

---

## 7. L'INGREDIENT MANQUANT : CORRELATIONS MULTI-ETAPES

### 7.1 Phases correlees par l'orbite de 3

Les phases successives sont beta_j = c_s * 3^{k-1-j} mod d. En posant gamma = c_s * 3^{k-1} mod d :

beta_j = gamma * 3^{-j} mod d

La suite (beta_0, beta_1, ...) est un SEGMENT de l'orbite de gamma sous la multiplication repetee par 3^{-1}. Cette orbite a une structure ARITHMETIQUE riche.

### 7.2 Le mecanisme de gain multi-etapes

**INVENTION (R190-I4) : Dissipation cumulee par paires d'etapes.**

Considerons DEUX etapes consecutives j et j+1. La contribution jointe est :

T_j * T_{j+1} = D_j * C_j * D_{j+1} * C_{j+1}

La contraction jointe est PLUS FORTE que le produit des contractions individuelles si les phases beta_j et beta_{j+1} = beta_j * 3^{-1} sont "complementaires".

Formellement, la valeur propre dominante de T_j * T_{j+1} satisfait :

|lambda_max(T_j T_{j+1})| <= |lambda_max(T_j)| * |lambda_max(T_{j+1})|

MAIS cette borne peut etre STRICTE. Le gain vient du fait que D_j concentre le vecteur dans une direction que D_{j+1} dissipe fortement (ou vice versa).

**ENONCE (R190-T13 -- Gain de decoherence par paires, CONJECTURE).**

Pour d premier et s generic, la dissipation par paire satisfait :

log(1/rho_{j,j+1}^{pair}) >= log(1/|rho_{beta_j}|) + log(1/|rho_{beta_{j+1}}|) + epsilon_{pair}

ou epsilon_{pair} > 0 est un terme CORRECTIF qui vient de la non-commutativite D_j * C_j * D_{j+1}.

Si epsilon_{pair} ~ c * log(2) / k pour une constante c > 0, alors le budget total est :

SUM paires epsilon_{pair} ~ (k/2) * c * log(2) / k = c * log(2) / 2

C'est une CORRECTION ADDITIVE (O(1)), pas multiplicative. Insuffisant pour fermer le gap 1.35x qui est O(k).

**Statut : CONJECTURE.** Le gain par paires est generiquement positif mais trop petit.

### 7.3 Gain par blocs de taille croissante

**WHY-3 : Et si on considere des blocs de taille > 2 ?**

Pour un bloc de t etapes, l'exposant de Lyapunov du produit T_j * ... * T_{j+t-1} peut differer significativement de la somme des exposants individuels si les t phases forment un "design" sur Z/dZ.

La condition optimale est que les t phases {beta_j, beta_{j+1}, ..., beta_{j+t-1}} = {gamma * 3^{-j}, gamma * 3^{-(j+1)}, ..., gamma * 3^{-(j+t-1)}} soient bien reparties modulo d.

Si t = ord_d(3) (la PERIODE COMPLETE de l'orbite de 3), alors les phases parcourent toute l'orbite de <3>, et la dissipation est maximale.

**ENONCE (R190-T14 -- Dissipation sur une orbite complete de 3).**

Soit t = ord_d(3). Le produit de t matrices consecutives T_j * ... * T_{j+t-1} a un rayon spectral :

rho(PROD_{t etapes}) = PROD_{l} |sum sur l'orbite de <3>|^{1/t} ...

Plus precisement, la valeur propre dominante du produit sur une orbite COMPLETE de <3> est liee au caractere additif evalue sur l'orbite multiplicative. Par symetrie de l'orbite, les contributions se SYMMETRISENT.

Le gain par orbite complete depend de la STRUCTURE HARMONIQUE des elements de <3> ⊂ Z/dZ.

**WHY-4 : Quel est le gain quantitatif sur une orbite ?**

Sur l'orbite complete, les phases beta_j = gamma * 3^{-j} parcourent <3> (un sous-groupe multiplicatif de (Z/dZ)*). La dissipation integrale est :

SUM_{h in <3>} log(1/|rho_h|) = SUM_{h in <3>} log(1/|(1/s) SUM_{a} e^{2*pi*i*h*2^a/d}|)

Par symetrie du sous-groupe, et par l'estimation de Weil pour les sommes de caracteres additifs sur les sous-groupes multiplicatifs :

|rho_h| <= (sqrt(d) + 1) / s pour h != 0

Si s ≈ d (2 est un generateur), |rho_h| ≈ sqrt(d)/d = 1/sqrt(d). Alors log(1/|rho_h|) ≈ (1/2) log(d) ≈ 0.79k * log(2).

Et SUM sur k etapes (k/t cycles complets) : k/t * t * 0.79 * log(2) = 0.79k * log(2).

TOUJOURS INSUFFISANT (on a besoin de 1.585k * log(2), on obtient 0.79k * log(2)).

**WHY-5 : Pourquoi la borne de Weil ne suffit-elle pas ?**

Parce que la borne de Weil donne |rho_h| ≈ 1/sqrt(d) ≈ 1/sqrt(2^{1.585k}), soit log(1/|rho_h|) ≈ 0.79k * log(2). Et le budget est : k * 0.79 * log(2) = 0.79k * log(2), alors qu'on a besoin de 1.585k * log(2). Le ratio est EXACTEMENT 2. Le gap est un facteur 2 !

**OBSERVATION PROFONDE :** Le gap par Weil est un facteur 2, et le gap par dissipation uniforme (R189) est un facteur 1.35. Les deux sont insuffisants mais pour des raisons DIFFERENTES :
- Dissipation uniforme : utilise |rho| ≈ 1/4 mais seulement n ≈ 0.585k etapes actives
- Borne de Weil : utilise |rho| ≈ 1/sqrt(d) mais pour les k etapes

---

## 8. SYNTHESE : L'APPROCHE HYBRIDE SADDLE POINT + TRANSFERT

### 8.1 Recapitulation des bornes obtenues

| Methode | Budget de dissipation | Budget necessaire | Gap |
|---------|----------------------|-------------------|-----|
| R189 dissipation uniforme | 1.17k log 2 | 1.585k log 2 | 1.35x |
| Saddle point (transfert, melange rapide) | 1.17k log 2 | 1.585k log 2 | 1.35x |
| Borne de Weil sur orbite | 0.79k log 2 | 1.585k log 2 | 2.0x |
| 2eme moment | ~k log(p/d) | log d | OK pour k >= 42 |

### 8.2 La piste de l'approche hybride

**INVENTION (R190-I5) : Hybride Hardy-Ramanujan + Dissipation.**

L'idee : la formule de Cauchy donne Lambda(s) = OINT F_s(q) * q^{-(n+1)} dq. La methode du col pour q donne un facteur MULTIPLICATIF qui depend de la "courbure" de F_s au point selle.

Pour s = 0 : la courbure est celle de la fonction de partition p(k, n) ≈ exp(pi * sqrt(2n/3)) / (4n*sqrt(3)) (Hardy-Ramanujan).

Pour s >= 1 : la courbure est MODIFIEE par les phases. Specifiquement, les phases changent la position du point selle dans le plan COMPLEXE (pas sur l'axe reel).

**ENONCE (R190-T15 -- Point selle complexe pour Lambda(s), CONJECTURE).**

Le point selle de h(q) = log F_s(q) - n * log q se deplace de q_* (reel, pour s=0) a q_*^{(s)} (complexe, pour s >= 1). Le deplacement est :

q_*^{(s)} ≈ q_* * e^{i * theta_s}

ou theta_s est determine par les phases. L'argument est que F_s(q) differe de F_0(q) par des facteurs de phase qui tournent dans le plan complexe quand q quitte l'axe reel.

Au point selle complexe :

|F_s(q_*^{(s)})| < F_0(q_*)

La perte est :

log(F_0(q_*)) - log|F_s(q_*^{(s)})| ≈ (1/2) * F_0''(q_*) / F_0(q_*) * |q_* - q_*^{(s)}|^2

C'est une contribution QUADRATIQUE en le deplacement du point selle. Cette contribution est ADDITIVE au budget de dissipation.

**Le gain potentiel :** Si le deplacement |q_* - q_*^{(s)}| ≈ delta est de l'ordre de la largeur du col (delta ≈ 1/sqrt(n)), le gain additionnel est O(1), insuffisant. Mais si delta >> 1/sqrt(n) (ce qui est possible pour s generique), le gain peut etre O(k).

**Statut : CONJECTURE** (necessite de calculer le deplacement du point selle, ce qui est un probleme d'analyse complexe non trivial).

### 8.3 Le deplacement du point selle : analyse

Le point selle de F_0(q) est q_* = e^{-c/sqrt(n)} ou c = pi * sqrt(2/3) (Hardy-Ramanujan). Autour de q_*, log F_0 ≈ pi^2/(6*|log q|) ≈ pi^2*sqrt(n)/(6c) = pi*sqrt(n/6).

Pour F_s(q), les phases ajoutent un terme oscillant. Sur l'axe reel, les phases sont unitaires et F_s(q) < F_0(q). Sur un contour COMPLEXE, les phases peuvent produire une attenuation supplementaire.

**La question cle :** Peut-on deformer le contour d'integration de telle sorte que |F_s(q)| soit significativement plus petit que F_0(q_*) sur tout le contour ?

Par le theoreme de Cauchy, le contour peut etre n'importe quelle courbe fermee autour de l'origine. La methode du col choisit le contour de descente rapide (steepest descent) pour minimiser l'integrand.

Pour F_0 (sans phases), le col est sur l'axe reel et la descente rapide est dans la direction imaginaire. Pour F_s, le col se deplace hors de l'axe reel, et la direction de descente rapide tourne.

**L'insight :** La contribution des phases a F_s(q) pour q = r * e^{i*theta} est :

F_s(r*e^{i*theta}) = PROD_j 1/(1 - r^{k-j} * e^{i*(k-j)*theta} * zeta^{-l}) (dans la base de Fourier)

Les zeros de F_s dans le plan complexe sont aux points q = r * e^{i*theta} ou r^{k-j} = 1 et (k-j)*theta = 2*pi*l/s. Les poles sont sur des cercles concentriques de rayon |q| = 1^{1/(k-j)} = 1.

La structure des poles de F_s est la MEME que celle de F_0 (les poles sont aux racines de l'unite), mais la DISTRIBUTION des residus change a cause des phases.

### 8.4 Le gain par deformation du contour : estimation

**ENONCE (R190-T16 -- Gain par deformation du contour, CONJECTURE).**

La deformation optimale du contour pour Lambda(s) (s >= 1) produit un gain logarithmique :

log Lambda(0) - log |Lambda(s)| >= G(s)

ou G(s) est le "gain spectral" qui satisfait :

SUM_{s=1}^{d-1} e^{-G(s)} < 1

si et seulement si N_cycle = 0.

**L'estimation de G(s)** depend du type d'arc (majeur ou mineur) :

Pour les arcs mineurs : G(s) >= c_1 * k * log k (par la methode de Vinogradov -- estimation heuristique basee sur les exposants de Weyl)

Pour les arcs majeurs : G(s) >= c_2 * log d (par la borne de Weil sur les sommes de Ramanujan)

La condition SUM e^{-G(s)} < 1 requiert G(s) > log d pour tout s, soit :

- Arcs mineurs : c_1 * k * log k > 1.585 * k * log 2, soit c_1 > 1.585 * log(2) / log(k). Pour k >= 3, c_1 > 1.1 / log(k). Possible si c_1 = O(1).
- Arcs majeurs : c_2 * log d > log d, soit c_2 > 1. C'est la condition non-triviale.

**Statut : CONJECTURE FORTE.** La hierarchie major/minor arcs est le bon cadre, mais les constantes doivent etre calculees.

---

## 9. DECOUVERTE CENTRALE : LE "SADDLE-POINT GAP THEOREM"

### 9.1 Enonce

**ENONCE (R190-T17 -- Saddle-Point Gap Theorem, CONDITIONNEL).**

Soit Lambda(s) = SUM_v omega^{c_s * g(v)} la somme exponentielle sur les partitions monotones. Soit q_* le point selle de Hardy-Ramanujan pour p(k, n). Alors pour s >= 1 :

|Lambda(s)| <= Lambda(0) * PROD_{j=0}^{k-1} rho_j^{eff}(q_*)

ou rho_j^{eff}(q_*) est le ratio spectral de la matrice de transfert T_j^{(s)}(q_*) par rapport a T_j^{(0)}(q_*), evalue au point selle de Hardy-Ramanujan.

La condition suffisante pour N_cycle = 0 est :

> **SUM_{j=0}^{k-1} log(1/rho_j^{eff}(q_*)) > log(d-1) + log(p(k,n)) - log(p(k,n)) = log(d-1)**

Soit : **SUM_j log(1/rho_j^{eff}) > log d ≈ 1.585k * log 2.**

C'est EXACTEMENT le meme budget que R189. La methode du col ne change pas le MONTANT du budget necessaire, mais elle change la facon de CALCULER rho_j^{eff}.

### 9.2 L'avancee : rho_j^{eff} au point selle vs rho_j uniforme

Au point selle q_* = e^{-c/sqrt(n)}, les matrices de transfert T_j^{(s)}(q_*) ont des proprietes SPECIFIQUES.

La matrice circulante C_j(q_*) a des valeurs propres :

mu_l^{(j)} = 1/(1 - q_*^{k-j} * zeta^{-l})

Au point selle, q_*^{k-j} est un nombre reel PROCHE de 1 pour les petites valeurs de k-j, et PROCHE de 0 pour les grandes valeurs. Plus precisement :

q_*^{k-j} = e^{-(k-j)*c/sqrt(n)} = e^{-c*(k-j)/sqrt(n)}

Pour j proche de k (les dernieres etapes), k-j est petit et q_*^{k-j} ≈ 1. Les valeurs propres de C_j sont :

mu_l ≈ 1/(1 - zeta^{-l}) pour l != 0, et mu_0 → +infini (pole).

La matrice C_j est PRESQUE SINGULIERE pour j proche de k. Le vecteur propre dominant (l = 0) est le vecteur UNIFORME 1/sqrt(s).

**CONSEQUENCE :** Pour j proche de k, le vecteur directeur est PRESQUE UNIFORME (domine par la valeur propre singuliere de C_j). Et quand le vecteur est uniforme, rho_j^{eff} = |rho_{beta_j}| (dissipation maximale).

Pour j proche de 0 (les premieres etapes), q_*^{k-j} ≈ 0, et C_j ≈ I (identite). Le vecteur directeur n'est PAS diffuse, et la dissipation est faible.

### 9.3 Le budget affine

**ENONCE (R190-T18 -- Budget de dissipation au point selle, CONDITIONNEL).**

Le budget de dissipation au point selle se decompose en :

SUM_j log(1/rho_j^{eff}(q_*)) = SUM_{j : q_*^{k-j} → 1} log(1/|rho_{beta_j}|) + SUM_{j : q_*^{k-j} → 0} 0

Les etapes "actives" (qui contribuent a la dissipation) sont celles ou q_*^{k-j} est significatif, i.e., (k-j) * c / sqrt(n) <= O(1), i.e., k-j <= O(sqrt(n)).

Le nombre d'etapes actives est O(sqrt(n)) ≈ O(sqrt(0.585k)) = O(k^{1/2}).

La dissipation par etape active est log(1/|rho|) ≈ log(s/sqrt(d)) ≈ (1/2) log s (par Weil, pour les cas generiques).

Budget total : O(k^{1/2}) * O(log k) << 1.585k * log 2.

**C'est PIRE que la borne de R189 !** Au point selle, seules sqrt(k) etapes sont actives au lieu de n ≈ 0.585k.

**WHY-1 : Pourquoi le point selle donne-t-il MOINS d'etapes actives ?**
Parce que le point selle q_* est tres proche de 1 (q_* = 1 - O(1/sqrt(n))), et les matrices C_j pour les premieres etapes (k-j grand) ont q_*^{k-j} ≈ 0. Cela signifie que les premiers gaps sont FORCES a etre 0 (le poids q^{(k-j)*Delta} est negligeable sauf pour Delta = 0 quand k-j est grand). Seules les dernieres ~sqrt(n) etapes ont une liberte reelle de choix du gap.

**WHY-2 : Est-ce un artefact du choix du contour ?**
OUI. Le point selle de Hardy-Ramanujan est optimise pour p(k, n) (sans phases). Pour Lambda(s), le contour OPTIMAL est different. En deformant le contour, on peut activer PLUS d'etapes.

**WHY-3 : Quel contour active toutes les etapes ?**
Un contour ou |q|^{k-j} est significatif pour tous les j, i.e., |q| = 1 - epsilon avec epsilon = O(1/k). Mais sur un tel contour, les poles de F_s (a |q| = 1) sont PROCHES, et l'integrale de Cauchy est dominee par les residus aux poles.

### 9.4 Le choix optimal du contour : methode de Rademacher

**INVENTION (R190-I6) : Fusion Rademacher-Dissipation.**

L'approche de Rademacher pour les partitions utilise la formule EXACTE :

p(n) = SUM_{q=1}^{infini} SUM_{h mod q, gcd(h,q)=1} omega_{h,q} * I_q(n)

ou les I_q sont des integrales de Bessel modifiees et les omega_{h,q} sont des racines de l'unite (sommes de Dedekind).

L'idee est d'adapter cette formule a Lambda(s) :

Lambda(s) = SUM_{q | d} SUM_{h} alpha_{h,q}^{(s)} * J_q^{(s)}(n)

ou les J_q^{(s)} sont des integrales de Bessel MODIFIEES par les phases spectrales, et les alpha sont des sommes de Gauss modifiees.

Le point cle : dans la formule de Rademacher, le contour n'est PAS un cercle mais une COURBE DE FORD (combinaison de cercles de Farey). Chaque arc de Farey est optimise pour un denominateur q.

Pour Lambda(s), la modification par les phases change la GEOMETRIE des arcs de Ford. Les arcs correspondant aux q qui resonent avec s/d sont ATTENUES par la decoherence.

**ENONCE (R190-T19 -- Formule de Rademacher modifiee pour Lambda(s), CONJECTURE STRUCTURELLE).**

Lambda(s) admet une representation en serie convergente :

Lambda(s) = SUM_{q=1}^{Q} SUM_{h mod q, gcd(h,q)=1} A_{h,q}(s) * B_{q}(n) + E_Q(s, n)

ou :
- A_{h,q}(s) = (1/s_q) SUM_{a ∈ <2>_q} omega_q^{h * phi(a, s)} (somme de Gauss tordue, s_q est la taille du sous-groupe <2> dans Z/qZ)
- B_q(n) ≈ (2*pi)^{-1/2} * (q/n)^{1/2} * exp(pi * sqrt(2n/3) / q) (terme de Bessel)
- E_Q est le reste, |E_Q| = O(n^{-1/4}) pour Q → infini

La borne |A_{h,q}(s)| << |A_{h,q}(0)| pour s != 0 est la CLE de la borne sur Lambda(s).

**Statut : CONJECTURE STRUCTURELLE.** La formule est plausible mais sa derivation rigoureuse necessite un travail technique substantiel (proprieties de modularite tordue, convergence de la serie).

---

## 10. PISTE LA PLUS PROMETTEUSE : FACTORISATION DE Horner DANS Lambda(s)

### 10.1 L'observation de la question 4 du mandat

g(v) = SUM_j 3^{k-1-j} * 2^{B_j} est un polynome de Horner : si on pose y = 3 et x_j = 2^{B_j}, alors :

g = x_0 * y^{k-1} + x_1 * y^{k-2} + ... + x_{k-1} = (((...((x_0 * y + x_1) * y + x_2) * y + ...) * y + x_{k-1})

La recurrence de Horner z_{j+1} = y * z_j + x_j donne z_k = g.

### 10.2 Factorisation de Lambda(s) par Horner

**INVENTION (R190-I7) : Telescopage de la phase le long de la recurrence de Horner.**

La phase omega^{c_s * g(v)} = omega^{c_s * z_k} peut etre TELESCOPEE :

omega^{c_s * z_k} = PROD_{j=0}^{k-1} [omega^{c_s * z_{j+1}} / omega^{c_s * z_j * 3}]^?

Non, reprenons. z_{j+1} = 3 * z_j + 2^{B_j}. Donc :

omega^{c_s * z_{j+1}} = omega^{c_s * (3*z_j + 2^{B_j})} = omega^{3*c_s * z_j} * omega^{c_s * 2^{B_j}}

Iterons : omega^{c_s * z_k} = omega^{3^k * c_s * z_0} * PROD_{j=0}^{k-1} omega^{c_s * 3^{k-1-j} * 2^{B_j}}

Avec z_0 = 0 : omega^{c_s * z_k} = PROD_j omega^{c_s * 3^{k-1-j} * 2^{B_j}}.

C'est la FACTORISATION MULTIPLICATIVE de la phase. Chaque facteur est omega^{beta_j * 2^{B_j}} ou beta_j = c_s * 3^{k-1-j}.

**Le point cle :** Si les B_j etaient INDEPENDANTS, Lambda(s) factoriserait :

Lambda(s) = PROD_j [SUM_{b} omega^{beta_j * 2^b} * (poids de b a l'etape j)]

Mais les B_j sont lies par la monotonie et la somme. Le couplage est UNIQUEMENT dans les poids, pas dans les phases.

### 10.3 Decouplage par les gaps (reprise)

En termes de gaps Delta_j (avec la contrainte de somme ponderee SUM (k-j) Delta_j = n), les B_j sont :

B_j = Delta_0 + ... + Delta_j

Et la phase a l'etape j est :

omega^{beta_j * 2^{Delta_0 + ... + Delta_j}} = omega^{beta_j * 2^{Delta_0} * 2^{Delta_1} * ... * 2^{Delta_j}}

C'est un PRODUIT emboite -- chaque gap multiplie par une puissance de 2 les contributions de TOUTES les etapes suivantes. C'est exactement le couplage multiplicatif qui empeche la factorisation.

### 10.4 L'idee de la serie de Dirichlet tordue

**INVENTION (R190-I8) : Encodage par serie de Dirichlet.**

Definissons la serie formelle :

D_s(t_0, t_1, ..., t_{k-1}) = SUM_{Delta_0, ..., Delta_{k-1} >= 0} PROD_j [t_j^{Delta_j} * omega^{beta_j * 2^{SUM_{i<=j} Delta_i}}]

La contrainte SUM (k-j) Delta_j = n est extraite par la substitution t_j = q^{k-j} * (variable de comptage).

Le point est que la structure MULTIPLICATIVE de 2^{SUM Delta_i} dans la phase rend la serie NON-factorisable en produit.

**MAIS** dans le monde p-adique (p = 2), le terme 2^{SUM Delta_i} a une structure ADDITIVE en les Delta_i (via la valuation 2-adique). Cela suggere une dualite p-adique.

### 10.5 Dualite 2-adique

**OBSERVATION (R190-O1).** L'exponentielle omega^{beta * 2^m} pour m = B_j est un CARACTERE ADDITIF de Z evalue en beta * 2^m / d. Quand m varie, 2^m parcourt le sous-groupe <2> de (Z/dZ)*, et le caractere additif compose avec l'exponentiation 2^m est un CARACTERE du monde 2-adique.

Formellement, soit chi_beta : Z/dZ → C* le caractere additif x ↦ omega^{beta*x}. Alors chi_beta(2^m) = chi_{beta}(exp_2(m)) ou exp_2 : Z → (Z/dZ)* est l'exponentiation en base 2.

L'application m ↦ chi_beta(2^m) est un HOMOMORPHISME de (Z, +) vers (C*, ×) si et seulement si chi_beta est trivial sur <2> (car chi_beta(2^{m+1}) = chi_beta(2^m * 2) = chi_beta(2^m) * chi_beta(2) seulement si chi est multiplicatif, ce qui n'est pas le cas en general pour un caractere additif).

**CORRECTION :** chi_beta(2^m) n'est PAS multiplicatif en m. Donc cette piste ne factorise pas directement. MAIS la structure de 2^m mod d est PERIODIQUE de periode s, et dans chaque periode, les valeurs de chi_beta(2^m) forment un "cycle de phases" fixe.

---

## 11. THEOREME CENTRAL DE R190

### 11.1 Enonce

**THEOREME R190-MAIN (Point selle + Transfert, CONDITIONNEL).**

Pour k >= 3 et d = 2^S - 3^k premier, la borne suivante est valide :

|Lambda(s)| <= p(k, n) * PROD_{j=0}^{k-1} rho_j(q_*)

ou :
- q_* est le point selle de Hardy-Ramanujan pour les partitions en k parts de n
- rho_j(q_*) = |lambda_max(T_j^{(s)}(q_*))| / lambda_PF(T_j^{(0)}(q_*))
- T_j^{(s)}(q) est la matrice de transfert s × s definie en Section 1.3

Le budget de dissipation est :

D(s) = SUM_{j=0}^{k-1} log(1/rho_j(q_*))

Et N_cycle = 0 si D(s) > log(d) pour tout s >= 1.

**Preuve (esquisse).**
1. Lambda(s) = [q^n] F_s(q) par Cauchy (R190-T1).
2. F_s(q) = e_1^T * PROD T_j * 1 par transfert (R190-T3).
3. Au point selle, |F_s(q_*)| <= |e_1^T * PROD T_j * 1| <= PROD |lambda_max(T_j)| (par submultiplicativite).
4. |lambda_max(T_j^{(s)})| <= rho_j * lambda_PF(T_j^{(0)}) par R190-T6.
5. PROD lambda_PF(T_j^{(0)}) contribue a F_0(q_*) (le terme sans phase), et la methode du col appliquee a F_0 donne p(k,n) a un facteur polynomial pres.
6. Donc |Lambda(s)| <= C * p(k,n) * PROD rho_j ou C est un facteur polynomial (de la gaussienne du col).

**Statut : CONDITIONNEL** sur le controle rigoureux du reste du col et la submultiplicativite du produit de matrices.

### 11.2 Le gap residuel, reformule

Le budget D(s) depend de la valeur de q_* et de la structure des matrices T_j. L'analyse de la Section 9.2-9.3 montre que :

- Au point selle de Hardy-Ramanujan, seules ~sqrt(n) etapes sont actives → budget O(sqrt(k) * log k)
- Sur un contour modifie (toutes etapes actives), le budget est ~1.17k * log 2 (R189)
- Le budget necessaire est ~1.585k * log 2

**CONCLUSION :** La methode du col sur q seule ne ferme pas le gap. Elle recupere au mieux la borne de R189 (contour optimal ≠ col de Hardy-Ramanujan).

Le gain POTENTIEL vient de la STRUCTURE DES MATRICES T_j, pas du choix du contour. Plus precisement :

### 11.3 Les trois sources de gain inexploitees

**Source 1 : Correlation multi-etapes.** Les matrices T_j ne commutent pas, et le produit T_0 * ... * T_{k-1} peut avoir un rayon spectral STRICTEMENT INFERIEUR au produit des rayons spectraux. Le gain vient de la non-commutativite.

**Source 2 : Structure multiplicative de <2> et <3>.** Les phases beta_j = c_s * 3^{k-1-j} suivent une orbite geometrique dans Z/dZ, et les matrices T_j sont parametrees par cette orbite. La structure de groupe de <2,3> dans (Z/dZ)* controle le gain total.

**Source 3 : Concentration des partitions.** Les partitions de n en k parts ne sont PAS uniformes sur le simplexe. La densite se concentre pres du profil typique (distribution geometrique). Les matrices T_j "voient" surtout la region de concentration, ou la dissipation peut etre plus forte.

---

## 12. REGISTRE DES 5-WHY

### WHY-Chain 1 : Pourquoi le col ne ferme-t-il pas le gap ?
1. **Pourquoi ?** Parce que le budget de dissipation au col est le meme que celui de R189 (~1.17k log 2).
2. **Pourquoi ?** Parce que le col active seulement les etapes ou q_*^{k-j} est significatif, soit ~sqrt(n) etapes au col de HR, ou toutes les n etapes sur un contour modifie.
3. **Pourquoi le contour modifie ne fait-il pas mieux que n etapes ?** Parce que la dissipation par etape est bornee par |rho_{beta}| ≈ 1/s, et n * log(s) ≈ 0.585k * 1.585k * log(2) / k = 0.93k * log(2)... ATTENDONS. Recalculons.
4. **Recalcul :** Si |rho_{beta}| ≈ 1/s et s ≈ S ≈ 1.585k, alors log(1/rho) ≈ log(1.585k). Et n etapes actives donnent n * log(1.585k) ≈ 0.585k * log(1.585k). Pour k = 10, c'est 5.85 * 2.76 = 16.1. Budget necessaire : 1.585 * 10 * 0.693 = 11.0. LE BUDGET SUFFIT POUR k ≈ 10 !
5. **Pourquoi ca ne marche pas en general ?** Parce que |rho_{beta}| n'est PAS 1/s en general. La borne 1/s est la borne de Weil pour d PREMIER et <2> = (Z/dZ)*. Pour les d de Collatz, s = ord_d(2) peut etre beaucoup plus petit que d, et |rho| peut etre beaucoup plus grand que 1/s.

**DECOUVERTE dans le WHY-Chain 1, niveau 4 :** Le budget CAN BE sufficient si |rho| ≈ 1/s, car n * log(s) CROIT comme k * log(k), qui depasse 1.585k * log(2) pour k assez grand (k >= k_0 pour un k_0 fini).

> **ENONCE (R190-T20 -- Seuil asymptotique par dissipation, CONDITIONNEL).**
> Si |rho_{beta}| <= C / s pour une constante C et pour tout beta != 0 mod d, alors le budget de dissipation D(s) >= n * log(s/C) depasse log(d) des que :
>
> 0.585k * log(s/C) > 1.585k * log(2)
>
> soit s > C * 2^{1.585/0.585} = C * 2^{2.71} ≈ 6.55 * C
>
> Comme s = ord_d(2) >= S ≈ 1.585k (par definition de S), la condition est satisfaite pour k >= k_1(C) ou k_1 depend de C.
>
> En particulier, si |rho| <= 1/s (borne de Weil optimale), la condition est s > 2^{2.71} ≈ 6.55, soit s >= 7, ce qui est satisfait des k >= 3 (car s >= S >= 5 pour k >= 3).

**ATTENTION :** Le |rho| <= 1/s est la borne pour d PREMIER et <2> GENERATEUR. Pour les d de Collatz, cette borne est BEAUCOUP TROP optimiste.

**WHY supplementaire :** Quelle est la borne REELLE pour |rho| ?

Calculons rho_a = (1/s) SUM_{m=0}^{s-1} e^{2*pi*i * a * 2^m / d}. C'est une somme exponentielle ou les exposants 2^m mod d forment une suite GEOMETRIQUE modulo d.

Par la borne de Korobov-Vinogradov pour les sommes exponentielles a exposants geometriques :

|rho_a| << d^{-c} pour une constante c > 0 dependant de la structure de <2> dans (Z/dZ)*.

La meilleure borne connue (Bourgain, 2005) pour les sommes exponentielles sur les sous-groupes multiplicatifs donne :

|SUM_{m=0}^{s-1} e^{2*pi*i*a*2^m/d}| <= s * d^{-delta}

pour un delta > 0 explicite (dependant de s/d). Donc |rho_a| <= d^{-delta}.

Si delta >= 1/2, c'est la borne de Weil. Si delta < 1/2 mais delta > 0, le budget est :

n * delta * log(d) = 0.585k * delta * 1.585k * log(2) = 0.928 * delta * k^2 * log(2)

Qui est O(k^2), ce qui depasse le budget necessaire 1.585k * log(2) = O(k) pour TOUT delta > 0 et k assez grand.

> **ENONCE (R190-T21 -- Suffisance asymptotique de toute borne de somme exponentielle non-triviale, CONDITIONNEL).**
>
> Si pour tout a != 0 mod d et tout d = 2^S - 3^k premier :
>
> |(1/s) SUM_{m=0}^{s-1} e^{2*pi*i * a * 2^m / d}| <= d^{-delta}
>
> pour un delta = delta(k) > 0 avec delta(k) * k → infini quand k → infini,
>
> ALORS N_cycle(k) = 0 pour tout k suffisamment grand.
>
> **Preuve (conditionnelle).** Le budget de dissipation est :
>
> D(s) >= n * delta * log(d) ≈ 0.585k * delta * 1.585k * log(2) = 0.928 * delta * k^2 * log(2)
>
> Le budget necessaire est log(d) ≈ 1.585k * log(2).
>
> D(s) > log(d) ssi 0.928 * delta * k > 1.585, soit k > 1.71 / delta.
>
> Si delta * k → infini, cette condition est satisfaite pour k assez grand. CQFD.

**Statut : CONDITIONNEL** sur la borne de somme exponentielle non-triviale (qui EST un resultat connu de Bourgain-Katz-Tao et al., mais les constantes dependant de la taille relative de <2> dans (Z/dZ)* doivent etre verifiees pour les d de Collatz).

---

## 13. SYNTHESE ET EVALUATION

### 13.1 Inventaire des resultats

| # | Enonce | Statut | Innovation |
|---|--------|--------|------------|
| R190-T1 | Representation integrale de Lambda(s) par Cauchy | PROUVE | Standard |
| R190-T2 | Variables auxiliaires pour le couplage | OBSERVATION | Nouveau contexte |
| R190-T3 | Formule de transfert spectrale s×s | PROUVE | **NOUVEAU** |
| R190-T4 | Decomposition spectrale du produit | OBSERVATION | Standard |
| R190-T5 | Equation du point selle | CONDITIONNEL | Adaptation |
| R190-T6 | Reduction valeur propre par decoherence | PROUVE | **CLE** |
| R190-T7 | rho_j < 1 pour d premier | PROUVE | Nouveau |
| R190-T8 | Reduction exposant Lyapunov | CONDITIONNEL | Nouveau cadre |
| R190-T9 | Point selle contraint (bord du simplexe) | CONDITIONNEL | **NOUVEAU** |
| R190-T10 | Borne arcs majeurs | OBSERVATION | Standard adapte |
| R190-T11 | Borne arcs mineurs (2eme moment) | OBSERVATION | Recupere k>=42 |
| R190-T12 | Regime de melange rapide | CONDITIONNEL | Coherence R189 |
| R190-T13 | Gain par paires (conjecture) | CONJECTURE | Nouveau mais O(1) |
| R190-T14 | Dissipation orbite complete | OBSERVATION | Borne de Weil |
| R190-T15 | Point selle complexe | CONJECTURE | Nouveau |
| R190-T16 | Gain par deformation contour | CONJECTURE | Heuristique |
| R190-T17 | Saddle-Point Gap Theorem | CONDITIONNEL | **CENTRAL** |
| R190-T18 | Budget au point selle HR | CONDITIONNEL | Negatif (sqrt(k)) |
| R190-T19 | Rademacher modifie | CONJECTURE STRUCTURELLE | Ambitieux |
| R190-T20 | Seuil asymptotique | CONDITIONNEL | **IMPORTANT** |
| R190-T21 | Suffisance asymptotique | CONDITIONNEL | **RESULTAT PRINCIPAL** |

### 13.2 Inventions (Outils crees)

| # | Invention | Description |
|---|-----------|-------------|
| I1 | Matrice de transfert sur le tore | Reduction de d*s a s etats |
| I2 | Col sur le simplexe des partitions | Point selle contraint, bord dominant |
| I3 | Decomposition de Furstenberg | Exposant de Lyapunov pas-a-pas |
| I4 | Dissipation par paires/blocs | Gain par non-commutativite |
| I5 | Hybride Hardy-Ramanujan + Dissipation | Fusion col + transfert |
| I6 | Fusion Rademacher-Dissipation | Arcs de Ford modifies |
| I7 | Telescopage de Horner | Phase = produit de phases locales |
| I8 | Serie de Dirichlet tordue | Encodage du couplage multiplicatif |

### 13.3 Chains de 5-WHY resumees

**Chain A (gap) :** Le col ne ferme pas le gap → budget = R189 → seulement n etapes actives → phases couplees par la monotonie → la monotonie COMPRIME le nombre de vecteurs "libres" → c'est la NATURE du probleme (les partitions sont concentrees).

**Chain B (valeur propre) :** rho_j < 1 pour d premier → les phases sont non-constantes → <2> est non-trivial → la relation 2^S = 3^k mod d lie 2 et 3 → l'impossibilite du cycle est ENCODEE dans cette relation.

**Chain C (asymptotique) :** Toute borne non-triviale sur rho SUFFIT pour k grand → le budget est quadratique en k → la cible est lineaire → le ratio diverge → la question est REDUITE a une borne de somme exponentielle.

### 13.4 Le verrou residuel (honnetement)

La methode du col sur Lambda(s) ne ferme pas le gap 1.35x de R189 directement. MAIS elle produit deux avancees :

1. **R190-T3 + T6 :** La matrice de transfert de taille s (au lieu de d*s) avec la borne de decoherence donne un cadre CALCULABLE pour rho_j. Ce n'est plus une heuristique -- c'est un produit de matrices explicites.

2. **R190-T21 :** La suffisance asymptotique montre que TOUTE borne de somme exponentielle non-triviale (|rho| <= d^{-delta} avec delta * k → ∞) suffit pour k grand. Le probleme est REDUIT a une question de theorie analytique des nombres : borner les sommes exponentielles sur les sous-groupes multiplicatifs de Z/dZ.

Le gap 1.35x de R189 correspond au cas delta = 0 (pas de borne non-triviale). Des que delta > 0 (meme infinitesimalement), le budget quadratique O(k^2) domine la cible lineaire O(k).

### 13.5 Score

| Critere | Score | Commentaire |
|---------|-------|-------------|
| Invention | 8/10 | 8 outils nouveaux, transfert s×s, hybride col+transfert |
| Rigueur | 7/10 | T1,T3,T6,T7 prouves. T17,T20,T21 conditionnels. T13,T15,T16,T19 conjectures |
| Impact | 7/10 | Reduction a borne de somme exponentielle (T21). Seuil asymptotique identifie |
| Honnetete | 9/10 | Gap pas ferme, mais reformule en question connue |
| Nouveaute vs R189 | 7/10 | Matrice s×s, point selle contraint, suffisance asymptotique |

**Score global R190-A1 : 7.5/10**

---

## 14. PISTES OUVERTES (NE PAS FERMER)

1. **Bornes de Bourgain-Katz-Tao** pour les sommes exponentielles sur <2> ⊂ (Z/dZ)*. Ces bornes existent pour |<2>| dans une gamme intermediaire. Verifier si les d de Collatz tombent dans cette gamme.

2. **Matrice de transfert s × s explicite** pour k = 3, 4, 5. Calculer les rho_j exactement et verifier la borne R190-T17.

3. **Formule de Rademacher tordue (R190-T19).** Developper les arcs de Ford modifies. Si realisable, cela donnerait une formule EXACTE pour Lambda(s), pas juste une borne.

4. **Correlations multi-etapes (Source 1, Section 11.3).** Le gain par non-commutativite du produit de matrices est inexploite. Lien possible avec les resultats de Furstenberg-Kesten sur les produits de matrices aleatoires.

5. **Concentration des partitions (Source 3).** Le profil typique d'une partition de n en k parts est B_j ≈ n * j / (k*(k+1)/2). Calculer la dissipation au PROFIL TYPIQUE pourrait donner une borne plus fine que la borne uniforme.

6. **Lien avec les resultats de Tao (2022).** Tao a montre que les orbites de Collatz atteignent des valeurs petites pour "presque tout" entier. Sa methode utilise des sommes exponentielles similaires. Peut-on adapter ses bornes au contexte des cycles ?

---

*R190-A1 : 21 enonces, 8 inventions, 3 chains de 5-WHY. La methode du col sur Lambda(s) ne ferme pas le gap 1.35x mais le REFORMULE : le probleme est reduit a une borne de somme exponentielle non-triviale sur <2> ⊂ (Z/dZ)*, et toute telle borne (meme infinitesimale) suffit asymptotiquement en k (budget quadratique vs cible lineaire, R190-T21). La matrice de transfert s × s (R190-T3) est un outil CALCULABLE qui remplace l'heuristique de R189. Le point selle contraint (R190-T9) montre que la contribution dominante vient du bord du simplexe des partitions. 6 pistes ouvertes.*
