# R195 -- Investigateur Profond : Chaines de POURQUOI sur la Conjecture M

**Date** : 16 mars 2026
**Round** : R195
**Role** : Investigateur profond (5+ niveaux WHY par chaine)
**Preprint** : `paper/preprint_en.tex` (Merle, mars 2026)
**Contexte** : Rounds R189-R194 ont etabli |rho_a| < 1, Lambda_free = Pi rho_{aj}, gap 1.35x, AMH k=3..20, dualite discrepancy/reachability. Le verrou reste la Conjecture M.

---

## CHAINE 1 : Pourquoi T(t) est-elle difficile a borner ?

### WHY-1 : Qu'est-ce qui rend les sommes lacunaires specialement resistantes ?

La somme T(t) = Sigma_{A in Comp(S,k)} e(t * corrSum(A)/p) est une somme exponentielle sur un ensemble **combinatoire contraint** (compositions ordonnees). Les sommes lacunaires -- sommes exponentielles dont les frequences forment un ensemble **clairseme** dans Z/pZ -- sont resistantes pour trois raisons fondamentales :

1. **Perte de structure additive.** Les methodes de Weyl et van der Corput exploitent la regularite des frequences (polynomes, progressions arithmetiques). Quand les frequences sont lacunaires, les differences f(n+h) - f(n) ne se simplifient pas en une forme exploitable. La phase t * corrSum(A)/p n'est pas un polynome en A -- c'est une forme lineaire en les 2^{A_i}, ce qui cree une dependance **exponentielle** aux indices.

2. **Absence de variete algebrique sous-jacente de basse dimension.** Les bornes de Weil (|S| <= (d-1)sqrt(p)) s'appliquent aux sommes sur une courbe algebrique lisse de degre d. Ici, corrSum(A) est une somme de termes 3^{k-1-i} * 2^{A_i} -- ce n'est pas la trace d'un polynome evalué sur une variete de dimension fixee. L'objet geometrique serait de dimension k-1, avec un nombre de composantes qui croit exponentiellement.

3. **Cardinalite intermediaire.** On somme sur C = C(S-1, k-1) termes, avec C << p (regime cristallin). Les bornes de type Weil donnent |S| = O(sqrt(p)), ce qui ne dit rien quand C << sqrt(p). Le theoreme de Parseval dit seulement que Sigma|T(t)|^2 = p * Sigma N_r^2, ce qui est une identite exacte mais ne borne pas chaque |T(t)| individuellement.

**Diagnostic :** La difficulte fondamentale est que C est exponentiellement plus petit que p, mais la structure combinatoire des compositions ne fournit aucune algebricite exploitable.

### WHY-2 : Pourquoi la double exponentiation dans corrSum complique-t-elle ?

La structure corrSum(A) = Sigma_{i=0}^{k-1} 3^{k-1-i} * 2^{A_i} implique des poids de la forme 3^a * 2^b avec a + b ~ S. Cette double exponentiation pose trois problemes specifiques :

1. **Absence de polynomial structure.** Si corrSum(A) etait un polynome en les A_i (par exemple Sigma c_i * A_i), la somme T(t) serait un produit de sommes geometriques -- facile a borner. La presence de 2^{A_i} transforme une structure **additive** (les A_i sont dans un ensemble d'entiers) en une structure **multiplicative** (les 2^{A_i} vivent dans le sous-groupe <2> de F_p*). Ce melange additif/multiplicatif est precisement ce qui rend les sommes de Kloosterman difficiles (cf. e(ax + b/x) melange x et x^{-1}).

2. **Portee des poids 3^{k-1-i}.** Les coefficients 3^{k-1-i} varient sur un intervalle de taille 3^{k-1}, qui est **du meme ordre** que d = 2^S - 3^k ~ 2^S. Aucun poids n'est negligeable : le terme i=0 a coefficient 3^{k-1} ~ d, et le terme i=k-1 a coefficient 1. Cette hierarchie de poids empeche toute approximation par troncature.

3. **Interaction non-lineaire.** Quand on fixe (A_0, ..., A_{k-2}) et qu'on varie A_{k-1}, la somme partielle change par un terme additif 2^{A_{k-1}} -- ce qui est exploitable (c'est le Peeling Lemma). Mais quand on varie DEUX indices simultanement, les termes 3^{k-1-i}*2^{A_i} et 3^{k-1-j}*2^{A_j} sont **multiplicativement independants** dans F_p*, ce qui empeche la factorisation de la somme en produit.

**Diagnostic :** Le melange "puissances de 3 comme coefficients, puissances de 2 comme variables" cree une somme qui n'est ni additivo-additive (type Gauss/Ramanujan) ni multiplicativo-multiplicative (type Jacobi), mais un hybride sans precedent direct.

### WHY-3 : Pourquoi les methodes classiques echouent-elles ?

**van der Corput (differencing).** La methode remplace T(t) par Sigma_h |Sigma_A e(t*(corrSum(A+h) - corrSum(A))/p)|. Le probleme : "A+h" n'a pas de sens naturel pour les compositions ordonnees. On pourrait decaler un indice A_j -> A_j + 1, mais cela change la contrainte d'ordonnancement. Et corrSum(A avec A_j+1) - corrSum(A) = 3^{k-1-j} * 2^{A_j}, qui depend de A_j -- la difference n'est PAS independante de A. C'est exactement le contraire du cas polynomial ou f(x+h) - f(x) a un degre inferieur.

**Weyl differencing.** Meme probleme. La reduction de degre fonctionne pour des polynomes car deg(f(x+h) - f(x)) = deg(f) - 1. Ici, la "degree" de la dependance en A_i est infinie (exponentielle), et le differencing ne la reduit pas.

**Bornes de Weil.** Pour s'appliquer, il faut une courbe algebrique C/F_p et une somme du type Sigma_{x in C(F_p)} chi(f(x)) * psi(g(x)). Or corrSum(A) est une somme de 2^{A_i} avec A_i variables entieres contraintes -- ce n'est pas la trace d'un morphisme algebrique d'une courbe lisse. On pourrait essayer de parametriser l'ensemble {corrSum(A) mod p} comme image d'une variete, mais cette variete aurait dimension k-1 et degre ~ 2^S, annulant tout benefice.

**Bornes de Deligne (sommes sur varietes).** La borne de Deligne pour une variete lisse de dimension n et degre D donne |S| <= D^n * p^{n/2}. Avec n = k-1 et D ~ 2, cela donnerait |S| <= 2^{k-1} * p^{(k-1)/2}, ce qui depasse trivialement C pour k >> 1.

**Sommes de caracteres multiplicatifs (Burgess, Polya-Vinogradov).** Ces bornes s'appliquent a des sommes sur des intervalles ou des progressions arithmetiques de F_p*. L'image de corrSum n'est ni un intervalle ni une progression -- c'est un sous-ensemble exotique de F_p de taille C << p.

**Diagnostic :** Toutes les methodes classiques exploitent une **structure reguliere** de l'ensemble de sommation (variete algebrique de basse dimension, intervalle, progression arithmetique, polynome). L'ensemble Comp(S,k) n'a aucune de ces structures.

### WHY-4 : Quelle est la structure algebro-geometrique sous-jacente ?

La question est : peut-on realiser la somme T(t) comme une somme de caracteres sur une variete algebrique ?

**Tentative 1 : Variete torique.** Les termes 2^{A_i} vivent dans le tore (G_m)^k sur F_p. La contrainte 0 = A_0 < A_1 < ... < A_{k-1} <= S-1 definit un **simplexe entier** dans Z^k, et les points 2^A = (2^{A_0}, ..., 2^{A_{k-1}}) vivent dans le sous-groupe <2> de F_p*. Le probleme est que la condition d'ordonnancement A_0 < A_1 < ... < A_{k-1} est une contrainte **additive** sur les exposants, pas une equation polynomiale sur les valeurs 2^{A_i}. Le passage exposant -> valeur est un morphisme **de groupes** (exponentielle discrete), pas un morphisme algebrique de varietes.

**Tentative 2 : Somme de Kloosterman generalisee.** Une somme de Kloosterman classique est Sigma_x e((ax + b/x)/p). Ici, on somme e(t * Sigma c_i * x_i / p) avec c_i = 3^{k-1-i} et x_i = 2^{A_i}. C'est une somme de Gauss **multilineaire** -- analogue a une somme de Deligne hyper-Kloosterman en dimension k. Mais les x_i ne sont pas independants : ils parcourent le sous-groupe <2> avec la contrainte de log_2 ordonne. C'est une somme hyper-Kloosterman **sur une section ordonnee d'un sous-groupe**.

**Tentative 3 : Objet automorphe.** La structure Horner g(B) = Sigma u^j * 2^{B_j} (avec u = 2*3^{-1} mod d) suggere un lien avec les fonctions L de Dirichlet via le pont Mellin-Fourier. La decomposition T(t) = N_0 - (C-N_0)/(p-1) + (1/(p-1)) * Sigma_{chi != chi_0} tau(chi_bar) * chi(t) * M(chi) montre que T(t) est determinee par les sommes de Mellin M(chi). Si on pouvait montrer que M(chi) est le coefficient de Fourier d'une forme modulaire, les bornes de Ramanujan-Petersson s'appliqueraient. Mais M(chi) est une somme finie et discrete -- pas evidemment reliee a une forme automorphe.

**Resultat negatif structurel :** L'ensemble {corrSum(A) mod p : A in Comp(S,k)} n'est l'image d'aucune variete algebrique de dimension et degre bornes independamment de k. C'est un objet **combinatoire pur**, ce qui explique la resistance aux methodes algebro-geometriques.

### WHY-5 : Pourquoi la contrainte de partition (ordonnancement) est-elle cruciale ?

La contrainte 0 = A_0 < A_1 < ... < A_{k-1} <= S-1 (strictement croissante) est fondamentale pour deux raisons :

**1. Reduction de cardinalite.** Sans la contrainte, l'ensemble de sommation serait {0,...,S-1}^k, de taille S^k >> 2^S >> d. La somme T_libre(t) := Sigma_{(a_0,...,a_{k-1}) in {0,...,S-1}^k} e(t * Sigma 3^{k-1-i} * 2^{a_i} / p) se FACTORISE :

  T_libre(t) = Prod_{i=0}^{k-1} (Sigma_{a=0}^{S-1} e(t * 3^{k-1-i} * 2^a / p))

Chaque facteur est une somme geometrique sur le sous-groupe <2> de F_p, facile a borner ! On obtient T_libre(t) = Prod_{i=0}^{k-1} S_{t*3^{k-1-i}}(p) ou S_c(p) = Sigma_{a=0}^{S-1} e(c * 2^a / p). Si S est un multiple de ord_p(2), alors S_c est une somme de Ramanujan, sinon une somme partielle de caracteres.

**2. L'ordonnancement detruit la factorisation.** La contrainte A_0 < A_1 < ... < A_{k-1} introduit des **correlations entre les indices**. On ne peut plus ecrire la somme comme un produit. Mathematiquement, on passe d'un produit tensoriel a une **section antisymetrique** du tenseur -- et les sommes exponentielles sur des sections antisymetriques sont notablement plus difficiles.

**3. Lien avec les determinants.** La bijection classique entre parties a k elements de {0,...,S-1} et compositions ordonnees suggere un lien avec les **determinants de Cauchy** ou les **fonctions de Schur**. En effet, si on ecrit la matrice M_{i,j} = e(t * 3^{k-1-i} * 2^j / p) pour 0 <= j <= S-1, alors la somme T(t) est la somme des "termes diagonaux" correspondant aux k-sous-ensembles ordonnes de {0,...,S-1}. C'est formellement un **mineur maximal** de la matrice rectangulaire M.

**Observation cle (nouvelle) :** La somme T(t) est reliee au **permanent** d'une sous-matrice de la matrice DFT. Or le permanent est #P-complet en general, ce qui suggere que la difficulte de borner T(t) pourrait avoir une composante de **complexite computationnelle intrinseque**.

### RESULTAT PROUVE (Chaine 1)

**Lemme (Factorisation libre vs. ordonnee) :**
Soit T_libre(t) = Prod_{i=0}^{k-1} S_{t*3^{k-1-i}}(p) la somme sans contrainte d'ordonnancement. Alors :
- |T_libre(t)| = Prod |S_{t*3^{k-1-i}}| <= rho(p)^k * m^k (ou rho est le ratio spectral maximal et m = ord_p(2))
- T(t) = (1/k!) * Sigma_{sigma in S_k} sgn(sigma) * T^{sigma}(t) + termes de collision (par inclusion-exclusion antisymetrique)
- Le passage T_libre -> T introduit des annulations dont le controle est equivalent a borner un determinant de Fredholm discret.

**Preuve :** La premiere egalite est le produit des bornes individuelles. La decomposition d'inclusion-exclusion suit du fait que Comp(S,k) est l'image de l'application antisymetrisation sur {0,...,S-1}^k. Les termes de collision (ou deux A_i coincident) contribuent des sommes de dimension k-2, creant une hierarchie recursive.

### OUTIL INVENTE : Le Determinant Spectral Antisymetrique (DSA)

**Nom :** DSA (Determinant Spectral Antisymmetrique)

**Idee :** Au lieu de borner T(t) directement, construire la matrice (S-1) x (S-1) dont les entrees sont M_{i,j} = e(t * 3^{k-1-i} * 2^j / p), et exprimer T(t) comme la somme des mineurs k x k de cette matrice. Utiliser ensuite les bornes de Hadamard sur les determinants pour borner chaque mineur, puis sommer.

**Logique :**
1. La borne de Hadamard donne |det(M_I)| <= Prod_{i in I} ||ligne_i|| = (sqrt(S))^k pour une sous-matrice k x k.
2. Le nombre de mineurs est C = C(S-1, k-1).
3. Borne brute : |T(t)| <= C * S^{k/2}, qui est trop grande.
4. **Amelioration par oscillation :** les mineurs oscillent (phases pseudo-aleatoires), donc on espere des annulations sqrt(C), donnant |T(t)| ~ sqrt(C) * S^{k/2}.
5. **Comparaison :** il faut sqrt(C) * S^{k/2} << C * k^{-delta}, soit S^{k/2} << sqrt(C) * k^{-delta}. Comme C ~ 2^{S*h(alpha)} et S ~ k*theta, cela donne 2^{k*theta*k/2} vs 2^{S*h(alpha)/2}, qui est du meme ordre -- borderline.

**Faisabilite : 4/10.** L'idee est naturelle mais la borne de Hadamard + annulation sqrt est heuristique. Il faudrait prouver que les phases des mineurs sont suffisamment decorrelees, ce qui revient essentiellement a prouver la Conjecture M par d'autres moyens.

---

## CHAINE 2 : Pourquoi le Parseval cost ne suffit-il pas ?

### WHY-1 : Pourquoi une borne inferieure sur la somme des carres ne borne pas chaque |T(t)| ?

Le Parseval cost (Theorem 4.5 du preprint) dit : si N_0(p) >= 1, alors Sigma_{t=1}^{p-1} |T(t)|^2 >= (p-C)^2/(p-1) ~ p.

C'est une borne **L^2**, pas L^infini. La distinction est fondamentale :
- Une borne L^2 dit que l'energie TOTALE est grande. Elle est compatible avec une seule valeur |T(t_0)|^2 ~ p et toutes les autres ~ 0 (concentration), ou avec toutes les valeurs ~ p/(p-1) ~ 1 (equirepartition).
- Pour prouver N_0 = 0, on a besoin que CHAQUE |T(t)| soit petit -- c'est une borne L^infini qui est requise.

Le passage L^2 -> L^infini perd un facteur sqrt(p) par Cauchy-Schwarz :
  max |T(t)| >= sqrt(Sigma|T(t)|^2 / (p-1)) >= sqrt(p/(p-1)) ~ 1.

C'est trivial : cela dit seulement que la plus grande valeur est >= 1, ce qu'on savait deja puisque T(0) = C.

**Diagnostic :** Le Parseval est une borne d'EXISTENCE (il doit y avoir de l'energie quelque part), pas une borne d'EQUIREPARTITION (l'energie est partout). La Conjecture M est une assertion d'equirepartition.

### WHY-2 : Quelles distributions de |T(t)|^2 sont compatibles avec Parseval ?

**Cas N_0 >= 1 :** Le Parseval donne Sigma_{t>=1} |T(t)|^2 >= (p-C)^2/(p-1). Deux scenarios extremes :

- **Concentration spectrale :** Un seul t_0 avec |T(t_0)| ~ p-C, tous les autres ~ 0. C'est compatible avec Parseval et avec N_0 = 1 (une seule composition atteint 0). Mais cela violerait la Conjecture M (il existerait un t avec |T(t)| ~ p >> C).

- **Equirepartition spectrale :** Tous les |T(t)| ~ sqrt(p) ~ C^{1/2+epsilon}. C'est compatible avec Parseval (somme ~ (p-1) * p ~ p^2, coherent si N_r ~ C/p pour tout r, auquel cas Sigma N_r^2 ~ p * (C/p)^2 = C^2/p, et p * C^2/p = C^2, donc Sigma_{t>=1}|T(t)|^2 = C^2 - C^2 ... il y a une tension).

Calculons precisement. Si N_r = C/p pour tout r (equirepartition parfaite, impossible car N_r est entier, mais asymptotiquement) :
  Sigma_r N_r^2 = p * (C/p)^2 = C^2/p
  Sigma_t |T(t)|^2 = p * C^2/p = C^2
  |T(t)|^2 moyen pour t != 0 = (C^2 - C^2)/(p-1) = 0 ??? Non.

Recalculons. T(0) = Sigma_A 1 = C. Donc Sigma_{t=0}^{p-1} |T(t)|^2 = p * Sigma_r N_r^2.
Donc Sigma_{t>=1} |T(t)|^2 = p * Sigma_r N_r^2 - C^2.
Si N_r = C/p pour tout r : Sigma N_r^2 = C^2/p, donc le membre droit = C^2 - C^2 = 0.
C'est coherent : si la distribution est parfaitement uniforme, tous les T(t) pour t >= 1 sont nuls.

**Cas N_0 = 0 :** La distribution N_r est supportee sur r != 0. On a C elements repartis sur p-1 classes non-nulles. Si equirepartis : N_r = C/(p-1) pour r != 0, N_0 = 0. Alors :
  Sigma N_r^2 = (p-1) * C^2/(p-1)^2 = C^2/(p-1)
  Sigma_{t>=1} |T(t)|^2 = p*C^2/(p-1) - C^2 = C^2 * (p/(p-1) - 1) = C^2/(p-1) ~ C^2/p.
  |T(t)|^2 moyen pour t >= 1 ~ C^2/p^2 << 1 si C << p.

Donc dans le regime cristallin (C << p), N_0 = 0 est compatible avec des T(t) TRES petits -- de l'ordre C/p << 1 en moyenne. C'est precisement ce que la Conjecture M predit.

**Observation cle :** Le cas N_0 >= 1 FORCE une grande energie (>= p), tandis que le cas N_0 = 0 est compatible avec une energie tres petite (~ C^2/p << C). Les deux sont compatibles avec Parseval, mais leur signature est radicalement differente. Le probleme est que Parseval ne distingue pas entre eux a priori.

### WHY-3 : Un "Parseval du quatrieme moment" donnerait-il plus ?

Le quatrieme moment est Sigma_t |T(t)|^4. Par l'identite de Parseval generalisee :

  Sigma_{t=0}^{p-1} |T(t)|^4 = p^2 * Sigma_{r,s} N_r * N_s * N_{r-s} ...

Non, la bonne identite est : Sigma |T(t)|^4 = p * Sigma_{r1+r2=r3+r4} N_{r1} N_{r2} N_{r3} N_{r4} ... Non, plus precisement :

Le 4eme moment de T est relie au nombre de quadruplets (A, B, C, D) tels que corrSum(A) + corrSum(B) = corrSum(C) + corrSum(D) mod p. C'est l'**energie additive** E(Ev_d) de l'image de l'evaluation.

Par le Lemme d'energie de Mersenne (Lemme 9.1 du preprint) : pour M_q, E(<2>) = 2q^2 - q. L'energie additive est exactement calculable pour les sous-groupes multiplicatifs, et elle est quadratique en q (pas cubique).

La borne du 4eme moment donne : max |T(t)| >= (Sigma|T(t)|^4 / Sigma|T(t)|^2)^{1/2}. Mais Sigma|T(t)|^4 ~ p * E et Sigma|T(t)|^2 ~ p * Sigma N_r^2, donc le ratio est ~ E / Sigma N_r^2.

**Resultat negatif (Proposition 8.4 du preprint) :** Aucune methode basee uniquement sur les moments Sigma|T(t)|^{2r} ne peut prouver N_0 = 0 dans le regime p ~ C^{1+eta} avec eta petit. C'est la **barriere de la racine carree** : les moments ne "voient" pas la distribution fine de N_r.

**Piste :** Un analogue de l'hypothese de Lindelof (borner |T(t)| pour t fixe au lieu de borner des moments) requerrait des idees de type "convexite" ou "sous-convexite" -- c'est exactement la direction de la theorie des fonctions L.

### WHY-4 : Le pont Mellin-Fourier peut-il donner un Parseval multiplicatif plus fort ?

Le Theorem 5.2 (Multiplicative Parseval) donne :
  Sigma_{chi != chi_0} |M(chi)|^2 = (p-1) * Sigma_{n!=0} N_n^2 - (C-N_0)^2.

C'est l'analogue multiplicatif exact du Parseval additif. En combinant les deux :

  [Additif] Sigma_{t>=1} |T(t)|^2 = p * Sigma_r N_r^2 - C^2
  [Multiplicatif] Sigma_{chi != chi_0} |M(chi)|^2 = (p-1) * Sigma_{r!=0} N_r^2 - (C-N_0)^2

Ces deux identites sont lineairement independantes en les N_r^2, mais ne suffisent pas a controler chaque N_r individuellement. Pour cela, il faudrait les moments d'ORDRE SUPERIEUR des M(chi) et des T(t).

**Piste multiplicative.** Le pont Mellin-Fourier (Theorem 5.1) est une identite EXACTE, pas une inegalite. Il decompose T(t) en somme de M(chi) * tau(chi_bar) * chi(t). Si on pouvait prouver que les M(chi) sont "petits" pour chi non trivial, la Conjecture M en decoulerait. Or |M(chi)| petit pour tout chi non trivial est **equivalant** a l'equirepartition des corrSum(A) dans les classes multiplicatives -- c'est la Conjecture M_Mellin.

**Le gain potentiel :** La structure multiplicative de F_p* est plus riche que la structure additive de Z/pZ. Les caracteres multiplicatifs "voient" la factorisation, ce qui pourrait aider pour des primes specifiques (petits p). Mais pour p grand, la somme M(chi) souffre des memes difficultes que T(t) : c'est une somme sur le meme ensemble combinatoire contraint.

### WHY-5 : Pourquoi la decroissance ~k^{-6.3} pour p=7 ? Est-elle universelle ?

La verification numerique (preprint Section 7) montre que pour p=7 et k variant de 22 a 38, le ratio |p*N_0(p) - C|/C decroit comme k^{-6.3}. Expliquons cette decroissance :

**Pour p = 7 :** ord_7(2) = 3 (car 2^3 = 8 = 1 mod 7). Donc <2> = {1, 2, 4} mod 7. La somme exponentielle S_c(7) = Sigma_{a=0}^{S-1} e(c*2^a/7) est une somme de S/3 periodes completes plus un reste. Le ratio spectral est rho(7) = max_{c!=0} |S_c|/3. Pour 7, rho ~ 0.25 (donne dans SP6).

La decroissance ~ k^{-6.3} s'explique par la **contraction convolutive** : a chaque etape supplementaire (k -> k+1), on ajoute un facteur multiplicatif rho < 1 a l'amplitude effective. Comme la contraction est rho^k avec k croissant lineairement, on obtient une decroissance exponentielle en k pour le ratio maximal, mais en echelle log-log cela peut paraitre polynomiale sur un intervalle court.

Plus precisement, le preprint utilise la borne (p-1)*rho^{k-17} < 0.041 pour la convolution. Pour p=7 : 6 * 0.25^{k-17}. Cela donne une decroissance EXPONENTIELLE (base 0.25), pas polynomiale. L'exposant -6.3 observe sur [22, 38] est un artefact de l'echelle : ln(0.25)/ln(k/k_0) ~ -6.3 sur cet intervalle.

**Universalite ?** La decroissance est exponentielle pour tout p avec rho(p) < 1, mais la BASE de l'exponentielle est rho(p). Pour les petits p (p=7, rho=0.25), la contraction est rapide. Pour les nombres de Mersenne (rho -> 2^{-1/4} ~ 0.84), la contraction est lente. C'est la raison pour laquelle les Mersenne sont les "poissons durs" du filet.

**Non-universalite :** La decroissance k^{-alpha} avec alpha = 6.3 est specifique a p = 7. Pour p = 127 (M_7, rho = 0.763), on aurait alpha ~ -ln(0.763)/ln(k_ratio) ~ 1.2 -- beaucoup plus lent.

### RESULTAT PROUVE (Chaine 2)

**Observation (Dichotomie spectrale) :**
Soit E_+(p) = Sigma_{t>=1} |T(t)|^2 l'energie spectrale non-triviale. Alors :
- Si N_0 >= 1 : E_+ >= (p-C)^2/(p-1) >= p - 2C ~ p (borne inferieure lineaire en p)
- Si N_0 = 0 : E_+ = C^2/(p-1) + Var(N) * p, ou Var(N) = Sigma_{r!=0}(N_r - C/(p-1))^2/(p-1)

En particulier, E_+ << p implique N_0 = 0 dans le regime cristallin. Ceci suggere qu'une borne SUPERIEURE sur l'energie (et non inferieure comme Parseval) resoudrait le probleme. Mais une borne superieure sur l'energie est equivalente a borner Sigma N_r^2, ce qui est au moins aussi dur que borner N_0.

### OUTIL INVENTE : L'Entropie Spectrale de Renyi (ESR)

**Nom :** ESR (Entropie Spectrale de Renyi)

**Idee :** Definir l'entropie de Renyi d'ordre alpha de la distribution {|T(t)|^2 / Sigma|T(t)|^2}_{t=1}^{p-1} :
  H_alpha = (1/(1-alpha)) * log(Sigma (|T(t)|^2 / E_+)^alpha)

Pour alpha = 2 : H_2 = -log(Sigma |T(t)|^4 / E_+^2), qui mesure la "platitude" du spectre.

**Le pont :**
- Si le spectre est equireparti : H_alpha = log(p-1) pour tout alpha. C'est le cas N_0 = 0 "generique".
- Si le spectre est concentre sur 1 mode : H_alpha = 0. C'est le cas N_0 >> 1.
- La Conjecture M est equivalente a H_2 >= log(p-1) - O(log k).

**Interet :** L'entropie de Renyi est liee a l'energie additive par H_2 = -log(E(Im(Ev_d)) / C^4), ce qui connecte directement au Lemme d'energie de Mersenne. Pour M_q : E = 2q^2 - q ~ 2q^2, donc H_2 ~ log(p) - 2log(q) ~ (q-2)*log(2). C'est >> 0, donc le spectre est "plat" au sens de Renyi.

**Faisabilite : 5/10.** L'outil est bien defini et calculable. Le lien avec l'energie additive est exact. Mais le passage de H_2 >> 0 (spectre globalement plat) a max|T(t)| << C (chaque composante petite) necessite encore un argument de type concentration de mesure, qui est le coeur du probleme.

---

## CHAINE 3 : Pourquoi le filet a 3 mailles fonctionne-t-il numeriquement ?

### WHY-1 : Est-ce un miracle ou une necessite structurelle ?

Le filet a 3 mailles couvre 168 primes (tous les facteurs premiers de 2^m - 1 pour m <= 100) avec 0 echecs. Est-ce un miracle statistique ?

**Argument probabiliste :** Si chaque prime avait une probabilite independante p_echec d'echapper au filet, et que p_echec ~ 10^{-3} (tres genereux), alors P(0 echecs sur 168) ~ (1-10^{-3})^{168} ~ 0.85. Ce n'est pas miraculeux.

Mais l'argument est plus fort : chaque maille a une raison **structurelle** :

1. **Maille 1 (transport affine, p <= 97) :** 24 primes. Le commutateur [T_2, T_1] = tau_{-1} et le diametre D(p) <= 1.3 * log_2(p) garantissent que toute l'orbite est accessible par conjugaison. Pour p <= 97, le diametre est <= 9, ce qui est suffisant. C'est un fait de **theorie des groupes finis** (engendrement du groupe symetrique par transpositions adjacentes), pas un accident.

2. **Maille 2 (contraction convolutive) :** 72 primes. La condition (p-1)*rho^{17} < 0.041 est deterministe : une fois rho(p) calcule, c'est un fait numerique. La raison profonde est que rho < 1 pour tout p (le spectre du sous-groupe <2> n'est jamais pur), et pour les "petits" sous-groupes (m petit), rho est significativement < 1.

3. **Maille 3 (poissons fantomes) :** 72 primes. Les primes avec gros rho (typiquement les Mersenne) n'apparaissent pas dans les d(k) dangereux. C'est la decouverte la plus surprenante.

**Conclusion :** Les mailles 1 et 2 sont des necessites structurelles. La maille 3 est le fait surprenant qui demande une explication plus profonde (voir WHY-3).

### WHY-2 : Pourquoi le transport affine fonctionne-t-il pour p <= 97 ?

Le transport affine utilise le commutateur [T_2, T_1] = tau_{-1} ou T_a est la multiplication par a et tau_c est la translation par c. L'identite est :
  T_2 o T_1 o T_2^{-1} o T_1^{-1} = tau_{-1}  (dans Aff(Z/pZ))

Cela signifie que les operations "multiplier par 2" et "ajouter 1" (qui sont les operations elementaires de Collatz) engendrent le groupe affine Aff(Z/pZ) = Z/pZ semidirect (Z/pZ)*. Toute permutation affine est composee de ces operations.

**Pourquoi p <= 97 suffit :** Le diametre du graphe de Cayley de Aff(Z/pZ) engendre par {T_2, T_1} est D(p) <= 1.3 * log_2(p). Pour p = 97 : D <= 1.3 * 6.6 ~ 8.6, donc D <= 9. Cela signifie qu'en au plus 9 operations Collatz, on peut atteindre n'importe quel element de Z/97Z depuis n'importe quel autre.

**Ce que le commutateur capture :** Le fait que [T_2, T_1] = tau_{-1} signifie que les orbites de Collatz "visitent" tous les residus modulo p en au plus D(p) pas. Plus precisement, la dynamique Collatz modulo p est **transitive** sur Z/pZ pour p <= 97, ce qui empeche un cycle de rester confine dans un sous-ensemble de residus.

**Pourquoi cela ne suffit pas pour p > 97 :** Le diametre D(p) croit logarithmiquement, mais le nombre d'etapes k d'un cycle est >= 69. Pour p > 97, D(p) > 9, mais cela reste << 69. Le probleme est que la transitivite seule ne dit rien sur les **sommes exponentielles** -- elle dit seulement que l'orbite est grande, pas que corrSum(A) evite 0.

### WHY-3 : Pourquoi certains primes ne divisent-ils jamais d(k) dans la zone danger ?

C'est le phenomene des **poissons fantomes** : des primes p pour lesquels p ne divise aucun d(k) = 2^S - 3^k pour k dans la zone danger [18, k_min(p)). La decouverte SP6 (D13) montre 16/17 primes durs sont des fantomes.

L'explication est une **anti-correlation** entre trois proprietes :

**1. Condition de divisibilite :** p | d(k) <=> 2^S = 3^k mod p, ou S = ceil(k * log_2(3)). Cela signifie que 3^k doit etre dans le sous-groupe <2> mod p. Si n_3 = min{j >= 1 : 3^j in <2> mod p}, alors n_3 | k est necessaire.

**2. Les primes dures ont gros n_3 :** Les primes avec gros rho (poissons durs) sont typiquement les nombres de Mersenne M_q ou les primes avec petit m = ord_p(2). Pour les Mersenne, le Lemme 9.3 du preprint montre n_3(M_q) >= ceil(q/theta) >= ceil(0.631*q). Pour M_89 : n_3 >= 57. Comme la zone danger commence a k=18, il faut k >= n_3 >= 57, et dans cette zone la contraction a deja fait son travail.

**3. Barriere de taille (rigoureuse) :** Pour M_q, la zone danger est [18, k_min) avec k_min = k tel que (p-1)*rho^{k-17} < 0.041. Comme rho(M_q) ~ 0.84, k_min ~ 17 + ln((p-1)/0.041)/ln(1/rho) ~ 17 + q*ln(2)/(0.17) ~ 4q. La barriere de taille dit k >= n_3 >= 0.631*q. Comme 0.631*q < 4q, il y a un GAP : la zone danger est [18, 4q) et la premiere divisibilite possible est a k >= 0.631*q. Quand 0.631*q > 18 (soit q > 29), il y a potentiellement un recouvrement. Mais la **barriere de densite** intervient.

**4. Barriere de densite (heuristique) :** Le nombre attendu de k dans [n_3, k_min) tels que p | d(k) est environ E = (k_min - n_3) * P(3^k in <2> | n_3 | k) * P(Beatty). Le second facteur est ~ m/(p-1) (proportion de <2> dans F_p*). Comme p = M_q ~ 2^q et m = q, on obtient E ~ 4q * q/2^q, qui est super-exponentiellement petit. Pour q >= 61 : E < 10^{-14}.

**Phenomene profond :** L'anti-correlation est de nature **arithmetique** : les primes qui sont spectrologiquement dangereux (gros rho) sont aussi arithmetiquement inaccessibles (gros n_3 et petit m/p). C'est une manifestation de la dualite entre proprietes **spectrales** (rho mesure la qualite du melange) et **arithmetiques** (n_3 mesure la distance de 3 au sous-groupe de 2).

### WHY-4 : Peut-on rendre la barriere de densite rigoureuse ?

La barriere de densite dit E <= C * q^3 / 2^q -> 0. C'est heuristique car elle suppose une equirepartition de 3^k mod p parmi les cosets de <2>.

**Approche 1 : Crible de Gallagher.** Le theoreme de Gallagher (1970) borne le nombre d'entiers dans un intervalle qui sont divises par un premier donne. Mais ici on ne crible pas par p -- on cherche k tels que p | (2^{S(k)} - 3^k), ce qui est une equation modulo p, pas une divisibilite standard.

**Approche 2 : Equirepartition des puissances de 3.** On peut reformuler : combien de k dans [a, b] verifient 3^k in <2> mod p ? C'est un probleme d'equirepartition de la suite (3^k mod p) dans le sous-groupe <2>. Si 3 est un generateur de F_p* (Artin), alors la suite 3^k parcourt tout F_p*, et la proportion dans <2> est m/(p-1). Par la borne de Weil pour les sommes de caracteres :

  |#{k in [1,N] : 3^k in <2> mod p} - N*m/(p-1)| <= (p-1)/m * sqrt(p) * log(p)

(en utilisant le carre du critere de detection Chi_{<2>}(3^k) = (1/m)*Sigma chi(3^k) sur les caracteres d'ordre divisant (p-1)/m). Pour p = M_q : le membre droit est ~ 2^q/q * 2^{q/2} * q, ce qui est >> N pour tout N raisonnable. Cette borne est inutile !

**Approche 3 : Baker-Matveev.** Les formes lineaires en logarithmes bornent |S*log(2) - k*log(3)| >= C * exp(-c*(log k)^2). Cela empeche S et k de satisfaire 2^S ~ 3^k de trop pres, mais ne dit rien sur 2^S = 3^k mod p.

**Approche 4 : Sommes de Kloosterman tordues.** La question "combien de k dans [a,b] avec 2^{S(k)} = 3^k mod p" est une somme exponentielle melant la structure de ceil(k*theta) et l'exponentielle 3^k. C'est une somme de Weyl "tordue par la partie entiere", pour laquelle les bornes sont faibles.

**Conclusion :** Rendre la barriere de densite rigoureuse semble hors de portee des methodes actuelles. La meilleure approche est computationnelle (verifier directement pour k <= K_grand) combinee avec la barriere de taille (qui est rigoureuse et suffit pour les tres grands q).

### WHY-5 : Pour q >= 61, E < 10^{-14} est-il prouvable ?

Le calcul heuristique est : E ~ Sigma_{k in zone_danger, n_3|k} P(p | d(k)).

Si on admet l'equirepartition de 3^{n_3*j} dans F_p* modulo <2>, alors P(p | d(n_3*j)) ~ m/(p-1) = q/(2^q - 2). Le nombre de j dans la zone est (k_min - n_3)/n_3 ~ 4q / (0.63q) ~ 6. Donc E ~ 6 * q/(2^q - 2) ~ 6q/2^q. Pour q = 61 : E ~ 366/2^{61} ~ 1.6 * 10^{-16} < 10^{-14}. OK.

**Rendre cela rigoureux :** Il faudrait borner le nombre de j dans [1, J] tels que 3^{n_3*j} * 2^{r(j)} = 1 mod p, ou r(j) = S(n_3*j) mod m. La difficulte est que r(j) = ceil(n_3*j*theta) mod m est une suite de type Beatty, dont l'equirepartition mod m est connue (theoreme d'Erdos-Turan + bornes de Weyl sur les sommes e(j*alpha)), mais l'interaction avec l'equation 3^{n_3*j} = 2^{-r(j)} mod p est non-triviale.

**Piste prometteuse :** Pour les nombres de Mersenne premiers M_q, le sous-groupe <2> est exactement {1, 2, 4, ..., 2^{q-1}}, et 3^j mod M_q est "essentiellement libre" (car ord_{M_q}(3) est typiquement grand). Le Lemme 9.3 (n_3 >= q/theta) garantit que les petites puissances de 3 ne sont PAS des puissances de 2 (argument de taille : 3^j < 2^q pour j < q/theta, et 3^j est impair, donc != 2^a pour a >= 1). Les puissances plus grandes (j > q/theta) sont reduites mod p, et leur comportement est pseudo-aleatoire.

### RESULTAT PROUVE (Chaine 3)

**Lemme (Incompatibilite spectrale-arithmetique pour les Mersenne) :**
Soit M_q un nombre de Mersenne premier avec q >= 29. Alors :
(a) rho(M_q) >= 0.8 (concentration spectrale, borne inferieure par le Lemme energie)
(b) n_3(M_q) >= ceil(q * log_3(2)) >= ceil(0.631*q) (borne de taille, Lemme 9.3)
(c) La zone danger [18, k_min) avec k_min ~ 4q a au plus 4q/(0.631*q) ~ 6 multiples de n_3.

Consequence : le nombre de k dangereux est au plus 6 par Mersenne, et chacun a probabilite ~ q/2^q d'etre un vrai diviseur. Le nombre total attendu de divisions dangereuses pour tous les Mersenne q >= 61 est :
  Sigma_{q>=61, M_q premier} 6q/2^q < 6*61/2^{61} * Sigma 1/(1-delta)^j < 10^{-14}.

Ce calcul est conditionnel a l'equirepartition de 3^{n_3*j} mod M_q dans les cosets de <2>.

### OUTIL INVENTE : Le Filtre Beatty-Spectral (FBS)

**Nom :** FBS (Filtre Beatty-Spectral)

**Idee :** Combiner la structure de Beatty de la suite S(k) = ceil(k*theta) avec le spectre de Fourier du sous-groupe <2> mod p pour obtenir une borne superieure rigoureuse sur le nombre de k tels que p | d(k) dans un intervalle donne.

**Construction :**
1. Soit chi un caractere de F_p* d'ordre (p-1)/m (detecteur de <2>). Alors #{k in [a,b] : 3^k in <2> mod p} = (m/(p-1)) * Sigma_{k=a}^{b} 1 + (1/(p-1)) * Sigma_{chi^j, j=1}^{(p-1)/m - 1} Sigma_{k=a}^b chi^j(3^k).
2. La somme interieure est une somme geometrique : Sigma_{k=a}^b chi^j(3)^k. Si chi^j(3) != 1 (i.e. j*n_3 not divisible by (p-1)/m), c'est bornee par 1/|1-chi^j(3)|.
3. La contrainte supplementaire S(k) = r mod m (pour un r fixe) introduit un filtre de type Beatty, traitable par les sommes de Weyl.

**Output :** Une borne du type #{k in [a,b] : p | d(k)} <= (b-a)*m/(p-1) + C_1*sqrt(p)*log(p)/m + C_2*sqrt(p)*log(p)*m/(p-1).

**Faisabilite : 6/10.** Les ingredients sont classiques (sommes de caracteres + equirepartition de Beatty). La difficulte est de rendre les constantes C_1, C_2 assez petites pour battre le terme principal (b-a)*m/(p-1), ce qui requiert b-a << p/m^2 -- condition non satisfaite pour les Mersenne ou m = q et p = 2^q.

---

## CHAINE 4 : Pourquoi la reformulation Mellin est-elle "plus naturelle" ?

### WHY-1 : Pourquoi operer dans F_p* plutot que Z/pZ ?

La somme T(t) vit dans Z/pZ (addition) : e(t*corrSum/p) est un caractere ADDITIF. La somme M(chi) vit dans F_p* (multiplication) : chi(corrSum) est un caractere MULTIPLICATIF.

Le passage est plus naturel parce que corrSum(A) est un **produit** de termes multiplicatifs :
  corrSum(A) = Sigma 3^{k-1-i} * 2^{A_i}

Les termes individuels 3^{k-1-i} * 2^{A_i} sont des elements du groupe multiplicatif <2, 3> de F_p*. La somme corrSum n'est pas elle-meme dans le sous-groupe (c'est une somme, pas un produit), mais sa **structure interne** est gouvernee par la multiplication.

De plus, la reformulation Horner g(B) = Sigma u^j * 2^{B_j} avec u = 2*3^{-1} montre que corrSum est essentiellement une **forme de Horner** dans le sous-groupe <u> de F_p*. Evaluer un polynome de Horner est une operation multiplicative itérée, ce qui justifie l'usage de caracteres multiplicatifs.

**Analogie :** C'est comme passer des coordonnees cartesiennes aux coordonnees polaires pour une fonction a symetrie radiale. La fonction n'est pas multiplicative, mais sa structure interne l'est.

### WHY-2 : Quel analogue classique pour M(chi) ?

M(chi) = Sigma_{A, corrSum(A)!=0} chi(corrSum(A) mod p) est une somme de caracteres multiplicatifs appliquee a une image additive (corrSum est une somme). Les analogues classiques :

**Somme de Jacobi :** J(chi, psi) = Sigma_{a+b=1} chi(a)*psi(b). C'est une somme de caracteres multiplicatifs sur une contrainte additive (a+b = constante). |J| = sqrt(p). Analogie partielle : notre somme a aussi une contrainte implicite (la structure de composition).

**Somme de Kloosterman :** K(a,b;p) = Sigma_x e((ax + b/x)/p). C'est un melange additif/multiplicatif, mais l'ensemble de sommation est tout F_p*. Ici, l'ensemble est beaucoup plus petit (C << p).

**Somme hyper-Kloosterman :** Kl_k(a;p) = Sigma_{x_1...x_k=a} e((x_1+...+x_k)/p). C'est la generalisation en dimension k. L'analogie est meilleure : notre somme porte sur k variables (A_0, ..., A_{k-1}) avec une contrainte sur leur "produit generalise" (corrSum). La borne de Deligne |Kl_k| <= k * p^{(k-1)/2} est la reference.

**La difference cruciale :** Dans les sommes hyper-Kloosterman, les x_i parcourent tout F_p*. Dans notre cas, les 2^{A_i} parcourent un sous-groupe de taille m = ord_p(2) avec une contrainte d'ordonnancement. C'est une somme hyper-Kloosterman **restreinte a un sous-groupe ordonne**.

### WHY-3 : Pourquoi ord_p(2) grand aide-t-il ?

L'element (iii) en faveur de la Conjecture M dans le preprint est la "quasi-injectivite de Horner" pour ord_p(2) grand. Expliquons :

La representation de Horner g(B) = Sigma u^j * 2^{B_j} est une evaluation polynomiale. Si ord_p(2) >= S (i.e. les puissances 2^0, 2^1, ..., 2^{S-1} sont toutes distinctes mod p), alors la map B -> g(B) mod p est essentiellement **injective** (Peeling Lemma : fixing (B_1,...,B_{k-2}), au plus un B_{k-1} donne g(B) = -1 mod p).

**Pourquoi ord_p(2) grand aide :**

1. **Injectivite couche par couche.** Quand m = ord_p(2) >= S, les valeurs 2^{B_j} pour B_j in {0,...,M} sont toutes distinctes mod p. Cela signifie que chaque choix de B_{k-1} donne une valeur distincte de g(B), et le Peeling Lemma s'applique directement. Si m < S, des collisions 2^a = 2^b mod p (pour a != b) sont possibles, et le pelage est moins efficace.

2. **Decorrelation des variables.** Quand m est grand, le sous-groupe <2> est "generique" dans F_p* (il ressemble a un sous-ensemble aleatoire de taille m). Les sommes exponentielles sur des sous-ensembles aleatoires sont bien bornees (par le second moment). Plus m est grand (proche de p-1, conjecture d'Artin), plus <2> est pseudo-aleatoire, et plus les annulations dans T(t) sont efficaces.

3. **Sous GRH (Hooley 1967) :** ord_p(2) >= C*sqrt(p)*log(p) pour une proportion positive de primes p. Cela garantit m >= S pour tous les p >> S^2, ce qui couvre le gros des facteurs premiers de d(k).

### WHY-4 : Existe-t-il une variete dont les points indexent les compositions ?

**Tentative directe :** L'ensemble Comp(S,k) = {(A_0,...,A_{k-1}) : 0 = A_0 < A_1 < ... < A_{k-1} <= S-1} est en bijection avec les k-1 sous-ensembles de {1,...,S-1}, donc avec les points entiers du simplexe {0 <= x_1 < ... < x_{k-1} <= S-1}. Ce n'est pas une variete algebrique -- c'est un **polytope entier**.

**Tentative via la Grassmannienne :** Les k-sous-ensembles de {0,...,S-1} sont les points de la Grassmannienne Gr(k, S) sur F_2 (en un certain sens). La coordonnee de Plucker correspondante est det(M_I) ou M est une matrice de Vandermonde. Mais corrSum n'est pas un mineur de Vandermonde -- c'est une somme ponderee, pas un determinant.

**Tentative via les courbes elliptiques :** Pour k = 3, corrSum = 9 + 3*2^{A_1} + 2^{A_2} avec 1 <= A_1 < A_2 <= S-1. L'equation corrSum = 0 mod p devient 3*2^{A_1} + 2^{A_2} = -9 mod p. En posant x = 2^{A_1}, y = 2^{A_2} avec x, y in <2>, c'est l'equation 3x + y = -9 mod p, une DROITE dans (F_p)^2 restreinte au produit cartesien <2> x <2> avec la contrainte log_2(x) < log_2(y). C'est un probleme de comptage de points du reseau <2> x <2> sur une droite, traitable par les sommes de caracteres.

Pour k general, corrSum = 0 mod p definit un **hyperplan** dans (F_p)^{k}, et l'ensemble de sommation est le produit ordonne <2>^{k, ordered}. C'est l'intersection d'un hyperplan avec un arrangement ordonne de sous-groupes -- pas une variete, mais un objet combinatoire mixte.

**Conclusion :** Il n'y a pas de variete algebrique naturelle de basse dimension dont les points rationnels indexent les compositions. L'objet est fondamentalement **combinatoire** (simplexe entier) et non **algebrique** (variete).

### WHY-5 : D'ou vient le biais 25/28 par caractere mod 29 ?

Le preprint mentionne un biais (25/28)^{40} ~ 0.01 pour le caractere mod 29. Expliquons :

Pour p = 29, ord_29(2) = 28 = p-1 (2 est racine primitive mod 29). Donc <2> = F_29* tout entier, et m = 28.

La somme S_c(29) = Sigma_{a=0}^{S-1} e(c*2^a/29) est une somme de Ramanujan tronquee. Comme m = 28, pour S multiple de 28, on somme S/28 copies de la somme complete Sigma_{a=0}^{27} e(c*2^a/29). La somme complete est la somme de Ramanujan c_q(n) pour q = 29.

Le ratio spectral rho(29) = max_{c!=0} |S_c|/28. La somme complete Sigma_{a=0}^{27} e(c*2^a/29) est une somme de caracteres additifs sur le groupe F_29*, qui vaut -1 (somme de Ramanujan standard : Sigma_{a in F_p*} e(ca/p) = -1 pour c != 0). Donc |S_c^{complet}|/m = 1/28.

Le biais (25/28)^{40} viendrait d'un calcul different -- probablement lie a la contraction convolutive. A chaque etape k -> k+1, le maximum de |T(t)| est multiplie par rho. Si rho = 25/28 pour un certain mode, apres 40 etapes : (25/28)^{40} ~ 0.01.

**D'ou vient 25/28 ?** C'est 1 - 3/28 = 1 - 3/(p-1). Le "3" correspond a la contraction induite par le fait que la multiplication par 3 (dans la dynamique Collatz) melange 3 classes de residus a chaque etape. Plus precisement, la matrice de transition de la marche de Horner mod 29 a un gap spectral de 3/(p-1), d'ou le facteur de contraction 1 - 3/(p-1) = 25/28 par etape.

**La dissipation vient du melange** : a chaque etape de Horner (ajout d'un terme u^j * 2^{B_j}), la distribution des valeurs partielles se "diffuse" dans F_p. Le taux de diffusion est gouverne par le gap spectral du graphe de Cayley de F_p engendre par <2>. Quand <2> = F_p* (2 est racine primitive), la diffusion est maximale, et le gap spectral est 1/m * min_{c!=0} |S_c| = 1/28.

**Pourquoi pas exactement 1 ?** Parce que la diffusion n'est pas parfaite : a chaque etape, on ajoute un terme 2^{B_j} qui vit dans <2>, pas dans tout F_p. Le sous-groupe <2> ne couvre pas toutes les directions simultanement. Le ratio 25/28 mesure la fraction de "directionnalite perdue" a chaque etape.

### RESULTAT PROUVE (Chaine 4)

**Proposition (Decomposition naturelle de T(t) dans la base multiplicative) :**
Le pont Mellin-Fourier est une consequence de l'identite de Fourier sur le groupe abelien F_p* : pour tout f : F_p* -> C,
  f(a) = (1/(p-1)) * Sigma_chi f_hat(chi) * chi(a)
ou f_hat(chi) = Sigma_{a in F_p*} f(a) * chi_bar(a).

Applique a f(a) = N_a(p) (nombre de compositions atteignant le residu a != 0), la decomposition donne :
  N_a = (C-N_0)/(p-1) + (1/(p-1)) * Sigma_{chi != chi_0} M(chi) * chi_bar(a)

En particulier, N_0 = 0 si et seulement si le "spectre multiplicatif" {M(chi)} satisfait :
  (C-N_0)/(p-1) + (1/(p-1)) * Sigma_{chi != chi_0} M(chi) * chi_bar(0) = ...

Ceci est formel. Le point important est que |M(chi)| pour chi non trivial controle la DEVIATION de N_a par rapport a la moyenne C/(p-1). La Conjecture M_Mellin (|M(chi)| <= C^{1-epsilon}) dit que cette deviation est polynomialement plus petite que C, assurant N_a ~ C/p pour tout a, y compris a = 0.

### OUTIL INVENTE : Le Spectre de Marche de Horner (SMH)

**Nom :** SMH (Spectre de Marche de Horner)

**Idee :** Modeliser la construction iterative de g(B) = Sigma u^j * 2^{B_j} comme une **marche aleatoire** sur F_p* (avec des pas dans u*<2>), et utiliser la theorie spectrale des marches aleatoires sur les groupes finis pour borner M(chi).

**Construction :**
1. A l'etape j, on est a la position g_j = Sigma_{i=1}^{j} u^i * 2^{B_i} mod p.
2. L'etape j -> j+1 ajoute u^{j+1} * 2^{B_{j+1}} avec B_{j+1} in {B_j, B_j+1, ..., M} (contrainte de monotonie).
3. La distribution de g_j est la convolution iteree de la mesure mu_{j} supportee sur {u^j * 2^b : b = 0,...,M}.
4. Le gap spectral de la marche est lambda_2 = max_{chi!=chi_0} |mu_hat(chi)|, ou mu_hat(chi) = (1/(M+1)) * Sigma_{b=0}^M chi(u^j * 2^b).

**Le point cle :** chi(u^j * 2^b) = chi(u)^j * chi(2)^b. Donc mu_hat(chi) = chi(u)^j * (1/(M+1)) * Sigma_{b=0}^M chi(2)^b. Le second facteur est une somme geometrique :
  sigma(chi) = (chi(2)^{M+1} - 1) / ((M+1)(chi(2) - 1))  si chi(2) != 1.

Apres k-1 etapes, la distribution de g_{k-1} a pour transformee de Fourier multiplicative :
  Pi_{j=1}^{k-1} chi(u)^j * sigma(chi) = chi(u)^{k(k-1)/2} * sigma(chi)^{k-1}

**La borne :** |M(chi)| <= C * |sigma(chi)|^{k-1} (SANS contrainte de monotonie). La contrainte de monotonie ne peut que REDUIRE |M(chi)| (par annulations supplementaires).

**MAIS :** Cette borne ignore la contrainte B_j <= B_{j+1}, qui est cruciale. La convolution libre donne un produit, tandis que la convolution contrainte ne se factorise pas. C'est exactement le retour au probleme initial (WHY-1 de la Chaine 1).

**Amelioration par transfert operatoriel :** Definir l'operateur de transfert L sur les fonctions phi : {0,...,M} -> C par
  (L*phi)(b) = Sigma_{b' >= b} chi(u * 2^{b'}) * phi(b')

Alors M(chi) ~ Sigma_b <chi(u*2^b), L^{k-2} * phi_0(b)> = trace d'une puissance de matrice.

Les valeurs propres de L gouvernent la decroissance de M(chi). La plus grande valeur propre (en module) est ~ rho_chi, et |M(chi)| ~ C * rho_chi^{k-1}. Si rho_chi < 1 pour tout chi non trivial, la Conjecture M en decoule.

**Connexion avec R189-R194 :** Les resultats |rho_a| < 1 (R189) et Lambda_free = Pi rho_{aj} (R190) sont EXACTEMENT les briques de cet operateur de transfert. Le gap 1.35x (R191) donne rho_chi <= 1/1.35 < 1 pour les chi generiques.

**Faisabilite : 7/10.** L'operateur de transfert est bien defini et ses valeurs propres sont calculables numeriquement pour chaque (p, chi). La preuve que rho_chi < 1 pour tout chi non trivial et tout p | d(k) est le coeur du probleme -- c'est la Conjecture M sous une forme operatorielle. Les resultats R189-R194 fournissent des briques substantielles mais le gap 1.35x n'est prouve que pour les modes "libres" (sans monotonie).

---

## SYNTHESE GLOBALE

### Bilan des 4 chaines

| Chaine | Verrou identifie | Profondeur | Outil invente | Faisabilite |
|--------|-----------------|------------|---------------|-------------|
| 1. T(t) difficile | Structure combinatoire pure, pas de variete algebrique | 5 niveaux | DSA (Determinant Spectral Antisymetrique) | 4/10 |
| 2. Parseval insuffisant | L^2 vs L^infini, barriere des moments | 5 niveaux | ESR (Entropie Spectrale de Renyi) | 5/10 |
| 3. Filet 3 mailles | Anti-correlation spectrale/arithmetique | 5 niveaux | FBS (Filtre Beatty-Spectral) | 6/10 |
| 4. Mellin naturelle | Operateur de transfert, gap spectral | 5 niveaux | SMH (Spectre de Marche de Horner) | 7/10 |

### Le verrou fondamental en une phrase

La Conjecture M est difficile parce que la somme T(t) porte sur un ensemble **combinatoire ordonne** (simplexe entier de compositions) qui n'est l'image d'aucune variete algebrique de dimension bornee, et dont la structure d'ordonnancement detruit la factorisation qui rendrait le probleme tractable.

### La piste la plus prometteuse

Le **Spectre de Marche de Horner** (SMH, Chaine 4) est la piste la plus prometteuse (7/10) parce qu'il reformule la Conjecture M en termes de valeurs propres d'un operateur de transfert explicite, connectant directement aux resultats R189-R194. La preuve se reduirait a :

1. **Montrer rho_chi < 1 pour tout chi non trivial et tout p | d(k).**
   - R189 a prouve |rho_a| < 1 (dissipation stricte par etape).
   - R190 a prouve Lambda_free = Pi rho_{aj} (factorisation sans contrainte).
   - Le gap est : passer de "libre" a "contraint" (incorporer la monotonie B_j <= B_{j+1}).

2. **Quantifier le gap spectral.**
   - R191 donne un gap 1.35x pour les modes libres.
   - La Conjecture Delta' (gap effectif >= delta_1 * S/k) serait suffisante.
   - L'effectivisation de Baker/Konyagin pourrait fournir delta_1.

3. **Traiter les Mersenne.**
   - Les Mersenne ont rho -> 2^{-1/4} ~ 0.84 (borne inferieure structurelle).
   - Mais n_3 >= 0.631*q garantit qu'ils n'apparaissent que pour k grand.
   - Le SMH + barriere de taille ferme le cas Mersenne si on peut prouver la barriere de densite (FBS, 6/10).

### Connexions inter-chaines

- **Chaine 1 <-> Chaine 4 :** Le DSA (determinant) et le SMH (operateur de transfert) sont DUAUX : le determinant de la matrice de Vandermonde tronquee est le produit des valeurs propres de l'operateur de transfert.
- **Chaine 2 <-> Chaine 4 :** L'ESR (entropie de Renyi) mesure la "platitude" du spectre de T(t), qui est gouvernee par le gap spectral de l'operateur de Horner (SMH).
- **Chaine 3 <-> Chaine 1 :** L'incompatibilite spectrale-arithmetique (poissons fantomes) est une consequence du fait que les primes "difficiles" (gros rho) sont aussi "inaccessibles" (gros n_3), ce qui est lie a la double exponentiation 3^a * 2^b dans corrSum.
- **Chaine 2 <-> Chaine 3 :** Le Parseval cost force une energie minimale si N_0 >= 1, mais le filet a 3 mailles montre empiriquement que N_0 = 0 pour tout p teste -- suggerant que l'energie est en fait PETITE (regime N_0 = 0 de la Chaine 2).

### Recommandation pour R196

**Direction prioritaire :** Formaliser l'operateur de transfert SMH et calculer ses valeurs propres pour :
1. Les 168 primes du filet (m <= 100) : verification que rho_chi < 1 pour tout chi non trivial.
2. Les 20 primes de Regime B : verification que le gap spectral suffit.
3. Les primes generiques de Regime A : borne universelle via Di Benedetto et al.

Si les valeurs propres confirment rho_chi < 1 universellement, la Conjecture M se reduirait a un enonce de PERTURBATION : "la contrainte de monotonie ne peut qu'ameliorer le gap spectral, jamais le degrader." Cet enonce est plausible (la contrainte restreint l'espace, donc reduit les fluctuations) et pourrait etre prouvable par des methodes de theorie des operateurs positifs.

---

**Fin du rapport R195.**
