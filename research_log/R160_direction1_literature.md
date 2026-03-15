# R160bis - Direction 1 : Litterature et outils fondamentaux pour sum e(2^n/p)

**Date** : 2026-03-15
**Objet** : Investigation systematique de la litterature pour borner S_H(t) = sum_{n=0}^{r-1} e(t * 2^n / p), |H| = r = ord_p(2) ~ log p

---

## SYNTHESE EXECUTIVE

**Verdict global : Il n'existe PAS d'outil connu capable de borner non-trivialement S_H(t) quand |H| = O(log p).**

Tous les outils existants necessitent |H| > p^delta pour un delta > 0 (meme arbitrairement petit). Le cas |H| = O(log p) est STRICTEMENT hors de portee de toute technique connue. Ceci n'est pas un probleme technique a resoudre — c'est une BARRIERE FONDAMENTALE de la theorie actuelle.

---

## AXE A : Recherche dans la litterature

### A1. Le theoreme de Bourgain-Glibichuk-Konyagin (BGK)

**Reference fondamentale** : Bourgain, Glibichuk, Konyagin (2006), "Exponential sum estimates over subgroups in an arbitrary finite field", J. Analyse Math.

**Enonce (reformule)** : Pour tout delta > 0, il existe epsilon = epsilon(delta) > 0 tel que pour tout sous-groupe multiplicatif H de F_p* avec |H| > p^delta, et pour tout a != 0 :

    |sum_{h in H} e(ah/p)| < |H|^{1 - epsilon}

C'est-a-dire : il y a une economie (saving) polynomiale par rapport a la borne triviale |H|.

**Methode** : Phenomene somme-produit (sum-product). Si A est un ensemble avec |A + A| et |A * A| petits, alors A est "structure". Mais un sous-groupe H a |H * H| = |H|, donc |H + H| doit etre grand, ce qui donne de la cancellation dans les sommes de caracteres additifs.

**Limitation CRUCIALE** : Le theoreme BGK necessite |H| > p^delta pour un delta > 0 FIXE. La constante epsilon(delta) -> 0 quand delta -> 0. Plus precisement, la preuve passe par des iterations du lemme de Balog-Szemeredi-Gowers qui necessitent que l'ensemble grossisse multiplicativement, ce qui echoue si |H| est trop petit par rapport a p.

**Pour |H| = O(log p)** : Le theoreme BGK est INAPPLICABLE. On a |H| = log p = p^{log log p / log p} = p^{o(1)}, donc delta = o(1) -> 0 et aucune economie n'est garantie.

**Source** : Kowalski (2024), "Exponential sums over small subgroups, revisited", arXiv:2401.04756 — expose pedagogique de la preuve BGK.

### A2. Extension de Bourgain : seuil q^{C / log log q}

**Resultat important** : Pour une extension de corps fini F_q, BGK ont montre que si |H| > q^{C / log log q} pour une constante C > 0, alors |sum_{h in H} psi(h)| = o(|H|).

**Analyse** : Ce seuil q^{C/log log q} est BEAUCOUP plus grand que log q :
- log q = q^{log log q / log q} = q^{o(1)} (decroit plus vite que toute puissance)
- q^{C/log log q} = exp(C * log q / log log q) (decroit plus lentement)

Donc meme cette extension ne couvre PAS le cas |H| = O(log p). Il y a un GOUFFRE exponentiel entre log p et le meilleur seuil connu.

### A3. Resultats de Bourgain sur les sommes de Korobov

**Sommes de Korobov** : S = sum_{n=1}^{N} e(a * b^n / m), exactement notre type de somme.

**Borne classique de Korobov (1953)** : Non-triviale pour N >= sqrt(m).

**Amelioration de Bourgain** : Utilisant le phenomene somme-produit, borne non-triviale des que N >= exp(log m / log^2 log m).

**Pour N = log p** : On a log p << exp(log p / log^2 log p), donc la borne de Bourgain est INAPPLICABLE. En fait, exp(log p / log^2 log p) = p^{1/log log p}, qui est encore une puissance (decroissante mais positive) de p. L'ecart avec log p est monstrueux.

### A4. Borne de Burgess et variantes

**Burgess** : Necessite |H| > p^{1/4+epsilon}. Inapplicable.
**Weil** : Necessite que la somme soit sur un sous-groupe de taille ~ sqrt(p). Inapplicable.
**Resultats "medium size"** : Pour |H| >> p^{1/2} log^{1/3} p. Inapplicable.

### A5. Problemes ouverts de Shparlinski

La liste de problemes ouverts de Shparlinski (UNSW) mentionne explicitement les sommes de caracteres sur petits sous-groupes comme probleme difficile. Le cas logarithmique n'est mentionne dans aucun resultat positif.

### VERDICT AXE A

**NEGATIF DEFINITIF.** Aucun theoreme de la litterature ne donne de borne non-triviale pour |S_H(t)| quand |H| = O(log p). Le meilleur resultat connu (BGK) necessite |H| > p^delta et le meilleur seuil atteignable est environ p^{C/log log p}, exponentiellement plus grand que log p.

---

## AXE B : Construction ab initio — la recurrence (doubling map)

### B1. Formulation dynamique

Les phases theta_n = t * 2^n / p satisfont theta_{n+1} = 2 * theta_n mod 1. C'est la transformation x -> 2x mod 1 (doubling map, ou Bernoulli shift). La somme S_H(t) = sum_{n=0}^{r-1} e(2*pi*i * theta_n) est une somme de Birkhoff pour l'observable f(x) = e(2*pi*i*x).

### B2. Resultats ergodiques

**Theoreme de Birkhoff** : Pour presque tout x, (1/N) * sum f(T^n x) -> integrale de f. Mais "presque tout" exclut potentiellement les rationnels t/p.

**Vitesse de convergence (von Neumann)** : Le theoreme ergodique de von Neumann donne une convergence en norme L^2 avec vitesse liee au trou spectral (spectral gap) de l'operateur de transfert.

**Resultats sur le doubling map** :
- L'operateur de Perron-Frobenius L satisfait ||L^n u|| <= C * 2^{-gamma*n} ||u|| + C ||u||_{L^1} (inegalite de Doeblin-Fortet)
- La decroissance exponentielle des correlations est prouvee pour les observables Holder
- Gouezel (2004) a montre des lois stables pour les sommes de Birkhoff du doubling map

### B3. Pourquoi ca NE S'APPLIQUE PAS

**Probleme fondamental** : Tous les resultats ergodiques donnent des bornes MOYENNES (en x) ou pour PRESQUE TOUT x. Mais nous avons besoin d'une borne POINTWISE pour x = t/p specifique.

De plus :
1. **Periodicite** : L'orbite de t/p sous le doubling map est PERIODIQUE de periode r = ord_p(2). Les theoremes ergodiques traitent des orbites NON-periodiques (generiques).
2. **Temps court** : La somme est sur r ~ log p termes. Les resultats ergodiques donnent des informations asymptotiques quand N -> infini. Ici N est FIXE et petit.
3. **Point rationnel** : t/p est rationnel. Les resultats "pour presque tout" excluent typiquement les rationnels.

**Exception potentielle** : Les resultats sur les sommes de Birkhoff TRIMEES (Haynes et al., 2018, arXiv:1810.03223) pour le doubling map. Mais ces resultats traitent aussi du comportement moyen, pas pointwise.

### B4. Lien avec le trou spectral

L'operateur T : f(x) -> f(2x) sur les fonctions sur F_p est une ISOMETRIE (permutation). Son spectre est exactement l'ensemble des racines r-iemes de l'unite (car T^r = Id sur l'orbite H). Le "trou spectral" sur l'orbite est ZERO — tous les eigenvalues sont de module 1. Donc les arguments de mixing sont INAPPLICABLES sur l'orbite finie.

### VERDICT AXE B

**NEGATIF.** L'approche ergodique/dynamique echoue pour trois raisons independantes : (1) pointwise vs presque partout, (2) orbite periodique de courte periode, (3) pas de trou spectral sur l'orbite finie. Aucune de ces trois obstructions n'est contournable.

---

## AXE C : Construction ab initio — l'automate

### C1. Description

La sequence (2^n * t mod p)_{n>=0} est generee par un automate a p etats (l'etat est le reste modulo p, la transition est x -> 2x mod p). C'est une permutation cyclique de longueur r sur l'orbite de t.

### C2. Complexite lineaire et correlations

**Complexite lineaire** : La complexite lineaire L(s) d'une sequence s = (s_n) sur un corps fini est la longueur du plus court LFSR qui la genere. Pour la sequence u_n = 2^n * t mod p vue modulo 2, la complexite lineaire est liee a l'ordre de 2 modulo p.

**Resultats de Winterhof et al.** : Relation entre mesure de correlation d'ordre k et complexite lineaire. Pour les sequences de Legendre, la mesure de correlation est essentiellement celle d'une sequence aleatoire, a des facteurs logarithmiques pres.

### C3. Pourquoi ca NE S'APPLIQUE PAS

La complexite lineaire mesure la PREVISIBILITE algebrique de la sequence, pas l'amplitude de la somme exponentielle. Une sequence peut avoir une complexite lineaire maximale et pourtant avoir |S_H(t)| grand (par exemple si les phases sont toutes proches de 0).

Les bornes de type "test spectral" (Knuth, Niederreiter) s'appliquent aux sequences de congruence LINEAIRE (x_{n+1} = ax_n + b), pas aux sequences exponentielles (x_n = g^n mod p). La distinction est fondamentale.

**Lempel-Ziv-Cohn** : Leurs resultats sur les registres a decalage a retroaction lineaire (LFSR) ne s'appliquent pas car la sequence 2^n * t mod p n'est pas generee par un LFSR sur F_2 (c'est une sequence sur F_p, pas sur F_2).

### VERDICT AXE C

**NEGATIF.** L'approche automate/complexite ne fournit pas d'outils pour borner |S_H(t)|. Les bonnes mesures de pseudo-aleatoirete (complexite lineaire, correlation) ne se traduisent pas en bornes sur les sommes exponentielles pour les sequences de longueur logarithmique.

---

## AXE D : L'operateur de multiplication

### D1. Formulation operatorielle

L'espace L^2(F_p) a dimension p. L'operateur T : f(x) -> f(2x) est unitaire (permutation). Les caracteres additifs e_t(x) = e(tx/p) forment une base propre de la transformee de Fourier, mais PAS de T.

S_H(t) = sum_{n=0}^{r-1} (T^n e_t)(1) = sum_{h in H} e_t(h)

### D2. Decomposition spectrale de T

T est une permutation de {0, 1, ..., p-1}. Ses orbites sont les classes laterales de <2> dans (Z/pZ)*. Sur chaque orbite de longueur r, le spectre de T est {e(k/r) : k = 0, ..., r-1}.

La decomposition spectrale donne :
S_H(t)/r = (1/r) * sum_{h in H} e_t(h) = P_H(e_t)(1)

ou P_H est le projecteur sur les fonctions H-invariantes. C'est EXACTEMENT la tautologie mentionnee dans l'enonce.

### D3. Vitesse de convergence ergodique et sommes completes

Pour les sommes PARTIELLES (N < r), les resultats sur la vitesse de convergence des moyennes ergodiques (von Neumann, Krengel) donnent :

||(1/N) sum_{n=0}^{N-1} T^n f - P f||^2 <= (1/N^2) * ||f||^2 * sum_{k: lambda_k != 1} |sum_{n=0}^{N-1} lambda_k^n|^2

Pour N = r (somme complete sur la periode), sum_{n=0}^{r-1} lambda_k^n = 0 pour tout lambda_k != 1 (somme geometrique complete). Donc la convergence est EXACTE : la somme partielle est egale a la projection. Il n'y a pas de "vitesse de convergence" a borner — la somme est deja la reponse exacte.

### D4. Tentative : bornes en termes de la representation spectrale

On pourrait chercher a decomposer e_t dans la base des fonctions propres communes a T et ecrire S_H(t) en termes des coefficients de Fourier. Mais :

e_t(x) = e(tx/p) n'est PAS une fonction propre de T (sauf si t = 0).

T e_t(x) = e(t * 2x/p) = e_{2t}(x)

Donc T permute les caracteres additifs : T e_t = e_{2t}. L'orbite de e_t sous T est {e_{2^n t} : n = 0, ..., r-1} = {e_s : s in tH}.

La representation de T sur l'espace engendre par {e_s : s in tH} est la representation reguliere du groupe cyclique Z/rZ. Les fonctions propres sont les combinaisons :

f_k = sum_{n=0}^{r-1} e(-kn/r) * e_{2^n t}

Et S_H(t) = sum_{n=0}^{r-1} f_n(1) * ... Non. Plus precisement :

S_H(t) = sum_{n=0}^{r-1} e_{2^n t}(1) = sum_{n=0}^{r-1} e(2^n t / p) = ce qu'on veut borner.

La decomposition spectrale ne simplifie pas : elle revient a reecrire la somme dans une base differente, sans fournir de borne.

### VERDICT AXE D

**NEGATIF (tautologie).** L'approche operatorielle est mathematiquement correcte mais ne produit aucune information nouvelle. La somme S_H(t) = r * P_H(e_t)(1) est exacte, pas une approximation, et P_H(e_t)(1) est exactement ce qu'on veut borner. Il n'y a pas de "vitesse de convergence" pertinente car la convergence est parfaite en r etapes.

---

## AXE E : Borner la somme sur t GLOBALEMENT

### E1. Le besoin reel

Le programme Collatz-Junction a besoin de borner :

|sum_{t=1}^{d-1} prod_{j} sigma_j(t)| ou sigma_j(t) sont des sommes partielles de caracteres sur les cosets de <2>.

L'approche pointwise (borner chaque prod_j sigma_j(t) individuellement) echoue car max |S_H(t)| ~ sqrt(r * log(p/r)) >> sqrt(r).

### E2. Cancellation dans la somme sur t

**Idee** : Meme si chaque produit prod_j sigma_j(t) peut etre grand pour certains t, la SOMME sur t pourrait exhiber de la cancellation supplementaire.

**Analogie avec Fouvry-Kowalski-Michel** : Leur "etude des sommes de produits" (2015) donne des resultats de cancellation pour sum_t prod_j K_j(t) ou K_j sont des fonctions traces de faisceaux l-adiques. Leur critere de Goursat-Kolchin-Ribet assure la cancellation sous une condition d'independance des faisceaux sous-jacents.

**MAIS** : Nous avons prouve en R160 que S_H(t) n'est PAS la trace de Frobenius d'un faisceau l-adique. Donc la theorie de Fouvry-Kowalski-Michel (qui repose sur Deligne et la theorie des faisceaux) est INAPPLICABLE directement.

### E3. Cancellation "elementaire" dans sum_t prod sigma_j(t)

Sans la machinerie des faisceaux, peut-on exploiter la cancellation dans la somme sur t ?

**Observation** : sum_{t=1}^{p-1} |S_H(t)|^2 = r(p-1) (Plancherel). Ceci signifie qu'en MOYENNE sur t, |S_H(t)|^2 ~ r. Mais on a besoin de borner sum_t prod_j S_{H_j}(t), pas sum_t |S_H(t)|^2.

**Ouverture possible** : Si les H_j sont des cosets DIFFERENTS de <2>, les sommes S_{H_j}(t) pour different j pourraient avoir des correlations exploitables. Concretement :

sum_t S_{H_1}(t) * conj(S_{H_2}(t)) = sum_t sum_{h1 in H_1} sum_{h2 in H_2} e(t(h1-h2)/p)
= p * |H_1 inter H_2|

Si H_1 et H_2 sont des cosets DISJOINTS, cette somme est NULLE. C'est une orthogonalite exacte.

**Limitation** : Cette orthogonalite ne concerne que les moments d'ORDRE 2 (correlation paire). Pour les produits de k facteurs, on aurait besoin de borner les moments d'ordre superieur, ce qui ramene au probleme combinatoire initial.

### E4. Approche directe par CRT (Chinese Remainder Theorem)

L'approche CRT decomposerait d = prod p_i et utiliserait l'independance des residus modulo differents primes. Mais le probleme est que les sommes S_H(t) modulo p ne se factorisent PAS via le CRT quand on somme sur t modulo d (un entier composite).

### VERDICT AXE E

**PARTIELLEMENT OUVERT.** L'orthogonalite des cosets donne une cancellation au second moment, mais pas aux moments superieurs. L'approche Fouvry-Kowalski-Michel est bloquee par l'absence de structure de faisceau. Cependant, cette direction n'est pas completement fermee : il pourrait exister une combinaison astucieuse utilisant l'orthogonalite des cosets et des inegalites de moments. C'est le seul AXE ou une percee reste theoriquement possible.

---

## BILAN COMPARATIF

| Axe | Approche | Meilleur resultat | Seuil | Applicable si |H|=log p ? | Verdict |
|-----|----------|-------------------|-------|---------------------------|---------|
| A1 | BGK (sum-product) | |S| < |H|^{1-eps(delta)} | |H| > p^delta, delta > 0 | NON | MORT |
| A2 | BGK etendu | |S| = o(|H|) | |H| > q^{C/log log q} | NON (>> log q) | MORT |
| A3 | Korobov-Bourgain | Non-triviale | N > exp(log m / log^2 log m) | NON (>> log m) | MORT |
| A4 | Burgess | Classique | |H| > p^{1/4+eps} | NON | MORT |
| B | Ergodique/Birkhoff | Presque partout | N -> infini | NON (pointwise, periodique) | MORT |
| C | Automate/complexite | Correlation bounds | - | NON (pas le bon objet) | MORT |
| D | Operateur unitaire | Tautologie S_H = r*P_H e_t | - | Exact, pas de borne | TAUTOLOGIE |
| E | Somme globale sur t | Orthogonalite ordre 2 | - | PARTIELLEMENT | OUVERT |

---

## CONCLUSIONS ET IMPLICATIONS POUR LE PROGRAMME

### 1. Le mur est REEL et FONDAMENTAL

Le cas |H| = O(log p) est un desert theorique. Aucune technique connue ne produit une borne non-triviale. L'ecart entre log p et le meilleur seuil atteignable (environ p^{C/log log p}) n'est pas un "gap a combler" — c'est un GOUFFRE de nature exponentielle.

### 2. Pourquoi c'est si difficile

- Les techniques de "sum-product" necessitent que l'ensemble puisse "grossir" par additions repetees. Mais un ensemble de taille log p dans F_p est si petit qu'il n'a pas assez de "masse" pour que le grossissement soit significatif.
- Les techniques spectrales/cohomologiques (Weil, Deligne) necessitent une structure algebrique (variete, faisceau) que la somme S_H ne possede pas.
- Les techniques ergodiques necesitent un temps long (N -> infini) et notre somme n'a que ~ log p termes.

### 3. Ce que cela signifie pour le programme Collatz-Junction

**Option 1** : Abandonner les bornes pointwise sur S_H(t) et travailler uniquement avec des bornes en MOYENNE (deuxieme moment). C'est l'Axe E.

**Option 2** : Chercher des bornes CONDITIONNELLES (sous GRH, sous Artin, etc.). Sous la conjecture d'Artin generalisee, on pourrait peut-etre obtenir des informations sur la distribution de ord_p(2), ce qui contraindrait indirectement S_H.

**Option 3** : Changer de strategie mathematique. Au lieu de borner sum_t prod sigma_j(t), trouver un chemin alternatif vers N_0(d) = 0 qui evite completement les sommes exponentielles sur les petits sous-groupes.

### 4. Resultats conditionnels potentiels

- **Sous GRH** : Hooley (1967) a prouve la conjecture d'Artin conditionnellement a GRH. Si 2 est racine primitive mod p pour une proportion positive de p, alors r = p-1 et S_H(t) est une somme de Gauss classique (bornee par sqrt(p)). Mais pour les p ou r = ord_p(2) est petit, on n'a RIEN meme sous GRH.
- **Heath-Brown (1986)** : Au moins un de {2, 3, 5} est racine primitive pour une infinite de primes. Mais cela ne couvre pas TOUS les primes.

---

## REFERENCES

1. Bourgain, Glibichuk, Konyagin (2006). "Exponential sum estimates over subgroups in an arbitrary finite field". J. Analyse Math.
   https://www.math.ias.edu/files/avi/Bourgain_Glibichuk.pdf

2. Kowalski (2024). "Exponential sums over small subgroups, revisited". arXiv:2401.04756
   https://arxiv.org/abs/2401.04756

3. Bourgain (2005). "Exponential sum estimates over subgroups of Z*_q, q arbitrary". J. Analyse Math. 97, 317-355.

4. Bourgain, Konyagin (2003). "Estimates for the number of sums and products and for exponential sums in fields of prime order". C. R. Acad. Sci. Paris.

5. Konyagin (2004). "Exponential sums over multiplicative groups in fields". PIMS lectures.
   https://mathtube.org/sites/default/files/lecture-notes/Konyagin_Lectures.pdf

6. Shparlinski. "Open problems on exponential and character sums".
   https://web.maths.unsw.edu.au/~igorshparlinski/CharSumProjects.pdf

7. Fouvry, Kowalski, Michel (2015). "A study in sums of products". Phil. Trans. R. Soc. A.
   https://arxiv.org/abs/1405.2293

8. Shakan. "Exponential sums over small subgroups" (blog).
   https://blog.georgeshakan.com/exponential-sums-over-small-subgroups/

9. Gouezel (2004). "Stable laws for the doubling map".
   https://perso.univ-rennes1.fr/sebastien.gouezel/articles/DoublingStable.pdf

10. Tao (2007). "Milliman Lecture III: Sum-product estimates, expanders, and exponential sums".
    https://terrytao.wordpress.com/2007/12/06/milliman-lecture-iii-sum-product-estimates-expanders-and-exponential-sums/

11. Hooley (1967). "On Artin's conjecture". J. Reine Angew. Math.

12. Heath-Brown (1986). "Artin's conjecture for primitive roots". Q. J. Math.

13. Kerr, Shparlinski (2022). "Weil sums over small subgroups". arXiv:2211.07739

14. Macourt, Shkredov, Shparlinski (2017). "Multiplicative Energy of Shifted Subgroups and Bounds On Exponential Sums with Trinomials in Finite Fields". Canad. J. Math.

15. Cochrane, Pinner (2020). "New estimates for exponential sums over multiplicative subgroups and intervals in prime fields". J. Number Theory.
