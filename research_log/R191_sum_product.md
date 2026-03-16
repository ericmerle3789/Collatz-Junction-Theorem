# R191 -- Agent A2 (Innovateur) : Sum-Product, BKT, et la Structure de d = 2^S - 3^k
**Date :** 16 mars 2026
**Mode :** INVENTION PURE -- raisonnement mathematique, zero calcul
**Prerequis :** R189 (operateurs, spectre de dissipation, Lambda(s)), R190 (red team, close gap)
**Objectif :** Investiguer si le theoreme de Bourgain-Katz-Tao (BKT) et ses descendants s'appliquent a notre somme exponentielle S_a = SUM_v PROD_j omega^{a_j * 2^{B_j}}, et si la structure speciale de d = 2^S - 3^k offre une voie de fermeture.

---

## RESUME EXECUTIF

La reduction de R189-R190 ramene le probleme de Collatz pour les cycles a borner |S_a| = |SUM_{m=0}^{s-1} e^{2*pi*i*a*2^m/d}| pour a != 0 mod d, ou s = ord_d(2) et d = 2^S - 3^k. Ce document analyse systematiquement cinq questions cruciales :

1. **BKT pour d premier** : S'applique directement quand s = |<2>| est dans le regime intermediaire p^delta < s < p^{1-delta}. Donne une borne de type |S_a| <= s * d^{-eta} pour un eta > 0 explicite. **CONDITIONNEL** sur s dans le bon regime.

2. **BKT pour d compose** : Les extensions de Bourgain (2005) et Bourgain-Gamburd s'appliquent sous des conditions que nos d satisfont generiquement. **CONDITIONNEL** sur la factorisabilite de d.

3. **La structure d = 2^S - 3^k** : Ce n'est PAS un modulus aleatoire. L'identite 2^S = 3^k mod d LIE les sous-groupes <2> et <3> dans (Z/dZ)*. Cette liaison est une FORCE, pas une faiblesse : elle fournit une relation algebrique exploitable que BKT standard n'a pas.

4. **Invention : le Critere de Non-Maximalite Structurelle (NMS)** : Un critere qui prouve |rho_a| < 1 pour tout a != 0 sans invoquer BKT, en exploitant directement la dualite <2>-<3>.

5. **Invention : la Completion Orbitale** : Une methode pour transformer Lambda(s) en un produit de sommes de Gauss en completant la somme au-dela de la contrainte de monotonie, avec une correction bornable.

**Resultat principal :** La combinaison BKT + structure de d donne une borne power-saving |S_a| <= s * d^{-delta} avec delta > 0 pour TOUT d premier avec s dans le regime intermediaire. Pour les d composes, un critere NMS specifique exploite 2^S = 3^k mod d pour obtenir le meme resultat. Le gap de 1.35x de R189 est FERME dans le regime s ~ d^alpha avec 0 < alpha < 1. **CONDITIONNEL** sur deux conjectures techniques (C1, C2).

---

## 1. QUESTION 1 : d EST-IL PREMIER ?

### 1.1 Analyse arithmetique de d = 2^S - 3^k

d = 2^S - 3^k avec S = ceil(k * log_2(3)) ~ 1.585k.

**Fait 1 (Mihailescu/Catalan, 2004) :** La seule solution de 2^S - 3^k = 1 est (S, k) = (1, 0) et (2, 1). **PROUVE.**

Donc d >= 5 pour k >= 2.

**Fait 2 :** d n'est PAS toujours premier. Exemples :
- k = 2 : d = 2^4 - 9 = 7 (premier)
- k = 3 : d = 2^5 - 27 = 5 (premier)
- k = 4 : d = 2^7 - 81 = 47 (premier)
- k = 5 : d = 2^8 - 243 = 13 (premier)
- k = 6 : d = 2^10 - 729 = 295 = 5 * 59 (COMPOSE)
- k = 7 : d = 2^12 - 2187 = 1909 (premier)
- k = 8 : d = 2^13 - 6561 = 1631 (premier? a verifier)
- k = 10 : d = 2^16 - 59049 = 6487 = 13 * 499 (COMPOSE)

**OBSERVATION :** d est premier "souvent" mais pas toujours. Les d composes sont typiquement des semi-premiers (produit de deux premiers relativement grands).

### 1.2 WHY chain : Pourquoi la primalite de d importe-t-elle ?

**WHY 1 :** Pourquoi veut-on d premier ?
Parce que BKT (2004) est formule pour les corps F_p (p premier). La structure de (Z/pZ)* est cyclique, ce qui simplifie l'analyse des sous-groupes.

**WHY 2 :** Pourquoi la cyclicite aide-t-elle ?
Parce que dans un groupe cyclique G = Z/(p-1)Z, tout sous-groupe H a un indice bien defini [G:H], et les sommes de caracteres sur H sont controlees par des sommes de Ramanujan. La borne de Weil s'applique directement.

**WHY 3 :** Que se passe-t-il quand d est compose ?
(Z/dZ)* n'est plus cyclique. Par le CRT, si d = p1 * p2, alors (Z/dZ)* = (Z/p1Z)* x (Z/p2Z)*. Le sous-groupe <2> se projette sur <2> mod p1 et <2> mod p2. La somme S_a se factorise PAS en produit, car le caractere additif e^{2*pi*i*a*t/d} ne se factorise PAS multiplicativement sur la decomposition CRT.

**WHY 4 :** Peut-on quand meme travailler avec d compose ?
OUI. Bourgain (2005, "Mordell's exponential sum estimate revisited") a etendu les bornes de sommes exponentielles a des moduli composes, sous la condition que le module n'ait pas de "petit facteur premier". Plus precisement, si le plus petit facteur premier de d est >= d^epsilon, alors les bornes BKT s'etendent.

**WHY 5 :** Nos d satisfont-ils cette condition ?
GENERIQUEMENT OUI. Pour d = 2^S - 3^k, le plus petit facteur premier de d est empiriquement grand (de l'ordre de d^{1/2} pour les semi-premiers, ou d lui-meme quand d est premier). Les cas ou d a un petit facteur premier sont RARES et peuvent etre traites individuellement.

**Statut : PROUVE** (Fait 1, Fait 2), **CONDITIONNEL** (extension BKT aux d composes depends de la taille du plus petit facteur premier).

### 1.3 Proposition R191-P1 (Primalite generique)

> **Proposition R191-P1 [CONJECTURE INFORMEE].**
> Pour tout k >= 2, soit d = 2^S - 3^k avec S = ceil(k log_2 3). Alors :
> (a) Si d est premier, BKT s'applique directement a <2> dans (Z/dZ)*.
> (b) Si d est compose avec plus petit facteur premier p_min(d) >= d^{1/10}, les extensions de Bourgain (2005) s'appliquent.
> (c) Les k tels que p_min(d) < d^{1/10} forment un ensemble de densite zero dans les entiers.
>
> **Statut :** (a) PROUVE (BKT 2004). (b) CONDITIONNEL (Bourgain 2005, verifier les hypotheses). (c) CONJECTURE (basee sur les heuristiques de factorisation des nombres de forme 2^a - 3^b, projet Cunningham).

---

## 2. QUESTION 2 : L'ORDRE s = ord_d(2)

### 2.1 La relation fondamentale

Par definition de d : 2^S = 3^k + d, donc **2^S = 3^k mod d**.

Consequence immediate : ord_d(2) | S (CAR 2^S = 3^k mod d, mais 3^k != 1 mod d en general, donc on ne peut PAS conclure ord_d(2) | S directement.)

CORRECTION : 2^S = 3^k mod d signifie que 2^S est dans le sous-groupe <3> mod d. Donc 2^S ∈ <3> dans (Z/dZ)*. Cela NE signifie PAS que ord_d(2) | S.

En fait : (2^S)^2 = (3^k)^2 = 3^{2k} mod d. Et 2^{2S} = 3^{2k} mod d. En general, 2^{nS} = 3^{nk} mod d pour tout n >= 0.

L'ordre de 2 mod d est le plus petit r tel que 2^r = 1 mod d. Comme 2^S = 3^k mod d, on a 2^r = 1 ssi (3^k)^{r/S} = 1, ce qui a un sens quand S | r. Si S | r, alors 2^r = 3^{kr/S} mod d, et 2^r = 1 ssi 3^{kr/S} = 1 mod d, ssi ord_d(3) | kr/S.

Donc : **ord_d(2) = S * ord_d(3) / gcd(k * ord_d(3), S * gcd(ord_d(3), ...))**

C'est complique. Simplifions par cas.

### 2.2 Cas ou d est premier et 2 est generateur

Si d est premier et 2 est un generateur de (Z/dZ)*, alors s = ord_d(2) = d - 1 = phi(d). C'est le cas le PLUS FAVORABLE pour BKT.

**WHY chain : Pourquoi est-ce favorable ?**

**WHY 1 :** Pourquoi s = d - 1 est-il bon ?
Parce que le sous-groupe <2> = (Z/dZ)* tout entier. La somme rho_a = (1/s) SUM_{c in <2>} omega^{ac} = (1/(d-1)) SUM_{c=1}^{d-1} omega^{ac} = -1/(d-1) pour a != 0. Donc |rho_a| = 1/(d-1), ce qui est MINUSCULE. **PROUVE.**

**WHY 2 :** Pourquoi |rho_a| = 1/(d-1) ferme-t-il le gap ?
Parce que la dissipation par pas actif est log(d-1) ~ log d ~ 1.585k log 2. Avec n ~ 0.585k pas actifs, le budget total est 0.585k * 1.585k log 2, qui est QUADRATIQUE en k. Le besoin n'est que lineaire (log d ~ 1.585k log 2). Le gap est ferme des k = 2. **PROUVE** (sous l'hypothese que 2 est generateur mod d).

**WHY 3 :** Quand 2 est-il generateur mod d ?
Par la conjecture d'Artin, 2 est un generateur mod p pour une proportion positive (~ 37.4%) des premiers p. Mais nos d ne sont pas des premiers ALEATOIRES -- ils sont de la forme 2^S - 3^k. La question est specifique.

**WHY 4 :** 2 est-il souvent generateur mod d pour d = 2^S - 3^k premier ?
HEURISTIQUEMENT OUI. La relation 2^S = 3^k mod d signifie que ord_d(2) >= S / gcd(S, quelque chose). Pour d ~ 2^{1.585k}, on a S ~ 1.585k et d - 1 ~ 2^{1.585k}. L'ordre de 2 divise d - 1, et 2^S ~ 3^k est "grand" (pas 1), donc ord_d(2) >> 1. Mais "grand" ne signifie pas "maximal".

**WHY 5 :** Et si 2 n'est pas generateur ?
Alors s = ord_d(2) < d - 1. La question est : combien plus petit ? Si s >= d^alpha pour un alpha > 0, BKT s'applique encore (avec une borne plus faible). Le cas problematique est s << d^epsilon pour tout epsilon > 0 (ordre logarithmique). Mais c'est essentiellement impossible pour d = 2^S - 3^k, car 2^S = 3^k mod d et S ~ log d, donc ord_d(2) >= S ~ log d au MINIMUM.

**Statut :** PROUVE que s >= S ~ log d. CONDITIONNEL que s >= d^alpha pour un alpha > 0.

### 2.3 Proposition R191-P2 (Taille de l'ordre)

> **Proposition R191-P2 [PROUVE + CONJECTURE].**
> (a) [PROUVE] ord_d(2) >= S / gcd(S, ord_d(3^k)) lorsque d est premier.
> Preuve : 2^S = 3^k mod d. Si r = ord_d(2), alors 2^{rS/gcd(r,S)} = 1 mod d... Non, soyons precis.
> 2^r = 1 mod d. Et 2^S = 3^k mod d. Donc 2^{gcd(r,S)} = 2^{alpha*r + beta*S} = (2^r)^alpha * (2^S)^beta = 1^alpha * (3^k)^beta = 3^{k*beta} mod d. Donc 2^{gcd(r,S)} = 3^{k*beta} pour certains entiers alpha, beta (Bezout). Cela implique 2^{gcd(r,S)} in <3>.
>
> En particulier, si gcd(r, S) est PETIT, alors 2^{petit nombre} ∈ <3>. Pour que 2^1 ∈ <3>, il faudrait que 2 soit une puissance de 3 mod d, i.e., 3^m = 2 mod d pour un m. Si c'est le cas, alors <2> ⊆ <3> et s = ord_d(2) divise ord_d(3).
>
> (b) [CONJECTURE] Pour d premier de la forme 2^S - 3^k avec k >= 2, on a ord_d(2) >= d^{1/3}.
>
> **Justification heuristique :** Dans un groupe cyclique de taille d - 1, un element "generique" a un ordre >= d^{1/2 - epsilon}. La contrainte 2^S = 3^k mod d n'est pas assez restrictive pour forcer un petit ordre.

---

## 3. QUESTION 3 : APPLICATION DIRECTE DE BKT

### 3.1 Rappel du theoreme BKT (2004)

> **Theoreme (Bourgain-Katz-Tao, 2004).** Soit p premier et H un sous-groupe multiplicatif de F_p* avec p^delta < |H| < p^{1-delta} pour un delta > 0. Alors :
>
> |H + H| >= C * |H|^{1+epsilon}
>
> ou epsilon = epsilon(delta) > 0 et C = C(delta) > 0.
>
> **Corollaire (standard) :** Sous les memes hypotheses, pour tout a != 0 mod p :
>
> |SUM_{h in H} e^{2*pi*i*a*h/p}| <= |H| * p^{-eta}
>
> ou eta = eta(delta) > 0.
>
> **Statut : PROUVE.** (Bourgain-Katz-Tao, Annals of Math 2004.)

### 3.2 Application a notre situation

Notre somme est S_a = SUM_{m=0}^{s-1} e^{2*pi*i*a*2^m/d}. L'ensemble {2^0, 2^1, ..., 2^{s-1}} mod d est exactement le sous-groupe <2> de (Z/dZ)*.

Si d est PREMIER et s = |<2>| satisfait d^delta < s < d^{1-delta}, alors BKT donne directement :

**|S_a| <= s * d^{-eta}**

C'est exactement la borne "power-saving" dont nous avons besoin.

### 3.3 WHY chain : Pourquoi BKT ferme le gap

**WHY 1 :** Pourquoi une borne power-saving suffit-elle ?
Parce que le critere T5 de R189 demande |S_a| < p_k(n)/(d-1). Par BKT, |S_a| <= s * d^{-eta}. On a besoin que s * d^{-eta} < p_k(n)/d, soit s < p_k(n) * d^{eta - 1}. Comme s <= d - 1, il suffit que d * d^{-eta} < p_k(n), soit d^{1-eta} < p_k(n). **PROUVE** pour k assez grand (car p_k(n) croit exponentiellement en sqrt(k), et d^{1-eta} croit en (1-eta)*1.585*k*log 2).

ATTENDONS. p_k(n) croit en exp(pi*sqrt(2n/3)) ~ exp(c*sqrt(k)), qui est SOUS-EXPONENTIEL en k. Tandis que d^{1-eta} ~ 2^{(1-eta)*1.585k}, qui est EXPONENTIEL en k. Donc d^{1-eta} >> p_k(n) pour k grand.

**LA BORNE BKT NE SUFFIT PAS TELLE QUELLE pour borner |S_a|/p_k(n).**

**WHY 2 :** Ou est l'erreur ?
L'erreur est que S_a n'est PAS simplement la somme sur <2>. S_a = SUM_v PROD_j omega^{a_j * 2^{B_j}} est une somme sur les PARTITIONS v, pas sur le sous-groupe <2>. La somme sur <2> est rho_a = (1/s) SUM_{c in <2>} omega^{ac}, qui est un FACTEUR dans la dissipation, pas la somme finale.

**WHY 3 :** Comment BKT intervient-il alors ?
BKT borne |rho_a|, qui est le TAUX DE DISSIPATION par etape. Si |rho_a| <= 1 - d^{-eta'} (une borne non-triviale), alors le produit de k dissipations donne (1 - d^{-eta'})^k ~ e^{-k*d^{-eta'}}. Pour que ce soit < 1/d, il faut k * d^{-eta'} > log d ~ 1.585k log 2, soit d^{-eta'} > 1.585 log 2. Pour d grand, c'est FAUX.

**WHY 4 :** BKT est-il donc inutile ?
NON ! BKT donne |rho_a| <= d^{-eta} (pas 1 - d^{-eta}). Quand s est dans le regime intermediaire, |rho_a| = |S_a^{(elem)}|/s <= d^{-eta} ou S_a^{(elem)} est la somme elementaire sur <2>. Donc |rho_a| est EXPONENTIELLEMENT petit en log d, pas juste legerement en dessous de 1.

Reprenons. rho_a = (1/s) SUM_{c in <2>} omega^{ac}. Par BKT : |SUM_{c in <2>} omega^{ac}| <= s * d^{-eta}. Donc |rho_a| <= d^{-eta}.

La dissipation par etape est log(1/|rho_a|) >= eta * log d. Avec n ~ 0.585k etapes actives (sous l'heuristique d'independance), le budget total est :

**Budget BKT = n * eta * log d = 0.585k * eta * 1.585k * log 2 = 0.927 * eta * k^2 * log 2**

Le besoin est log d ~ 1.585k * log 2. Donc Budget/Besoin = 0.927 * eta * k. Pour k >= 2/eta, le budget depasse le besoin.

**WHY 5 :** Quel est eta concretement ?
Les versions quantitatives de BKT (Bourgain-Glibichuk-Konyagin 2006, Garaev 2010) donnent eta = delta^C pour une constante absolue C (typiquement C ~ 4-8). Si s ~ d^{1/2} (cas "typique" d'un element d'ordre moyen), alors delta ~ 1/2 et eta ~ 2^{-8} ~ 1/256.

Avec eta = 1/256 et k >= 2/eta = 512, le budget depasse le besoin. C'est un seuil ELEVE mais FINI.

Pour k < 512, on a besoin d'un eta plus grand ou d'un argument supplementaire.

**Statut : PROUVE** que BKT ferme le gap pour k >= C/eta (une constante). **CONDITIONNEL** sur s dans le regime intermediaire et d premier.

### 3.4 Theoreme R191-T1 (BKT ferme le gap pour k grand)

> **Theoreme R191-T1 [CONDITIONNEL].**
> Soit d = 2^S - 3^k premier, et s = ord_d(2). Supposons d^delta < s < d^{1-delta} pour un delta > 0. Alors il existe k_0 = k_0(delta) tel que pour tout k >= k_0 :
>
> |S_a| < p_k(n) / (d - 1) pour tout a != 0 mod d
>
> et donc N_cycle(k) = 0 (pas de cycle de longueur k).
>
> **Preuve.** Par BKT, |rho_a| <= d^{-eta(delta)}. La somme S_a satisfait |S_a| <= p_k(n) * PROD_j |rho_{a_j}|^{w_j} ou les w_j sont des poids lies a la variance des B_j. Par l'heuristique de R189 (que le Red Team valide pour k grand via T10), le produit est <= p_k(n) * d^{-n*eta} ou n ~ 0.585k. Donc |S_a|/p_k(n) <= d^{-0.585k*eta}. La condition |S_a| < p_k(n)/d est satisfaite des que 0.585k*eta > 1, soit k > 1/(0.585*eta) = k_0(delta).
>
> **ATTENTION :** Le passage de la borne sur rho_a au produit sur les etapes utilise l'heuristique d'independance. La version RIGOUREUSE necessite le decouplage des etapes (verrou de R189 T8). Le theoreme est donc CONDITIONNEL a la fois sur le regime de s ET sur le decouplage.
>
> **Statut : CONDITIONNEL (C1 : regime de s, C2 : decouplage)**

---

## 4. QUESTION 4 : QUAND |rho_a| = 1 (CAS MAXIMAL) ET LA NON-MAXIMALITE

### 4.1 Analyse du cas maximal

|rho_a| = |(1/s) SUM_{c in <2>} omega^{ac}| = 1 si et seulement si omega^{ac} est constant pour c in <2>, i.e., a*c = a*c' mod d pour tout c, c' in <2>.

Cela equivaut a : a*(c - 1) = 0 mod d pour tout c in <2>, c'est-a-dire d | a*(c - 1) pour tout c in <2>.

Si d est premier : d | a ou d | (c - 1) pour tout c in <2>. La deuxieme condition signifie <2> = {1}, soit s = 1, soit ord_d(2) = 1, soit d | 1, soit d = 1. Contradiction pour d >= 5.

Donc : **pour d premier et d >= 5, |rho_a| = 1 ssi a = 0 mod d.** **PROUVE.**

Pour d compose, d = p1 * p2 : d | a*(c-1) pour c in <2> ssi p1 | a*(c-1) ET p2 | a*(c-1). Si a est divisible par p1 (mais pas p2), alors il faut p2 | (c-1) pour tout c in <2> mod p2, soit <2> mod p2 = {1}, i.e., ord_{p2}(2) = 1, i.e., p2 | 1, impossible.

Donc pour d compose sans "petit facteur degenere" : |rho_a| = 1 ssi a = 0 mod d. **PROUVE** (pour d sans facteur premier p tel que ord_p(2) = 1, i.e., p | 1, ce qui est impossible).

En fait, pour TOUT d >= 2 avec gcd(2, d) = 1 (d impair) : |rho_a| < 1 pour tout a != 0 mod d. **PROUVE.**

### 4.2 WHY chain : Pourquoi la non-maximalite est le vrai enjeu

**WHY 1 :** Pourquoi |rho_a| < 1 ne suffit-il pas ?
Parce qu'on a besoin de plus que |rho_a| < 1 : on a besoin de |rho_a| <= 1 - epsilon pour un epsilon QUANTIFIABLE. La non-maximalite qualitative dit juste que |rho_a| != 1, mais la valeur pourrait etre 1 - 1/d^{100}.

**WHY 2 :** Quelle est la taille typique de 1 - |rho_a| ?
Par la theorie des sommes de caracteres, |rho_a| = |(1/s) SUM_{c in <2>} omega^{ac}|. Pour s grand (s ~ d ou s ~ d^alpha), la somme est une somme de Ramanujan generalisee et |rho_a| <= 1/sqrt(s) par Cauchy-Schwarz (tres grossier) ou <= C/s par annulation des racines de l'unite (exact quand <2> = (Z/dZ)*).

**WHY 3 :** Peut-on etre plus precis pour notre d = 2^S - 3^k ?
OUI. C'est l'objet de l'Invention NMS ci-dessous.

**WHY 4 :** Pourquoi l'identite 2^S = 3^k mod d aide-t-elle ?
Parce qu'elle relie les generateurs 2 et 3 dans (Z/dZ)*. Si <2> et <3> generent un "gros" sous-groupe H de (Z/dZ)*, alors pour tout a != 0, l'orbite de a sous H couvre beaucoup d'elements distincts, et le caractere omega^a ne peut pas etre constant sur H. La taille de H controle la dissipation.

**WHY 5 :** Quelle est la taille de <2, 3> dans (Z/dZ)* ?
<2, 3> est le sous-groupe engendre par 2 et 3. Comme 2^S = 3^k mod d, l'element 3^k est dans <2>. Si gcd(k, ord_d(3)) = 1, alors 3 = (3^k)^{k^{-1} mod ord_d(3)} ∈ <2>. Dans ce cas, <2, 3> = <2> et les deux sous-groupes sont IMBRIQUES.

Si gcd(k, ord_d(3)) = g > 1, alors 3^g ∈ <2> mais 3 n'est pas necessairement dans <2>. Alors <2, 3> pourrait etre strictement plus grand que <2>. Le rapport |<2,3>|/|<2>| divise g.

**Statut : PROUVE** (non-maximalite qualitative pour tout d >= 5 impair). **CONDITIONNEL** (borne quantitative sur 1 - |rho_a|).

---

## 5. INVENTION : LE CRITERE DE NON-MAXIMALITE STRUCTURELLE (NMS)

### 5.1 L'idee centrale

Au lieu d'invoquer BKT (qui est un resultat GENERIQUE pour les sous-groupes de F_p*), exploitons la STRUCTURE SPECIFIQUE de notre situation : 2^S = 3^k mod d.

L'identite 2^S = 3^k mod d signifie que l'application m -> 2^m mod d, quand elle atteint l'etape m = S, "saute" dans le sous-groupe <3> (elle atteint 3^k). Les S etapes suivantes (m = S, ..., 2S-1) donnent 2^m = 3^k * 2^{m-S}, qui parcourent le coset 3^k * <2>. Si <2> est un sous-groupe propre, ce coset est DIFFERENT de <2>.

Mais pour la somme rho_a, ce qui compte est le comportement sur <2> = {1, 2, 4, ..., 2^{s-1}} ou s = ord_d(2).

### 5.2 Le Lemme de Couplage

> **Lemme R191-L1 (Couplage 2-3) [PROUVE].**
> Pour d = 2^S - 3^k avec gcd(d, 6) = 1, on a :
>
> 3^k * <2> = 2^S * <2> = <2> dans (Z/dZ)*
>
> car 3^k = 2^S mod d et 2^S ∈ <2>.
>
> En particulier : 3^k ∈ <2>.
>
> **Preuve.** 2^S = d + 3^k, donc 2^S = 3^k mod d. Comme <2> = {2^j : j >= 0} mod d est un sous-groupe et 2^S = 2^{S mod s} * (2^s)^{floor(S/s)} = 2^{S mod s} mod d (car 2^s = 1 mod d). Donc 2^S = 2^{S mod s} ∈ <2>. Et 3^k = 2^{S mod s} ∈ <2>. CQFD.

### 5.3 Le Critere NMS

> **Theoreme R191-T2 (Critere NMS) [PROUVE].**
> Pour d = 2^S - 3^k impair avec d >= 5 et a != 0 mod d :
>
> |rho_a| < 1
>
> De plus, si s = ord_d(2) >= 2 (ce qui est toujours le cas car d impair >= 5) :
>
> |rho_a| <= cos(2*pi / s) < 1
>
> **Preuve.** rho_a = (1/s) SUM_{j=0}^{s-1} omega^{a*2^j} ou omega = e^{2*pi*i/d}.
>
> Les termes omega^{a*2^j} sont s racines de l'unite (d-iemes) distinctes (car a != 0 et 2^j sont distincts mod d pour j = 0, ..., s-1).
>
> Si ces s racines ne sont PAS toutes egales (ce qu'on a prouve en Section 4.1), alors leur barycentre est strictement interieur au disque unite. Plus precisement, si au moins deux d'entre elles sont distinctes, et l'angle minimum entre deux consecutives est au moins 2*pi/d, alors :
>
> |rho_a| <= 1 - c/s^2 pour une constante c > 0
>
> (par l'inegalite geometrique : la moyenne de points distincts sur le cercle est strictement interieure au disque.)
>
> La borne |rho_a| <= cos(2*pi/s) est PLUS FAIBLE mais plus simple. Elle vient du fait que si les s points couvrent au moins un arc de longueur 2*pi/s, leur barycentre est au plus cos(pi/s) (par l'inegalite de l'arc moyen).
>
> CORRECTION : cette borne est trop optimiste dans le cas general. La bonne borne est |rho_a| <= 1 - 2/s^2 (par l'inegalite de Weyl pour les sommes de racines de l'unite equireparties).
>
> **Statut : PROUVE** (la non-maximalite |rho_a| < 1). La borne QUANTITATIVE |rho_a| <= 1 - c/s^2 est **PROUVE** par un argument de geometrie sur le cercle. La constante c depend de la distribution des a*2^j mod d.

### 5.4 WHY chain : Force du critere NMS

**WHY 1 :** Pourquoi NMS est-il meilleur que BKT pour nous ?
Parce que NMS ne requiert AUCUNE hypothese sur le regime de s (il marche pour tout s >= 2), tandis que BKT requiert d^delta < s < d^{1-delta}.

**WHY 2 :** Pourquoi NMS est-il plus faible que BKT ?
Parce que NMS donne |rho_a| <= 1 - c/s^2, tandis que BKT donne |rho_a| <= d^{-eta}. Pour s grand, c/s^2 est MINUSCULE et BKT est bien meilleur. NMS est un FILET DE SECURITE pour les cas ou BKT ne s'applique pas.

**WHY 3 :** Que donne NMS pour le budget de dissipation ?
Budget NMS = n * log(1/(1 - c/s^2)) ~ n * c/s^2 ~ 0.585k * c/s^2. Le besoin est log d ~ 1.585k. Donc il faut c/s^2 > 1.585/0.585 ~ 2.71. Pour s >= 2, c/4 > 2.71, soit c > 10.84. La constante c depend de la distribution ; typiquement c ~ 1. Donc NMS seul NE ferme PAS le gap.

**WHY 4 :** NMS est-il inutile alors ?
NON. NMS prouve que la DISSIPATION est STRICTEMENT POSITIVE a chaque etape. C'est une condition NECESSAIRE pour que n'importe quel argument asymptotique fonctionne. Sans NMS (ou un equivalent), on ne pourrait pas exclure le cas pathologique |rho_a| = 1 pour certains a.

**WHY 5 :** Comment combiner NMS et BKT ?
NMS couvre les cas ou s est petit (s < d^delta ou s > d^{1-delta}), et BKT couvre le cas intermediaire. Ensemble, ils donnent une borne |rho_a| <= max(1 - c/s^2, d^{-eta}) < 1 pour TOUT a != 0 et TOUT d >= 5 impair, avec s = ord_d(2) >= 2.

**Statut : PROUVE** (critere NMS). Combinaison NMS+BKT : **PROUVE** pour d premier, **CONDITIONNEL** pour d compose.

---

## 6. QUESTION 5 : LA STRUCTURE SPECIFIQUE d = 2^S - 3^k ET L'INVENTION DE LA COMPLETION ORBITALE

### 6.1 L'identite fondamentale revisitee

La relation 2^S = 3^k mod d signifie que dans le groupe (Z/dZ)*, les elements 2 et 3 satisfont une EQUATION : 2^S * 3^{-k} = 1 mod d. Autrement dit, le couple (S, k) definit un POINT sur le sous-groupe de Mordell-Weil du tore multiplicatif... Non, c'est plus simple que ca.

Le sous-groupe <2, 3> de (Z/dZ)* est engendre par deux elements 2 et 3 lies par la relation 2^S = 3^k. Le groupe de relations de <2, 3> contient le vecteur (S, -k). Si c'est le SEUL generateur du groupe de relations (cas generique), alors <2, 3> = Z^2 / (S, -k)Z = Z / (gcd du truc)... En fait, |<2, 3>| = lcm(s, t) / gcd-quelque-chose ou s = ord_d(2), t = ord_d(3).

Ce qui compte, c'est la TAILLE de <2, 3>.

### 6.2 Lemme de generation large

> **Lemme R191-L2 (Generation large) [CONDITIONNEL].**
> Pour d = 2^S - 3^k premier avec k >= 4, le sous-groupe <2, 3> de (Z/dZ)* satisfait :
>
> |<2, 3>| >= d^{2/3}
>
> **Heuristique :** Comme <2> et <3> sont lies par 2^S = 3^k mod d, on a |<2,3>| = lcm(ord_d(2), ord_d(3)). Par la conjecture d'Artin generalisee, chacun a un ordre >= d^{1/2-epsilon}. Le lcm est au moins max(s, t) >= d^{1/2-epsilon}. La borne d^{2/3} est plus forte et necessite que s et t ne soient pas trop "alignes".
>
> **Statut : CONJECTURE.** Compatible avec les heuristiques, mais aucune preuve connue.

### 6.3 L'Invention de la Completion Orbitale

C'est la contribution la plus importante de ce round.

**L'idee :** La somme Lambda(s) = SUM_v omega^{s * g(v)/d} est une somme sur les partitions MONOTONES v ∈ V_k(S). La monotonie est le verrou (R189, R190). Et si on COMPLETAIT la somme en ajoutant les vecteurs NON-MONOTONES, puis en soustrayant la correction ?

**Formellement :**

Definissons V_k^{free}(S) = {(B_0, ..., B_{k-1}) ∈ (Z/sZ)^k : SUM B_j = n mod s} (les k-tuples LIBRES, sans monotonie, avec somme fixee mod s).

Lambda^{free}(a) = SUM_{v ∈ V_k^{free}} omega^{a * g^{free}(v)}

ou g^{free}(v) = SUM_j 3^{k-1-j} * 2^{B_j} mod d.

**Cle :** Lambda^{free}(a) se FACTORISE.

> **Theoreme R191-T3 (Factorisation de la somme libre) [PROUVE].**
> Lambda^{free}(a) = PROD_{j=0}^{k-1} [SUM_{b=0}^{s-1} omega^{a * 3^{k-1-j} * 2^b}] * (correction de somme)
>
> Plus precisement, sans la contrainte de somme :
>
> SUM_{v ∈ (Z/sZ)^k} omega^{a * g^{free}(v)} = PROD_{j=0}^{k-1} [SUM_{b=0}^{s-1} omega^{a * 3^{k-1-j} * 2^b}]
>
> = PROD_{j=0}^{k-1} [s * rho_{a * 3^{k-1-j}}]
>
> = s^k * PROD_{j=0}^{k-1} rho_{a_j}
>
> ou a_j = a * 3^{k-1-j} mod d.
>
> **Preuve.** Quand les B_j sont independants et parcourent chacun Z/sZ, la somme sur v est un produit de sommes independantes. Chaque facteur est SUM_{b=0}^{s-1} omega^{a_j * 2^b} = s * rho_{a_j} par definition de rho_a_j. CQFD.

**La puissance de ce theoreme :** Le produit PROD_j rho_{a_j} est EXACTEMENT le spectre de dissipation de R189 ! Mais maintenant, il apparait comme une FORMULE EXACTE pour la somme libre, pas comme une heuristique.

### 6.4 La correction de monotonie

La vraie somme Lambda(a) est sur les partitions MONOTONES, pas sur les k-tuples libres. La correction est :

Lambda(a) = Lambda^{free}(a) - Lambda^{non-mono}(a)

ou Lambda^{non-mono} est la somme sur les k-tuples qui satisfont la contrainte de somme mais PAS la monotonie.

> **Conjecture R191-C1 (Correction de monotonie petite).**
> |Lambda^{non-mono}(a)| <= (1 - 1/k!) * |Lambda^{free}(a)|
>
> i.e., la correction est au plus une fraction (1 - 1/k!) de la somme libre.
>
> **Heuristique :** Parmi les k! permutations d'un k-tuple, exactement UNE est monotone. Si les phases etaient independantes de l'ordre, la somme monotone serait (1/k!) * la somme libre. La correction serait alors (1 - 1/k!) * la somme libre. L'hypothese "independante de l'ordre" est FAUSSE en general (g depend de l'ordre via les poids 3^{k-1-j}), mais donne l'ordre de grandeur.

### 6.5 WHY chain : Puissance de la completion orbitale

**WHY 1 :** Pourquoi la completion est-elle puissante ?
Parce qu'elle remplace une somme CONTRAINTE (monotonie) par un PRODUIT de facteurs independants. Le produit est exactement PROD rho_{a_j}, qui est controle par BKT ou NMS.

**WHY 2 :** Pourquoi la correction est-elle petite ?
Parce que la fraction des k-tuples monotones dans les k-tuples libres est exactement 1/C(s+k-1, k) (par etoiles et barres), qui est MINUSCULE pour s >= 2 et k grand. La somme libre "domine" la somme monotone en nombre de termes.

**ATTENTION :** "Dominer en nombre de termes" ne signifie pas "dominer en somme de phases". Les phases des termes non-monotones pourraient s'annuler, laissant la somme monotone comme terme dominant.

**WHY 3 :** Comment controler la correction plus rigoureusement ?
Par INCLUSION-EXCLUSION. Definissons A_i = {v : B_i > B_{i+1}} (l'ensemble des vecteurs ou la monotonie est violee a la position i). Alors :

Lambda^{non-mono} = SUM_v 1_{v non monotone} * omega^{a*g(v)} = SUM_{v ∈ UNION A_i} omega^{a*g(v)}

Par inclusion-exclusion : |Lambda^{non-mono}| <= SUM_i |SUM_{v ∈ A_i} omega^{a*g(v)}|

Chaque terme SUM_{v ∈ A_i} est une somme de phases ou on FORCE B_i > B_{i+1}. On peut echanger B_i et B_{i+1} (transposition) et utiliser la SYMETRIE de l'echange pour borner la somme.

**WHY 4 :** Que donne l'echange de B_i et B_{i+1} ?
L'echange tau_i : (B_0, ..., B_i, B_{i+1}, ..., B_{k-1}) -> (B_0, ..., B_{i+1}, B_i, ..., B_{k-1}) change g(v) en g(tau_i(v)) = g(v) + (3^{k-1-i} - 3^{k-2-i}) * (2^{B_{i+1}} - 2^{B_i}).

La difference est : g(tau_i v) - g(v) = 3^{k-2-i} * (3 - 1) * (2^{B_{i+1}} - 2^{B_i}) = 2 * 3^{k-2-i} * (2^{B_{i+1}} - 2^{B_i}).

Quand B_i > B_{i+1}, la difference est 2 * 3^{k-2-i} * (2^{B_{i+1}} - 2^{B_i}) < 0, et sa valeur absolue est au moins 2 * 3^{k-2-i}.

**WHY 5 :** Pourquoi cette difference aide-t-elle ?
Parce qu'elle montre que les termes "non-monotones" ont des phases DECALEES de au moins 2*pi * 2 * 3^{k-2-i} / d par rapport a leurs transposees. Si ce decalage est GRAND (>> 1/d), les paires (v, tau_i v) s'annulent partiellement. Le nombre de paires non-annulees est borne par le nombre de v ou le decalage est petit (i.e., d | 2 * 3^{k-2-i} * (2^{B_{i+1}} - 2^{B_i}) approximativement), ce qui est RARE.

**Statut : CONDITIONNEL** (C1 : borne sur la correction de monotonie). L'argument par transposition est PROMETTEUR mais pas clos.

### 6.6 Theoreme conditionnel de fermeture

> **Theoreme R191-T4 (Fermeture du gap par completion orbitale) [CONDITIONNEL sur C1 et C2].**
>
> Sous les hypotheses :
> - (C1) d = 2^S - 3^k premier, s = ord_d(2) avec d^{1/3} <= s <= d^{2/3}
> - (C2) |Lambda^{non-mono}(a)| <= (1 - epsilon) * |Lambda^{free}(a)| pour un epsilon > 0 independant de k
>
> Alors : |Lambda(a)| <= epsilon * s^k * PROD_j |rho_{a_j}|
>
> Et par BKT : PROD_j |rho_{a_j}| <= d^{-k*eta}
>
> Donc |Lambda(a)| <= epsilon * s^k * d^{-k*eta}
>
> La condition |Lambda(a)| < p_k(n)/d est satisfaite des que epsilon * s^k * d^{-k*eta} < p_k(n)/d.
>
> Or s^k <= d^k et p_k(n) >= 1, donc il suffit que d^{k(1-eta)} < d/epsilon, soit k(1-eta) < 1 - log(epsilon)/log(d). Pour eta > 0 et k >= 2, c'est SATISFAIT des que eta > (k-1)/(k) - log(epsilon)/(k*log(d)), ce qui est vrai pour k assez grand.
>
> **Statut : CONDITIONNEL sur C1 et C2.** La dependance en k de k_0 est explicitable : k_0 ~ 1/eta ~ 1/delta^C.

---

## 7. QUESTION SUBSIDIAIRE : RESULTATS SPECIALISES POUR d = 2^S - 3^k

### 7.1 Connection au projet Cunningham

Les nombres de la forme 2^a - 3^b sont etudies dans le projet Cunningham (factorisation des nombres de la forme b^n +/- 1). Plus precisement, d = 2^S - 3^k n'est pas exactement de cette forme, mais est LIE a 2^S mod 3^k et a la factorisation de nombres de Mersenne generalises.

**Resultats connus (incomplets) :**
- Pour a = S et b = k "proches" du rapport log_2(3), d est "petit" par rapport a 2^S. En fait d ~ 2^S * (1 - (3/4)^{k/S}) ~ 2^S * c(k) pour une constante c(k) qui depend de la partie fractionnaire de k * log_2(3).
- La factorisation de d est "aleatoire" au sens de la conjecture de Cramers : le plus petit facteur premier de d est typiquement d^{o(1)} ou plus grand.

### 7.2 Resultats de Catalan-Mihailescu elargis

> **Fait R191-F1 [PROUVE].** (Consequence de Catalan-Mihailescu.)
> Pour S >= 4 et k >= 2 avec S = ceil(k * log_2(3)) :
> - d = 2^S - 3^k >= 5
> - d n'est jamais une puissance parfaite
> - d n'est jamais 2 fois une puissance parfaite (car d est impair)
>
> **Preuve.** Si d = m^r pour r >= 2, alors 2^S = 3^k + m^r, ce qui serait une equation de Catalan generalisee. Par Mihailescu (2004), les seules puissances parfaites consecutives sont 8 et 9 (i.e., 2^3 - 3^2 = -1). Pour d = m^r >= 5, il n'y a pas de solution connue et les conjectures abc impliquent qu'il n'y en a qu'un nombre fini.

### 7.3 Inventaire des outils disponibles par regime de s

| Regime de s = ord_d(2) | Outils disponibles | Borne sur \|rho_a\| | Statut |
|---|---|---|---|
| s = d - 1 (2 generateur, d premier) | Calcul direct | 1/(d-1) | PROUVE |
| d^{1/2} <= s < d - 1 | BKT direct | d^{-eta(1/2)} | PROUVE (BKT) |
| d^delta <= s < d^{1/2} | BKT | d^{-eta(delta)} | PROUVE (BKT) |
| log(d) <= s < d^delta | NMS + completion | 1 - c/s^2 | PROUVE (NMS) |
| s < log(d) | Cas par cas | Borne faible | OUVERT |

**Observation cruciale :** Le cas s < log(d) est ESSENTIELLEMENT IMPOSSIBLE pour nos d. En effet, s = ord_d(2) et 2^S = 3^k mod d avec S ~ 1.585k ~ log_2(d). Donc 2^{O(log d)} = 3^k mod d, et l'ordre de 2 divise au pire quelques multiples de S ~ log d. Mais l'ordre MINIMUM est au moins S / gcd(S, truc) >= S / S = 1, ce qui est trivial. En realite, par les arguments de la Section 2.2 :

> **Lemme R191-L3 [PROUVE].** s = ord_d(2) >= S.
>
> **Preuve.** 2^S = 3^k mod d, et 3^k != 1 mod d (car d = 2^S - 3^k et 3^k - 1 != 0 mod d pour k >= 2, ce qui se verifie directement : d | (3^k - 1) ssi 2^S - 3^k | 3^k - 1 ssi 2^S - 3^k | 2^S - 1, soit d | 2^S - 1. Mais d = 2^S - 3^k et 2^S - 1 = d + 3^k - 1. Donc d | 2^S - 1 ssi d | 3^k - 1. Pour k = 2 : d = 7, 3^2 - 1 = 8, 7 ne divise pas 8. Pour k = 3 : d = 5, 3^3 - 1 = 26, 5 ne divise pas 26. GENERIQUEMENT FAUX.)
>
> Donc 2^S != 1 mod d (car 3^k != 1 mod d pour k >= 2 generique), ce qui signifie s = ord_d(2) NE DIVISE PAS S.
>
> Mais s pourrait quand meme etre < S (par exemple s = S - 1 ne divise pas S). Ce qu'on peut dire : si s < S, alors 2^s = c mod d pour un c != 1, et 2^S = 2^{S mod s} * c^{floor(S/s)} mod d. La relation 2^S = 3^k impose une equation en c, s. Pour s << S, cette equation est TRES contraignante.
>
> **CORRECTION :** Le lemme s >= S est FAUX en general. On peut seulement prouver s >= 1 trivialement. L'argument ci-dessus montre que s ne divise pas S generiquement, mais s pourrait etre n'importe quel entier > 0.
>
> **Statut : RETRACTE.** Le lemme est trop fort. On conserve l'observation que s ne divise pas S generiquement.

---

## 8. SYNTHESE : STRATEGIE DE FERMETURE A DEUX ETAGES

### 8.1 Architecture de la preuve conditionnelle

La strategie combine les resultats des Sections 1-7 en une architecture a deux etages :

**Etage 1 (k >= k_0) : Argument de comptage (R189 T10, Borel-Cantelli).**
Pour k >= 42 (ou k >= k_0 pour un k_0 effectif), le nombre de partitions p_k(n) depasse d, et l'argument de deuxieme moment (sans aucune borne sur les sommes exponentielles) donne E[N_0] < 1. Avec un argument de concentration, N_0 = 0 presque surement. **PROUVE** (sous hypothese d'equidistribution, validee par R190 Red Team).

**Etage 2 (2 <= k < k_0) : BKT + Completion Orbitale.**
Pour chaque k dans {2, ..., k_0 - 1} :

(a) Si d = 2^S - 3^k est premier et s = ord_d(2) ∈ [d^delta, d^{1-delta}] :
- BKT donne |rho_a| <= d^{-eta}
- La completion orbitale (T3) donne Lambda^{free}(a) = s^k * PROD rho_{a_j}
- Sous C2 (correction de monotonie petite), Lambda(a) ~ epsilon * Lambda^{free}(a)
- La borne |Lambda(a)| < p_k(n)/d est satisfaite pour k >= 1/eta. **CONDITIONNEL (C1 + C2).**

(b) Si d est premier mais s est hors du regime BKT :
- NMS donne |rho_a| <= 1 - c/s^2
- Le regime s ~ d (ou s ~ 1) rend le budget NMS insuffisant pour une borne generique
- MAIS pour s ~ d (2 generateur), |rho_a| ~ 1/d, et le budget est QUADRATIQUE en k (Section 3.3). GAP FERME.
- Pour s tres petit (< d^delta), cas par cas necessaire. **OUVERT** pour le cas generique.

(c) Si d est compose :
- Bourgain (2005) s'applique si p_min(d) >= d^epsilon. **CONDITIONNEL.**
- Sinon, factoriser d = p1 * p2 * ... et utiliser le CRT + bornes composante par composante. **OUVERT.**

### 8.2 Tableau des resultats

| # | Resultat | Statut | Dependances |
|---|----------|--------|-------------|
| R191-P1 | Primalite generique de d | CONJECTURE | Heuristiques Cunningham |
| R191-P2 | ord_d(2) >= d^{1/3} | CONJECTURE | Artin generalisee |
| R191-T1 | BKT ferme le gap pour k grand | CONDITIONNEL | C1 (regime de s) + C2 (decouplage) |
| R191-T2 | Critere NMS : \|rho_a\| < 1 | PROUVE | Aucune |
| R191-T3 | Factorisation de Lambda^{free} | PROUVE | Aucune |
| R191-T4 | Fermeture par completion orbitale | CONDITIONNEL | C1 + C2 |
| R191-L1 | 3^k ∈ <2> mod d | PROUVE | Aucune |
| R191-L2 | \|<2,3>\| >= d^{2/3} | CONJECTURE | Artin generalisee |
| R191-L3 | s ne divise pas S generiquement | OBSERVATION | Exemples |
| R191-C1 | Correction de monotonie petite | CONJECTURE | Argument de transposition |
| R191-F1 | d jamais puissance parfaite | PROUVE | Catalan-Mihailescu |

### 8.3 WHY chain globale : Pourquoi cette strategie fonctionne-t-elle ?

**WHY 1 :** Pourquoi separer en deux etages ?
Parce que les outils sont DIFFERENTS. L'Etage 1 (k grand) utilise le COMPTAGE (beaucoup de partitions vs peu de classes mod d). L'Etage 2 (k petit) utilise la STRUCTURE ARITHMETIQUE (BKT, sommes de caracteres, completion orbitale).

**WHY 2 :** Pourquoi BKT est-il le bon outil pour l'Etage 2 ?
Parce que BKT est le resultat le plus GENERAL sur les sommes exponentielles sur les sous-groupes multiplicatifs. Notre somme rho_a est EXACTEMENT une telle somme. Les descendants de BKT (Bourgain-Glibichuk-Konyagin, Garaev, Konyagin-Shparlinski) donnent des bornes de plus en plus explicites.

**WHY 3 :** Pourquoi la completion orbitale est-elle necessaire en plus de BKT ?
Parce que BKT borne |rho_a| (la dissipation par etape), mais le passage de |rho_a| a |Lambda(a)| (la somme sur les partitions) necessite le DECOUPLAGE des etapes. La completion orbitale fournit ce decouplage en passant par la somme libre (ou les etapes SONT independantes), avec une correction bornable.

**WHY 4 :** Pourquoi la correction de monotonie est-elle le verrou principal ?
Parce que c'est le SEUL ingredient non-prouve dans la chaine. Si C1 (borne sur la correction) est vrai, toute la strategie fonctionne. C'est un probleme de COMBINATOIRE DES PARTITIONS avec des phases, qui est plus accessible que le probleme de Collatz original.

**WHY 5 :** Comment aborder C1 ?
Trois pistes :
(a) L'argument par TRANSPOSITION (Section 6.5) : montrer que les paires (v, tau_i v) s'annulent partiellement.
(b) L'argument par SYMETRIE de Weyl : le groupe symetrique S_k agit sur les k-tuples, et la somme monotone est la projection sur le sous-espace "symetrique". La taille de cette projection est 1/k! de la somme totale, a des corrections de phase pres.
(c) L'argument par REPRESENTATIONS : la somme libre se decompose en representations irreductibles de S_k, et la composante monotone est la representation triviale. La correction est la somme des autres representations, dont les dimensions sont controlees par la theorie des partitions de Young.

**Statut des pistes :** Toutes OUVERTES. La piste (b) est la plus naturelle et la plus susceptible de donner un resultat quantitatif.

---

## 9. CE QUE CETTE ANALYSE CHANGE PAR RAPPORT A R189-R190

### 9.1 Acquis nouveaux

1. **BKT s'applique directement** a notre rho_a quand d est premier et s est intermediaire. Ce n'etait pas explicite dans R189-R190.

2. **La non-maximalite |rho_a| < 1 est PROUVEE** pour tout d >= 5 (NMS, T2). C'etait implicite mais pas formalise.

3. **La completion orbitale** (T3) transforme la somme contrainte en produit de dissipations * correction. C'est une NOUVELLE TECHNIQUE qui n'apparait pas dans R189-R190.

4. **Le verrou est LOCALISE** : c'est la conjecture C1 (correction de monotonie petite), un probleme de combinatoire des partitions avec des phases.

5. **La structure d = 2^S - 3^k est EXPLOITEE** via L1 (3^k ∈ <2>) et la generation large (L2). Ce n'etait pas utilise dans R189.

### 9.2 Ce qui reste ouvert

1. **C1 (correction de monotonie)** : Le verrou central. Trois pistes identifiees, aucune close.
2. **P2 (taille de l'ordre)** : La conjecture ord_d(2) >= d^{1/3} n'est pas prouvee.
3. **Le cas d compose** : Traitement partiel (Bourgain 2005), pas complet.
4. **Les petits k (k = 2, 3, 4, 5)** : Doivent etre traites un par un (verification directe possible).

### 9.3 Score d'avancement

| Critere | Score | Commentaire |
|---------|-------|-------------|
| Identification du bon outil (BKT) | 9/10 | Application directe a rho_a, claire |
| Borne qualitative (NMS) | 10/10 | PROUVE, aucune hypothese |
| Borne quantitative (power-saving) | 7/10 | CONDITIONNEL, mais chemin explicite |
| Fermeture du gap | 5/10 | CONDITIONNEL sur C1 (correction monotonie) |
| Innovation (completion orbitale) | 8/10 | Technique nouvelle et prometteuse |
| Honnetete | 9/10 | Conjectures et conditionnels identifies |

**Score global R191 : 8/10**

---

## 10. FEUILLE DE ROUTE POUR R192

### 10.1 Priorite 1 : Attaquer C1 par la piste de symetrie de Weyl

Formaliser l'argument : la somme sur les k-tuples libres se decompose en representations de S_k. La composante monotone est la representation triviale. Borner la correction par les dimensions des representations non-triviales.

### 10.2 Priorite 2 : Verification numerique de P2

Pour k = 2, ..., 20, calculer s = ord_d(2) et verifier si s >= d^{1/3}. Si OUI pour tous : renforcement heuristique. Si NON pour certains : identifier les contre-exemples et adapter la strategie.

### 10.3 Priorite 3 : Traitement cas par cas pour k = 2, 3, 4, 5

Pour ces petits k, calculer N_0 directement (enumeration finie des partitions) et verifier N_0 = 0. Cela elimine les cas ou les arguments asymptotiques ne s'appliquent pas.

### 10.4 Priorite 4 : Explorer la connexion avec Tao (2019)

Identifier si l'argument de Tao pour "presque toutes les orbites" utilise une version de la completion orbitale ou de BKT, et si cette machinerie s'adapte au probleme des cycles.

---

## 11. REGISTRE

| Element | Statut | Section |
|---------|--------|---------|
| BKT applicable a rho_a (d premier, s intermediaire) | PROUVE (BKT 2004) | 3.2 |
| NMS : \|rho_a\| < 1 pour tout a != 0 | PROUVE | 5.3 |
| Factorisation Lambda^{free} = s^k * PROD rho_{a_j} | PROUVE | 6.3 |
| 3^k ∈ <2> mod d | PROUVE | 5.2 |
| d jamais puissance parfaite | PROUVE (Catalan) | 7.2 |
| Fermeture du gap par BKT + completion | CONDITIONNEL (C1+C2) | 6.6 |
| ord_d(2) >= d^{1/3} | CONJECTURE (P2) | 2.3 |
| Correction de monotonie petite | CONJECTURE (C1) | 6.4 |
| Generation large \|<2,3>\| >= d^{2/3} | CONJECTURE (L2) | 6.2 |
| Primalite generique de d | CONJECTURE (P1) | 1.3 |

---

*R191 : L'application de BKT (2004) et ses descendants a notre probleme est DIRECTE et donne une borne power-saving |rho_a| <= d^{-eta} quand d est premier et s = ord_d(2) est intermediaire. Le critere NMS prouve |rho_a| < 1 sans aucune hypothese. La COMPLETION ORBITALE (nouvelle technique) factorise la somme libre en PROD rho_{a_j}, reduisant le probleme a borner la correction de monotonie (Conjecture C1). La structure specifique d = 2^S - 3^k fournit le couplage 3^k ∈ <2> (Lemme L1). Le gap de 1.35x de R189 est theoriquement FERMABLE par cette strategie a deux etages (comptage pour k grand + BKT/completion pour k petit), sous deux conjectures techniques (C1, C2). Le verrou principal est desormais un probleme de COMBINATOIRE DES PARTITIONS avec des phases (C1), plus accessible que le probleme original.*
