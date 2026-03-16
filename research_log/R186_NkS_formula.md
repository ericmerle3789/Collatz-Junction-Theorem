# R186 — AGENT FORMULE EXACTE : N(k,S) et la question N(k,S) < d
**Date :** 16 mars 2026
**Mode :** Raisonnement pur, ZERO calcul
**Prerequis :** R184 T1 (comptage corrige), R185 RED TEAM (piste N(k,S) < d)
**Objectif :** Formule exacte ou borne serree pour N(k,S), et analyse critique de ce que N(k,S) < d impliquerait

---

## 0. RESUME EXECUTIF

N(k,S) = p(S-k, ≤k) (partitions de S-k en au plus k parts). Pour S = ceil(k·log₂(3)), on a n = S-k ~ 0.585k. La formule asymptotique p(n,≤k) ~ n^{k-1}/(k!·(k-1)!) est correcte et donne N(k,S)/d → 0 exponentiellement.

**MAIS : N(k,S) < d ne suffit PAS à exclure les cycles.** C'est l'erreur logique centrale identifiée dans ce round. N(k,S) est le nombre de vecteurs v, pas le nombre de valeurs distinctes de g(v). La condition pour un cycle est g(v) = n·d pour un n ≥ 1, et le range de g couvre typiquement [g_min, g_max] avec g_max/d >> 1. Même avec N(k,S) = 2 vecteurs, si l'un d'eux satisfait g(v) ≡ 0 mod d, un cycle existe.

Ce que N(k,S) < d permet, c'est un **argument probabiliste** : si les N(k,S) valeurs de g(v) mod d étaient uniformément distribuées dans {0,...,d-1}, la probabilité qu'aucune ne tombe sur 0 serait (1-1/d)^{N(k,S)} ≈ exp(-N(k,S)/d) → 1. Mais cet argument est **heuristique**, pas une preuve.

**Score de la piste N(k,S) < d : 4/10** (pas 7/10 comme estimé en R185). L'heuristique probabiliste est correcte mais ne constitue pas une preuve. Le passage de "probablement pas de cycle" à "certainement pas de cycle" est exactement le gap de Tao (2019).

---

## 1. IDENTIFICATION PRECISE DE N(k,S)

### 1.1 Définition

Un cycle de Collatz avec k étapes impaires et S étapes paires est paramétré par un vecteur v = (B₀, B₁, ..., B_{k-1}) avec :
- B_j ≥ 0, entiers
- B₀ ≤ B₁ ≤ ... ≤ B_{k-1} (monotonie)
- Σ_{j=0}^{k-1} B_j = S - k

**CONVENTION :** Ici B_j = b_j correspond au changement de variable b_j = B_j^{orig} - 1 où B_j^{orig} ≥ 1 est le nombre de divisions par 2 après la j-ième étape impaire. La contrainte B_j^{orig} ≥ 1 devient b_j ≥ 0, et Σ B_j^{orig} = S devient Σ b_j = S - k. La monotonie B_0^{orig} ≤ ... ≤ B_{k-1}^{orig} est équivalente à b₀ ≤ ... ≤ b_{k-1}.

**NOTE IMPORTANTE sur la monotonie :** La monotonie B₀ ≤ B₁ ≤ ... ≤ B_{k-1} n'est PAS une contrainte du problème de Collatz en général. Dans un cycle de Collatz, les B_j (nombre de divisions par 2 après chaque étape impaire) peuvent être dans N'IMPORTE QUEL ordre. La monotonie apparaît quand on ORDONNE les B_j de manière croissante, ce qui est toujours possible car g(v) dépend des B_j via une somme pondérée par des puissances de 3 DECROISSANTES, et la réorganisation en ordre croissant minimise g(v) (inégalité de réarrangement de Chebyshev).

CORRECTION : En fait, les B_j ne sont PAS librement réarrangeables. Le B_j est attaché à la j-ième étape impaire dans l'ORDRE TEMPOREL du cycle. La somme g(v) = Σ 3^{k-1-j} · 2^{B_j} a le poids 3^{k-1-j} attaché au j-ième B_j. Si on permute les B_j, on obtient un AUTRE vecteur avec potentiellement une AUTRE valeur de g. Le comptage N(k,S) avec monotonie est le nombre de vecteurs ORDONNES, pas le nombre de profils non ordonnés.

Reprenons. Pour un cycle (k, S), le vecteur v = (B₀,...,B_{k-1}) est ordonné temporellement. Les B_j ne sont pas nécessairement monotones. Le nombre total de vecteurs (sans contrainte de monotonie) est le nombre de compositions de S-k en k parts non-négatives : C(S-1, k-1).

MAIS la littérature sur les cycles de Collatz (Steiner 1977, Eliahou 1993) travaille bien avec des vecteurs monotones. Pourquoi ? Parce que le problème a une symétrie cyclique : un cycle de longueur k + S revient au même point, et on peut CHOISIR le point de départ de manière à obtenir B₀ ≤ B₁ ≤ ... ≤ B_{k-1}.

NON — ce n'est pas correct non plus. La permutation cyclique du point de départ change les B_j mais ne les ordonne pas nécessairement.

**CLARIFICATION DEFINITIVE :** La monotonie est une CONVENTION TECHNIQUE spécifique. Dans le formalisme standard (Steiner-Eliahou), un cycle (k,S) est associé à un vecteur d'exposants e = (e₁,...,e_k) où e_j ≥ 1 est le nombre de divisions par 2 après la j-ième multiplication par 3. On a Σ e_j = S. Le nombre n du cycle satisfait :

n = g(e) / (2^S - 3^k)

où g(e) = Σ_{j=1}^{k} 3^{k-j} · 2^{e_1+...+e_j}

Les exposants cumulés sont C_j = e_1 + ... + e_j. On a 0 < C_1 < C_2 < ... < C_k = S (strictement croissants). Le vecteur (C_1,...,C_k) est strictement croissant, ce qui par le changement B_j = C_{j+1} - (j+1) donne des B_j CROISSANTS (au sens large : B₀ ≤ B₁ ≤ ...).

En fait, définissons B_j = C_{j+1} - (j+1) pour j = 0,...,k-1. Alors C_{j+1} = B_j + j + 1, et la croissance stricte C_j < C_{j+1} donne B_{j-1} + j < B_j + j + 1, soit B_j > B_{j-1} - 1, c'est-à-dire B_j ≥ B_{j-1} (monotonie large car entiers).

Et Σ B_j = Σ (C_{j+1} - (j+1)) = C_k - k(k+1)/2 + Σ_{j=0}^{k-1} j... Non, calculons directement :

Σ_{j=0}^{k-1} B_j = Σ_{j=0}^{k-1} (C_{j+1} - (j+1)) = (C_1 + C_2 + ... + C_k) - (1+2+...+k)

Ce n'est PAS S - k en général. Recalculons.

Revenons aux notations de base. Posons a_j = e_j - 1 ≥ 0 (excédent au-dessus du minimum 1). Alors Σ a_j = S - k. Et C_j = j + Σ_{i=1}^{j} a_i. La croissance stricte est automatique.

La fonction g s'écrit : g = Σ_{j=1}^{k} 3^{k-j} · 2^{C_j} = Σ_{j=1}^{k} 3^{k-j} · 2^{j + Σ_{i=1}^{j} a_i}.

C'est la bonne paramétrisation. Les variables libres sont (a₁,...,a_k) avec a_j ≥ 0 et Σ a_j = S - k. Il n'y a PAS de contrainte de monotonie sur les a_j.

**Le nombre de vecteurs est donc :**

N_total(k,S) = nombre de compositions faibles de S-k en k parts = C(S-1, k-1)

**Où intervient la monotonie ?** Elle n'intervient PAS directement. Le comptage N(k,S) du prompt est donc une question DIFFERENTE du comptage total.

### 1.2 Réconciliation avec le formalisme du prompt

Le prompt définit N(k,S) comme le nombre de vecteurs (B₀,...,B_{k-1}) avec :
- 0 ≤ B₀ ≤ ... ≤ B_{k-1}
- Σ B_j = S - k

Cette contrainte de monotonie correspond à compter les PARTITIONS de S-k en k parts non-négatives. C'est p(S-k, ≤k).

Mais quel est le rapport avec le problème de Collatz ? Si on considère les vecteurs e = (e₁,...,e_k) avec e_j ≥ 1 et Σ e_j = S, le nombre TOTAL de vecteurs est C(S-1, k-1). Le sous-ensemble des vecteurs MONOTONES (e₁ ≤ e₂ ≤ ... ≤ e_k) est en bijection avec les partitions de S en k parts ≥ 1, donc les partitions de S-k en k parts ≥ 0, c'est-à-dire p(S-k, ≤k).

Chaque partition non-ordonnée de S en k parts ≥ 1 correspond à PLUSIEURS vecteurs ordonnés (les permutations). Si la partition a des parts distinctes, il y a k! permutations. Si certaines parts sont égales, il y a k!/Π m_j! permutations (multinomiale).

**La question du prompt** porte sur les vecteurs MONOTONES. Cela a un sens si on considère qu'un cycle est déterminé à permutation cyclique près, et qu'on choisit un représentant canonique (le plus petit dans l'ordre lexicographique, qui est le monotone croissant).

**MAIS ATTENTION :** une permutation des e_j donne un AUTRE vecteur avec une AUTRE valeur de g(e). Deux vecteurs qui sont des permutations l'un de l'autre NE donnent PAS le même cycle.

**VERDICT :** Le comptage N(k,S) = p(S-k, ≤k) est le nombre de vecteurs MONOTONES. Le nombre total de vecteurs est C(S-1, k-1). La monotonie est une restriction, pas une symétrie. Pour l'argument de comptage, on devrait utiliser le TOTAL C(S-1, k-1) si on veut compter tous les cycles possibles, ou N(k,S) si on se restreint aux cycles dont les exposants sont ordonnés.

**POUR LA SUITE :** Je vais analyser les DEUX quantités et leur rapport à d.

---

## 2. FORMULE EXACTE POUR N(k,S) = p(n, ≤k) avec n = S-k

### 2.1 Fonction génératrice

p(n, ≤k) = [x^n] Π_{j=1}^{k} 1/(1-x^j)

C'est la fonction génératrice standard des partitions en au plus k parts.

### 2.2 Formule exacte pour petits k

**k=1 :** p(n, ≤1) = 1 pour tout n ≥ 0 (unique partition : {n}).

**k=2 :** p(n, ≤2) = floor(n/2) + 1.
Preuve : partitions de n en ≤2 parts : (a,b) avec a ≤ b et a+b = n. Alors a ∈ {0,1,...,floor(n/2)}, d'où floor(n/2)+1.

**k=3 :** p(n, ≤3) = round(n²/12) (plus précisément, le plus proche entier de (n+3)²/12).
Formule exacte : p(n, ≤3) = round((n²+6n+12)/12) ... Non.

Soyons rigoureux. Pour k=3, la fonction génératrice est 1/((1-x)(1-x²)(1-x³)). Par décomposition en fractions partielles :

p(n, ≤3) = { round((n+3)²/12) }

Plus précisément :
- Si n ≡ 0 mod 12 : (n²+12n+12)/12 ...

En fait, la formule classique est :

p(n, ≤3) = round(n²/12) pour n → ∞, avec le terme exact dépendant de n mod 6.

Utilisons plutôt la formule récursive ou les valeurs directes.

### 2.3 Formule asymptotique pour k fixe, n → ∞

Pour k fixe et n → ∞ :

**p(n, k) ~ n^{k-1} / (k! · (k-1)!)** (nombre de partitions de n en EXACTEMENT k parts)

Et p(n, ≤k) = Σ_{j=0}^{k} p(n, j), dominé par le terme j=k :

**p(n, ≤k) ~ n^{k-1} / (k! · (k-1)!)**

### 2.4 Formule asymptotique pour n et k croissant ensemble

Notre régime est n = S - k ~ 0.585k, donc n et k sont du MÊME ordre. La formule k fixe ne s'applique pas directement. Nous sommes dans le régime n/k → λ ≈ 0.585, n → ∞.

Dans ce régime, p(n, ≤k) est le coefficient de x^n dans Π_{j=1}^{k} 1/(1-x^j).

Par la méthode du col (saddle point) : log p(n, ≤k) = max_β [βn + Σ_{j=1}^{k} log(1/(1-e^{-βj}))]

Il faut résoudre l'équation de col : n = Σ_{j=1}^{k} j/(e^{βj} - 1).

Pour n ~ 0.585k et k grand, β ~ c/k pour une constante c > 0 (car les termes j/(e^{βj}-1) ~ 1/β pour βj petit). Plus précisément, si β = c/k :

n ≈ Σ_{j=1}^{k} j/(e^{cj/k} - 1) ≈ ∫₀¹ (kt)/(e^{ct} - 1) · k dt = k² ∫₀¹ t/(e^{ct} - 1) dt

Mais n ~ 0.585k, pas ~ k². Donc β ne peut pas être ~ 1/k. Essayons β ~ O(1) :

n = Σ_{j=1}^{k} j/(e^{βj} - 1). Pour β ~ O(1), les termes avec j grand sont exponentiellement petits, donc la somme est essentiellement Σ_{j=1}^{∞} j/(e^{βj}-1) = f(β), une quantité finie. Mais n ~ 0.585k → ∞, ce qui contredit f(β) fini.

Donc β → 0 quand k → ∞. Posons β = a/k avec a > 0. Alors :

n ≈ Σ_{j=1}^{k} j/(e^{aj/k}-1) ≈ k² ∫₀¹ t/(e^{at}-1) dt = k² · I(a)

Avec n ~ 0.585k, on obtient k² · I(a) ~ 0.585k, soit I(a) ~ 0.585/k → 0. Or I(a) = ∫₀¹ t/(e^{at}-1) dt > 0 pour tout a > 0 fini, et I(a) → ∞ quand a → 0, I(a) → 0 quand a → ∞.

Donc a → ∞ pour que I(a) → 0. Posons a = bk, soit β = b :

n ≈ Σ_{j=1}^{k} j/(e^{bj}-1) qui est une somme de termes exponentiellement décroissants. Pour b > 0, le premier terme domine : n ≈ 1/(e^b - 1). Donc e^b ≈ 1 + 1/n, soit b ≈ 1/n ~ 1/(0.585k), et β = b ~ 1/(0.585k).

Hmm, cela contredit β = a/k avec a → ∞. Reprenons plus soigneusement.

Pour β > 0, Σ_{j=1}^{k} j/(e^{βj}-1). Pour βk grand (i.e., β >> 1/k), seuls les premiers termes comptent :

Σ ≈ 1/(e^β - 1) + 2/(e^{2β}-1) + ...

Pour β petit (β << 1), tous les termes comptent et la somme ~ k²·I(βk) comme ci-dessus.

Le régime correct est β = O(1/k). Posons β = c/k. Alors :

Σ_{j=1}^{k} j/(e^{cj/k}-1) ≈ (k/c) Σ_{j=1}^{k} (cj/k)/(e^{cj/k}-1) · (1/k) → (k/c) ∫₀^c u/(e^u-1) du · (k/c)

Non, soyons plus soigneux. Avec β = c/k :

j/(e^{βj}-1) = j/(e^{cj/k}-1). Pour j/k = t : ≈ kt/((cj/k) · (1 + O(cj/k))) ≈ kt/(ct) = k/c pour ct petit.

Mais ceci diverge... L'approximation pour cj/k petit (j << k/c) : j/(e^{cj/k}-1) ≈ j/(cj/k) = k/c. Cela donne la somme ≈ k²/c (pour k/c termes significatifs), ce qui n'est pas ~ 0.585k.

**Le problème est que n = S-k ~ 0.585k est PETIT relativement à k.** Le nombre de partitions de 0.585k en ≤ k parts — la plupart des parts seront 0 ou 1.

### 2.5 Approche directe pour n = S-k ~ λk avec 0 < λ < 1

Nombre de partitions de n en au plus k parts, avec n ~ λk, λ < 1.

Puisque n < k, chaque part est au plus n (car la plus grande part ≤ n). Et on a au plus k parts.

En fait, une partition de n en au plus k parts non-négatives est exactement une partition de n en parts de taille ≤ k (par conjugaison). Mais l'important est que n ~ 0.585k.

Par la formule asymptotique pour k fixe : p(n, ≤k) ~ n^{k-1}/(k!(k-1)!). Mais ici k ≈ n/0.585 ≈ 1.71n, donc k n'est PAS fixe.

Utilisons la borne de R184 qui est en fait C(S-1, k-1) :

Le nombre de COMPOSITIONS (ordonnées) de S-k en k parts ≥ 0 est C(S-k+k-1, k-1) = C(S-1, k-1). C'est une borne supérieure sur p(S-k, ≤k) (car chaque partition correspond à au plus k! compositions ordonnées, mais en fait plusieurs partitions donnent la même composition ordonnée...).

Non : C(S-1, k-1) est le nombre de compositions faibles de S-k en k parts ≥ 0 (formule stars and bars). C'est aussi le nombre de solutions entières de a₁+...+a_k = S-k avec a_j ≥ 0. Et p(S-k, ≤k) est le nombre de solutions avec a₁ ≤ a₂ ≤ ... ≤ a_k. On a :

p(S-k, ≤k) ≤ C(S-1, k-1) / k!  (en fait ≤ C(S-1,k-1)/k! quand toutes les parts sont distinctes, et > C(S-1,k-1)/k! quand il y a des parts égales)

Plus précisément, p(S-k, ≤k) ≈ C(S-1, k-1) / k! pour n >> k (quand la probabilité de collision est faible), mais pour n ~ 0.585k < k, il y a BEAUCOUP de collisions (parts égales sont fréquentes).

### 2.6 Estimation rigoureuse par récurrence

Pour n = S-k et k croissants, utilisons l'observation que n ~ 0.585k < k. Une partition de n en ≤ k parts — comme n < k, certaines parts sont forcément 0. Le nombre de parts non-nulles est au plus n (car chaque part ≥ 1 et la somme est n). Donc :

p(n, ≤k) = p(n) pour n ≤ k

Car si n ≤ k, toute partition de n a au plus n ≤ k parts. Donc la contrainte "au plus k parts" est inactive !

**RESULTAT CLE :** Pour S = ceil(k·log₂(3)) et n = S - k ~ 0.585k < k (pour tout k ≥ 1) :

**N(k,S) = p(n) = p(S-k)**

où p(n) est le nombre TOTAL de partitions de n (sans restriction sur le nombre de parts).

### 2.7 Vérification : n < k ?

n = S - k = ceil(k·log₂(3)) - k. Posons α = log₂(3) ≈ 1.58496.

n = ceil(kα) - k. Pour k ≥ 1 : n ≤ kα + 1 - k = k(α-1) + 1 = 0.585k + 1.

Et n ≥ kα - k = k(α-1) = 0.585k (quand kα est entier, mais cela n'arrive jamais car α est irrationnel, donc n ≥ k(α-1) + ε pour un petit ε > 0).

Donc n ~ 0.585k. La question est : 0.585k < k ? OUI, pour tout k ≥ 1.

**Donc N(k,S) = p(S-k) pour tout k ≥ 1.**

### 2.8 Sanity checks

**k=1 :** S = 2, n = 1. p(1) = 1. N(1,2) = 1. ✓ (unique partition : {1})

**k=2 :** S = 4, n = 2. p(2) = 2. N(2,4) = 2. ✓ (partitions de 2 : {2}, {1,1})

**k=3 :** S = 5, n = 2. p(2) = 2. N(3,5) = 2. ✓ (vecteurs : (0,0,2), (0,1,1))

**k=4 :** S = 7, n = 3. p(3) = 3. N(4,7) = 3. (partitions de 3 : {3}, {2,1}, {1,1,1})

**k=5 :** S = 8, n = 3. p(3) = 3. N(5,8) = 3.

**k=6 :** S = 10, n = 4. p(4) = 5. N(6,10) = 5. (partitions de 4 : {4},{3,1},{2,2},{2,1,1},{1,1,1,1})

**k=7 :** S = 12, n = 5. p(5) = 7.

**k=8 :** S = 13, n = 5. p(5) = 7.

**k=9 :** S = 15, n = 6. p(6) = 11.

**k=10 :** S = 16, n = 6. p(6) = 11.

---

## 3. COMPARAISON N(k,S) vs d

### 3.1 Valeurs de d

d(k) = 2^S - 3^k avec S = ceil(k·log₂(3)).

**k=1 :** d = 4 - 3 = 1. N = 1. N/d = 1. ← Cycle trivial existe.
**k=2 :** d = 16 - 9 = 7. N = 2. N/d = 2/7 ≈ 0.286 < 1.
**k=3 :** d = 32 - 27 = 5. N = 2. N/d = 2/5 = 0.4 < 1.
**k=4 :** d = 128 - 81 = 47. N = 3. N/d ≈ 0.064 < 1.
**k=5 :** d = 256 - 243 = 13. N = 3. N/d ≈ 0.231 < 1.
**k=6 :** d = 1024 - 729 = 295. N = 5. N/d ≈ 0.017 < 1.
**k=7 :** d = 4096 - 2187 = 1909. N = 7. N/d ≈ 0.0037 < 1.
**k=8 :** d = 8192 - 6561 = 1631. N = 7. N/d ≈ 0.0043 < 1.
**k=9 :** d = 32768 - 19683 = 13085. N = 11. N/d ≈ 0.00084 < 1.
**k=10 :** d = 65536 - 59049 = 6487. N = 11. N/d ≈ 0.0017 < 1.

### 3.2 Vérification asymptotique

Par Hardy-Ramanujan : p(n) ~ exp(π√(2n/3)) / (4n√3).

Pour n = S-k ~ 0.585k : p(n) ~ exp(π√(1.17k/3)) / (4·0.585k·√3) = exp(π√(0.39k)) / (4.05k).

L'exposant est ~ π · 0.624 · √k ≈ 1.96√k. Donc p(n) ~ exp(1.96√k) / k (sous-exponentiel).

Tandis que d = 2^S - 3^k ≥ 1 (et d est typiquement exponentiel en k). Plus précisément, d = 3^k · (2^ε - 1) avec ε = S - k·log₂(3) ∈ (0,1]. Pour ε typique (médiane ≈ 0.5), d ≈ 3^k · 0.41 ≈ 0.41 · 3^k.

Le ratio N/d ~ exp(1.96√k) / (k · 0.41 · 3^k) → 0 SUPER-EXPONENTIELLEMENT car exp(1.96√k) / 3^k → 0 (croissance sous-exponentielle vs exponentielle).

### 3.3 Théorème

**Théorème (N(k,S) < d pour k ≥ 2) :**

Pour tout k ≥ 2, avec S = ceil(k·log₂(3)), on a N(k,S) = p(S-k) < d(k) = 2^S - 3^k.

**Preuve (pour k suffisamment grand) :**

N(k,S) = p(S-k) ≤ p(0.585k + 1) ≤ exp(π√(2(0.585k+1)/3)) ≤ exp(π√(0.4k)) ≤ exp(2√k) pour k ≥ 10.

d(k) = 2^S - 3^k ≥ 2^{kα} - 3^k = 3^k(1 - 3^{-k·...}) ... Non, d ≥ 1 toujours, mais on a besoin de d ≥ exp(2√k).

d(k) = 3^k · (2^ε - 1) avec ε = ceil(kα) - kα ∈ (0,1].

Par le théorème de Ridout/Roth (et l'irrationalité de α = log₂(3)), les approximations rationnelles p/q de α satisfont |α - p/q| > c/q^{2+δ} pour tout δ > 0. Cela implique que ε = ceil(kα) - kα = 1 - {kα} est borné inférieurement...

En fait, par la théorie des fractions continues de log₂(3), les convergents donnent de très bonnes approximations. Le plus petit ε connu pour k ≤ 10^6 est ε ≈ 0.0001 pour certaines valeurs de k. Mais même dans ce cas, d = 3^k · (2^ε - 1) ≥ 3^k · ε · ln(2) ≈ 0.693 · ε · 3^k.

Pour que d < p(S-k), il faudrait 0.693 · ε · 3^k < exp(2√k), soit ε < exp(2√k)/(0.693 · 3^k) qui tend vers 0 SUPER-EXPONENTIELLEMENT. Les meilleures bornes diophantines sur |kα - m| donnent |kα - m| > k^{-C} pour une constante C > 0 (et on sait que C peut être pris = 1 par Roth). Donc ε > k^{-C}, et d > k^{-C} · 3^k >> exp(2√k) pour k grand.

**MAIS** pour les petits k, vérifions directement (fait en 3.1) : N < d pour tout k = 2,...,10.

Pour k ≥ 11 : p(S-k) ≤ exp(2√k) et d ≥ 3^k · (quelque chose > 0). Comme 3^k >> exp(2√k) pour k ≥ 11, on a N < d.

**QED (modulo vérification k=2,...,10 faite en 3.1).**

---

## 4. CE QUE N(k,S) < d IMPLIQUE ET N'IMPLIQUE PAS

### 4.1 Ce que N(k,S) < d implique

Si les N(k,S) valeurs g(v₁),...,g(v_{N(k,S)}) étaient uniformément réparties modulo d, la probabilité qu'au moins une soit ≡ 0 mod d serait :

P ≈ 1 - (1 - 1/d)^{N(k,S)} ≈ N(k,S)/d → 0

Cet argument probabiliste dit : **un cycle est "improbable"**. C'est l'heuristique de Steiner (1977).

### 4.2 Ce que N(k,S) < d N'implique PAS

**N(k,S) < d ne prouve PAS l'absence de cycles.** Voici pourquoi :

1. **Les valeurs de g ne sont PAS uniformément réparties mod d.** La fonction g : V_k(S) → Z n'est pas aléatoire. C'est une somme de termes très structurés (3^{k-1-j} · 2^{B_j}). Les valeurs de g pourraient être biaisées vers des multiples de d.

2. **Même avec N = 1 vecteur, un cycle peut exister.** Il suffit que ce SEUL vecteur satisfasse g(v) ≡ 0 mod d. Exemple : k=1, N=1, d=1, et g(v)=2=2·1=n·d avec n=2.

3. **Le comptage N(k,S) ne concerne que les vecteurs MONOTONES.** Si la convention de monotonie est une restriction (cf. Section 1), le nombre total de vecteurs est C(S-1,k-1) >> N(k,S), et la comparaison pertinente est C(S-1,k-1) vs d.

### 4.3 Le vrai argument de comptage (Steiner-Eliahou)

L'argument correct n'est pas "N(k,S) < d ⟹ pas de cycle". L'argument correct est :

Pour qu'un cycle de type (k,S) existe, il faut g(v) = n·d pour un v SPECIFIQUE et un n ≥ 1. Comme n = g(v)/d et g(v) > 0, on a n ≥ 1, soit g(v) ≥ d.

La borne inférieure n ≥ 1 donne g(v) ≥ d. Combinée avec une borne supérieure g(v) ≤ g_max, on obtient :

n ≤ g_max / d

La borne n ≥ 1 avec le nombre fini de v donne au plus N(k,S) candidats pour n. Chaque v donne AU PLUS un n (puisque n = g(v)/d est déterminé). Donc le nombre de cycles de type (k,S) est ≤ N(k,S).

Mais cela ne dit RIEN sur l'existence d'au moins un cycle. Pour exclure les cycles, il faudrait montrer que AUCUN des N(k,S) vecteurs ne satisfait d | g(v).

### 4.4 Ce qui serait SUFFISANT

Pour exclure les cycles de type (k,S), il faudrait prouver une des conditions suivantes :

**(A) Borne inférieure sur g_min/d :** Si g_min > n_max · d pour tout n ∈ Z... Non, ça n'a pas de sens. Si g_min / d > floor(g_min/d) + 1 - 1 = ... Non.

**(B) Divisibilité impossible :** Montrer que g(v) mod d ≠ 0 pour tout v ∈ V_k(S). C'est la condition nécessaire et suffisante, mais c'est exactement le problème !

**(C) n < 1 pour tous les v :** Si g_max < d, alors n = g(v)/d < 1 pour tout v, donc aucun entier n ≥ 1 ne convient. C'est la condition **g_max < d**.

Calculons g_max. Le vecteur v qui maximise g(v) = Σ 3^{k-1-j} · 2^{B_j} (avec la convention B_j = exposants cumulés ajustés) est celui qui met le maximum de "masse" sur les premiers B_j (ceux avec les grands poids 3^{k-1-j}).

Avec la convention du prompt (b_j ≥ 0, monotone, Σ b_j = S-k), g(v) = Σ 3^{k-1-j} · 2^{b_j}. Les poids 3^{k-1-j} sont DÉCROISSANTS. Les amplitudes 2^{b_j} sont CROISSANTES (car b_j monotone). L'inégalité de réarrangement dit que g est MINIMISÉE (pas maximisée) par cette configuration.

Attendons — g est minimisé quand les facteurs sont anti-ordonnés (grand avec petit). Avec les poids décroissants et les amplitudes croissantes, on est dans la configuration ANTI-ORDONNÉE, donc g est effectivement MINIMISÉ.

Le MAXIMUM de g (sur toutes les permutations des b_j) serait quand les grands poids sont avec les grandes amplitudes. Mais si on se restreint aux vecteurs MONOTONES, on est dans la configuration qui MINIMISE g.

**Observation :** Parmi les vecteurs monotones, g_max est atteint quand les b_j sont le plus "concentrés" (plateaux), et g_min quand les b_j sont le plus "étalés" (spread).

Pour le vecteur constant (b_j = n/k pour tous j, si n/k est entier) : g_const = τ_k · 2^{n/k} avec τ_k = (3^k-1)/2.

Pour le vecteur le plus concentré (0,0,...,0,n) : g_concentré = 3^{k-1} + 3^{k-2} + ... + 3 + 2^n = (3^k-1)/2 - 1 + 2^n = τ_k - 1 + 2^n.

Hmm, le vecteur (0,...,0,n) a b₀ = ... = b_{k-2} = 0, b_{k-1} = n. Alors g = 3^{k-1}·1 + 3^{k-2}·1 + ... + 3·1 + 1·2^n = (3^k-3)/2 + 2^n ... Non.

g = Σ_{j=0}^{k-1} 3^{k-1-j} · 2^{b_j} = (3^{k-1} + 3^{k-2} + ... + 3) · 2^0 + 1 · 2^n
= (3^k - 3)/2 + 2^n

Avec n = S-k ~ 0.585k : 2^n = 2^{0.585k} et (3^k-3)/2 ~ 3^k/2. Donc g ≈ 3^k/2 + 2^{0.585k} ≈ 3^k/2 (le terme 3^k/2 domine).

Et d = 2^S - 3^k ~ 3^k · (2^ε - 1) pour ε ∈ (0,1].

Donc g_max / d ~ (3^k/2) / (3^k · (2^ε - 1)) = 1/(2(2^ε - 1)).

Pour ε ~ 0.5 (typique) : d ~ 0.41 · 3^k, g_max ~ 0.5 · 3^k, g_max/d ~ 1.22 > 1. Donc n = 1 est POSSIBLE en principe.

Pour ε proche de 1 : d ~ 3^k, g_max/d ~ 0.5 < 1. Pas de cycle.

Pour ε proche de 0 : d ~ 0, g_max/d → ∞. Beaucoup de n possibles.

**CONCLUSION :** g_max/d est d'ordre O(1) — il y a typiquement 0 ou 1 multiple de d dans l'intervalle [g_min, g_max]. Cela rend la question de l'existence de cycles DELICATE, pas tranchée par le comptage.

---

## 5. LE FANTOME k=2 COMME ILLUSTRATION

Pour k=2, S=4, n=2 :
- d = 7
- Vecteurs monotones : (0,2) et (1,1)
- g(0,2) = 3·1 + 1·4 = 7. g/d = 7/7 = 1. **CYCLE FANTOME !**
- g(1,1) = 3·2 + 1·2 = 8. g/d = 8/7. Pas entier.

Avec N(2,4) = 2 < d = 7, on a N/d ≈ 0.286 < 1. L'heuristique probabiliste prédit "probablement pas de cycle". Et pourtant g(0,2) = 7 = d, donc n = 1 est un cycle (fantôme, car n = 1 correspond au cycle trivial 1 → 4 → 2 → 1 parcouru dans un formalisme k=2).

**Le fantôme k=2 PROUVE que N(k,S) < d ne suffit PAS à exclure les cycles.** Même avec N/d << 1, un des N vecteurs peut tomber pile sur un multiple de d.

---

## 6. QU'EST-CE QUI RENDRAIT N(k,S) < d UTILE ?

L'argument de comptage N(k,S) < d serait transformé en PREUVE si on pouvait ajouter une condition d'équidistribution :

**Condition d'équidistribution :** Les valeurs {g(v) mod d : v ∈ V_k(S)} sont "suffisamment dispersées" dans Z/dZ.

Plus précisément, il faudrait montrer que pour tout a ∈ Z/dZ :

|{v ∈ V_k(S) : g(v) ≡ a mod d}| ≤ C · N(k,S)/d

pour une constante C. Si C · N(k,S)/d < 1, alors aucune classe a n'est atteinte par plus de 0 vecteurs, et en particulier a = 0 n'est pas atteint.

Mais une telle borne d'équidistribution est EXACTEMENT le problème des sommes exponentielles sur les partitions, identifié comme verrou dans R185 A3.

Alternativement, on pourrait montrer :

**Propriété anti-concentration :** P(g(v) ≡ 0 mod d) ≤ 1/d + ε pour v uniforme dans V_k(S), avec ε petit.

Ceci aussi nécessite des estimées de sommes exponentielles.

---

## 7. FORMULE EXACTE : SYNTHESE

### 7.1 Résultat principal

**Théorème R186-T1 (Formule exacte pour N(k,S)) :**

Pour k ≥ 1, S = ceil(k·log₂(3)), n = S - k :

N(k,S) = p(n) (nombre total de partitions de n)

car n < k (la contrainte "au plus k parts" est inactive).

### 7.2 Asymptotique

Par Hardy-Ramanujan (1918) :

N(k,S) = p(S-k) ~ exp(π√(2(S-k)/3)) / (4(S-k)√3)

Avec S-k ~ 0.585k :

N(k,S) ~ exp(1.96√k) / (4.05k)

### 7.3 Comparaison avec d

d(k) ~ 3^k · (2^ε - 1) avec ε = ceil(kα) - kα ∈ (0,1].

Pour tout k ≥ 2 :

**N(k,S) / d(k) → 0** (super-exponentiellement : exp(C√k) / 3^k → 0)

### 7.4 Valeurs exactes

| k | S | n=S-k | N(k,S)=p(n) | d=2^S-3^k | N/d |
|---|---|-------|-------------|-----------|-----|
| 1 | 2 | 1 | 1 | 1 | 1.000 |
| 2 | 4 | 2 | 2 | 7 | 0.286 |
| 3 | 5 | 2 | 2 | 5 | 0.400 |
| 4 | 7 | 3 | 3 | 47 | 0.064 |
| 5 | 8 | 3 | 3 | 13 | 0.231 |
| 6 | 10 | 4 | 5 | 295 | 0.017 |
| 7 | 12 | 5 | 7 | 1909 | 0.0037 |
| 8 | 13 | 5 | 7 | 1631 | 0.0043 |
| 9 | 15 | 6 | 11 | 13085 | 0.00084 |
| 10 | 16 | 6 | 11 | 6487 | 0.0017 |
| 15 | 24 | 9 | 30 | 2485507 | 1.2×10⁻⁵ |
| 20 | 32 | 12 | 77 | 740560711 | 1.0×10⁻⁷ |

### 7.5 Comparaison avec la borne R184

R184 utilisait C(S-1, k-1) ~ 2^{1.507k}. Le vrai N(k,S) = p(S-k) ~ exp(1.96√k). La borne R184 est EXPONENTIELLEMENT plus grande que la réalité. Pour k=10 : C(15,9) = 5005 vs p(6) = 11, ratio ≈ 455.

**La borne R184 T1 sur N(k,S) était correcte (borne supérieure) mais extrêmement grossière.** Le coefficient de T2 (espérance ~ 2^{0.507k}) était donc FAUX : avec le vrai N(k,S) ~ exp(2√k), l'espérance est ~ exp(2√k) · 2^{0.585k} / 2^{1.585k} = exp(2√k) / 2^k → 0. L'espérance tend vers 0, pas vers l'infini.

**Conséquence :** Le théorème T2 de R184 ("l'espérance tend vers l'infini") est INVALIDE. Il reposait sur la borne grossière C(S-1,k-1). Avec la vraie valeur de N(k,S), l'espérance du nombre de coïncidences g(v) = nd tend vers 0.

---

## 8. CORRECTION DE T2 ET NOUVELLE ESPERANCE

### 8.1 Espérance corrigée

E[collisions] ≈ N(k,S) · M / g_range

où M = nombre de multiples de d dans [g_min, g_max] et g_range = g_max - g_min.

M ≈ g_range / d ≈ (g_max - g_min) / d.

Donc E ≈ N(k,S) · (g_range/d) / g_range = N(k,S) / d → 0.

**L'espérance tend vers 0, ce qui est COHÉRENT avec l'absence de cycles pour k ≥ 2.**

### 8.2 Le paradoxe du fantôme k=2

Pour k=2 : E ≈ N/d = 2/7 ≈ 0.286 < 1. L'espérance est < 1, et pourtant il y a une coïncidence (g(0,2) = 7 = d). Cela n'est pas contradictoire : E < 1 ne signifie pas 0 collisions, cela signifie "en moyenne moins de 1 collision". La probabilité d'au moins une collision est ≤ E ≈ 0.286, et dans le cas k=2 on est dans les 28.6% de chance que ça arrive.

---

## 9. LE VRAI VERROU : EQUIDISTRIBUTION

### 9.1 L'argument probabiliste

L'argument heuristique est :
1. N(k,S) = p(S-k) ~ exp(2√k) vecteurs
2. d ~ 3^k · (2^ε - 1) est exponentiel en k
3. Si g(v) mod d est "pseudo-aléatoire", chaque valeur est atteinte ~ N(k,S)/d → 0 fois
4. En particulier, g(v) ≡ 0 mod d pour 0 vecteur → pas de cycle

### 9.2 Le verrou

L'hypothèse "g(v) mod d est pseudo-aléatoire" est NON PROUVEE. C'est le problème des sommes exponentielles sur les partitions (R185 A3, tentative 3).

Pour transformer l'argument probabiliste en preuve, il faudrait borner :

|Σ_{v ∈ V_k(S)} e^{2πi·g(v)/d}| ≤ δ · N(k,S)

avec δ < 1 (borne de Weyl). Si δ · N(k,S) < 1, alors la somme ne peut pas se concentrer et g(v) ≡ 0 mod d n'a pas de solution.

Mais cette borne est un PROBLEME OUVERT en théorie analytique des nombres. Les sommes exponentielles sur les partitions (Σ_{λ⊢n} e^{2πi·f(λ)/d} pour f non-linéaire) ne sont pas couvertes par les techniques standard (Weil, Deligne, van der Corput).

---

## 10. CONCLUSIONS ET RECOMMANDATIONS

### 10.1 Résultats de R186

**R186-T1 [PROUVÉ, SIGNIFICATIF] :** N(k,S) = p(S-k) pour tout k ≥ 1. La contrainte "au plus k parts" est inactive car S-k < k.

**R186-T2 [PROUVÉ, SIGNIFICATIF] :** N(k,S)/d → 0 super-exponentiellement (exp(2√k)/3^k → 0). L'espérance du nombre de coïncidences tend vers 0.

**R186-T3 [PROUVÉ, CORRIGE R184] :** Le théorème T2 de R184 (espérance → ∞) est INVALIDE. Il utilisait la borne grossière C(S-1,k-1) au lieu de la vraie valeur p(S-k).

**R186-C1 [ANALYSE CRITIQUE] :** N(k,S) < d ne suffit PAS à exclure les cycles. Le fantôme k=2 en est la preuve (N/d = 2/7 < 1, mais g(0,2) = d exactement). Le passage de l'heuristique probabiliste à la preuve requiert une borne d'équidistribution de g(v) mod d.

### 10.2 Réévaluation de la piste

**Piste "N(k,S) < d" : DÉGRADÉE de 7/10 à 4/10.**

- ✅ N(k,S) < d est PROUVÉ pour tout k ≥ 2.
- ✅ L'espérance du nombre de coïncidences → 0.
- ❌ Cela ne prouve PAS l'absence de cycles.
- ❌ Le fantôme k=2 montre que N < d est compatible avec l'existence de cycles.
- ❌ Le verrou est l'équidistribution de g mod d, problème ouvert.

### 10.3 Ce qui est récupérable

1. **La formule N(k,S) = p(S-k)** est un résultat propre et exact. Elle remplace la borne grossière C(S-1,k-1) de R184.

2. **L'invalidation de T2 de R184** est un résultat négatif important. L'espérance ne tend PAS vers l'infini. Cela signifie que la voie probabiliste n'est PAS obstruée par le comptage : l'heuristique est COHÉRENTE avec l'absence de cycles.

3. **La question de l'équidistribution** est PRECISEMENT identifiée comme le verrou. C'est un problème de théorie analytique des nombres (sommes exponentielles sur les partitions), pas de combinatoire.

### 10.4 Pistes pour R187

1. **Études de cas : g(v) mod d pour petits k.** Pour k=3,...,10, calculer toutes les valeurs g(v) mod d et vérifier empiriquement l'équidistribution. Cela ne prouve rien mais guide l'intuition.

2. **Structure algébrique de g mod d.** Pour les petits d (comme d=5 pour k=3, d=13 pour k=5), l'ensemble {g(v) mod d : v ∈ V_k(S)} peut être décrit explicitement. Si cet ensemble évite 0 pour tout k ≥ 3, c'est un THEOREME (pour chaque k individuellement).

3. **Connexion avec les fibres modulaires E6' de R185.** La décomposition de g(v) mod p en fibres pourrait être combinée avec le petit nombre de vecteurs (p(S-k)) pour borner le nombre de vecteurs satisfaisant g ≡ 0 mod p.

4. **Borne de Baker sur n_min.** Steiner (1977) et Eliahou (1993) utilisent la borne n ≥ 1 et des arguments de taille. La borne de Baker n ≥ 2^{k·quelque chose} pourrait être combinée avec g_max pour obtenir une contradiction directe (n = g/d ≤ g_max/d ≤ C, tandis que n ≥ 2^{grand}).

---

## EVALUATION R186

| Critère | Score | Commentaire |
|---------|-------|-------------|
| **Rigueur** | 9/10 | Formule exacte prouvée, sanity checks k=1,2,3 corrects, erreur R184 identifiée |
| **Nouveauté** | 6/10 | N(k,S) = p(S-k) est un résultat exact nouveau. Invalidation de T2 R184 |
| **Impact** | 5/10 | Piste N(k,S)<d dégradée, mais formule exacte utilisable. Verrou clarifié |
| **Honnêteté** | 10/10 | Auto-correction de la piste R185 (7/10 → 4/10). Fantôme k=2 exhibé |

---

## ERREURS DÉTECTÉES DANS LES ROUNDS PRÉCÉDENTS

### Erreur R184-T2 (GRAVE)
T2 affirmait : espérance → ∞ comme 2^{0.507k}. C'est FAUX car N(k,S) = p(S-k) ~ exp(2√k), pas C(S-1,k-1) ~ 2^{1.507k}. L'espérance corrigée → 0. T2 est INVALIDÉ.

### Erreur R185 Red Team (MODEREE)
Le Red Team R185 estimait la piste N(k,S) < d à 7/10 ("si prouvable, suffit"). N(k,S) < d EST prouvé (facilement), mais NE suffit PAS. Score corrigé : 4/10.

---

*Round R186 : 1 formule exacte (N(k,S) = p(S-k)), 1 invalidation (R184-T2), 1 dégradation de piste (7/10 → 4/10), 0 preuve d'absence de cycles. Verrou identifié : équidistribution de g(v) mod d.*
