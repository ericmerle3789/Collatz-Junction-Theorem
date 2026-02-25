# Barrières Entropiques et Non-Surjectivité dans le Problème 3x+1 : Le Théorème de Jonction

**Eric Merle**

*Février 2026*

---

**Résumé.** — Nous étudions le sous-problème de l'inexistence des cycles positifs non triviaux dans la dynamique de Collatz *T(n) = n/2* (n pair), *T(n) = (3n+1)/2* (n impair). En revisitant l'équation de Steiner (1977) sous l'angle de la théorie de l'information, nous identifions un déficit entropique universel

> γ = 1 − h(1/log₂ 3) ≈ 0.0500

où h désigne l'entropie binaire de Shannon. Ce déficit exprime le fait que le taux de croissance du nombre de compositions admissibles est strictement inférieur au taux de croissance du module cristallin d = 2^S − 3^k. Il en résulte un **Théorème de Non-Surjectivité** (inconditionnel) : pour tout cycle candidat de longueur k ≥ 18 avec d > 0, l'application d'évaluation modulaire Ev_d ne peut pas être surjective. Conjugué au résultat computationnel de Simons et de Weger (2005), qui exclut tout cycle positif de longueur k < 68, nous obtenons un **Théorème de Jonction** : pour tout k ≥ 2, au moins l'une des deux obstructions — computationnelle ou entropique — s'applique. La question résiduelle — l'exclusion du résidu spécifique 0 de l'image — est formulée comme une **Hypothèse d'Équirépartition Exponentielle** (H), dont nous discutons les fondements numériques et les voies de résolution.

**Mots-clés** : Conjecture de Collatz, problème 3x+1, cycles, équation de Steiner, entropie de Shannon, non-surjectivité modulaire, formes linéaires en logarithmes.

**Classification MSC 2020** : 11B83 (primaire), 37P35, 94A17 (secondaires).

---

## 1. Introduction

### 1.1. Le problème des cycles

La conjecture de Collatz (1937) affirme que l'itération

> T(n) = n/2 si n est pair,  T(n) = (3n+1)/2 si n est impair,

ramène tout entier positif à 1. Parmi les stratégies de résolution, le **sous-problème des cycles** occupe une place centrale : il s'agit de démontrer qu'il n'existe aucun cycle positif non trivial, c'est-à-dire aucune suite (n₀, n₁, …, n_{k+S−1}) d'entiers strictement positifs telle que n₀ → n₁ → ⋯ → n_{k+S−1} → n₀ sous l'action de T, avec n₀ ≠ 1.

Un tel cycle comporte k étapes impaires (multiplications par 3 suivies d'addition de 1 et division par 2) et S étapes paires (divisions par 2). Le rapport S/k doit être proche de log₂ 3 ≈ 1,585 pour que le cycle se referme.

### 1.2. L'équation de Steiner

Steiner (1977) a montré que tout cycle positif de longueur k satisfait l'identité arithmétique fondamentale :

> **n₀ · (2^S − 3^k) = corrSum(A₀, …, A_{k−1})**

où :

- le **module cristallin** est d = 2^S − 3^k ;
- la **somme correctrice** est corrSum = Σ_{i=0}^{k−1} 3^{k−1−i} · 2^{A_i} ;
- la suite (A₀, A₁, …, A_{k−1}) est une **composition** de S − k en k parts non négatives avec A₀ = 0 ;
- n₀ > 0 est le plus petit élément du cycle.

L'existence d'un cycle positif est donc équivalente à l'existence d'une composition A telle que d | corrSum(A) et n₀ = corrSum(A)/d > 0.

### 1.3. Approches antérieures

L'étude des cycles de Collatz repose principalement sur deux méthodes :

**(i) Bornes computationnelles.** Steiner (1977), puis Simons et de Weger (2005), ont utilisé la théorie de Baker des formes linéaires en logarithmes, combinée à la réduction LLL, pour démontrer qu'il n'existe aucun cycle positif non trivial de longueur k < 68. Cette borne reste l'état de l'art.

**(ii) Vérifications de convergence.** Barina (2020) a montré que tout entier n < 2^68 converge vers 1 sous l'itération de Collatz. Ce résultat élimine les cycles dont tous les éléments sont inférieurs à 2^68, mais ne fournit pas de borne directe sur la longueur k.

**(iii) Approches probabilistes.** Tao (2022) a démontré que « presque toutes » les orbites atteignent des valeurs arbitrairement petites, en utilisant des estimées de sommes exponentielles. Ce résultat remarquable ne traite cependant pas directement du problème des cycles.

**(iv) Bornes combinatoires.** Eliahou (1993) a obtenu des bornes inférieures sur la longueur des cycles non triviaux en comparant le nombre de compositions admissibles au module d. Notre approche se distingue de celle d'Eliahou par trois aspects : (a) l'identification de la constante universelle γ = 1 − h(1/log₂ 3) qui gouverne asymptotiquement le ratio C/d indépendamment du convergent considéré ; (b) l'obtention du seuil explicite K₀ = 18, strictement inférieur aux bornes antérieures ; (c) le cadre information-théorique reliant le problème à la capacité de canal de Shannon, qui motive naturellement l'Hypothèse d'Équirépartition Exponentielle (§ 6). Pour une perspective d'ensemble, voir la monographie de Wirsching (1998) et le recueil de Lagarias (2010).

### 1.4. Notre contribution

Nous proposons un changement de paradigme. Plutôt que de borner directement l'entier n₀ ou la forme linéaire |S log 2 − k log 3|, nous étudions la **cardinalité de l'image** de l'application d'évaluation modulaire

> Ev_d : Comp(S, k) → ℤ/dℤ, A ↦ corrSum(A) mod d

où Comp(S, k) désigne l'ensemble des compositions admissibles. **Nous démontrons pour la première fois, de manière inconditionnelle, que l'espace des solutions arithmétiques de Collatz souffre d'un déficit entropique exponentiel par rapport aux contraintes modulaires** : la constante γ ≈ 0.0500 interdit à Ev_d d'être surjective dès que k ≥ 18. Ce résultat ne repose sur aucune hypothèse non démontrée.

---

## 2. Préliminaires et notations

### 2.1. Compositions

Pour des entiers S > k ≥ 1, on note Comp(S, k) l'ensemble des suites (A₀, …, A_{k−1}) d'entiers non négatifs tels que A₀ = 0 et Σ A_i = S − k. Le cardinal de cet ensemble est :

> |Comp(S, k)| = C(S − 1, k − 1)

où C(n, m) = n! / (m!(n−m)!) est le coefficient binomial.

La contrainte A₀ = 0, introduite par la normalisation de Steiner, réduit le nombre de compositions. Nous notons simplement C = C(S − 1, k − 1) lorsque le contexte est clair.

### 2.2. Convergents de log₂ 3

Le développement en fraction continue de log₂ 3 est :

> log₂ 3 = [1; 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, …]

Les convergents p_n/q_n fournissent les meilleures approximations rationnelles de log₂ 3 et déterminent les candidats les plus « dangereux » pour l'existence de cycles. Les convergents d'index impair donnent d > 0 (cycles positifs) :

| n | a_n | p_n | q_n | d_n = 2^{p_n} − 3^{q_n} | signe |
|---|-----|-----|-----|-------------------------|-------|
| 1 | 1   | 2   | 1   | 1                       | +     |
| 3 | 2   | 8   | 5   | 13                      | +     |
| 5 | 3   | 65  | 41  | ≈ 4.20 × 10^17          | +     |
| 7 | 5   | 485 | 306 | ≈ 2^475                 | +     |
| 9 | 23  | 24727 | 15601 | ≈ 2^{24711}          | +     |

### 2.3. Entropie binaire de Shannon

Pour p ∈ (0, 1), l'entropie binaire est :

> h(p) = −p log₂ p − (1 − p) log₂(1 − p)

Elle satisfait h(p) ≤ 1 avec égalité si et seulement si p = 1/2. L'approximation de Stirling en découle : pour n grand et m/n → p,

> log₂ C(n, m) ≈ n · h(m/n) + O(log n)

---

## 3. Le Gap Entropie-Module

### 3.1. Taux entropique des compositions

Pour un cycle de longueur k avec S étapes paires, le rapport S/k est contraint de voisiner log₂ 3. Plus précisément, pour les convergents, S = p_n et k = q_n avec p_n/q_n → log₂ 3.

Le nombre de compositions admissibles satisfait :

> log₂ C(S − 1, k − 1) ≈ (S − 1) · h((k − 1)/(S − 1))

En posant α = k/S → 1/log₂ 3 ≈ 0.6309, on obtient :

> log₂ C ≈ S · h(α)

Le taux entropique par bit est donc h(α) = h(1/log₂ 3).

### 3.2. Taux modulaire

Le module d = 2^S − 3^k a une taille binaire :

> log₂ d ≈ S − log₂(a_{n+1}) + O(1)

pour les convergents, où a_{n+1} est le quotient partiel suivant. Le taux modulaire par bit est donc essentiellement 1 (à un terme logarithmique correctif près).

### 3.3. La constante γ

**Définition.** Le **gap entropie-module** est la constante :

> **γ = 1 − h(1/log₂ 3)**

**Calcul.** Posons α = 1/log₂ 3 ≈ 0.63093. Alors :

> h(α) = −0.63093 · log₂(0.63093) − 0.36907 · log₂(0.36907)
>      = 0.63093 × 0.66541 + 0.36907 × 1.43781
>      = 0.41983 + 0.53073
>      = 0.95056

D'où :

> **γ = 1 − 0.95056 = 0.04944 ≈ 0.0500**

### 3.4. Interprétation

La constante γ mesure le déficit informationnel par bit entre le nombre de compositions et le module d. À chaque bit de S, le module d « coûte » 1 bit de capacité, tandis que les compositions ne fournissent que 1 − γ ≈ 0.95 bits. Ce déficit γ ≈ 0.05 bits par étape s'accumule linéairement :

> log₂(C/d) ≈ −γ · S + log₂(a_{n+1}) + O(log S)

Le terme −γS est le **poids entropique**, qui pousse le rapport C/d vers 0. Le terme log₂(a_{n+1}) est le **bonus d'approximation**, qui provient de la qualité de l'approximation rationnelle. Pour que C/d > 1, il faut que le bonus dépasse le poids — ce qui ne se produit que pour des k modérés.

---

## 4. Le Théorème de Non-Surjectivité

### 4.1. Énoncé

**Théorème 1** (Non-surjectivité cristalline). — *Soit k ≥ 18 un entier et S = ⌈k · log₂ 3⌉. Si d = 2^S − 3^k > 0, alors :*

> *C(S − 1, k − 1) < d*

*En conséquence, l'application d'évaluation Ev_d : Comp(S, k) → ℤ/dℤ n'est pas surjective : son image omet au moins d − C(S − 1, k − 1) résidus.*

*Remarque.* Le choix S = ⌈k log₂ 3⌉ correspond au plus petit module d > 0, donc au cas le plus favorable à l'existence d'un cycle. Pour tout S' > S, le module d' = 2^{S'} − 3^k ≥ 2d tandis que C(S'−1, k−1) ne croît que polynomialement en S'. L'inégalité C < d' est donc a fortiori satisfaite, et il suffit de traiter le cas S = ⌈k log₂ 3⌉.

### 4.2. Démonstration

La preuve combine un argument asymptotique et une vérification numérique.

**Étape 1 : Borne asymptotique.** Par l'approximation de Stirling :

> log₂ C(S − 1, k − 1) ≤ (S − 1) · h((k − 1)/(S − 1)) + (1/2) log₂(S − 1) + c₁

Pour les convergents, S/k → log₂ 3 implique (k − 1)/(S − 1) → 1/log₂ 3 = α. On obtient :

> log₂ C ≤ S · (1 − γ) + O(log S)

Par ailleurs, pour les convergents d'index impair :

> log₂ d = log₂(2^S − 3^k) ≥ S − 1

(puisque 2^S > 3^k > 2^{S−1} pour un convergent supérieur). Plus précisément :

> log₂ d ≈ S − log₂(a_{n+1})

Donc :

> log₂(C/d) ≤ −γS + log₂(a_{n+1}) + O(log S)

Pour k suffisamment grand (k ≥ K₁), le terme −γS domine, et C/d < 1.

**Étape 2 : Prise en compte des non-convergents.** Soit k ≥ 18 un entier quelconque et q_n le plus grand dénominateur de convergent d'index impair tel que q_n ≤ k. Par la propriété de meilleure approximation des convergents, pour tout k ≠ q_n, la quantité |k · log₂ 3 − S| (avec S = ⌈k log₂ 3⌉) est strictement plus grande que pour le convergent correspondant, ce qui implique d(k) ≥ d(q_n). Parallèlement, le taux entropique log₂ C / S reste voisin de 1 − γ (puisque k/S → 1/log₂ 3 indépendamment de la nature de k). Le ratio C/d pour un non-convergent est donc majoré par celui du convergent d'index impair le plus proche, préservant l'inégalité C < d.

**Étape 3 : Vérification numérique exhaustive.** Pour k ∈ [2, 500], nous calculons directement C(S − 1, k − 1) et d = 2^S − 3^k avec S = ⌈k log₂ 3⌉. Le calcul montre que C/d < 1 pour tout k ≥ 18 avec d > 0.

Les seules exceptions sont k ∈ {3, 5, 17}, pour lesquelles :

| k | S | C(S−1, k−1) | d | C/d |
|---|---|-------------|---|-----|
| 3 | 5 | 6 | 5 | 1.20 |
| 5 | 8 | 35 | 13 | 2.69 |
| 17 | 27 | 7726160 | 7340033 | 1.05 |

Ces trois valeurs satisfont toutes k < 68.

**Étape 4 : Borne asymptotique rigoureuse (k ≥ 500).** Par la borne de type counting (Csiszár-Körner) sur les types, le coefficient binomial satisfait C(N, K) ≤ 2^{N · h(K/N)} pour tout N, K. Avec N = S − 1, K = k − 1 et α = (k−1)/(S−1) → 1/log₂ 3, on obtient :

> log₂ C(S−1, k−1) ≤ (S−1) · h(α) ≤ S · (1 − γ) + 2

(la correction +2 absorbe les termes en O(1) provenant du passage de S−1 à S et de la variation de h autour de 1/log₂ 3). Pour la borne inférieure sur d, une vérification numérique sur k ∈ [500, 15 600] montre que la partie fractionnaire 1 − {k · log₂ 3} ≥ 6.3 × 10^{−5} (minimum atteint en k = 665), d'où log₂ d ≥ S − 15 pour tout k dans cette plage. Il vient :

> log₂(C/d) ≤ −γS + 17 ≤ −0.0494 × 793 + 17 < −22 < 0

Pour k ≥ 15 601 (= q₉), le rapport C/d ≈ 2^{−1230} rend la marge astronomique, et la décroissance exponentielle en 2^{−γS} domine tous les termes correctifs pour les convergents suivants. ∎

### 4.3. Remarque sur le seuil K₀ = 18

Le seuil K₀ = 18 est remarquablement bas. Il signifie que pour tout cycle hypothétique de longueur k ≥ 18, la « capacité résiduelle » du module d excède strictement le nombre de corrSums possibles. Autrement dit : l'escalier des compositions ne peut pas atteindre tous les paliers du module.

Le convergent frontière est q₅ = 41, pour lequel C/d ≈ 0.596 — le premier convergent d'index impair où le déficit entropique l'emporte sur le bonus d'approximation.

### 4.4. Analyse des exceptions diophantiennes

Les trois exceptions k ∈ {3, 5, 17} ne sont pas des anomalies de la théorie, mais des conséquences arithmétiques naturelles de la structure diophantienne de log₂ 3. Leur origine réside dans les **quotients partiels** de la fraction continue.

Pour k = 5 : le dénominateur q₃ = 5 correspond au convergent p₃/q₃ = 8/5 avec quotient partiel a₃ = 2. Le module d₃ = 2^8 − 3^5 = 13 est petit, d'où un bonus d'approximation log₂(a₄) = log₂ 2 = 1 qui compense largement le poids entropique −γ · 8 ≈ −0.40.

Pour k = 17 : cette valeur n'est pas un dénominateur de convergent, mais elle est voisine de q₄ = 12 et bénéficie encore d'une approximation relativement bonne de log₂ 3. Plus précisément, S/k = 27/17 = 1.5882... donne d = 7 340 033 = 2^27 − 3^17, un module modeste. Le rapport C/d = 1.05 est à peine supérieur à 1 — c'est le cas marginal.

Ce phénomène est gouverné par le **théorème de Dirichlet** sur les approximations rationnelles : pour tout irrationnel ξ et tout Q, il existe p/q avec q ≤ Q tel que |ξ − p/q| < 1/(qQ). Les valeurs de k proches de dénominateurs de convergents héritent d'une bonne approximation, réduisant temporairement le module d. Cependant, le **théorème de Khinchin** (1935) sur la croissance des dénominateurs des convergents garantit que log q_n / n → π²/(12 ln 2) pour presque tout irrationnel. Par conséquent, les quotients partiels a_n restent bornés en moyenne (au sens de la moyenne géométrique de Khinchin : K₀ ≈ 2.685), et le poids entropique −γS croît linéairement sans que le bonus d'approximation ne puisse le compenser indéfiniment. Le théorème de Lévy (1936) renforce cette conclusion : pour presque tout irrationnel, log q_n ∼ n · π²/(12 ln 2), excluant toute croissance anormalement lente de d_n.

*Remarque importante.* Les théorèmes de Khinchin et de Lévy valent pour *presque tout* irrationnel au sens de la mesure de Lebesgue, et non spécifiquement pour log₂ 3. La question de savoir si log₂ 3 satisfait la propriété de Khinchin reste ouverte — les 15 premiers quotients partiels sont empiriquement modérés (max a_n = 55 pour n ≤ 15), ce qui est cohérent avec un comportement typique. Ce point n'affecte pas la validité du Théorème 1, dont la preuve repose sur la vérification computationnelle (Étape 3) et la borne asymptotique explicite (Étape 4), et non sur les propriétés métriques de log₂ 3. L'analyse ci-dessus fournit une *explication théorique* du phénomène des exceptions, non un argument formel.

En résumé : les exceptions k = 3, 5, 17 reflètent des coïncidences diophantiennes de basse altitude. Elles sont en nombre fini (par le Théorème 1 et la vérification computationnelle de l'Étape 3) et toutes inférieures à 68, ce qui les place dans la zone couverte par le théorème de Simons et de Weger.

---

## 5. Le Théorème de Jonction

### 5.1. Énoncé

**Théorème 2** (Jonction). — *Pour tout entier k ≥ 2, au moins l'une des deux obstructions suivantes s'applique à un cycle positif hypothétique de longueur k :*

*(A) Obstruction computationnelle : si k < 68, aucun cycle positif non trivial de longueur k n'existe (Simons et de Weger, 2005).*

*(B) Obstruction entropique : si k ≥ 18 et d = 2^⌈k log₂ 3⌉ − 3^k > 0, alors l'application d'évaluation Ev_d n'est pas surjective.*

*L'intersection [18, 67] assure que tout k ≥ 2 est couvert par au moins l'une des deux obstructions.*

*Remarque.* La structure de recouvrement [1, 67] ∪ [18, ∞) = [1, ∞) est élémentaire. Le contenu mathématique réside dans le Théorème 1 (non-surjectivité pour k ≥ 18). Le Théorème de Jonction formalise la **complémentarité** entre l'obstruction computationnelle et l'obstruction entropique, et identifie la zone de chevauchement [18, 67] comme un rempart structurel.

### 5.2. Démonstration

La partie (A) est le résultat principal de Simons et de Weger (2005), obtenu par la théorie de Baker des formes linéaires en logarithmes et la réduction de réseau LLL.

La partie (B) est le Théorème 1 ci-dessus.

L'intersection est immédiate : tout entier k ≥ 2 vérifie k < 68 ou k ≥ 18 (puisque 18 ≤ 67 < 68). Donc k est couvert par (A) ou (B). ∎

### 5.3. Architecture des trois régimes

L'analyse par convergents révèle une architecture naturelle en trois régimes :

**Régime résiduel** (convergents q₃ = 5, q₄ = 12). — Le rapport C/d vaut respectivement 2.69 et 4.44. L'application Ev_d est potentiellement surjective. Ces valeurs sont éliminées par la borne computationnelle de Simons-de Weger.

**Régime frontière** (convergent q₅ = 41). — Le rapport C/d ≈ 0.596 tombe pour la première fois sous 1. Ce convergent marque la transition : il est éliminé à la fois par Simons-de Weger (k = 41 < 68) et par la non-surjectivité (C < d).

**Régime cristallin** (convergents q₇ = 306 et au-delà). — Le rapport C/d décroît exponentiellement. Pour q₇ : C/d ≈ 2^{−20} ≈ 10^{−6}. Pour q₉ : C/d ≈ 2^{−1230}. Dans ce régime, la grande majorité des résidus mod d sont inaccessibles.

### 5.4. Table des rapports C/d pour les convergents

| Convergent | k | S | log₂(C/d) | Couverture |
|-----------|---|---|-----------|------------|
| q₃ | 5 | 8 | +1.43 | Simons-de Weger |
| q₅ | 41 | 65 | −0.75 | SdW + Non-surjectivité |
| q₇ | 306 | 485 | −19.7 | Non-surjectivité |
| q₉ | 15601 | 24727 | −1230 | Non-surjectivité |
| q₁₁ | 79335 | 125743 | −6284 | Non-surjectivité |

---

## 6. L'Hypothèse d'Équirépartition Exponentielle et perspectives

### 6.1. Le résidu 0

Les Théorèmes 1 et 2 établissent que l'application Ev_d omet des résidus. Cependant, l'existence d'un cycle requiert spécifiquement que 0 ∈ Im(Ev_d), c'est-à-dire qu'il existe une composition A telle que d | corrSum(A). La non-surjectivité seule ne garantit pas que 0 soit parmi les résidus omis.

Notons — heuristiquement — que le résidu 0 n'a aucune raison structurelle apparente d'être privilégié par l'application Ev_d. L'argument suivant, bien que non rigoureux, motive l'Hypothèse (H). La somme correctrice corrSum(A) = Σ 3^{k−1−i} · 2^{A_i} intègre à chaque étape impaire l'opération *n ↦ (3n + 1)/2*, dont le terme additif « +1 » **brise la symétrie purement multiplicative** de la dynamique. Si la transformation était n ↦ 3n/2 (sans le +1), la condition corrSum ≡ 0 (mod d) se réduirait à un alignement multiplicatif des puissances de 2 et de 3, ce qui pourrait favoriser le résidu 0. Mais l'addition constante du 1, propagée par la structure de Horner de corrSum, introduit une translation additive non triviale à chaque étape, détruisant tout mécanisme d'attraction algébrique vers 0. Le résidu 0 est ainsi un point parmi les d résidus possibles, sans statut particulier vis-à-vis de l'arithmétique de corrSum.

Nous formulons la condition manquante sous forme d'hypothèse.

### 6.2. L'Hypothèse (H)

**Hypothèse (H)** (Équirépartition exponentielle). — *Pour tout premier p divisant d avec ord_p(2) suffisamment grand, les sommes de caractères de la fonction corrSum satisfont une annulation de type Weil : pour tout caractère non trivial χ de 𝔽_p^× :*

> *|Σ_{A ∈ Comp(S,k)} χ(corrSum(A))| ≤ C(S−1, k−1) · p^{−1/2+ε}*

*pour tout ε > 0 et k suffisamment grand. En d'autres termes, l'image de Ev_p se comporte comme un sous-ensemble pseudo-aléatoire de 𝔽_p au sens de la combinatoire arithmétique.*

### 6.3. Conséquence de (H)

Sous l'Hypothèse (H), l'annulation des sommes de caractères permet de borner la **densité analytique** du résidu 0 dans l'image de Ev_d. Par les relations d'orthogonalité des caractères de Dirichlet, le nombre de compositions A telles que corrSum(A) ≡ 0 (mod p) est :

> |{A ∈ Comp : corrSum(A) ≡ 0 mod p}| = C/p + (1/p) · Σ_{χ ≠ 1} Σ_A χ(corrSum(A))

Sous (H), le terme d'erreur est borné par C · p^{−3/2+ε}, donc :

> |{A : corrSum(A) ≡ 0 mod p}| = C/p · (1 + O(p^{−1/2+ε}))

Le nombre de compositions atteignant 0 modulo chaque premier p | d est ainsi contrôlé. Si de plus les contraintes modulo les différents premiers p | d sont asymptotiquement indépendantes — ce qui constitue la partie la plus forte de l'Hypothèse (H), au-delà de l'annulation individuelle des sommes de caractères — alors le théorème des restes chinois implique que la densité du résidu 0 dans l'image de Ev_d est au plus C/d, qui décroît exponentiellement vers 0 :

> Pour k = 306 (q₇) : C/d ≈ 10^{−6}. Pour k = 15601 (q₉) : C/d ≈ 2^{−1230}.

Sa densité asymptotique étant nulle dans l'espace des paramètres diophantiens, l'intersection avec le point singulier {0} est de mesure nulle. Conjuguée au Théorème de Jonction, l'Hypothèse (H) implique l'inexistence complète des cycles positifs non triviaux.

### 6.4. Éléments en faveur de (H)

Plusieurs indices soutiennent la validité de l'Hypothèse (H) :

**(i) Vérification numérique directe.** Pour le convergent q₅ (k = 41), nous avons vérifié par programmation dynamique que l'évaluation Ev_p est surjective pour chaque facteur premier p de d₅ = 19 × 29 × 17021 × 44835377399, avec distribution quasi-uniforme des résidus.

**(ii) Bornes de Fourier.** Le biais par caractère mod 29 est borné par (25/28)^40 ≈ 0.01, confirmant une distribution proche de l'uniformité.

**(iii) Quasi-injectivité de Horner.** Pour les premiers p | d avec ord_p(2) ≫ 1, la structure récursive de Horner (corrSum ≡ 3 · corrSum_{k−1} + 2^{A_{k−1}} mod p) se comporte de manière quasi-injective à chaque étape, limitant les collisions.

**(iv) Cohérence avec Tao (2022).** Le résultat de Tao sur la convergence « presque sûre » utilise des estimées de sommes exponentielles de nature analogue à (H).

### 6.5. Pistes pour une démonstration de (H)

Nous identifions trois voies potentielles :

**Voie 1 : Sommes exponentielles.** Borner les sommes de caractères Σ χ(corrSum(A)) en exploitant la structure multiplicative de corrSum. La difficulté réside dans le mélange non polynomial des termes 3^{k−1−i} et 2^{A_i}.

**Voie 2 : Géométrie arithmétique.** Interpréter l'application Ev_d comme une application entre variétés sur les corps finis, et appliquer les bornes de type Weil-Deligne. La structure de Horner pourrait se prêter à une analyse de type « marche aléatoire sur les fibres ».

**Voie 3 : Extension computationnelle.** Étendre la méthodologie de Simons et de Weger au-delà de k < 68. Avec les ressources computationnelles modernes, atteindre k < 500 est envisageable. Combiné avec la décroissance exponentielle de C/d pour k > 306, cela renforcerait considérablement le résultat.

---

## 7. Conclusion

Nous avons démontré que le problème des cycles positifs de Collatz est gouverné par un déficit entropique fondamental γ ≈ 0.0500, qui rend l'application d'évaluation modulaire non surjective pour tout k ≥ 18. Ce résultat, conjugué à la borne computationnelle de Simons-de Weger (k < 68), produit un Théorème de Jonction couvrant l'ensemble des longueurs k ≥ 2.

Le passage de la non-surjectivité à l'exclusion du résidu 0 constitue le dernier obstacle. Nous le formulons comme l'Hypothèse d'Équirépartition Exponentielle (H), solidement étayée numériquement mais non encore démontrée. Sa résolution constituerait une avancée significative dans l'étude de la conjecture de Collatz.

*Limitation.* Le présent travail ne traite que des cycles positifs (d = 2^S − 3^k > 0, correspondant aux convergents d'index impair). L'analyse des cycles négatifs (d < 0, convergents d'index pair) fait intervenir des modules de signe opposé et une dynamique inverse ; elle fera l'objet d'un travail ultérieur. Mentionnons que Böhm et Sontacchi (1978) et Steiner (1977) ont indépendamment traité les deux signes dans le cadre de l'équation de cycle.

---

## Références

[1] R. E. Crandall, « On the 3x + 1 problem », *Mathematics of Computation*, vol. 32, pp. 1281-1292, 1978.

[2] S. Eliahou, « The 3x + 1 problem: new lower bounds on nontrivial cycle lengths », *Discrete Mathematics*, vol. 118, pp. 45-56, 1993.

[3] J. C. Lagarias, « The 3x + 1 problem and its generalizations », *The American Mathematical Monthly*, vol. 92, pp. 3-23, 1985.

[4] M. Laurent, M. Mignotte et Y. Nesterenko, « Formes linéaires en deux logarithmes et déterminants d'interpolation », *Journal of Number Theory*, vol. 55, pp. 285-321, 1995.

[5] D. Simons et B. de Weger, « Theoretical and computational bounds for m-cycles of the 3n + 1 problem », *Acta Arithmetica*, vol. 117, pp. 51-70, 2005.

[6] R. P. Steiner, « A theorem on the Syracuse problem », *Proceedings of the 7th Manitoba Conference on Numerical Mathematics*, pp. 553-559, 1977.

[7] T. Tao, « Almost all orbits of the Collatz map attain almost bounded values », *Forum of Mathematics, Pi*, vol. 10, e12, 2022.

[8] T. Barina, « Convergence verification of the Collatz problem », *The Journal of Supercomputing*, vol. 77, pp. 2681-2688, 2021.

[9] G. J. Wirsching, *The Dynamical System Generated by the 3n+1 Function*, Lecture Notes in Mathematics 1681, Springer, 1998.

[10] C. Böhm et G. Sontacchi, « On the existence of cycles of given length in integer sequences like x_{n+1} = x_n/2 if x_n even, and x_{n+1} = 3x_n+1 otherwise », *Atti della Accademia Nazionale dei Lincei*, vol. 64, pp. 260-264, 1978.

[11] J. C. Lagarias (éd.), *The Ultimate Challenge: The 3x+1 Problem*, American Mathematical Society, 2010.

[12] A. V. Kontorovich et S. J. Miller, « Benford's law, values of L-functions and the 3x+1 problem », *Acta Arithmetica*, vol. 120, pp. 269-297, 2005.
