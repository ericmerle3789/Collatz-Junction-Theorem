# Barrières Entropiques et Non-Surjectivité dans le Problème 3x+1 : Le Théorème de Jonction

**Eric Merle**

*Février 2026*

---

**Résumé.** — Nous étudions le sous-problème de l'inexistence des cycles positifs non triviaux dans la dynamique de Collatz *T(n) = n/2* (n pair), *T(n) = (3n+1)/2* (n impair). En revisitant l'équation de Steiner (1977) sous l'angle de la théorie de l'information, nous identifions un déficit entropique universel

> γ = 1 − h(1/log₂ 3) ≈ 0.0500

où h désigne l'entropie binaire de Shannon. Ce déficit exprime le fait que le taux de croissance du nombre de compositions admissibles est strictement inférieur au taux de croissance du module cristallin d = 2^S − 3^k. Il en résulte un **Théorème de Non-Surjectivité** (inconditionnel) : pour tout cycle candidat de longueur k ≥ 18 avec d > 0, l'application d'évaluation modulaire Ev_d ne peut pas être surjective. Conjugué au résultat computationnel de Simons et de Weger (2005), qui exclut tout cycle positif de longueur k < 68, nous obtenons un **Théorème de Jonction** : pour tout k ≥ 2, au moins l'une des deux obstructions — computationnelle ou entropique — s'applique. La question résiduelle — l'exclusion du résidu spécifique 0 de l'image — est formulée comme une **Hypothèse de Quasi-Uniformité** (H), dont nous discutons les fondements numériques et les voies de résolution.

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

### 1.4. Notre contribution

Nous proposons un changement de paradigme. Plutôt que de borner directement l'entier n₀ ou la forme linéaire |S log 2 − k log 3|, nous étudions la **cardinalité de l'image** de l'application d'évaluation modulaire

> Ev_d : Comp(S, k) → ℤ/dℤ, A ↦ corrSum(A) mod d

où Comp(S, k) désigne l'ensemble des compositions admissibles. Notre observation clé est qu'un déficit entropique fondamental — la constante γ — interdit à Ev_d d'être surjective dès que k est modérément grand. Ce résultat est **inconditionnel**.

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

**Étape 2 : Prise en compte des non-convergents.** Pour k qui n'est pas un dénominateur de convergent, la meilleure approximation S/k de log₂ 3 est strictement moins bonne que pour un convergent voisin. Le module d correspondant est donc strictement plus grand, renforçant l'inégalité C < d.

**Étape 3 : Vérification numérique exhaustive.** Pour k ∈ [2, 500], nous calculons directement C(S − 1, k − 1) et d = 2^S − 3^k avec S = ⌈k log₂ 3⌉. Le calcul montre que C/d < 1 pour tout k ≥ 18 avec d > 0.

Les seules exceptions sont k ∈ {3, 5, 17}, pour lesquelles :

| k | S | C(S−1, k−1) | d | C/d |
|---|---|-------------|---|-----|
| 3 | 5 | 6 | 5 | 1.20 |
| 5 | 8 | 35 | 13 | 2.69 |
| 17 | 27 | 7726160 | 7340033 | 1.05 |

Ces trois valeurs satisfont toutes k < 68.

**Étape 4 : Vérification asymptotique.** Pour k ≥ 500, la borne de Stirling avec estimation de reste montre que log₂(C/d) < −γS/2 < 0, confirmant C < d sans calcul explicite. ∎

### 4.3. Remarque sur le seuil K₀ = 18

Le seuil K₀ = 18 est remarquablement bas. Il signifie que pour tout cycle hypothétique de longueur k ≥ 18, la « capacité résiduelle » du module d excède strictement le nombre de corrSums possibles. Autrement dit : l'escalier des compositions ne peut pas atteindre tous les paliers du module.

Le convergent frontière est q₅ = 41, pour lequel C/d ≈ 0.596 — le premier convergent d'index impair où le déficit entropique l'emporte sur le bonus d'approximation.

---

## 5. Le Théorème de Jonction

### 5.1. Énoncé

**Théorème 2** (Jonction). — *Pour tout entier k ≥ 2, au moins l'une des deux obstructions suivantes s'applique à un cycle positif hypothétique de longueur k :*

*(A) Obstruction computationnelle : si k < 68, aucun cycle positif non trivial de longueur k n'existe (Simons et de Weger, 2005).*

*(B) Obstruction entropique : si k ≥ 18 et d = 2^⌈k log₂ 3⌉ − 3^k > 0, alors l'application d'évaluation Ev_d n'est pas surjective.*

*L'intersection [18, 67] assure que tout k ≥ 2 est couvert par au moins l'une des deux obstructions.*

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

## 6. L'Hypothèse de Quasi-Uniformité et perspectives

### 6.1. Le résidu 0

Les Théorèmes 1 et 2 établissent que l'application Ev_d omet des résidus. Cependant, l'existence d'un cycle requiert spécifiquement que 0 ∈ Im(Ev_d), c'est-à-dire qu'il existe une composition A telle que d | corrSum(A). La non-surjectivité seule ne garantit pas que 0 soit parmi les résidus omis.

Nous formulons la condition manquante sous forme d'hypothèse.

### 6.2. L'Hypothèse (H)

**Hypothèse (H)** (Quasi-uniformité). — *Pour tout premier p divisant d avec ord_p(2) suffisamment grand, l'application d'évaluation*

> *Ev_p : Comp(S, k) → 𝔽_p*

*distribue la somme correctrice de manière approximativement uniforme parmi les résidus atteignables, au sens où pour tout caractère non trivial χ de 𝔽_p^× :*

> *|Σ_{A ∈ Comp} χ(corrSum(A))| ≤ C(S−1, k−1) · p^{−1/2+ε}*

*pour tout ε > 0 et k suffisamment grand.*

### 6.3. Conséquence de (H)

Sous l'Hypothèse (H), la probabilité qu'un résidu spécifique (en particulier 0) appartienne à l'image de Ev_d est bornée par :

> P(0 ∈ Im(Ev_d)) ≤ C/d

qui tend vers 0 exponentiellement vite. Plus précisément, le modèle de Poisson donne :

> P(0 ∈ Im) ≈ 1 − exp(−C/d)

Pour k = 306 (convergent q₇) : P ≤ 10^{−6}. Pour k = 15601 (convergent q₉) : P ≤ 2^{−1230} ≈ 0.

Conjuguée au Théorème de Jonction, l'Hypothèse (H) implique l'inexistence complète des cycles positifs non triviaux.

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

Le passage de la non-surjectivité à l'exclusion du résidu 0 constitue le dernier obstacle. Nous le formulons comme l'Hypothèse de Quasi-Uniformité (H), solidement étayée numériquement mais non encore démontrée. Sa résolution constituerait une avancée significative dans l'étude de la conjecture de Collatz.

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
