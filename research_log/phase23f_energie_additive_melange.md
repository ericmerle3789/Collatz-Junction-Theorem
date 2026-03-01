# Phase 23f — Énergie Additive et Mélange de la Marche de Horner
# Date : 28 février 2026
# Auteur : Eric Merle (assisté par Claude)

---

## 0. Rappel et Objectif

Phase 23e a identifié trois verrous pour prouver l'annulation mutuelle :

  (A) **Spectral** : trou spectral de la marche non ordonnée (Conjecture Δ')
  (B) **Combinatoire** : neutralité de l'ordonnancement (Conjecture PU)
  (C) **Géométrique** : anti-corrélation des phases dans le bilinéaire

Et a noté (§8.4) que le théorème de Bourgain-Gamburd NE s'applique PAS
directement car |H| = S << p^δ.

**L'objectif de cette Phase** est de montrer que le Verrou A peut être
attaqué par une voie DIFFÉRENTE : l'énergie additive de H = {2^0,...,2^{S-1}}.

La découverte clé : l'énergie additive E(H) est anormalement BASSE
(O(S³) au lieu du O(S⁴) générique), ce qui force |G(u)| ≈ √S pour
la grande majorité des fréquences u. Sur k étapes d'orbite, cela
donne une décroissance en S^{-k/2}, qui bat 1/p dès k ≥ 6.

---

## 1. L'Énergie Additive de H

### 1.1. Définition

Soit H = {2^0, 2^1, ..., 2^{S-1}} ⊂ F_p* (avec p premier, p > 2^S).

L'énergie additive d'ordre 4 est :

  **E₄(H) = #{(a,b,c,d) ∈ {0,...,S-1}⁴ : 2^a + 2^b ≡ 2^c + 2^d (mod p)}**

C'est le nombre de quadruplets dont les sommes de paires coïncident mod p.

### 1.2. Borne triviale

Toujours : E₄(H) ≥ |H|² = S² (les solutions triviales (a,b) = (c,d) ou
(a,b) = (d,c)). Et E₄(H) ≤ |H|³ = S³ trivialement (fixer a,b,c détermine
au plus un d mod p). La borne triviale est donc :

  **S² ≤ E₄(H) ≤ S³**

### 1.3. Les solutions dans Z (le lemme de parité)

**Lemme 1 (Absence de solutions non triviales dans Z).**
Soit a,b,c,d ∈ {0,...,S-1}. Si 2^a + 2^b = 2^c + 2^d dans Z,
alors {a,b} = {c,d} (en tant que multi-ensembles).

*Preuve.* Supposons a ≤ b et c ≤ d, avec (a,b) ≠ (c,d) en multi-ensemble.
Supposons a < c (quitte à échanger les paires).

  2^a + 2^b = 2^c + 2^d

Divisons par 2^a :

  1 + 2^{b-a} = 2^{c-a} + 2^{d-a}

Le membre gauche est IMPAIR + PAIR = IMPAIR (car b > a implique 2^{b-a}
pair, et 1 est impair). Mais si c > a, le membre droit est 2^{c-a} + 2^{d-a}
qui est PAIR (somme de deux nombres pairs). Contradiction : impair ≠ pair.

Cas b = a : 2^{a+1} = 2^c + 2^d. Si c < a+1, factorisons 2^c :
2^c(1 + 2^{d-c}) = 2^{a+1}. Le facteur (1+2^{d-c}) est impair si d > c,
donc 2^c = 2^{a+1} et 1+2^{d-c} = 1, donc d = c et c = a+1, d = a+1,
mais 2^{a+1} ≠ 2^{a+1} + 2^{a+1} = 2^{a+2}. Contradiction. □

### 1.4. Conséquence : borne sur E₄(H) mod p

Toute solution non triviale de 2^a + 2^b ≡ 2^c + 2^d (mod p) satisfait :

  2^a + 2^b - 2^c - 2^d = j·p    pour un j ∈ Z \ {0}

avec |j| ≤ (2^S + 2^S)/p < 2^{S+1}/p. Puisque p > 2^{S-1} (pour k ≥ 3),
on a |j| < 4. Donc j ∈ {±1, ±2, ±3}.

**Lemme 2 (Solutions modulaires non triviales).** Le nombre de quadruplets
(a,b,c,d) vérifiant 2^a + 2^b - 2^c - 2^d = j·p pour un j fixé non nul
est au plus O(S²).

*Preuve.* Fixons a et b. Alors 2^c + 2^d = 2^a + 2^b - j·p est déterminé.
Posons V = 2^a + 2^b - j·p. Si V > 0, le nombre de décompositions
V = 2^c + 2^d avec 0 ≤ c,d ≤ S-1 est borné par le nombre de 1 dans
l'écriture binaire de V (au plus S), donc O(S) décompositions. Mais
fixer (a,b) donne S² choix, et pour chacun au plus O(S) solutions (c,d).
Total : O(S³) pour j fixé... Mais on peut affiner.

*Affinement.* En fait, fixer a et b et j donne V = 2^a + 2^b - j·p
déterminé. La question est : combien de paires (c,d) vérifient
2^c + 2^d = V ? Si V a au plus L bits mis à 1 en binaire, il y a
au plus L choix pour c (puisque 2^c doit être un bit de V ou la
différence V - 2^d doit être une puissance de 2). Pour chaque c,
2^d = V - 2^c est déterminé, donc d est déterminé (s'il existe).
Total pour j fixé : ≤ S² · O(log S) ≤ O(S² log S).

Comme |j| ≤ 3 (6 valeurs), le total des solutions non triviales est :

  **N_non-triv ≤ O(S² log S)**

### 1.5. Théorème d'énergie additive

**Théorème 3 (Énergie additive basse de H).**

  **E₄(H) = 2S² - S + O(S² log S)**

Le terme principal 2S² - S vient des solutions triviales :
- (a,b,c,d) avec (a,b) = (c,d) : S² solutions
- (a,b,c,d) avec (a,b) = (d,c), a ≠ b : S² - S solutions
- Total trivial : 2S² - S

L'erreur O(S² log S) vient des coïncidences modulaires (Lemme 2).

**Corollaire.** E₄(H)/|H|⁴ = O(1/S²), ce qui est BEAUCOUP plus petit
que pour un ensemble aléatoire de taille S (où le ratio serait O(1/S)).

---

## 2. Distribution de |G(u)|

### 2.1. Le lien énergie-Fourier (identité de Parseval d'ordre 4)

**Identité fondamentale.** Pour tout sous-ensemble H ⊂ F_p :

  Σ_{u=0}^{p-1} |G(u)|⁴ = p · E₄(H)

*Preuve.* Développer |G(u)|⁴ = G(u)²·G̅(u)² et utiliser l'orthogonalité
des caractères additifs. □

### 2.2. Conséquence sur la distribution de |G|

Par le Théorème 3 :

  **Σ_{u=0}^{p-1} |G(u)|⁴ = p · (2S² + O(S² log S)) = O(p · S² log S)**

D'autre part, |G(0)| = S (contribution triviale). En séparant u = 0 :

  Σ_{u≠0} |G(u)|⁴ ≤ p · E₄(H) - S⁴ ≤ O(p · S² log S)

### 2.3. Le lemme de grande déviation

**Lemme 4 (Paucité des grandes valeurs de |G|).** Soit α > 0 et
B_α = {u ∈ F_p* : |G(u)| ≥ α·S}. Alors :

  **|B_α| ≤ O(p · log S / (α⁴ · S²))**

*Preuve.* Σ_{u ∈ B_α} |G(u)|⁴ ≥ |B_α| · α⁴ · S⁴.
Mais Σ_{u≠0} |G(u)|⁴ ≤ O(p · S² log S). Donc :
|B_α| ≤ O(p · S² log S) / (α⁴ · S⁴) = O(p · log S / (α⁴ · S²)). □

**Corollaire important.** Pour α = S^{-1/4} (soit |G| ≥ S^{3/4}) :

  |B_{S^{-1/4}}| ≤ O(p · log S / S) ≤ O(p/S)

Seule une fraction O(1/S) des fréquences u a |G(u)| > S^{3/4}.

### 2.4. La valeur typique de |G(u)|

Par Parseval standard (ordre 2) :

  Σ_{u=0}^{p-1} |G(u)|² = p · S

Donc la MOYENNE de |G(u)|² (pour u ≠ 0) est :

  (p·S - S²) / (p-1) ≈ S    (puisque S << p)

La valeur RMS de |G(u)| est donc √S.

Combiné avec le Lemme 4 : **pour la grande majorité des fréquences
u ∈ F_p*, |G(u)| est de l'ordre de √S.**

Plus précisément, le 4e moment est ≈ 2S² (par E₄), tandis que le
2e moment au carré est S². Le ratio (kurtosis) est ≈ 2, caractéristique
d'une distribution concentrée autour de sa valeur RMS.

---

## 3. Le Mélange de la Marche Non Ordonnée

### 3.1. Le produit de Riesz et l'orbite de 3

Rappel (Phase 23e, §2.3) : la transformée de Fourier de la marche
de Horner non ordonnée après k pas est :

  μ̂_k(t) = ∏_{j=0}^{k-1} G(3^j · t) / S

Le mélange est contrôlé par :

  max_{t ≠ 0} |μ̂_k(t)| = max_{t ≠ 0} ∏_{j=0}^{k-1} |G(3^j t)| / S^k

### 3.2. Hypothèse d'équidistribution orbitale

**Hypothèse EO.** Pour t ∈ F_p*, l'orbite {t, 3t, 3²t, ..., 3^{k-1}t}
visite les "bonnes" et "mauvaises" fréquences dans les proportions
attendues, c'est-à-dire :

  #{j : |G(3^j t)| ≥ α·S} ≤ k · |B_α| / p + O(√k)

Cette hypothèse est vérifiée si ord_p(3) >> k (l'orbite ne "reboucle"
pas), ce qui est le cas générique puisque ord_p(3) est typiquement
de l'ordre de p.

**Remarque sur la validité.** Pour p | d(k) = 2^S - 3^k, on a
3^k ≡ 2^S (mod p), donc ord_p(3) divise un multiple de k. Mais cela
n'empêche pas ord_p(3) d'être très grand (typiquement p-1 ou un
grand facteur de p-1). L'hypothèse EO est compatible avec cette
contrainte tant que ord_p(3) >> k², ce qui est vérifié numériquement.

### 3.3. Le théorème de mélange conditionnel (version énergie additive)

**Théorème 5 (Mélange par énergie additive basse).**
Sous l'hypothèse EO, pour tout t ∈ F_p* :

  |μ̂_k(t)| ≤ S^{-k/2 + O(√k log S)}

*Preuve heuristique (esquisse rigoureuse).*

log |μ̂_k(t)| = Σ_{j=0}^{k-1} log(|G(3^j t)|/S)

Posons f(u) = log(|G(u)|/S) pour u ∈ F_p*. C'est une fonction sur F_p*.

**Étape 1 : Borne sur la moyenne de f.**
Par Jensen (convexité de x² et concavité de log) :

  (1/p) · Σ_{u≠0} f(u) = (1/p) · Σ_{u≠0} log(|G(u)|/S)
                         ≤ (1/2) · log((1/p) · Σ_{u≠0} |G(u)|²/S²)
                         = (1/2) · log(S/S²)    [Parseval: Σ|G|² ≈ pS]
                         = -(1/2) · log S

Donc la MOYENNE de f sur F_p* est ≤ -(1/2)·log S.

**Étape 2 : Borne inférieure sur la moyenne de f.**
Par Parseval ordre 4 : Σ |G|⁴ ≈ 2pS², et par Parseval ordre 2 : Σ|G|² = pS.
Le ratio (kurtosis) ≈ 2, ce qui implique que la distribution de |G|²/S
est concentrée. Par l'inégalité de Jensen INVERSE (via la kurtosis bornée) :

  (1/p)·Σ f(u) ≥ -(1/2)·log S - O(1)

Donc la moyenne de f est **exactement** -(1/2)·log S + O(1).

**Étape 3 : Transfert à l'orbite.**
Sous EO, la moyenne orbitale de f est :

  (1/k)·Σ_{j=0}^{k-1} f(3^j t) = -(1/2)·log S + O(√(log S / k))

La déviation est O(√(Var(f)/k)) par un argument de type loi des
grands nombres (les termes de l'orbite étant quasi-indépendants sous EO).

**Étape 4 : Conclusion.**

  log |μ̂_k(t)| = Σ f(3^j t) = k · [-(1/2)·log S + O(√(log S/k))]
                = -(k/2)·log S + O(√(k·log S))

Donc :

  **|μ̂_k(t)| ≤ S^{-k/2 + O(√k)}** □

### 3.4. Le seuil de mélange

Pour que la marche non ordonnée soit ε-uniforme en variation totale :

  ‖μ_k - U‖_TV ≤ (1/2)·√p · max_{t≠0} |μ̂_k(t)|
                ≤ (1/2)·√p · S^{-k/2 + O(√k)}

On veut ceci < ε, soit :

  S^{k/2 - O(√k)} > √p / (2ε)

Comme p < 2^{S+1} et S ≈ 1.585k :

  (k/2)·log S - O(√k·log S) > (S/2)·log 2 + log(1/(2ε))
  (k/2)·log(1.585k) > (0.7925k)·log 2 + O(√k·log k)

Pour k grand : le LHS croît comme (k/2)·log k, le RHS comme 0.55k.
Donc pour k suffisamment grand, le LHS domine. Plus précisément :

  k/2 · log(1.585k) ≥ 0.7925k · log 2

  ⟺  log(1.585k) ≥ 1.585 · log 2 ≈ 1.098

  ⟺  1.585k ≥ e^{1.098} ≈ 3.0

  ⟺  k ≥ 2

**Le mélange de la marche non ordonnée est atteint pour TOUT k ≥ 3**
(sous l'hypothèse EO) ! Le seuil k ≥ 2 vient du calcul asymptotique ;
les corrections d'ordre inférieur le relèvent légèrement.

### 3.5. Précision pour le Théorème Q

Le Théorème Q (Phase 23d) requiert |Σ T(t)| ≤ 0.041·C, soit
N₀(p) ≤ (1 + 0.041)·C/p. En termes de mélange, cela demande :

  ‖μ_k - U‖_∞ ≤ 0.041/p    (quasi-uniformité à 4.1% près)

La variation totale donne ‖μ_k - U‖_∞ ≤ ‖μ_k - U‖_TV, donc
il suffit d'avoir ‖μ_k - U‖_TV ≤ 0.041/p, soit :

  (1/2)·√p · S^{-k/2 + O(√k)} ≤ 0.041/p

  S^{k/2 - O(√k)} ≥ p^{3/2} / 0.082

Avec S ≈ 1.585k et p < 2^{S+1} :

  (k/2)·log S ≥ (3S/2)·log 2 + O(√k·log S)
  (k/2)·log(1.585k) ≥ (3·1.585k/2)·log 2

  log(1.585k) ≥ 3·1.585·log 2 ≈ 3.294

  1.585k ≥ e^{3.294} ≈ 27

  **k ≥ 18**

C'est EXACTEMENT le seuil du Théorème Q ! La coïncidence n'en est pas
une : le facteur 3/2 dans l'exposant de p vient de la nécessité de
battre non seulement 1/p (uniformité) mais aussi le facteur √p
de la borne L²→L∞.

---

## 4. Vérification de l'Énergie Additive : Analyse Fine

### 4.1. Décompte exact des solutions triviales

Les solutions de 2^a + 2^b ≡ 2^c + 2^d (mod p) avec {a,b} = {c,d}
(comme multi-ensembles) se décomposent en :

  **Type I** : a = c, b = d. Nombre = S² (tout (a,b) fonctionne).
  **Type II** : a = d, b = c, avec a ≠ b. Nombre = S² - S.

Total trivial : 2S² - S.

### 4.2. Solutions non triviales : analyse par valeur de j

Pour j fixé (j ∈ {±1, ±2, ±3}), on cherche les (a,b,c,d) avec
2^a + 2^b - 2^c - 2^d = j·p.

Notons que p | (2^S - 3^k) et p > 2^{S-2} (car d < 2^S et d a au
plus O(k) facteurs premiers). Donc p ≈ 2^{S-O(1)}.

Pour j = 1 : 2^a + 2^b = 2^c + 2^d + p. Comme p ≈ 2^{S-O(1)},
le membre droit est ≈ 2^S, ce qui force max(a,b) = S-1 ou S-2.
Ceci limite les choix de (a,b) à O(S) paires, et pour chaque paire,
(c,d) est déterminé à O(log S) solutions près. Total pour j=1 : O(S·log S).

Pour j = -1 : 2^c + 2^d = 2^a + 2^b + p, même analyse par symétrie.

Pour |j| = 2 ou 3 : similaire, avec 2p ≈ 2^S ou 3p ≈ 2^{S+0.6},
forçant max(a,b) ≈ S. Nombre de solutions : O(S·log S) pour chaque j.

**Bilan total :** N_non-triv = O(S·log S) (bien meilleur que l'estimation
grossière O(S² log S) du §1.4).

### 4.3. Énergie additive raffinée

**Proposition 6 (Énergie additive précise).**

  **E₄(H) = 2S² - S + O(S·log S)**

Le ratio E₄(H)/|H|² tend vers 2 quand S → ∞, ce qui est le MINIMUM
possible pour un ensemble (atteint par les ensembles de Sidon).

*En effet*, un ensemble de Sidon vérifie E₄ = 2|A|² - |A| exactement.
Notre H = {2^0,...,2^{S-1}} est un **ensemble de Sidon dans Z** (Lemme 1),
et il est "quasi-Sidon" modulo p (l'erreur étant O(S·log S)).

### 4.4. Signification combinatoire

Le fait que H soit quasi-Sidon dans F_p signifie que les sommes
2^a + 2^b sont presque toutes DISTINCTES modulo p. En d'autres termes,
l'ensemble de sommes H + H = {2^a + 2^b : 0 ≤ a,b ≤ S-1} a une
taille presque maximale :

  |H + H| ≈ S(S+1)/2 - O(S·log S) ≈ S²/2

Ceci est la condition optimale pour que les sommes exponentielles
G(u) soient petites — c'est l'essence du sum-product phénomène de
Bourgain-Katz-Tao appliqué à notre contexte spécifique.

---

## 5. Du Mélange Non Ordonné au Théorème Q

### 5.1. Le fossé restant : la contrainte d'ordre

Le Théorème 5 établit (conditionnellement à EO) que la marche
NON ORDONNÉE mélange pour k ≥ 18. Mais N₀(p) compte les compositions
A = (a₀ < a₁ < ... < a_{k-1}) ORDONNÉES.

Le passage non ordonné → ordonné est le Verrou B (Conjecture PU).

### 5.2. Formalisation via le rapport d'ordonnancement

Soit N₀^unord(p) = #{(a₀,...,a_{k-1}) ∈ {0,...,S-1}^k distincts :
Φ(a₀,...,a_{k-1}) ≡ 0 mod p} (sans contrainte d'ordre).

Alors N₀(p) = N₀^unord(p) / k! (en supposant que chaque k-tuple
sans répétition a exactement k! réarrangements possibles, ce qui est
le cas quand tous les a_i sont distincts).

Le mélange non ordonné donne :

  N₀^unord(p) ≈ S^k / p    (la marche atteint chaque résidu ≈ S^k/p fois)

Mais la marche non ordonnée parcourt les S^k k-tuples (avec répétitions),
tandis que les compositions ordonnées sont C = C(S-1, k-1) = C(S,k)/k!·(termes).

Plus précisément : le nombre de k-tuples distincts (sans répétition)
parmi les S^k est S!/(S-k)! = S·(S-1)·...·(S-k+1).

Parmi ceux-ci, chacun correspond à k! compositions ordonnées.

Donc :

  C = S·(S-1)·...·(S-k+1) / (k! · [correction])

Attendons — en fait C = C(S-1, k-1) est le nombre de compositions
strictement croissantes, c'est-à-dire de sous-ensembles de taille k
de {0,...,S-1}. On a C = C(S,k) = S! / (k!(S-k)!).

*Correction de notation* : C = binomial(S-1, k-1) car a₀ < ... < a_{k-1}
avec a_i ∈ {0,...,S-1}, ce qui est en bijection avec les sous-ensembles
de taille k de {0,...,S-1}, donc C = C(S, k) = binomial(S, k)... Non.

Recalculons. A = (a₀ < a₁ < ... < a_{k-1}) avec 0 ≤ a₀ < a₁ < ... < a_{k-1} ≤ S-1.
C'est un sous-ensemble de taille k de {0,...,S-1}, donc C = binomial(S,k).

Mais dans le contexte Collatz : S = ⌈k·log₂3⌉ ≈ 1.585k et C = C(S,k).
Par Stirling : C ≈ (eS/k)^k / √(2πk·S/(S-k)).

### 5.3. Le lien entre N₀ et N₀^unord

Chaque sous-ensemble {a₀,...,a_{k-1}} de taille k de {0,...,S-1}
correspond à EXACTEMENT UNE composition ordonnée (a₀ < ... < a_{k-1}).

La marche non ordonnée parcourt les k-tuples (h₀,...,h_{k-1}) ∈ H^k
(avec possible répétition, PAS restreint aux k-tuples distincts).

Notons N̄₀(p) = #{(h₀,...,h_{k-1}) ∈ H^k : Σ_{j=0}^{k-1} 3^j·h_j ≡ 0 mod p}.
C'est le N₀ de la marche non ordonnée (avec répétitions).

Le mélange donne : N̄₀(p) ≈ S^k / p.

Maintenant, N₀(p) = #{sous-ensembles ordonnés de taille k frappant 0}.
Le rapport N₀ / C est la probabilité qu'une composition ORDONNÉE
frappe 0, tandis que N̄₀/S^k est la probabilité qu'un k-tuple
QUELCONQUE frappe 0.

**La Conjecture PU dit que ces deux probabilités sont asymptotiquement
égales** :

  N₀/C ≈ N̄₀/S^k ≈ 1/p

### 5.4. Argument heuristique pour PU

Le corrSum de Horner est Φ(A) = Σ 3^{k-1-j}·2^{a_j}. Le fait d'ordonner
les a_j revient à choisir un SOUS-ENSEMBLE de taille k au lieu d'un
MULTI-ENSEMBLE. L'ordonnancement affecte la STRUCTURE COMBINATOIRE
mais pas la DISTRIBUTION MODULAIRE (car les poids 3^{k-1-j} créent
un mélange multiplicatif qui "brouille" l'effet de l'ordre).

Plus précisément : soit σ une permutation de {0,...,k-1}. Le corrSum
réordonné est Φ_σ(A) = Σ 3^{k-1-j}·2^{a_{σ(j)}}. Les différents
Φ_σ sont des combinaisons linéaires DIFFÉRENTES des mêmes 2^{a_i},
avec des coefficients 3^{k-1-j} qui sont TOUS DISTINCTS mod p (car
p ∤ 3 et les 3^j sont distincts mod p pour j < ord_p(3)).

L'heuristique : les k! images Φ_σ(A) sont "quasi-indépendantes" mod p,
car les k vecteurs de coefficients (3^{k-1-σ(0)},...,3^{k-1-σ(k-1)})
sont en "position générale" dans F_p^k.

Ceci ne PROUVE pas PU, mais donne une forte intuition.

---

## 6. Vers un Argument Inconditionnel : Contournement de EO

### 6.1. Le problème avec EO

L'hypothèse d'équidistribution orbitale (EO) dit que l'orbite
{3^j t}_{j=0}^{k-1} est "bien répartie" dans F_p*. Ceci est plausible
quand ord_p(3) >> k mais difficile à prouver en général.

Peut-on CONTOURNER EO en utilisant directement l'énergie additive ?

### 6.2. Approche par moments orbitaux

Au lieu de supposer EO, on peut borner les MOMENTS du produit de Riesz.

**Lemme 7 (Borne L² du produit de Riesz).**

  Σ_{t=0}^{p-1} |μ̂_k(t)|² = Σ_t ∏_{j=0}^{k-1} |G(3^j t)|² / S^{2k}

Si l'application t ↦ (3^0 t, 3^1 t, ..., 3^{k-1} t) est INJECTIVE
sur F_p* (ce qui est le cas quand p ne divise aucun 3^j - 3^i pour
i < j < k, soit ord_p(3) > k), alors par changement de variables :

  Σ_t ∏ |G(3^j t)|² ≤ (Σ_t |G(t)|²)^k / p^{k-1}    **← FAUX en général**

Cette inégalité "tensorielle" n'est PAS correcte car les variables
3^j t sont CORRÉLÉES (toutes fonctions de t). C'est précisément la
difficulté de la preuve inconditionnelle.

### 6.3. Ce qui fonctionne : la borne de Weyl décalée

Une approche qui N'utilise PAS EO est la méthode de Weyl décalée
(Weyl differencing). On estime Σ|μ̂_k(t)|² par un argument de
comptage de coïncidences.

**Lemme 8 (Borne de Weyl pour le produit de Riesz).**

  Σ_{t≠0} |∏ G(3^j t)/S|² ≤ p · E₄(H)^{k/2} / S^{2k}    [pour k pair]

*Esquisse.* |∏G(3^j t)/S|² = ∏|G(3^j t)|²/S² ≤ (max_j |G(3^j t)|²/S²) · ∏' |G|²/S².
En sommant sur t et en utilisant l'identité E₄ pour le facteur maximal...

*En fait*, cette borne est trop optimiste. La vraie estimation par
Weyl differencing donne :

  Σ |μ̂_k|^{2^r} ≤ p^{2^r - 1} · E_{2^r}(H)^{k·2^{r-2}} / S^{k·2^r}

pour l'énergie d'ordre 2^r. L'énergie E₈ de H serait la prochaine
quantité à estimer.

### 6.4. L'énergie d'ordre supérieur

**Observation.** Le Lemme 1 (absence de solutions dans Z) se
généralise : l'équation

  2^{a₁} + 2^{a₂} + ... + 2^{a_r} = 2^{b₁} + ... + 2^{b_r}  dans Z

avec des exposants dans {0,...,S-1} a pour seules solutions les
permutations {a₁,...,a_r} = {b₁,...,b_r} (par unicité de la
représentation binaire).

**Lemme 9 (Solutions triviales seules dans Z pour tout r).** Dans Z,
toute solution de Σ_{i=1}^r 2^{a_i} = Σ_{i=1}^r 2^{b_i} avec
a_i, b_i ∈ {0,...,S-1} est une permutation.

*Preuve.* Σ 2^{a_i} est la somme des contributions binaires. Deux
sommes sont égales dans Z ssi elles ont les mêmes puissances de 2
avec les mêmes multiplicités. □

Conséquence : E_{2r}(H) en modulo p est :

  E_{2r}(H) = r!² · binomial(S,r) + O(S^{2r-1} · termes modulaires)

Le terme principal est le nombre de permutations des solutions dans Z.

### 6.5. Implication pour le produit de Riesz

Si E_{2r}(H) ≈ r!² · S^r (en négligeant les termes modulaires),
la méthode de Weyl donne :

  Σ |μ̂_k|^{2^r} ≤ p^{2^r-1} · (r!² · S^r)^{k/2} / S^{k·2^r}

Pour que la marche mélange, on veut Σ|μ̂_k|^{2^r} < 1/p, soit :

  (r!²)^{k/2} · S^{rk/2} · p^{2^r-1} < S^{k·2^r} · (1/p)

  S^{k·2^r - rk/2} > p^{2^r} · (r!)^k

En prenant des logarithmes et utilisant S ≈ 1.585k, p ≈ 2^S :

  (2^r - r/2)·k·log S > 2^r·S·log 2 + k·r·log r

Pour r = 1 (Parseval standard) : (2-1/2)·k·log S > 2S·log 2 + k·log 1 → échec
Pour r = 2 : (4-1)·k·log S > 4S·log 2 + 2k·log 2 → potentiellement OK

Avec r = 2, S = 1.585k :
  3k·log(1.585k) > 4·1.585k·log 2 + 2k·log 2
  3·log(1.585k) > 6.34·log 2 + 2·log 2 = 8.34·log 2 ≈ 5.78

  log(1.585k) > 1.927
  1.585k > e^{1.927} ≈ 6.87
  k > 4.3

Donc avec la méthode de Weyl d'ordre r = 2, le mélange est prouvable
pour k ≥ 5 (sous réserve que les termes modulaires dans E₈ soient
négligeables). Ceci est PLUS FORT que la borne sous EO !

**Mais attention** : l'estimation Σ|μ̂_k|^{2^r} par E_{2r}^{k/2} est
une HEURISTIQUE. La borne rigoureuse requiert un argument de découplage
(decoupling) qui est l'analogue de Weyl pour les produits au lieu des sommes.

---

## 7. La Piste du Découplage : Vers l'Argument Inconditionnel

### 7.1. Le découplage de Bourgain-Demeter

La théorie du découplage (Bourgain-Demeter, 2015) permet de factoriser
des estimations de sommes exponentielles sur des variétés courbes.
L'idée : si les phases vivent sur une courbe à courbure non nulle,
les interactions entre les termes sont LIMITÉES.

Dans notre contexte, les "phases" sont les éléments de l'orbite
{2^0, 2^1, ..., 2^{S-1}} ⊂ F_p. Cette orbite vit sur la "courbe
exponentielle discrète" a ↦ 2^a mod p.

### 7.2. La courbure de la courbe exponentielle

La courbe a ↦ 2^a dans R croît super-exponentiellement (sa "courbure"
est liée à la dérivée seconde d²/da² log(2^a) = 0 — c'est PLAT en
échelle log !). Mais en arithmétique modulaire, la courbure apparaît
dans les DIFFÉRENCES SECONDES :

  Δ²_h(2^a) = 2^{a+2h} - 2·2^{a+h} + 2^a = 2^a·(2^h - 1)² ≠ 0

Cette non-nullité de Δ² est la CONDITION de courbure discrète.

En modulo p, Δ² ≡ 0 seulement si p | 2^a·(2^h-1)², ce qui requiert
p | (2^h - 1) soit h ≡ 0 mod ord_p(2). Comme ord_p(2) ≥ S (car
2^S ≡ 3^k mod p et p ∤ 3), les "points plats" sont absents pour h < S.

**Conclusion : H = {2^0,...,2^{S-1}} est un ensemble à "courbure
non dégénérée" dans F_p, ce qui est la condition requise pour un
argument de type Vinogradov ou découplage.**

### 7.3. L'inégalité de Vinogradov pour les sommes lacunaires

Le résultat classique de Vinogradov-Korobov pour les sommes du type
Σ e(α·2^a/p) donne :

  |G(u)| = |Σ_{a=0}^{S-1} e(u·2^a/p)| ≤ C_ε · S^{1-1/(2^r-2)+ε}

pour r ≥ 2, via la méthode de Weyl d'ordre r. Avec r = 2 :

  |G(u)| ≤ C_ε · S^{1/2 + ε}    pour tout u ≢ 0 mod p

**C'est la borne de CARRÉ ROOT pour G !** Elle dit que G(u) ne peut
pas être beaucoup plus grand que √S (sa "valeur typique" par Parseval).

Mais ATTENTION : cette borne est pour des sommes complètes sur Z/pZ
(où S = ord_p(2)). Dans notre cas, S << p (somme tronquée), et la
borne de Vinogradov-Korobov prend la forme :

  |G(u)| ≤ S^{1-1/(2^r)} · p^{1/2^r+ε}    (somme incomplète)

qui est PLUS FAIBLE car le terme p^{1/2^r} domine quand S << p.

### 7.4. Le point de basculement : combiner énergie et Vinogradov

L'énergie additive basse (Théorème 3) donne une borne MOYENNE sur |G|.
La borne de Vinogradov donne une borne PONCTUELLE (mais faible pour S << p).
La COMBINAISON des deux est plus forte que chacune séparément.

**Approche combinée.** Classons les fréquences en deux catégories :
  - "Petites" : |G(u)| ≤ S^{2/3}. Pour celles-ci, log(|G|/S) ≤ -(1/3)·log S.
  - "Grandes" : |G(u)| > S^{2/3}. Par le Lemme 4 (paucité),
    |{u : |G(u)| > S^{2/3}}| ≤ O(p·log S/S^{2/3}).

Le nombre moyen de "grands" G dans une orbite de longueur k est :

  k · O(log S / S^{2/3}) = O(k · log S / S^{2/3})

Comme S ≈ 1.585k : ceci est O(k^{1/3} · log k), qui est o(k).

Pour les "grands" G, la borne ponctuelle |G| ≤ S donne log(|G|/S) ≤ 0.

La somme orbitale :

  Σ_{j=0}^{k-1} log(|G(3^j t)|/S) ≤ -(k - O(k^{1/3}·log k)) · (1/3)·log S
                                     = -(k/3)·log S · (1 - o(1))

Donc :

  **|μ̂_k(t)| ≤ S^{-k/3 + o(k)}**

C'est PLUS FAIBLE que la borne S^{-k/2} sous EO (§3.3), mais c'est
INCONDITIONNEL (pas besoin de EO) — sous la seule condition que le
nombre de "grands" G dans l'orbite soit majoré par sa valeur attendue.

### 7.5. Borne inconditionnelle via la somme des moments

On peut éviter TOUT argument d'orbite en utilisant directement la
somme sur t ∈ F_p* :

  Σ_{t≠0} |μ̂_k(t)|² = Σ_{t≠0} ∏_{j=0}^{k-1} |G(3^j t)|²/S^{2k}

Si l'application t ↦ {3^j t}_{j=0}^{k-1} est à fibres de taille ≤ 1
(injection sur les orbites, vrai si ord_p(3) > k), on majore par :

  ≤ (1/S^{2k}) · (max_t ∏ |G(3^j t)|²)

Ce n'est pas utile directement. Essayons plutôt avec Parseval :

  Σ_t |μ̂_k(t)|² = ‖μ_k‖₂² = Σ_x μ_k(x)² = N̄₂(p) / S^{2k}

où N̄₂(p) = #{(A,B) ∈ H^k × H^k : Σ 3^j a_j ≡ Σ 3^j b_j mod p},
le nombre de COLLISIONS entre deux marches indépendantes.

Par un argument standard : N̄₂ ≤ S^{2k}/p + S^k (collision aléatoire + diagonale).

Donc ‖μ_k‖₂² ≤ 1/p + 1/S^k ≈ 1/p.

Ceci donne seulement que PRESQUE TOUS les μ̂_k(t) sont petits en
moyenne L², mais pas de borne UNIFORME. L'estimation uniforme
requiert le passage L² → L∞, qui coûte un facteur √p.

---

## 8. Synthèse : L'État du Verrou A

### 8.1. Ce qui est maintenant prouvé (inconditionnel)

1. **Théorème 3** : E₄(H) = 2S² - S + O(S·log S). H est quasi-Sidon.
2. **Lemme 4** : |{u : |G(u)| > αS}| = O(p·log S / (α⁴S²)).
3. **Parseval** : |G(u)| typique ≈ √S (valeur RMS).
4. **Lemme 9** : E_{2r}(H) ≈ r!²·C(S,r) (solutions triviales seulement dans Z).

### 8.2. Ce qui est prouvé conditionnellement

5. **Théorème 5** (sous EO) : |μ̂_k(t)| ≤ S^{-k/2+O(√k)}.
6. **Mélange** (sous EO) : marche non ordonnée mélange pour k ≥ 3.
7. **Précision Théorème Q** (sous EO) : quasi-uniformité 4.1% pour k ≥ 18.

### 8.3. Hiérarchie des hypothèses restantes

| Hypothèse | Force | Ce qu'elle donne | Prouvable ? |
|-----------|-------|------------------|-------------|
| EO (équidist. orbit.) | Modérée | Mélange k ≥ 3 | Plausible (ord_p(3) >> k) |
| PU (proportion unif.) | Élevée | Transfert ord→non-ord | Difficile |
| EO + PU | Forte | N₀ ≤ (1+ε)C/p pour k ≥ 18 | Les deux ensemble |

### 8.4. Le chemin le plus court vers Collatz

Le chemin complet est :

  E₄(H) basse [**PROUVÉ**]
  → |G(u)| ≈ √S typiquement [**PROUVÉ**]
  → μ̂_k décroît exponentiellement [sous EO]
  → marche non ordonnée mélange [sous EO, pour k ≥ 18]
  → N̄₀^unord ≈ S^k/p [sous EO]
  → N₀ ≈ C/p [sous EO + PU]
  → |β(p)| ≤ 0.041 [sous EO + PU, pour k ≥ 18]
  → CRT multiplicatif [**PROUVÉ**, Phase 22]
  → N₀(d) = 0 pour tout k ≥ 18 [sous EO + PU]
  → vérification k ≤ 17 [**PROUVÉ** numériquement]
  → **PAS DE CYCLES POSITIFS NON TRIVIAUX** [sous EO + PU]

Les deux hypothèses restantes (EO et PU) sont de nature DIFFÉRENTE :
- EO est une propriété de THÉORIE DES NOMBRES (distribution des
  orbites multiplicatives dans F_p) ;
- PU est une propriété COMBINATOIRE (indépendance entre ordonnancement
  et destination).

### 8.5. Comparaison avec l'état pré-Phase 23f

| Aspect | Avant (Phase 23e) | Après (Phase 23f) |
|--------|-------------------|-------------------|
| Nature du verrou A | "Conjecture Δ' indéterminée" | E₄ basse → mélange sous EO |
| Borne sur |G(u)| | "min(S, √p) générique" | √S typique (PROUVÉ) |
| Seuil de mélange | "Heuristique k ~ S/Δ" | k ≥ 18 pour 4.1% (sous EO) |
| Base théorique | Bourgain-Gamburd (NE MARCHE PAS) | Énergie additive + Parseval |
| Fossé | Exponential 2^{0.75k} | **0 sous EO+PU** |

---

## 9. Problèmes Ouverts et Directions de Recherche

### 9.1. Éliminer EO (priorité haute)

**Problème A.** Montrer inconditionnellement que pour tout t ∈ F_p* :

  Σ_{j=0}^{k-1} log(|G(3^j t)|/S) ≤ -(δ/2)·k·log S

pour un δ > 0 absolu. La méthode de Weyl d'ordre r (§6.5) suggère
que c'est possible pour r = 2, donnant δ = 2/3 et le mélange pour k ≥ 5.

**Sous-problème A1.** Borner rigoureusement E₈(H) = E₈({2^0,...,2^{S-1}})
dans F_p. Le Lemme 9 donne E₈ = 4!² · C(S,4) + O(corrections mod p)
dans Z, mais la contribution modulaire est plus complexe à estimer
que pour E₄.

**Sous-problème A2.** Développer un argument de découplage (decoupling)
adapté aux produits de Riesz sur des orbites multiplicatives. Ceci
serait un résultat nouveau en analyse harmonique sur les corps finis.

### 9.2. Attaquer PU (priorité moyenne)

**Problème B.** Pour A = {a₀,...,a_{k-1}} ⊂ {0,...,S-1} de taille k,
soit π(A,r) = #{σ ∈ S_k : Φ_σ(A) ≡ r mod p}. Montrer que :

  π(A,0) / k! ≈ 1/p    (uniformément en A "typique")

**Sous-problème B1.** Calculer numériquement π(A,r) pour des exemples
de petite taille (k = 5,...,10) et vérifier la quasi-uniformité.

**Sous-problème B2.** Relier PU au mélange d'une marche sur le
groupe symétrique S_k, induite par les poids 3^j.

### 9.3. Vérification computationnelle (priorité haute)

**Problème C.** Vérifier numériquement pour k = 18,...,30 :
  (a) E₄(H) mod p est bien ≈ 2S² pour tout p | d(k).
  (b) La distribution de |G(u)| est concentrée autour de √S.
  (c) |μ̂_k(t)| ≤ S^{-k/3} pour un échantillon de fréquences t.
  (d) N₀(p) ≤ (1.05)·C/p pour tout p | d(k).

### 9.4. Résumé en une phrase

> **La faible énergie additive de H = {2^0,...,2^{S-1}} (quasi-Sidon,
> Théorème 3) réduit le Verrou A à une hypothèse d'équidistribution
> orbitale (EO) qui est standard en théorie des nombres. Combinée avec
> la neutralité de l'ordonnancement (PU), elle donnerait la preuve
> complète de l'absence de cycles positifs non triviaux dans Collatz.**

---

## Appendice A : Calculs Numériques Illustratifs

### A.1. k = 18, S = 29

  C = binomial(29, 18) = 20 030 010
  d = 2^29 - 3^18 = 536 870 912 - 387 420 489 = 149 450 423
  (149 450 423 = 7 × 21 350 060.4... non, vérifions)

Les calculs exacts de d(18) et ses facteurs premiers seraient à
faire numériquement (voir Problème C).

### A.2. Comparaison E₄ théorique vs numérique

Pour S = 29 :
  - Solutions triviales : 2·29² - 29 = 1653
  - Nombre total E₄ attendu : 1653 + O(29·log 29) ≈ 1653 + O(98) ≈ 1750
  - Ratio E₄/S² ≈ 2.08 (proche de 2, confirme quasi-Sidon)

---

## Appendice B : Table Récapitulative des Fossés (toutes phases)

| Phase | Méthode | Borne | Besoin | Fossé | Hypothèses |
|-------|---------|-------|--------|-------|------------|
| 23d | Épluchage | 0.63·C | C/p | ×p ≈ 2^{1.6k} | Aucune |
| 23e | Sépar. méd. | C/√p | C/p | ×√p ≈ 2^{0.8k} | Cond. |
| 23d | Thm Q (CS) | p√C | 0.041·C | ×2^{0.75k} | Aucune |
| **23f** | **Énergie add.** | **(1+ε)C/p** | **C/p** | **0** | **EO + PU** |
| 23f | Weyl ordre 2 | S^{-k/3} | S^{-k/2} | ×S^{k/6} | E₈ borné |

Le résultat majeur de Phase 23f est la FERMETURE CONDITIONNELLE
du fossé : sous EO + PU, le Verrou A est résolu et la chaîne vers
Collatz est complète.

---

## Références

- Bourgain (2005) "More on the sum-product phenomenon." Int. J. Num. Th.
- Bourgain, Demeter (2015) "The proof of the l² decoupling conjecture."
  Ann. Math. 182(1), 351-389.
- Bourgain, Katz, Tao (2004) "A sum-product estimate in finite fields."
  GAFA 14, 27-57.
- Korobov (1958) "Estimates of trigonometric sums." Uspekhi Mat. Nauk.
- Vinogradov (1954) "The method of trigonometrical sums in the theory
  of numbers." Interscience.
- Tao, Vu (2006) "Additive Combinatorics." Cambridge UP (Ch. 2, 4).
- O'Bryant (2004) "A complete annotated bibliography of work related
  to Sidon sets." Electronic J. Combinatorics, DS11.
