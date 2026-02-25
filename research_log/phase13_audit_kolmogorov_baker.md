# Phase 13 — Audit de l'argument Baker-Kolmogorov

> **Date** : 2026-02-25
> **Statut** : RALPH REVIEW — Identification d'erreurs fatales dans les prémisses
> **Verdict** : L'argument est **invalide** dans sa forme actuelle.

---

## 0. RÉSUMÉ EXÉCUTIF

L'argument Baker-Kolmogorov propose que :
1. Baker borne n₀ ≤ k⁷ (taille binaire ≈ 7·log₂k bits)
2. L'entropie du chemin requiert γk bits encodés dans n₀
3. Pour k > 1500 : γk > 7·log₂k → contradiction

**Trois prémisses sont factuellement fausses :**

| Prémisse | Affirmation | Réalité | Erreur |
|----------|-------------|---------|--------|
| corrSum < 3^k | corrSum borné par 3^k | corrSum_max ≈ (3/2)^k · 3^k / 9 | Facteur (3/2)^k manquant |
| d > 3^k / k⁷ | Baker donne ce bound | Baker trivial pour k < 10000 | Constantes de Baker ignorées |
| n₀ ≤ k⁷ | Conséquence des deux | n₀_max ≈ 2^{0.585k} | **Exponentiel**, pas polynomial |

L'entier n₀ a **0.585k bits**, largement assez pour "encoder" les γk = 0.05k bits d'entropie. Le goulot d'étranglement informationnel **n'existe pas**.

---

## 1. ERREUR 1 : corrSum ≫ 3^k

### 1.1 L'affirmation

> "Puisque corrSum < 3^k, on a obligatoirement n₀ ≤ k⁷."

### 1.2 Le calcul réel

La somme correctrice de Steiner est :

$$\text{corrSum} = \sum_{i=0}^{k-1} 3^{k-1-i} \cdot 2^{A_i}$$

avec $A_0 = 0$ et $\sum A_i = S - k$.

**Si tous les A_i étaient 0** : corrSum = (3^k − 1)/2 ≈ 3^k/2 (OK, < 3^k).

**Mais les A_i ne sont PAS tous 0 !** Leur somme vaut S − k ≈ 0.585k.

Le **maximum** de corrSum est atteint en concentrant toute la "masse" sur
un seul terme. En posant A₁ = S − k (et les autres = 0 sauf A₀ = 0) :

$$\text{corrSum}_{max} \approx 3^{k-2} \cdot 2^{S-k}$$

Le facteur clé : 2^{S-k} = 2^{0.585k} = (3/2)^k exactement (car
2^{log₂(3/2)} = 3/2 et S−k ≈ k·(log₂3−1) = k·log₂(3/2)).

Donc :

$$\text{corrSum}_{max} \approx \frac{3^k \cdot (3/2)^k}{9} \gg 3^k$$

### 1.3 Vérification numérique

| k | S | corrSum_max / 3^k | Factor |
|---|---|-------------------|--------|
| 5 | 8 | 0.89 | < 1 (exception) |
| 12 | 19 | 14.2 | ≫ 1 |
| 41 | 65 | 1,864,135 | ≫ 1 |
| 306 | 485 | ≈ 10^{50} | astronomique |

**Pour k = 41** : corrSum_max ≈ 6.8 × 10²⁵ tandis que 3⁴¹ ≈ 3.6 × 10¹⁹.
Le rapport est ≈ 1.86 million.

### 1.4 Source de l'erreur

L'intuition "corrSum ≈ 3^k" vient de la géométrie de la somme Σ 3^{k-1-i}
qui est effectivement ≈ 3^k/2. Mais les facteurs **2^{A_i}** multiplient
exponentiellement certains termes. La somme correctrice n'est PAS une
"correction modeste" de 3^k — elle peut être exponentiellement plus grande.

---

## 2. ERREUR 2 : La borne de Baker est triviale pour k modéré

### 2.1 L'affirmation

> "Par les formes linéaires de logarithmes, d_n > 3^k / k⁷."

### 2.2 Les vraies constantes de Baker

Le meilleur résultat effectif pour deux logarithmes (Laurent-Mignotte-
Nesterenko, 1995, Corollaire 2) donne :

$$\log|\Lambda| \geq -24.34 \cdot h_1 \cdot h_2 \cdot \max(\log b' + 0.14,\; 21)^2$$

avec $h_1 = 1$, $h_2 = \log 3 \approx 1.099$, $b' \approx 2.443k$.

Pour k < e^{20.86} ≈ 10⁹ : le max vaut **21** (constante !), donc :

$$\log|\Lambda| \geq -24.34 \times 1.099 \times 441 \approx -11\,793$$

Cela donne : $d \geq 3^k \cdot e^{-11793}$.

Or $3^k > e^{11793}$ seulement quand $k > 11793/\log 3 \approx 10\,739$.

**Pour k < 10739 : la borne de Baker est triviale** (elle dit juste d ≥ 1,
ce que nous savons déjà).

### 2.3 Vérification numérique

| k | log₂(d) Baker | log₂(d) réel | Baker utile ? |
|---|---------------|-------------|---------------|
| 41 | −16,948 | 58.5 | NON |
| 306 | −16,528 | 475.1 | NON |
| 1500 | −14,636 | 2376 | NON |
| 5000 | −9,088 | 7922 | NON |
| 15601 | +7,714 | 24711 | OUI (enfin !) |

Baker ne devient utile qu'à partir de k ≈ 10,000.

### 2.4 Source de l'erreur

Le facteur "k⁷" correspond à un **exposant d'irrationalité** de log₂3,
qui serait valide si log₂3 était un nombre algébrique de type diophantien
connu. Mais :
- L'exposant d'irrationalité de log₂3 est **inconnu** (conjecturé = 2)
- Baker ne donne pas d > 3^k/k⁷ mais d > 3^k · e^{−C·(log k)²}
- Les constantes de Baker sont **énormes** (C ≈ 11,793 pour le terme constant)

---

## 3. ERREUR 3 : n₀ est exponentiel, pas polynomial

### 3.1 Conséquence des erreurs 1 et 2

Puisque corrSum_max ≈ 3^{k-2} · 2^{S-k} et d ≈ 3^k / q_{n+1} :

$$n_{0,max} = \frac{\text{corrSum}_{max}}{d} \approx \frac{2^{S-k} \cdot q_{n+1}}{9}$$

La taille binaire de n₀ est :

$$\text{bits}(n_0) \approx (S - k) + \log_2(q_{n+1}) \approx 0.585k + O(\log k)$$

C'est **exponentiel en k** (le terme dominant est 0.585k).

### 3.2 Vérification

| k | S | bits(n₀_max) | 7·log₂(k) | n₀ ≤ k⁷ ? |
|---|---|-------------|-----------|-----------|
| 5 | 8 | 4.1 | 16.3 | ✓ |
| 41 | 65 | 27.3 | 37.5 | ✓ (par chance) |
| 306 | 485 | **185.8** | 57.8 | **✗** |
| 15601 | 24727 | **9138.6** | 97.5 | **✗** |

Pour k = 306 : n₀ a 186 bits, mais l'argument prétend qu'il en a au plus 58.
C'est faux d'un facteur **3.2×**.

---

## 4. POURQUOI L'ARGUMENT INFORMATIONNEL EST INVALIDE

### 4.1 L'absence de goulot d'étranglement

L'argument dit : "n₀ doit encoder γk = 0.05k bits d'entropie."

Or n₀ a 0.585k bits disponibles. Puisque **0.585k ≫ 0.05k**,
n₀ a largement assez de "capacité informationnelle" pour porter
toute l'entropie du chemin. Il n'y a aucun conflit.

### 4.2 L'erreur conceptuelle plus profonde

Même si n₀ était "petit", l'argument confond deux choses :

- **Existence** : il existe une composition A avec corrSum(A) = n₀ · d
- **Spécification** : on peut identifier cette composition à partir de n₀

Pour qu'un cycle existe, on a besoin d'**existence**, pas de spécification.
n₀ n'a pas besoin d'"encoder" le chemin — il suffit que le nombre n₀ · d
tombe dans l'image de la fonction corrSum.

C'est comme dire : "le nombre 12 encode-t-il l'information de sa
factorisation 2² × 3 ?" Non — 12 existe indépendamment de notre
capacité à le factoriser.

### 4.3 Ce que donnerait la version correcte

Si on formalise correctement l'argument comme un **problème de comptage** :

- Nombre de candidats n₀ : N = corrSum_max/d ≈ 2^{0.585k}
- Fraction de résidus mod d atteints : ≤ C/d ≈ 2^{−0.079k}
- Nombre espéré de succès : N × (C/d) × (1/N) = C/d

On retombe exactement sur le rapport **C/d** de la Phase 12.
L'argument de Baker-Kolmogorov, correctement formalisé, **ne fait que
reproduire la borne C/d < 1** sans rien ajouter de nouveau.

---

## 5. CE QUI RESTE VRAI ET INTÉRESSANT

### 5.1 L'intuition est correcte (mais le mécanisme est différent)

Il y a bien une tension entre "l'entropie" des compositions et
la "capacité" du module d. C'est exactement ce que capture notre
constante γ = 0.0500. Mais cette tension s'exprime via le rapport
C/d (Théorème 12.1), pas via un goulot informationnel sur n₀.

### 5.2 Baker POURRAIT aider (mais pas de cette façon)

Baker aide dans la méthodologie Simons-de Weger :
1. Baker donne une borne initiale grossière : k < K_Baker (~10¹⁵)
2. LLL réduit cette borne : k < K_LLL (~10⁴)
3. Calcul direct élimine : k < 68

Si on pouvait **étendre l'étape 3** (calcul direct) à k < K₀ (notre
seuil de non-surjectivité), la boucle serait fermée... mais K₀ = 18,
et 18 < 68, donc Simons-de Weger couvre déjà la zone !

Le **vrai problème** n'est pas le seuil K₀ mais la différence entre
non-surjectivité (prouvée) et exclusion de 0 (conditionnelle sur H).

---

## 6. ÉTAT HONNÊTE DE LA PREUVE

```
┌─────────────────────────────────────────────────────────┐
│                  ÉTAT AU 2026-02-25                      │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  INCONDITIONNEL:                                        │
│    ✓ Pas de cycle positif avec k < 68 (Simons-de Weger)│
│    ✓ Ev_d non surjective pour k ≥ 18 (Phase 12)        │
│    ✓ γ = 0.0500 (gap entropie-module)                  │
│    ✓ C/d → 0 exponentiellement (Phase 11C)             │
│                                                         │
│  CONDITIONNEL (sur H):                                  │
│    ○ 0 ∉ Im(Ev_d) pour k ≥ 68                          │
│    ○ Aucun cycle positif n'existe                       │
│                                                         │
│  RÉFUTÉ AUJOURD'HUI:                                    │
│    ✗ corrSum < 3^k (FAUX)                               │
│    ✗ d > 3^k / k⁷ via Baker (Baker trivial pour k<10⁴) │
│    ✗ n₀ ≤ k⁷ (FAUX, n₀ est exponentiel)               │
│    ✗ Argument Kolmogorov-Baker (prémisses fausses)      │
│                                                         │
│  LE GAP QUI RESTE:                                      │
│    Prouver 0 ∉ Im(Ev_d) sans hypothèse (H)             │
│    ← Ceci est le problème ouvert fondamental            │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

---

## 7. PISTES POUR FERMER LE GAP

### 7.1 Piste A : Sommes exponentielles (Weil/Deligne)

Borner |Σ_A χ(corrSum(A))| pour les caractères χ mod p | d.
Si cette somme est o(C), alors l'image de Ev_p est "quasi-uniforme"
et (H) est prouvée. Le défi : la fonction corrSum mélange 3^i et 2^{A_i}
de façon non-polynomiale, hors portée des bornes de Weil standard.

### 7.2 Piste B : Propagation de Horner

Exploiter la récurrence corrSum ≡ 3 · corrSum_{k-1} + 2^{A_{k-1}} (mod p).
La quasi-injectivité de Horner (Théorème 11C.2) montre que pour les
grands premiers p | d, chaque étape est "presque injective".
Si on peut borner l'accumulation des collisions sur k étapes,
on obtient (H) pour les grands premiers.

### 7.3 Piste C : Extension computationnelle de Simons-de Weger

Étendre leur méthodologie au-delà de k < 68. Avec le matériel moderne
(GPU, calcul distribué), il pourrait être possible d'atteindre k < 500
ou même k < 1000. Combiné avec notre borne C/d (qui est très forte
pour k > 306), cela réduirait le gap conditionnel.

### 7.4 Piste D : Combinaison Baker-LLL affinée

Utiliser la réduction LLL pour affiner la borne de Baker sur chaque
convergent individuellement. Pour q₇ (k=306), cela donnerait une
borne beaucoup plus serrée sur n₀, potentiellement suffisante pour
un calcul exhaustif des candidats n₀ · d ∈ Im(corrSum).

---

*Phase 13 — Audit Ralph : argument Baker-Kolmogorov réfuté. Le gap conditionnel
sur (H) reste le problème ouvert fondamental.*
