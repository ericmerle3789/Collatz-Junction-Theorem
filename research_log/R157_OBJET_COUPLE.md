# R157 — OBJET COUPLÉ (h, h-1) : DÉCOMPOSITION BILINÉAIRE ET ÉNERGIE MIXTE

**Date** : 15 mars 2026
**Type** : Investigation autonome — front unique
**Front retenu** : Objet couplé (h, h-1)
**Méthode** : TAN véritablement nouveau — séparation des variables entre Z/rZ et F_p*

---

## 0. POURQUOI CE FRONT EST LÉGITIME

### Ce que T175/T176 ont tué
- Double contrainte add+mult sur les MÊMES 4-tuples dans F_p* → dégénéré
- Double contrainte mult+mult(translaté) sur les MÊMES 4-tuples dans F_p* → dégénéré
- Raison : (σ₁, σ₂) = (somme, produit) est une bijection sur les paires → force {h₃,h₄}={h₁,h₂}

### Ce que T175/T176 n'ont PAS tué
- Des contraintes sur des structures DIFFÉRENTES, reliées par une application non linéaire
- Spécifiquement : contrainte additive dans Z/rZ (espace des indices) + contrainte multiplicative dans F_p* (espace des valeurs)

### L'application non linéaire qui relie les deux
Le pont entre Z/rZ et F_p* est l'APPLICATION EXPONENTIELLE :

φ : Z/rZ → F_p*,  a ↦ 1 - 2^a mod p

C'est le cœur du problème Collatz : l'ensemble H-1 = {1-2^a : a = 0,...,r-1} est l'IMAGE de cette application.

---

## 1. L'OBJET : FORME BILINÉAIRE B(s,t)

### Définition

B(s,t) = Σ_{a=1}^{r-1} e^{2πisa/r} · χ^{tr}(1-2^a)

- Le premier facteur e^{2πisa/r} est un CARACTÈRE ADDITIF de Z/rZ évalué en a
- Le second facteur χ^{tr}(1-2^a) est un CARACTÈRE MULTIPLICATIF de F_p* évalué en 1-2^a
- B mélange les deux structures via le pont a ↦ 1-2^a

### Lien avec S_H

S_H(t) = Σ_{a=1}^{r-1} χ^{tr}(1-2^a) = B(0, t)

Notre somme S_H est le MODE s=0 de la forme bilinéaire B. C'est le terme constant de la décomposition de Fourier de la fonction a ↦ χ^{tr}(1-2^a) sur le groupe Z/rZ.

### Parseval sur Z/rZ

Σ_{s=0}^{r-1} |B(s,t)|² = r · Σ_{a=1}^{r-1} |χ^{tr}(1-2^a)|² = r(r-1)

Puisque |χ^{tr}(1-2^a)| = 1 pour tout a.

Donc : |S_H(t)|² = |B(0,t)|² ≤ Σ_s |B(s,t)|² = r(r-1)

Ce qui donne |S_H(t)| ≤ √(r(r-1)) ≈ r — c'est la borne TRIVIALE, pas de gain.

### 4ème moment sur Z/rZ

Σ_{s=0}^{r-1} |B(s,t)|⁴ = r · Σ_{a₁+a₂≡a₃+a₄ mod r} χ^{tr}((1-2^{a₁})(1-2^{a₂}) / ((1-2^{a₃})(1-2^{a₄})))

= r · [E_triv + Σ_{non-trivial} χ^{tr}(Q(a₁,a₂,a₃,a₄))]

où Q = (1-2^{a₁})(1-2^{a₂}) / ((1-2^{a₃})(1-2^{a₄})).

---

## 2. L'ÉNERGIE MIXTE E_mixed

### Définition

E_mixed(H,p) = #{(a₁,a₂,a₃,a₄) ∈ {1,...,r-1}⁴ :
  a₁+a₂ ≡ a₃+a₄ mod r  [contrainte ADDITIVE dans Z/rZ]
  ET  (1-2^{a₁})(1-2^{a₂}) = (1-2^{a₃})(1-2^{a₄})  [contrainte MULTIPLICATIVE dans F_p*]}

### Hypothèse initiale : pourquoi ce ne serait PAS tué par T175/T176

T175/T176 tuent les double contraintes sur le MÊME espace. Ici :
- La contrainte additive vit dans Z/rZ (les indices a_j)
- La contrainte multiplicative vit dans F_p* (les valeurs 1-2^{a_j})
- Le pont entre les deux est l'application φ(a) = 1-2^a, qui est NON LINÉAIRE

L'hypothèse était que les deux contraintes ne se "simplifient" pas l'une dans l'autre parce qu'elles vivent dans des structures algébriques DIFFÉRENTES.

**CETTE HYPOTHÈSE EST FAUSSE.** Voir §3 (T177).

### Décomposition

E_mixed = E_trivial + N_cross

où E_trivial = 2(r-1)² - (r-1) (permutations {a₃,a₄} = {a₁,a₂})
et N_cross = collisions NON TRIVIALES (quadruples avec {a₃,a₄} ≠ {a₁,a₂})

### Connexion au verrou

Par la borne du 4ème moment :

|S_H(t)|⁴ ≤ Σ_s |B(s,t)|⁴ / r^?

Non, plus précisément : |B(0,t)|⁴ ≤ (Σ_s |B(s,t)|⁴) × (1/r)^?

En fait, par Cauchy-Schwarz dans un sens spécifique, ou simplement par :

|S_H(t)|⁴ = |B(0,t)|⁴ ≤ max_s |B(s,t)|² · Σ_s |B(s,t)|² = max_s |B(s,t)|² · r(r-1)

Ce n'est pas directement utile. Utilisons plutôt le moment 4 pur :

Σ_{t} |S_H(t)|⁴ = M₄(S_H) ≈ (p-1) · E^×(H-1) [c'est T171]

Ce que la forme bilinéaire apporte est une DÉCOMPOSITION de M₄ en composantes modales :

Σ_t |B(s,t)|⁴ dépend de s, et pour s=0 c'est Σ_t |S_H(t)|⁴ = M₄.

La vraie connexion est :

Si E_mixed est petit (disons O(r^{2-δ})), alors la restriction du 4ème moment de B aux quadruples additifs avec collision multiplicative est petite, ce qui borne le 4ème moment TOTAL et donc max|S_H|.

---

## 3. VÉRIFICATION NUMÉRIQUE ET KILL

### Résultat numérique

| p | r | E_mixed | E_trivial | N_cross | N_cross/(r-1)² |
|---|---|---------|-----------|---------|----------------|
| 31 | 5 | 28 | 28 | **0** | 0 |
| 89 | 11 | 190 | 190 | **0** | 0 |
| 127 | 7 | 66 | 66 | **0** | 0 |
| 257 | 16 | 435 | 435 | **0** | 0 |
| 521 | 260 | 133903 | 133903 | **0** | 0 |
| 1031 | 515 | 527878 | 527878 | **0** | 0 |
| 8191 | 13 | 276 | 276 | **0** | 0 |

**N_cross = 0 pour TOUS les premiers testés.** La double contrainte est purement triviale.

### Preuve algébrique : Théorème T177

**Théorème T177** (Dégénérescence de E_mixed via l'homomorphisme exponentiel).

Pour tout premier p et H = ⟨2⟩ ⊂ F_p* d'ordre r, l'énergie mixte satisfait :

**E_mixed = E_trivial = (r-1)(2r-3), N_cross = 0.**

**Preuve.** Les deux contraintes sont :
- (ADD) a₃ + a₄ ≡ a₁ + a₂ mod r
- (MULT) (1-2^{a₃})(1-2^{a₄}) = (1-2^{a₁})(1-2^{a₂}) dans F_p*

Posons s = a₁ + a₂ mod r. Par (ADD), a₄ = s - a₃ mod r.

Développons (MULT) :
1 - 2^{a₃} - 2^{a₄} + 2^{a₃+a₄} = 1 - 2^{a₁} - 2^{a₂} + 2^{a₁+a₂}

Puisque a₃+a₄ ≡ s ≡ a₁+a₂ mod r, les termes 2^{a₃+a₄} et 2^{a₁+a₂} s'annulent :

**2^{a₃} + 2^{s-a₃} = 2^{a₁} + 2^{a₂}**

Posons x = 2^{a₃}, y = 2^{s-a₃}. On a :
- x + y = 2^{a₁} + 2^{a₂} (somme)
- x · y = 2^s = 2^{a₁} · 2^{a₂} (produit — automatique car s = a₁+a₂)

Par Vieta, {x, y} = {2^{a₁}, 2^{a₂}} comme multiensemble. Puisque a ↦ 2^a est injective (ordre r), {a₃, a₄} = {a₁, a₂}. QED.

### Diagnostic : pourquoi l'hypothèse de séparation était fausse

**Le pont a ↦ 2^a n'est PAS une "application non linéaire quelconque" — c'est un HOMOMORPHISME DE GROUPES** de (Z/rZ, +) vers (H, ×).

Conséquence fatale : la contrainte additive a₃+a₄ ≡ a₁+a₂ dans Z/rZ se TRADUIT automatiquement en contrainte multiplicative 2^{a₃}·2^{a₄} = 2^{a₁}·2^{a₂} dans H. Combinée avec la contrainte sur les (1-2^{aⱼ}), le développement fait apparaître les fonctions symétriques élémentaires des 2^{aⱼ}, qui déterminent le multiensemble {a₃,a₄} = {a₁,a₂}.

**C'est T175 en déguisement.** La "séparation des variables" entre Z/rZ et F_p* est illusoire quand le pont est un homomorphisme.

### Leçon T177 (archivée)

**TOUTE double contrainte couplant Z/rZ et F_p* via l'exponentielle a ↦ 2^a se réduit à une contrainte unique**, parce que l'homomorphisme transforme automatiquement la contrainte additive en contrainte multiplicative.

**Pour obtenir une vraie séparation**, il faudrait un pont qui n'est PAS un homomorphisme — c'est-à-dire une application a ↦ f(a) telle que f(a+b) ≠ f(a)·f(b) en général. L'application a ↦ 1-2^a est la composition de l'homomorphisme a ↦ 2^a avec la translation h ↦ 1-h, mais cette translation ne rompt pas la structure : le développement du produit fait réapparaître les fonctions symétriques de {2^{aⱼ}}.

---

## 4. KILL SWITCHES ET VERDICT

### Kill switches déclenchés

- **KS4 (vacuité générique)** : DÉCLENCHÉ — E_mixed = (r-1)(2r-3) pour TOUT sous-groupe H de TOUT corps. Aucune arithmétique de H n'intervient.
- **KS5 (instanciation triviale)** : DÉCLENCHÉ — identique à T175.
- **KS6 (redondance structurelle)** : DÉCLENCHÉ — T177 est la même dégénérescence que T175, causée par le même mécanisme (fonctions symétriques élémentaires).

### Verdict : **[ÉLIMINÉ]**

L'objet couplé (h, h-1) via la forme bilinéaire B(s,t) et l'énergie mixte E_mixed est **mort**. La séparation des variables entre Z/rZ et F_p* est illusoire quand le pont est l'homomorphisme exponentiel.

### Morts confirmés ajoutés

| Objet | Statut | Kill |
|-------|--------|------|
| B(s,t) forme bilinéaire | [MORT] | T177 — même dégénérescence que T175 |
| E_mixed énergie add-mult séparée | [MORT] | T177 — N_cross = 0 universellement |
| Séparation Z/rZ ↔ F_p* via 2^a | [MORT] | Pont = homomorphisme → pas de séparation réelle |

---

## 5. LEÇON PROFONDE — CE QUE T175+T176+T177 TUENT COLLECTIVEMENT

### Le pattern commun

T175 : double contrainte add+mult sur F_p* (mêmes variables) → dégénéré
T176 : double contrainte mult+mult(translaté) sur F_p* (mêmes variables) → dégénéré
T177 : double contrainte add(Z/rZ)+mult(F_p*) sur variables "séparées" → dégénéré

**La raison commune** : dans les trois cas, les deux contraintes déterminent les fonctions symétriques élémentaires (σ₁, σ₂) = (somme, produit) des éléments d'une paire, ce qui fixe la paire elle-même (dans un corps, un polynôme de degré 2 a au plus 2 racines).

### Ce qui reste

Pour échapper à cette dégénérescence, il faudrait :
1. Des contraintes impliquant **plus de 2 fonctions symétriques** (k-tuples avec k ≥ 3, pas juste des paires)
2. Des contraintes sur des objets **sans structure de groupe** (pas via un homomorphisme)
3. Des objets qui **ne se réduisent pas à des 4-tuples** (géométrie algébrique, faisceaux, etc.)

Aucune de ces trois directions n'est actuellement accessible dans le régime r ≈ log p.

---

## 6. REGISTRE FAIL-CLOSED FINAL

| Objet | Statut |
|-------|--------|
| B(s,t) = Σ e^{2πisa/r} · χ^{tr}(1-2^a) | [MORT] — T177, Parseval donne borne triviale, énergie mixte dégénérée |
| E_mixed (énergie add-mult séparée) | [MORT] — T177, N_cross = 0 universellement |
| Séparation Z/rZ ↔ F_p* via exponentielle | [MORT] — pont = homomorphisme, pas de séparation réelle |
| T177 (dégénérescence via homomorphisme) | [OBJET RÉEL] — théorème prouvé (5 lignes) |
| Front objet couplé (h, h-1) | **[FERMÉ]** — aucun objet bilinéaire/énergie sur ce couplage ne survit |
| Suspension recherche pure Bloc 3 | **MAINTENUE (7ème : R141, R151, R152, R153, R154, R155, R157)** |

**IVS** : 1.5/10 (résultat négatif propre mais plus de front ouvert)

---

## 7. RECOMMANDATION STRATÉGIQUE

**Le front "objet couplé (h, h-1)" est FERMÉ.**

Les trois théorèmes de dégénérescence T175/T176/T177 tuent collectivement toute approche par double contrainte sur des 4-tuples, que les contraintes vivent dans le même espace ou dans des espaces différents reliés par l'homomorphisme exponentiel.

**Condition de réouverture** :
- Identification d'un pont non-homomorphique entre deux structures (aucun connu)
- OU résultat extérieur sur les sommes d'exponentielles composées (Korobov, Bourgain-Gamburd étendu)
- OU outil de géométrie algébrique qui transcende les contraintes polynomiales sur les 4-tuples
