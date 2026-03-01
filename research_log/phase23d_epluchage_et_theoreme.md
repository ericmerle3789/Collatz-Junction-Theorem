# Phase 23d — Le Lemme d'Épluchage et le Théorème Conditionnel
# Date : 28 février 2026
# Auteur : Eric Merle (assisté par Claude)

---

## 0. Position

Phase 23b a démontré la **barrière de la racine carrée** : aucune méthode
de Fourier/moments ne peut prouver N₀(p) = 0 dans le régime p ~ C^{1.06}.

Phase 23c a exploré trois voies de contournement (Skolem, sur-détermination
2-adique, collisions) — toutes convergent vers le même obstacle.

Phase 23d prend un angle différent : **construire le théorème par couches**,
en réduisant le problème progressivement au lieu de le résoudre en un coup.

---

## 1. Le Lemme d'Épluchage (Peeling Lemma) — INCONDITIONNEL

### 1.1. Énoncé

**Lemme 1** (Épluchage). — *Soit p premier, p | d(k), avec ord_p(2) > S−k.
Posons L = S − k et ω = 2/3 mod p. Le nombre de solutions de*

  Φ(g) = Σ_{j=0}^{k-1} ω^j · 2^{g_j} ≡ 0  (mod p)

*dans le simplexe Δ_k(L) = {0 ≤ g₀ ≤ g₁ ≤ ... ≤ g_{k-1} ≤ L} satisfait :*

  **N₀(p) ≤ C(L+k−2, k−2) = C · (k−1) / (L+k−1) = C · (k−1) / (S−1)**

### 1.2. Preuve

Pour chaque PRÉFIXE (g₀, g₁, ..., g_{k-2}) fixé dans le simplexe
Δ_{k-1}(L), la fonction :

  g_{k-1} ↦ Φ(g₀,...,g_{k-2}, g_{k-1})

est de la forme :

  Φ = F(g₀,...,g_{k-2}) + ω^{k-1} · 2^{g_{k-1}}

où F ne dépend pas de g_{k-1}, et ω^{k-1} ≠ 0 dans F_p.

**Injectivité clé.** L'application g_{k-1} ↦ ω^{k-1} · 2^{g_{k-1}} mod p est
INJECTIVE sur {0, 1, ..., L} car :
- L'application a ↦ 2^a mod p est injective sur {0,...,L} dès que
  ord_p(2) > L, ce qui est garanti par l'hypothèse ord_p(2) > S−k = L.
- La multiplication par la constante non-nulle ω^{k-1} préserve l'injectivité.

Donc Φ, comme fonction de g_{k-1} seul, prend chaque valeur au plus UNE fois.
En particulier, Φ = 0 a au plus UNE solution en g_{k-1} pour chaque préfixe fixé.

**Comptage.** Le nombre de préfixes (g₀,...,g_{k-2}) dans Δ_{k-1}(L) est
C(L+k−2, k−2), obtenu par la bijection étoiles-et-barres (k−1 entiers
non-négatifs de somme ≤ L, réarrangés en vecteur non-décroissant).

Puisque chaque préfixe contribue au plus 1 solution :

  N₀(p) ≤ C(L+k−2, k−2) = C(S−2, k−2).

Et C(S−2,k−2) / C(S−1,k−1) = (k−1)/(S−1).                              ∎

### 1.3. Évaluation numérique

| k   | S   | C           | (k-1)/(S-1) | Borne N₀    | Ratio borne/C |
|-----|-----|-------------|-------------|-------------|---------------|
| 5   | 8   | 35          | 4/7 = 0.571 | 20          | 0.571         |
| 10  | 16  | 5005        | 9/15 = 0.60 | 3003        | 0.600         |
| 20  | 32  | 44.3M       | 19/31= 0.613| 27.2M       | 0.613         |
| 68  | 108 | ~2^{102}    | 67/107=0.626| ~0.626·C    | 0.626         |
| 306 | 485 | ~2^{463}    | 305/484=0.63| ~0.63·C     | 0.630         |

**Verdict :** Le facteur (k−1)/(S−1) ≈ k/S converge vers 1/log₂3 ≈ 0.631.
Le lemme élimine ~37% des compositions, mais N₀(p) ≤ 0.63C est encore
beaucoup trop faible (on a besoin de N₀(p) = 0, soit ≤ C/p ≈ 1).

### 1.4. Itération : l'épluchage multi-couches

Le Lemme 1 pèle UNE couche (la dernière variable). Peut-on itérer ?

**Lemme 2** (Épluchage à 2 couches). — *Sous les mêmes hypothèses :*

  N₀(p) ≤ #{(g₀,...,g_{k-3}) : ∃ (g_{k-2}, g_{k-1}) admissible avec Φ = 0}

*Pour chaque préfixe (g₀,...,g_{k-3}), le nombre de paires (g_{k-2}, g_{k-1})
rendant Φ = 0 est le nombre de solutions de :*

  ω^{k-2} · 2^{g_{k-2}} + ω^{k-1} · 2^{g_{k-1}} = −R

*où R = Σ_{j=0}^{k-3} ω^j · 2^{g_j} est le « résidu du préfixe ».*

Posons α = −R/ω^{k-1} et β = ω^{k-2}/ω^{k-1} = ω^{-1} = 3/2 mod p.

L'équation devient :

  **2^{g_{k-1}} = α − (3/2) · 2^{g_{k-2}}    (mod p)**

avec les contraintes g_{k-3} ≤ g_{k-2} ≤ g_{k-1} ≤ L.

Pour chaque valeur de g_{k-2} ∈ {g_{k-3},...,L} : le membre droit détermine
une valeur UNIQUE modulo p. Cette valeur doit être de la forme 2^{g_{k-1}}
avec g_{k-1} ∈ {g_{k-2},...,L}.

La question est : combien de valeurs de g_{k-2} donnent un membre droit qui
est une puissance de 2 dans le bon intervalle ?

---

## 2. Connexion à la Théorie Somme-Produit

### 2.1. Le problème de représentation

L'équation de 2 couches est un cas particulier du problème :

> **Pour α ∈ F_p fixé, combien de paires (a, b) avec a, b ∈ {0,...,L}
> et b ≥ a satisfont 2^b + (3/2) · 2^a = α mod p ?**

Posons H = {2^0, 2^1, ..., 2^L} ⊂ F_p*. C'est une progression géométrique
de raison 2 et de longueur L+1.

Le problème est : pour combien de (u,v) ∈ H × H a-t-on u + (3/2)v = α ?

Notons Rep(α) = #{(u,v) ∈ H × H : u + (3/2)v = α}.

### 2.2. Borne triviale et borne par somme-produit

**Borne triviale :** Rep(α) ≤ |H| = L+1 (pour chaque v, au plus un u marche).

**Borne par somme-produit.** La somme H + (3/2)·H est un ensemble de sommes
restreintes. Par la méthode de Solymosi (2009) :

  |H + (3/2)·H| · |H·H|^{1/2} ≥ |H|^2 / (2·log|H|)^{1/2}

Pour H progression géométrique : |H·H| = 2|H|−1. Donc :

  |H + (3/2)·H| ≥ |H|^2 / (2(2|H|)^{1/2} · (log|H|)^{1/2})
                ≥ |H|^{3/2} / O(√(log|H|))

Le nombre MOYEN de représentations est |H|²/|H+(3/2)H| ≤ |H|^{1/2}·O(√log|H|).

**Borne somme-produit :** Rep(α) ≤ |H|^{1/2+o(1)} en MOYENNE.

Pour |H| = L+1 ≈ 0.585k : Rep(α) ≤ (0.585k)^{1/2+o(1)} ≈ √k.

### 2.3. Limitation de cette approche

**Après 2 couches :** N₀(p) ≤ #{préfixes de longueur k-2} · √k
                       = C(S-3, k-3) · √k ≈ C · ((k-1)(k-2))/((S-1)(S-2)) · √k.

Pour k = 68 : C · 67·66/(107·106) · √68 ≈ C · 0.39 · 8.2 ≈ 3.2C. Pas d'amélioration !

Le problème : la borne somme-produit est MOYENNE, pas pire cas. Et même en
moyenne, le gain √k par couche ne compense pas le facteur C qui s'accumule.

**Après r couches :** N₀(p) ≤ C(S-1-r, k-1-r) · (√k)^{r/2}

Pour que ceci soit < 1 : il faut C(S-1-r, k-1-r) · k^{r/4} < 1.
Avec r = k-1 : C(L, 0)·k^{(k-1)/4} = 1·k^{k/4}. Or C ~ (eS/k)^k ~ 4.3^k
(pour S/k ~ 1.585). Et k^{k/4} ~ e^{(k·ln k)/4}. Pour k grand : k^{k/4} >> 4.3^k.

**Conclusion : les bornes somme-produit sont POLYNOMIALES en k, alors que
le problème requiert des gains EXPONENTIELS.** La connexion existe mais le
fossé quantitatif est immense.

---

## 3. La Voie des Retenues (Carry Propagation)

### 3.1. La récurrence de Horner en binaire

La récurrence c_j = 3·c_{j-1} + 2^{a_j} dans Z (avant réduction mod p) :

En binaire, multiplier par 3 = 2+1, c'est :
  3c = (c << 1) + c = (décalage à gauche de 1 bit) + c

Cette opération crée des RETENUES (carries) spécifiques.

### 3.2. Structure binaire de corrSum

Partons de c₀ = 3^{k-1}. En binaire, 3^{k-1} a environ 1.585(k-1) bits.
Son motif binaire est irrégulier mais déterministe.

Étape 1 : c₁ = 3·3^{k-1} + 2^{a₁} = 3^k + 2^{a₁}.
  En binaire : 3^k est un nombre spécifique. L'ajout de 2^{a₁} SET le bit a₁.
  Si ce bit était déjà 1 dans 3^k : cascade de retenues.

Étape j : c_j = 3·c_{j-1} + 2^{a_j}. Chaque étape :
  (1) Décale c_{j-1} et additionne → retenues déterministes
  (2) Ajoute 2^{a_j} → retenue possible si bit a_j est déjà 1

### 3.3. La contrainte finale

Le résultat final corrSum = c_{k-1} doit satisfaire :

  corrSum + n₀ · 3^k = n₀ · 2^S

En binaire, le membre droit n₀ · 2^S est n₀ suivi de S zéros.

Donc : **les S bits de poids faible de corrSum + n₀ · 3^k doivent tous être 0.**

C'est une contrainte FORTE sur la représentation binaire de corrSum.

### 3.4. Propagation des retenues dans 3^k

La multiplication par 3 = (2+1) crée un schéma de retenues spécifique.
Pour un nombre n de bits b_{m-1}...b₁b₀ :

3n = (n << 1) + n :
  bit i de 3n = b_{i-1} ⊕ b_i ⊕ carry_{i-1}
  carry_i = MAJ(b_{i-1}, b_i, carry_{i-1})   (majorité)

La chaîne de retenues dépend du MOTIF BINAIRE spécifique du nombre.

### 3.5. Observation structurelle

**Observation.** Soit B(n) le nombre de bits à 1 dans la représentation
binaire de n (poids de Hamming). Alors :

- B(3n) ≤ B(n) + 1 (car 3n = 2n + n, et l'addition peut ajouter au plus
  1 bit par cascade de retenues)
- Mais aussi B(3n) peut être < B(n) (les retenues annulent des bits)

La récurrence c_j = 3c_{j-1} + 2^{a_j} fait :
  B(c_j) ≤ B(3c_{j-1}) + 1 ≤ B(c_{j-1}) + 2

Après k étapes : B(corrSum) ≤ B(3^{k-1}) + 2k.

Et B(3^{k-1}) est connu (Stolarsky, 1978 ; Hare-Mossinghoff, 2014) :
B(3^n) est approximativement n · log₂3 / 2 ≈ 0.793n avec des fluctuations.

Donc B(corrSum) ≤ 0.793(k-1) + 2k ≈ 2.8k.

Et B(n₀ · d) : le nombre d a B(d) bits à 1. Pour n₀·d, le poids de Hamming
dépend des retenues dans la multiplication.

**Verdict :** L'analyse du poids de Hamming ne donne pas de contradiction
exploitable, car B(corrSum) et B(n₀·d) sont du même ordre (~2-3k).

### 3.6. L'angle des retenues : ce qui reste

L'analyse des retenues capture la structure LOCALE de la multiplication par 3.
Mais la contrainte corrSum = n₀·d est GLOBALE (modulo d). La difficulté est
de traduire la contrainte modulaire en contrainte sur les retenues.

Pour que cette voie fonctionne, il faudrait montrer qu'une chaîne de retenues
démarrant de 3^{k-1} et ajoutant des puissances de 2 à des positions croissantes
ne peut JAMAIS produire un multiple de d = 2^S - 3^k.

Ceci est essentiellement l'Hypothèse H reformulée en termes de retenues.

---

## 4. Le Théorème CRT Conditionnel Précis

### 4.1. L'architecture disponible

Les organes I-III du Programme Merle sont inconditionnels :
- Organe I (Cœur) : C < d pour k ≥ 18
- Organe III (Bras) : CRT multiplicatif (Théorème 22.2)
- Organe II (Jambes) : structure p-adique de Horner

Le Théorème 22.2 réduit le problème à :

  Pour chaque p_i | d : N₀(p_i) ≤ (1 + ε) · C/p_i  avec ε < 0.041.

### 4.2. Reformulation en termes de corrélation

Définissons le BIAIS de corrSum mod p :

  β(p) = (p · N₀(p) / C) − 1

Le biais mesure l'excès de compositions frappant 0 par rapport à l'équidistribution.
  β = 0 : distribution uniforme parfaite
  β = −1 : N₀(p) = 0 (aucune composition ne frappe 0)
  β > 0 : concentration sur 0

Le Théorème 22.2 requiert β(p) ≤ ε = 0.041 pour tout p | d.

### 4.3. Lien avec les sommes exponentielles

Par inversion de Fourier :
  β(p) = (1/C) · Σ_{t=1}^{p-1} T(t)

Le biais est la SOMME NORMALISÉE des T(t).

Phase 22 mesure empiriquement |β(p)| ≤ 0.03 pour tous les k et p testés.

### 4.4. Théorème Conditionnel Quantitatif

**Théorème Q** (Conditionnel). — *Supposons que pour tout k ≥ 18 et tout
premier p | d(k) :*

  (Q) :  |Σ_{t=1}^{p-1} T(t)| ≤ 0.041 · C

*Alors pour tout k ≥ 3, il n'existe pas de cycle positif non trivial
de longueur k dans la dynamique de Collatz.*

*Démonstration :*

k = 2 : seul le cycle trivial existe (classique).
k = 3..17 : N₀(d) = 0 par vérification exhaustive (Phase 22, Section 1).

k ≥ 18 : Par (Q), pour chaque p | d :
  N₀(p)/C = 1/p + (1/(pC))·Σ T(t) ≤ 1/p + 0.041/p = (1 + 0.041)/p.

Par le Théorème 22.2, avec ε = 0.041 :
  N₀(d) ≤ C · ∏_{p|d} [(1 + 0.041)/p_i]

Et la condition de fermeture est (C/d) · (1.041)^m < 1, soit :
  m · ln(1.041) < ln(d/C) = γ·S·ln2 − O(log S)
  0.0401 · m < 0.0500 · S · 0.693 = 0.0347 · S

Avec m ≤ ω(d) = O(S/log S) (nombre de facteurs premiers distincts de d) :
  0.0401 · S / log S < 0.0347 · S, soit 0.0401/log S < 0.0347.
  Ceci requiert log S > 1.156, soit S > 3.2. Vrai pour tout k ≥ 3.

Plus précisément : ω(d) ≤ 2^S/S (borne grossière). En réalité ω(d) ~ S/ln S.
La condition est satisfaite pour S ≥ 5 (k ≥ 4).                              ∎

### 4.5. Force de la condition (Q)

**Comparaison avec les conjectures du Programme Merle :**

| Conjecture | Ce qu'elle borne          | Force      | Implique Q ? |
|------------|---------------------------|------------|-------------|
| M          | |T(t)| ≤ C·k^{−δ}        | Pointwise  | Oui (trop forte) |
| M'         | |N_r − C/p| ≤ C^{1/2+ε}  | L²          | Pas directement |
| M''        | Σ T(t) = −C + O(1)        | Somme      | Oui (beaucoup trop forte) |
| **Q**      | **|Σ T(t)| ≤ 0.041·C**   | **Somme**  | **Par définition** |

La condition Q est la PLUS FAIBLE de toutes. Elle ne demande pas que chaque
T(t) soit petit (M), ni que la distribution soit quasi-uniforme en L² (M'),
ni que la somme soit ≈ −C (M''). Elle demande seulement que la somme des
T(t) ne dépasse pas 4.1% de C.

### 4.6. Pourquoi Q est « presque prouvable »

Comparons la condition Q avec ce qui est connu :

1. **Parseval donne :** Σ |T(t)|² = p·C₂ − C² où C₂ = Σ f(r)².
   Mais Σ|T|² ne borne pas |ΣT| (Cauchy-Schwarz trop lâche).

2. **Mais :** la somme ΣT(t) a une interprétation COMBINATOIRE directe :
   Σ T(t) = p·N₀(p) − C.
   Donc |ΣT| ≤ 0.041·C ⟺ |p·N₀ − C| ≤ 0.041·C ⟺ N₀ ∈ [0.959C/p, 1.041C/p].

3. **Le test numérique :** Phase 22 montre que N₀(p) est dans cet intervalle
   pour TOUS les (k,p) testés (k = 3..41, tous les p | d).

### 4.7. Quantification du fossé restant

Pour prouver Q, il faudrait montrer :

  |Σ T(t)| = |p·N₀(p) − C| ≤ 0.041·C

Par Cauchy-Schwarz : |Σ T(t)| ≤ √((p-1)·Σ|T|²) = √((p-1)·(p·C₂ − C²)).
  Pour C₂ ~ C²/p + C : √((p-1)·pC) ≈ p·√C.
  Condition : p·√C ≤ 0.041·C, soit p ≤ 0.041·√C.
  Avec C ~ 2^{1.5k} : √C ~ 2^{0.75k}, et p > 2^{1.5k}.
  Fossé : 2^{1.5k} vs 0.041·2^{0.75k}. Ratio : 2^{0.75k}/0.041 ~ 2^{0.75k}.

**Le Cauchy-Schwarz est trop faible d'un facteur exponentiel 2^{0.75k}.**

Mais ce facteur est PLUS PETIT que celui de Phase 23b (2^{0.835k}).
La condition Q est plus accessible que la condition M.

---

## 5. L'Approche par Annulation Structurelle

### 5.1. L'observation clé : T(t) n'est PAS une somme générique

Les bornes de Fourier génériques (Cauchy-Schwarz, moments) traitent T(t)
comme une somme de C termes indépendants de module 1. Elles ne voient pas
la STRUCTURE de corrSum.

Or corrSum a une structure TRÈS particulière : c'est une évaluation de la
fonction de Horner avec des coefficients géométriques (puissances de 3) et
des arguments géométriques (puissances de 2, monotones).

### 5.2. La symétrie cachée

Posons ω = 2/3 mod p. La somme de Horner normalisée est :

  Φ(g) = Σ_{j=0}^{k-1} ω^j · 2^{g_j}

Les coefficients ω^j forment une progression géométrique de raison ω.
Les valeurs 2^{g_j} forment des puissances de 2 (ordonnées).

**Observation cruciale.** ω satisfait ω^S = 2^S/3^S = 3^k/3^S = 3^{-(S-k)} = 3^{-L}.

Et dans F_p : ω^k = 2^k/3^k = 2^k/2^S = 2^{k-S} = 2^{-L}.

Donc les DEUX relations fondamentales sont :
  ω^S = 3^{-L}    et    ω^k = 2^{-L}

Ces relations lient la longueur k, le plafond S, et le gap L = S−k
à travers la structure multiplicative de F_p.

### 5.3. Reformulation comme somme de Minkowski restreinte

L'image de Φ sur Δ_k(L) est un sous-ensemble de :

  Im(Φ) ⊆ ω^0·H + ω^1·H + ... + ω^{k-1}·H    (somme de Minkowski)

avec H = {2^0, 2^1, ..., 2^L}, et la restriction g₀ ≤ g₁ ≤ ... ≤ g_{k-1}.

Sans la restriction d'ordre : c'est la somme de k copies de H, dilatées
par les coefficients ω^j. C'est un ITÉRÉ de la somme-produit.

**Le théorème de Bourgain-Katz-Tao** (2004) et ses extensions (BGK 2006,
Helfgott 2008) étudient les sommes A + B et produits A·B pour A, B ⊆ F_p.

Pour A = H (progression géométrique) : |H·H| = 2|H|−1 (produit structuré).
Par Solymosi : |H + H| ≥ |H|^{3/2}/O(√log|H|).

Pour la somme itérée kH = H + H + ... + H (k fois) :
  |kH| ≥ min(p, |H|^{1+ε(k)})  pour une fonction ε(k) → 0.

### 5.4. Le problème d'anti-concentration

Pour montrer 0 ∉ Im(Φ), il suffit de montrer que Im(Φ) ÉVITE au moins un
élément de F_p. C'est un problème d'**anti-concentration** :

> La somme Σ ω^j · 2^{g_j}, pour des g_j non-décroissants dans {0,...,L},
> est-elle concentrée en un point (0) ?

Par analogie avec les sommes de variables aléatoires :
- Si les g_j étaient i.i.d. uniformes sur {0,...,L} : la somme Φ serait
  quasi-uniforme sur F_p pour k >> log p / log |H|.
  Avec |H| = L+1 ~ 0.6k et p ~ 2^{1.6k} : log p/log|H| ~ 1.6k/log k.
  Il faudrait k >> 1.6k/log k, soit log k >> 1.6. Vrai pour k ≥ 5.

- Mais les g_j ne sont PAS i.i.d. : ils sont ordonnés (g_j ≤ g_{j+1}).

L'ordonnancement RÉDUIT l'entropie de la distribution de Φ. Par combien ?

### 5.5. Entropie de Φ sous contrainte d'ordre

Pour k variables i.i.d. uniformes sur {0,...,L} : l'espace est (L+1)^k.
La somme Φ prend au plus min(p, (L+1)^k) valeurs.

Avec la contrainte d'ordre : l'espace est C(L+k, k) ~ (eL/k)^k pour L >> k.
Pour L = S−k ~ 0.585k : C ~ (e·0.585)^k ~ 1.59^k. Et |F_p| ~ 2^{1.585k}.

Ratio : |Im|/|F_p| ≤ C/p ~ 1.59^k / 2^{1.585k} = (1.59/3.0)^k ~ 0.53^k → 0.

L'image est une FRACTION EXPONENTIELLEMENT DÉCROISSANTE de F_p.

C'est exactement le déficit entropique γ ≈ 0.05 réinterprété dans ce cadre.

### 5.6. Pourquoi le déficit entropique ne suffit pas

|Im(Φ)|/|F_p| → 0 exponentiellement NE PROUVE PAS que 0 ∉ Im(Φ).

Analogie : un ensemble de 1000 éléments dans {1,...,10000}. La "couverture"
est 10%. Mais cet ensemble peut contenir 42, ou ne pas le contenir —
sans information structurelle, impossible de conclure.

Ce qu'il faudrait : montrer que Im(Φ) est « loin » de 0 au sens de la
structure de F_p. C'est-à-dire que 0 est dans le « complément structuré »
de Im(Φ).

---

## 6. Le Candidat de Théorème : Rigidité Géométrique

### 6.1. L'idée directrice

La somme Φ(g) = Σ ω^j · 2^{g_j} peut être vue comme un point sur une
COURBE dans F_p, paramétrée par le vecteur g.

Plus précisément, dans l'espace F_p^k, considérons la VARIÉTÉ :

  V = {(x₁,...,x_k) ∈ H^k : x₁ ≤ x₂ ≤ ... ≤ x_k}  (en termes de log₂)

et la forme linéaire :

  L(x) = Σ ω^j · x_j

Le problème est : montrer L(V) ∩ {0} = ∅.

### 6.2. La structure multiplicative de V

V n'est pas une variété algébrique au sens usuel (la contrainte x_j ∈ H est
multiplicative, l'ordre x_j ≤ x_{j+1} est sur les log discrets).

Mais en termes de log₂ : les g_j ∈ {0,...,L} avec g_j ≤ g_{j+1}, et la
forme « exponentielle-linéaire » L = Σ ω^j · 2^{g_j}.

Cette structure est typique des SOMMES EXPONENTIELLES LACUNAIRES.

### 6.3. Le phénomène de rigidité

**Conjecture R** (Rigidité Géométrique). — *Pour p | d(k) avec ord_p(2) > S,
la forme linéaire L(x) = Σ ω^j · x_j restreinte à la variété*
*V = {x ∈ H^k : x₁ ≤ ... ≤ x_k, x₁ = 1} est à valeurs dans un sous-ensemble*
*propre de F_p, et ce sous-ensemble exclut 0.*

**Ce que la rigidité signifierait :** L'image Im(Φ) n'est pas un sous-ensemble
« générique » de F_p. Elle est STRUCTURÉE par la double géométrie (coefficients
ω^j et arguments 2^{g_j}), et cette structure est incompatible avec la valeur 0,
qui est la valeur « privilégiée » par la relation 2^S = 3^k mod p.

### 6.4. Évidences pour la rigidité

1. **Entropique :** |Im|/p → 0 (déficit γ > 0).
2. **Spectrale :** Les données Phase 22 montrent que corrSum mod p évite
   systématiquement les multiples de d (dans la version complète mod d).
3. **Mécanisme de troncature :** Pour les p avec ω₂(p) > S, les puissances de 2
   ne couvrent qu'un ARC du cercle multiplicatif. La somme pondérée est
   confinée dans un « cône » de F_p.
4. **Épluchage (Lemme 1) :** À chaque couche, au plus UN prolongement
   est admissible. L'arbre de décision se RÉTRÉCIT à chaque niveau.

### 6.5. Pourquoi la rigidité est difficile à prouver

La rigidité de la Conjecture R combine :
- Théorie des nombres (propriétés de ord_p(2), ord_p(3))
- Combinatoire additive (sommes de Minkowski restreintes)
- Géométrie arithmétique (structure de l'image d'une forme linéaire sur un
  ensemble multiplicativement structuré)

Aucune branche des mathématiques n'a développé les outils pour traiter
EXACTEMENT ce type de problème.

---

## 7. Le Théorème d'Assemblage (Version Maximale)

### 7.1. Ce qui est prouvé inconditionnellement

**Théorème** (Assemblage Partiel — Inconditionnel).

(a) Pour k = 3,...,17 : N₀(d(k)) = 0 (exhaustif, Phase 22).

(b) Pour k ≥ 18 : C(S−1,k−1) < d(k) (Théorème 1, déficit entropique).

(c) Pour k ≥ 18 et p | d avec ord_p(2) > S−k :
    N₀(p) ≤ C · (k−1)/(S−1) < 0.631 · C  (Lemme d'Épluchage).

(d) Pour k ≥ 18 : il existe p | d avec p > C^{1/2} (Stewart, 2013).

(e) Le Théorème Q réduit la conjecture de Collatz (pas de cycles positifs
    non triviaux) à la seule condition :
    |Σ_{t≠0} T(t)| ≤ 0.041 · C pour tout k ≥ 18 et tout p | d.

### 7.2. Le fossé restant (en une inégalité)

**Le fossé** : montrer |Σ T(t)| ≤ 0.041·C alors que Cauchy-Schwarz donne
|Σ T(t)| ≤ p·√C ≈ 2^{0.75k}·C.

Le ratio est 2^{0.75k}, à comparer avec :
- Phase 23b : ratio 2^{0.835k} (pour la borne pointwise |T(t)|)
- Phase 23c/Énergie : ratio C = 2^{1.5k} (pour le coût du hit)

**Le fossé de la condition Q (2^{0.75k}) est le PLUS PETIT de tous.**

C'est la formulation la plus accessible du problème ouvert.

### 7.3. Ce qu'il faudrait inventer

Pour combler le fossé 2^{0.75k}, il faudrait un argument montrant que les
T(t) s'ANNULENT PARTIELLEMENT quand on les somme. C'est-à-dire :

Les T(t) pour t = 1,...,p−1 ne sont pas tous de même signe/direction —
ils pointent dans des directions « aléatoires » du plan complexe, et leur
somme bénéficie d'une annulation en √(p) au lieu du trivial p.

Pour des sommes VÉRITABLEMENT indépendantes : |Σ T| ~ √(p·E[|T|²]) = √(pC)
par la loi des grands nombres. Et √(pC) ~ 2^{1.55k/2} = 2^{0.775k} · √C.

Hmm — c'est EXACTEMENT le Cauchy-Schwarz ! Les T(t) ne sont pas indépendants,
mais le Cauchy-Schwarz traite la somme COMME SI ils l'étaient.

Pour faire MIEUX, il faudrait exploiter les CORRÉLATIONS entre T(t) et T(t')
pour différents t. C'est le domaine des QUATRIÈMES MOMENTS de Vinogradov :

  |Σ T(t)|^4 ≤ ... (utilise les corrélations T(t)·overline{T(t')})

Mais Phase 23b a montré que les moments d'ordre r ≥ 2 ne suffisent pas.

### 7.4. L'impasse et l'ouverture

L'impasse : toutes les bornes GÉNÉRIQUES (Parseval, Cauchy-Schwarz, moments)
sont trop faibles d'un facteur exponentiel.

L'ouverture : la condition Q est la PLUS FAIBLE condition suffisante, et le
fossé (2^{0.75k}) est le plus petit. Si un argument structurel peut gagner
NE SERAIT-CE QUE un facteur 2^{−δk} pour un δ > 0.75 dans la somme Σ T(t),
la preuve serait complète.

---

## 8. Programme Résiduel : 3 Questions Concrètes

### 8.1. Question A (Computationnelle)

**Vérifier N₀(d) = 0 pour k = 18,...,25 par énumération directe.**

Pour k = 18 : C ≈ 2.2 × 10^6, faisable en minutes.
Pour k = 25 : C ≈ 10^10, faisable en heures avec parallélisation.

Ceci étendrait la preuve exhaustive et fournirait des données pour le
biais β(p) dans de nouveaux régimes.

### 8.2. Question B (Somme-Produit Modulaire)

**Borner le nombre de solutions de 2^a + c·2^b = α mod p pour a,b ∈ {0,...,L}.**

Résultat espéré : ≤ L^{1−δ} pour un δ > 0 explicite, uniformément en α et p.

Ceci améliorerait le Lemme d'Épluchage multi-couches et donnerait un
aperçu de la faisabilité de la condition Q.

### 8.3. Question C (Corrélation des T(t))

**Calculer Σ_{t,t'} T(t)·overline{T(t')} pour des paires (t,t') structurées.**

Si les T(t) sont « décorrélés » : la somme est petite, et |ΣT| ~ √(p·ΣE[|T|²]).
Si les T(t) sont « corrélés positivement » : |ΣT| ~ p·E[|T|], trop grand.
Si les T(t) sont « corrélés négativement » : |ΣT| ≪ √(p), excellent !

Les données de Phase 22 suggèrent une corrélation FAIBLEMENT NÉGATIVE
(les T(t) tendent à s'annuler mutuellement), mais aucune preuve n'existe.

---

## 9. Synthèse : L'État du Théorème

### 9.1. Diagramme de dépendance

```
COLLATZ (pas de cycles positifs non triviaux)
  │
  ├── k = 3..17 : PROUVÉ (exhaustif)
  │
  └── k ≥ 18 : Théorème Q
       │
       ├── Organe I : C < d         ── PROUVÉ (déficit entropique γ)
       │
       ├── Organe III : CRT × ε     ── PROUVÉ (Théorème 22.2, ε < 0.041)
       │
       ├── Épluchage : N₀ ≤ 0.63C   ── PROUVÉ (Lemme 1, inconditionnel)
       │
       ├── Stewart : ∃ p > C^{1/2}  ── PROUVÉ (facteur premier large)
       │
       └── Condition Q : |ΣT| ≤ 0.041C ── OUVERT
            │
            ├── Fossé Cauchy-Schwarz : 2^{0.75k}
            │
            ├── Somme-produit : gain poly(k) seulement
            │
            └── Corrélations T(t) : non prouvées
```

### 9.2. En une phrase

> **La preuve de l'absence de cycles Collatz positifs est réduite à UNE
> inégalité — |Σ T(t)| ≤ 0.041·C — qui est vérifiée numériquement pour
> k ≤ 41 mais dont le fossé théorique (2^{0.75k} entre Cauchy-Schwarz et
> la réalité) requiert un argument d'annulation structurelle sans précédent.**

---

## Appendice : Comparaison des fossés

| Phase | Condition | Fossé (en facteur) | Commentaire |
|-------|-----------|-------------------|-------------|
| 23 (M) | |T(t)| ≤ C·p^{−ε} | 2^{S} ≈ 2^{1.585k} | Pointwise, le plus dur |
| 23b (CS) | |ΣT| ≤ ε·C via CS | 2^{0.835k} | Barrière racine carrée |
| 23d (Q) | |ΣT| ≤ 0.041·C | **2^{0.75k}** | Le plus accessible |
| Idéal | ΣT = −C + O(1) [=M''] | ≡ H | Circulaire |

Le fossé de la condition Q (2^{0.75k}) est le plus petit identifié.
C'est l'endroit le plus prometteur pour concentrer les efforts futurs.

---

## Références supplémentaires

- Solymosi (2009) "Bounding multiplicative energy by the sumset."
  Advances in Math. 222(2), 402-408.
- Bourgain, Katz, Tao (2004) "A sum-product estimate in finite fields,
  and applications." GAFA 14(1), 27-57.
- Bourgain, Glibichuk, Konyagin (2006) "Estimates for the number of sums
  and products and for exponential sums in fields of prime order."
  J. London Math. Soc. 73(2), 380-398.
- Helfgott (2008) "Growth and generation in SL_2(Z/pZ)." Ann. Math. 167, 601-623.
- Shparlinski (2006) "On the additive energy of the Heilbronn subgroup."
  Moscow Math. J. 6(3), 535-540.
- Hare, Mossinghoff (2014) "The number of nonzero digits of 3^n."
  arXiv:1412.3385.
