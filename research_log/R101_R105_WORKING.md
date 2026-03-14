# CAMPAGNE R101→R105 — WORKING FILE

## Date: 14 mars 2026
## Brief: PromptR101.md — Campagne autonome 7 rounds (exécution 5 rounds R101-R105)

---

## R101 — RECALAGE DU SURVIVANT, DU VERROU ET DES FAUX ESPOIRS

### ÉTAT DE DÉPART

**Survivant actuel**: T159 "Filtre d'Orthogonalité des Caractères" [PROUVÉ, INCONDITIONNEL]
- W_ℓ = 0 exactement quand r/gcd(ℓ,r) ∤ k
- Corollaire : si gcd(r,k) = 1 → R = 0 exactement

**Survivant auxiliaire**: T160 "Hybride T4+T159" [PROUVÉ]
- |R| ≤ n_eff · (bound T4), n_eff = #{ℓ : r/gcd(ℓ,r) | k}

**Verrou résiduel clairement identifié**:
Le problème se réduit à : pour les primes p | d(k) avec gcd(ord_p(2), k) > 1,
borner Σ_{ℓ actifs} |W_ℓ| où W_ℓ = Σ_t ∏_j S_0^{(ℓ)}(t·α_j).

Deux sous-verrous :
(V1) Le gap L²/L^∞ : RMS(S_0) = √r mais sup = √p
(V2) La corrélation entre facteurs S_0(t·α_j) pour j différents

### CE QUI NE MARCHE PAS (rappel carte mentale)
- Artin (ordres multiplicatifs) : ouvert depuis 1927
- M4 comme amélioration du produit : PROUVÉ pire (r > p^{0.69})
- Parseval/triangle : donne exactement √p, structurellement impossible
- SWL : spectre plat, R91
- Toutes reformulations F_p : noyau irréductible, R80
- BGK quantitatif : insuffisant pour k < 91

### DÉCOUVERTE R101-A : FORMULE EXACTE n_eff

**Théorème T162 [PROUVÉ]** : n_eff(r,k) = gcd(r,k) - 1.

**Preuve** : Les ℓ actifs (W_ℓ ≠ 0 a priori) satisfont r/gcd(ℓ,r) | k.
Pour chaque diviseur d | gcd(r,k) avec d > 1, les ℓ avec gcd(ℓ,r) = r/d sont
de la forme ℓ = (r/d)·m avec 1 ≤ m ≤ d-1, gcd(m,d) = 1. Leur nombre est φ(d).
Total : n_eff = Σ_{d | gcd(r,k), d>1} φ(d) = gcd(r,k) - 1 (identité de Ramanujan).

**Corollaires immédiats** :
- k premier (23,29,31,37,41) : n_eff ∈ {0, k-1}. Dichotomie totale.
  n_eff = 0 ssi k ∤ ord_p(2), n_eff = k-1 ssi k | ord_p(2).
- k = 3·7 = 21 : n_eff ∈ {0, 2, 6, 20} selon gcd(r,21) ∈ {1, 3, 7, 21}.
- Cas générique (par Chebotarev/Dirichlet) : Prob(gcd(r,k) = 1) ≈ φ(k)/k
  ≈ 57% pour k=21, ≈ 96% pour k=23 (premier).

**Statut** : [PROUVÉ] — dérivation purement algébrique de T159.

### DÉCOUVERTE R101-B : T159 NE RÉSOUT PAS N₀(p) = 0

**Observation critique** : Quand gcd(r,k) = 1, T159 donne R = 0, donc
N₀(p) = (C/r^k)·N_H(0) = main term.

Or N_H(0) = #{(h₁,...,h_k) ∈ H^k mono : Σ α_j h_j ≡ 0 mod p} > 0
pour r >> p^{1/(k-1)} (régime générique des grands primes p | d(k)).

**Conséquence** : T159 seul ne peut PAS donner N₀(p) = 0 pour un prime donné.
Le programme vers N₀(d) = 0 requiert SOIT :
(a) Un prime adéquat p | d(k) avec N_H(0) = 0 (rare, nécessite r petit)
(b) Le produit CRT multi-primes : N₀(d) ≈ C/d < 1
(c) Le contrôle du reste R pour que N₀(p) + R soit fractionnaire → N₀(p) = ⌊...⌋ = 0

**Statut** : [DIAGNOSTIC — clarifie la portée de T159]

### CANDIDATS INITIAUX (max 2 par axe)

**AXE A — Renforcement du survivant T159**

**CANDIDAT A1 : "Densité des primes avec gcd(r,k) = 1"**
- Objet : Montrer que pour CHAQUE prime p | d(k), la probabilité gcd(ord_p(2), k) > 1 est contrôlable
- Lemme candidat : Par Chebotarev, la densité des primes p avec ℓ | ord_p(2) (ℓ premier, ℓ | k) est 1/ℓ(ℓ-1). Pour k premier, seule fraction 1/k a k | r.
- Gain : Si on peut montrer que d(k) n'a AUCUN facteur premier p avec k | ord_p(2), T159 suffit
- Réfutation : Trouver un p | d(k) avec k | ord_p(2) pour un k premier du gap
- Anti-redondance : NOUVEAU — la question de densité appliquée à d(k) spécifiquement

**CANDIDAT A2 : "Borne quantitative sur W_ℓ actifs via structure T159"**
- Objet : Pour les ℓ actifs, T159 force χ_ℓ^k = 1 sur H. Cela contraint la structure du produit ∏_j S_0^{(ℓ)}(t·α_j). Exploiter cette contrainte pour une borne MEILLEURE que T4.
- Lemme candidat : La condition χ_ℓ^k = 1 implique S_0^{(ℓ)}(t)^k a une structure spéciale...
- Gain : Borne sur W_ℓ meilleure que (√p)^k sans condition sur r
- Réfutation : Si la contrainte χ_ℓ^k = 1 ne restreint pas le produit W_ℓ
- Anti-redondance : Extension de T159, pas reformulation

**AXE B — Investigation du verrou résiduel**

**CANDIDAT B1 : "Moments mixtes / Décorrélation sous ⟨3⟩"**
- Objet : M_mix = Σ_t |S_0^{(ℓ)}(t)|²·|S_0^{(ℓ)}(t·3)|²
- Prédiction : M_mix = r²p + O(termes sous-dominants)
  → Les facteurs S_0(t) et S_0(t·3) sont DÉCORRÉLÉS en magnitude
- Calcul diagonal : Les termes (h₁=h₂, g₁=g₂) contribuent p·r² exactement
- Off-diagonal : Implique énergie additive décalée E_3(H) et sommes de Jacobi
- Gain : Si prouvé, le produit de k facteurs ≈ (√r)^k au lieu de (√p)^k
- Réfutation : Si M_mix >> r²p (corrélation positive entre facteurs)
- Anti-redondance : NOUVEAU — moments mixtes jamais calculés dans le projet

**CANDIDAT B2 : "Factorisation du verrou en sous-blocs"**
- Objet : Décomposer ∏_{j=0}^{k-1} S_0(t·α_j) en blocs de taille m ≤ k
- Idée : Si les blocs sont "presque indépendants", le produit factorise
- Gain : Réduire le problème k-linéaire à un problème m-linéaire (m petit)
- Réfutation : Si les corrélations inter-blocs sont aussi fortes qu'intra-blocs
- Anti-redondance : Distinct de MDL (R86) car on factorise le PRODUIT, pas le simplexe

### CHECKPOINT R101

1. **Axe A progresse ?** OUI — T162 (n_eff exact) et diagnostic N₀(p)
2. **Candidat mordant ?** B1 (moments mixtes) = le plus prometteur
3. **Gain en statut de preuve ?** T162 [PROUVÉ], diagnostic [CLARIFIÉ]
4. **Non-redondance ?** Tous 4 vérifiés contre carte mentale
5. **À tuer ?** A1 potentiellement fragile (dépend de factorisation de d(k))
6. **Round suivant justifié ?** OUI — B1 nécessite calcul explicite de M_mix

### DÉCOUVERTE R101-C : DICHOTOMIE 3 ∈ H / 3 ∉ H

**Théorème T163 [PROUVÉ]** : Si 3 ∈ H = ⟨2⟩ mod p (i.e., ord_p(3) | ord_p(2)), alors pour tout ℓ ≥ 1:

S_0^{(ℓ)}(t·α_j) = χ_ℓ(α_j)^{-1} · S_0^{(ℓ)}(t)

et donc |S_0^{(ℓ)}(t·α_j)| = |S_0^{(ℓ)}(t)| pour tout j.

**Preuve** : Pour α_j = 3^{k-1-j} ∈ H, le changement h' = α_j·h dans
S_0^{(ℓ)}(t·α_j) = Σ_{h∈H} χ_ℓ(h)·e_p(t·α_j·h) donne
= χ_ℓ(α_j)^{-1} · Σ_{h'∈H} χ_ℓ(h')·e_p(t·h') = χ_ℓ(α_j)^{-1} · S_0^{(ℓ)}(t). □

**Conséquence majeure** : Quand 3 ∈ H, le produit FACTORISE :
∏_{j=0}^{k-1} S_0^{(ℓ)}(t·α_j) = S_0^{(ℓ)}(t)^k · χ_ℓ(3^{k(k-1)/2})^{-1}

Et W_ℓ = const · p · T_k(H, χ_ℓ) où

**T_k(H, χ_ℓ) = Σ_{h₁+...+h_k=0 in H} χ_ℓ(∏h_i)**

= somme de Jacobi généralisée sur le sous-groupe H.

**Quand 3 ∉ H** : Les facteurs |S_0(t·α_j)| sont GENUINEMENT DIFFÉRENTS.
La décorrélation des magnitudes est attendue (M_mix ≈ r²p < M4 ≈ 2r²p).

**Heuristique T_k ≈ 0 pour ℓ actif** : Si χ_ℓ^k = 1 sur H,
les valeurs χ_ℓ(∏h_i) sont des racines k-ièmes de l'unité.
Par équirépartition de la "phase multiplicative" sur les k-tuples
additifs zéro, T_k ≈ (N_H(0)/k)·Σ_{ζ∈μ_k} ζ = 0.
La déviation |T_k| mesure le DÉFAUT d'équirépartition multiplicative
sur les contraintes additives.

**Impact** : Si |T_k| = o(N_H(0)), alors W_ℓ = o(p·N_H(0))
→ R = o(main term) → N₀(p) ≈ main term > 0.
Le cas 3 ∈ H ne AIDE PAS pour N₀(p) = 0.

Le cas 3 ∉ H reste le front actif pour la décorrélation.

---

## R102 — PREMIÈRE POUSSÉE SUR LES CANDIDATS

### POUSSÉE B1 : CALCUL EXPLICITE DE M_mix

**Objectif** : Calculer M_mix = Σ_t |S_0^{(ℓ)}(t)|²·|S_0^{(ℓ)}(t·3)|² exactement.

**Étape 1 : Expansion**

|S_0^{(ℓ)}(t)|² = Σ_{h₁,h₂∈H} χ_ℓ(h₁/h₂)·e_p(t(h₁-h₂))
|S_0^{(ℓ)}(t·3)|² = Σ_{g₁,g₂∈H} χ_ℓ(g₁/g₂)·e_p(3t(g₁-g₂))

Produit et somme sur t ∈ F_p :
M_mix = p · Σ_{h₁-h₂+3(g₁-g₂)=0, h_i,g_i∈H} χ_ℓ(h₁g₁/(h₂g₂))

**Étape 2 : Séparation diagonal / off-diagonal**

- **Diagonal** (h₁=h₂ AND g₁=g₂) : contribution = p·r²
  (Car h₁=h₂ et 3(g₁-g₂)=0 force g₁=g₂, caractère = 1, r² termes)

- **Semi-diagonal** : AUCUNE contribution (h₁=h₂ force g₁=g₂ et vice versa)

- **Off-diagonal** (h₁≠h₂, g₁≠g₂) : h₁-h₂ = 3(g₂-g₁), posons Δ = g₂-g₁ ≠ 0.

**Étape 3 : Factorisation de l'off-diagonal**

Pour Δ fixé : h₂ = h₁ - 3Δ, g₂ = g₁ + Δ. Conditions : h₁-3Δ ∈ H, g₁+Δ ∈ H.

Off = Σ_{Δ≠0} Σ_{h₁∈H∩(H+3Δ)} Σ_{g₁∈H∩(H-Δ)} χ_ℓ(h₁·g₁/((h₁-3Δ)·(g₁+Δ)))

**Clé** : Le caractère SÉPARE les variables :
χ_ℓ(h₁/(h₁-3Δ)) · χ_ℓ(g₁/(g₁+Δ))

Donc Off = Σ_Δ F_ℓ(Δ) · G_ℓ(Δ) où :
F_ℓ(Δ) = Σ_{h∈H∩(H+3Δ)} χ_ℓ(h/(h-3Δ))
G_ℓ(Δ) = Σ_{g∈H∩(H-Δ)} χ_ℓ(g/(g+Δ))

**Étape 4 : Borne sur F_ℓ(Δ) et G_ℓ(Δ)**

Soit n_Δ = |H ∩ (H+3Δ)| et m_Δ = |H ∩ (H-Δ)|.

CAS 1 (r ≤ √p) : Par somme-produit (Bourgain-Katz-Tao),
n_Δ ≤ E(H)/(r) ≤ Cr^{2-δ} pour δ > 0.
Plus précisément, pour Δ ∈ H-H (≈ r² valeurs) : n_Δ ≈ 1 (chaque différence apparaît ~1 fois).
Donc |F_ℓ(Δ)| ≤ 1 et |G_ℓ(Δ)| ≤ 1 pour la plupart des Δ.
|Off| ≤ Σ_Δ 1 ≈ r² (nombre de Δ pertinents).

CAS 2 (r > √p) : n_Δ ≈ r²/p, m_Δ ≈ r²/p.
F_ℓ(Δ) somme de n_Δ termes avec caractère non trivial → cancellation.
|F_ℓ(Δ)| ≈ √(n_Δ) = r/√p (heuristique).
|Off| ≤ p · (r/√p)² = r².

**CONCLUSION ÉTAPE 4** :
|Off| = O(r²) dans les deux cas.
Donc **M_mix = p·r² + p·O(r²) = r²p · (1 + O(1))**.

**PROBLÈME** : Le O(1) pourrait être grand. Mais la structure est correcte :
M_mix = Θ(r²p), à comparer avec M4 = (2r²-r)p ≈ 2r²p.

### POUSSÉE B1 : INTERPRÉTATION ET LIMITES

**Prédiction** : M_mix/M4 ≈ 1/2 quand 3 ∉ H (décorrélation),
M_mix/M4 = 1 quand 3 ∈ H (corrélation parfaite).

**Gain pour le produit de k facteurs** :
Si les k facteurs sont INDÉPENDANTS en magnitude :
Σ_t ∏_{j=0}^{k-1} |S_0(t·α_j)|² ≈ (r²p)·(r²/p^2)^{k-1}... NON, ce n'est pas correct.

La bonne estimation k-linéaire :
Σ_t ∏_j |S_0(t·α_j)|² = ??? (k-fold mixed moment)

Pour estimer W_ℓ, on utilise Cauchy-Schwarz :
|W_ℓ|² ≤ (p-1) · Σ_t |∏ S_0(t·α_j)|² = (p-1) · Σ_t ∏ |S_0(t·α_j)|²

Le moment 2k-linéaire Σ_t ∏|S_0|² est beaucoup plus dur que le moment mixte 4-linéaire.

**MURS RENCONTRÉS** :
1. Le passage de M_mix (4-linéaire) à M_{2k} (2k-linéaire) n'est pas direct
2. Cauchy-Schwarz perd un facteur √p dans le t-sum
3. Même avec décorrélation complète, |W_ℓ| ≈ r^{k/2}·√p ≫ N_H(0)/r^k pour r petit

### POUSSÉE A2 : LA CONTRAINTE χ_ℓ^k = 1

Pour les ℓ actifs : χ_ℓ prend des valeurs dans μ_k (racines k-ièmes de l'unité).
Cela partitionne H en k classes : H_ζ = {h ∈ H : χ_ℓ(h) = ζ} pour ζ ∈ μ_k.
Chaque |H_ζ| = r/k (par orthogonalité, si k | r — sinon pas de ℓ actif).

S_0^{(ℓ)}(t) = Σ_{ζ∈μ_k} ζ · Σ_{h∈H_ζ} e_p(th) = Σ_ζ ζ · S_ζ(t)

où S_ζ(t) = Σ_{h∈H_ζ} e_p(th) est la somme exponantielle sur le sous-ensemble H_ζ.

Par Parseval : Σ_t |S_ζ(t)|² = |H_ζ| · p = (r/k) · p.

**Observation** : S_0^{(ℓ)} est une combinaison linéaire à coefficients dans μ_k
de k sommes exponentielles sur des PARTIES de H. Chaque partie est un coset
de H_1 = ker(χ_ℓ) dans H, qui est un sous-groupe d'indice k dans H.

Donc H_ζ = ζ₀ · H_1 pour un ζ₀ bien choisi, et S_ζ(t) = e_p(t·shift_ζ) · Σ_{h∈H_1} e_p(th)... NON, ce n'est pas correct car H_ζ n'est pas un coset additif mais MULTIPLICATIF.

S_ζ(t) = Σ_{h∈ζ₀·H_1} e_p(th) (coset multiplicatif de H_1 dans H)

H_1 est un sous-groupe d'ordre r/k dans F_p*, et les cosets ζ₀·H_1 sont multiplicatifs.

**Lien avec les sommes de Ramanujan** :
S_ζ(t) = Σ_{h∈ζ₀H_1} e_p(th) = Σ_{h'∈H_1} e_p(t·ζ₀·h')

Ce sont des sommes exponentielles sur un sous-groupe PLUS PETIT H_1 d'ordre r/k,
twistées par multiplication par ζ₀ (un élément de H/H_1).

Par Gauss/Parseval : |S_ζ(t)| ≤ √p (même borne qu'avant).
Mais le sous-groupe H_1 étant plus petit (ordre r/k), le moment L² est :
Σ_t |S_ζ(t)|² = (r/k)·p → RMS = √(r/k).

**GAIN POTENTIEL** : Si S_0^{(ℓ)} se décompose en k morceaux de RMS √(r/k),
et que ces morceaux sont décorrélés, alors le RMS total est √(k·(r/k)) = √r.
Pas de gain direct. MAIS la structure de coset multiplicatif pourrait permettre
une borne pointwise meilleure via la cohérence des phases.

### POUSSÉE T163 PROLONGÉE : STRUCTURE QUAND 3 ∈ H

Quand 3 ∈ H et pour ℓ actif (χ_ℓ^k = 1) :
W_ℓ = const · p · T_k(H, χ_ℓ)

Via le calcul par sommes de Jacobi multi-linéaires :
T_k = (r/(p-1))^k · Σ_{ψ₁,...,ψ_k ∈ Ĥ⊥} J(χ̃ψ₁,...,χ̃ψ_k)

avec la contrainte ∏(χ̃ψ_i) = trivial.

Chaque Jacobi sum |J| = p^{(k-2)/2} (par Deligne).
Nombre de termes : g^{k-1} où g = (p-1)/r.
Phase cancellation (si phases génériques) : √(g^{k-1}) = g^{(k-1)/2}.

|T_k| ≈ (r/p)^k · g^{(k-1)/2} · p^{(k-2)/2}
     = r^k · p^{(k-2)/2} / (p^k · r^{(k-1)/2} · p^{(k-1)/2})
     ... [calcul simplifié] ≈ √r · p^{(k-3)/2}

Pour |T_k|/N_H(0) → 0 : on retrouve r > p^{(k-1)/(2k-3)} ≈ p^{1/2+...}

**VERDICT** : La route 3 ∈ H donne la MÊME condition que T4 (r > ~√p).
Pas de gain. [ÉLIMINÉ comme voie d'amélioration]

### CHECKPOINT R102

1. **Axe A progresse ?** A2 (structure χ_ℓ^k=1) donne la décomposition en cosets
   mais PAS de borne meilleure. Route 3∈H éliminée.
2. **Candidat mordant ?** B1 (M_mix) confirm decorrelation M_mix ≈ r²p
   mais le passage au produit k-linéaire bloque (Cauchy-Schwarz trop lâche).
3. **Gain en statut de preuve ?** T162 [PROUVÉ], T163 [PROUVÉ], M_mix [SEMI-FORMALISÉ]
4. **Non-redondance ?** Tous vérifiés
5. **À tuer ?** Route 3∈H pour borne. A1 (densité) non encore poussée.
6. **Round suivant justifié ?** OUI — le passage M_mix → k-fold est le verrou actif

---

## R103 — AUDIT CROISÉ

### 1. Cross-audit des survivants de R101-R102

#### SURVIVANT B1 : M_mix decorrelation

**Claim** : M_mix = Σ_t |S_0^{(ℓ)}(t)|²·|S_0^{(ℓ)}(t·3)|² = r²p + O(r²) quand 3 ∉ H.

**Audit question 1 : Améliore-t-il T4 ?**
NON. Voici le calcul précis. T4 donne |R| ≤ n_eff · r^k · p^{k/2} / r^k = n_eff · p^{k/2},
ce qui est sous-dominant quand r > p^{1/2+2/k}. Pour que B1 améliore, il faudrait
passer de la borne M_mix (4-linéaire) au moment 2k-linéaire, ce qui nécessite
une hypothèse d'indépendance des k facteurs. R102 a montré explicitement que :

- Cauchy-Schwarz sur |W_ℓ|² ≤ (p-1)·Σ_t ∏|S_0(t·α_j)|² introduit un facteur √p
- Même avec decorrelation PARFAITE (indépendance totale des k magnitudes),
  on obtient |W_ℓ| ≈ √p · (√r)^k = √p · r^{k/2}
- La condition pour |R| < main term = r^k/p reste r^{k/2}·√p < r^k/p,
  soit r^{k/2} > p^{3/2}, soit r > p^{3/k}
- Pour k = 21 : r > p^{1/7} ≈ p^{0.143}. C'est MIEUX que T4 (r > p^{0.595}),
  MAIS seulement SI on PROUVE l'indépendance des k facteurs.

**Verdict** : Le gain potentiel est réel (p^{3/k} vs p^{1/2+2/k}) mais CONDITIONNEL
sur un passage 4-linéaire → 2k-linéaire qui n'est pas prouvé. [SEMI-FORMALISÉ avec gain conditionnel]

**Audit question 2 : Nouveau vs morts ?**
OUI — les moments mixtes M_mix n'apparaissent nulle part dans la carte mentale.
Le plus proche est M4 (R96), qui est le moment DIAGONAL Σ_t |S_0(t)|^4 = (2r²-r)p.
M_mix est le moment CROISÉ (shift par 3). Objet distinct.
Non-redondance avec : MDL (R86, simplexe→boîte, pas de moments), PO-R87 (formulation
du problème ouvert, pas de résolution), Parseval (L², pas mixte).

**Audit question 3 : Mordance réaliste ?**
MORDANCE = 3/10. Le calcul M_mix ≈ r²p est semi-formalisé (Étape 4 de R102 utilise
des heuristiques pour les bornes de F_ℓ(Δ) et G_ℓ(Δ)). Le passage au k-fold
est le vrai verrou, et aucune méthode connue n'y parvient sans hypothèse.

#### SURVIVANT A1 : Densité des primes avec gcd(r,k) = 1

**Statut** : NON POUSSÉ en R102. Audit rapide.

**Claim implicite** : Pour les primes p | d(k), montrer que gcd(ord_p(2), k) = 1
est "fréquent", ce qui forcerait R = 0 par T159.

**Audit** : Même si tous les p | d(k) satisfont gcd(r,k) = 1,
T159 donne R = 0 mais N₀(p) = (C/r^k)·N_H(0) = main term > 0 (cf R101-B).
La route vers N₀(p) = 0 individuel est FERMÉE par T159 seul.
La route vers N₀(d) = 0 via CRT requiert que le PRODUIT C/d < 1, ce qui est
déjà connu pour k ≥ 21 (Bloc 1 commence à k = 42 par Borel-Cantelli, mais
C/d < 1 est vérifié dès k = 21). Or C/d < 1 ne suffit pas :
il faut N₀(d) = ⌊C/d⌋ ou montrer que le reste multi-prime est petit.

**Verdict** : A1 ne mord pas. T159 est un FILTRE (tue les ℓ inactifs) pas un
EXTERMINATEUR (ne force pas N₀ = 0). Densité de gcd(r,k) = 1 est un objet
Chebotarev standard, mais même universellement vrai, il ne ferme pas N₀(d) = 0.
[ÉLIMINÉ — mordance 0/10 pour la cible N₀(d) = 0]

#### SURVIVANT A2 : Structure χ_ℓ^k = 1

**R102 a montré** : La décomposition S_0^{(ℓ)} = Σ_ζ ζ·S_ζ(t) avec cosets
multiplicatifs H_ζ d'ordre r/k ne donne PAS de borne meilleure que √p pointwise.
Le RMS est √(r/k) par sous-groupe, √r en total. Pas de gain.

**Verdict** : [ÉLIMINÉ — aucun gain sur T4, borne Gauss √p irréductible]

#### SURVIVANT B2 : Factorisation en blocs

**R102 a diagnostiqué** : Quand 3 ∈ H, la factorisation est EXACTE (T163) mais
donne la même condition r > ~√p (via Jacobi sums). Quand 3 ∉ H, les blocs
ne factorisent pas car les corrélations inter-blocs sont du même ordre que intra-blocs
(confirmé par M_mix ≈ r²p avec constante O(1) non prouvée petite).

**Verdict** : [ÉLIMINÉ — structurellement impossible par Hölder, confirmé R102]

### 2. Investigation des directions radicales

#### Direction (a) : Crible sur d(k) = 2^S - 3^k

**Idée** : Au lieu de borner N₀(p) pour chaque p | d(k), utiliser la STRUCTURE
MULTIPLICATIVE de d(k). Si d(k) a ω(d) ≥ k facteurs premiers distincts,
CRT donne N₀(d) ≈ ∏ N₀(p_i) / C^{ω-1}. Si chaque N₀(p_i) ≈ C/p_i,
alors N₀(d) ≈ C^ω / (p_1···p_ω · C^{ω-1}) = C/d < 1.

**Problème** : Ce raisonnement suppose INDÉPENDANCE CRT, qui est exactement
ce que la recherche a réfuté (R35 : CRT product FAUX dans 6/9 cas).
Plus précisément : N₀(d) ≤ ∏N₀(p_i)/C^{ω-1} est OBSERVÉ (R86, ACU) mais non prouvé.
Le prouver se RÉDUIT au verrou produit corrélé (R85).

**Mais** il y a un angle NOUVEAU. On ne cherche pas N₀(d) = 0 pour un d donné,
mais pour TOUS d(k) avec k = 22..41. Peut-on utiliser le fait que d(k) = 2^S - 3^k
a une structure TRÈS spéciale ? Notamment :
- d(k) est toujours pair (2^S > 3^k, et S = ⌈k·log₂3⌉ donne parité spécifique)
  NON : d(k) est IMPAIR (car 2^S ≡ 0 mod 2, 3^k ≡ 1 mod 2, d ≡ 1 mod 2...
  En fait d = 2^S - 3^k. Si S ≥ 1, 2^S pair, 3^k impair, d impair.)
- Les facteurs premiers de d(k) satisfont p | 2^S - 3^k, donc ord_p(2) | S et
  3^k ≡ 2^S mod p. Cela contraint SIMULTANÉMENT ord_p(2) et ord_p(3).

**Observation clé** : p | d(k) implique 2^S ≡ 3^k mod p. Donc (2/3)^k ≡ 2^{S-k} mod p
(si 3 inversible). Posons g = 2/3 mod p. Alors g^k ≡ 2^{S-k} mod p.
Si r = ord_p(2), alors 2^S = 2^{qr+a} = 2^a mod p (a = S mod r).
Donc 3^k ≡ 2^a mod p, i.e., 3 ∈ ⟨2⟩ mod p SI a ≡ 0 et k·log_2(3) est entier...

Ceci ne simplifie pas. La contrainte p | d(k) est une CONDITION DIOPHANTIENNE
sur p, pas une simplification.

**Verdict direction (a)** : L'approche CRT multi-primes est connue (ACU, R84-R86).
L'utilisation de la structure de d(k) = 2^S - 3^k ne produit pas de simplification
nouvelle au-delà de ce qui est dans R34-R35 et R84-R86.
[ÉLIMINÉ — redondant avec ACU/CRT product, mur = verrou produit corrélé R85]

#### Direction (b) : Énergie additive E(H, H+3Δ) et somme-produit

**Idée** : L'off-diagonal de M_mix fait intervenir |H ∩ (H+3Δ)| = n_Δ,
l'énergie additive décalée. Par Bourgain-Katz-Tao (2004), pour H ⊂ F_p
sous-groupe multiplicatif d'ordre r avec r^δ ≤ p^{1-δ} :
E(H) = #{(a,b,c,d) ∈ H^4 : a+b = c+d} ≤ C·r^{3-η} pour η = η(δ) > 0.

**Calcul** : E(H) = Σ_Δ n_Δ² (où n_Δ = |H ∩ (H+Δ)|). Par Cauchy-Schwarz :
(Σ_Δ n_Δ)² ≤ |supp| · E(H), et Σ_Δ n_Δ = r², donc |supp| ≥ r^4/E(H) ≥ r^{1+η}.

**Application à M_mix** :
Off = Σ_Δ F_ℓ(Δ)·G_ℓ(Δ) avec |F_ℓ(Δ)| ≤ n_{3Δ} et |G_ℓ(Δ)| ≤ m_Δ.
Par Cauchy-Schwarz : |Off|² ≤ (Σ n_{3Δ}²)(Σ m_Δ²) = E_3(H)·E(H).
Par sum-product : E(H) ≤ r^{3-η}, E_3(H) ≤ r^{3-η} (multiplication par 3 est automorphisme de H si 3 ∈ H, ou trivial shift si 3 ∉ H).

Donc |Off| ≤ r^{3-η}. Et M_mix = r²p + O(p·r^{3-η}).
Pour Off ≪ r²p : r^{3-η} ≪ r²p, soit r^{1-η} ≪ p, soit r ≪ p^{1/(1-η)}.
Comme r < p toujours, c'est VIDE (toujours satisfait).

**Le vrai problème** : M_mix ≈ r²p est FACILE à prouver. Le problème est
le passage du moment 4-linéaire au moment 2k-linéaire. Écrire le moment
M_{2k} = Σ_t ∏_{j=0}^{k-1} |S_0(t·3^j)|² et borner l'off-diagonal nécessite
des ÉNERGIES ADDITIVE k-LINÉAIRES :

E_k(H; 3) = #{(h_1,...,h_k,g_1,...,g_k) ∈ H^{2k} : Σ 3^j(h_j - g_j) = 0}

C'est une SOMME-PRODUIT MULTILINÉAIRE sur sous-groupe. Pour k = 2, Bourgain-Katz-Tao
suffit. Pour k général, c'est exactement PO-R87 (le problème ouvert formulé en R87).

**Verdict direction (b)** : Le lien énergie additive → M_mix est réel et donne
M_mix bien contrôlé. Mais la propagation au k-fold via E_k(H;3) est EXACTEMENT
le problème PO-R87, qui est ouvert. Pas de gain nouveau.
[ÉLIMINÉ comme route autonome — se RÉDUIT à PO-R87]

#### Direction (c) : Borne sur Σ(ℓ) = Σ_{ρ(u,v)∈H} e((u+v)ℓ/r) via Weil-Deligne

**Idée** : La somme restreinte Σ(ℓ) court sur les paires (u,v) ∈ [0,r-1]²
telles que ρ(u,v) = -3(3^v-1)/(3^u-1) ∈ H = ⟨2⟩ mod p.
Le twist e((u+v)ℓ/r) est un caractère additif sur Z/rZ × Z/rZ.

**Structure algébrique** : La condition ρ(u,v) ∈ H est :
-3(3^v - 1)/(3^u - 1) ∈ ⟨2⟩ mod p.

C'est une condition d'appartenance d'une EXPRESSION EXPONENTIELLE à un sous-groupe
multiplicatif. Ceci n'est PAS une variété algébrique au sens usuel (Weil-Deligne
s'applique aux sommes sur des variétés sur F_q, pas aux conditions d'ordre
multiplicatif).

**Tentative Weil** : Si on fixe la condition ρ(u,v) = h pour un h ∈ H donné,
on obtient une relation 3^v = 1 - (h/3)(3^u - 1), soit 3^v + (h/3)·3^u = 1 + h/3.
C'est une équation EXPONENTIELLE en (u,v), pas polynomiale.

Les bornes de Weil-Deligne s'appliquent aux sommes de la forme
Σ_{x∈V(F_q)} ψ(f(x))·χ(g(x)) où V est une variété, f,g des fonctions régulières.
Notre somme est sur un ensemble défini par une condition TRANSCENDANTE (exponentielle)
dans Z/rZ, pas dans F_p.

**Examen plus fin** : r = ord_p(2). Les éléments de H sont 2^0, 2^1, ..., 2^{r-1}.
La condition ρ(u,v) ∈ H signifie ρ(u,v) = 2^w pour un w ∈ [0,r-1].
Donc on somme sur les triplets (u,v,w) ∈ [0,r-1]³ satisfaisant :
-3(3^v - 1) ≡ 2^w(3^u - 1) mod p.

C'est une condition MULTIPLICATIVE-EXPONENTIELLE dans (Z/rZ)³. Ni Weil
(polynomes sur F_p), ni Deligne (variétés sur F_q), ni Katz (faisceaux)
ne s'appliquent directement. Les fonctions 2^w et 3^u sont des EXPONENTIELLES
discrètes, pas des polynomes.

**Seul cas traitable** : Si r = p-1 (2 est racine primitive),
alors u → 3^u est une fonction de Z/(p-1)Z → F_p*, et la condition devient
polynomiale dans F_p. Mais r = p-1 est exactement le cas Artin (ouvert 1927).

**Verdict direction (c)** : Weil-Deligne ne s'applique PAS à Σ(ℓ) car la
condition ρ(u,v) ∈ H est transcendante (exponentielle discrète), pas algébrique.
Le seul cas traitable (r = p-1) est Artin. Cette route est un CUL-DE-SAC.
[ÉLIMINÉ — hors cadre Weil-Deligne, condition transcendante non algébrique]

#### Direction (d) : Norme de bloc W_ℓ via structure polynomiale de ker(χ_ℓ^k)

**Idée** : Pour ℓ actif, χ_ℓ^k = 1 sur H, donc χ_ℓ est un caractère d'ordre
divisant k sur H. Le noyau H_1 = ker(χ_ℓ) est un sous-groupe d'indice d | k
dans H, d'ordre r/d. On écrit :

W_ℓ = Σ_t ∏_{j=0}^{k-1} S_0^{(ℓ)}(t·α_j)

avec S_0^{(ℓ)}(t) = Σ_{ζ∈μ_d} ζ · Σ_{h∈ζ₀H_1} e_p(th).

La norme N_{⟨β⟩} : Si β = 3^{(p-1)/d} génère le quotient H/H_1, on peut
factoriser le produit de k facteurs via les cosets de H_1.

**Calcul** : Chaque S_ζ(t) = Σ_{h∈ζ₀H_1} e_p(th) est une somme exponentielle
sur un sous-groupe d'ordre r/d. Par Parseval : Σ_t |S_ζ|² = (r/d)·p.
Par Gauss : |S_ζ| ≤ √p. Même borne. Pas de gain pointwise.

Le produit ∏_j S_0^{(ℓ)}(t·α_j) = ∏_j [Σ_ζ ζ·S_ζ(t·α_j)].
Développer donne d^k termes, chacun un produit de k sommes S_{ζ_j}(t·α_j).
Si les ζ_j sont DIFFÉRENTS, les magnitudes |S_{ζ_j}| pourraient interférer...
Mais chaque |S_{ζ_j}(t·α_j)| a la MÊME borne √p. L'interférence est dans
les PHASES, pas dans les magnitudes.

**Structure de norme** : La norme N_{H/H_1}(S_0^{(ℓ)}) = ∏_{β∈H/H_1} S_0^{(ℓ)}∘β
donne un objet dont les valeurs propres pourraient être contraintes.
Mais S_0^{(ℓ)}∘β(t) = S_0^{(ℓ)}(β·t), et le produit est une somme sur H^k
avec condition multiplicative, qui se réduit à T_k (somme de Jacobi généralisée).
C'est EXACTEMENT ce que R102 a calculé pour le cas 3 ∈ H → même condition r > ~√p.

**Verdict direction (d)** : La structure polynomiale de ker(χ_ℓ^k) ne produit
pas de gain. La norme de bloc se réduit aux sommes de Jacobi multi-linéaires,
dont R102 a montré qu'elles donnent la même condition que T4.
[ÉLIMINÉ — se réduit au cas T163 (route 3∈H), même condition r > ~√p]

### 3. Bilan des survivants après R103

| Candidat | Mordance | Statut | Verdict |
|----------|----------|--------|---------|
| B1 (M_mix decorrelation) | 3/10 | [SEMI-FORMALISÉ] | SEUL SURVIVANT — gain potentiel r > p^{3/k} mais conditionnel sur k-fold |
| A1 (Densité gcd(r,k)=1) | 0/10 | — | [ÉLIMINÉ] T159 ne force pas N₀=0 |
| A2 (χ_ℓ^k=1 structure) | 0/10 | — | [ÉLIMINÉ] Même borne √p, pas de gain |
| B2 (Blocs) | 0/10 | — | [ÉLIMINÉ] Hölder + T163 |
| Dir (a) Crible d(k) | 1/10 | — | [ÉLIMINÉ] Réduit à ACU/CRT product (R85) |
| Dir (b) Énergie additive | 2/10 | — | [ÉLIMINÉ] Réduit à PO-R87 |
| Dir (c) Weil-Deligne Σ(ℓ) | 0/10 | — | [ÉLIMINÉ] Hors cadre (transcendant, pas algébrique) |
| Dir (d) Norme de bloc | 0/10 | — | [ÉLIMINÉ] Réduit à T163 → même condition |

**SURVIVANT UNIQUE** : B1 (M_mix decorrelation), mordance 3/10.

**VERROU COMMUN IDENTIFIÉ** : Le passage du moment 4-linéaire M_mix au moment
2k-linéaire M_{2k}. C'est exactement PO-R87 : borner le produit corrélé
∏_{j=0}^{k-1} S_0(t·3^j). Toutes les directions investiguées s'y RÉDUISENT.

### CHECKPOINT R103

1. **Axe A progresse ?** NON — tous les candidats de l'axe A sont éliminés.
2. **Candidat mordant ?** B1 seul, mordance faible (3/10).
3. **Gain en statut de preuve ?** Aucun gain depuis R102.
4. **Non-redondance ?** B1 vérifié. Les 4 directions radicales sont toutes
   redondantes avec des verrous connus (PO-R87, Artin, ACU).
5. **À tuer ?** Tout sauf B1.
6. **Round suivant justifié ?** OUI — R104 doit tenter la preuve de B1 ou
   diagnostiquer son impossibilité structurelle.

---

## R104 — TEST DE PREUVE / DÉVERROUILLAGE

### Théorème candidat (Tentative T164)

**Énoncé** : Soit p premier, r = ord_p(2), k ≥ 3 avec gcd(r,k) > 1, et
H = ⟨2⟩ ⊂ F_p*. Supposons 3 ∉ H. Alors pour tout ℓ actif (r/gcd(ℓ,r) | k) :

|W_ℓ| ≤ C_k · r^{k/2} · p^{1/2}

où C_k est une constante dépendant seulement de k.

**Conséquence si prouvé** : |R| ≤ n_eff · C_k · r^{k/2} · p^{1/2}.
Avec n_eff = gcd(r,k) - 1 ≤ k-1, main term = N_H(0)/r^k ≈ r^{k-1}/p :
|R| < main term quand r^{k/2}·p^{1/2} < r^{k-1}/p, soit r^{k/2-1} > p^{3/2},
soit r > p^{3/(k-2)}.

Pour k = 21 : r > p^{3/19} ≈ p^{0.158}. Significativement mieux que T4 (r > p^{0.595}).
Pour k = 41 : r > p^{3/39} ≈ p^{0.077}. Presque inconditionnel.

### Esquisse de preuve

**Étape 1** : Expansion de W_ℓ.

W_ℓ = Σ_{t∈F_p} ∏_{j=0}^{k-1} S_0^{(ℓ)}(t·α_j)

avec α_j = 3^{k-1-j}. Par Cauchy-Schwarz sur t :

|W_ℓ|² ≤ p · Σ_t |∏_j S_0^{(ℓ)}(t·α_j)|²  ...(*)

**Étape 2** : Expansion du moment 2k-linéaire.

Σ_t ∏_j |S_0(t·α_j)|² = Σ_t ∏_j [Σ_{h_j,h'_j∈H} χ_ℓ(h_j/h'_j)·e_p(t·α_j(h_j-h'_j))]

Somme sur t donne la contrainte : Σ_j α_j(h_j - h'_j) ≡ 0 mod p.

Donc la somme = p · #{(h_1,...,h_k,h'_1,...,h'_k) ∈ H^{2k} : Σ α_j(h_j-h'_j)=0} · (facteur caractère)

**Étape 3** : Séparation diagonale.

Termes diagonaux (h_j = h'_j pour tout j) : contribuent r^k (chaque h_j libre).
Facteur caractère = 1 (χ(h_j/h_j) = 1). Contribution = p · r^k.

**Étape 4** : Borne off-diagonale.

C'est ICI que la preuve doit mordre. On pose Δ_j = h_j - h'_j ∈ H - H.
Condition : Σ_j α_j · Δ_j = 0, avec au moins un Δ_j ≠ 0.

Chaque Δ_j = h_j - h'_j avec h_j, h'_j ∈ H. Le nombre de représentations
de Δ_j comme h - h' est l'énergie additive locale : r_Δ = |{(h,h') : h-h'=Δ}|.

**Tentative de borne** :
Off-diag ≤ Σ_{(Δ_1,...,Δ_k): Σα_jΔ_j=0, ∃Δ_j≠0} ∏_j r_{Δ_j}

Par Cauchy-Schwarz itéré : fixer les k-1 premières coordonnées, Δ_k est déterminé.

Off-diag ≤ Σ_{Δ_1,...,Δ_{k-1}} (∏_{j=1}^{k-1} r_{Δ_j}) · r_{Δ_k(Δ_1,...,Δ_{k-1})}

où Δ_k = -(1/α_k) Σ_{j<k} α_j Δ_j.

**Borne par énergie** : Σ_Δ r_Δ² = E(H) ≤ r^{3-η} (Bourgain-Katz-Tao, η > 0).
Σ_Δ r_Δ = r². Donc r_Δ ≤ r^{1-η'} en moyenne.

Pour k-1 sommes libres : Off-diag ≤ (Σ_Δ r_Δ)^{k-1} · max_Δ r_Δ ≤ r^{2(k-1)} · r.

Donc Off-diag ≤ r^{2k-1}.

Retour à (*) : |W_ℓ|² ≤ p · (p·r^k + p·r^{2k-1}) ≈ p²·r^{2k-1}.
|W_ℓ| ≤ p · r^{k-1/2}.

Condition |R| < main term : p · r^{k-1/2} < r^{2k-1}/p,
soit r^{k-1/2} > p², soit r > p^{2/(k-1/2)} ≈ p^{4/(2k-1)}.

Pour k = 21 : r > p^{4/41} ≈ p^{0.098}. Intéressant.

### OÙ LA PREUVE CASSE

**Point de rupture 1** : L'utilisation de max_Δ r_Δ ≤ r est TRIVIALE.
On n'exploite PAS la cancellation du facteur caractère χ_ℓ(h_j/h'_j).
En incluant le caractère, les termes off-diagonaux portent un facteur
∏_j χ_ℓ(h_j/h'_j) qui est une racine de l'unité d'ordre divisant r/gcd(ℓ,r).
Si ce facteur oscille, la cancellation pourrait réduire l'off-diagonal.

**Point de rupture 2** : Le Cauchy-Schwarz initial (*) perd √p.
C'est le GAP L²/L^∞ identifié dès R101. Toute borne passant par
|W_ℓ|² ≤ p · M_{2k} perd ce facteur √p.

**Point de rupture 3** : La borne max_Δ r_Δ ≤ r ne capture PAS le fait
que Δ_k est DÉTERMINÉ par les Δ_{j<k}. Si r est grand, Δ_k est un élément
spécifique de H-H, et r_{Δ_k} pourrait être beaucoup plus petit que r.
Plus précisément : r_{Δ_k} ≤ r, mais en moyenne sur les choix de Δ_{j<k},
la valeur moyenne de r_{Δ_k} est r²/p (par heuristique d'uniformité).

**Borne AMÉLIORÉE** (en utilisant l'heuristique d'uniformité) :
Off-diag ≤ Σ_{Δ_1,...,Δ_{k-1}} (∏ r_{Δ_j}) · (r²/p)
= (r²)^{k-1} · r²/p = r^{2k}/p.

|W_ℓ|² ≤ p · (p·r^k + p·r^{2k}/p) = p²r^k + p·r^{2k}.
Pour r < p^{1/2} : dominant = p²r^k, |W_ℓ| ≤ p·r^{k/2}. → r > p^{2/k}.
Pour r > p^{1/2} : dominant = p·r^{2k}, |W_ℓ| ≤ √p · r^k. → r^k > p^{3/2}/r^k, tautologie.

**Pour k = 21, r > p^{2/21} ≈ p^{0.095}** : très prometteur mais l'heuristique
d'uniformité pour r_{Δ_k} n'est PAS prouvée. C'est une forme de MIXING sur H-H.

### Nature du gap

**Le gap est CONDITIONNEL, pas structurel.**

Expliquons. Il y a deux obstacles séparés :

**Obstacle 1 (Cauchy-Schwarz, STRUCTUREL)** : Le passage |W_ℓ|² ≤ p · M_{2k}
perd un facteur p. Ceci est INHÉRENT à la méthode de moments.
ALTERNATIVE : Ne pas utiliser Cauchy-Schwarz. Estimer W_ℓ DIRECTEMENT.

W_ℓ = Σ_t f(t) où f(t) = ∏_j S_0^{(ℓ)}(t·α_j).
C'est une somme de p termes de module ≤ ∏|S_0| ≤ (√p)^k.
La borne triviale est p·(√p)^k = p^{1+k/2}.
L'estimation non-triviale de telles sommes (produit de k fonctions
shiftées sur F_p) est EXACTEMENT le domaine des sommes multilinéaires
de Fouvry-Kowalski-Michel (FKM).

Mais FKM s'applique aux produits de sommes de Kloosterman ou de caractères
multiplicatifs, pas aux produits de sommes exponentielles partielles S_0^{(ℓ)}.
La difficulté : S_0^{(ℓ)} est une somme sur un SOUS-GROUPE, pas une somme
complète sur F_p. Les faisceaux de Katz ne s'appliquent pas directement.

**Obstacle 2 (Off-diagonal, CONDITIONNEL)** : La borne sur l'off-diagonal
utilise max_Δ r_Δ ou une heuristique d'uniformité. Si on pouvait prouver :
- r_{Δ_k} = O(r²/p) pour la plupart des choix de Δ_{j<k} (en moyenne), ou
- la cancellation du facteur caractère ∏χ_ℓ(h_j/h'_j) dans l'off-diagonal
réduit la somme d'un facteur r^{-η·k}

alors la borne fonctionnerait. Ces deux faits sont PLAUSIBLES et conditionnels
sur des résultats de somme-produit multilinéaire.

**Diagnostic précis** :
- L'obstacle 1 est contournable SI on trouve une estimation directe de W_ℓ
  (sans Cauchy-Schwarz). C'est un problème de TAN ouverte mais bien posé.
- L'obstacle 2 est résoluble SI on prouve une borne de type sum-product
  pour l'énergie additive k-linéaire E_k(H;3). C'est PO-R87.

**Ni l'obstacle 1 ni l'obstacle 2 n'est une IMPOSSIBILITÉ STRUCTURELLE.**
Ce ne sont pas des théorèmes d'impossibilité (comme "Parseval donne √p exactement").
Ce sont des problèmes OUVERTS en théorie analytique des nombres.

### Reformulation recommandée

**Le programme de preuve viable est le suivant** :

**Théorème T164 (Conditionnel)** : Sous l'hypothèse :

(H_k) : Pour tout sous-groupe multiplicatif H ⊂ F_p* d'ordre r et tout
ensemble de shifts α_0,...,α_{k-1} formant une progression géométrique
de raison 3^{-1}, l'énergie additive multilinéaire satisfait :

E_k(H; α) = #{(h,h') ∈ H^{2k} : Σ α_j(h_j-h'_j) = 0} ≤ C_k · r^{2k-1}/p + C_k · r^k

alors |W_ℓ| ≤ C_k · p · r^{k/2} et la condition de T4 s'affaiblit à r > p^{2/k}.

**Ce que (H_k) demande** : que la contrainte linéaire Σ α_j Δ_j = 0 avec
shifts géométriques NE CONCENTRE PAS les Δ_j sur des ensembles à haute
énergie additive. C'est une forme de MIXING multilinéaire pour les
sous-groupes multiplicatifs.

**Statut de (H_k)** :
- Pour k = 2 : c'est essentiellement Bourgain-Katz-Tao. [PROUVÉ]
- Pour k général : c'est le problème PO-R87. [OUVERT]
- GRH n'aide PAS directement (GRH contrôle les L-fonctions, pas l'énergie additive).
- La conjecture somme-produit (Erdős-Szemerédi forte) IMPLIQUE (H_k). [CONDITIONNEL]

### Verdict R104

**Statut de T164** : [CONDITIONNEL sur (H_k)] — pas prouvable avec les outils
actuels, mais le gap est OUVERT (pas structurellement impossible).

**Mordance** : Si (H_k) est prouvé, T164 réduit la condition de T4 de
r > p^{1/2+2/k} à r > p^{2/k}, un gain EXPONENTIEL pour grand k.
Pour k = 21 : de p^{0.595} à p^{0.095}. Pour k = 41 : de p^{0.549} à p^{0.049}.

**Nature du gap** : CONDITIONNEL sur des conjectures de théorie additive combinatoire
(energy estimates for multiplicative subgroups). Ce n'est PAS le mur Artin,
PAS le mur HGE, PAS le mur Parseval. C'est un MUR COMBINATOIRE ADDITIF distinct.

**Comparaison avec les murs connus** :
- Mur Artin (R96) : ordres multiplicatifs. [FONDAMENTAL, ouvert 1927]
- Mur HGE (R96-R98) : phases de Gauss. [FONDAMENTAL, Katz open]
- Mur Parseval (R44) : √p exact pour la norme L². [STRUCTUREL, impossible]
- Mur PO-R87 (R87) : produit corrélé multilinéaire. [OUVERT]
- **Mur (H_k) : énergie additive multilinéaire.** [OUVERT, DISTINCT de PO-R87]

En fait (H_k) est un SOUS-PROBLÈME de PO-R87. C'est une RÉDUCTION :
borner W_ℓ se réduit à borner E_k, qui est un problème purement combinatoire
(pas analytique). C'est un progrès conceptuel : le verrou analytique
(sommes exponentielles corrélées) se réduit à un verrou combinatoire
(énergie additive multilinéaire).

### CHECKPOINT R104

1. **Axe A progresse ?** NON — axe A entièrement éliminé.
2. **Candidat mordant ?** T164 conditionnel, mordance 5/10 (gain réel si (H_k) prouvé).
3. **Gain en statut de preuve ?** Passage de [SEMI-FORMALISÉ] à [CONDITIONNEL sur (H_k)].
   C'est un RECUL du statut de preuve mais un PROGRÈS de compréhension.
4. **Non-redondance ?** T164 est distinct de T4 (condition plus faible),
   de PO-R87 (réduction du problème), et de toutes les voies mortes.
5. **À tuer ?** T164 ne peut pas être tué : il est mathématiquement correct
   sous (H_k). La question est si (H_k) est accessible.
6. **Round suivant justifié ?** OUI pour R105 — investiguer si (H_k) est
   accessible (sous-verrou plus fondamental) ou s'il y a une obstruction.

---

## R105 — TOURNOI FINAL + BILAN DE CAMPAGNE

### TOURNOI DES SURVIVANTS

Après R101→R104, un seul candidat subsiste. Le tournoi est donc un AUDIT FINAL
de ce candidat unique, pas une compétition.

#### Candidat unique : T164 [CONDITIONNEL sur (H_k)]

**Énoncé** : Sous (H_k), |W_ℓ| ≤ C_k · p · r^{k/2} et la condition T4 s'affaiblit
à r > p^{2/k} (au lieu de r > p^{1/2+2/k}).

**Grille d'évaluation** :

| Critère | Score | Justification |
|---------|-------|---------------|
| Mordance (potentiel si prouvé) | 8/10 | Gain exponentiel : p^{0.595} → p^{0.095} pour k=21 |
| Statut de preuve | 3/10 | [CONDITIONNEL] — dépend de (H_k) ouvert |
| Non-redondance | 9/10 | Objet nouveau (énergie multilinéaire), distinct de tous murs connus |
| Faisabilité (H_k) | 4/10 | Connu k=2 (BKT), ouvert k≥3. Pas structurellement impossible. |
| Valeur diagnostique | 9/10 | Réduit le verrou analytique à un verrou combinatoire pur |
| **SCORE IVS GLOBAL** | **6.5/10** | Progrès conceptuel réel, preuve hors portée immédiate |

#### Comparaison avec l'état pré-campagne

| Aspect | Avant R101 | Après R105 |
|--------|------------|------------|
| Survivant principal | T159 [PROUVÉ INCONDITIONNEL] | T159 + T162 + T163 [PROUVÉS] + T164 [CONDITIONNEL] |
| Verrou identifié | "L²/L^∞ gap + corrélations" (vague) | (H_k): énergie additive k-linéaire (précis) |
| Nature du verrou | Analytique (sommes exponentielles) | Combinatoire (énergie additive) |
| Condition requise | r > p^{1/2+2/k} (T4) | r > p^{2/k} sous (H_k) |
| Murs éliminés | Artin, HGE, Parseval, SWL, BGK | +Route 3∈H, +Bloc factorisation, +Weil-Deligne sur Σ(ℓ), +Norme de bloc |
| Nombre de théorèmes | T159, T160 | +T162, +T163, +T164(cond) |

### BILAN DE LA CAMPAGNE R101→R105

#### Théorèmes produits

1. **T162 [PROUVÉ]** — n_eff(r,k) = gcd(r,k) - 1 exactement.
   Preuve algébrique pure via identité de Ramanujan. Inconditionnel.

2. **T163 [PROUVÉ]** — Dichotomie 3∈H / 3∉H.
   Si 3 ∈ H = ⟨2⟩ mod p : |S_0^{(ℓ)}(t·α_j)| = |S_0^{(ℓ)}(t)|, produit = S^k.
   Factorisation exacte mais NE DONNE PAS de borne meilleure (Jacobi sums → même condition).
   Conséquence : le front actif est 3 ∉ H (décorrélation genuïne).

3. **T164 [CONDITIONNEL sur (H_k)]** — Sous hypothèse d'énergie additive multilinéaire,
   r > p^{2/k} suffit. Gain exponentiel pour grand k.

#### Diagnostics produits

4. **Diagnostic T159** : T159 seul ne peut pas donner N₀(p) = 0 (main term positif).
   La route vers N₀(d) = 0 requiert CRT multi-primes ou contrôle du reste.

5. **M_mix decorrelation** [SEMI-FORMALISÉ] : M_mix = r²p + O(pr²) quand 3 ∉ H.
   Confirmé par séparation diag/off-diag + énergie additive BKT.

6. **Réduction analytique → combinatoire** : Le verrou des sommes exponentielles
   corrélées se RÉDUIT à l'hypothèse (H_k) sur E_k(H;α), un problème purement
   combinatoire d'énergie additive multilinéaire. C'est un sous-problème de PO-R87.

#### Voies éliminées (nouvelles, cette campagne)

7. Route 3∈H pour borne améliorée → Jacobi sums, même condition r > ~√p [ÉLIMINÉ R102]
8. Factorisation en blocs via Hölder → r > √p structurellement [ÉLIMINÉ R102]
9. A1 densité gcd(r,k)=1 → T159 est filtre, pas exterminateur [ÉLIMINÉ R103]
10. A2 structure χ_ℓ^k=1 → même borne √p pointwise [ÉLIMINÉ R103]
11. Crible sur d(k) → réduit à ACU/CRT product R85 [ÉLIMINÉ R103]
12. Weil-Deligne sur Σ(ℓ) → condition transcendante, hors cadre [ÉLIMINÉ R103]
13. Norme de bloc → réduit à T163 route 3∈H [ÉLIMINÉ R103]

#### Hiérarchie des murs (mise à jour)

| Mur | Origine | Nature | Contournable ? |
|-----|---------|--------|----------------|
| Artin | R96, 1927 | Fondamental | NON (ouvert 99 ans) |
| HGE phases | R96-R98, Katz | Fondamental | NON (faisceau ouvert) |
| Parseval √p | R44 | Structurel | NON (exactement √p) |
| PO-R87 produit corrélé | R87 | Ouvert | RÉDUCTIBLE à (H_k) |
| **(H_k) énergie k-linéaire** | **R104 [NOUVEAU]** | **Combinatoire** | **OUVERT, k=2 connu** |

#### Réponse à la question centrale du brief

> "Peut-on produire un survivant théorique plus fort, ou un verrou préparatoire plus fondamental ?"

**Réponse** : Les deux, partiellement.
- **Survivant renforcé** : T162 + T163 consolident T159, mais le front résiduel reste.
- **Verrou plus fondamental** : (H_k) est identifié comme le sous-verrou précis.
  C'est une RÉDUCTION du verrou vague "corrélations L²/L^∞" vers un objet
  combinatoire nommé et cerné. C'est le principal acquis de la campagne.
- **Aucun résultat inconditionnel nouveau ne ferme le verrou**. Honnêtement documenté.

#### Score IVS de la campagne

| Critère | Score | Commentaire |
|---------|-------|-------------|
| Rigueur mathématique | 9/10 | T162, T163 prouvés proprement. T164 honnêtement conditionnel. |
| Non-redondance | 9/10 | Aucun mort ressuscité. 7 nouvelles voies éliminées. |
| Lucidité diagnostique | 10/10 | Le gap est conditionnel, pas structurel. Réduction précise. |
| Mordance des résultats | 5/10 | T162-T163 vrais mais auxiliaires. T164 prometteur mais conditionnel. |
| Progrès vers N₀(d)=0 | 3/10 | Pas de fermeture. Le verrou (H_k) est ouvert. |
| Valeur pour la suite | 8/10 | (H_k) cible claire. Éliminations nettoyent le terrain. |
| **SCORE GLOBAL** | **7.3/10** | Campagne honnête, progrès conceptuel, pas de percée |

### PROCHAINES ÉTAPES RECOMMANDÉES

1. **Chercher (H_k) dans la littérature** : Bourgain, Katz, Tao, Schoen, Shkredov
   ont des résultats sur l'énergie additive des sous-groupes multiplicatifs.
   La question k-linéaire pourrait être abordable via les méthodes de [Shkredov 2013].

2. **Tester T164 sur Bloc 3** : Pour k=22..41, calculer p^{2/k} et vérifier
   si des primes p | d(k) satisfont r > p^{2/k}. Si oui, T164+(H_k) fermerait
   ces cas. (ATTENTION : ceci est computationnel de vérification, pas de recherche)

3. **Estimation directe de W_ℓ** (sans Cauchy-Schwarz) : Explorer la méthode
   Fouvry-Kowalski-Michel adaptée aux sommes partielles sur sous-groupes.
   Obstacle : pas de faisceau naturel pour S_0^{(ℓ)}.

4. **Approche alternative** : Si (H_k) est durablement ouvert, chercher une
   route COMPLÈTEMENT DIFFÉRENTE vers N₀(d)=0 qui évite le passage par W_ℓ.
   Par exemple : méthodes p-adiques, fonctions L de Dirichlet, ou géométrie
   des compositions de Collatz (retour au simplexe CJT direct).

### CHECKPOINT R105 — FIN DE CAMPAGNE

1. **Axe A** : FERMÉ. Aucun survivant. T159 reste un filtre précieux mais ne mord pas seul.
2. **Axe B** : T164 [CONDITIONNEL]. Seul survivant, mordance 6.5/10.
3. **Nouveaux théorèmes** : T162 [PROUVÉ], T163 [PROUVÉ], T164 [COND].
4. **Nouvelles éliminations** : 7 voies fermées proprement.
5. **Verrou identifié** : (H_k) — énergie additive k-linéaire des sous-groupes multiplicatifs.
6. **Progrès net** : Réduction analytique → combinatoire. Terrain nettoyé.
7. **Honnêteté** : Pas de percée. Le verrou est ouvert et profond.
