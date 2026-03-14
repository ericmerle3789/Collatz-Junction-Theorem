# ROUNDS R84-R88 — Fichier de travail au fil de l'eau

## Stratégie globale
R84 : Preuve computationnelle N₀(d(21)) = 0. R85-R86 : Investigation causale + Innovation.

---

# R84 — Preuve computationnelle k=21 + cartographie CRT
## Type : X/P (investigation + preuve partielle) | IVS : 9/10

### Résultat principal
**★★★ THÉORÈME (R84) : N₀(d(21)) = 0. Aucun 21-cycle non-trivial n'existe. ★★★**

Méthode : DP hiérarchique mod 692,515 (= 5×43×3221) + backtracking de 1,738 compositions + vérification mod 34,511 → 0 survivants.

### Données CRT pour k=21 (S=35, d = 5 × 43 × 3221 × 34511 = 23,899,385,165)
| Modulus | N₀ | C/m | Ratio N₀·m/C |
|---------|-----|------|-------------|
| 5 | 278,361,810 | 278,395,128 | 0.99988 |
| 43 | 32,371,851 | 32,371,992 | 0.99999 |
| 3,221 | 430,709 | 432,155 | 0.99665 |
| 34,511 | 41,113 | 40,332 | 1.01937 |
| 692,515 | 1,738 | 2,009 | 0.865 |
| 7,419,865 | 238 | 188 | 1.269 |
| **d (complet)** | **0** | **0.058** | **0** |

Ratio Law vérifié haute précision. Anticorrélation CRT confirmée (N₀(d) = 0 < C/d ≈ 0.058).

---

# R85 — Investigation causale : pourquoi l'impasse théorique ?
## Type : X (investigation) | IVS : 8/10

### Diagnostic de la situation (vérifié contre la carte mentale)

**Fait 1** : C(S-1,k-1)/d(k) < 1 pour tout k ≥ 21 (PROUVABLE).
Conséquence : si les résidus de corrSum mod d étaient uniformes, N₀ = 0.

**Fait 2** : Les résidus SONT quasi-uniformes (Ratio Law, vérifiée k=3..21).

**Fait 3** : AUCUN outil ne prouve l'uniformité. 83 rounds, 112+ pistes fermées.

### Les 4 murs classiques et pourquoi ils échouent (R32)
- **Weyl** : Nécessite un domaine = intervalle, pas un simplexe
- **Weil** : S'applique sur F_p complet, pas sur des sous-ensembles structurés
- **Large Sieve** : La boîte englobant le simplexe a volume k! × simplexe → perte totale
- **Erdős-Turán** : Circulaire (nécessite exactement les bornes qu'on cherche)

### Le mur Cauchy-Schwarz/Parseval (R56)
Le passage L² → L∞ perd √p. Pour compenser, il faudrait μ = 1 + O(p^{-k}),
ce qui est de la précision 10^{-150}. Structurellement impossible.

### Diagnostic RACINE (nouveau, R85)

**Le verrou est un problème de PRODUITS CORRÉLÉS de sommes de caractères.**

La décomposition caractère donne : N₀(p) = C/p + (1/p) Σ_{t≠0} S(t)

Chaque S(t) = Σ_A ω^{t·corrSum(A)} peut s'écrire (via Horner/produit) comme un coefficient d'un PRODUIT de k generating functions, chacune ayant un "twist" différent α_i = 3^{k-1-i}.

Pour borner S(t), on borne chaque facteur individuellement par la borne de Gauss |σ_i| ≤ √p. Le produit donne (√p)^k. Or :
- (√p)^k CROÎT exponentiellement avec k
- L'erreur réelle est O(C/p) qui est BIEN PLUS PETITE
- Le gap : les k facteurs ne sont PAS indépendants (ils partagent le paramètre t)
- Les différents "twists" α_i créent des INTERFÉRENCES CONSTRUCTIVES entre facteurs
- Cette interférence réduit le produit de (√p)^k à ≈ r^{k/2} (cancellation racine)
- Mais la cancellation racine dans un produit corrélé est un PROBLÈME OUVERT

### Ce qui est NOUVEAU vs les 4 murs

Le problème n'est PAS de trouver une meilleure borne sur un SEUL σ_i (Gauss est tight).
Le problème EST de borner le PRODUIT ∏ σ_i quand les facteurs sont corrélés.

C'est un problème de **sommes multilinéaires exponentielles**, distinct des 4 murs classiques.

Outils potentiels (non dans la carte mentale) :
1. **Découplement ℓ² (Bourgain-Demeter-Guth 2015)** — borne les moments de sommes exp
2. **Bornes multilinéaires de Kloosterman (Fouvry-Kowalski-Michel)** — produits de twists
3. **Théorème de la valeur moyenne de Vinogradov** — moments de sommes exp polynomiales

### Statut de ces outils
- BDG 2015 : s'applique aux phases POLYNOMIALES (a^s), pas exponentielles (2^a). Adaptation non triviale.
- FKM : s'applique aux produits de fractions type Kloosterman. Possible pont via la structure multiplicative de ⟨2⟩.
- VMVT : même limitation que BDG (polynômes, pas exponentielles).

**Conclusion R85** : Le problème est réduit à une question PRÉCISE et BIEN DÉFINIE en théorie analytique des nombres, distincte des murs déjà identifiés. Mais les outils existants ne s'appliquent pas directement (phases exponentielles vs polynomiales).

---

# R86 — Innovation : Découplage Modulaire + Audit
## Type : I/X (innovation + investigation) | IVS : 7/10

### Tentative : Modular Decoupling Lemma (MDL)

**Idée nouvelle** : Réduire mod r = ord_p(2) pour convertir le simplexe en boîte.

Puisque 2^{A_i} mod p ne dépend que de A_i mod r, on pose b_i = A_i mod r.
Alors corrSum mod p = F(b₀,...,b_{k-1}) où F est définie sur la BOÎTE {0,...,r-1}^k.

Les compositions du simplexe avec A_i ≡ b_i mod r sont comptées par un poids W(b)
(stars-and-bars dans les quotients q_i = ⌊A_i/r⌋).

### Résultat du MDL
La décomposition est CORRECTE et NOUVELLE (pas dans la carte mentale).
MAIS le bound obtenu est INUTILE :

Pour p=5, r=4, k=21 :
- Chaque σ_i(t,v) atteint |σ| = √5 ≈ 2.24 (borne de Gauss EXACTE, pas améliorable)
- Le produit naïf (√5)^21 ≈ 2.2×10⁷ EXPLOSE
- L'erreur prédite ≈ C × p^{k/2} / (p·r) ≈ 10^{15} (ridicule vs réalité ≈ 3.3×10⁴)

### Diagnostic MDL
Le découplage modulaire convertit correctement le simplexe en boîte.
Mais le PRODUIT de k bornes de Gauss individuelles reste le bottleneck.
La conversion simplexe → boîte ne résout pas le problème de produit corrélé.

**MDL est un CADRE CORRECT mais QUANTITATIVEMENT MORT** par le même mur que R32 :
les bornes individuelles par facteur ne capturent pas la cancellation du produit.

### Tournoi des candidats (protocole R83)

**Candidat 1 — MDL (Modular Decoupling)** : Cadre nouveau, conversion simplexe→boîte CORRECTE. Mais borne quantitative MORTE ((√p)^k trop gros). **ÉLIMINÉ**.

**Candidat 2 — ACU (Anticorrélation CRT Universelle)** : N₀(d) ≤ ∏ N₀(pᵢ)/C^{ω-1} observé R35 et confirmé k=21. Si PROUVÉ, donne N₀(d) = 0 car C/d < 1. Mais AUCUN mécanisme de preuve identifié. Le "pourquoi" de l'anticorrélation est exactement le problème de produit corrélé (R85). **EN SUSPENS — réductible au verrou R85**.

**Candidat 3 — DEMC (Densité via Méthode du Cercle)** : Intégrale de Cauchy [x^S]∏g_i évaluée par arcs majeurs/mineurs. Méthode classique puissante. Mais les phases sont EXPONENTIELLES (2^a) et non polynomiales (a^s), ce qui sort du cadre standard Hardy-Littlewood. **EN SUSPENS — nécessite adaptation non triviale**.

### Survivants
**Aucun candidat ne passe le test de mordant du R83** :
- MDL quantitativement mort
- ACU et DEMC théoriquement vivants mais sans chemin de preuve identifié

---

# R87 — Synthèse et recommandation stratégique
## Type : S (synthèse) | IVS : 8/10

### Ce que R84-R86 ont apporté

1. **PREUVE k=21** : N₀(d(21)) = 0. Premier k dans le gap prouvé. Méthode reproductible pour d'autres k faisables. (Impact : 10/10 local, 3/10 global car k-par-k)

2. **Ratio Law haute précision** : Vérifiée à 4+ décimales pour k=21. Plus forte que toutes les vérifications précédentes. (Impact : 7/10, renforce la conjecture)

3. **Identification du VERROU PRÉCIS** : Le problème est réduit à borner des PRODUITS CORRÉLÉS de sommes de Gauss. Ce n'est NI un mur Weyl/Weil/LS/ET (ceux-ci concernent des facteurs individuels), NI un problème de conversion simplexe/boîte (résolu par MDL). C'est un problème de SOMMES MULTILINÉAIRES. (Impact : 9/10 pour le diagnostic)

4. **Cadre MDL** : La réduction modulaire convertit correctement le simplexe en boîte, mais ne résout pas le produit. Cadre CORRECT, borne MORTE. (Impact : 5/10 comme cadre, 0/10 comme borne)

### L'outil manquant (formulation finale)

**PROBLÈME OUVERT (PO-R87)** : Borner le produit

  ∏_{i=0}^{k-1} σ_i(t, v)  où  σ_i(t,v) = Σ_{b=0}^{r-1} ψ^{vb} · ω^{t · 3^{k-1-i} · 2^b}

pour t ≠ 0, uniformément en v, k, p.

**Borne individuelle connue** : |σ_i| ≤ √p (Gauss, tight).
**Borne naïve du produit** : ≤ p^{k/2} (INUTILE, croît exponentiellement).
**Borne heuristique du produit** : ≈ r^{k/2} (cancellation racine, non prouvée).
**Borne nécessaire** : |∏ σ_i| ≤ r^k · p^{-1-ε} (pour que l'erreur totale soit < 1).

Les TWISTS α_i = 3^{k-1-i} mod p forment une progression géométrique de raison 3^{-1} mod p. Cette structure géométrique spécifique est la CLÉ non exploitée.

### Recommandation

Le programme devrait :
1. **Publier la preuve k=21** comme résultat partiel solide
2. **Formuler PO-R87 proprement** comme problème ouvert en théorie analytique des nombres
3. **Explorer la piste multilinéaire** (Fouvry-Kowalski-Michel) pour les produits de twists géométriques
4. **NE PAS** faire du k-par-k computationnel (même si techniquement faisable pour 12/21 valeurs)
5. **Explorer si la structure géométrique des α_i** (progression en 3^{-1} mod p) permet un traitement spécial — c'est là que le projet a le plus de chances de trouver une prise nouvelle

---

# BILAN R84-R87

## Score global
- **R84** : IVS 9/10 — Preuve k=21, données haute précision
- **R85** : IVS 8/10 — Diagnostic racine, identification du verrou multilinéaire
- **R86** : IVS 7/10 — MDL cadre correct/borne morte, candidats audités honnêtement
- **R87** : IVS 8/10 — Synthèse, formulation PO-R87, recommandation

## Ce qui survit
- La preuve k=21 (FAIT)
- Le cadre MDL (simplexe → boîte, CORRECT mais insuffisant seul)
- Le problème ouvert PO-R87 (BIEN DÉFINI, NOUVEAU)
- La piste multilinéaire/twists géométriques (À EXPLORER)

## Ce qui meurt
- MDL comme outil de preuve autonome (borne ∝ p^{k/2} inutile)
- Tout espoir de preuve par sommes de caractères INDIVIDUELLES (Gauss tight)
- Les routes A (indépendance CRT) et C (cercle) sans nouvel outil sur les produits
