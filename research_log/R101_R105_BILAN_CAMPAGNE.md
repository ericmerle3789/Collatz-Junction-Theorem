# BILAN DE CAMPAGNE R101→R105

## Date : 14 mars 2026
## Brief : PromptR101.md — Campagne autonome (5 rounds exécutés sur 7 prévus)

---

## RÉSUMÉ EXÉCUTIF

La campagne R101→R105 a poursuivi l'exploration du front résiduel après la preuve inconditionnelle de T159 (R95→R100). Elle a produit **3 théorèmes** (2 prouvés, 1 conditionnel), **éliminé 7 nouvelles voies**, et identifié un **verrou combinatoire précis** ((H_k) : énergie additive k-linéaire) comme sous-problème du verrou analytique PO-R87.

**Résultat principal** : Le verrou des sommes exponentielles corrélées se RÉDUIT à un problème purement combinatoire (H_k). Cette réduction est le principal acquis conceptuel de la campagne. Aucune percée inconditionnelle n'a été obtenue.

**Score IVS global** : 7.3/10 (campagne honnête, progrès conceptuel, pas de percée).

---

## THÉORÈMES PRODUITS

### T162 [PROUVÉ — INCONDITIONNEL] — Formule exacte de n_eff

**Énoncé** : Pour r = ord_p(2) et k ≥ 2, le nombre de ℓ actifs (W_ℓ ≠ 0 a priori) est :
$$n_{\text{eff}}(r,k) = \gcd(r,k) - 1$$

**Preuve** : Les ℓ actifs satisfont r/gcd(ℓ,r) | k. Pour chaque diviseur d | gcd(r,k) avec d > 1, les ℓ avec gcd(ℓ,r) = r/d sont de la forme ℓ = (r/d)·m avec 1 ≤ m ≤ d-1, gcd(m,d) = 1. Leur nombre est φ(d). Total : n_eff = Σ_{d | gcd(r,k), d>1} φ(d) = gcd(r,k) - 1 par l'identité de Ramanujan Σ_{d|n} φ(d) = n. □

**Corollaires** :
- k premier (23,29,31,37,41) : n_eff ∈ {0, k-1}. Dichotomie totale.
- k composé (21=3·7) : n_eff ∈ {0, 2, 6, 20} selon gcd(r,21).
- Par Chebotarev : Prob(gcd(r,k) = 1) ≈ φ(k)/k. Pour k premier : ~(k-1)/k ≈ 96%.

**Impact** : Quantifie exactement le nombre de termes restants dans le reste R de SLS.

### T163 [PROUVÉ — INCONDITIONNEL] — Dichotomie 3∈H / 3∉H

**Énoncé** : Si 3 ∈ H = ⟨2⟩ mod p (i.e., ord_p(3) | ord_p(2)), alors pour tout ℓ ≥ 1 :
$$S_0^{(\ell)}(t \cdot \alpha_j) = \chi_\ell(\alpha_j)^{-1} \cdot S_0^{(\ell)}(t)$$
et donc |S_0^{(ℓ)}(t·α_j)| = |S_0^{(ℓ)}(t)| pour tout j.

**Preuve** : Pour α_j = 3^{k-1-j} ∈ H, changement h' = α_j·h dans la somme S_0^{(ℓ)}(t·α_j). L'invariance de H sous multiplication par α_j ∈ H donne la factorisation. □

**Conséquences** :
- Quand 3 ∈ H : ∏_j S_0^{(ℓ)}(t·α_j) = S_0^{(ℓ)}(t)^k · constante → W_ℓ = const · T_k(H, χ_ℓ) (somme de Jacobi généralisée). Mais cette route donne la même condition r > ~√p que T4. [ÉLIMINÉ comme voie d'amélioration]
- Quand 3 ∉ H : les magnitudes |S_0(t·α_j)| sont genuïnement DIFFÉRENTES. C'est le front actif pour la décorrélation.

**Impact** : Sépare le problème en deux cas structurellement distincts. Le cas 3∈H est fermé (pas de gain). Le cas 3∉H est le seul front actif.

### T164 [CONDITIONNEL sur (H_k)] — Borne améliorée via énergie additive multilinéaire

**Énoncé** : Soit p premier, r = ord_p(2), k ≥ 3, gcd(r,k) > 1, H = ⟨2⟩ ⊂ F_p*, 3 ∉ H. Sous l'hypothèse :

**(H_k)** : Pour tout sous-groupe multiplicatif H ⊂ F_p* d'ordre r et tout ensemble de shifts α_0,...,α_{k-1} formant une progression géométrique de raison 3^{-1}, l'énergie additive multilinéaire satisfait :
$$E_k(H; \alpha) = \#\{(h,h') \in H^{2k} : \sum \alpha_j(h_j-h'_j) = 0\} \leq C_k \cdot r^{2k-1}/p + C_k \cdot r^k$$

Alors |W_ℓ| ≤ C_k · p · r^{k/2} et la condition de T4 s'affaiblit à **r > p^{2/k}**.

**Gain** : Pour k=21 : de r > p^{0.595} (T4) à r > p^{0.095}. Pour k=41 : de p^{0.549} à p^{0.049}.

**Statut de (H_k)** :
- k = 2 : prouvé (Bourgain-Katz-Tao 2004)
- k ≥ 3 : OUVERT — sous-problème de PO-R87
- GRH n'aide pas directement
- Conjecture somme-produit forte (Erdős-Szemerédi) implique (H_k)

**Nature du gap** : CONDITIONNEL, PAS structurel. Pas d'impossibilité prouvée.

---

## DIAGNOSTICS MAJEURS

### D1 : T159 ne résout pas N₀(p) = 0

Quand gcd(r,k) = 1, T159 donne R = 0, donc N₀(p) = main term > 0.
T159 est un FILTRE (tue les ℓ inactifs) pas un EXTERMINATEUR (ne force pas N₀ = 0).
Le programme vers N₀(d) = 0 requiert soit : (a) un prime avec N_H(0) = 0 (rare), (b) le produit CRT multi-primes C/d < 1, (c) le contrôle du reste R.

### D2 : M_mix decorrelation [SEMI-FORMALISÉ]

M_mix = Σ_t |S_0^{(ℓ)}(t)|²·|S_0^{(ℓ)}(t·3)|² = r²p + O(pr²) quand 3 ∉ H.
Confirmé par séparation diagonal / off-diagonal + énergie additive BKT (E(H) ≤ r^{3-η}).
M_mix/M4 ≈ 1/2 (décorrélation), vs M_mix/M4 = 1 quand 3 ∈ H (corrélation parfaite).

### D3 : Réduction analytique → combinatoire

Le verrou sur les sommes exponentielles corrélées W_ℓ = Σ_t ∏_j S_0(t·α_j) se RÉDUIT à l'hypothèse (H_k) sur E_k(H;α). C'est un problème purement combinatoire d'énergie additive multilinéaire, distinct du verrou analytique originel.

C'est le **principal acquis conceptuel** de la campagne : une réduction du verrou, pas sa résolution.

---

## VOIES ÉLIMINÉES (7 NOUVELLES)

| # | Voie | Raison d'élimination | Round |
|---|------|---------------------|-------|
| 1 | Route 3∈H pour borne améliorée | Jacobi sums → même condition r > ~√p que T4 | R102 |
| 2 | Factorisation en blocs via Hölder | r > √p structurellement | R102 |
| 3 | A1 densité gcd(r,k)=1 | T159 est filtre, pas exterminateur | R103 |
| 4 | A2 structure χ_ℓ^k=1 | Même borne √p pointwise | R103 |
| 5 | Crible multiplicatif sur d(k) | Réduit à ACU/CRT product (R85) | R103 |
| 6 | Weil-Deligne sur Σ(ℓ) restreinte | Condition transcendante, hors cadre algébrique | R103 |
| 7 | Norme de bloc via ker(χ_ℓ^k) | Réduit à T163 route 3∈H, même condition | R103 |

---

## HIÉRARCHIE DES MURS (MISE À JOUR)

| Rang | Mur | Origine | Nature | Contournable ? |
|------|-----|---------|--------|----------------|
| 1 | Artin (ordres multiplicatifs) | 1927 | Fondamental | NON (ouvert 99 ans) |
| 2 | HGE (phases de Gauss) | Katz | Fondamental | NON (faisceau ouvert) |
| 3 | Parseval √p | R44 | Structurel | NON (exactement √p) |
| 4 | PO-R87 (produit corrélé) | R87 | Ouvert | RÉDUCTIBLE à (H_k) |
| 5 | **(H_k) énergie k-linéaire** | **R104** | **Combinatoire** | **OUVERT, k=2 connu (BKT)** |

---

## COMPARAISON AVANT / APRÈS CAMPAGNE

| Aspect | Avant R101 (fin R100) | Après R105 |
|--------|----------------------|------------|
| Survivant principal | T159 [PROUVÉ] | T159 + T162 + T163 [PROUVÉS] + T164 [COND] |
| Verrou identifié | "L²/L^∞ gap + corrélations" (vague) | (H_k) : énergie additive k-linéaire (précis) |
| Nature du verrou | Analytique | Combinatoire |
| Condition suffisante | r > p^{1/2+2/k} (T4) | r > p^{2/k} sous (H_k) |
| Voies mortes | ~124 | ~131 (+7 nouvelles) |
| Théorèmes totaux | ~161 | ~164 (+T162, T163, T164) |

---

## SCORE IVS DE LA CAMPAGNE

| Critère | Score | Commentaire |
|---------|-------|-------------|
| Rigueur mathématique | 9/10 | T162, T163 prouvés proprement. T164 honnêtement conditionnel. |
| Non-redondance | 9/10 | Aucun mort ressuscité. 7 nouvelles voies éliminées. |
| Lucidité diagnostique | 10/10 | Gap conditionnel, pas structurel. Réduction précise. |
| Mordance des résultats | 5/10 | T162-T163 vrais mais auxiliaires. T164 prometteur mais conditionnel. |
| Progrès vers N₀(d)=0 | 3/10 | Pas de fermeture. Le verrou (H_k) est ouvert. |
| Valeur pour la suite | 8/10 | (H_k) cible claire. Terrain nettoyé. |
| **SCORE GLOBAL** | **7.3/10** | **Campagne honnête, progrès conceptuel, pas de percée** |

---

## PROCHAINES ÉTAPES RECOMMANDÉES

1. **Recherche bibliographique (H_k)** : Explorer Shkredov (2013+), Schoen, Bourgain (2005+) pour des résultats sur l'énergie additive multilinéaire de sous-groupes multiplicatifs de F_p*. La question est bien posée et pourrait avoir une réponse partielle dans la littérature.

2. **Vérification computationnelle de T164** : Pour k=22..41 (Bloc 3), calculer p^{2/k} pour les primes p | d(k) et vérifier si ord_p(2) > p^{2/k}. Si oui systématiquement, T164+(H_k) fermerait ces cas conditionnellement. (Vérification, pas recherche.)

3. **Estimation directe de W_ℓ** : Méthode Fouvry-Kowalski-Michel pour éviter la perte Cauchy-Schwarz. Obstacle : S_0^{(ℓ)} est une somme partielle sur sous-groupe, pas un objet de type faisceau.

4. **Route alternative** : Si (H_k) s'avère durablement ouvert, explorer des approches évitant complètement le passage par W_ℓ : méthodes p-adiques, géométrie du simplexe CJT direct, ou reformulation L-fonctions.

---

## RÉFÉRENCES AJOUTÉES

- Bourgain, Katz, Tao (2004) : "A sum-product estimate in finite fields" — E(H) ≤ r^{3-η} pour sous-groupes multiplicatifs. Base de (H_k) pour k=2.
- Shkredov (2013+) : Énergie additive de sous-groupes multiplicatifs, bornes améliorées.
- Fouvry, Kowalski, Michel (2014) : Sommes multilinéaires de Kloosterman, stratification.
- Ramanujan : Σ_{d|n} φ(d) = n (utilisé dans T162).
- Goyal & Welch (2008) — déjà référencé, pertinent pour les conditions de type "r > p^ε".

---

*Bilan rédigé le 14 mars 2026. Campagne R101→R105 close.*
*Prochain round recommandé : R106 — recherche bibliographique (H_k).*
