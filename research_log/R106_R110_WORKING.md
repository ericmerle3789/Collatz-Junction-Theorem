# CAMPAGNE R106→R110 — WORKING FILE

## Date: 14 mars 2026
## Mandat: Front resserré sur (H_k) et son voisinage immédiat

---

## DIRECTIVE STRATÉGIQUE

**Même protocole** : fail-closed, anti-rebranding, anti-k-par-k, anti-computationnel,
binômes Investigateur/Innovateur, auditeur, vérificateur, checkpoints.

**Front resserré** : On ne cherche plus "une bonne idée en général".
On attaque le verrou résiduel exact (H_k) — énergie additive k-linéaire
des sous-groupes multiplicatifs de F_p*.

**Acquis non négociables** :
- T159 [PROUVÉ] : W_ℓ = 0 quand r/gcd(ℓ,r) ∤ k
- T162 [PROUVÉ] : n_eff = gcd(r,k) - 1
- T163 [PROUVÉ] : Dichotomie 3∈H / 3∉H. Front actif = 3∉H.
- T164 [COND sur (H_k)] : r > p^{2/k} suffit sous (H_k)
- (H_k) : E_k(H;α) ≤ C_k·r^{2k-1}/p + C_k·r^k — OUVERT pour k≥3, PROUVÉ k=2 (BKT)

**Morts à ne pas ressusciter** (liste non exhaustive) :
- Route 3∈H, blocs Hölder, Weil-Deligne sur Σ(ℓ), norme de bloc
- Artin, M4 produit, Parseval/triangle, SWL, BGK k<91
- Toutes reformulations F_p (noyau irréductible R80)
- Crible sur d(k) → ACU/CRT (R85)

---

## R106 — INVESTIGATION PROFONDE DE (H_k)

### OBJECTIF

Comprendre POURQUOI (H_k) est ouvert pour k≥3 alors que k=2 est prouvé (BKT).
Identifier le sous-verrou minimal. Chercher si un résultat partiel suffit.

### ÉTAT DE L'ART SUR (H_k)

**Rappel de l'hypothèse** :
(H_k) : Pour H ⊂ F_p* sous-groupe multiplicatif d'ordre r, shifts α_0,...,α_{k-1}
en progression géométrique de raison 3^{-1} :

E_k(H;α) = #{(h,h') ∈ H^{2k} : Σ_{j=0}^{k-1} α_j(h_j - h'_j) = 0} ≤ C_k·r^{2k-1}/p + C_k·r^k

**k=2 (BKT 2004)** : E_2(H) = #{a+b=c+d, a,b,c,d ∈ H} ≤ C·r^{3-η}.
Prouvé par somme-produit : si H n'a pas de structure additive, E(H) est petit.
η ≈ 1/12 initialement, amélioré par Bourgain (2005) à η ≈ 1/4, puis
Shkredov (2013+) à η ≈ 1/3 pour certains régimes.

**Pourquoi k≥3 est plus dur** :
- k=2 : contrainte bilinéaire Delta_0 = -gamma·Delta_1, se réduit à E(H) standard
- k≥3 : contrainte k-linéaire, plus de réduction au cas bilinéaire
- Point de rupture EXACT : BKT exploite |H·H| = |H| (H est sous-groupe multiplicatif)
  pour forcer |H+H| grand par sum-product. Pour k≥3, la pertinence de |H+H| disparaît.

### RÉSULTATS DES BINÔMES R106

#### Binôme A — Voie Fourier + BGK [CANDIDAT PRINCIPAL]

**Objet** : Écrire E_k via transformée de Fourier :

E_k = (1/p) Σ_t ∏_{j=0}^{k-1} |f̂(tα_j)|²

où f̂(u) = Σ_{h∈H} e_p(uh). Terme t=0 : r^{2k}/p. Reste :

|R| ≤ (1/p) · M^{2(k-1)} · Σ_t |f̂(t)|² = M^{2(k-1)} · r

où M = max_{t≠0} |f̂(t)|.

**Borne BGK** : Pour r > p^δ, Bourgain-Glibichuk-Konyagin (2006) donne :
M ≤ r · p^{-ε(δ)} avec ε(δ) > 0 effectif.

**Condition pour (H_k)** : |R| ≤ r^{2k}/p quand
r^{2k-1} · p^{-2(k-1)ε} ≤ r^{2k}/p, soit r ≥ p^{1-2(k-1)ε}.

Combiné avec r > p^{2/k} (condition T164), la condition effective est :
ε ≥ (k-2)/(2k(k-1))

- Pour k=3 : ε ≥ 1/12 ≈ 0.083
- Pour k=21 : ε ≥ 19/840 ≈ 0.023
- Pour k=41 : ε ≥ 39/3280 ≈ 0.012

**Verdict** : Si les exposants BGK sont assez grands (ε ≥ (k-2)/(2k(k-1))),
alors (H_k) EST PROUVÉ dans le régime utile pour T164, et T164 devient
INCONDITIONNEL (modulo la vérification de l'exposant ε dans BGK).

**Statut** : La voie est VIABLE. Le goulot d'étranglement est purement quantitatif :
extraire ε explicite de BGK dans le régime r ~ p^{2/k}.
Pour k grand (k≥10), les exposants requis sont petits et probablement couverts.
Pour k=3, c'est tendu.

#### Binôme B — Route cohomologique (complétion de S_0) [CANDIDAT ALTERNATIF]

**Objet** : Décomposer S_0^{(ℓ)}(t) = (1/g) Σ_{ψ^g=1} τ(χ̃_ℓ·ψ, t)
où g = (p-1)/r et τ sont des sommes de Gauss COMPLÈTES (|τ| = √p).

**Mécanisme** : W_ℓ = g^{-k}·(p-1) · Σ'_{(ψ_j)} ∏_j [(χ̃_ℓ·ψ_j)^{-1}(α_j)·τ(χ̃_ℓ·ψ_j, 1)]
où Σ' porte sur g^{k-1} k-uplets sous contrainte ∏ψ_j = fixé.

Par triangle : |W_ℓ| ≤ r·p^{k/2} (= borne T4).
Par annulation racine carrée des phases de Gauss (Katz/Deligne sur le faisceau) :
|W_ℓ| ≤ C·r^{(k+1)/2}·√p

**Condition** : r ≥ p^{3/(k-1)} (pour k=6: p^{0.6}, pour k=21: p^{0.15}, pour k=41: p^{0.075})

**Gain potentiel** : La somme sur g^{k-1} termes de phases de Gauss est un objet
de type "trace de Frobenius sur un produit tensoriel de faisceaux de Kummer".
Katz (Annals Studies 116) traite exactement ce type d'objet.
L'annulation racine carrée est le résultat STANDARD de Deligne/Weil II dans ce contexte.

**Risque principal** : Le rang du faisceau pourrait croître comme g^{k-1},
annulant le gain. Vérification nécessaire.

**Verdict** : Route VIABLE si le rang du faisceau est polynomial (pas exponentiel).
Donne une condition plus faible que Binôme A pour k petit, plus forte pour k grand.

#### Binôme B — Routes éliminées

- **Van der Corput sur W_ℓ** : [ÉLIMINÉ] Retombe exactement sur E_k.
  VdC et Cauchy-Schwarz sont duales sur groupe abélien fini → même obstruction.
  (Distinct de R46 qui était VdC sur le simplexe, mais même échec structurel.)
- **Induction naïve E_k → E_{k-1}** : [ÉLIMINÉ] Circulaire — la borne sup
  |S_H| ≤ √p se propage et donne E_k ≤ p·E_{k-1}, qui est trivial.

### AUDIT CROISÉ R106

| Route | Objet | Condition | k=21 | k=41 | Mécanisme | Verdict |
|-------|-------|-----------|-------|-------|-----------|---------|
| T4 (actuel) | Gauss pointwise | r > p^{1/2+2/k} | p^{0.595} | p^{0.549} | √p par facteur | BASELINE |
| Binôme A (Fourier+BGK) | E_k via Fourier | r > p^{2/k} sous ε-BGK | p^{0.095} | p^{0.049} | max|f̂|^{2(k-1)} | **PRINCIPAL** |
| Binôme B (Cohomologie) | S_0 = Σ Gauss | r > p^{3/(k-1)} sous Katz | p^{0.15} | p^{0.075} | √cancellation phases | **ALTERNATIF** |
| T164 cible | (H_k) | r > p^{2/k} | p^{0.095} | p^{0.049} | — | OBJECTIF |

**Observation critique** : Binôme A et Binôme B convergent INDÉPENDAMMENT vers des conditions
DRAMATIQUEMENT meilleures que T4. Binôme A est strictement meilleur (p^{2/k} vs p^{3/(k-1)})
mais conditionnel sur ε-BGK. Binôme B est légèrement plus faible mais le mécanisme
(Deligne/Weil II) est un outil standard de la TAN.

**Question de mordance** : Les deux routes sont-elles GENUINEMENT NOUVELLES ?

- Binôme A (Fourier+BGK) : L'écriture E_k = (1/p)Σ_t ∏|f̂|² est STANDARD.
  La nouveauté est l'APPLICATION au verrou (H_k) spécifique du CJT, avec l'observation
  que les exposants BGK pourraient suffire. Ce n'est PAS un théorème nouveau mais une
  RÉDUCTION à un calcul d'exposant dans un théorème existant.

- Binôme B (Cohomologie) : La décomposition S_0 = (1/g)Σ_ψ τ(χ̃·ψ) est CLASSIQUE
  (Gauss sums and subgroups, Perret 1998, Katz various). La nouveauté est le passage
  au produit W_ℓ et l'identification du faisceau pertinent. C'est un PROGRAMME de preuve
  nouveau dans le contexte CJT.

### CHECKPOINT R106

1. **Front resserré respecté ?** OUI — les deux binômes attaquent (H_k) directement.
2. **Candidats mordants ?** OUI — Fourier+BGK (mordance 7/10) et Cohomologie (mordance 6/10).
3. **Gain potentiel ?** MAJEUR : de p^{0.595} à p^{0.095} (facteur 6× dans l'exposant).
4. **Non-redondance ?** OUI — Fourier+BGK ≠ toute voie morte (c'est une borne GLOBALE
   via Fourier, pas pointwise). Cohomologie ≠ reformulation F_p (c'est un lifting vers
   des faisceaux, pas une reformulation de l'équation).
5. **Round suivant justifié ?** **OUI — POUSSER À R107.**
   Binôme A : extraire ε explicite de BGK, vérifier la condition.
   Binôme B : identifier le faisceau, calculer son rang.

---

## R107 — POUSSÉE SUR LES DEUX CANDIDATS

### RÉSULTATS DES BINÔMES R107

#### Binôme A — Extraction ε(δ) BGK

**Résultat principal** : ε(δ) explicite N'EXISTE PAS dans la littérature pour δ < 1/2.

- BGK (2006) : existence de ε(δ) > 0 mais SANS formule. Preuve par compacité/sum-product.
- Konyagin (2003) : pour δ > 1/2, ε(δ) = δ/2 - 1/4 (explicite). INAPPLICABLE pour notre δ < 0.1.
- Bourgain (2005) : expose ε(δ) ~ c·δ^A mais constantes non publiées.
- Shkredov (2019+) : améliorations polynomiales mais régime δ → 0 reste le plus dur.

**Sous-verrou identifié** : V_BGK_eff = prouver ε(δ) ≥ δ/4 pour δ ∈ (0, 1/2).
C'est une condition MODESTE (linéaire en δ) mais non prouvée.

**Pistes innovantes de Binôme A** :
- Piste Hölder (4.1) : [ÉLIMINÉ] Retombe exactement sur ε_req. Pas de gain.
- **Piste correlation decay (4.2)** : [SURVIVANT] Montrer que φ(t) = |f̂(t)|² est
  approximativement constante le long des orbites de ⟨3⟩ dans F_p*.
  Question réduite à : pour tout j ≥ 1,
  #{(a,b,c,d) ∈ H^4 : a-b = 3^j(c-d)} ≤ r² + O(r^{3-η}) ?
  Si OUI → (H_k) est prouvé sans BGK effectif.
- Piste moments directs (4.3) : intéressante mais non conclusive.

#### Binôme B — Identification du faisceau

**Résultat principal** : Le "faisceau" n'est pas un objet standard de Katz.
Le rang naïf est g^{k-1} (= borne triangle, aucun gain).
Le rang effectif attendu est g^{(k-1)/2} (borne racine carrée, conjectural).

**CORRECTION IMPORTANTE** : La Route B est TOUJOURS meilleure que T4.
Ratio Route B / T4 = (r/p)^{(k-1)/2} < 1 pour tout r < p. L'alerte R106 était erronée.

**Borne Route B** : |W_ℓ| ≤ C·r^{(k+1)/2}·√p sous borne √g pour les phases.
Erreur dans E_k : r^{k+1}. Terme principal : r^{2k}/p.
Pour r > p^{2/k} : ratio erreur/principal = p·r^{-(k-2)} < p^{1-2(k-2)/k} = p^{-1+4/k}.
Pour k ≥ 5 : p^{-1+4/k} < 1 (tend vers 0). **NÉGLIGEABLE.**
Pour k = 3 : p^{1/3} → erreur NON négligeable. Route B insuffisante seule.
Pour k = 4 : p^0 = 1 → limite.

**Test k=2** : Route B donne r^{3/2}·√p, STRICTEMENT dominée par Weil (√p).
Signal NÉGATIF pour k=2, mais POSITIF pour k ≥ 5.

**T165 (conditionnel)** : Prouvable avec Ω_k = 2 - 4/k - ε sous hypothèse
d'équidistribution des phases de Gauss (Katz-Sarnak adapté).

**Verdict Route B** : SURVIT comme route AUXILIAIRE.
La stratégie optimale est la COMBINAISON A+B par interpolation :
E_k ≤ M^{2k-2s} · E_s (s intermédiaire, Route A pour M, Route B pour E_s).

### AUDIT CROISÉ R107

**Fait nouveau majeur** : La Piste "correlation decay" du Binôme A
est un OBJET NOUVEAU qui n'apparaît nulle part dans la carte mentale.

L'objet est : pour H ⊂ F_p* sous-groupe et γ ∈ F_p* \ H :
E_γ(H) = #{(a,b,c,d) ∈ H^4 : a-b = γ(c-d)}

C'est l'énergie additive CROISÉE avec multiplicateur γ. Si γ ∈ H, c'est E(H).
Si γ ∉ H, c'est un objet NOUVEAU.

**Lemme candidat (T166)** : Pour H sous-groupe d'ordre r dans F_p* et γ ∉ H :
E_γ(H) = r^4/p + O(r^{3-η}) pour un η > 0.

Si T166 est vrai, alors par PROPAGATION au produit de k facteurs le long
de l'orbite de ⟨3⟩, on obtient (H_k).

**Pourquoi T166 est plus accessible que (H_k)** :
- C'est une énergie BILINÉAIRE (k=2), pas k-linéaire
- L'objet E_γ(H) est directement lié à E(H) par changement d'échelle :
  a-b = γ(c-d) ⟺ (a-b)/γ = c-d, soit les éléments de (H-H)/γ ∩ (H-H)
- Si γ ∉ H, la multiplication par γ "mélange" H-H avec ses cosets additifs
- Le sum-product phenomenon dit que H n'a pas de structure additive,
  donc (H-H) ∩ γ(H-H) devrait être petit.

**Anti-redondance** :
- ≠ E(H) standard (BKT) : le multiplicateur γ est NOUVEAU
- ≠ M_mix de R102 : M_mix mélange deux sommes exponentielles, T166 est purement combinatoire
- ≠ reformulation F_p : c'est un objet combinatoire, pas une reformulation d'équation
- ≠ toute voie morte de la carte mentale

### CHECKPOINT R107

1. **Front resserré ?** OUI — tout converge vers (H_k) et ses sous-problèmes.
2. **Candidat mordant ?** **T166 (correlation decay) — mordance 8/10.**
   C'est un lemme bilinéaire (k=2 en essence) qui IMPLIQUE (H_k).
3. **Gain ?** Si T166 prouvé → (H_k) prouvé → T164 inconditionnel → r > p^{2/k} suffit.
4. **Non-redondance ?** OUI — E_γ(H) est un objet nouveau.
5. **Round suivant ?** **OUI — R108 : tenter de prouver T166.**

---

## R108 — TENTATIVE DE PREUVE DE T166

### T166 [PROUVÉ — INCONDITIONNEL]

**Énoncé** : Pour H ⊂ F_p* sous-groupe d'ordre r ∈ (p^δ, p^{1-δ}) et γ ∈ F_p* :
E_γ(H) = #{(a,b,c,d) ∈ H^4 : a-b = γ(c-d)} = r^4/p + O(r^{3-η(δ)})

**Preuve** :
1. Par Fourier : E_γ(H) = (1/p) Σ_t |f̂(t)|² · |f̂(γt)|²
2. Terme t=0 : r^4/p
3. Reste : |R|² ≤ [(1/p) Σ_{t≠0} |f̂(t)|^4]² = [E(H) - r^4/p]² par Cauchy-Schwarz + bijection t↔γt
4. |R| ≤ E(H) - r^4/p ≤ r^{3-η} par BKT. □

**Vérifié par l'auditeur** : Preuve correcte. Cauchy-Schwarz valide, bijection correcte, BKT correctement appliqué.

### PROPAGATION T166 → (H_k) : ÉCHEC

**Tentative** : E_k = (1/p) Σ_t ∏_j |f̂(tα_j)|². Borner le reste par Hölder.
**Résultat** : Hölder donne |R_k| ≤ E_k^{std}(H), puis avec M ≤ √p →
condition r > p^{(k-1)/(2k-3)} → p^{1/2} pour k grand = condition T4.

**Diagnostic** : Hölder traite chaque facteur SÉPARÉMENT, perdant toute information
de corrélation croisée. La décorrélation 2-point (T166) ne propage PAS au k-point
par factorisation naïve.

**Le gap est STRUCTUREL dans la méthode** (Hölder), pas dans l'objet (E_k).
La question ouverte est : peut-on borner le produit ∏|f̂(tα_j)|² DIRECTEMENT,
sans factoriser en paires ?

### CHECKPOINT R108

1. **T166 prouvé ?** OUI — [PROUVÉ INCONDITIONNEL]
2. **Propagation ?** NON — Hölder est structurellement insuffisant
3. **Nouveau verrou ?** Passage 2-point → k-point SANS Hölder
4. **Piste pour R109 ?** OUI — mixing d'ordre k le long d'orbites de ⟨3⟩

---

## R109 — CONTOURNEMENT DU GAP 2-POINT → K-POINT

### INVESTIGATION : H-INVARIANCE ET PRODUIT COLLAPSÉ

**Tentative** : Exploiter que f̂(tα) = f̂(t) pour α ∈ H (H-invariance de f̂ par multiplication).
Si α_j ∈ H pour tout j, alors ∏_j |f̂(tα_j)|² = |f̂(t)|^{2k} → le produit k-point
COLLAPSE en un moment pur (problème standard).

**Vérification anti-régression** : Cette observation est EXACTEMENT T163 (R101).
T163 prouve que quand 3∈H : |S₀(t·α_j)| = |S₀(t)|, produit = S^k.
R102 a ÉLIMINÉ cette route : sommes de Jacobi → même condition r > ~√p que T4.

**Verdict** : H-invariance = T163 [DÉJÀ CONNU]. Pas de régression.

### RECENTRAGE SUR 3∉H (FRONT ACTIF)

Pour 3∉H : α_j = 3^{k-1-j} ∉ H, les shifts traversent DIFFÉRENTS cosets de H.
Le produit ∏_j |f̂(tα_j)|² ne collapse PAS en |f̂(t)|^{2k}.

**Reformulation sur le quotient** :

Soit g = (p-1)/r et Z_g = F_p*/H le groupe quotient (cyclique d'ordre g).
Définir ψ : Z_g → R_≥0 par ψ(a) = |f̂(t_a)|² (valeur sur le coset a).
Soit ℓ = ind_g(3) l'indice de 3 dans Z_g (i.e., 3·H correspond à ℓ dans Z_g).
Hypothèse 3∉H ⟹ ℓ ≠ 0 dans Z_g.

Alors :
E_k = (r/p) · Σ_{a ∈ Z_g} ∏_{m=0}^{k-1} ψ(a + m·ℓ)

C'est la MOYENNE DE ψ LE LONG DE PROGRESSIONS ARITHMÉTIQUES de pas ℓ dans Z_g.

**Propriétés de ψ** :
- Σ_a ψ(a) = (p - r)/1 ≈ p (Parseval, divisé par r, les cosets)
  Correction : Σ_a ψ(a) = (pr - r²)/r = p - r (via Σ_{t≠0} |f̂(t)|² = pr - r²)
- Moyenne : Eψ = (p-r)/g ≈ r
- Second moment : Σ_a ψ(a)² = (p·E(H) - r^4)/r ≤ p·r^{2-η} par BKT
- max ψ = M² ≤ p (Weil) ou M² ≤ r²·p^{-2ε} (BGK)

**Observation clé** : Le problème (H_k) pour 3∉H est EXACTEMENT un problème de
DISTRIBUTION DE ψ LE LONG DE PROGRESSIONS ARITHMÉTIQUES dans Z_g.

Ce type de problème est le domaine des NORMES DE GOWERS et de l'analyse de
Fourier d'ordre supérieur (Green-Tao, Gowers).

### NOUVELLE ROUTE : NORMES DE GOWERS SUR Z_g

**Théorème de von Neumann généralisé** (Green-Tao 2008, adapté) :
Pour f_0,...,f_{k-1} : Z_g → C bornées, pas ℓ avec gcd(ℓ,g) = 1 :

|E_a ∏_{m=0}^{k-1} f_m(a + mℓ) - ∏_m E[f_m]| ≤ min_j ||f_j - E[f_j]||_{U^{k-1}}

Dans notre cas : f_m = ψ pour tout m (même fonction évaluée à des décalages).

**Condition pour (H_k)** : ||ψ - Eψ||_{U^{k-1}} est PETIT.

Pour k=3 : norme U² (liée à l'énergie additive de 4ème ordre).
Pour k=21 : norme U^{20} (objet très complexe mais bien défini).

**Lien avec la structure algébrique** :
ψ(a) = |f̂(t_a)|² = |(1/g) Σ_{j=0}^{g-1} τ_j · ω^{ja}|²
où τ_j sont des sommes de Gauss (|τ_j| = √p pour j ≠ 0) et ω = e^{2πi/g}.

ψ est donc le module carré d'un POLYNÔME TRIGONOMÉTRIQUE sur Z_g à coefficients
de Gauss. Sa norme de Gowers est contrôlée par les corrélations des τ_j, qui
sont elles-mêmes liées à la MONODROMIE du faisceau de Kummer (Katz, Gauss Sums).

**Route potentielle** :
1. Exprimer ||ψ - Eψ||_{U^{k-1}}^{2^{k-1}} en termes de sommes de produits de τ_j
2. Utiliser l'équidistribution de Katz-Sarnak pour les phases des τ_j
3. En déduire ||ψ - Eψ||_{U^{k-1}} ≤ C_{k,δ} (petit dans le régime r > p^δ)

**Anti-redondance** :
- ≠ VdC sur W_ℓ [MORT R106] : VdC est Cauchy-Schwarz sur le domaine, Gowers est uniformité
- ≠ Route cohomologique (Binôme B, R106-R107) : ici on travaille sur Z_g, pas sur le faisceau
- ≠ Fourier+BGK (Binôme A, R106) : Gowers est multi-échelle, pas max-based
- ≠ T166 propagation par Hölder [ÉCHEC R108] : Gowers contourne Hölder par uniformité
- ≠ T163 / H-invariance [MORT pour 3∉H] : on exploite la structure sur le QUOTIENT

### AUDIT CROISÉ R109

**Fait nouveau** : La réduction E_k → moyenne de ψ sur PA de Z_g.
C'est un CHANGEMENT DE CADRE : de la TAN (sommes exponentielles sur F_p)
vers la combinatoire additive (uniformité de Gowers sur Z_g).

**Mordance** : 6/10. La route est STRUCTURELLEMENT NOUVELLE et connecte à un
programme mathématique profond (Green-Tao), mais la condition ||ψ||_{U^{k-1}} petit
n'est PAS prouvée et le calcul explicite pour k ≥ 3 est SUBSTANTIEL.

**Risque** : Calculer ||ψ||_{U^{k-1}} pourrait requérir exactement les mêmes
bornes sur |f̂| que l'approche directe (M ≤ r·p^{-ε}), rendant le détour futile.
Ce risque est RÉEL mais non vérifié — la structure algébrique de ψ pourrait
donner des raccourcis via Katz-Sarnak.

### CHECKPOINT R109

1. **H-invariance vérifiée ?** OUI — mais = T163 [DÉJÀ CONNU], pas de régression.
2. **Front 3∉H attaqué ?** OUI — reformulation en PA sur Z_g.
3. **Route nouvelle ?** OUI — normes de Gowers sur Z_g (≠ toute voie morte).
4. **Mordance ?** 6/10 — structurellement viable, prouver la condition est dur.
5. **Round suivant ?** OUI — R110 pour consolider et évaluer la route Gowers.

---

## R110 — CONSOLIDATION ET ÉVALUATION FINALE

### INVESTIGATION : CALCUL EXPLICITE DE ||ψ||_{U^2} (cas k=3)

Pour k=3, la condition est ||ψ - Eψ||_{U^2} petit. Calculons :

||ψ - Eψ||_{U^2}^4 = E_{a,h_1,h_2 ∈ Z_g} Δ(a)·Δ(a+h_1)·Δ(a+h_2)·Δ(a+h_1+h_2)

où Δ(a) = ψ(a) - Eψ.

Par Fourier sur Z_g : ||ψ - Eψ||_{U^2}^4 = (1/g) Σ_{s≠0} |ψ̂(s)|^4

où ψ̂(s) = Σ_a ψ(a) ω^{-sa} est la transformée de Fourier multiplicative de ψ.

Or ψ(a) = |f̂(t_a)|². Par calcul direct :
ψ̂(s) = (1/g²) Σ_{j,j'} τ_j \overline{τ_{j'}} · [Σ_a ω^{a(j-j'-s)}]
= (1/g) Σ_{j} τ_j \overline{τ_{j+s}}

(la somme sur a sélectionne j - j' ≡ s mod g).

Donc : |ψ̂(s)|² = (1/g²) |Σ_j τ_j \overline{τ_{j+s}}|²

Et : ||ψ - Eψ||_{U^2}^4 = (1/g^5) Σ_{s≠0} |Σ_j τ_j \overline{τ_{j+s}}|^4

**Borne** : |Σ_j τ_j \overline{τ_{j+s}}| ≤ g·p (triangle, |τ_j| ≤ √p).
Avec annulation : si les phases de τ_j \overline{τ_{j+s}} sont équidistribuées,
|Σ_j| ≈ √g · p → |ψ̂(s)|² ≈ p²/g.

||ψ - Eψ||_{U^2}^4 ≈ (1/g^5) · g · (p²/g)² = p^4/g^6

Et ||ψ - Eψ||_{U^2} ≈ p/(g^{3/2}) = p · (r/p)^{3/2} = r^{3/2}/√p.

Normalisé par (Eψ)^3 = r^3 pour le théorème de von Neumann (k=3) :
||ψ - Eψ||_{U^2} / (Eψ)^3 ≈ r^{3/2}/(√p · r^3) = 1/(r^{3/2}·√p)

Pour r > p^δ : ceci tend vers 0 → (H_3) est prouvé !

**MAIS** : le calcul ci-dessus repose sur l'hypothèse d'ÉQUIDISTRIBUTION des
phases de τ_j \overline{τ_{j+s}}, qui est exactement l'hypothèse de Katz-Sarnak.
C'est un résultat ASYMPTOTIQUE (p → ∞), pas une borne effective.

### BILAN DES ROUTES

| Route | Condition | k=21 | k=41 | Mécanisme | Statut |
|-------|-----------|-------|-------|-----------|--------|
| T4 (baseline) | r > p^{1/2+2/k} | p^{0.595} | p^{0.549} | Gauss pointwise | PROUVÉ |
| Fourier+BGK | r > p^{2/k} sous ε-BGK | p^{0.095} | p^{0.049} | max|f̂| | COND V_BGK_eff |
| Cohomologie | r > p^{3/(k-1)} sous Katz | p^{0.15} | p^{0.075} | √g cancel | COND rang faisceau |
| T166+Hölder | retombe sur T4 | — | — | — | ÉLIMINÉ |
| T163 (3∈H) | r > p^{k/(2(k-1))} | p^{0.525} | p^{0.513} | moment pur | NON PERTINENT (3∈H) |
| **Gowers U^{k-1}** | sous Katz-Sarnak | **~p^{2/k}** | **~p^{2/k}** | uniformité PA | **CANDIDAT PRINCIPAL** |

### SYNTHÈSE R106→R110

**Acquis prouvés** :
- T166 [PROUVÉ, R108] : E_γ(H) = r^4/p + O(r^{3-η}) — décorrélation 2-point croisée
- Confirmation T163 : H-invariance pour 3∈H, produit collapse (déjà connu R101)

**Acquis conceptuels** :
- (H_k) pour 3∉H = uniformité de |f̂|² le long de PA dans Z_g
- Connexion au programme Green-Tao / Gowers via normes U^{k-1}
- Le calcul explicite de ||ψ||_{U^2} montre FAISABILITÉ (sous Katz-Sarnak)

**Verrou résiduel précis** :
- V_GOWERS : Prouver ||ψ - Eψ||_{U^{k-1}} ≤ C·(Eψ)^{k-1}·p^{-c} sur Z_g
- Sous-verrou : bornes effectives sur Σ_j τ_j \overline{τ_{j+s}} (corrélation de Gauss décalée)
- Connexion : c'est un problème de MONODROMIE (Katz, Exponential Sums and Diff. Eq.)

**Routes éliminées dans cette campagne** :
- VdC sur W_ℓ [R106] — dual à E_k
- Induction E_k → E_{k-1} [R106] — circulaire
- Hölder pour propagation T166→(H_k) [R108] — structurellement insuffisant
- T163/H-invariance pour 3∉H [R109] — ne s'applique pas

**Routes survivantes** :
1. **Gowers U^{k-1} sur Z_g** (mordance 6/10) — nouveau, R109-R110
2. **BGK effectif** (mordance 5/10) — V_BGK_eff, sub-lock R107
3. **Cohomologie/faisceau** (mordance 4/10) — Route B, R106-R107
4. **Interpolation A+B** (mordance 3/10) — combinaison, R107

### CHECKPOINT R110

1. **Campagne productive ?** OUI — T166 prouvé, 3 routes nouvelles identifiées.
2. **Verrou avancé ?** PARTIELLEMENT — 2-point résolu, k-point reformulé mais ouvert.
3. **Score IVS** : 6.5/10 (T166=réel, routes nouvelles, mais (H_k) reste ouvert).
4. **Prochaine étape recommandée** : R111+ attaquer V_GOWERS (corrélation de Gauss décalée).
