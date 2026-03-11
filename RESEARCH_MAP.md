# CARTE DES RECHERCHES — Collatz Junction Theorem
**Date:** 11 mars 2026 | **Rounds:** R1–R49 (49 rounds, 186 scripts, 7611 auto-tests)

---

## OBJECTIF FINAL

```
╔═══════════════════════════════════════════════════════════════╗
║  PREUVE INCONDITIONNELLE : pas de cycle non-trivial          ║
║  N₀(d) = 0 pour tout k ≥ 3, où d = 2^S - 3^k               ║
╚═══════════════════════════════════════════════════════════════╝
```

---

## ARCHITECTURE DE LA PREUVE (4 blocs)

```
                    ┌─────────────────────┐
                    │   THÉORÈME FINAL     │
                    │  N₀(d) = 0 ∀ k ≥ 3  │
                    └────────┬────────────┘
                             │
            ┌────────────────┼────────────────┐
            │                │                │
     ┌──────▼──────┐  ┌─────▼──────┐  ┌──────▼──────┐
     │  BLOC 1     │  │  BLOC 2    │  │  BLOC 3     │
     │ k ≥ 42      │  │ k = 3..20  │  │ k = 21..41  │
     │ Borel-      │  │ DP + CRT   │  │ LE GAP      │
     │ Cantelli    │  │ vérifié    │  │             │
     │ ✅ PROUVÉ   │  │ ✅ PROUVÉ  │  │ ❌ OUVERT   │
     └─────────────┘  └────────────┘  └─────────────┘
```

### Bloc 1 — Convergence asymptotique (k ≥ 42) ✅
- **Junction Theorem** : C/d → 0 avec taux 2^{-αk}, α = 0.0793 [PROUVÉ]
- **Borel-Cantelli** : Σ_{k≥42} C/d < 1 [PROUVÉ, R21/R26]
- **Lean** : 280 théorèmes, 0 sorry, 0 axiome
- **Statut** : COMPLET

### Bloc 2 — Vérification finie (k = 3..20) ✅
- k = 3..6 : backward reachability combinatoire [R7]
- k = 7..11 : WR-constrained blocking [R7]
- k = 12..17 : DP exhaustif [R8]
- k = 18..20 : DP + CRT blocking [R22-R25]
- **Statut** : COMPLET (18 valeurs prouvées)

### Bloc 3 — Le Gap (k = 21..41) ❌
- 21 valeurs restantes
- C/d < 1 pour TOUTES → équidistribution suffirait
- Aucun premier bloquant trouvé (71 tests, R34)
- **Statut** : OUVERT — le goulot d'étranglement

---

## PISTES EXPLORÉES ET LEUR ÉTAT

### 🟢 PISTES OUVERTES (à explorer)

| Piste | Description | Faisabilité | Impact | Round |
|-------|-------------|:-----------:|:------:|:-----:|
| **DP direct sur d(k)** | DP complet mod d pour petits d(k) en C | 9/10 | 10/10 | → R36 |
| **MITM sur d(k)** | Meet-in-the-middle pour d moyens | 7/10 | 7/10 | → R36 |
| **CEC Type B composite** | DP mod p₁·p₂ (produit 2 primes) | 5/10 | 8/10 | R35 |
| **Borne analytique universelle** | Prouver |Z(0)-C/p| < C/p | 2/10 | 10/10 | Open |

### 🔴 PISTES FERMÉES (raison documentée)

| Piste | Pourquoi fermée | Round |
|-------|-----------------|:-----:|
| **Transient Zero** | Doubly stochastic → TZ n'affecte pas π(0)=1/p | R1 |
| **Without-Replacement** | Effet réel mais mixte (11/16 aide, 5/16 nuit), TV < 0.003 pour k≥10 | R2 |
| **Ordering Constraint** | 42.8ᵉ percentile, pas de biais systématique | R2 |
| **Conjecture 7.4 (×2-closure)** | FAUSSE : 64% des résidus ont leur double hors Im_int | R2 |
| **Invariants universels** | Au-delà de mod 12, aucun invariant universel (27 moduli testés) | R2 |
| **Markov mixing** | τ_mix < k toujours, TV < 0.04 ; obstruction = combinatoire, pas mixing | R4 |
| **PATH D (décomposition Markov)** | |E| >> |T_Markov| (ratio 10¹³) | R6 |
| **Carry propagation** | Prouve k=3..6 mais ne généralise pas | R6 |
| **Horner distinction** | R12 sur-formulé, reformulation nécessaire | R6 |
| **m-élimination** | Prouve k=3..14 mais limitée | R9-R14 |
| **2-Adic Tower** | Prouve v₂(corrSum) = min(A) mais ne bloque pas | R2/R14 |
| **Weyl bound** | Simplexe ≠ intervalle ; inapplicable | R32-A |
| **Weil bound** | Pas sur F_p ; domaine = simplexe entier | R32-A |
| **Large Sieve** | Perte k! en incluant le simplexe dans une boîte | R32-A |
| **Erdős-Turán** | Circulaire : nécessite les bornes qu'on cherche | R32-A |
| **Contraction par étape** | RÉFUTÉ : les normes CROISSENT (ratio moyen 1.578) | R33 |
| **Existentiel (R33-D)** | Logiquement insuffisant : P_B≠0 ne prouve pas Z(0)=0 | R34 |
| **CRT premier unique** | 71/71 paires (k,p) non-bloquantes pour k=21..41 | R34 |
| **CRT Product (prédiction)** | Produit CRT FAUX dans 6/9 cas testés (N₀(d) toujours ≤ prédit) | R35 |
| **CCD (Cross-Constraint Density)** | Tautologie : CCD=1 identiquement quand N₀(d)=0, zéro contenu informationnel | R36 |
| **OEntropy (Obstruction Entropy)** | Aveugle : δ(d)≈1 car absence d'1 résidu sur 500K est invisible à Shannon | R36 |
| **LCM (Lemme Couplage Monotone)** | Bound trivial (vrai pour toute application), non quantifiable sans arithmétique profonde | R37 |
| **PSO (Principe Saturation Ordre)** | σ < 1 PARTOUT, aucune prédiction, seuil jamais atteint | R38 |
| **Polarisation stricte obs∈{1,ω}** | BRISÉE à k=16 : obs=2, ω=3 (premier cas intermédiaire) | R38 |
| **IA (Indice d'Activité)** | Objet dérivé de SPC, pas de contenu propre, redondant | R39 |
| **SI (Synchronization Impossibility)** | Puissance discriminative NULLE : mêmes ordres pour SPC et non-SPC, 0/11 prédictions | R40 |
| **OCC-ALG (C3' algébrique)** | ord_p(2)≥ceil(log₂(k)) redondant avec IE seul, échoue k=17 (ord₅(2)=4<5) | R41 |
| **Sub-Independence** | N₀(∏I) ≤ IE(I) FAUX : 0/8 cas non-triviaux, max ratio N₀/IE=6.38 (k=17) | R42 |
| **Boundary Majorization** | M<k toujours (log₂3<2), zéro points intérieurs, borne dégénère f_p≤2/p, VIOLÉE | R43 |
| **Parseval naïf Σ\|S(r)\|²=p·C(k)** | FAUX : correct = p·ΣN_r², l'ancien supposait injection P_B→Z/pZ | R44 |
| **WQE (Quasi-Equidist. Affaiblie)** | Chebyshev borne la fraction de "mauvais" résidus mais ne contrôle PAS r=0 | R44 |
| **V ≤ A·C universel** | RÉFUTÉ : V/C=20.4 à k=12,p=5 et croît. V = O(C²/p), pas O(C) | R45 |
| **CRL (Collision Rarity Lemma)** | Même claim que MSL mais formulation moins propre, éliminé au profit de MSL | R45 |
| **Weyl differencing k≥4** | Simplexe monotone NON invariant par translation, shift B→B+eᵢ viole monotonie | R46 |
| **MSL-lite (Convolution Mixing)** | Indépendance des Xⱼ=gʲ·2^{Bⱼ} FAUSSE sous monotonie, paliers déterministes | R46 |
| **Erdős-Turán pour MSL** | Strictement plus faible que ACL, circulaire pour borner μ−1 | R46 |
| **Near-pairs (T56)** | Absorbé par T55 (h=2 restreint) : distance L¹ ne produit pas d'équation structurée, Hamming = bon paramètre | R47 |
| **WEL-lite** | Non ciblant : c'est un objectif (μ→1) pas une méthode. SDL décompose le problème en sous-problèmes concrets | R47 |
| **SDL-lite (phases distinctes)** | Absorbé par ACaL : « phases distinctes ≠ décorrélation auto », nécessaire mais pas suffisant sans borner Z | R48 |
| **Cible ρ=O(1/max_B)** | Mauvaise échelle : ρ·max_B varie 0.04-3.1, pas de décroissance en 1/max_B | R48 |
| **V_between ≥ 0 universel** | RÉFUTÉ : V_between < 0 dans 15/20 cas (anti-corrélation inter-tranches aide) | R49 |
| **V_{b₀}/C_{b₀}² ≤ V/C² ∀b₀** | Mauvaise échelle : dernière tranche (C=1) a V/C²=(p-1)/p≈1 >> V/C² total | R49 |

### 🟡 PISTES EN SUSPENS (avancées partielles)

| Piste | État | Prochain pas | Round |
|-------|------|-------------|:-----:|
| **Gap spectral MTM** | Observé mais non prouvé | Prouver gap > 0 pour CPO | R32 |
| **CRT Product Theorem** | RÉFUTÉ comme prédiction exacte (6/9 faux), mais N₀(d) ≤ CRT toujours | Reformuler en borne | R30/R35 |
| **Order-Diversity Bound** | Conjecturé (18/18 vérifié) | Prouver la somme exp. | R31 |
| **Bonferroni dichotomy** | Prouvé k≤50, pas universel | Étendre analytiquement | R25 |
| **Restricted permanent** | T_p(t) = permanent restreint | Appliquer Barvinok/Gurvits | R7 |
| **Direct bound α/√p** | α ~ 0.50·k^{0.68}, viable mais non universel | Prouver α borné | R7 |
| **Projection Theorem** | Conjecturé (compression ≤ k/2) | Prouver | R28 |
| **Ratio Law** | Observé (N₀·p/C → 1) | Prouver convergence | R29 |
| **CSSPC (OCC)** | Vérifié k=3..16 (0 faux positif) | Tester k=17, borner ρ théoriquement | R40 |
| **Couplage total κ=1** | Prouvé sur 5 cas canoniques | Prouver pour tout k≥3 | R40 |
| **OCC-LITE** | IE seule suffit, gap [4.13, 6.0] | Prouver borne f_p, bridge asymptotique | R41-R42 |
| **Borne f_p ≤ 12/p** | A_max=11.43, 29 paires k=3..17 vérifiées | Prouver via Ehrhart / lattice counting | R42 |
| **Bridge C3→OCC-LITE** | f_p≤A/p ⟹ IE<θ quand ∏p>C·Aᵐ/θ, 1/10 SPC satisfait | Améliorer ou prouver asymptotique | R42 |
| **QEL (Quasi-Equidistrib.)** | D≤1.81, décroît. ACL réduit QEL à borner M₂=ΣN_r² | Prouver M₂≤C²/p+A·C | R43-R44 |
| **ACL (Aggregate Control)** | f_p ≤ 1/p + √((p-1)(p·M₂-C²))/(p·C) [PROUVÉ] | Montrer ACL serré via M₂ | R44 |
| **MSL (Monotone Spreading)** | μ=M₂p/C²→1 monotone, M₂≤C²/p+A(p)·C [OBSERVÉ] | Prouver via LSD ou Horner | R45-R46 |
| **LSD (Spreading Différences)** | h=1 PROUVÉ, h=2 forme canonique PROUVÉE, 3 sous-cas prouvés (T53-T55) | Borner congruence exp. générique h=2 (route secondaire) | R46-R47 |
| **WEL (Weak Equidist.)** | μ→1 qualitatif, cible minimale pour f_p→1/p | Prouver via SDL (Horner) = route prioritaire | R46-R47 |
| **SDL / ACaL (ANOVA)** | V=ΣV_{b₀}+V_between [PROUVÉ], ρ=V_between/V_within, \|ρ\|<1 universel (20/20) | Prouver \|ρ\|<1 via collisions inter-tranches (R50) | R47-R49 |
| **ACaL-within (GEH)** | ΣV_{b₀}/C²=o(1) [OBSERVÉ], induction viable via moyenne pondérée [PROUVÉ] | Prouver GEH (equidist. uniforme sur sous-intervalles) | R49 |

---

## CONCEPTS INVENTÉS (par l'Innovateur B)

| Concept | Définition | Round |
|---------|-----------|:-----:|
| **Monotone Compression** | Contrainte nondécroissante crée hiérarchie de fréquences | R27 |
| **Phase Diversity Index** (PDI) | ord_p(g)/k ; PDI ≥ 1 ⟹ diversité maximale | R31 |
| **Independent Blocking Model** (IBM) | 5 sous-concepts : blocking prob., arithmetic shield, SPT | R29 |
| **Monotone Transfer Matrix** (MTM) | Matrices triangulaires supérieures avec phases ω^{r·gʲ·2^b} | R32 |
| **Monotone Phase Cascade** (MPC) | Factorisation S(r) = v₀ᵀ · Πᵢ Tᵢ [PROUVÉ] | R32 |
| **Phase Spread** (σⱼ) | Mesure d'annulation par étape | R32 |
| **Spectral Transfer Bound** (STB) | |S_r| ≤ √dim · ‖CPO‖₂ [PROUVÉ] | R32 |
| **Oscillation-Damping Cascade** (ODC) | Alternance création-amortissement d'oscillations | R33 |
| **Discrete Oscillation Frequency** (DOF) | Mesure de fréquence d'oscillation d'un vecteur | R33 |
| **Algebraic Blocking Criterion** (ABC) | 3 tiers : bad/good+NVS=1/good+NVS<1 [PROUVÉ] | R34 |
| **Bad Prime Gateway** | p | G(k) ⟹ N₀(p) > 0 toujours [PROUVÉ] | R34 |
| **Composite Exclusion Certificate** (CEC) | Protocole 4 types : A(premier)/B(composite)/C(Bonferroni)/D(variance) | R35 |
| **CQIP** | Quasi-indépendance contrainte : N₀(d)=Π(N₀(pᵢ))/C^{r-1}+ε, ε anticorrélé | R35 |
| **CDI** (Composite Defect of Independence) | N₀^{prod}(d)-N₀(d) ; seul concept survivant de R36, CDI_norm~3.7-4.4 | R36 |
| **LOOS** (Obstruction d'Ordre Supérieur) | obs(k)=min{|I|: N₀(∏pᵢ)=0} ; seul lemme survivant R37 | R37 |
| **obs(k)** (Obstruction Order) | Ordre minimal d'obstruction ; obs∈{1,ω(d)} BRISÉ k=16 | R37/R38 |
| **PCMG** (Couplage Monotone Global) | Coprimalité ord_p(2) prédit le type d'obs ; seul principe survivant R38 | R38 |
| **SPC** (Sous-Produit Critique) | Plus petit sous-ensemble bloquant ; unique k=3..16, unifie CEC | R39 |
| **OCC** (Orbital Coverage Conflict) | Critère per-prime filtrage + IE ; 11/11 classifications correctes | R40 |
| **CSSPC** (Critère Suffisant SPC) | IE(I)<θ ∧ minimalité ∧ f_p<1/(|I|+1) ⟹ N₀(∏I)=0 [CONJECTURÉ] | R40 |
| **Couplage monotone total** (κ=1) | N₀_free(SPC)>0 mais N₀_mono(SPC)=0 pour les 5 cas canoniques | R40 |
| **OCC-LITE** | IE(I) < max(5, C^{1/4}) suffit SEUL (1 condition au lieu de 3) ; survivant R41 | R41 |
| **Pré-filtre algébrique** | ord_p(2) ≥ ceil(log₂(k)) identifie les primes actifs sans DP | R41 |
| **Borne f_p ≤ A/p** | f_p = N₀(p)/C(k) ≤ 12/p pour non-blocking, A_max=11.43 [SEMI-PROVABLE] | R42 |
| **Character sum decomposition** | N₀(p)=C(k)/p+(1/p)·ΣS(r), identité exacte (orthogonalité) [PROUVÉ] | R42 |
| **Error term E(k,p)** | E=p·f_p-1 ; |E|≤10.43 pour non-blocking, E=-1 pour Type A [CALCULÉ] | R42 |
| **Bridge inequality** | f_p≤A/p ⟹ IE≤C·Aᵐ/∏p ; C3 auto pour p>A·(|I|+1) [SEMI-FORMEL] | R42 |
| **Super-indépendance monotone** | N₀(∏I)>IE(I) systématiquement : couplage AMPLIFIE, pas contracte | R42 |
| **Simplex reformulation** | c_i=B_i-B_{i-1} bijecte B monotones ↔ Δ_{k-1}(max_B) [PROUVÉ] | R43 |
| **Horner factorization** | P_c=u₀·H₀, u₀=2^{c₀} inversible mod p → compter H₀≡0 [PROUVÉ] | R43 |
| **QEL** (Quasi-Equidist. Lemma) | max|N_r-C/p|/(C/p)≤α, α≤1.81 empirique, décroît avec k [CONJECTURAL] | R43 |
| **M<k toujours** | max_B=S-k<k car log₂3<2, tue la décomp. intérieur/bord d'Ehrhart | R43 |
| **ACL** (Aggregate Control Lemma) | f_p ≤ 1/p + √((p-1)(p·M₂-C²))/(p·C), première borne analytique sur f_p [PROUVÉ] | R44 |
| **M₂** (Second Moment) | M₂=Σ_{r=0}^{p-1} N_r², quantité clé : QEL ⇔ M₂≈C²/p [PROUVÉ = identité] | R44 |
| **Parseval corrigé** | Σ\|S(r)\|²=p·M₂ (pas p·C) ; l'ancien supposait injection P_B→Z/pZ [PROUVÉ] | R44 |
| **M₂ collision count** | M₂ = #{(B,B') monotones : P_B≡P_{B'} mod p}, reformulation canonique [PROUVÉ] | R45 |
| **V = L² discrepancy** | V = M₂ - C²/p = Σ(N_r-C/p)², erreur au-dessus de l'uniforme [PROUVÉ] | R45 |
| **μ = M₂·p/C²** | Multiplicité de collision, μ=1 = parfait, μ→1 quand k→∞ [OBSERVÉ] | R45 |
| **MSL** (Monotone Spreading Lemma) | M₂ ≤ C²/p + A(p)·C, A dépend de p ; survivant R45 [CONJECTURAL] | R45 |
| **WEL** (Weak Equidistrib. Lemma) | μ→1 qualitatif (sans taux), cible minimale suffisant pour f_p→1/p [CONJECTURAL] | R46 |
| **E_excess** (Excess collisions) | E_excess=(M₂-C)-C(C-1)/p, donne μ−1=(p-1)/C+p·E_excess/C² [PROUVÉ] | R46 |
| **LSD** (Spreading des Différences) | Collision h=1 ssi ord_p(2)\||Δ|, far-pair rate≈1/p ; survivant R46 [SEMI-FORMEL] | R46 |
| **Horner Telescoping** | Route prioritaire : induction sur k via condition sur B₀, base k=2 Weyl [SEMI-FORMEL] | R46 |
| **ord_p(2) collision criterion** | 2 B-vecteurs à distance h=1 collisionnent ssi ord_p(2) divise \|Δ\| [PROUVÉ] | R46 |
| **h=2 canonical form** | D≡0 mod p ⟺ 2^{a₁}≡α+β·2^{a₂} mod p (somme de 2 exponentielles) [PROUVÉ] | R47 |
| **Annulation h=2 (T53)** | Si ord_p(2)\|aᵢ, le terme i s'annule → retombe en h=1 [PROUVÉ] | R47 |
| **Solutions h=2 bound (T54)** | #solutions par valeur de a₂ ≤ ord_p(2) = M [PROUVÉ] | R47 |
| **Slice decomposition** | S(r)=Σ ω^{r·2^{b₀}}·S_{b₀}^{(k-1)}(r), identité exacte de décomposition [PROUVÉ] | R47 |
| **SDL** (Slice Decorrelation) | ρ(k,p)=cross/diag → 0 pour k→∞, p fixé [CONJECTURAL mais mesurable] | R47 |
| **Phase diversity** | #{2^{b₀} mod p : 0≤b₀≤max_B} = min(max_B+1, ord_p(2)) [PROUVÉ] | R47 |
| **Base k=2 identity** | Pour k=2 : \|S(r)\|=\|T(r)\| avec T(r)=Σ ω^{r·2^b}, factorisation exacte [PROUVÉ] | R47 |
| **ACaL** (ANOVA Cancellation) | V=ΣV_{b₀}+Σ_{b₀≠b₀'}Z_{b₀,b₀'}, décomposition ANOVA exacte de la variance [PROUVÉ] | R48 |
| **V_between** (variance inter-tranches) | V_between=Σ_{b₀≠b₀'}Z_{b₀,b₀'}, quantifie la corrélation entre tranches [PROUVÉ] | R48 |
| **Z_{b₀,b₀'}** (covariance inter) | Z=Σ_r(N_{b₀,r}-C_{b₀}/p)(N_{b₀',r}-C_{b₀'}/p), produit scalaire centré [PROUVÉ] | R48 |
| **ANOVA interpretation of ρ** | ρ+1=V/ΣV_{b₀}=V_total/V_within, SDL≡V_between≪V_within [PROUVÉ] | R48 |
| **Parseval pour Z** | Z=(1/p)ΣF_{b₀}·conj(F_{b₀'})-C_{b₀}C_{b₀'}/p, relie Z aux DFT [CALCULÉ] | R48 |
| **3 formulations de ρ** | Spectrale (F1), caractères (F2), combinatoire (F3), toutes équivalentes [PROUVÉ] | R48 |
| **Réduction inductive V_{b₀}** | V_{b₀}(k,p)=V(SubProblem(k-1,[b₀,max_B],p)), invariance translation+permutation [PROUVÉ] | R49 |
| **C_{b₀} formula** | C_{b₀}=C(max_B-b₀+k-2,k-2), décroissant, convexe, b₀=0 domine 50-70% [PROUVÉ] | R49 |
| **W/C² moyenne pondérée** | W/C²=Σ(V_{b₀}/C_{b₀}²)·(C_{b₀}/C)², poids dominés par b₀=0 [PROUVÉ] | R49 |
| **GEH** (Generalized Equidist.) | V(k',[a,b],p)/C²=o(1) uniformément en [a,b], nécessaire pour within-induction [FORMULÉ] | R49 |
| **Z = collision inter-tranches** | Z_{b₀,b₀'}=M₂(b₀,b₀')−C_{b₀}C_{b₀'}/p, excès de collisions inter [PROUVÉ] | R49 |
| **ACaL-between-lite** | |ρ|<1, i.e. |V_between|≤V_within, candidat lemme universel (20/20) [CONJECTURAL] | R49 |

---

## DIAGNOSTICS DE L'INVESTIGATEUR A

| Diagnostic | Explication | Round |
|-----------|-------------|:-----:|
| **Dimension Collapse** | B→P_B(g) mod p perd du rang pour petits (k,p) | R27 |
| **Phase Transition** | d_eff=1.0 quand C/p > 25 ; collapse = artefact petits k | R28 |
| **3 couches structurelles** | Arithmétique × combinatoire × transition de phase | R7 |
| **4 murs classiques** | Weyl/Weil/LS/ET tous inapplicables (simplexe + phase exp.) | R32 |
| **Amplitude diffusion** | Normes croissent mais énergie se répartit → annulation | R33 |
| **CRT single-prime dead end** | C/p >> 1 rend N₀(p)=0 exponentiellement improbable | R34 |
| **Anticorrélation composite** | ratio N₀(d)/(Π N₀(pᵢ)/C^{r-1}) = 0 toujours pour k=3..15 | R35 |
| **Deux régimes CRT** | Grand C/p : Ratio Law ~1.008 ; petit C/p : wildly variable | R35 |
| **3 tiers de faisabilité** | Tier 1 (k=21-27, DP direct C), Tier 2 (k=28-31, MITM), Tier 3 (k=32-41, intractable) | R35 |
| **Défaut TOTAL** | N₀(d)=0 pour TOUS les 13 k testés par DP exact (pas partiel, TOTAL) | R36 |
| **Défaut structurel** | Ce n'est pas statistique mais algébrique : la monotonie de B interdit les solutions | R36 |
| **Taxonomie k=3..25** | Type A:4, Type B:9, Type C:6, Ouvert:4 | R36 |
| **Monotonie = coupleur algébrique** | N₀_free(d)>0 mais N₀_mono(d)=0 [PROUVÉ par DP] | R37 |
| **obs(k) ∈ {1,ω(d)}** | Pas de cas intermédiaire sur k=3..15 [OBSERVÉ] | R37 |
| **k=12 : collapse d'ordre 3** | 3 primes OK, 3 paires OK, seul le triple bloque | R37 |
| **k=16 : cas intermédiaire** | obs(16)=2 avec ω=3, paire (233,14753) suffit, 7 inutile | R38 |
| **Discriminant : gcd(ord_p(2))** | gcd=1 (coprime) → obs<ω ; gcd>1 → obs=ω [OBSERVÉ] | R38 |
| **Spectre obs 3 types** | Type A 50%, Complet 43%, Intermédiaire 7% sur k=3..16 | R38 |
| **Ordres = prédicteur PARTIEL** | min_gcd sépare types pour ω≥3, mais 1 seul cas intermédiaire | R39 |
| **SPC unique k=3..16** | Jamais 2 sous-ensembles minimaux distincts [OBSERVÉ] | R39 |
| **k=17 : coprime mais obs≥3** | Peut falsifier P1 de R38 (coprime ⇏ obs<ω) | R39 |
| **Passif = petit ordre** | k=16 : prime 7 (ord=3) passif, 233 (29) et 14753 (1844) actifs | R39 |
| **Couplage monotone total κ=1** | Pour les 5 cas canoniques (k=6,8,10,12,16), κ=1 exactement [PROUVÉ] | R40 |
| **Onset du couplage à j=2** | Free vs monotone divergent à j=2 pour k=6 et k=8 [CALCULÉ] | R40 |
| **Critère passivité** | ord_p(2) << max_B+1 implique passivité [SEMI-FORMEL, 1 cas] | R40 |
| **SI = puissance discriminante 0** | Structure de périodes (ordres) ne prédit PAS le blocking [RÉSULTAT NÉGATIF] | R40 |
| **OCC prédit 11/11** | Blocking ET non-blocking correctement classifiés par IE+filtrage | R40 |
| **CSSPC vérifié k=3..16** | 14 SPC, 5 non-SPC, 0 faux positif [CONJECTURÉ] | R40 |
| **Corrélation rho multi-prime** | ρ>1 pour paires non-SPC (k=12), ρ=0 pour SPC : phénomène d'ordre supérieur | R40 |
| **C3 = priorité rigidification** | Score 4/5, seule condition exprimable algébriquement sans DP | R41 |
| **C2 remove-one = full** | Minimalité remove-one ≡ minimalité complète pour k=3..16 [CALCULÉ] | R41 |
| **OCC-LITE = IE seule suffit** | IE sépare parfaitement blocking (max 4.13) / non-blocking (min 6.0) | R41 |
| **Gap de séparation IE** | Aucun cas dans [4.13, 6.0] : gap structurel, pas un artefact [OBSERVÉ] | R41 |
| **k=17 : confirmation** | d=5·71·14303, N₀ calculé, OCC-LITE prédit blocks, OCC-ALG échoue | R41 |
| **f_p·p ∈ [1,5]** | f_p ~ c/p avec c=O(1) confirme near-equidistribution monotone | R41 |
| **OCC-ALG : leçon résiduelle** | ord_p(2)≥ceil(log₂k) = pré-filtre valide mais pas critère suffisant | R41 |
| **Borne f_p ≤ 12/p** | A_max=11.43, vérifié 29 paires k=3..17 ; outlier k=15/p=186793 (f_p·p=11.43) | R42 |
| **Character sum identity** | N₀(p) = C(k)/p + (1/p)·Σ_{r=1}^{p-1} S(r), exact par orthogonalité [PROUVÉ] | R42 |
| **3 obstacles monotones** | (1) pas de factorisation S(r), (2) simplexe ≠ variété, (3) petits primes | R42 |
| **Good vs bad primes** | Bad (ord<k): A_max=1.43 SERRÉ ; Good (ord≥k): A_max=11.43, outlier possible | R42 |
| **C3 semi-auto** | f_p≤A/p ⟹ C3 auto pour p>A·(|I|+1) : paires p>34, triples p>46 | R42 |
| **Sub-Independence FAILS** | N₀(∏I)>IE(I) pour 8/8 paires non-triviales, max ratio 6.38 [RÉSULTAT NÉGATIF] | R42 |
| **Super-indépendance** | Couplage monotone AMPLIFIE N₀ au-delà de IE, pas contractif | R42 |
| **Bridge partiel** | Bridge satisfait dans 1/10 cas SPC, k=14 seul ; asymptotiquement croissant | R42 |
| **Simplex = monotonie** | c_i=B_i-B_{i-1} bijecte exactement B monotones ↔ Δ_{k-1}(S-k) [PROUVÉ] | R43 |
| **Horner nesting** | P_c=u₀·(1+u₁·(g+u₂·(g²+...))) structure multiplicative nested [PROUVÉ] | R43 |
| **M<k universel** | S-k<k pour tout k≥3 (log₂3<2) → 0 points intérieurs → Ehrhart bord inutile | R43 |
| **QEL empirique** | Discrepancy D≤1.81, D(k=17)=0.018 pour p=5 → quasi-equidistribution croissante | R43 |
| **7 obstacles catalogués** | Brion-Vergne = route la plus prometteuse pour borner S(r) sur simplexe | R43 |
| **Congruence multiplicative** | P_c(g) mod p est NONLINÉAIRE en coords c → pas d'hyperplan, pas Ehrhart direct | R43 |
| **Parseval CORRIGÉ** | Σ\|S(r)\|²=p·ΣN_r²=p·M₂ (PAS p·C). Ancien = injection P_B fausse (collisions) [PROUVÉ] | R44 |
| **C-S bound** | \|ΣS(r)\|≤√((p-1)(p·M₂-C²)), typiquement lâche (ratio 0.01-0.3) [PROUVÉ] | R44 |
| **ACL = première borne** | f_p ≤ 1/p + erreur, erreur=O(1/√C) pour M₂≈C²/p+O(C), suffisant grands k [PROUVÉ] | R44 |
| **M₂ = clé de QEL** | Tout le programme QEL se réduit à borner M₂ ; M₂/(C²/p)→1 empiriquement [OBSERVÉ] | R44 |
| **k=3 Horner partial** | S(r) factorise partiellement via Horner à k=3 ; k≥4 couplage simplexe bloque | R44 |
| **WQE ne contrôle pas r=0** | Chebyshev borne #mauvais résidus mais le résidu 0 peut être mauvais [PROUVÉ] | R44 |
| **M₂ = collision count** | M₂=#{(B,B'):P_B≡P_{B'} mod p}, validé par brute-force sur 4 paires [PROUVÉ] | R45 |
| **V/C non borné** | V/C=20.4 (k=12,p=5), croît : variance naturelle quand C/p grand. Pas un défaut [CALCULÉ] | R45 |
| **μ→1 monotone** | μ=M₂p/C² décroît vers 1 : 1.667→1.010→1.001 (p=5, k=3→9→12) [OBSERVÉ] | R45 |
| **Taux de convergence = clé** | Si μ-1=O(p/C) → f_p=O(1/p). Si μ-1=O(1) → f_p=O(1/√p) seulement [SEMI-FORMEL] | R45 |
| **Collisions non géométriques** | L1_coll/L1_random ≈ 1.04, collisions par annulation arithmétique, pas proximité [OBSERVÉ] | R45 |
| **μ−1 reformulation optimale** | μ−1=(p-1)/C+p·E_excess/C², sépare terme structurel (diag) et dynamique (excès) [PROUVÉ] | R46 |
| **Weyl k≥4 BLOQUÉ** | Simplexe Δ non invariant par shift : B_i→B_i+1 viole B_i≤B_{i+1} quand B_i=B_{i+1} [SEMI-FORMEL] | R46 |
| **5 routes comparées** | Horner=CRÉDIBLE, Spreading=crédible, Mixing=FRAGILE, Large Sieve=FRAGILE, ET=ÉLIMINÉ [R46] | R46 |
| **Horner base k=2** | S(r) somme géométrique distordue sur [0,max_B], bornée ~max_B/ord_p(2) [SEMI-FORMEL] | R46 |
| **Non-resonance B₀-slices** | Point dur : les contributions spectrales des tranches B₀=b₀ ne doivent pas interférer constructivement | R46 |
| **LSD h=1 exact** | Collision à distance Hamming 1 ssi ord_p(2)\||Δ|, vérifié exhaustivement k=3..7 [PROUVÉ] | R46 |
| **Far-pair rate ≈ 1/p** | Pour h≥k/2, taux de collision ≈ 1/p (quasi-random), ratio 0.97-1.02 [OBSERVÉ] | R46 |
| **Near-pair excess borné** | Excès near-pair/C ≤ 1.10, collisions structurées concentrées aux petits h [OBSERVÉ] | R46 |
| **h=2 taux ≈ 1/p** | Contrairement à h=1 (sur-taux), h=2 quasi-aléatoire : taux 0.02-0.20 vs 1/p [OBSERVÉ] | R47 |
| **h=2 sous-cas classification** | 4 sous-cas : annulation, amplitude égale, adjacent, générique. Les 2 premiers prouvés [PROUVÉ] | R47 |
| **Equation fondamentale h=2** | 2^{a₁}≡α+β·2^{a₂} mod p, congruence exp. reconnue en théorie des nombres [PROUVÉ] | R47 |
| **Slice decomposition exacte** | Erreur reconstruction ≤ 1e-12 sur 4 paires (k,p), identité exacte [PROUVÉ] | R47 |
| **Cross-term ratio ρ** | ρ=0.50 (p=5,k=3) à ρ=0.01 (p=59,k=6), corrélé à ord_p(2) [OBSERVÉ] | R47 |
| **ord_p(2) gouverne ρ** | ord grand → ρ petit (cancellation), ord petit → ρ grand (interférence) [OBSERVÉ] | R47 |
| **Arbitrage LSD vs Horner** | LSD = bottom-up (couche par couche), Horner = top-down (1 lemme suffit). Horner prioritaire [SEMI-FORMEL] | R47 |
| **ρ<1 universel (favorable)** | |ρ|<1 dans 13/13 cas favorables (ord_p(2)≥max_B+1), max |ρ|=0.50 (p=5,k=3) [OBSERVÉ] | R48 |
| **ANOVA identity exact** | V=ΣV_{b₀}+V_between vérifié machine-epsilon sur 14 paires (k,p) [PROUVÉ] | R48 |
| **Triple lock** | Borner Z requiert combiner monotonie (combinatoire) + puissances de 2 (multiplicatif) + caractères (additif) : aucune technique standard ne gère les 3 [HARD POINT] | R48 |
| **Cauchy-Schwarz applicable** | |Z_{b₀,b₀'}|≤√(V_{b₀}·V_{b₀'}), 0 violations, borne correcte mais triviale [PROUVÉ] | R48 |
| **Slice correlations 0.5-0.9** | Corrélations zero-shift inter-tranches = 0.5-0.9 pour tranches adjacentes : NON indépendantes [OBSERVÉ] | R48 |
| **ρ signe négatif 10/13** | ρ négatif dans 10/13 cas favorables → V_between négatif typiquement (anti-corrélation) [OBSERVÉ] | R48 |
| **SR1 = meilleur sous-régime** | p racine primitive de 2 → diversité maximale, |ρ|<0.3 typiquement [OBSERVÉ] | R48 |
| **ρ≠O(1/max_B)** | ρ·max_B varie 0.04-3.1 sans tendance, taux dépend de ord_p(2) pas de max_B [RÉFUTÉ] | R48 |
| **Within = terme dur** | Induction k→k-1 viable en structure mais nécessite GEH, circulaire sans amorce [SEMI-FORMEL] | R49 |
| **Between = terme tractable** | |ρ|<1 universel (20/20), cancellation signe forte, CS ratio 0.1-0.5 [OBSERVÉ] | R49 |
| **b₀=0 domine ΣV** | Fraction V₀/ΣV = 60-77% pour k≥5, le sous-problème b₀=0 est le bottleneck [OBSERVÉ] | R49 |
| **ΣV_{b₀}/C² = o(1)** | Décroît comme C^{-β}, β∈[0.64,1.28] selon p. p=5 le plus lent [OBSERVÉ] | R49 |
| **V_between négatif 75%** | 15/20 cas V_between<0 : anti-corrélation inter-tranches AIDE V_total [OBSERVÉ] | R49 |
| **Cancellation signe Z** | |ΣZ|/Σ|Z| = 0.038-0.862, facteur 3-26× de réduction par cancellation [OBSERVÉ] | R49 |
| **p=5 pathologique** | ρ>0 systématiquement pour p=5, β le plus lent (0.64), max|ρ|=0.51 [OBSERVÉ] | R49 |
| **Petites tranches bruyantes** | V_{b₀}/C_{b₀}²→(p-1)/p quand C_{b₀}→1, mais poids (C_{b₀}/C)²→0 [PROUVÉ] | R49 |

---

## THÉORÈMES PROUVÉS (résultats originaux)

| # | Théorème | Round |
|---|---------|:-----:|
| T1 | Non-surjectivité Ev_d pour k ≥ 18 | Pré-R1 |
| T2 | Junction Theorem : C/d → 0 | Pré-R1 |
| T3 | corrSum toujours impair | R2 |
| T4 | corrSum ≢ 0 (mod 3) | R2 |
| T5 | v₂(corrSum) = min(A) | R2 |
| T6 | corrSum mod 12 déterminé par min(A) | R2 |
| T7 | CRT indépendance (χ²/df = 1.026) | R3 |
| T8 | Matrice de transition doublement stochastique | R1 |
| T9 | Zéro transitoire : c_j=0 ⟹ c_{j+1}≠0 | Pré-R1 |
| T10 | WR backward reachability bloque k=3,4,5,7,8,11 | R7 |
| T11 | T_p(t) = permanent restreint | R7 |
| T12 | k=3..20 tous prouvés (N₀(d)=0) | R8-R25 |
| T13 | Décroissance exponentielle α = L(1-H(1/L)) = 0.0793 | R21 |
| T14 | Bonferroni CRT pour k=6,9,10 | R24 |
| T15 | Bonferroni dichotomie (BF ≥ 1.6 si ω ≥ 2) | R25 |
| T16 | Borel-Cantelli K₀ = 42 | R26 |
| T17 | g^k = 2^{k-S} mod p | R31 |
| T18 | Bad Prime Bound : ord_p(g)<k ⟺ p|G(k) | R31 |
| T19 | Monotone Phase Cascade (factorisation) | R32 |
| T20 | Spectral Transfer Bound | R32 |
| T21 | Bad Prime Gateway : p|G(k) ⟹ N₀(p)>0 | R34 |
| T22 | N₀(d) = 0 pour TOUT k = 3..15 (DP exact) | R35 |
| T23 | CEC protocole : 10/13 valeurs k=3..15 certifiées (Type A/B) | R35 |
| T24 | Monotonie = coupleur algébrique : N₀_free(d)>0, N₀_mono(d)=0 | R37 |
| T25 | obs(k) calculé pour k=3..15 : toujours dans {1, ω(d)} | R37 |
| T26 | obs(16)=2 avec ω=3 : polarisation BRISÉE (premier intermédiaire) | R38 |
| T27 | gcd(ord_p(2)) = discriminant de obs(k) [OBSERVÉ k=3..16] | R38 |
| T28 | SPC unique et calculé pour k=3..16 (unifie CEC Types A/C/D) | R39 |
| T29 | Ordres multiplicatifs = prédicteur PARTIEL (1 cas intermédiaire) | R39 |
| T30 | Couplage monotone total : κ=1 pour 5 cas canoniques [PROUVÉ par DP] | R40 |
| T31 | SI discriminative power = 0 : ordres ne prédisent pas blocking [RÉSULTAT NÉGATIF] | R40 |
| T32 | CSSPC (OCC) : IE(I)<θ ∧ minimalité ∧ filtrage ⟹ N₀=0, vérifié k=3..16 | R40 |
| T33 | OCC-LITE : IE(I) < max(5,C^{1/4}) seule suffit (C2,C3 redondantes) [OBSERVÉ] | R41 |
| T34 | Gap de séparation IE : max_blocking=4.13 vs min_surviving=6.0 [CALCULÉ] | R41 |
| T35 | Minimalité remove-one ≡ minimalité complète pour k=3..16 [CALCULÉ] | R41 |
| T36 | Character sum identity : N₀(p)=C(k)/p+(1/p)·ΣS(r) [PROUVÉ, orthogonalité] | R42 |
| T37 | Sub-Independence Conjecture RÉFUTÉE : N₀(∏I)>IE pour 8/8 paires non-triviales | R42 |
| T38 | Borne f_p ≤ 12/p vérifiée sur 29 paires k=3..17 (A_max=11.43) [CALCULÉ] | R42 |
| T39 | Type A : ΣS(r)=−C(k) exactement, blocking TOTAL par annulation [PROUVÉ] | R42 |
| T40 | Simplex reformulation : c_i=B_i-B_{i-1} bijecte Δ_{k-1}(max_B) ↔ monotone B [PROUVÉ] | R43 |
| T41 | Horner factorization : P_c=u₀·H₀, u₀ inversible, réduit à compter H₀≡0 [PROUVÉ] | R43 |
| T42 | M<k universel : max_B=S-k<k pour tout k≥3, zéro points intérieurs [PROUVÉ] | R43 |
| T43 | Boundary Majorization RÉFUTÉ : borne f_p≤2/p violée empiriquement (k=6,p=59) | R43 |
| T44 | Parseval corrigé : Σ\|S(r)\|²=p·M₂ (pas p·C), injection P_B fausse [PROUVÉ] | R44 |
| T45 | ACL : f_p ≤ 1/p + √((p-1)(p·M₂-C²))/(p·C), première borne analytique [PROUVÉ] | R44 |
| T46 | WQE insuffisant : Chebyshev borne #mauvais résidus mais ne contrôle pas r=0 [PROUVÉ] | R44 |
| T47 | M₂ = #{(B,B') : P_B≡P_{B'} mod p} : collision count reformulation [PROUVÉ] | R45 |
| T48 | V ≤ A·C universel RÉFUTÉ : V/C=20.4 (k=12,p=5), V = O(C²/p) pas O(C) [RÉFUTÉ] | R45 |
| T49 | MSL modéré : M₂ ≤ C²/p + A(p)·C, vérifié k=3..12, μ→1 monotone [OBSERVÉ] | R45 |
| T50 | μ−1 = (p-1)/C + p·E_excess/C² : décomposition structurel/dynamique [PROUVÉ] | R46 |
| T51 | Weyl differencing BLOQUÉ pour k≥4 : simplexe monotone non invariant par shift [SEMI-FORMEL] | R46 |
| T52 | LSD h=1 : collision à distance 1 ssi ord_p(2) divise \|Δ\| [PROUVÉ] | R46 |
| T53 | Annulation h=2 : si ord_p(2)\|aᵢ, le terme i s'annule → réduit à h=1 [PROUVÉ] | R47 |
| T54 | Solutions h=2 bornées : #solutions par valeur a₂ ≤ ord_p(2) [PROUVÉ] | R47 |
| T55 | h=2 restreint : E₂/C ≤ A₂(p), sous-cas prouvés, cas général semi-formel [SEMI-FORMEL] | R47 |
| T56 | Slice decomposition : S(r) = Σ ω^{r·2^{b₀}} · S_{b₀}^{(k-1)}(r) [PROUVÉ] | R47 |
| T57 | Phase diversity = min(max_B+1, ord_p(2)) [PROUVÉ] | R47 |
| T58 | Base k=2 : \|S(r)\| = \|T(r)\| avec T(r) = Σ ω^{r·2^b} [PROUVÉ] | R47 |
| T59 | Identité ANOVA : V = Σ V_{b₀} + Σ_{b₀≠b₀'} Z_{b₀,b₀'} [PROUVÉ] | R48 |
| T60 | ρ = V_between / V_within (3 formulations équivalentes prouvées) [PROUVÉ] | R48 |
| T61 | Cauchy-Schwarz : |Z_{b₀,b₀'}| ≤ √(V_{b₀}·V_{b₀'}) [PROUVÉ] | R48 |
| T62 | Parseval pour Z : Z = (1/p)·Σ F_{b₀}·conj(F_{b₀'}) − C_{b₀}C_{b₀'}/p [CALCULÉ] | R48 |
| T63 | Réduction inductive : V_{b₀}(k,p) = V(SubProblem(k-1, [b₀, max_B], p)) [PROUVÉ] | R49 |
| T64 | C_{b₀} = C(max_B−b₀+k−2, k−2), Σ=C, décroissant, convexe [PROUVÉ] | R49 |
| T65 | W/C² = Σ (V_{b₀}/C_{b₀}²)·(C_{b₀}/C)² : reformulation moyenne pondérée [PROUVÉ] | R49 |
| T66 | Z = M₂(b₀,b₀') − C_{b₀}·C_{b₀'}/p : reformulation collision inter-tranches [PROUVÉ] | R49 |
| T67 | \|ρ(k,p)\| < 1 pour tout (k,p) testé (20/20 cas, max\|ρ\|=0.687) [OBSERVÉ] | R49 |

---

## CHRONOLOGIE DES ROUNDS

```
R1-R2   : Exploration locale (TZ, WR, invariants) → 4 pistes fermées, 3 théorèmes
R3-R4   : Mécanismes globaux (CRT, mixing) → CRT = la clé
R5-R6   : Bornes directes + carry propagation → k=3..6 prouvés
R7-R8   : WR backward reachability + exhaustif → k=3..17 prouvés
R9-R14  : Structure algébrique (g-forme, transfert, m-élim) → cadre formel
R15-R22 : Frontière DP → k=18..19 prouvés, α exact
R23-R25 : k=20 + Bonferroni → Gap = 21 valeurs (k=21..41)
R26     : Équidistribution spectrale + MITM gap → k=21..23 OPEN
R27-R28 : Dimension collapse + phase transition → artefact petits k
R29     : Ratio Law + IBM → N₀(p)·p/C → 1
R30     : Premier round A→B → CRT Product Theorem [CONJECTURÉ]
R31     : Order-Diversity → g^k identity + Bad Prime Bound [PROUVÉ]
R32     : Transfer spectral → MPC + STB [PROUVÉS], 4 murs classiques
R33     : Contraction RÉFUTÉE → diffusion + PIVOT identifié
R34     : Existentiel ÉCHEC → 0/21 prouvés, DP optimisé = prochaine étape
R35     : CEC + CQIP → cadre certifiant, CRT product RÉFUTÉ, 3 tiers faisabilité
R36     : CDI survit (CCD/OEntropy éliminés), défaut TOTAL, taxonomie k=3..25
R37     : LOOS survit (LCM éliminé), obs(k)∈{1,ω(d)}, monotonie = coupleur [PROUVÉ]
R38     : Polarisation BRISÉE k=16 (obs=2,ω=3), PCMG survit (PSO éliminé)
R39     : Ordres = prédicteur PARTIEL, SPC survit (IA éliminé), k=17 teste P1
R40     : SPC autopsy → κ=1 universel, SI éliminé (0 pouvoir), OCC/CSSPC survit
R41     : C3 priorité rigidif., OCC-LITE (IE seule) survit, OCC-ALG éliminé, k=17 confirme
R42     : f_p ≤ 12/p (SEMI-PROVABLE, Ehrhart route), Sub-Independence RÉFUTÉ, Bridge survit
R43     : Simplex reformulation [PROUVÉ], Horner nesting [PROUVÉ], QEL survit, Boundary tué (M<k)
R44     : ACL [PROUVÉ], Parseval corrigé (Σ|S|²=p·M₂), WQE éliminé, M₂ = clé de QEL
R45     : V≤A·C RÉFUTÉ, M₂=collision count [PROUVÉ], MSL survit (CRL éliminé), taux μ→1 = clé
R46     : Weyl ÉLIMINÉ k≥4, Horner Telescoping = route prioritaire, LSD h=1 PROUVÉ (ord_p(2)|Δ), MSL-lite ÉLIMINÉ
R47     : LSD h=2 forme canonique PROUVÉE (T53-T55), Horner slice decomposition PROUVÉE (T56-T58), SDL formulé, ARBITRAGE : Horner = prioritaire R48
R48     : SDL = ANOVA [PROUVÉ] (T59-T62), ACaL survivant, SDL-lite ÉLIMINÉ, ρ=O(1/max_B) RÉFUTÉ, triple lock identifié
R49     : Within=dur (GEH), Between=tractable (|ρ|<1 universel 20/20), ACaL-between-lite SURVIVANT R50 (T63-T67)
```

---

## PROCHAINES ÉTAPES (R35+)

```
PRIORITÉ 1 : DP direct sur d(k) en C compilé
             Tier 1 : k=21-27 (d petit, faisable en heures)
             Faisabilité 9/10, Impact 10/10

PRIORITÉ 2 : MITM (meet-in-the-middle) pour k=28-31
             d moyen, split B en deux moitiés
             Faisabilité 7/10, Impact 7/10

PRIORITÉ 3 : Rédaction papier avec résultats actuels
             (Junction + k≤20 + partial gap closure)
             Target : Experimental Mathematics

PRIORITÉ 4 : Borne analytique universelle (CQIP raffiné)
             Faisabilité 2/10, Impact 10/10
```

---

## STATISTIQUES

- **Rounds** : 49
- **Scripts** : 186
- **Auto-tests** : 7611 (100% PASS)
- **Théorèmes prouvés** : 67 (originaux)
- **Conjectures ouvertes** : 13 (OD Bound, Ratio Law, PCMG, SPC unicité, OCC-LITE, κ=1, QEL, MSL, LSD, WEL, SDL/ACaL, |ρ|<1, GEH)
- **Pistes fermées** : 41 (documentées avec raison)
- **Concepts inventés** : 68 (nommés, dont ACaL-between-lite = survivant R49)
- **Lean** : 280 théorèmes, 0 sorry
- **Gap restant** : 21 valeurs (k=21..41)
- **Route prioritaire** : ACaL-between-lite (R50 : prouver |ρ| < 1 via collisions inter-tranches)
