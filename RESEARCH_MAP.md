# CARTE DES RECHERCHES — Collatz Junction Theorem
**Date:** 13 mars 2026 | **Rounds:** R1–R64 (64 rounds, 216 scripts, 12066 auto-tests)

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
| **ρ-lite direct** | Absorbé par Z-lite : |ρ| est un symptôme de la structure des Z, pas un levier de preuve | R50 |
| **Borne paire-par-paire Z** | Trop faible : cancellation signe (ratio 0.48) perdue paire-par-paire, agrégé meilleur | R50 |
| **Seuil |ρ|<0.5 pour α=2** | Contredit : max|ρ|=0.655 dans R2, seuil α=4 nécessaire pour max<0.4 | R50 |
| **Cascade A(k)≤A(k-1)** | Contredite : p=5 A croît 0.8→17.0 monotonement, petits primes = obstruction structurelle | R51 |
| **TQL-strong (D∞ uniforme)** | Mauvaise échelle : D∞ explose pour tranches dégénérées (C_{b₀}=1), L² meilleur que L∞ | R51 |
| **μ−1 ~ p·logC/C** | Contredite : R²=0.565 vs 0.909 pour p/C. Correction log inutile, p/C suffit | R52 |
| **μ−1 ~ (max_B+1)/C** | Mauvaise échelle : R²=0.425, pire fit. p contrôle, pas max_B | R52 |
| **Famille dominante isolable** | Contredite : Gini→0 avec C (0.575→0.152), collisions diffuses, pas de hub vectors | R53 |
| **h≤2 dominance asymptotique** | Mauvaise échelle : corr(logC, frac_near)=-0.675, contributions se dispersent pour grand k | R53 |
| **r=0 dominant V** | Contredite : r=0 dominant dans 33% des cas seulement, V distribué sur 45-71% résidus | R53 |
| **Contraction pointwise μ(sub)<μ(full)** | Contredite : max_b μ(k-1,b,p) > μ(full) dans 6/6 cas (petites tranches C_b<<p) | R54 |
| **Poly vanishing route principale** | Trop faible : h≥3 = 98.3% à k=7, contraintes indépendantes échouent facteur 7000×, Weyl toujours bloquant | R54 |
| **N_h ~ C·(1/p)^{h-1}** | Contredite : heuristique d'indépendance prédit N_3≈0.05 vs réel=365 (k=7,p=127) | R54 |
| **Récurrence universelle V(k)≤α·Σ·V+β·C** | Trop faible : dichotomie ANOVA (V_cross change de signe), aucune forme unique ne couvre tous les k | R55 |
| **Contraction multiplicative ρ<1 universelle** | Contredite : ρ>1 pour k=3..6 (V_cross<0 rend V<V_within), contraction seulement k≥7 | R55 |
| **V_cross ≤ 0 universel** | Contredite : V_cross>0 pour k=7,8. Tendance s'inverse pour grand k, pas d'hypothèse de signe | R55 |
| **A(2) ≤ 1.22 universel** | Corrigée par R56 : A(2)≤2.28 sur 2931 cas R1. Cas dégénéré g≡-1 mod p (A=2.28) manquait dans R55 (622 cas) | R56 |
| **Cauchy-Schwarz pour |γ|<1** | PROUVÉ INSUFFISANT : Jensen ⟹ θ_CS = CS/V_within ≥ n-1 ≥ 1, CS ne peut structurellement prouver |γ|<1 | R56 |
| **Cross-first strategy** | Éliminée : V_cross contrôle = OBSERVÉ SEULEMENT, aucun outil de preuve disponible. Base k=2 plus prouvable | R56 |
| **Orbites complètes comme levier base** | Trop faible : en R1 TOUTES orbites sont incomplètes (prouvé R56), lemme V=0 orbites complètes est vacueux | R57 |
| **max N_r ≈ C/p (équidist. naïve)** | Mauvaise échelle : ratio multiplicatif max N_r/(C/p) atteint 25.7, bonne borne = additive pas multiplicative | R57 |
| **Base-first séquentiel strict** | Non ciblante : base déjà semi-formalisée (6 faits prouvés), cross utilise outils DIFFÉRENTS, parallèle > séquentiel | R57 |
| **Second moment comme noyau base-lite** | Trop faible : passage L²→L∞ perd √p (facteur 448×), contrôle pas pointwise, Candidat 1 additive strictement plus fort | R58 |
| **Pseudo-aléa dlogs c_δ** | Contredite : c_δ couvre 12-31% de (Z/pZ)* seulement, suite très structurée, pas uniforme dans le multiplicatif | R58 |
| **Borne Weil directe sur dlogs affines** | Non ciblante : sommes sur dlogs de suites affines hors cadre standard Weil, pas de théorème applicable | R58 |
| **Critère Weyl seul pour max N_r** | Trop faible : vérifie S(h)→0 mais sans vitesse quantitative, ne donne pas de borne exploitable | R58 |
| **Large sieve route directe pour K_linear** | Trop faible : borne (M+1)·(1+M/ord) ≥ M+1 TOUJOURS, pire que trivial dans 4/4 cas testés | R59 |
| **F3 borne logarithmique** | Trop agressive : K₃ non borné stablement, fluctuations trop grandes quand M petit | R59 |
| **Tranches dyadiques seule** | Trop faible : somme des bornes par tranche ≈ 2(M+1), pas mieux que trivial, argument global nécessaire | R59 |
| **Candidat 2 hybride L²** | Strictement plus faible : √V ≈ c·M reconstruit borne linéaire avec pire constante, 0% supérieur dans cas significatifs | R59 |
| **Candidat 2 bridge+nesting comme noyau** | Trop dur : prouver α=O(1/√M) strictement plus difficile que α<1, démontrabilité inférieure (39/60 vs 49/60) | R60 |
| **Discrepancy D∞ standard comme bridge** | Non ciblante : ne capture pas la pondération par fenêtres, métrique inadéquate pour borner α | R60 |
| **Nesting comme route autonome** | Trop faible : contrôle rugosité (J_r borné) mais ne borne PAS α directement, auxiliaire seulement | R60 |
| **Route 2 espacement multiplicatif** | Non ciblante : dlog des ratios c_{δ+1}/c_δ quasi-uniformes, pas de structure exploitable pour hit-hit | R61 |
| **Candidat 2 chaînes courtes comme route principale** | Absorbée : score 68/100 vs 71/100 pour Candidat 1 pointwise, complexité supplémentaire sans avantage net | R61 |
| **τ < 1 universel tous régimes sans restriction** | Trop ambitieuse : cas dégénérés (n=2) potentiellement τ=1, commencer par R3 puis étendre | R61 |
| **Nesting seul comme preuve de (c)** | Trop faible : J_r borné aide mais ne contrôle pas τ directement (confirmé R60+R61) | R61 |
| **Route 1 fenêtres pure pour ε>0** | Trop faible : ε_géom = 1/(M+1) → 0 pour p grand, ne donne pas ε>0 uniforme | R62 |
| **Candidat 2 bornes de Weil directes** | Non ciblante : c_δ=1+g^{2δ} n'est pas un polynôme, Weil ne s'applique pas directement sur sous-groupe | R62 |
| **ε indépendant de quasi-uniformité** | Contredite : sans uniformité de d_δ, concentration possible dans la fenêtre, gap annulé | R62 |
| **Réduction combinatoire par incidences** | Absorbée : énergie additive contrôle L² pas L∞, passage E→D∞ pointwise = cul-de-sac (Parseval ramène aux sommes exp.) | R63 |
| **Pseudo-aléatoireté naïve de d_δ** | Non ciblante : structure affine c_{δ+1}=g²c_δ+(1−g²) exploitable, pas à contourner | R63 |
| **Weil directe sur F_p entier** | Non adaptée : somme sur sous-groupe ⟨g²⟩ pas sur tout F_p, besoin Burgess/Bourgain | R63 |
| **Bourgain-Konyagin pour ⟨g²⟩** | Absorbée : indice 2 → complétion élémentaire via η, Jacobi suffit, outil sophistiqué inutile | R64 |
| **Weil directe non décomposée** | Non ciblante : décomposition S_h=(A_h+B_h)/2 puis Jacobi = plus propre et plus fort | R64 |
| **Candidat 2 S_h avec résidu** | Absorbée : cas spéciaux h=0, h=(p-1)/2 hors plage utile H≈√p | R64 |

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
| **SDL / ACaL (ANOVA)** | V=ΣV_{b₀}+V_between [PROUVÉ], phase shift PROUVÉ, between-within UNIFIÉS | Prouver TQL (tail quasi-uniformity) = ferme les deux moitiés | R47-R50 |
| **ACaL-within (GEH)** | ΣV_{b₀}/C²=o(1) [OBSERVÉ], induction viable via moyenne pondérée [PROUVÉ] | Absorbé par TQL (même mécanisme que between) | R49-R50 |
| **TQL (Tail Quasi-uniformity)** | TQL-mu : schéma de preuve 4 sous-étapes (a,b PROUVÉES, c,d CONJECTURALES), bridge = discrepancy pondérée, preuve conditionnelle validée (<0.01% violation), verrou = transition hit-hit < 1, Candidat 1 bridge-lite SURVIVANT (49/60) | Prouver sous-étape (c) : taux transition hit-hit < 1 uniformément via structure affine x→2x−1 mod p | R50-R60 |

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
| **Phase shift Δ_{b₀,b₀'}** | Δ=g⁻¹·(2^{b₀'}−2^{b₀}) mod p, constante par paire, anti-sym+transitif [PROUVÉ] | R50 |
| **Z = conv décalée** | M₂(b₀,b₀')=Σ_r N^{tail}_{b₀,r}·N^{tail}_{b₀',r−Δ}, cross-corrélation tail [PROUVÉ] | R50 |
| **Unification between-within** | Quasi-uniformité tail contrôle V_{b₀} ET Z simultanément [SEMI-FORMEL] | R50 |
| **TQL** (Tail Quasi-uniformity) | N^{tail}≈C/p ⟹ Z≈0 ET V≈0, cible unifiée pour ACaL complet [FORMULÉ] | R50 |
| **Aliasing de phase** | ord_p(2)<max_B+1 → 2^{b₀} non distincts mod p → corrélation artificielle [OBSERVÉ] | R50 |
| **Régime α=4** | ord≥4·(max_B+1) : max|ρ| chute à 0.39 (transition de phase empirique) [OBSERVÉ] | R50 |
| **Identité rotation tail** | N^{tail}_{b₀,r} = N^{std}_{r·α⁻¹ mod p}, α=2^{b₀}·g, tail = sous-problème rotaté exactement [PROUVÉ] | R51 |
| **μ-invariance** | μ^{tail}(b₀) = μ(k-1, [0, max_B-b₀], p) : la rotation ne change pas μ [PROUVÉ] | R51 |
| **TQL-mu** | μ(b₀)−1 ≤ K·p/C_{b₀}, K(R3)=1.29, K(R1)=2.61, K(global)=4.32 [LEMME CANDIDAT] | R51 |
| **Lemme A (max-sub)** | μ(k) ≤ max_{b₀} μ(k-1, M-b₀, p), vrai universellement (50+/50+) [OBSERVÉ] | R51 |
| **Chaîne TQL→f_p** | TQL-mu → V_{b₀}≤K·C_{b₀} → |Z|≤K·√(C_i·C_j) → V/C²=O(max_B/C)→0 → f_p→1/p [SEMI-FORMEL] | R51 |
| **μ-lite collision** | E_excess/C borné en R1 ⟹ V≤A·C ⟹ μ−1≤A·p/C ; reformulation purement combinatoire [LEMME CANDIDAT] | R52 |
| **V ≤ A·C en R1** | V≤1.42·C dans TOUS les 232 cas R1+ (échoue globalement : V/C=10.4 pour p=5) [OBSERVÉ] | R52 |
| **E_excess/C borné R1** | \|E_excess/C\|<0.90 en R1, collisions excédentaires sous-linéaires en C [OBSERVÉ] | R52 |
| **Cancellation cross-terms** | Cross-terms spectraux s'annulent 75-88% en R1+ via phases ω^{r·(2^{b₀}−2^{b₀'})} [OBSERVÉ] | R52 |
| **Horner > CS factor** | Borne Horner 3.7-5.5× meilleure que Cauchy-Schwarz seul en R1 [OBSERVÉ] | R52 |
| **h=1 vacuous en R1** | ord_p(2) > max_B ⟹ ∄Δ avec ord\|Δ et 1≤Δ≤max_B, donc 0 collisions h=1 [PROUVÉ] | R53 |
| **E_excess < 0 en R1** | Monotonie crée anti-concentration : sous-collisions, pas sur-collisions [OBSERVÉ] | R53 |
| **Min Hamming + poly vanishing** | h≥2 + Σg^j·Δ_j≡0 mod p contraint les collisions : route vers E_excess=O(C) [SEMI-FORMEL] | R53 |
| **Collision degree diffus** | Gini(coll) décroît 0.575→0.152 avec C, pas de hub vectors, excess spread [OBSERVÉ] | R53 |
| **E_intra dominance** | Fixer B_{k-1}=b : E_intra = 65-96% de E_excess en R1, induction viable [OBSERVÉ] | R53 |
| **Weighted inductive contraction** | Σ(C_b/C)²·μ(k-1,b,p)/μ(k,M,p) ∈ [0.51,0.67], contraction universelle (6/6) [OBSERVÉ] | R54 |
| **Weighted Inductive V-bound** | V(k)≤α·Σ(C_b/C)·V(k-1,b,p)+β·C, α<2.25, β<0.61, base V(2)/C<2 [LEMME CANDIDAT] | R54 |
| **h=2 signature unique** | Pour (a,b,δ_a,δ_b) fixés, B_a−B_b uniquement déterminé par poly constraint en R1 [CALCULÉ] | R54 |
| **N_2 sub-simplex prediction** | N_2 calculable exact = signature counting × stars-and-bars, 6/6 parfait [CALCULÉ] | R54 |
| **V_cross anti-corrélation** | V_cross<0 dans 4/6 cas, |V_cross/C|<0.27 : inter-tranche réduit V_total [OBSERVÉ] | R54 |
| **Dichotomie ANOVA** | V_cross<0 ⟹ V≤V_within (direct) mais ρ>1 ; V_cross>0 ⟹ ρ<1 mais V>V_within. Aucun régime ne donne les deux [OBSERVÉ] | R55 |
| **|γ| = |V_cross/V_within| < 1** | Terme croisé ne domine jamais le within : γ∈[-0.75,+0.39], universel 7/7 cas [OBSERVÉ] | R55 |
| **Shift-invariance k=2** | P_{B+(1,1)} = 2g·P_B mod p, conséquence algébrique directe, orbites sous shift identifiées [PROUVÉ] | R55 |
| **Base A(2) ≤ 1.22 en R1** | V(2)/C(2) borné sur 622 cas R1, mécanisme = orbites complètes s'annulent, bords seuls contribuent [OBSERVÉ] | R55 |
| **Base-lite + bootstrap** | A(2)≤K prouvable via décomposition orbitale, bootstrap vers k≥3 via |γ|<1 + contrôle V_cross [LEMME CANDIDAT] | R55 |
| **Cas dégénéré g≡-1 mod p** | P_{(a,a)}=0 ∀a (concentration diagonale sur r=0), N_0≥M+1, seule source A>2, rare (9/2931=0.3%) [PROUVÉ] | R56 |
| **Décomposition orbitale exacte** | N_r = N_r^{complet} + N_r^{incomplet}, orbites complètes → V=0 (coset), incomplètes = bord contribuant [PROUVÉ] | R56 |
| **CS insuffisance (Jensen)** | θ_CS = Σ|Z_{CS}|/V_within ≥ n-1 ≥ 1 par Jensen, Cauchy-Schwarz ne peut structurellement prouver |γ|<1 [PROUVÉ] | R56 |
| **Phase cancellation 89%** | |V_cross| utilise 11% du bound CS, 89% annulé par rotations ω^{r·Δ(b,b')} : vrai mécanisme [OBSERVÉ] | R56 |
| **Décroissance |V_cross|/C ~ C^{-0.25}** | V_cross = o(C) observé asymptotiquement, plus fort que V_cross=O(C), fit power-law [OBSERVÉ] | R56 |
| **Gap max N_r** | Prouver A(2)≤K se réduit à borner max_r N_r = #{(a,b): 2^a+g·2^b≡r mod p} via structure log discret [IDENTIFIÉ] | R56 |
| **δ-reformulation** | N_r = #{δ ∈ [0,M] : dlog(r/c_δ) ∈ [0,M-δ]}, c_δ=(1+g·2^δ) mod p, factorisation P=2^a·c_δ [PROUVÉ] | R57 |
| **Suite affine c_δ** | c_{δ+1} = 2c_δ − 1 mod p, suite AFFINE (pas géométrique), tous c_δ distincts en R1 [PROUVÉ] | R57 |
| **Borne triviale N_r ≤ M+1 en R1** | Chaque δ contribue au plus 1 solution (car ord > M+1), borne exacte atteinte par N_0 si g≡-1 [PROUVÉ] | R57 |
| **Borne sub-triviale K_lin < 1** | max N_r ≤ C/p + 0.76·(M+1) en R1 générique : distribution PAS concentrée [OBSERVÉ] | R57 |
| **Identité bilinéaire Z** | Z_{b,b'} = #{(a,a'): a+b≡a'+b' mod ord, a∈[0,b], a'∈[0,b']} − C_b·C_{b'}/p, forme bilinéaire exacte [PROUVÉ] | R57 |
| **Cancellation agrégée 50%** | |Σ Z_{b,b'}|/Σ|Z_{b,b'}| ≈ 0.50, signes mixtes (44%/56%), cancellation structurelle [OBSERVÉ] | R57 |
| **Cross-lite Candidat B** | |V_cross|/C → 0 (pente -0.246 en log-log), target le plus robuste et le plus prouvable [OBSERVÉ] | R57 |
| **K' Kloosterman normalisé** | |Z|/(baseline·√p) < 1 dans tous les cas testés, connexion Weil non rigoureuse [OBSERVÉ] | R57 |
| **Formulation canonique gap dlog** | Prouver max_r N_r ≤ α·(M+1) pour α<1, avec fenêtres [0,M-δ] rétrécissantes + récurrence affine c_{δ+1}=2c_δ−1 [SEMI-FORMALISÉ] | R58 |
| **K_linear** | (max N_r − C/p)/(M+1), métrique cible : K_lin<1 pour TOUS les 92 cas testés, moyen 0.18, max 0.76 [OBSERVÉ] | R58 |
| **Route 2 (fenêtres variables)** | Compter les δ dans fenêtres [0,M-δ] rétrécissantes : la plus crédible des 3 routes (vs sommes exp, vs collisions) [SÉLECTIONNÉE] | R58 |
| **Discrepancy dlogs c_δ** | D∞/(1/√n) ∈ [0.39, 0.97] : comparable à pseudo-aléatoire mais non uniforme dans (Z/pZ)* [OBSERVÉ] | R58 |
| **Incréments Δ_δ** | dlog(c_{δ+1})−dlog(c_δ) : tous uniques, variance sub-uniforme pour certains p (0.23 pour p=1021) [OBSERVÉ] | R58 |
| **Sommes exponentielles S(h) sur dlogs** | Cancellation >50% pour la plupart des primes, mais partielle (24% min pour p=1021) [OBSERVÉ] | R58 |
| **Clustering des contributeurs max N_r** | Les δ maximisant N_r sont GROUPÉS en espace dlog : ratio distance 0.02-0.27 [OBSERVÉ] | R58 |
| **Implication additive ⟹ cross** | max N_r borné ⟹ Σ N_r² borné ⟹ V_cross borné : Candidat 1 contrôle base ET cross simultanément [PROUVÉ] | R58 |
| **Surmultiplicité bornée** | Σ N_r² / (C²/p) ≤ 2.72 (cas significatifs), explose pour petits M [OBSERVÉ] | R58 |
| **Barrier counting reformulation** | N_r = #{δ ∈ [0,M] : δ + d_δ ≤ M}, d_δ = dlog(r/c_δ), comptage de points sous barrière linéaire [SEMI-FORMALISÉ] | R59 |
| **Formulation F4 (α < 1)** | max N_r ≤ C/p + α·(M+1) avec α < 1 universel, la plus réaliste des 4 formulations comparées [SÉLECTIONNÉE] | R59 |
| **Lemme K-lite** | Premier lemme prouvable pour base k=2 : α < 1 via barrier counting, Ladder 5/9 [LEMME CANDIDAT] | R59 |
| **Window dominance** | Difficulté vient principalement des fenêtres, pas de la suite affine (ratio real/random = 0.89) [OBSERVÉ] | R59 |
| **Contributions small-δ** | Contributions au max N_r dominées par petits δ : frac_low = 0.67 en moyenne [PROUVÉ] | R59 |
| **Route 6 (Barrier Counting)** | Compter directement les points (δ, d_δ) sous d = M − δ, route prioritaire R60 [SÉLECTIONNÉE] | R59 |
| **Route 8 (Nesting)** | Sauts rares dans suite des hits (≤ 1 par cas), emboîtement monotone des fenêtres, route auxiliaire [OBSERVÉ] | R59 |
| **α-régimes décroissants** | α décroît avec sous-régime : R3 < R2 < R1 < global, hiérarchie cohérente [OBSERVÉ] | R59 |
| **α_max = 0.50 pointwise** | 34 cas testés, max α = 0.50, borne suffisante pour A(2) = O(1) en R1 [OBSERVÉ] | R59 |
| **Bridge décomposition A+B** | (A) géométrie barrière triangle C=(M+1)(M+2)/2 [PROUVÉ] + (B) suite affine non concentrante [À PROUVER] | R60 |
| **Discrepancy pondérée max_Dw** | max_Dw = α·(M+1)/C, identité EXACTE reliant discrepancy pondérée par fenêtre à α [PROUVÉ] | R60 |
| **Preuve conditionnelle** | Sous d_δ uniformes : Pr[α≥1] < 0.01% (1000 simulations), bridge conditionnel VALIDE [OBSERVÉ] | R60 |
| **Schéma 4 sous-étapes** | (a) reformulation δ [PROUVÉ] (b) \|S_δ\|≤1 [PROUVÉ] (c) transition hit-hit<1 [CONJECTURAL] (d) intégration [À PROUVER] | R60 |
| **Transition hit-hit** | Taux moyen = 0.0625, max ponctuel = 1.0 (cas dégénérés n=2). Verrou = prouver < 1 uniformément [CONJECTURAL] | R60 |
| **Nesting sous-lemme J_r** | J_r ≤ 2M²/ord + 2 : nombre de sauts borné, structure en grappes courtes [OBSERVÉ] | R60 |
| **Bridge-lite pointwise** | Premier schéma de preuve articulé pour K-lite : α < 1 via 4 sous-étapes, Ladder 5/9 [LEMME CANDIDAT] | R60 |
| **Taux de transition hit-hit τ(r)** | #{hit→hit parmi hits éligibles} / #{hits éligibles}, formulation canonique du verrou (c) [SEMI-FORMALISÉ] | R61 |
| **ε = 1 − τ_max** | Gap explicite, cible ε ≥ c/log(ord), c ∈ [2.6, 4.2], forme fonctionnelle stable [OBSERVÉ] | R61 |
| **Route 3 rareté** | Décroissance géométrique des chaînes de hits (ρ ≈ 0.04), 96.5% longueur 1, route prioritaire [OBSERVÉ] | R61 |
| **Hit-hit-lite pointwise** | Survivant R62 : τ(r) < 1−ε en R3, une pièce manquante = quasi-uniformité d_δ [SEMI-FORMALISÉ] | R61 |
| **Séparation fenêtre/dynamique** | Ratio τ_real/τ_random ≈ 0.96, géométrie fenêtres = facteur dominant, structure multiplicative neutre [PROUVÉ] | R61 |
| **Dilution géométrique** | ε_dilution = (p+1)/(2(p−1)) → 1/2 : fenêtre couvre ≤ 1/2 de [0,p−1], formule EXACTE [PROUVÉ] | R62 |
| **Quasi-uniformité d_δ** | D∞(d_δ) < 0.10 pour p≥251, KS moyen = 0.017, vérifié numériquement [OBSERVÉ] | R62 |
| **Sous-lemme ε>0 conditionnel** | Si D∞ < 1/2 alors τ ≤ 1/2 + D∞ < 1, preuve conditionnelle complète [PROUVÉ CONDITIONNEL] | R62 |
| **Lemme d'équidistribution** | Verrou final : prouver D∞(d_δ) → 0 en R3 via Erdős-Turán + sommes exponentielles [IDENTIFIÉ] | R62 |
| **ε-lite par dilution** | Survivant R63 : τ ≤ 1/2 + D∞, une pièce = équidistribution, Ladder L5 [SEMI-PROUVÉ] | R62 |
| **Réduction Erdős-Turán** | D∞ ≤ 1/H + (1/M)·Σ|S_h|/h, inégalité standard appliquée au problème [PROUVÉ] | R63 |
| **Somme exponentielle S_h** | S_h = Σ χ_h(1+g^{2δ}) sur ⟨g²⟩, objet minimal unique à borner [IDENTIFIÉ] | R63 |
| **Gain carré-racine** | |S_h|/(M+1) < 0.11, |S_h|/√p ≈ 0.50, borne Weil-like plausible [OBSERVÉ] | R63 |
| **Récurrence affine** | c_{δ+1} = g²·c_δ + (1−g²) dans F_p, structure exploitable [PROUVÉ] | R63 |
| **D∞-lite analytique** | D∞ = O(ln(p)/√p) → 0 sous |S_h| ≤ C·√p, survivant R64 Ladder L6 [SCHÉMA DE PREUVE] | R63 |
| **Seuil pratique** | p_seuil ≈ 4538 pour η < 1/4 (marge confortable τ < 3/4) [CALCULÉ] | R63 |
| **Complétion sous-groupe** | S_h = (A_h+B_h)/2 via indicatrice (1+η(t))/2 de ⟨g²⟩, décomposition EXACTE [PROUVÉ] | R64 |
| **Orthogonalité A_h = −1** | Σ_{F_p*} χ_h(1+t) = −1 pour χ_h non trivial, par orthogonalité des caractères [PROUVÉ] | R64 |
| **Jacobi B_h = η(−1)·J(η,χ_h)** | Substitution t→−t, |J(η,χ_h)| = √p classique [PROUVÉ] | R64 |
| **Borne |S_h| ≤ (1+√p)/2** | Conséquence directe de A_h+B_h, ratio max 0.999 [PROUVÉ] | R64 |
| **Sous-étape (c) FERMÉE** | τ < 1 pour p ≥ 37 en R3, via D∞→0 PROUVÉ + dilution PROUVÉE [PROUVÉ] | R64 |
| **Seuil p_0 = 37** | ε > 0 garanti dès p ≥ 37, p_comfort = 167 pour D∞ < 0.25 [CALCULÉ] | R64 |

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
| **Phase shift = clé R50** | Z dépend d'une constante Δ par paire : cross-corrélation tail décalée [PROUVÉ] | R50 |
| **Unification between-within** | Quasi-uniformité tail contrôle V_{b₀} ET Z : même mécanisme pour les 2 moitiés [SEMI-FORMEL] | R50 |
| **Aliasing de phase** | ord<max_B+1 → phases non distinctes → corrélation artificielle = source des cas durs [OBSERVÉ] | R50 |
| **Seuil α=4** | ord≥4·(max_B+1) : max|ρ| chute de 0.655 à 0.393, transition empirique nette [OBSERVÉ] | R50 |
| **CS loin du tight** | avg(|Z|/√V·V')=0.276, CS tendu uniquement pour ord=3 (cas dégénéré) [OBSERVÉ] | R50 |
| **Cancellation signe agrégée** | avg ratio=0.483, min=0.027, approche agrégée supérieure à paire-par-paire [OBSERVÉ] | R50 |
| **Shift anti-sym+transitif** | Δ(i,j)+Δ(j,i)≡0, Δ(a,b)+Δ(b,c)≡Δ(a,c) : structure de groupe [PROUVÉ] | R50 |
| **|ρ|<1 universel (264)** | Confirmé 264/264 paires (extension massive de 20/20 R49), max=0.687 [OBSERVÉ] | R50 |
| **μ−1 = meilleure métrique** | μ−1 = p·V/C² = D₂², invariant par rotation, additif en ANOVA, plus algébrique que D∞ [PROUVÉ] | R51 |
| **D∞ non uniforme en b₀** | D∞ explose pour tranches dégénérées (C_{b₀}=1 ⟹ D∞=p-1), poids (C/C)² négligeable [OBSERVÉ] | R51 |
| **K(sous-régime) borné** | K(R3)=1.29, K(R2)=2.61, K(R1)=2.61, K(global)=4.32 ; croît avec l'aliasing [OBSERVÉ] | R51 |
| **Tail = sous-problème rotaté** | Identité exacte (pas approximation) : facteur α=2^{b₀}·g mod p est une permutation [PROUVÉ] | R51 |
| **Cascade naïve ÉCHOUE p=5** | A(k) croît 0.8→17.0 monotonement pour p=5 ; petits primes = obstruction structurelle | R51 |
| **p=11 cascade parfaite** | A stabilisé à 0.91 de k=2 à k=10 : modèle de ce que la cascade DEVRAIT être [OBSERVÉ] | R51 |
| **Contraction inductive 0.01-0.17** | μ(k)-1 toujours < max(μ(k-1)-1), facteur 0.003-0.17, dimension AIDE [OBSERVÉ] | R51 |
| **Chaîne TQL→ACL→f_p** | TQL-mu ⟹ V/C²=O(max_B/C) ⟹ QEL ⟹ ACL ⟹ f_p→1/p : première chaîne complète identifiée [SEMI-FORMEL] | R51 |
| **V ≤ 1.42·C en R1** | Borne V=O(C) tient dans tout R1 (232 cas), K_max=1.41. ÉCHOUE globalement (p=5 : V/C=10.4) [OBSERVÉ] | R52 |
| **E_excess/C < 0.90 en R1** | Collisions excédentaires bornées, E/C typiquement négatif (mean −0.33 à −0.37) [OBSERVÉ] | R52 |
| **K < 1.42 en R1** | K=(μ−1)·C/p : K_max=1.42 en R1 vs 4.3 global (R51). Sous-régime fait vraie différence [OBSERVÉ] | R52 |
| **Fit μ−1 ≈ K·p/C** | R²=0.909, meilleur que log (0.565) ou max_B (0.425). Power-law p^1.26/C^1.11 (R²=0.963) [OBSERVÉ] | R52 |
| **p=5 = seule source** | En R_gen K atteint 10.4, TOUJOURS à cause de p=5. En R1, p=5 rare (ord=4, max_B≥2 pour k≥4) [OBSERVÉ] | R52 |
| **Cancellation 75-88%** | Ratio cancellation (|actual|/|trivial|) : R3=0.112, R2=0.154, R1=0.249. Interférence destructive [OBSERVÉ] | R52 |
| **Quasi-orthogonalité |ρ|** | |ρ| par régime : R3=0.10, R2=0.28, R1=0.30, R_gen=0.51. Hiérarchie claire [OBSERVÉ] | R52 |
| **Horner 3.7-5.5× sur CS** | Facteur amélioration : R3=3.55×, R2=5.48×, R1=3.73×. Gain structurel réel [OBSERVÉ] | R52 |
| **Contraction inductive <0.13** | (μ−1)/avg(sub μ−1) < 0.13 uniformément : dimension k comprime la variance [OBSERVÉ] | R52 |
| **E_excess NÉGATIF en R1** | Sous-collisions systématiques : E/C ∈ [-0.61, -0.25] pour k=3..7, monotonie = anti-concentration [OBSERVÉ] | R53 |
| **h=1 = 0 en R1 [PROUVÉ]** | ord_p(2)>max_B en R1 ⟹ aucun Δ∈[1,max_B] divisible par ord. Conséquence directe LSD+R1 [PROUVÉ] | R53 |
| **Toutes collisions R1 ont h≥2** | Corollaire immédiat de h=1 vacuous. Contraint chaque collision à ≥2 positions modifiées [PROUVÉ] | R53 |
| **Gini collisions → 0** | Coefficient Gini : 0.575 (k=3) → 0.152 (k=7), pas de concentration sur hub vectors [OBSERVÉ] | R53 |
| **Near frac décroît** | corr(logC, frac_near) = -0.675, contributions se dispersent sur h=1..k pour grand C [OBSERVÉ] | R53 |
| **E_intra = 65-96%** | Décomposition par B_{k-1} : intra-slice domine cross-slice dans 4/5 cas R1 [OBSERVÉ] | R53 |
| **|E_b/C_b| ≤ 0.67** | Borne uniforme par tranche de dernière coordonnée : pas de tranche pathologique [OBSERVÉ] | R53 |
| **r=0 non dominant** | r=0 dominant V dans 33% des cas seulement. Discrepancy collective sur 45-71% résidus [OBSERVÉ] | R53 |
| **Min Hamming + poly = 12/15** | Meilleure stratégie sur 7 testées : viabilité 4, tightness 4, provability 4 [ÉVALUÉ] | R53 |
| **Contraction pondérée 0.51-0.67** | Σ(C_b/C)²·μ(sub)/μ(full) : stable, universelle 6/6, petites tranches neutralisées par (C_b/C)² [OBSERVÉ] | R54 |
| **Contraction pointwise ÉCHOUE** | max_b μ(sub) = 15.5×μ(full) pour k=7 : tranche b=1 (C_b=6) a μ=18.14 vs μ_full=1.17 [RÉFUTÉ] | R54 |
| **V_cross < 0 dans 4/6 cas** | Anti-corrélation inter-tranches : V_intra/V=100-151%, V_cross AIDE le total [OBSERVÉ] | R54 |
| **E_intra se renforce avec k** | 65%→90%→96% de E_excess : induction de plus en plus propre quand k augmente [OBSERVÉ] | R54 |
| **h≥3 domine : 98.3% à k=7** | Route h-par-h impraticable pour grand k, seule approche globale viable [OBSERVÉ] | R54 |
| **h=2 prédiction exacte 6/6** | Signature + poly constraint + stars-and-bars = N_2 exact sans énumération [CALCULÉ] | R54 |
| **Heuristique indépendance ÉCHOUE** | N_h réel/prédit = 7000× pour h=3 k=7 : corrélations monotone dominent [RÉFUTÉ] | R54 |
| **α < 2.25 stable** | Constante de récurrence V(k)≤α·weighted_V+β·C : α borné, ne diverge pas avec k [OBSERVÉ] | R54 |
| **Base V(2)/C < 2** | 25 primes testées, V/C ∈ [0.14, 1.23] : base case solide pour récurrence [OBSERVÉ] | R54 |
| **Dichotomie V_cross signe** | V_cross<0 pour k=3..6, V_cross>0 pour k≥7 : signe change, récurrence unique impossible [OBSERVÉ] | R55 |
| **|γ|<1 universel (7/7)** | γ=V_cross/V_within : [-0.75, +0.39], V_cross ne domine jamais V_within [OBSERVÉ] | R55 |
| **3 formes récurrence testées** | Additive (β change signe), multiplicative (ρ>1 petit k), α-contraction (instable) : aucune universelle [OBSERVÉ] | R55 |
| **Shift P_{B+(1,1)}=2g·P_B** | k=2 en R1 : algébrique direct, crée orbites de longueur ord_p(2g) [PROUVÉ] | R55 |
| **A(2)≤1.22 sur 622 cas R1** | Orbites complètes annulent variance, seuls termes de bord contribuent. Moy=0.89, med=0.88 [OBSERVÉ] | R55 |
| **A(2) diverge hors R1** | A(2)>5 possible quand ord<max_B : borne A≤K spécifique à R1 [OBSERVÉ] | R55 |
| **Transport k=2→k+1 : 79%** | V_cross≤0 ⟹ V(k)≤V_within ⟹ transport, marche dans 5/7 cas R1, échoue k≥7 [OBSERVÉ] | R55 |
| **ρ>1 pour k petit** | ρ=V_within/V>1 pour k=3..6 (car V_cross<0) : contraction multiplicative non universelle [OBSERVÉ] | R55 |
| **Chemin preuve A(2)** | Orbites shift → complètes O(1) contrib. → incomplètes ≤max_B → contrib ≤ longueur → V=O(max_B²)=O(C) [SEMI-FORMEL] | R55 |
| **V_cross = vrai verrou** | Ni récurrence ni base ne sont le problème : c'est le contrôle du terme croisé inter-tranches [IDENTIFIÉ] | R55 |
| **A(2) corrigé ≤ 2.28** | R55 donnait ≤1.22 sur 622 cas. R56 sur 2931 cas : max A=2.28 (dégénéré g≡-1), max A(générique)=1.89 | R56 |
| **g≡-1 mod p : concentration** | P_{(a,a)}=Σ(2^a+g·2^a)=Σ(1+g)·2^a≡0. Toute la diagonale mappe sur r=0 ⟹ N_0≥M+1 | R56 |
| **Orbites complètes V=0** | Si orbite shift = coset complet de Z/pZ, la contribution à V s'annule exactement (somme nulle sur coset) | R56 |
| **En R1 strict : toutes orbites incomplètes** | ord_p(2g) > max_B+1 en R1 ⟹ aucune orbite complète, lemme V=0 vacueux [PROUVÉ] | R56 |
| **Gap = max N_r via log discret** | Borner A(2) se réduit à : combien de paires (a,b) satisfont 2^a+g·2^b≡r mod p pour le pire r | R56 |
| **Factorisation spectrale S(r)** | S(r) = Σ_b ω^{rg·2^b}·T(r,b) vérifié exactement (200 cas). Sépare contribution par tranche b [PROUVÉ] | R56 |
| **CS structurellement insuffisant** | Jensen inequality appliquée à la convexité de |·| : bound CS ≥ V_within toujours, |γ|<1 inatteignable par CS | R56 |
| **Quasi-orthogonalité aussi insuffisante** | QO seule ne suffit pas : |γ|<1 nécessite cancellation de PHASES en plus de quasi-orthogonalité [OBSERVÉ] | R56 |
| **|γ|<1 confirmé 28/28** | Extension de 7/7 (R55) à 28/28 (R56, k=3..9), max|γ|=0.87 (k=3,p=5), robuste [OBSERVÉ] | R56 |
| **V_cross signe non prédictible** | V_cross change de signe selon (k,p), pas juste selon k. Pas de pattern simple [OBSERVÉ] | R56 |
| **Spectral reformulation V_cross** | V_cross = (1/p)Σ_{r≥1}Σ_{b≠b'} S_b(r)·conj(S_{b'}(r)), identité exacte vérifiée (120 sous-tests) [PROUVÉ] | R56 |
| **δ-reformulation = bonne vue** | P_{(a,b)}=2^a·c_{b-a}, N_r=#{δ:dlog(r/c_δ)∈[0,M-δ]}, réduit tout à comptage de hits dans fenêtres | R57 |
| **c_δ affine, pas géométrique** | c_{δ+1}=2c_δ−1 : pseudo-orbite plus complexe qu'orbite multiplicative. log(somme)≠somme(log) = difficulté | R57 |
| **max N_r / (M+1) ≤ 0.91 générique** | Distribution PAS concentrée : aucun résidu ne capture >91% des couches δ [OBSERVÉ, 300+ cas] | R57 |
| **Borne sqrt : K=6.48** | max N_r ≤ C/p + 6.48·√(M+1), tight, donnerait A(2)=O(p/M)→0 si prouvable [OBSERVÉ] | R57 |
| **N_0 pas spécial en générique** | N_0 < max_{r>0} N_r dans 95% des cas : r=0 n'est pas le résidu le plus chargé [OBSERVÉ] | R57 |
| **Z = congruence bilinéaire** | Z_{b,b'} = #{a+b≡a'+b' mod ord} − C_b·C_{b'}/p : réduit le cross à un lattice counting [PROUVÉ] | R57 |
| **CS ratio 0.115** | |V_cross|/CS_bound = 11.5% en moyenne : CS perd 88.5% de l'énergie par design [CONFIRMÉ] | R57 |
| **Signes Z mixtes 44/56%** | Z_{b,b'} positifs 44%, négatifs 56% : cancellation agrégée structurelle, pas artefact [OBSERVÉ] | R57 |
| **K' Kloosterman < 1 normalisé** | |Z|/(C_b·C_{b'}/p·√p) borné < 1 : borne type Weil plausible mais non rigoureuse [OBSERVÉ] | R57 |
| **Maturité cross 3/5** | ✅ Identité bilinéaire ✅ CS compris ✅ Cancellation quantifiée ❌ |Z| bound ❌ Weil connection [ÉVALUÉ] | R57 |
| **5 outils morts cross** | CS, QO seule, récurrence univ., V_cross≤0 univ., ρ<1 univ. — ne PAS ressusciter [INVENTORIÉ] | R57 |
| **Discrepancy L∞ comparable pseudo-random** | D∞/(1/√n) ∈ [0.39, 0.97] sur 6 primes : dlogs c_δ pas uniformes mais discrepancy du bon ordre [OBSERVÉ] | R58 |
| **Incréments dlog sub-uniforme** | Variance(Δ_δ)/Var(uniform) descend à 0.23 (p=1021) : structure affine crée corrélations subtiles [OBSERVÉ] | R58 |
| **Cancellation exp. sums partielle** | Min cancellation 24% (p=1021 h=9) : pas de garantie >50% universelle, route 1 fragile [OBSERVÉ] | R58 |
| **K_lin < 1 universel (92/92)** | Jamais de cas K≥1 dans les 92 tests (p,n) : borne sub-triviale très robuste empiriquement [OBSERVÉ] | R58 |
| **√(M+1) vs (M+1) scaling** | K_sqrt max=8 mais K_linear max=0.76 : le scaling linéaire en M+1 est plus propre que √(M+1) [OBSERVÉ] | R58 |
| **Candidat 2 perte √p** | √(Σ N_r²)/max N_r ≈ 6.2 en moyenne : passage L²→L∞ trop lâche, facteur 448× [CALCULÉ] | R58 |
| **V_cross = Σ N_r² − C** | Identité exacte V_cross = Σ N_r(N_r−1), vérifié exhaustivement [PROUVÉ] | R58 |
| **Candidat 1 score 14 vs 7** | Arbitrage systématique : additive bat second moment en serrage, utilité, démontrabilité, et contrôle cross [CALCULÉ] | R58 |
| **c_δ couvre 12-31% de (Z/pZ)**** | Suite affine TRÈS structurée : loin de l'uniformité multiplicative, approche probabiliste non justifiée [PROUVÉ] | R58 |
| **Contributeurs max N_r GROUPÉS** | Distance médiane dlogs des contributeurs = 2-27% de ord : collisions structurées, pas aléatoires [OBSERVÉ] | R58 |
| **|V_cross|/(C²/p) < 1.14** | Préparation cross R57 reste viable après nouvelle lecture δ de la base : cross toujours intact [OBSERVÉ] | R58 |
| **Ratio real/random = 0.89** | max N_r réel / max N_r aléatoire ≈ 0.89 : suite affine ne crée pas de concentration pathologique [OBSERVÉ] | R59 |
| **F1-F4 comparaison** | F1 √(M) stretch, F2 (M)^θ intermédiaire, F3 log trop agressif, F4 α·(M+1) OPTIMAL : K le plus borné [CALCULÉ] | R59 |
| **α_max = 0.50 (34 cas)** | Candidat 1 pointwise : α maximal observé = 0.50, moyenne ≈ 0.18, borne robuste [OBSERVÉ] | R59 |
| **Large sieve borne ≥ M+1** | Large sieve donne (M+1)·(1+M/ord) ≥ M+1 toujours : structurellement inutile comme route directe [PROUVÉ] | R59 |
| **Nesting : sauts ≤ 1** | Dans la suite des δ contributeurs consécutifs, nombre de sauts (d_δ croissant) ≤ 1 dans tous les cas [OBSERVÉ] | R59 |
| **d_δ non-croissant 67%** | Parmi les δ contributeurs, d_δ décroît 67% du temps : emboîtement naturel des fenêtres [OBSERVÉ] | R59 |
| **frac_low = 0.67** | Contributions au max N_r dominées par δ ≤ M/2 (grandes fenêtres) : conséquence directe |W_δ| décroissant [PROUVÉ] | R59 |
| **Candidat 2 ≤ Candidat 1** | √V ≈ c·M ≥ α·(M+1) toujours : hybride L² reconstruit même borne linéaire avec pire constante [PROUVÉ] | R59 |
| **A(2) impliqué par α** | Si α < 1 : A(2) ≤ 1 + 2α·p/(M+2), borné en R1 car p/(M+2)=O(1) [SEMI-FORMEL] | R59 |
| **T108-T109 confirmés numériquement** | Σ N_r² ≤ max_Nr · C et V_cross ≤ (max_Nr−1)·C vérifiés sur tous les cas R59 [CONFIRMÉ] | R59 |
| **Preuve conditionnelle = étape R60** | Si d_δ équidistribués ⟹ α < 1 par fluctuations standard ; bridge = noyau dur [IDENTIFIÉ] | R59 |
| **Bridge = discrepancy pondérée** | D∞ standard (non pondérée, max 0.72) ne suffit PAS, la couverture pondérée par taille de fenêtre est la bonne métrique [PROUVÉ] | R60 |
| **Taux transition hit-hit = 0.0625** | Hits consécutifs (δ et δ+1 sous la barrière) très rares en moyenne, max ponctuel = 1.0 pour n=2 [OBSERVÉ] | R60 |
| **Preuve conditionnelle < 0.01%** | Sous uniforme, α ≥ 1 dans < 0.01% des 1000 simulations. Bridge conditionnel = solide [OBSERVÉ] | R60 |
| **α ≤ 1 − 1/(4·log(ord)) en R3** | Énoncé intermédiaire crédible pour sous-régime R3 (ord > 4(M+1)), vérifié numériquement [CONJECTURAL] | R60 |
| **Nesting = auxiliaire, pas moteur** | J_r ≤ 2M²/ord+2 vérifié, mais ne borne PAS α directement, réduit l'espace de configurations [OBSERVÉ] | R60 |
| **Candidat 2 bridge+nesting éliminé** | Score 39/60 vs 49/60, prouver α=O(1/√M) strictement plus dur que α<1 [CALCULÉ] | R60 |
| **Sous-étapes (a)+(b) Ladder 7/8** | Reformulation δ et injectivité dlog prouvées, fondation solide du schéma [PROUVÉ] | R60 |
| **Verrou = sous-étape (c)** | Taux transition hit-hit < 1 uniformément. Outils standard (Weil, Weyl) inapplicables car d_δ ≠ polynôme en δ [IDENTIFIÉ] | R60 |
| **Chaîne globale K-lite → f_p** | K-lite ⟹ A(2) borné ⟹ V/C²→0 ⟹ f_p→1/p, tous maillons vérifiés numériquement [SEMI-FORMEL] | R60 |
| **V/C² converge ≈ 1/3** | Consistant avec 2α/(M+2)→0 pour M croissant, contrôle cross intact [OBSERVÉ] | R60 |
| **α décroît 95.5% des transitions** | α diminue quand n augmente dans 95.5% des cas, convergence robuste [OBSERVÉ] | R60 |
| **τ_moyen = 0.317** | Taux transition hit-hit fortement sous 1, τ_max = 0.529, ε ≥ 0.47 sur 4 primes [OBSERVÉ] | R61 |
| **ε ≈ c/log(ord)** | Forme fonctionnelle stable, c ∈ [2.6, 4.2], cible prouvable [OBSERVÉ] | R61 |
| **Ratio τ_real/τ_random = 0.96** | Géométrie fenêtres (|W_{δ+1}|=|W_δ|−1) = facteur dominant, multiplicativité neutre [PROUVÉ] | R61 |
| **Décroissance géométrique chaînes** | ρ ≈ 0.04, 96.5% longueur 1, 3.5% longueur 2, aucune plus longue [OBSERVÉ] | R61 |
| **Route 3 rareté score 8/10** | Meilleure route parmi 4 comparées, décroissance géométrique nette [CALCULÉ] | R61 |
| **Candidat 1 > Candidat 2 : 71 vs 68** | Hit-hit-lite pointwise plus simple et mieux intégrable dans (d) que chaînes courtes [CALCULÉ] | R61 |
| **0 cas dégénérés sur 1086** | Aucun τ=1 observé hors cas triviaux, mais non exclu théoriquement [OBSERVÉ] | R61 |
| **Chaîne (c)→(d)→K-lite→f_p valide R3** | 20 cas R3 testés, chaîne complète valide, sous-régime ne brise rien [SEMI-FORMEL] | R61 |
| **Verrou = quasi-uniformité d_δ** | Pièce manquante : P(d_{δ+1} ∈ [0,M−δ−1] | d_δ ∈ [0,M−δ]) < 1 pour ord suffisant [IDENTIFIÉ] | R61 |
| **ε_dilution = 1/2 exact** | Formule (p+1)/(2(p−1)), gap substantiel et indépendant de p [PROUVÉ] | R62 |
| **τ_théorique = 0.250** | Sous uniformité, formule fermée τ = (M+1)/(2(p−1)), très loin de 1 [CALCULÉ] | R62 |
| **KS = 0.017** | Test Kolmogorov-Smirnov : d_δ quasi-uniforme dans fenêtre, signal très fort [OBSERVÉ] | R62 |
| **D∞ < 0.10 pour p≥251** | Discrepancy basse, quasi-uniformité robuste avec p croissant [OBSERVÉ] | R62 |
| **Sommes |S|/q < 0.12** | Sommes de caractères bien sous-linéaires, outil Weil pertinent mais indirect [CALCULÉ] | R62 |
| **A(2) < 3.2 borné** | Sous ε=0.47, A(2)_théo < 3.2, A(2)_réel < 1.35, marge confortable [SEMI-FORMEL] | R62 |
| **Candidat 1 > Candidat 2 : 82 vs 61** | Dilution plus simple, ε plus large, mieux quantifié que Weil direct [CALCULÉ] | R62 |
| **Verrou final = équidistribution** | Tout réduit à D∞(d_δ)→0 en R3, outils : Erdős-Turán, Vinogradov, Bourgain-Konyagin [IDENTIFIÉ] | R62 |
| **D∞ observé décroît O(1/√p)** | mean D∞ : 0.100 (p=101) → 0.028 (p=1009), tendance claire [OBSERVÉ] | R63 |
| **D∞_ET optimal décroît** | 0.407→0.159 pour p=101→1009, asymptotique O(ln(p)/√p) [CALCULÉ] | R63 |
| **|S_h|/√p ≈ 0.50 universel** | Moyenne stable ~0.50 pour tous p testés, 100% sous 1.0 [OBSERVÉ] | R63 |
| **Arc = sous-groupe complet** | {g^0,g^2,...,g^{2M}} couvre exactement ⟨g²⟩ (fraction=1.0) [PROUVÉ] | R63 |
| **Candidat 1 ≫ Candidat 2 : 84 vs 39** | Analytique (Erdős-Turán) domine combinatoire (incidences) sur 10 critères [CALCULÉ] | R63 |
| **p_seuil = 4538** | Premier p tel que D∞ < 1/4 (margin confortable) sous borne Weil-like [CALCULÉ] | R63 |
| **Verrou R64 = |S_h| ≤ C·√p** | Unique pièce manquante : borne de type Weil sur Σχ(1+t) restreinte à ⟨g²⟩ [IDENTIFIÉ] | R63 |
| **|S_h| ≤ (1+√p)/2 PROUVÉ** | Décomposition exacte S_h=(A_h+B_h)/2, A_h=-1, |B_h|=√p via Jacobi [PROUVÉ] | R64 |
| **D∞ → 0 PROUVÉ** | Erdős-Turán + |S_h| ≤ (1+√p)/2 → D∞ = O(ln(p)/√p) [PROUVÉ] | R64 |
| **τ < 1 PROUVÉ** | Dilution 1/2 + D∞ → 0, τ < 1 pour p ≥ 37 [PROUVÉ] | R64 |
| **(c) FERMÉE** | Sous-étape (c) du schéma K-lite fermée pour p ≥ 37 en R3 [PROUVÉ] | R64 |
| **Candidat 1 ≫ Candidat 2 : 98 vs 51** | Standardisé vs résidu : preuve complète vs inutile [CALCULÉ] | R64 |
| **Ladder L8 atteint** | 3 niveaux montés en R64 : S_h, D∞, (c) tous à L8 lemme prouvé [PROUVÉ] | R64 |

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
| T68 | Phase shift : M₂(b₀,b₀') = #{(tail,tail') : T−T' ≡ Δ mod p}, Δ constante par paire [PROUVÉ] | R50 |
| T69 | Shift anti-symétrie + transitivité : Δ(i,j)+Δ(j,i)≡0, Δ(a,b)+Δ(b,c)≡Δ(a,c) [PROUVÉ] | R50 |
| T70 | Convolution : M₂ = Σ_r N^{tail}_{b₀,r} · N^{tail}_{b₀',r−Δ} (cross-corrélation décalée) [PROUVÉ] | R50 |
| T71 | Unification between-within : quasi-uniformité tail contrôle V ET Z simultanément [SEMI-FORMEL] | R50 |
| T72 | Régime α=4 : ord≥4·(max_B+1) ⟹ max\|ρ\|<0.4 (transition empirique, 188/188) [OBSERVÉ] | R50 |
| T73 | Identité rotation tail : N^{tail}_{b₀,r} = N^{std}_{r·(2^{b₀}·g)⁻¹ mod p} [PROUVÉ] | R51 |
| T74 | μ-invariance : μ^{tail}(b₀) = μ(k-1, [0, max_B−b₀], p) exactement [PROUVÉ] | R51 |
| T75 | TQL-mu : μ(b₀)−1 ≤ K·p/C_{b₀}, K=1.29 (R3) à 4.32 (global), 564/564 [OBSERVÉ] | R51 |
| T76 | Cascade A(k)≤A(k-1) RÉFUTÉE : p=5, A croît 0.8→17.0 monotonement [RÉFUTÉ] | R51 |
| T77 | Lemme A : μ(k) ≤ max_{b₀} μ(k-1, M−b₀, p), universel (50+/50+ cas) [OBSERVÉ] | R51 |
| T78 | V ≤ 1.42·C en R1 (232/232 cas R1+), borne V=O(C) dans tout sous-régime R1 [OBSERVÉ] | R52 |
| T79 | E_excess/C borné en R1 : \|E/C\| < 0.90, collisions excédentaires sous-linéaires [OBSERVÉ] | R52 |
| T80 | Cancellation cross-terms 75-88% en R1+ : interférence destructive effective [OBSERVÉ] | R52 |
| T81 | Horner donne 3.7-5.5× amélioration sur CS en R1 (gain structurel réel) [OBSERVÉ] | R52 |
| T82 | Fit μ−1 ≈ K·p/C, R²=0.909, K<1.42 en R1 : première borne quantitative [OBSERVÉ] | R52 |
| T83 | h=1 vacuous en R1 : ord_p(2) > max_B ⟹ ∄Δ valide, 0 collision h=1 [PROUVÉ] | R53 |
| T84 | E_excess < 0 en R1 : monotonie crée anti-concentration (sous-collisions systématiques) [OBSERVÉ] | R53 |
| T85 | Toutes collisions R1 ont h ≥ 2 (corollaire direct T83) [PROUVÉ] | R53 |
| T86 | Gini(collisions) décroît avec C : 0.575→0.152, collisions diffuses, pas de hub vectors [OBSERVÉ] | R53 |
| T87 | E_intra domine E_cross en R1 : 65-96% via dernière coordonnée fixée, induction viable [OBSERVÉ] | R53 |
| T88 | Contraction pondérée : Σ(C_b/C)²·μ(k-1,b,p)/μ(k,M,p) ∈ [0.51, 0.67], universelle 6/6 | R54 |
| T89 | Contraction pointwise RÉFUTÉE : max_b μ(sub) > μ(full) toujours (petites tranches C_b<<p) [RÉFUTÉ] | R54 |
| T90 | V_cross ≤ 0 typique : anti-corrélation inter-tranches, |V_cross/C| < 0.27, AIDE V_total [OBSERVÉ] | R54 |
| T91 | h=2 signature unique : B_a−B_b uniquement déterminé par poly constraint en R1 [CALCULÉ] | R54 |
| T92 | N_2 sub-simplex prediction exacte : 6/6 parfait, calculable sans énumération [CALCULÉ] | R54 |
| T93 | Dichotomie ANOVA : V_cross<0 ⟹ V≤V_within, V_cross>0 ⟹ ρ<1. Aucun régime ne donne les deux [OBSERVÉ] | R55 |
| T94 | |γ| = |V_cross/V_within| < 1 universellement : γ ∈ [-0.75, +0.39], 7/7 cas [OBSERVÉ] | R55 |
| T95 | Shift-invariance k=2 : P_{B+(1,1)} = 2g·P_B mod p, conséquence algébrique directe [PROUVÉ] | R55 |
| T96 | Base A(2) = V(2)/C(2) ≤ 1.22 en R1 (622 cas), mécanisme orbital identifié [OBSERVÉ] | R55 |
| T97 | Transport k=2→k≥3 via V_cross≤0 : fonctionne 79% (5/7 R1), échoue V_cross>0 [OBSERVÉ] | R55 |
| T98 | A(2) ≤ 2.28 en R1 (2931 cas), max A(générique)=1.89, max A(dégénéré g≡-1)=2.28 [OBSERVÉ] | R56 |
| T99 | Cas dégénéré g≡-1 : P_{(a,a)}=0 ∀a, N_0≥M+1, source UNIQUE de A>2 (9/2931=0.3%) [PROUVÉ] | R56 |
| T100 | Décomposition orbitale : N_r = N_r^{complet} + N_r^{incomplet}, complètes→V=0, R1→toutes incomplètes [PROUVÉ] | R56 |
| T101 | CS INSUFFISANT pour |γ|<1 : Jensen ⟹ θ_CS ≥ n-1 ≥ 1, CS ne peut prouver |γ|<1 [PROUVÉ] | R56 |
| T102 | Phase cancellation = 89% : |V_cross| utilise 11% du bound CS, rotation ω^{r·Δ} annule le reste [OBSERVÉ] | R56 |
| T103 | δ-reformulation : N_r = #{δ : dlog(r/c_δ) ∈ [0,M-δ]}, c_δ=(1+g·2^δ), identité algébrique exacte [PROUVÉ] | R57 |
| T104 | En R1, chaque δ contribue ≤1 solution, c_δ tous distincts, borne triviale N_r ≤ M+1 [PROUVÉ] | R57 |
| T105 | Récurrence c_{δ+1} = 2c_δ − 1 mod p : suite AFFINE, tous termes distincts en R1 [PROUVÉ] | R57 |
| T106 | Borne sub-triviale : max N_r ≤ C/p + 0.76·(M+1) en R1 générique, K < 1 strict [OBSERVÉ] | R57 |
| T107 | Identité bilinéaire : Z_{b,b'} = #{a+b≡a'+b' mod ord} − C_b·C_{b'}/p, forme bilinéaire exacte [PROUVÉ] | R57 |
| T108 | Σ_r N_r² ≤ max_r(N_r) · Σ_r N_r : inégalité algébrique directe (lien max → second moment) [PROUVÉ] | R58 |
| T109 | V_cross ≤ (max_r(N_r) − 1) · C : borne additive ⟹ contrôle cross automatique [PROUVÉ] | R58 |
| T110 | Candidat 1 (additive) contrôle base ET cross simultanément via T108-T109 [PROUVÉ] | R58 |
| T111 | Les dlogs de c_δ ne sont pas uniformes dans (Z/pZ)* : couverture 12-31% seulement [PROUVÉ] | R58 |
| T112 | Second moment ⟹ perte √p dans passage L²→L∞ : facteur 448× trop lâche, éliminé [PROUVÉ] | R58 |
| T113 | Contributions au max N_r dominées par petits δ : frac_low = 0.67 (|W_δ| décroissant) [PROUVÉ] | R59 |
| T114 | Large sieve non viable : borne (M+1)·(1+M/ord) ≥ M+1 toujours, pire que trivial [PROUVÉ] | R59 |
| T115 | Candidat 2 hybride strictement ≤ Candidat 1 pointwise : √V ≈ c·M, même échelle, pire constante [PROUVÉ] | R59 |
| T116 | Nesting : sauts rares dans suite des hits (≤ 1 par cas testé), emboîtement des fenêtres [OBSERVÉ] | R59 |
| T117 | Sous-régimes : α décroît R3 < R2 < R1 < global, hiérarchie cohérente avec aliasing [OBSERVÉ] | R59 |
| T118 | Bridge conditionnel : sous d_δ uniformes, Pr[α≥1] < 0.01% (1000 simulations) [OBSERVÉ] | R60 |
| T119 | Discrepancy pondérée : max_Dw = α·(M+1)/C, identité exacte reliant discrepancy à α [PROUVÉ] | R60 |
| T120 | Nesting borne : J_r ≤ 2M²/ord + 2, auxiliaire seulement [OBSERVÉ] | R60 |
| T121 | Candidat 1 domine Candidat 2 : score 49/60 vs 39/60, bridge-lite pointwise survit [CALCULÉ] | R60 |
| T122 | Chaîne globale K-lite → f_p → 1/p : K-lite ⟹ A(2) borné ⟹ V/C²→0 ⟹ f_p→1/p [SEMI-FORMEL] | R60 |
| T123 | Taux transition hit-hit : τ_moyen = 0.317, τ_max ≤ 0.53, ε ≥ 0.47 sur 4 primes [OBSERVÉ] | R61 |
| T124 | Décroissance géométrique des chaînes de hits : ρ ≈ 0.04, 96.5% longueur 1 [OBSERVÉ] | R61 |
| T125 | Géométrie fenêtres = facteur dominant : ratio τ_real/τ_random ≈ 0.96 [PROUVÉ] | R61 |
| T126 | Candidat 1 pointwise domine Candidat 2 chaînes courtes : 71 vs 68 /100 [CALCULÉ] | R61 |
| T127 | Chaîne globale (c)→(d)→K-lite→A(2)→f_p valide en R3 (20 cas) [SEMI-FORMEL] | R61 |
| T128 | Dilution géométrique : ε_dilution = (p+1)/(2(p−1)) → 1/2, formule exacte [PROUVÉ] | R62 |
| T129 | Quasi-uniformité d_δ : KS moyen = 0.017, D∞ < 0.10 pour p ≥ 251 [OBSERVÉ] | R62 |
| T130 | Sous-lemme ε>0 conditionnel : si D∞ < 1/2 alors τ ≤ 1/2 + D∞ < 1 [PROUVÉ CONDITIONNEL] | R62 |
| T131 | Candidat 1 dilution domine Candidat 2 Weil : 82 vs 61 /100 [CALCULÉ] | R62 |
| T132 | Chaîne globale A(2) < 3.2 borné sous ε = 0.47 [SEMI-FORMEL] | R62 |
| T133 | D∞(d_δ) décroît : mean 0.100→0.028 pour p=101→1009, tendance O(1/√p) [OBSERVÉ] | R63 |
| T134 | Erdős-Turán réduction : D∞ ≤ 1/H + (1/M)·Σ|S_h|/h, applicable et quantitatif [PROUVÉ] | R63 |
| T135 | Objet minimal : S_h = Σ χ_h(1+g^{2δ}) somme complète sur ⟨g²⟩, |S_h|/√p ≈ 0.50 [OBSERVÉ] | R63 |
| T136 | Gain carré-racine : |S_h|/(M+1) < 0.11, bien sous borne triviale [OBSERVÉ] | R63 |
| T137 | D∞_ET optimal = O(ln(p)/√p) → 0, sous |S_h| ≤ C·√p [SEMI-PROUVÉ] | R63 |
| T138 | Candidat 1 analytique domine Candidat 2 combinatoire : 84 vs 39 /100 [CALCULÉ] | R63 |
| T139 | Seuil pratique : p_seuil ≈ 4538 pour η < 1/4, marge confortable [CALCULÉ] | R63 |
| T140 | Décomposition exacte : S_h = (A_h + B_h)/2 via indicatrice (1+η)/2 de ⟨g²⟩ [PROUVÉ] | R64 |
| T141 | Orthogonalité : A_h = −1 pour χ_h non trivial [PROUVÉ] | R64 |
| T142 | Jacobi : B_h = η(−1)·J(η, χ_h), |J| = √p [PROUVÉ] | R64 |
| T143 | Borne racine carrée : |S_h| ≤ (1+√p)/2 pour h dans plage utile [PROUVÉ] | R64 |
| T144 | D∞ PROUVÉ : D∞ ≤ C·ln(p)/√p → 0, via Erdős-Turán + T143 [PROUVÉ] | R64 |
| T145 | Sous-étape (c) FERMÉE : τ < 1 pour p ≥ 37 en R3 [PROUVÉ] | R64 |
| T146 | Chaîne S_h→D∞→τ<1→ε>0→α<1 complète, p ≥ 37 [PROUVÉ] | R64 |

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
R50     : PHASE SHIFT = clé (Z = conv décalée), UNIFICATION between-within via TQL, Z-lite SURVIVANT R51 (T68-T72)
R51     : Tail = sous-problème rotaté [PROUVÉ], TQL-mu = premier noyau prouvable (K≤4.3), cascade RÉFUTÉE p=5 (T73-T77)
R52     : V≤1.42·C en R1 [OBSERVÉ], μ-lite collision SURVIVANT (E_excess/C<0.90), Horner 3.7-5.5× sur CS (T78-T82)
R53     : h=1 vacuous en R1 [PROUVÉ], E_excess<0, collisions diffuses, Min Hamming+poly = SURVIVANT R54 (T83-T87)
R54     : Poly vanishing=FRAGILE (h≥3 domine), INDUCTION l'emporte (contraction 0.51-0.67), Weighted V-bound = SURVIVANT R55 (T88-T92)
R55     : Récurrence universelle RÉFUTÉE (dichotomie ANOVA), base A(2)≤1.22 FORTE, shift-inv PROUVÉE, V_cross=vrai verrou, Base-lite+bootstrap = SURVIVANT R56 (T93-T97)
R56     : A(2) corrigé ≤2.28 (dégénéré g≡-1 PROUVÉ), CS INSUFFISANT [PROUVÉ Jensen], cancellation phases 89%, gap=max N_r, Base-lite+cross-lite = SURVIVANT R57 (T98-T102)
R57     : δ-reformulation PROUVÉE (6 faits), suite affine c_δ, borne sub-triviale K<1, identité bilinéaire Z PROUVÉE, cross-lite B cadré, Base+cross parallèles = SURVIVANT R58 (T103-T107)
R58     : Gap dlog FORMULÉ (canonique), 3 routes comparées (Route 2 fenêtres PRIORITAIRE), Candidat 1 additive SURVIVANT (K_lin<1 universel 92 cas), Candidat 2 second moment ÉLIMINÉ (perte √p), T108-T112 (additive⟹cross), Borne additive via large sieve = SURVIVANT R59
R59     : Barrier counting reformulation (δ+d_δ≤M), F4 α<1 SÉLECTIONNÉE (α_max=0.50), fenêtres=source principale (ratio 0.89), large sieve ÉLIMINÉ (≥M+1), Candidat 2 hybride ÉLIMINÉ (≤Candidat 1), Route 6 barrier counting PRIORITAIRE, Lemme K-lite Ladder 5/9, T113-T117 = SURVIVANT R60
R60     : Bridge décomposé A+B (géométrie barrière PROUVÉ + suite affine À PROUVER), discrepancy pondérée = bonne métrique (T119 PROUVÉ), preuve conditionnelle valide (<0.01%, T118), schéma 4 sous-étapes (2 prouvées, 2 conjecturales), Candidat 2 bridge+nesting ÉLIMINÉ (39/60), D∞ standard ÉLIMINÉ, nesting autonome ÉLIMINÉ, verrou = transition hit-hit < 1, T118-T122, Bridge-lite pointwise = SURVIVANT R61
R61     : Contrôle hit-hit FORMULÉ (τ<1−ε, ε≈c/log(ord)), Route 3 rareté SÉLECTIONNÉE (8/10), décroissance géométrique chaînes (ρ≈0.04), Candidat 1 pointwise SURVIVANT (71 vs 68), Route 2 multiplicatif ÉLIMINÉE, Candidat 2 chaînes ABSORBÉ, fenêtres=facteur dominant (0.96), verrou = quasi-uniformité d_δ, T123-T127, Hit-hit-lite pointwise = SURVIVANT R62
R62     : Dilution géométrique ε=1/2 PROUVÉ (formule exacte), quasi-uniformité d_δ OBSERVÉE (KS=0.017, D∞<0.10), sous-lemme ε>0 conditionnel PROUVÉ (τ≤1/2+D∞), Route 2 probabiliste SÉLECTIONNÉE (8/10), Route 1 fenêtres ÉLIMINÉE (ε→0), Weil direct ÉLIMINÉ (sous-groupe), Candidat 1 dilution SURVIVANT (82 vs 61), verrou final = équidistribution d_δ via Erdős-Turán, T128-T132, ε-lite dilution = SURVIVANT R63
R63     : Réduction Erdős-Turán PROUVÉE (D∞≤1/H+(1/M)Σ|S_h|/h), objet minimal IDENTIFIÉ (S_h=Σχ_h(1+g^{2δ}) sur ⟨g²⟩), |S_h|/√p≈0.50 universel, gain carré-racine OBSERVÉ (<0.11), D∞=O(ln(p)/√p)→0 SEMI-PROUVÉ, arc=sous-groupe complet PROUVÉ, Candidat 2 incidences ÉLIMINÉ (39/100, absorbé via Parseval), pseudo-aléa naïf ÉLIMINÉ, p_seuil≈4538, récurrence affine PROUVÉE, T133-T139, D∞-lite analytique Ladder L6 = SURVIVANT R64
R64     : **ROUND DÉCISIF** — |S_h|≤(1+√p)/2 **PROUVÉ** (décomposition exacte + orthogonalité + Jacobi), A_h=-1 PROUVÉ, |B_h|=√p PROUVÉ, D∞→0 PROUVÉ, τ<1 PROUVÉ, sous-étape (c) **FERMÉE** (p≥37, R3), Bourgain-Konyagin ÉLIMINÉ (inutile), Weil non décomposée ÉLIMINÉE, chaîne S_h→D∞→τ→ε→α COMPLÈTE, Ladder **L8**, T140-T146, Intégration (d) = SURVIVANT R65
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

- **Rounds** : 64
- **Scripts** : 216 (+2 en R64 : r64_sum_decomposition + r64_sh_lite)
- **Auto-tests** : 12066 (46 en R64 : 18 sum_decomposition + 28 sh_lite, 100% PASS)
- **Théorèmes prouvés** : 146 (originaux, +7 en R64 : T140-T146)
- **Conjectures ouvertes** : 15 (OD Bound, Ratio Law, PCMG, SPC unicité, OCC-LITE, κ=1, QEL, MSL, LSD, WEL, ACaL, |ρ|<1, TQL-mu, α<1 universel, Base+cross) — |S_h|≤C√p PROUVÉ et retiré
- **Pistes fermées** : 87 (documentées avec raison, +3 en R64)
- **Concepts inventés** : 169 (nommés, +7 en R64, dont |S_h|≤(1+√p)/2 PROUVÉ = Ladder L8)
- **Lean** : 280 théorèmes, 0 sorry
- **Gap restant** : 21 valeurs (k=21..41)
- **Route prioritaire** : Lemme K-lite — sous-étapes (a)(b)(c) PROUVÉES, reste (d) intégration α<1 SEMI-FORMEL + cas p<37 [LEMME CANDIDAT L7]
