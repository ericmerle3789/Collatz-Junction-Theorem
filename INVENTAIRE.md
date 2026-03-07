# INVENTAIRE COMPLET DU PROJET

**Projet:** Nonexistence of Nontrivial Cycles in Collatz Dynamics
**Auteur:** Eric Merle
**Date:** Mars 2026
**Fichiers:** ~260 (hors .git, __pycache__, .DS_Store)

---

## 1. Racine

| Fichier | Role |
|---------|------|
| `README.md` | Documentation principale |
| `INVENTAIRE.md` | Ce fichier |
| `LICENSE` | MIT (code) |
| `LICENSE-PAPER` | CC-BY 4.0 (paper) |
| `.gitignore` | Exclusions git |
| `META_PROMPT_SESSION.md` | Meta-prompt session initiale |
| `META_PROMPT_SESSION_NEXT.md` | Meta-prompt continuation (mars 2026) |

## 2. Paper (`paper/`, 9 fichiers)

| Fichier | Description |
|---------|-------------|
| `preprint_en.tex` | Preprint anglais (principal) |
| `preprint_fr.tex` | Preprint francais (version originale) |
| `preprint.md` | Version Markdown de reference |
| `Merle_2026_*.pdf` | PDF compile |
| `preprint_en.{aux,log,out,toc,pdf}` | Fichiers de compilation LaTeX |

**Contenu du preprint :**
- Steiner's equation + proprietes arithmetiques de corrSum (R6/R7)
- Deficit entropique + nonsurjectivite (Theorem 1)
- Junction Theorem (Theorem 2)
- Obstruction analytique (Parseval, CRT)
- Mellin--Fourier bridge
- Peeling Lemma (R1) + Conjecture M
- Square Root Barrier (R5)
- Verification numerique N0(d)=0 pour k=3..17 (R4)
- Theorem Q conditionnel (C1)
- Filet a trois mailles (SP6) : 168 primes, 0 echecs
- Ghost Fish + Deux Barrieres (SP6) : Mersenne q <= 127
- Geologie de jonction (SP7) : K_MAX=63, Fish-Tunnel Incompatibility
- Proposition L13 : Effective Regime B Vacuity
- Proposition L14 : One Good Prime Suffices
- **A mettre a jour** : sessions 10b-10f20 (Blocking Mechanism)
- 3 conjectures ouvertes + chaine conditionnelle
- Formalisation Lean 4 (73+58 theoremes)

## 3. Lean (`lean/`, 19 fichiers)

### 3.1. Verified core (`lean/verified/`, Lean 4.15.0)

| Fichier | Contenu | sorry | axiom |
|---------|---------|:-----:|:-----:|
| `CollatzVerified/Basic.lean` | 73 theoremes | 0 | 0 |
| `CollatzVerified.lean` | Module root | — | — |
| `Main.lean` | Entry point | — | — |
| `lakefile.toml` | Config Lake | — | — |
| `lean-toolchain` | Lean 4.15.0 | — | — |
| `README.md` | Documentation | — | — |
| `.github/workflows/lean_action_ci.yml` | CI local | — | — |
| `.gitignore` | Exclusions | — | — |
| `lake-manifest.json` | Dependances | — | — |

Couverture : nonsurjectivite k=18-25, zero-exclusion q3, Gersonides, parite, cosets, Parseval, CRT, Mellin radar.

### 3.2. Research skeleton (`lean/skeleton/`, Lean 4.29.0-rc2 + Mathlib4)

| Fichier | Contenu | sorry | axiom |
|---------|---------|:-----:|:-----:|
| `JunctionTheorem.lean` | Junction Theorem | 1* | 1** |
| `SyracuseHeight.lean` | Hauteur Syracuse | 0 | 0 |
| `BinomialEntropy.lean` | Bornes entropie | 0 | 0 |
| `EntropyBound.lean` | Entropie tangente | 0 | 0 |
| `ConcaveTangent.lean` | Inegalite tangente | 0 | 0 |
| `LegendreApprox.lean` | Contrap. Legendre | 0 | 0 |
| `FiniteCases.lean` | k in [18,200] | 0 | 0 |

\* sorry residuel : `crystal_nonsurjectivity` pour k >= 201 (verifie numeriquement a k = 10^6).
\** axiome : Simons-de Weger (resultat publie, Acta Arith. 2005).

### 3.3. Configuration

| Fichier | Role |
|---------|------|
| `lakefile.lean` | Mathlib pinnee a v4.29.0-rc2 |
| `lean-toolchain` | Lean 4.29.0-rc2 |
| `lake-manifest.json` | Dependances resolues |

## 4. Scripts

### 4.1. Core (`scripts/core/`, 10 scripts, Phases 14-19 + SP5)

Scripts publies, verifies, associes au preprint.

| Script | Phase | Contenu |
|--------|:-----:|---------|
| `verify_nonsurjectivity.py` | — | Theorem 1 pour k in [18, 500] |
| `multidimensional_mold.py` | 14 | Obstruction multidimensionnelle |
| `interdimensional_tension.py` | 15 | Rigidite cosets + zero-exclusion |
| `analytical_obstruction.py` | 16 | Sommes de caracteres + Parseval |
| `keyhole_geometry.py` | 17 | Geometrie p-adique + Newton |
| `programme_merle.py` | 18 | Assemblage Programme Merle |
| `radar_mellin.py` | 19 | Radar Mellin multiplicatif |
| `verify_condition_q.py` | SP5 | Condition (Q) pour k in [18, 28] |
| `stress_test.py` | — | 402 tests de robustesse |
| `numerical_audit.py` | — | 152 verifications numeriques |

### 4.2. Exploration (`scripts/exploration/`, 81 scripts, Phases 20-22 + SP6-SP10 + A-F)

Scripts de recherche exploratoire (approche entropique).

| Script | Phase | Contenu |
|--------|:-----:|---------|
| `phase20_crt_analysis.py` | 20 | Analyse CRT hybride |
| `phase20_mixing_simulation.py` | 20 | Simulation mixing |
| `phase20_type_classification.py` | 20b | Classification Type I/II |
| `phase21_*.py` (9 scripts) | 21 | Mellin spectral, CRT, decroissance, multilineaire |
| `phase22_*.py` (5 scripts) | 22 | CRT amplification, bornes spectrales |
| `sp6_*.py` (5 scripts) | SP6 | Ghost Fish, filet 3 mailles, Mersenne, tunnel |
| `sp7_*.py` (4 scripts) | SP7 | K_MAX, rho precis, Fish-Tunnel danger, gap scan |
| `sp8_*.py` (2 scripts) | SP8 | Nature des poissons, analyse Fish-Tunnel |
| `sp9_*.py` (4 scripts) | SP9 | Scan k→500, mpmath, D26/D28, Voie 4 |
| `sp10_*.py` (33 scripts) | SP10 | Condition (Q) L1-L13, Beatty, regimes A/B |
| `phase_a1_exhaustive_k18_25.py` | A1 | Verification exhaustive DP k=18..25 |
| `phase_a2_regime_b_extension.py` | A2 | Classification Regime A/B k=18..67 |
| `phase_a2plus_ecm_cofactors.py` | A2+ | Factorisation ECM 12 cofacteurs |
| `phase_b1_energy_E8.py` | B1 | Energie E8 |
| `phase_b2_weyl_analysis.py` | B2 | Analyse de Weyl |
| `phase_b3_PU_verify.py` | B3 | Verification Proportion Uniformity |
| `phase_c_*.py` (2 scripts) | C | Census Regime B + chasse 4 routes |
| `phase_d_formal_proof.py` | D | Theoreme formel (Proposition L13) |
| `phase_e_one_good_prime.py` | E | CRT bypass (Proposition L14) |
| `phase_f_*.py` (2 scripts) | F | Deep dive + extension k=19-21 |

### 4.3. Tools (`scripts/tools/`, 70 scripts + 6 logs, Sessions 7-10f20)

Scripts de recherche sur le mecanisme de blocage.

| Script | Session | Contenu |
|--------|:-------:|---------|
| **Session 7-9 (fondations)** | | |
| `session7_scratch.md` | 7 | Cahier de brouillon session 7 |
| `session8_*.py` (5 scripts) | 8 | Baker, SAT/SMT, blocking prime |
| `session8_scratch.md` | 8 | Cahier de brouillon session 8 |
| `session9_*.py` (5 scripts) | 9 | CRT anti-correlation, target -1 |
| `session9_scratch.md` | 9 | Cahier de brouillon session 9 |
| **Session 10 (pre-10b)** | | |
| `session10_*.py` (2 scripts) | 10 | General prime blocking, protocol |
| `session10_protocol_research.md` | 10 | Protocole de recherche |
| **Sessions 10b-10d** | | |
| `session10b_contradiction_approach.py` | 10b | Approche contradiction |
| `session10b_scratch.md` | 10b | **Cahier principal (R1-R79)** |
| `session10c_exclusion_chain.py` | 10c | Chaine d'exclusion |
| `session10d_mechanism_II_crt.py` | 10d | Mecanisme II CRT |
| `session10d_scratch.md` | 10d | Cahier session 10d |
| **Sessions 10e-10e4** | | |
| `session10e_filtration_proof.py` | 10e | Preuve filtration |
| `session10e2_backward_chain_universal.py` | 10e2 | Backward chain universelle |
| `session10e3_algebraic_proof.py` | 10e3 | Preuve algebrique debordement |
| `session10e4_universal_sigma0.py` | 10e4 | sigma_tilde=0 universel |
| **Sessions 10f1-10f6** | | |
| `session10f_overflow_universal.py` | 10f1 | Overflow universel |
| `session10f2_structural_argument.py` | 10f2 | Argument structural |
| `session10f3_cascade_contradiction.py` | 10f3 | Cascade contradiction |
| `session10f4_algebraic_boundary.py` | 10f4 | Boundary algebrique |
| `session10f5_band_structure.py` | 10f5 | Structure de bandes |
| `session10f6_universal_directions.py` | 10f6 | Directions universelles |
| **Sessions 10f7-10f8b** | | |
| `session10f7_crt_mechanism2.py` | 10f7 | CRT anti-correlation etendue |
| `session10f8_dp_large_k.py` | 10f8 | DP grands k |
| `session10f8b_dp_optimized.py` | 10f8b | DP optimisee (k<=67) |
| **Sessions 10f9-10f12 (induction)** | | |
| `session10f9_theoretical_framework.py` | 10f9 | Framework theorique unifie |
| `session10f10_uniform_arguments.py` | 10f10 | Arguments uniformes |
| `session10f11_gap2_iminterior.py` | 10f11 | Im_interior ×2-clos |
| `session10f12_double_border_induction.py` | 10f12 | **Induction 4 cas** |
| **Sessions 10f13-10f15 (polynome)** | | |
| `session10f13_target_nonzero_proof.py` | 10f13 | **Polynome F(u)** |
| `session10f14_size_argument.py` | 10f14 | Argument de taille C/d→0 |
| `session10f15_lean_ready_formulation.py` | 10f15 | Formulation Lean-ready |
| **Sessions 10f16-10f17 (gaps)** | | |
| `session10f16_conjectures_attack.py` | 10f16 | Attaque des 4 gaps |
| `session10f16b_remaining.py` | 10f16b | Gaps residuels |
| `session10f17_squarefree.py` | 10f17 | Investigation squarefree |
| `session10f17b_squarefree_fast.py` | 10f17b | Squarefree rapide |
| `session10f17c_fz_mod_p.py` | 10f17c | F_Z mod p coprimite locale |
| `session10f17d_extended_verif.py` | 10f17d | Verification etendue |
| **Session 10f18 (G2a)** | | |
| `session10f18_g2a_theory.py` | 10f18a | Theorie G2a, periodes T_F/T_d |
| `session10f18b_critical_density.py` | 10f18b | Densite premiers critiques |
| `session10f18c_extended_final.py` | 10f18c | **F_Z mod d ≠ 0 pour k≤10001** |
| **Session 10f19 (G2c)** | | |
| `session10f19_g2c_attack.py` | 10f19a | Attaque G2c initiale |
| `session10f19b_g2c_fast.py` | 10f19b | **2^C mod d ≠ 1 (19 d prem.)** |
| **Session 10f20 (G2c inconditionnel)** | | |
| `session10f20_g2c_unconditional.py` | 10f20 | ord>S prouve, gap S→C |
| **Outils generaux** | | |
| `front1_*.py` (3 scripts) | — | Mecanisme de blocage, k=5 |
| `front2_spectral_analysis.py` | — | Analyse spectrale |
| `front4_invariants.py` | — | Invariants corrSum |
| `character_sum_analysis.py` | — | Sommes de caracteres |
| `counting_bound_approach.py` | — | Bornes de comptage |
| `double_peeling_proof.py` | — | Double peeling |
| `drift_formalization.py` | — | Formalisation drift |
| `enonce_c_*.py` (2 scripts) | — | Investigation enonce C |
| `formal_statements.py` | — | Enonces formels |
| `horner_drift_theorem.py` | — | Theoreme drift Horner |
| `obstruction_search.py` | — | Recherche obstructions |
| `ordered_backward_automaton.py` | — | Automate backward ordonne |
| `phantom_position_test.py` | — | Test positions fantomes |
| `position_incompatibility_analysis.py` | — | Analyse incompatibilite |
| `prime_factor_obstruction.py` | — | Obstruction facteurs premiers |
| `regression_test.py` | — | Tests de regression |
| `spectral_ordered_automaton.py` | — | Automate ordonne spectral |
| `test_small_k.py` | — | Test petits k |
| `theorem82_ord_proof.py` | — | Preuve ord theoreme 8.2 |
| `weight_asymmetry_proof.py` | — | Asymetrie des poids |
| `why_c0_equals_1.py` | — | Pourquoi c_0 = 1 |

## 5. Research Protocol (`research_protocol/`, 5 fichiers)

| Fichier | Contenu |
|---------|---------|
| `BLOCKING_MECHANISM_PROOF_SKETCH.md` | **Esquisse de preuve v0.15** (22 sections) |
| `DISCOVERY_PROTOCOL.md` | Protocole de recherche v2.2 |
| `MIND_MAP.md` | Carte mentale des dependances |
| `session6_research_log.md` | Journal session 6 |
| `session7_research_log.md` | Journal session 7 |

## 6. Research Log (`research_log/`, 56 fichiers)

### Fondations (Phases 10-13)

| Fichier | Contenu |
|---------|---------|
| `phase10c_red_team.md` | Red team analysis |
| `phase10d_reflexion_profonde.md` | Deep reflection |
| `phase10e_synthese_finale.md` | Final synthesis |
| `phase10f_audit_gouzel.md` | Gouzel-style audit |
| `phase10g_hauteur_syracuse.md` | Syracuse height |
| `phase10h_assaut_infini.md` | Infinite assault |
| `phase10i_cisaillement_diophantien.md` | Diophantine shearing |
| `phase10j_dissonance_resonance.md` | Dissonance/resonance |
| `phase10k_estocade.md` | Estocade |
| `phase10l_choc_des_cristaux.md` | Crystal clash |
| `phase10m_theoreme_fondamental.md` | Fundamental theorem |
| `phase11a_obstruction_algebrique.md` | Algebraic obstruction |
| `phase11b_verification_computationnelle.md` | Computational verification |
| `phase11c_reduction_lll.md` | LLL reduction |
| `phase12_junction_theorem.md` | Junction Theorem |
| `phase13_audit_kolmogorov_baker.md` | Rejected attempt (honest audit) |

### Developpement analytique (Phases 14-19)

| Fichier | Contenu |
|---------|---------|
| `phase14_moule_multidimensionnel.md` | Multidimensional mold |
| `phase15_tension_interdimensionnelle.md` | Inter-dimensional tension |
| `phase16_obstruction_analytique.md` | Analytical obstruction |
| `phase17_geometrie_serrure.md` | Keyhole geometry |
| `phase18_programme_merle.md` | Programme Merle assembly |
| `phase19_radar_mellin.md` | Mellin radar |

### Exploration avancee (Phases 20-23)

| Fichier | Contenu |
|---------|---------|
| `phase20_synthese_4_pistes.md` | Diagnostic unifie : tout mene aux sommes lacunaires |
| `phase20a_piste_CRT_hybride.md` | Piste CRT hybride |
| `phase20b_piste_structure_algebrique.md` | Classification Type I/II des premiers |
| `phase20c_piste_mixing_random_walk.md` | Gaps spectraux quantifies |
| `phase20d_piste_extension_tao.md` | Extension Tao ecartee (resultat negatif) |
| `phase21_mellin_mater_mboup.md` | corrSum impair (R6), non div. par 3 (R7) |
| `phase22_borne_lacunaire_CRT.md` | N0(d)=0 pour k=3..17 (R4), Conjecture 22.3 |
| `phase23_formule_verdict.md` | Analyse de defaillance systematique |
| `phase23b_assemblage_formule.md` | Barriere racine carree (R5) |
| `phase23c_au_dela_barriere.md` | 3 voies de contournement |
| `phase23d_epluchage_et_theoreme.md` | Peeling Lemma (R1), Theorem Q (C1) |
| `phase23e_annulation_mutuelle.md` | Conjectures Delta', PU, chaine conditionnelle |
| `phase23f_energie_additive_melange.md` | E4(H) quasi-Sidon (R2), parcimonie (R3) |

### Investigations SP5-SP10

| Fichier | Contenu |
|---------|---------|
| `sp5_investigation.md` | Investigation SP5 : Condition (Q) via GPS |
| `sp6_ghost_fish.md` | Investigation SP6 : Ghost Fish + filet 3 mailles (4/5) |
| `sp7_junction_geology.md` | Investigation SP7 : Geologie de jonction (4.75/5) |
| `sp8_fish_nature.md` | Investigation SP8 : Nature des poissons (4.85/5) |
| `sp9_formalization_and_extension.md` | Investigation SP9 : Extension k→500, D28-D30 (4.85/5) |
| `sp10_motor_b2_investigation.md` | Investigation SP10 : Condition (Q) analysis L1-L9 |
| `sp10_synthese_formelle.md` | SP10 : Synthese formelle — propositions et architecture |
| `sp10_level10_correction_cascade.md` | SP10 L10 : correction cascade BGK |
| `sp10_level11_structural.md` | SP10 L11 : structural analysis |
| `sp10_level12_effectivisation.md` | SP10 L12 : effectivisation |

### Resultats temporaires et syntheses

| Fichier | Contenu |
|---------|---------|
| `phase_a1_resultats.tmp.md` | Phase A1 : verification exhaustive k=18..25 |
| `phase_a2_resultats.tmp.md` | Phase A2 : classification k=18..67 (0/165 Regime B) |
| `phase_a2plus_resultats.tmp.md` | Phase A2+ : ECM 12 cofacteurs, 25 premiers |
| `phase_b1_resultats.tmp.md` | Phase B1 : energie E8 |
| `phase_b2_resultats.tmp.md` | Phase B2 : analyse Weyl |
| `phase_b3_resultats.tmp.md` | Phase B3 : Proportion Uniformity |
| `sp10_l12_exploration.tmp.md` | SP10 L12 : exploration |
| `sp10_l13_exploration.tmp.md` | SP10 L13 : exploration |
| `synthese_gap_closure.tmp.md` | Synthese complete fermeture du gap k=18..67 |
| `carte_mentale_exhaustive.tmp.md` | Carte mentale exhaustive |

### Corrections

| Fichier | Contenu |
|---------|---------|
| `ERRATA.md` | Corrections aux valeurs du research log |

## 7. Audits (`audits/`, 4 fichiers)

| Version | Resultat | Niveau |
|---------|----------|--------|
| V1 | Certification refusee (blocages identifies) | Post-doctoral |
| V2 | Nouveau blocage identifie | Ultra-severe |
| V3 | Certifie (tous blocages resolus) | DO-178C / IEC 61508 / EAL7 |
| V4 | Verification mathematique chaine logique | Pur mathematique |

## 8. Documentation (`docs/`)

| Fichier | Contenu |
|---------|---------|
| `plans/2026-02-27-phase20-4-pistes-design.md` | Design document Phase 20 |
| `plans/2026-03-03-gap-closure-design.md` | Design document fermeture gap |

## 9. CI/CD (`.github/workflows/`)

| Fichier | Action |
|---------|--------|
| `lean-check.yml` | Verification automatique : 0 sorry, 0 axiom supplementaire |
| `sp10-phase1.yml` | SP10 Phase I: verification Condition (Q) k=69..500 |

---

## Resultats par statut

### Resultats majeurs (Blocking Mechanism, sessions 10b-10f20)

| # | Resultat | Session |
|---|---------|:-------:|
| — | Induction 4 cas : interior + border + double-border | 10f12 |
| — | Im_interior ×2-clos | 10f11 |
| — | Polynome F(u) : annulation double-bord | 10f13 |
| — | F_Z mod d ≠ 0 pour k ≤ 10001 | 10f18c |
| — | 8 premiers critiques, densite → 0 | 10f18b |
| — | CRT inequality N₀(d) ≤ N₀(p) | 10d |
| — | DP exhaustive N₀(d) = 0 pour k ≤ 67 | 10f8b |
| — | ord_d(2) > C pour 19 d premiers | 10f19b |
| — | C/d → 0 prouve (Stirling + entropie) | 10f14 |
| — | **G2c sous GRH** : Hooley (1967) | 10f19 |
| — | ord_d(2) > S prouve (k ≥ 4) | 10f20 |

### Inconditionnels (approche entropique, dans le preprint)

| # | Resultat | Section |
|---|---------|:-------:|
| R1 | Peeling Lemma : N0(p) <= 0.63C | S7.2 |
| R4 | N0(d) = 0 pour k=3..17 | S8.2 |
| R5 | Barriere racine carree | S7.4 |
| R6 | corrSum toujours impair | S2.1 |
| R7 | corrSum jamais divisible par 3 | S2.1 |

### Conditionnels (dans le preprint)

| # | Resultat | Section |
|---|---------|:-------:|
| C1 | Theorem Q : |sigma T| <= 0.041C => pas de cycles | S9.1 |

### Reserves pour papier 2 (dans research_log uniquement)

| # | Resultat | Source |
|---|---------|--------|
| R2 | E4(H) = 2S^2 - S + O(S log S), H quasi-Sidon | phase23f |
| R3 | Parcimonie |{u : |G(u)| >= alphaS}| | phase23f |

### Conjectures ouvertes

| Conjecture | Enonce | Statut |
|------------|--------|--------|
| G2c | ord_d(2) > C pour d = 2^S - 3^k premier | **Resolu sous GRH** |
| G2a | F(u) ≠ 0 mod d pour tout k | Quasi-resolu (8 p critiques) |
| G1 | sigma_tilde = 0 seulement pour k=3,5 | Quasi-clos (Zsygmondy + verif k≤499) |
| G3 | CRT anti-correlation d compose pour k≥68 | Extrapole (verifie k≤67) |
| 22.3 | Equidistribution de Horner | Ouvert |
| Delta' | Gap spectral fort | Ouvert |
| PU | Proportion uniforme | Ouvert |
