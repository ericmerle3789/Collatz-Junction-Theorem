# INVENTAIRE COMPLET DU PROJET

**Projet:** Entropic Barriers and Nonsurjectivity in the 3x+1 Problem
**Auteur:** Eric Merle
**Date:** Mars 2026
**Fichiers:** 147 (hors .git)

---

## 1. Racine

| Fichier | Role |
|---------|------|
| `README.md` | Documentation principale |
| `INVENTAIRE.md` | Ce fichier |
| `LICENSE` | MIT (code) |
| `LICENSE-PAPER` | CC-BY 4.0 (paper) |
| `.gitignore` | Exclusions git |

## 2. Paper (`paper/`)

| Fichier | Description |
|---------|-------------|
| `preprint_en.tex` | Preprint anglais (principal, ~16 pages) |
| `preprint_fr.tex` | Preprint francais (version originale) |
| `preprint.md` | Version Markdown de reference |
| `Merle_2026_*.pdf` | PDF compile |

**Contenu du preprint (v3, mars 2026):**
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
- Proposition L13 : Effective Regime B Vacuity (57 primes, 0 dangerous)
- Proposition L14 : One Good Prime Suffices (CRT bypass, Regime B irrelevant)
- 3 conjectures ouvertes + chaine conditionnelle
- Formalisation Lean 4 (73+58 theoremes)

## 3. Lean (`lean/`)

### 3.1. Verified core (`lean/verified/`, Lean 4.15.0)

| Fichier | Contenu | sorry | axiom |
|---------|---------|:-----:|:-----:|
| `CollatzVerified/Basic.lean` | 73 theoremes | 0 | 0 |
| `CollatzVerified.lean` | Module root | — | — |
| `Main.lean` | Entry point | — | — |
| `lakefile.toml` | Config Lake | — | — |
| `lean-toolchain` | Lean 4.15.0 | — | — |

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

### 4.2. Exploration (`scripts/exploration/`, 46 scripts, Phases 20-22 + SP6-SP10 + A1-A2+-B3-C-D-E)

Scripts de recherche exploratoire.

| Script | Phase | Contenu |
|--------|:-----:|---------|
| `phase20_crt_analysis.py` | 20 | Analyse CRT hybride |
| `phase20_mixing_simulation.py` | 20 | Simulation mixing |
| `phase20_type_classification.py` | 20b | Classification Type I/II |
| `phase21_convergent_asymptotics.py` | 21 | Asymptotiques convergents |
| `phase21_crt_synergy.py` | 21 | Synergie CRT |
| `phase21_decay_analysis.py` | 21 | Analyse de decroissance |
| `phase21_divisibility_obstruction.py` | 21 | Obstruction divisibilite |
| `phase21_mellin_spectral.py` | 21 | Mellin spectral |
| `phase21_multilinear.py` | 21 | Analyse multilineaire |
| `phase21_proof_construction.py` | 21 | Construction preuve |
| `phase21_second_moment.py` | 21 | Second moment |
| `phase21_voie_b_arithmetic.py` | 21 | Voie B arithmetique |
| `phase22_crt_amplification.py` | 22 | Amplification CRT |
| `phase22_exploration.py` | 22 | Exploration generale |
| `phase22_gap_verification.py` | 22 | Verification gap |
| `phase22_largest_prime_mechanism.py` | 22 | Mecanisme plus grand premier |
| `phase22_spectral_bound.py` | 22 | Borne spectrale |
| `sp6_ghost_fish.py` | SP6 | Ghost Fish (17 primes dures) |
| `sp6_ghost_fish_large.py` | SP6 | Ghost Fish LARGE (p > 10^6) |
| `sp6_tunnel_factors.py` | SP6 | Tunnel : ord_p(2) des facteurs de d(k) |
| `sp6_three_mesh_net.py` | SP6 | Filet a trois mailles (168 primes, 0 echecs) |
| `sp6_mersenne_direct.py` | SP6 | Verification directe Mersenne (q <= 127) |
| `sp7_kmax.py` | SP7 | K_MAX = 63 (jonction overlap [63,68]) |
| `sp7_rho_precise.py` | SP7 | Calcul precis de rho (arithmetique modulaire) |
| `sp7_ghost_fish_danger.py` | SP7 | Fish-Tunnel Incompatibility (11 primes danger) |
| `sp7_gap_scan.py` | SP7 | Scan exhaustif d(k) pour k in [69,120] |
| `sp8_fish_nature.py` | SP8 | Nature des poissons dans d(k), k in [69,300] (vectorise) |
| `sp8_fish_tunnel_analysis.py` | SP8 | Analyse theorique mecanisme Fish-Tunnel |
| `sp9_scan_v3.py` | SP9 | Scan k ∈ [69,500], trial division d(k), 541 primes |
| `sp9_mpmath_new_worst.py` | SP9 | Verification mpmath 50 decimales des pires cas SP9 |
| `sp9_d26_analysis.py` | SP9 | Analyse D26/D28, contrainte divisibilite reduite |
| `sp9_voie4_bypass.py` | SP9 | Voie 4 bypass arithmetique (dead end confirme) |
| `sp10_level8_phase1_final.py` | SP10 | Phase I verification (Q) k=69..500 (local+CI) |
| `sp10_level8_debug_fail.py` | SP10 | Debug des faux positifs Phase I (p=31, p=257) |
| `sp10_level9_baker_matveev.py` | SP10 | Piste 2: Baker-Matveev (v_p toujours petit) |
| `sp10_level9_counting.py` | SP10 | Piste 1: Comptage via structure ⟨2⟩ + Beatty |
| `sp10_level9_beatty_formal.py` | SP10 | Formalisation Beatty + Trois Distances |
| `sp10_level9_n3_corrected.py` | SP10 | Investigation n₃ CORRIGEE (regime B vide) |
| `phase_a1_exhaustive_k18_25.py` | A1 | Verification exhaustive DP k=18..25 |
| `phase_a2_regime_b_extension.py` | A2 | Classification Regime A/B k=18..67 (165 premiers) |
| `phase_a2plus_ecm_cofactors.py` | A2+ | Factorisation ECM 12 cofacteurs (25 premiers) |
| `phase_b3_PU_verify.py` | B3 | Verification Proportion Uniformity (22 paires) |
| `phase_c_structural_proof.py` | C | Census Regime B (m≤300) + analyse structurelle (5 analyses) |
| `phase_c_regime_b_hunt.py` | C | Chasse Regime B 4 routes (classification, enumeration, non-divisibilite, structure) |
| `phase_d_formal_proof.py` | D | Theoreme formel + synthese (Proposition L13) |
| `phase_e_one_good_prime.py` | E | CRT bypass : One Good Prime Suffices (Proposition L14) |

## 5. Research Log (`research_log/`, 48 fichiers)

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

| Fichier | Resultats cles |
|---------|----------------|
| `phase20_synthese_4_pistes.md` | Diagnostic unifie : tout mene aux sommes lacunaires |
| `phase20a_piste_CRT_hybride.md` | Piste CRT hybride |
| `phase20b_piste_structure_algebrique.md` | Classification Type I/II des premiers |
| `phase20c_piste_mixing_random_walk.md` | Gaps spectraux quantifies |
| `phase20d_piste_extension_tao.md` | Extension Tao ecartee (resultat negatif) |
| `phase21_mellin_mater_mboup.md` | corrSum impair (R6), corrSum non div. par 3 (R7) |
| `phase22_borne_lacunaire_CRT.md` | N0(d)=0 pour k=3..17 (R4), Conjecture 22.3 |
| `phase23_formule_verdict.md` | Analyse de defaillance systematique |
| `phase23b_assemblage_formule.md` | Barriere racine carree (R5) |
| `phase23c_au_dela_barriere.md` | 3 voies de contournement |
| `phase23d_epluchage_et_theoreme.md` | Peeling Lemma (R1), Theorem Q (C1) |
| `phase23e_annulation_mutuelle.md` | Conjectures Delta', PU, chaine conditionnelle |
| `phase23f_energie_additive_melange.md` | E4(H) quasi-Sidon (R2), parcimonie (R3) |

### Corrections

| Fichier | Contenu |
|---------|---------|
| `ERRATA.md` | Corrections aux valeurs du research log |
| `sp5_investigation.md` | Investigation SP5 : Condition (Q) via GPS |
| `sp6_ghost_fish.md` | Investigation SP6 : Ghost Fish + filet 3 mailles (4/5) |
| `sp7_junction_geology.md` | Investigation SP7 : Geologie de jonction (4.75/5) |
| `sp8_fish_nature.md` | Investigation SP8 : Nature des poissons (4.85/5) |
| `sp9_formalization_and_extension.md` | Investigation SP9 : Extension k→500, D28-D30, Voie 4 (4.85/5) |
| `sp10_motor_b2_investigation.md` | Investigation SP10 : Condition (Q) analysis L1-L9 (80K+ mots) |
| `sp10_synthese_formelle.md` | SP10 : Synthese formelle — propositions et architecture de preuve |
| `phase_a1_resultats.tmp.md` | Phase A1 : resultats verification exhaustive k=18..25 |
| `phase_a2_resultats.tmp.md` | Phase A2 : classification Regime A/B k=18..67 (0/165 Regime B) |
| `phase_a2plus_resultats.tmp.md` | Phase A2+ : ECM 12 cofacteurs, 25 nouveaux premiers (tous Regime A) |
| `phase_b3_resultats.tmp.md` | Phase B3 : Proportion Uniformity (ratio=0.999, P(pi0=0)=0) |
| `synthese_gap_closure.tmp.md` | Synthese complete fermeture du gap k=18..67 |

## 6. Audits (`audits/`, 4 fichiers)

| Version | Resultat | Niveau |
|---------|----------|--------|
| V1 | Certification refusee (blocages identifies) | Post-doctoral |
| V2 | Nouveau blocage identifie | Ultra-severe |
| V3 | Certifie (tous blocages resolus) | DO-178C / IEC 61508 / EAL7 |
| V4 | Verification mathematique chaine logique | Pur mathematique |

## 7. Documentation (`docs/`)

| Fichier | Contenu |
|---------|---------|
| `plans/2026-02-27-phase20-4-pistes-design.md` | Design document Phase 20 |

## 8. CI/CD (`.github/workflows/`)

| Fichier | Action |
|---------|--------|
| `lean-check.yml` | Verification automatique : 0 sorry, 0 axiom supplementaire |
| `sp10-phase1.yml` | SP10 Phase I: verification Condition (Q) k=69..500 |

---

## Resultats par statut

### Inconditionnels (dans le preprint)

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

### Conjectures ouvertes (mentionnees en S9.2)

| Conjecture | Enonce |
|------------|--------|
| 22.3 | Equidistribution de Horner |
| Delta' | Gap spectral fort |
| PU | Proportion uniforme |
