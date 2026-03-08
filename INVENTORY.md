# COMPLETE PROJECT INVENTORY

**Project:** Nonexistence of Nontrivial Cycles in Collatz Dynamics
**Author:** Eric Merle
**Date:** March 2026
**Files:** ~270 (excluding .git, __pycache__, .DS_Store)

---

## 1. Root

| File | Role |
|------|------|
| `README.md` | Main documentation |
| `INVENTORY.md` | This file |
| `LICENSE` | MIT (code) |
| `LICENSE-PAPER` | CC-BY 4.0 (paper) |
| `.gitignore` | Git exclusions |
| `META_PROMPT_SESSION.md` | Initial session meta-prompt (internal) |
| `META_PROMPT_SESSION_NEXT.md` | Continuation meta-prompt (internal) |

## 2. Paper (`paper/`, 9 files)

| File | Description |
|------|-------------|
| `preprint_en.tex` | English preprint (principal) |
| `preprint_fr.tex` | French preprint (original version) |
| `preprint.md` | Markdown reference version |
| `Merle_2026_*.pdf` | Compiled PDF |
| `preprint_en.{aux,log,out,toc,pdf}` | LaTeX compilation files |

**Preprint contents:**
- Steiner's equation + arithmetic properties of corrSum (R6/R7)
- Entropic deficit + nonsurjectivity (Theorem 1)
- Junction Theorem (Theorem 2)
- Analytical obstruction (Parseval, CRT)
- Mellin--Fourier bridge
- Peeling Lemma (R1) + Conjecture M
- Square Root Barrier (R5)
- Numerical verification N0(d)=0 for k=3..17 (R4)
- Conditional Theorem Q (C1)
- Three-mesh net (SP6): 168 primes, 0 failures
- Ghost Fish + Two Barriers (SP6): Mersenne q <= 127
- Junction geology (SP7): K_MAX=63, Fish-Tunnel Incompatibility
- Proposition L13: Effective Regime B Vacuity
- Proposition L14: One Good Prime Suffices
- Sessions 10b-10f20 (Blocking Mechanism)
- 3 open conjectures + conditional chain
- Lean 4 formalization (97 verified + ~38 skeleton theorems)

## 3. Lean (`lean/`, 22 files)

### 3.1. Verified core (`lean/verified/`, Lean 4.15.0)

| File | Contents | sorry | axiom |
|------|----------|:-----:|:-----:|
| `CollatzVerified/Basic.lean` | 73 theorems | 0 | 0 |
| `CollatzVerified/G2c.lean` | 24 theorems (CRT, modular) | 0 | 0 |
| `CollatzVerified.lean` | Module root | — | — |
| `Main.lean` | Entry point | — | — |
| `lakefile.toml` | Lake config | — | — |
| `lean-toolchain` | Lean 4.15.0 | — | — |
| `README.md` | Documentation | — | — |
| `.github/workflows/lean_action_ci.yml` | Local CI | — | — |
| `.gitignore` | Exclusions | — | — |
| `lake-manifest.json` | Dependencies | — | — |

Coverage: nonsurjectivity k=18-25, zero-exclusion q3, Gersonides, parity, cosets, Parseval, CRT, Mellin radar.

### 3.2. Research skeleton (`lean/skeleton/`, Lean 4.29.0-rc2 + Mathlib4)

| File | Contents | sorry | axiom |
|------|----------|:-----:|:-----:|
| `JunctionTheorem.lean` | Junction Theorem | 0 | 1* |
| `SyracuseHeight.lean` | Syracuse height | 0 | 0 |
| `BinomialEntropy.lean` | Entropy bounds | 0 | 0 |
| `EntropyBound.lean` | Tangent entropy | 0 | 0 |
| `ConcaveTangent.lean` | Tangent inequality | 0 | 0 |
| `LegendreApprox.lean` | Legendre contrapositive | 0 | 0 |
| `FiniteCases.lean` | k in [18, 200] | 0 | 0 |
| `FiniteCasesExtended.lean` | k in [201, 306] | 0 | 0 |
| `FiniteCasesExtended2.lean` | k in [307, 665] | 0 | 0 |
| `AsymptoticBound.lean` | k >= 666 (asymptotic) | 0 | 1** |

**Total skeleton: 0 sorry, 2 axioms.**

\* Axiom 1: Simons--de Weger (published result, Acta Arith. 2005).
\** Axiom 2: continued fraction lower bound for convergents of log₂3 (Hardy & Wright §10.8, not yet in Mathlib).

### 3.3. Configuration

| File | Role |
|------|------|
| `lakefile.lean` | Mathlib pinned to v4.29.0-rc2 |
| `lean-toolchain` | Lean 4.29.0-rc2 |
| `lake-manifest.json` | Resolved dependencies |

## 4. Scripts

### 4.1. Core (`scripts/core/`, 13 scripts, Phases 14-19 + SP5 + Research)

Published, verified scripts associated with the preprint.

| Script | Phase | Contents |
|--------|:-----:|---------|
| `verify_nonsurjectivity.py` | — | Theorem 1 for k in [18, 500] |
| `multidimensional_mold.py` | 14 | Multidimensional obstruction |
| `interdimensional_tension.py` | 15 | Coset rigidity + zero-exclusion |
| `analytical_obstruction.py` | 16 | Character sums + Parseval |
| `keyhole_geometry.py` | 17 | p-adic geometry + Newton |
| `programme_merle.py` | 18 | Programme Merle assembly |
| `radar_mellin.py` | 19 | Multiplicative Mellin radar |
| `verify_condition_q.py` | SP5 | Condition (Q) for k in [18, 28] |
| `stress_test.py` | — | 402 robustness tests |
| `numerical_audit.py` | — | 152 numerical verifications |
| `prove_fz_gap_closure.py` | R | **Gap C closure**: d ∤ F_Z for all odd k ≥ 7 (2-adic valuation) |
| `transient_zero_analysis.py` | R | **Transient Zero Property**: c_j=0 ⟹ c_{j+1}≠0 mod p |
| `image_density_analysis.py` | R | Image density: |Im(Ev_d)|/d matches birthday model (negative result) |

### 4.2. Research (`scripts/research/`, 5 files, Transient Zero investigation)

Research sprint on the Transient Zero Property — multi-agent investigation.

| Script | Agent | Contents |
|--------|:-----:|---------|
| `tz_arc_decomposition.py` | Théoricien | Arc decomposition of Horner chains between zeros |
| `tz_exhaustive_enumeration.py` | Calculateur | Exhaustive zero census for small k |
| `tz_markov_analysis.py` | Probabiliste | Markov chain model — **doubly stochastic theorem** |
| `tz_bridge_connections.py` | Connecteur | Cross-prime correlations via CRT |
| `tz_exhaustive_results.json` | Calculateur | Raw enumeration data |

**Key finding (Round 1 — CLOSED)**: The Horner transition matrix is doubly stochastic
(proved), so the Transient Zero Property has NO effect on the stationary probability
π(0) = 1/p. All 4 agents converge: TZ is a LOCAL constraint, while cycle exclusion
requires GLOBAL properties. The arc decomposition provides no multiplicative
improvement beyond 1/p. Cross-prime CRT correlations are undetectable.

**Pistes de rebond identifiées** → Round 2 (scripts/research/r2_*.py):
- Sans remplacement (non-Markov correlations)
- Ordonnancement (structure géométrique de 2^a)
- Attaque alternative de la Conjecture 7.4 (-1 ∉ Im(g))
- Innovation computationnelle (motifs cachés dans corrSum)

### 4.3. Exploration (`scripts/exploration/`, 81 scripts, Phases 20-22 + SP6-SP10 + A-F)

Research exploration scripts (entropic approach).

| Script | Phase | Contents |
|--------|:-----:|---------|
| `phase20_crt_analysis.py` | 20 | Hybrid CRT analysis |
| `phase20_mixing_simulation.py` | 20 | Mixing simulation |
| `phase20_type_classification.py` | 20b | Type I/II classification |
| `phase21_*.py` (9 scripts) | 21 | Mellin spectral, CRT, decay, multilinear |
| `phase22_*.py` (5 scripts) | 22 | CRT amplification, spectral bounds |
| `sp6_*.py` (5 scripts) | SP6 | Ghost Fish, 3-mesh net, Mersenne, tunnel |
| `sp7_*.py` (4 scripts) | SP7 | K_MAX, precise rho, Fish-Tunnel danger, gap scan |
| `sp8_*.py` (2 scripts) | SP8 | Fish nature, Fish-Tunnel analysis |
| `sp9_*.py` (4 scripts) | SP9 | Scan k->500, mpmath, D26/D28, Voie 4 |
| `sp10_*.py` (33 scripts) | SP10 | Condition (Q) L1-L13, Beatty, regimes A/B |
| `phase_a1_exhaustive_k18_25.py` | A1 | Exhaustive DP verification k=18..25 |
| `phase_a2_regime_b_extension.py` | A2 | Regime A/B classification k=18..67 |
| `phase_a2plus_ecm_cofactors.py` | A2+ | ECM factorization 12 cofactors |
| `phase_b1_energy_E8.py` | B1 | E8 energy |
| `phase_b2_weyl_analysis.py` | B2 | Weyl analysis |
| `phase_b3_PU_verify.py` | B3 | Proportion Uniformity verification |
| `phase_c_*.py` (2 scripts) | C | Regime B census + 4-route hunt |
| `phase_d_formal_proof.py` | D | Formal theorem (Proposition L13) |
| `phase_e_one_good_prime.py` | E | CRT bypass (Proposition L14) |
| `phase_f_*.py` (2 scripts) | F | Deep dive + extension k=19-21 |

### 4.4. Tools (`scripts/tools/`, 70+ scripts + 6 logs, Sessions 7-10f26)

Research scripts for the blocking mechanism.

| Script | Session | Contents |
|--------|:-------:|---------|
| **Session 7-9 (foundations)** | | |
| `session7_scratch.md` | 7 | Scratch notebook session 7 |
| `session8_*.py` (5 scripts) | 8 | Baker, SAT/SMT, blocking prime |
| `session8_scratch.md` | 8 | Scratch notebook session 8 |
| `session9_*.py` (5 scripts) | 9 | CRT anti-correlation, target -1 |
| `session9_scratch.md` | 9 | Scratch notebook session 9 |
| **Session 10 (pre-10b)** | | |
| `session10_*.py` (2 scripts) | 10 | General prime blocking, protocol |
| `session10_protocol_research.md` | 10 | Research protocol |
| **Sessions 10b-10d** | | |
| `session10b_contradiction_approach.py` | 10b | Contradiction approach |
| `session10b_scratch.md` | 10b | **Main notebook (R1-R79)** |
| `session10c_exclusion_chain.py` | 10c | Exclusion chain |
| `session10d_mechanism_II_crt.py` | 10d | Mechanism II CRT |
| `session10d_scratch.md` | 10d | Scratch notebook session 10d |
| **Sessions 10e-10e4** | | |
| `session10e_filtration_proof.py` | 10e | Filtration proof |
| `session10e2_backward_chain_universal.py` | 10e2 | Universal backward chain |
| `session10e3_algebraic_proof.py` | 10e3 | Algebraic overflow proof |
| `session10e4_universal_sigma0.py` | 10e4 | Universal sigma_tilde=0 |
| **Sessions 10f1-10f6** | | |
| `session10f_overflow_universal.py` | 10f1 | Universal overflow |
| `session10f2_structural_argument.py` | 10f2 | Structural argument |
| `session10f3_cascade_contradiction.py` | 10f3 | Cascade contradiction |
| `session10f4_algebraic_boundary.py` | 10f4 | Algebraic boundary |
| `session10f5_band_structure.py` | 10f5 | Band structure |
| `session10f6_universal_directions.py` | 10f6 | Universal directions |
| **Sessions 10f7-10f8b** | | |
| `session10f7_crt_mechanism2.py` | 10f7 | Extended CRT anti-correlation |
| `session10f8_dp_large_k.py` | 10f8 | DP large k |
| `session10f8b_dp_optimized.py` | 10f8b | Optimized DP (k<=67) |
| **Sessions 10f9-10f12 (induction)** | | |
| `session10f9_theoretical_framework.py` | 10f9 | Unified theoretical framework |
| `session10f10_uniform_arguments.py` | 10f10 | Uniform arguments |
| `session10f11_gap2_iminterior.py` | 10f11 | Im_interior x2-closed |
| `session10f12_double_border_induction.py` | 10f12 | **4-case induction** |
| **Sessions 10f13-10f15 (polynomial)** | | |
| `session10f13_target_nonzero_proof.py` | 10f13 | **Polynomial F(u)** |
| `session10f14_size_argument.py` | 10f14 | Size argument C/d->0 |
| `session10f15_lean_ready_formulation.py` | 10f15 | Lean-ready formulation |
| **Sessions 10f16-10f17 (gaps)** | | |
| `session10f16_conjectures_attack.py` | 10f16 | Attack on 4 gaps |
| `session10f16b_remaining.py` | 10f16b | Residual gaps |
| `session10f17_squarefree.py` | 10f17 | Squarefree investigation |
| `session10f17b_squarefree_fast.py` | 10f17b | Fast squarefree |
| `session10f17c_fz_mod_p.py` | 10f17c | F_Z mod p local coprimality |
| `session10f17d_extended_verif.py` | 10f17d | Extended verification |
| **Session 10f18 (G2a)** | | |
| `session10f18_g2a_theory.py` | 10f18a | G2a theory, periods T_F/T_d |
| `session10f18b_critical_density.py` | 10f18b | Critical prime density |
| `session10f18c_extended_final.py` | 10f18c | **F_Z mod d != 0 for k<=10001** |
| **Session 10f19 (G2c)** | | |
| `session10f19_g2c_attack.py` | 10f19a | Initial G2c attack |
| `session10f19b_g2c_fast.py` | 10f19b | **2^C mod d != 1 (19 prime d)** |
| **Session 10f20 (G2c unconditional)** | | |
| `session10f20_g2c_unconditional.py` | 10f20 | ord>S proved, gap S->C |
| **Sessions 10f21-10f26 (Artin investigation)** | | |
| `session10f21_*.py` | 10f21 | G2c investigation |
| `session10f22_*.py` (12 scripts) | 10f22 | Artin investigation, thermal analysis |
| `session10f23_*.py` | 10f23 | Small prime blocker |
| `session10f24_*.py` | 10f24 | G2a quadratic |
| `session10f25_*.py` | 10f25 | CRT closure |
| `session10f26_*.py` (12 scripts) | 10f26 | Artin attack, smoothness, order bounds |
| **General tools** | | |
| `front1_*.py` (3 scripts) | — | Blocking mechanism, k=5 |
| `front2_spectral_analysis.py` | — | Spectral analysis |
| `front4_invariants.py` | — | corrSum invariants |
| `character_sum_analysis.py` | — | Character sums |
| `counting_bound_approach.py` | — | Counting bounds |
| `double_peeling_proof.py` | — | Double peeling |
| `drift_formalization.py` | — | Drift formalization |
| `enonce_c_*.py` (2 scripts) | — | Statement C investigation |
| `formal_statements.py` | — | Formal statements |
| `horner_drift_theorem.py` | — | Horner drift theorem |
| `obstruction_search.py` | — | Obstruction search |
| `ordered_backward_automaton.py` | — | Ordered backward automaton |
| `phantom_position_test.py` | — | Phantom position test |
| `position_incompatibility_analysis.py` | — | Incompatibility analysis |
| `prime_factor_obstruction.py` | — | Prime factor obstruction |
| `regression_test.py` | — | Regression tests |
| `spectral_ordered_automaton.py` | — | Spectral ordered automaton |
| `test_small_k.py` | — | Small k test |
| `theorem82_ord_proof.py` | — | Theorem 8.2 ord proof |
| `weight_asymmetry_proof.py` | — | Weight asymmetry |
| `why_c0_equals_1.py` | — | Why c_0 = 1 |
| **Sieve programs (C)** | | |
| `sieve_*.c` (5 programs) | — | Compiled sieve programs for Artin |
| `mscan_n23*.c` (2 programs) | — | M-scan sieve programs |

## 5. Research Protocol (`research_protocol/`, 8+ files)

| File | Contents |
|------|---------|
| `BLOCKING_MECHANISM_PROOF_SKETCH.md` | **Proof sketch v0.15** (22 sections) |
| `DISCOVERY_PROTOCOL.md` | Research protocol v2.2 |
| `MIND_MAP.md` | Dependency map |
| `session6_research_log.md` | Session 6 journal |
| `session7_research_log.md` | Session 7 journal |
| `artin_analysis_10f26.md` | Artin analysis |
| `artin_synthesis_*.md` | Artin synthesis documents |

## 6. Research Log (`research_log/`, 56 files)

### Foundations (Phases 10-13)

| File | Contents |
|------|---------|
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

### Analytical development (Phases 14-19)

| File | Contents |
|------|---------|
| `phase14_moule_multidimensionnel.md` | Multidimensional mold |
| `phase15_tension_interdimensionnelle.md` | Inter-dimensional tension |
| `phase16_obstruction_analytique.md` | Analytical obstruction |
| `phase17_geometrie_serrure.md` | Keyhole geometry |
| `phase18_programme_merle.md` | Programme Merle assembly |
| `phase19_radar_mellin.md` | Mellin radar |

### Advanced exploration (Phases 20-23)

| File | Contents |
|------|---------|
| `phase20_synthese_4_pistes.md` | Unified diagnostic: all roads lead to lacunary sums |
| `phase20a_piste_CRT_hybride.md` | Hybrid CRT approach |
| `phase20b_piste_structure_algebrique.md` | Type I/II prime classification |
| `phase20c_piste_mixing_random_walk.md` | Quantified spectral gaps |
| `phase20d_piste_extension_tao.md` | Tao extension ruled out (negative result) |
| `phase21_mellin_mater_mboup.md` | corrSum odd (R6), not div. by 3 (R7) |
| `phase22_borne_lacunaire_CRT.md` | N0(d)=0 for k=3..17 (R4), Conjecture 22.3 |
| `phase23_formule_verdict.md` | Systematic failure analysis |
| `phase23b_assemblage_formule.md` | Square root barrier (R5) |
| `phase23c_au_dela_barriere.md` | 3 bypass routes |
| `phase23d_epluchage_et_theoreme.md` | Peeling Lemma (R1), Theorem Q (C1) |
| `phase23e_annulation_mutuelle.md` | Conjectures Delta', PU, conditional chain |
| `phase23f_energie_additive_melange.md` | E4(H) quasi-Sidon (R2), sparsity (R3) |

### Investigations SP5-SP10

| File | Contents |
|------|---------|
| `sp5_investigation.md` | SP5: Condition (Q) via GPS |
| `sp6_ghost_fish.md` | SP6: Ghost Fish + 3-mesh net (4/5) |
| `sp7_junction_geology.md` | SP7: Junction geology (4.75/5) |
| `sp8_fish_nature.md` | SP8: Fish nature (4.85/5) |
| `sp9_formalization_and_extension.md` | SP9: Extension k->500, D28-D30 (4.85/5) |
| `sp10_motor_b2_investigation.md` | SP10: Condition (Q) analysis L1-L9 |
| `sp10_synthese_formelle.md` | SP10: Formal synthesis -- propositions and architecture |
| `sp10_level10_correction_cascade.md` | SP10 L10: BGK correction cascade |
| `sp10_level11_structural.md` | SP10 L11: structural analysis |
| `sp10_level12_effectivisation.md` | SP10 L12: effectivisation |

### Temporary results and syntheses

| File | Contents |
|------|---------|
| `phase_a1_resultats.tmp.md` | Phase A1: exhaustive verification k=18..25 |
| `phase_a2_resultats.tmp.md` | Phase A2: classification k=18..67 (0/165 Regime B) |
| `phase_a2plus_resultats.tmp.md` | Phase A2+: ECM 12 cofactors, 25 primes |
| `phase_b1_resultats.tmp.md` | Phase B1: E8 energy |
| `phase_b2_resultats.tmp.md` | Phase B2: Weyl analysis |
| `phase_b3_resultats.tmp.md` | Phase B3: Proportion Uniformity |
| `sp10_l12_exploration.tmp.md` | SP10 L12: exploration |
| `sp10_l13_exploration.tmp.md` | SP10 L13: exploration |
| `synthese_gap_closure.tmp.md` | Complete gap closure synthesis |
| `carte_mentale_exhaustive.tmp.md` | Exhaustive mind map |

### Corrections

| File | Contents |
|------|---------|
| `ERRATA.md` | Corrections to research log values |

## 7. Audits (`audits/`, 5 files)

| Version | Result | Level |
|---------|--------|-------|
| V1 | Certification refused (blockers identified) | Post-doctoral |
| V2 | New blocker identified | Ultra-severe |
| V3 | Certified (all blockers resolved) | DO-178C / IEC 61508 / EAL7 |
| V4 | Mathematical verification of logical chain | Pure mathematics |
| V8 | Red Team 4-expert panel (7.4/10, PUBLISH after revision) | Expert panel |

## 8. Documentation (`docs/`)

| File | Contents |
|------|---------|
| `plans/2026-02-27-phase20-4-pistes-design.md` | Phase 20 design document |
| `plans/2026-03-03-gap-closure-design.md` | Gap closure design document |

## 9. CI/CD (`.github/workflows/`)

| File | Action |
|------|--------|
| `lean-check.yml` | Automatic verification: 0 sorry, 0 extra axiom |
| `sp10-phase1.yml` | SP10 Phase I: Condition (Q) verification k=69..500 |

---

## Results by status

### Major results (Blocking Mechanism, sessions 10b-10f26)

| # | Result | Session |
|---|--------|:-------:|
| — | 4-case induction: interior + border + double-border | 10f12 |
| — | Im_interior x2-closed | 10f11 |
| — | Polynomial F(u): double-border annihilation | 10f13 |
| — | F_Z mod d != 0 for k <= 10001 | 10f18c |
| — | 8 critical primes, density -> 0 | 10f18b |
| — | CRT inequality N₀(d) <= N₀(p) | 10d |
| — | Exhaustive DP N₀(d) = 0 for k <= 67 | 10f8b |
| — | ord_d(2) > C for 19 prime d | 10f19b |
| — | C/d -> 0 proved (Stirling + entropy) | 10f14 |
| — | **G2c under GRH**: Hooley (1967) | 10f19 |
| — | ord_d(2) > S proved (k >= 4) | 10f20 |

### Unconditional (entropic approach, in the preprint)

| # | Result | Section |
|---|--------|:-------:|
| R1 | Peeling Lemma: N0(p) <= 0.63C | S7.2 |
| R4 | N0(d) = 0 for k=3..17 | S8.2 |
| R5 | Square root barrier | S7.4 |
| R6 | corrSum always odd | S2.1 |
| R7 | corrSum never divisible by 3 | S2.1 |

### New results (March 2026 research sprint)

| # | Result | Script | Status |
|---|--------|--------|--------|
| R8 | **Gap C closed**: d ∤ F_Z for all odd k ≥ 7 (2-adic valuation) | `prove_fz_gap_closure.py` | **Proved** |
| R9 | **Transient Zero Property**: c_j=0 ⟹ c_{j+1}≠0 mod p (p odd) | `transient_zero_analysis.py` | **Proved** (trivial) |
| R10 | Image density matches birthday model (no extra thinning) | `image_density_analysis.py` | Negative result |
| R11 | **Doubly stochastic theorem**: Horner transition matrix T is doubly stochastic | `tz_markov_analysis.py` | **Proved** |
| — | TZ constraint invisible at single-prime level (π(0) = 1/p exactly) | `tz_markov_analysis.py` | Proved (negative) |

### Conditional (in the preprint)

| # | Result | Section |
|---|--------|:-------:|
| C1 | Theorem Q: |sigma T| <= 0.041C => no cycles | S9.1 |

### Reserved for paper 2 (in research_log only)

| # | Result | Source |
|---|--------|--------|
| R2 | E4(H) = 2S^2 - S + O(S log S), H quasi-Sidon | phase23f |
| R3 | Sparsity |{u : |G(u)| >= alphaS}| | phase23f |

### Open conjectures

| Conjecture | Statement | Status |
|------------|-----------|--------|
| G2c | ord_d(2) > C for d = 2^S - 3^k prime | **Resolved under GRH** |
| G2a | F(u) != 0 mod d for all k | Quasi-resolved (8 critical primes) |
| G1 | sigma_tilde = 0 only for k=3,5 | Quasi-closed (Zsygmondy + verif k<=499) |
| G3 | CRT anti-correlation for composite d, k>=68 | Extrapolated (verified k<=67) |
| 22.3 | Horner equidistribution | Open |
| Delta' | Strong spectral gap | Open |
| PU | Uniform proportion | Open |
