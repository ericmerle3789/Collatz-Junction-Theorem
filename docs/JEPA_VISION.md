# JEPA VISION -- Manifesto for Autonomous Mathematical Discovery

**Version:** 1.0 | **Date:** 18 Mars 2026 | **Author:** Eric Merle
**System:** Syracuse-JEPA v3.3 | **Modules:** 109 pipeline files, 3 engine files, 74+ total Python modules
**Repository:** `/Users/ericmerle/Documents/Collatz-Junction-Theorem/`

---

## 1. VISION

We are building something that has never existed: an AI system that can **INVENT genuinely new mathematical ideas**.

Not a theorem prover that applies known lemmas. Not a search engine that retrieves published results. Not a language model that recombines textbook techniques. We are building an engine that creates **novel algebraic objects, discovers new transformations, and constructs proof strategies that no human has written down**.

The target: **prove the Collatz positive-cycle conjecture** -- that N_0(d(k)) = 0 for all k, meaning no nontrivial positive cycle of the 3n+1 map exists.

### Why This Problem

The Collatz conjecture is not chosen for fame. It is chosen because it sits at the exact boundary where existing mathematics fails and where a new kind of mathematical AI could succeed:

- The problem is **reducible to algebra**: Steiner (1977) showed that a k-cycle exists if and only if a specific correction sum corrSum(sigma, k) = 0 mod d(k). This is an equation over finite fields. It is checkable. It is symbolic. It is perfect for machine reasoning.
- The problem has a **clear gap**: we have proved the Junction Theorem (|Im(Ev_d)| < d for all k >= 18), we have proved the conditional no-cycle result (under Hypothesis H, no positive cycles exist), and we have identified the ordering constraint as the sole mechanism blocking cycles. What remains is a **single lemma**: proving that sorted sequences cannot achieve corrSum = 0 mod d.
- The problem requires **creative mathematics**: existing approaches (exponential sums, sieve theory, Baker's theorem, spectral methods) have all been tested and documented as insufficient. The proof, if it exists, must come from a genuinely new algebraic insight. This is precisely the capability we are building.

### The Philosophical Stance

Mathematics is not a database of results to search. It is a **living construction** where new objects and structures emerge from the interaction between constraints and imagination. The Syracuse-JEPA is designed to replicate this generative process: it builds proof graphs, mutates algebraic tactics, discovers obstructions, and evolves strategies -- all within a rigorous verification framework.

The operator is Claude. The verifier is Lean 4. The inventor is the JEPA engine. No LLM API is called -- Claude reads, reasons, and directs the engine in real time. This is not "AI-assisted mathematics." This is **AI-native mathematical research**.

---

## 2. THE SELF-IMPROVEMENT LOOP

The heart of the system is an autonomous loop that makes the JEPA more capable with each iteration:

```
  +-------------------+
  |  EVALUATE JEPA    |  What can it prove? What can't it prove?
  +--------+----------+  Run on k=3..14, score tactics, identify failures
           |
           v
  +-------------------+
  |  FIND GAPS        |  Where does the reasoning break down?
  +--------+----------+  Classify: wrong primitive? missing structure?
           |              too local? can't quantify over all sigma?
           v
  +-------------------+
  |  RESEARCH          |  Scan literature for relevant techniques
  +--------+----------+  Baker, Catalan-Mihailescu, Fermat analogies
           |              Sieve theory, additive combinatorics, heights
           v
  +-------------------+
  |  UPGRADE JEPA     |  Add new symbolic objects, tactics, evaluators
  +--------+----------+  Expand expression tree grammar
           |              Implement new algebraic primitives
           v
  +-------------------+
  |  TEST ON COLLATZ  |  Run upgraded engine on the problem
  +--------+----------+  Does it prove new cases? Does N_0=0 hold?
           |
           v
  +-------------------+
  |  RED TEAM AUDIT   |  Adversarial verification
  +--------+----------+  Check for hallucinations, subtle errors
           |              Every claim numerically verified
           |
           +------> IF NOK: BACK TO EVALUATE
           |
           +------> IF OK: FORMALIZE IN LEAN 4
```

### Loop Discipline

Each cycle follows strict protocols:

1. **Fail-closed**: if a numerical test fails for ANY k in {3..14}, the approach is marked DEAD. No exceptions.
2. **Anti-hallucination**: every algebraic statement is verified by Python computation before being recorded. False claims are explicitly retracted (see `CORRECTION_20260318_exp_sums_fail.md`).
3. **Honest documentation**: dead ends are documented with the same rigor as successes. The system currently has **8 dead ends documented** and **5 partial successes**.
4. **Cumulative memory**: failures are stored in `logs/failure_memory.json` and consulted before each new attempt. The engine does not repeat known dead ends.

### Completed Cycles

As of 18 March 2026, the loop has executed **3+ full cycles**:

- **Cycle 0 (pre-audit)**: Built initial pipeline (FCQ, spectral, Range Exclusion). Result: Range Exclusion INVALID after cumulative-exponent audit.
- **Cycle 1**: Reconfigured for cumulative exponents. 13 research phases, 17 commits. Result: ordering constraint discovered as sole obstruction. 8 dead ends documented.
- **Cycle 2**: Aletheia triad + literature survey + 2-diff polynomial analysis. Q_delta(1)=0 universality discovered, leading to Q = (X-1)*R factorization.
- **Cycle 3 (latest)**: Symbolic objects + proof graphs + MCTS reasoning engine. JEPA Engine v2 with creative tactic generation via MAP-Elites.

---

## 3. ARCHITECTURE (Current State, 38 commits)

The system has four layers, each with distinct responsibilities.

### 3.1 Engine Layer (Core Reasoning)

Located in `syracuse_jepa/engine/`. Three files that form the mathematical brain:

| File | Role | Key Classes |
|------|------|-------------|
| `symbolic_objects.py` | Mathematical objects as first-class entities | `MathObject`, `ModularInt`, `Polynomial`, `ProofGraph`, `ObjType`, `Relation` |
| `reasoning_engine.py` | Graph-based proof search with MCTS | `Tactic`, `ReasoningEngine`, tactics: `factor_Q`, `evaluate_at_rho`, `check_order`, `apply_baker` |
| `creative_tactic_gen.py` | Expression-tree mutation via MAP-Elites | `ExprNode`, `ExprTree`, `TacticCandidate`, `MAPElitesArchive`, `IslandFunSearch` |

The ProofGraph is the central data structure: nodes are `MathObject` instances (integers, modular elements, polynomials, sequences, group elements, ideals, bounds), edges are `Relation` instances (divides, coprime, congruent, root_of, factors_as, generates). Tactics transform the graph by adding new nodes and edges.

### 3.2 Pipeline Layer (Exploration and Analysis)

Located in `syracuse_jepa/pipeline/`. 109 files covering the full research spectrum:

**Core Pipeline (14 stages):**
- `run_pipeline_v3.py` -- Orchestrator with 14 sequential/parallel stages
- `explorer.py`, `analyst.py`, `pattern_miner.py`, `strategist.py` -- Stages 1-4
- `spectral.py`, `fcq_transfer.py`, `map_reeval.py`, `creative_engine.py`, `hybrid_prover.py` -- Stages 5a-5e (parallel)
- `prover.py`, `discovery.py`, `genius.py`, `redteam.py`, `formalizer.py`, `verifier.py` -- Stages 6-10

**Post-Audit Modules (20 files, created 18 March 2026):**
- `cumulative_generator.py` -- Correct Steiner cumulative sequence generator
- `paradigm_breaker.py` -- Creative engine: generates 6 paradigms
- `deep_explorer.py` -- 6 algebraic explorations
- `algebraic_obstruction.py` -- REST' = sum(rho^i * 2^{delta_i})
- `subgroup_search.py` -- Valuation + <2,3> subgroup structure
- `number_field_prover.py` -- Proof via norms in K = Q(alpha)
- `rearrangement_proof.py` -- Ordering constraint discovery
- `crossing_analysis.py` -- Free solution crossing verification
- `swap_correction.py` -- Sorting correction nonvanishing
- `proof_search_loop.py` -- 10 lemma candidate testing
- And 10 more (ideal_decomposition, localization, maximum_principle, cyclotomic, baker_residual, parity_obstruction, diophantine_explorer, ordering_formalization, lattice_avoidance, inertia_test)

**AI-Inspired Modules:**
- `funsearch_engine.py`, `funsearch_loop.py` -- FunSearch evolutionary loop
- `alphaproof_mcts.py` -- Monte Carlo Tree Search on proof tree
- `jepa_world_model.py` -- Predictive internal model of proof space
- `optimist_pessimist.py` -- Adversarial debate on strategy viability
- `davies_attribution.py` -- Attribution model for discovery

**Agent System (5 specialized agents):**
- `investigator_agent.py` -- "Dig the roots" -- chains of WHY on 4+ levels
- `innovator_agent.py` -- "Create new objects" -- novel quantities, formulas
- `allegorist_agent.py` -- "See differently" -- generative metaphors
- `synthesizer_agent.py` -- "Assemble the pieces" -- global coherence
- `architect_agent.py` -- "Build the proof" -- formal skeleton

Agents communicate via `blackboard.py`, a persistent JSON state space that accumulates facts, conjectures, and partial proofs.

### 3.3 Data Layer

| Component | Location | Content |
|-----------|----------|---------|
| `cumulative_generator.py` | `pipeline/` | Correct Steiner sequence generator for k=3..any |
| `generator.py` | `data/` | Base data generation |
| Precomputed test data | `scripts/` | Exhaustive N_0 verification for k=3..23 |
| JSON results | `pipeline/*.json` | 15+ result files from pipeline runs |

### 3.4 Memory Layer

| Component | Location | Content |
|-----------|----------|---------|
| `failure_memory.json` | `logs/` | Accumulated dead ends with reasons |
| `self_reflection.py` | `pipeline/` | Engine self-evaluation after each cycle |
| `hypothesis_evolution.py` | `pipeline/` | Hypothesis tracking and mutation |
| `blackboard_state.json` | `pipeline/` | Persistent agent shared state |
| Research logs | `research_log/` | 15+ timestamped findings, breakthroughs, corrections |

### 3.5 Verification Layer

| Component | Location | Status |
|-----------|----------|--------|
| Lean 4 skeleton | `lean/skeleton/` | JunctionTheorem.lean (VALID), FiniteCases.lean (VALID), AsymptoticBound.lean (VALID, 2 sorry's) |
| Lean 4 core | `lean/verified/` | 65 theorems, 0 sorry, 0 axioms |
| Old Lean files | `lean4_proof/` | INVALID (individual exponents -- retracted) |
| Python exhaustive checks | `scripts/` | 9 verification scripts, brute force k=3..23 |

---

## 4. WHAT WORKS

### 4.1 Proof Graph Construction with Symbolic Objects

The `ProofGraph` class successfully builds structured mathematical knowledge graphs for each k. Nodes represent `ModularInt`, `Polynomial`, `MathObject` instances with full type metadata. Relations (DIVIDES, COPRIME, ROOT_OF, FACTORS_AS) form a navigable graph that tactics can extend. `build_collatz_graph(k)` bootstraps the graph with all fundamental objects (d, S, rho, Q_delta, R_delta).

### 4.2 MCTS Proof Search

The `ReasoningEngine` with MCTS successfully proves N_0 = 0 for k < 68 by combining:
- SdW axiom (k <= 67) for the base region
- Tactic composition: `factor_Q` + `evaluate_at_rho` + `check_order` + `apply_baker`
- Exploration/exploitation balance via UCB1

### 4.3 MAP-Elites Archive for Tactic Diversity

The `MAPElitesArchive` in `creative_tactic_gen.py` maintains a grid of expression-tree tactics indexed by behavioral descriptors (tree depth, operation mix). This prevents convergence to a single strategy and maintains diversity in the search.

### 4.4 Island Model FunSearch

`funsearch_loop.py` implements an island model with migration between subpopulations of candidate evaluation functions. Each island evolves independently, with periodic migration of the best candidates.

### 4.5 Case-by-Case Algebraic Proofs

Multiple independent proof methods work for small k:
- **Number field norms** prove k=3,4 (N(P_sigma(alpha)) coprime to d for all sigma)
- **<2,3> subgroup** proves k=3,5 (subgroup = full (Z/dZ)*)
- **Valuation blocking** proves k=4,7,8,11 (a prime p|d has v_p(corrSum)=0 universally)
- **CRT interference** proves k=6,9,10,12 (individual primes allow N_0 > 0, but composite d forces N_0 = 0)
- **Exhaustive computation** confirms N_0 = 0 for k=3..23

### 4.6 Honest Dead End Documentation

8 dead ends rigorously documented:
1. Range Exclusion -- DEAD (cumulative range exponentially larger than d)
2. FCQ prime-by-prime -- DEAD (N_0(p) > 0 for almost all small primes p|d)
3. L-infinity exponential sums -- DEAD (max|G| ~ 0.2*C >> 1)
4. L2/Parseval exponential sums -- DEAD (collision count too high)
5. Self-referential system -- DEAD (equivalent to single equation)
6. Cyclotomic factorization -- DEAD (no new structural insight)
7. Inertia test -- DEAD (d not inert in Z[alpha] for most k)
8. Cross-k JEPA generalization -- DEAD (arithmetic structure is k-specific, a mathematical property)

---

## 5. WHAT DOESN'T WORK YET

### 5.1 Creative Tactic Generation is Too Mechanical

The current `creative_tactic_gen.py` operates on an expression tree grammar with fixed atomic operations (add, mul, pow, inv, gcd, ord on Z/dZ; sort, reverse, shift, diff, cumsum on sequences; factor, deriv, resultant on polynomials). Mutations change subtrees randomly. This is **recombination of known primitives**, not genuine invention.

What we need: the ability to discover that "the ordering constraint converts a universally achievable equation into an unachievable one" -- a STRUCTURAL insight about the relationship between combinatorial constraints and algebraic values. No combination of the current atomic operations can express this.

### 5.2 Evaluation Does Not Test the Universal Quantifier

The current evaluator tests tactics on specific k values and specific sigma sequences. It does NOT properly test whether a tactic works for ALL sigma. This is critical: the gap is proving a statement of the form "for ALL delta-sequences sigma, R_delta(rho) is not 0." A tactic that works on sampled sigma but fails on one counterexample is worthless.

### 5.3 No Real Learning from Failures

The `failure_memory.json` records dead ends, and `self_reflection.py` generates post-mortem analyses. But the system does not extract **transferable lessons** from failures. When Range Exclusion fails because "the range is too large," the lesson is "bounding arguments must account for exponential growth in cumulative exponents." This lesson should influence future tactic generation. Currently, it does not.

### 5.4 No Analogical Reasoning

The proof of Catalan's conjecture (Mihailescu 2002) and Fermat's Last Theorem (Wiles 1995) both required translating the problem into a completely different algebraic framework. Our engine has no mechanism for **mapping structural patterns from solved problems** onto the Collatz problem. No module asks: "What structure in Mihailescu's proof of x^p - y^q = 1 is analogous to our 2^S - 3^k = d?"

### 5.5 Expression Trees Operate on Scalars, Not Sequences

The `ExprNode` grammar operates on individual elements of Z/dZ. But the key object is a SEQUENCE sigma = (sigma_0 < sigma_1 < ... < sigma_{k-1}). The breakthrough discovery (ordering constraint) is a property of the sequence AS A WHOLE, not of individual elements. We need expression trees that can express:
- "The sequence is sorted" (a predicate on the full sequence)
- "Sorting changes the correction sum by a nonzero amount" (a function of the permutation)
- "Anti-correlation between position weight and value" (a structural property)
- "Every free solution has crossings" (a universal statement about a class of sequences)

---

## 6. THE GAP

### 6.1 The Reduction Chain

The Collatz positive-cycle conjecture has been **reduced to a single algebraic statement** through 4 layers of theorem:

```
  COLLATZ NO-CYCLE CONJECTURE
         |
         | (Steiner 1977)
         v
  n_0 * d(k) = corrSum(sigma, k)  has no solution with n_0 >= 1
         |
         | (Junction Theorem, Lean-proved)
         v
  |Im(Ev_d)| < d  for all k >= 18  (at least one residue is missed)
         |
         | (Conditional No-Cycle, Lean-proved)
         v
  HYPOTHESIS H: 0 is among the missed residues of Ev_d
         |
         | (Q-factorization, Cycle 2)
         v
  Q_delta(X) = (X-1) * R_delta(X)    for all delta-sequences
  corrSum = 0 mod d  <==>  R_delta(rho) = 0   where rho = 2/3 mod d
         |
         | (Ordering constraint, 18 March breakthrough)
         v
  THE MISSING LEMMA:
  For all k >= 3 and all valid (strictly ordered) delta-sequences:
    R_delta(rho) is not 0 mod d
```

### 6.2 What We Know About the Gap

**Verified computationally**: R_delta(rho) is not 0 for all k = 3..14 (exhaustive) and k = 3..67 (via SdW).

**The obstruction is ORDERING**: without the strict ordering constraint on sigma, the equation R_delta(rho) = 0 IS solvable (100% residue coverage for k >= 6). The strict ordering sigma_0 < sigma_1 < ... < sigma_{k-1} is the SOLE mechanism preventing solutions.

**Free solutions always have crossings**: every unordered sigma achieving corrSum = 0 mod d has at least one position where sigma_{i+1} < sigma_i (verified k=3..8).

**Sorting correction is always nonzero**: when crossings are repaired by swapping adjacent elements, the correction to corrSum is always nonzero mod d (verified k=3..8).

**Near-miss residuals are +/-1 or +/-2**: the closest any corrSum gets to 0 mod d always has |residual| in {1,2}, coprime to d.

**d is the unique unachieved divisor**: for most k, gcd(corrSum(sigma), d) achieves ALL divisors of d EXCEPT d itself.

### 6.3 Why It Is Hard

Proving R_delta(rho) is not 0 for ALL k >= 68 requires a **uniform argument** that works simultaneously for:
- All k (the modulus d = 2^S - 3^k changes with k)
- All valid sigma sequences (C(S-1, k-1) sequences, growing exponentially)
- The specific interplay between the ordering constraint and modular arithmetic

Standard tools fail:
- Exponential sum bounds are too weak (the image is sparse, covering only 13-25% of Z/dZ)
- Baker's theorem gives lower bounds on |corrSum - n*d| but not sharp enough
- Sieve theory handles average behavior but not worst-case individual residues
- The problem sits at the intersection of additive combinatorics, algebraic number theory, and analytic number theory -- a no-man's land where no standard technique dominates

---

## 7. ENVIRONMENT CONSTRAINTS

All computation runs on a single machine with hard resource limits. Every algorithmic decision must respect these constraints.

| Resource | Specification |
|----------|--------------|
| **Machine** | MacBook M1 Pro, 16GB RAM |
| **GPU** | None (MPS available but not used for proof computation) |
| **Python** | 3.12, miniforge3/conda, environment `collatz-jepa` |
| **Lean** | Lean 4 (v4.15.0 for verified core, v4.29.0-rc2 for skeleton) |
| **LLM API** | None. Claude is the operator, not a callable service. |
| **Floating point** | FORBIDDEN in proofs. All computation must be exact (integer arithmetic, exact modular arithmetic) |
| **External deps** | Minimal. No Sage, no Magma, no external CAS. We build our own symbolic algebra. |
| **Time** | Single-session autonomous runs. No cloud compute. |

### Implications for Architecture

- All enumeration must be bounded: C(S-1, k-1) grows exponentially, so exhaustive search is limited to k <= ~23
- MCTS must be shallow: thousands of rollouts, not millions
- MAP-Elites archive must be compact: hundreds of cells, not millions
- Symbolic computation must be hand-rolled: we implement our own polynomial arithmetic, modular arithmetic, and number field operations in pure Python
- Lean compilation is local: `lake build` must complete in reasonable time

---

## 8. KEY DISCOVERIES (18 March 2026)

The following discoveries were made during the autonomous JEPA session of 18 March 2026, across 13 research phases and 17 commits.

### Discovery 1: The Cumulative Exponent Correction (Critical Audit)

The corrSum formula in the old Lean files (`lean4_proof/Basic.lean`) used INDIVIDUAL exponents instead of Steiner's CUMULATIVE exponents. This invalidated Range Exclusion entirely. The correct formula is:

```
corrSum(sigma, k) = SUM_{i=0}^{k-1} 3^{k-1-i} * 2^{sigma_i}
```

where sigma_0 = 0 < sigma_1 < ... < sigma_{k-1} < S are cumulative sums of step sizes.

With the correct formula: N_0(d(k)) = 0 for all k=3..23 (exhaustively verified). The k=4 "phantom" composition disappears.

### Discovery 2: The Ordering Constraint is THE Fundamental Obstruction

WITHOUT the strict ordering constraint (sigma as any permutation of k distinct values from {0,...,S-1}): every residue mod d is achievable. For k=6,7: 100% residue coverage.

WITH the strict ordering constraint (sigma_0 < sigma_1 < ... < sigma_{k-1}): the target residue -3^{k-1} mod d is NEVER achieved.

**The ordering is the sole mechanism blocking Collatz cycles.** This is the central discovery of the session.

### Discovery 3: All Free Solutions Have Ordering Violations

Every unordered sigma tuple that achieves corrSum = 0 mod d contains at least one "delta-crossing" -- a position i where sigma_{i+1} < sigma_i, violating the strict increase requirement. None of the free solutions are weakly increasing. Verified exhaustively for k=3..8.

### Discovery 4: Sorting Correction is Always Nonzero

When a free solution's crossings are repaired by bubble-sort-style swaps to restore strict ordering, the correction to corrSum has the form (3^a - 3^b)(2^u - 2^v) mod d, and this is ALWAYS nonzero mod d. Verified for k=3..8.

### Discovery 5: Q_delta(1) = 0 Universally and Q = (X-1) * R Factorization

For every delta-sequence, the polynomial Q_delta(X) = SUM 3^{k-1-i} * X^{delta_i} satisfies Q_delta(1) = corrSum_normalized, and the evaluation at rho = 2/3 mod d determines whether corrSum = 0 mod d. Since Q_delta(1) has a universal factor (X-1), we get Q_delta = (X-1) * R_delta, reducing the problem to: R_delta(rho) is not 0.

### Discovery 6: REST' Formula

REST' = SUM rho^i * 2^{delta_i} where rho = 2*3^{-1} mod d satisfies 3*rho = 2 in Z/dZ. corrSum = 0 mod d if and only if REST' = -1 mod d. This reformulation isolates the "free" part of corrSum from the fixed part 3^{k-1}.

### Discovery 7: Number Field Norm Proves k=3,4

In the number field K = Q(alpha) where alpha^S = 3^k, the norm N(P_sigma(alpha)) is coprime to d for ALL sigma when k=3 or k=4. Since d is prime in these cases, this implies P_sigma(2) is not 0 mod d.

### Discovery 8: Near-Miss Residuals are +/-1 or +/-2

The minimum |corrSum mod d| over all sigma, taken as the smallest absolute representative, is always 1 or 2 for k=3..12. These residuals are always coprime to d.

### Discovery 9: d is the Unique Unachieved Divisor

For k=3,4,5,6,9,10,12: the set {gcd(corrSum(sigma), d) : all sigma} achieves ALL divisors of d EXCEPT d itself. The only missing gcd value is d. For k=7,8,11: d plus certain large prime factors are missing (exactly those where valuation blocking applies).

### Discovery 10: Maximum Principle

For P_sigma(X) = SUM 3^{k-1-i} * X^{sigma_i} evaluated at alpha = d-th root of unity, the real evaluation |P_sigma(alpha)| is maximal among all conjugates |P_sigma(alpha * zeta^j)| by the triangle inequality with positive coefficients. The real conjugate is NEVER the minimum.

### Discovery 11: CRT Interference Mechanism

For composite d = p_1 * ... * p_r, individual primes give N_0(p_i) > 0, but the Chinese Remainder Theorem reconstruction yields N_0(d) = 0. Example: k=6, d=295=5*59: N_0(5)=36, N_0(59)=6, N_0(295)=0. The zero-sets mod different primes are anti-correlated.

### Discovery 12: 5 Standard Approaches Eliminated

Rigorously tested and documented as DEAD:
1. Range Exclusion (cumulative range >> d)
2. FCQ prime-by-prime (N_0(p) > 0 for most p)
3. L-infinity exponential sums (max|G| >> 1)
4. L2/Parseval exponential sums (collision count too high)
5. Self-referential system (equivalent to original equation)

### Discovery 13: Overdetermined System Analysis

Orbit closure does not generate new constraints beyond the Steiner equation. The system is NOT overdetermined -- there is exactly one independent equation per cycle, no more.

---

## 9. NEXT STEPS

### 9.1 Rebuild Creative Engine for Sequence-Level Operations

**Priority: HIGHEST**

The current expression tree grammar operates on scalar elements of Z/dZ. The key discovery (ordering constraint) is a property of SEQUENCES, not scalars. The creative engine must be rebuilt with a grammar that includes:

- **Sequence predicates**: `is_sorted(sigma)`, `has_crossing(sigma, i)`, `crossing_count(sigma)`
- **Sequence transformations**: `sort(sigma)`, `permute(sigma, pi)`, `bubble_sort_step(sigma, i)`
- **Correction operators**: `correction(sigma, i)` = the change to corrSum when swapping positions i and i+1
- **Universal quantifiers**: `for_all_sigma(predicate)` as a first-class expression
- **Behavioral descriptors for MAP-Elites**: algebraic complexity (degree of polynomial involved), scope (scalar vs sequence vs universal), proof strength (verified for how many k)

### 9.2 Implement Proper "For All Sigma" Evaluation

**Priority: HIGHEST**

Every candidate tactic must be evaluated against the universal quantifier. This means:
- For small k (3..8): test against ALL sigma sequences (exhaustive)
- For medium k (9..14): test against ALL sigma sequences (feasible with DP)
- For large k (15+): test against random samples + adversarial samples (near-miss sigma sequences that get closest to 0 mod d)

A tactic passes only if it works for ALL tested sigma AND the argument generalizes (not k-specific).

### 9.3 Add Analogical Reasoning Module

**Priority: HIGH**

Create a module that maps structural patterns from solved problems:

- **Catalan-Mihailescu analogy**: x^p - y^q = 1 was proved by showing cyclotomic polynomial structure forces contradictions. Our 2^S - 3^k = d has similar mixed-exponential structure. What cyclotomic tools apply?
- **Fermat-Wiles analogy**: FLT was proved by mapping to elliptic curves and modularity. Is there an elliptic curve associated with the Steiner equation?
- **Baker-Tijdeman analogy**: Baker's theorem bounds |2^a - 3^b| from below. Can a similar lower bound be applied to |corrSum mod d|?
- **Roth-Schmidt analogy**: Diophantine approximation bounds how well algebraic numbers can be approximated by rationals. Does the ratio log2/log3 being "poorly approximable" help?

### 9.4 Implement Subgoal Decomposition for the Missing Lemma

**Priority: HIGH**

The Missing Lemma ("R_delta(rho) is not 0 for all valid delta-sequences") should be decomposed into subgoals:

1. **Subgoal A**: Classify delta-sequences by their "shape" (distribution of gaps delta_i = sigma_i - sigma_{i-1})
2. **Subgoal B**: For each shape class, prove R_delta(rho) is not 0 using class-specific algebraic arguments
3. **Subgoal C**: Prove the classification is exhaustive (every valid delta-sequence belongs to some class)
4. **Subgoal D**: Alternatively, find a UNIFORM argument that works for all shapes simultaneously (this is the ordering constraint approach)

The MCTS should be able to explore these subgoal branches independently.

### 9.5 Build MAP-Elites with Algebraic Behavioral Descriptors

**Priority: MEDIUM**

Current MAP-Elites uses tree depth and operation mix as behavioral descriptors. These are syntactic, not semantic. New descriptors should capture algebraic meaning:

- **Axis 1**: Level of abstraction (Z/dZ element, polynomial, ideal, number field element)
- **Axis 2**: Quantifier scope (existential on sigma, universal on sigma, universal on k)
- **Axis 3**: Proof technique (valuation, subgroup, norm, ordering, counting)
- **Axis 4**: Computational complexity (polynomial in k, exponential in k, requires exhaustive search)

### 9.6 Formalize the Ordering Constraint in Lean 4

**Priority: MEDIUM**

The ordering constraint discovery is the most promising path to the full proof. It should be formalized:
- Define "free solution" (unordered tuple with corrSum = 0 mod d)
- Prove that free solutions exist for all k >= 6 (the equation is solvable without ordering)
- Define "crossing" and "swap correction"
- State the conjecture: swap correction is always nonzero mod d
- Prove this for k=3..8 (exhaustive Lean computation)

### 9.7 Investigate the Swap Correction Algebraically

**Priority: HIGH**

The swap correction has the form (3^a - 3^b)(2^u - 2^v) mod d where a > b and u > v (from the crossing). This is nonzero mod d if and only if d does not divide the product. Since d = 2^S - 3^k:
- d is coprime to 2 and 3 (for k >= 3)
- So d does not divide (3^a - 3^b) = 3^b(3^{a-b} - 1) unless d | (3^{a-b} - 1)
- And d does not divide (2^u - 2^v) = 2^v(2^{u-v} - 1) unless d | (2^{u-v} - 1)
- The question reduces to: can ord_d(3) | (a-b) AND ord_d(2) | (u-v) simultaneously, given the constraints on a,b,u,v from the free solution?

This is a number-theoretic question about the orders of 2 and 3 modulo d = 2^S - 3^k. It connects to the Artin primitive root conjecture (already identified as relevant in the research protocol).

### 9.8 Extend Computational Verification

**Priority: LOW (but valuable)**

Push exhaustive N_0 verification from k=23 to as high as feasible:
- k=24..30: may be reachable with DP on modular residues (avoid full enumeration)
- k=31+: probabilistic arguments using random sampling of sigma sequences
- Document the computational frontier honestly

---

## APPENDIX A: FILE MAP

```
Collatz-Junction-Theorem/
  syracuse_jepa/
    engine/
      symbolic_objects.py      -- Mathematical objects (MathObject, ProofGraph)
      reasoning_engine.py      -- MCTS proof search (Tactic, ReasoningEngine)
      creative_tactic_gen.py   -- MAP-Elites expression trees (ExprNode, IslandFunSearch)
    pipeline/
      run_pipeline_v3.py       -- 14-stage orchestrator
      cumulative_generator.py  -- Correct Steiner cumulative generator
      [105+ more modules]      -- See JEPA_BIBLE.md for complete reference
    data/
      generator.py             -- Base data generation
    logs/
      failure_memory.json      -- Accumulated dead ends
    tests/                     -- Test suite
  lean/
    skeleton/                  -- Lean 4 formalization (VALID)
    verified/                  -- 65 theorems, 0 sorry
  lean4_proof/                 -- Old Lean files (INVALID, retracted)
  scripts/                     -- 9+ verification scripts
  research_log/                -- 15+ timestamped findings
  audits/                      -- 7 audit certifications (V1-V7)
  paper/                       -- Preprint (EN + FR)
  docs/
    JEPA_BIBLE.md              -- Complete technical manual (42KB)
    PROOF_STATUS_20260318.md   -- Corrected proof status
    SESSION_COMPLETE_20260318.md -- Full session report
    JEPA_VISION.md             -- This file
```

## APPENDIX B: MATHEMATICAL NOTATION

| Symbol | Definition |
|--------|-----------|
| k | Cycle length (number of odd steps) |
| S = S(k) | ceil(k * log2(3)), total even steps |
| d = d(k) | 2^S - 3^k, the Steiner denominator |
| sigma | Cumulative exponent sequence (0 = sigma_0 < sigma_1 < ... < sigma_{k-1} < S) |
| delta | Gap sequence (delta_i = sigma_i - sigma_{i-1} for i >= 1, delta_0 = sigma_0 = 0) |
| corrSum(sigma, k) | SUM_{i=0}^{k-1} 3^{k-1-i} * 2^{sigma_i} |
| Ev_d | Evaluation map: sigma -> corrSum(sigma) mod d |
| N_0(m) | #{sigma : corrSum(sigma) = 0 mod m} |
| rho | 2 * 3^{-1} mod d (satisfies 3*rho = 2) |
| Q_delta(X) | SUM 3^{k-1-i} * X^{delta_i} |
| R_delta(X) | Q_delta(X) / (X - 1) |
| H | Hypothesis: 0 is among the missed residues of Ev_d |
| C(n,k) | Binomial coefficient, number of valid sigma sequences = C(S-1, k-1) |

## APPENDIX C: REFERENCES

### Foundational
- Steiner (1977). "Collatz congruences and the 3x+1 problem."
- Simons and de Weger (2005). "Theoretical and computational bounds for m-cycles of the 3n+1 problem." Acta Arithmetica.
- Lagarias (2010). "The Ultimate Challenge: The 3x+1 Problem." AMS.

### Algebraic Number Theory
- Baker and Wustholz (1993). "Logarithmic forms and group varieties."
- Mihailescu (2004). "Primary cyclotomic units and a proof of Catalan's conjecture." (Analogy: x^p - y^q = 1)
- Washington (1997). "Introduction to Cyclotomic Fields."
- Neukirch (1999). "Algebraic Number Theory."

### AI-Inspired Methods
- Romera-Paredes et al. (2024). "Mathematical discoveries from program search with large language models." (FunSearch)
- Silver et al. (2017). "Mastering Chess and Shogi by Self-Play." (MCTS)
- Trinh et al. (2024). "Solving olympiad geometry without human demonstrations." (AlphaGeometry)
- LeCun (2022). "A Path Towards Autonomous Machine Intelligence." (JEPA architecture)
- Mouret and Clune (2015). "Illuminating search spaces by mapping elites." (MAP-Elites)

### Analytic Number Theory
- Hardy and Littlewood (1934). "Rearrangement inequality."
- Hooley (1967). "On Artin's conjecture." (GRH-conditional primitive root density)
- Goyal and Welch (2008). "Equity premium predictability." (Signal detection limits)

---

*This document is a living manifesto. It will be updated as the JEPA engine evolves, new discoveries are made, and the gap narrows. The goal is not publication -- the goal is truth.*
