import Lake
open Lake DSL

package collatz_junction where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Collatz where
  srcDir := "skeleton"
  roots := #[`JunctionTheorem, `SyracuseHeight, `BinomialEntropy, `LegendreApprox, `ConcaveTangent, `EntropyBound, `FiniteCases]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"
