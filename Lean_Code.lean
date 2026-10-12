import Lean_Code.Basis.UniqueExpansion
import Lean_Code.Main.NonnegBasis
import Lean_Code.Main.Translates

/-!
# Structured coordinate systems in `Lᵖ(ℝ)`: the internal proof library

Umbrella module. The three imports pull in the whole library:

* `Lean_Code.Main.NonnegBasis`: Theorem 1.1 (non-negative Schauder bases of `Lᵖ(ℝ)`,
  `1 ≤ p < ∞`), from `Lean_Code/PositiveBiorthogonal` (`1 < p < ∞`) and `Lean_Code/PositiveL1`
  (`p = 1`).
* `Lean_Code.Main.Translates`: Theorems 1.3 and 1.4 (Schauder bases of translates), from
  `Lean_Code/SchauderTranslates` (`p = 2`; the sharp estimates are in its subfolder `Sharp`)
  and `Lean_Code/PositiveTranslates` (`p > 2`).
* `Lean_Code.Basis.UniqueExpansion`: Mathlib's `SchauderBasis` agrees with the definition by
  unique norm-convergent expansions.

General facts about Schauder bases are in `Lean_Code/Basis`.
-/
