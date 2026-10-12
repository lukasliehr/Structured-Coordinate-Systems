import Lean_Code.PositiveTranslates.StageMachine

/-!
# Local bases on a cell

`LocalBasis p β A B` says that `β` is a normalized, non-negative, compact-step Schauder
basis of `Lᵖ(A)` (the classes vanishing a.e. off `A`) whose finite prefixes are bounded by
`B`.  It is the cellwise input of the global splitting in
`Lean_Code/PositiveTranslates/Global/Main.lean`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

/-- `β` is a normalized non-negative compact-step Schauder basis of `Lᵖ(A)` with prefix
constant `B`.

* `step`: every `β n` is a compactly supported step function (finite real combination of
  indicators of bounded half-open intervals);
* `nonneg`: every `β n` is real and non-negative almost everywhere;
* `norm`: `‖β n‖ = 1`;
* `supported`: every `β n` vanishes almost everywhere outside `A`;
* `dense`: every `F ∈ Lᵖ(ℝ)` vanishing almost everywhere outside `A` lies in the closed
  complex linear span of the `β n`;
* `prefix_le`: for every finitely supported coefficient family `c` and every `N`,
  `‖∑_{n<N} cₙ βₙ‖ ≤ B ‖∑ₙ cₙ βₙ‖`.

By the finite prefix criterion these properties say exactly that `β` is a Schauder basis of
`Lᵖ(A)` all of whose partial sum projections have norm at most `B`. -/
structure LocalBasis (p : ℝ≥0∞) [Fact (1 ≤ p)] (β : ℕ → LebesgueLp p) (A : Set ℝ) (B : ℝ) : Prop where
  step : ∀ n, IsCompactStep p (β n)
  nonneg : ∀ n, IsNonneg (β n)
  norm : ∀ n, ‖β n‖ = 1
  supported : ∀ n, SupportedOn (β n) A
  dense : ∀ F : LebesgueLp p, SupportedOn F A →
    F ∈ closure (Submodule.span ℂ (Set.range β) : Set (LebesgueLp p))
  prefix_le : ∀ (N : ℕ) (c : ℕ →₀ ℂ),
    ‖∑ n ∈ Finset.range N, c n • β n‖ ≤ B * ‖Finsupp.linearCombination ℂ β c‖

end StructuredBases.PositiveTranslates
