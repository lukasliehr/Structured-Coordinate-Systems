import Lean_Code.Basis.Criterion
import Lean_Code.PositiveL1.Density

/-!
# A Schauder basis of `L¹(ℝ)` consisting of non-negative functions

For every `0 < θ < 1/2` there is a Schauder basis of `L¹(ℝ)` consisting of non-negative
functions whose partial sum projections all have norm at most `1 + 2θ`
(`StructuredBases.exists_nonneg_schauderBasis_L1`).

## The construction

For a bounded interval `V` of positive length let `e_V = 𝟙_V / |V|`.  The unit intervals
`I_j = (z j, z j + 1]` are enumerated by a bijection `z : ℕ → ℤ`.  We start with the
partition `𝒫₀ = {I₀}` and `b₀ = e_{I₀}`.  In step `n` the oldest interval `D` of `𝒫ₙ` is
split into a left part `B` of length `θ |D|` and a right part `C`, a fresh unit interval
`J = I_{n+1}` is added, and the two new basis functions are

`b_{2n+1} = e_C + e_J`,  `b_{2n+2} = e_B + e_J`.

The proof is distributed as follows.

* `Lean_Code/PositiveL1/Abstract.lean`: the prefix bound
  `‖∑_{k<N} a_k b_k‖ ≤ (1 + 2θ) ‖∑_{k<M} a_k b_k‖` (`N ≤ M`) in an abstract normed space,
  by means of two operators `R` (of norm one) and `S` (of norm at most `1 + 2θ`) for each step.
* `Lean_Code/PositiveL1/Indicators.lean`: indicator functions in `L¹` and a density criterion.
* `Lean_Code/PositiveL1/Cells.lean`: normalised indicators and set integrals in `L¹(μ)` satisfy
  the abstract hypotheses.
* `Lean_Code/PositiveL1/Intervals.lean`: the interval cells.
* `Lean_Code/PositiveL1/Density.lean`: the linear span of the basis functions is dense.

The statement then follows from the finite prefix criterion
`StructuredBases.exists_schauderBasis_of_prefix_bound'`.
-/

set_option autoImplicit false

namespace StructuredBases

open MeasureTheory
open scoped ENNReal NNReal ComplexOrder

/-- For every `0 < θ < 1/2` there is a Schauder basis of `L¹(ℝ)` (real or complex scalars)
consisting of non-negative functions whose partial sum projections all have norm `≤ 1 + 2θ`. -/
theorem exists_nonneg_schauderBasis_L1 (𝕜 : Type*) [RCLike 𝕜] {θ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1 / 2) :
    ∃ b : SchauderBasis 𝕜 (Lp 𝕜 1 (volume : Measure ℝ)),
      (∀ n, ∀ᵐ x : ℝ, 0 ≤ b n x) ∧ ∀ N, ‖b.proj N‖ ≤ 1 + 2 * θ := by
  have hz : Function.Bijective (Equiv.intEquivNat.symm : ℕ → ℤ) := Equiv.intEquivNat.symm.bijective
  have hc : PositiveL1.SplitCells (volume : Measure ℝ) θ
      (PositiveL1.cellSet (Equiv.intEquivNat.symm : ℕ → ℤ) θ) :=
    PositiveL1.splitCells hz.injective hθ (by linarith)
  have hs : PositiveL1.SplitSystem θ (hc.vec 𝕜) (hc.fn 𝕜) := hc.splitSystem
  obtain ⟨b, hb, hproj⟩ := exists_schauderBasis_of_prefix_bound' (𝕜 := 𝕜)
    (PositiveL1.splitSeq (hc.vec 𝕜)) hs.splitSeq_ne_zero
    (PositiveL1.dense_span_splitSeq hz hθ'.le hc) hs.prefix_bound
  refine ⟨b, fun n => ?_, hproj⟩
  rw [hb]
  exact hc.splitSeq_nonneg n

end StructuredBases
