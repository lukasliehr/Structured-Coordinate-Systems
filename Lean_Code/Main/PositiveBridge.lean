import Lean_Code.Basis.Criterion
import Lean_Code.PositiveBiorthogonal.Statements

/-!
# Non-negative bases for `1 < p < ∞`, in Mathlib's language

The library `Lean_Code/PositiveBiorthogonal` uses its own structure
`PositiveBiorthogonal.SchauderBasis`. It has the same four fields as Mathlib's
`SchauderBasis`; this file converts in both directions and restates the two results
needed for the main theorem.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexOrder

namespace StructuredBases

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- From the internal structure to Mathlib's `SchauderBasis`. -/
def ofPositiveBiorthogonal (B : PositiveBiorthogonal.SchauderBasis 𝕜 p) :
    SchauderBasis 𝕜 (Lp 𝕜 p (volume : Measure ℝ)) :=
  ofCoord B.b B.coeff
    (fun n m => by rw [B.biorthogonal m n]; simp only [eq_comm]) B.expansion

@[simp] theorem ofPositiveBiorthogonal_coe (B : PositiveBiorthogonal.SchauderBasis 𝕜 p) :
    ⇑(ofPositiveBiorthogonal B) = B.b := rfl

theorem ofPositiveBiorthogonal_proj (B : PositiveBiorthogonal.SchauderBasis 𝕜 p) (N : ℕ) :
    (ofPositiveBiorthogonal B).proj N = PositiveBiorthogonal.P B N := rfl

/-- From Mathlib's `SchauderBasis` to the internal structure. -/
def toPositiveBiorthogonal (b : SchauderBasis 𝕜 (Lp 𝕜 p (volume : Measure ℝ))) :
    PositiveBiorthogonal.SchauderBasis 𝕜 p where
  b := b
  coeff := b.coord
  biorthogonal n l := by rw [coord_apply_basis]; simp only [eq_comm]
  expansion := tendsto_expansion b

theorem toPositiveBiorthogonal_P (b : SchauderBasis 𝕜 (Lp 𝕜 p (volume : Measure ℝ))) (N : ℕ) :
    PositiveBiorthogonal.P (toPositiveBiorthogonal b) N = b.proj N := rfl

/-- **Existence for `1 < p < ∞`.** -/
theorem exists_nonneg_schauderBasis_of_one_lt (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp₁ : 1 < p) (hp : p ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : SchauderBasis 𝕜 (Lp 𝕜 p (volume : Measure ℝ)),
      (∀ n, ∀ᵐ x : ℝ, 0 ≤ b n x) ∧ (b.nnnormProjBound : ℝ) < 1 + ε := by
  obtain ⟨B, hB, -, hK⟩ :=
    PositiveBiorthogonal.exists_almost_monotone_positive_basis 𝕜 p hp₁ hp.lt_top ε hε
  refine ⟨ofPositiveBiorthogonal B, hB, ?_⟩
  exact nnnormProjBound_lt_of_le _ (fun N => PositiveBiorthogonal.projection_le_K B N) hK

/-- **No monotone non-negative basis for `1 < p < ∞`**: the first coordinate projection
is never contractive. -/
theorem one_lt_norm_proj_one_of_nonneg (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp₁ : 1 < p) (hp : p ≠ ∞)
    (b : SchauderBasis 𝕜 (Lp 𝕜 p (volume : Measure ℝ))) (hb : ∀ n, ∀ᵐ x : ℝ, 0 ≤ b n x) :
    1 < ‖b.proj 1‖ :=
  PositiveBiorthogonal.first_projection_not_contractive_of_positive_basis 𝕜 p hp₁ hp.lt_top
    (toPositiveBiorthogonal b) hb

end StructuredBases
