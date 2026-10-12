import Lean_Code.SchauderTranslates.ActivationInverse

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

theorem rawGram_norm_le_one (s : ScalarData d n) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram‖ ≤ 1 := by
  let u := fun i => s.vector (s.augmentedFrequency i)
  have hU : ‖hilbertSynthesis (𝕜 := ℂ) u‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro c
    have h := (s.toTorusWeight.synthesis_norm_sq_bounds (b := 0) le_rfl
      (fun x => (s.positive x).le) s.augmentedFrequency s.augmentedFrequency_injective c).2
    simpa only [one_mul] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
  have he := hilbertSynthesis_gram (𝕜 := ℂ) u
  change ((hilbertSynthesis (𝕜 := ℂ) u)†).comp (hilbertSynthesis (𝕜 := ℂ) u) =
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram at he
  rw [← he, norm_adjoint_comp_self]
  nlinarith [norm_nonneg (hilbertSynthesis (𝕜 := ℂ) u)]

theorem one_le_rawGram_inverse_norm (s : ScalarData d n) :
    1 ≤ ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram⁻¹‖ := by
  let Φ := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)
  have hinv : Φ s.rawGram⁻¹ * Φ s.rawGram = 1 := by
    rw [← map_mul, Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp s.rawGram_posDef.isUnit), map_one]
  have h := norm_mul_le (Φ s.rawGram⁻¹) (Φ s.rawGram)
  rw [hinv, norm_one] at h
  exact h.trans (by
    have hu := s.rawGram_norm_le_one
    calc
      ‖Φ s.rawGram⁻¹‖ * ‖Φ s.rawGram‖ ≤ ‖Φ s.rawGram⁻¹‖ * 1 :=
        mul_le_mul_of_nonneg_left hu (norm_nonneg _)
      _ = _ := mul_one _)

/-- Activation does not increase the augmented inverse operator norm. -/
theorem activatedInverse_norm_le (s : ScalarData d n) (p : ℝ) :
    ‖s.activatedInverse p‖ ≤
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram⁻¹‖ := by
  have h := activationOperator_norm_le (μ := AddCircle.haarAddCircle)
    (activationSet p) (activationSet_measurable p)
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ Fin n)) s.rawGram⁻¹)
  rw [max_eq_right s.one_le_rawGram_inverse_norm] at h
  exact h

end ScalarData
end SchauderTranslates
