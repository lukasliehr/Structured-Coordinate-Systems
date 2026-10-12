import Lean_Code.SchauderTranslates.SeedCarrierGram

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SeedCarrier
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {ρ : Measure S} [IsProbabilityMeasure ρ] (c : SeedCarrier (ι := ι) ρ)

/-- The carrier together with independent seed phases is orthonormal for the reference measure. -/
theorem rows_reference (L : ℕ) :
    integralGram (ρ.prod (torusMeasure L)) (fun _ => 1) (c.rows L) = 1 := by
  have hκ : ∀ x, ‖(0 : ℂ) * c.e x‖ ≤ 1 / 4 := by intro x; norm_num
  have h : c.gram L 1 0 = 1 := by
    ext i j
    cases i with
    | inl i => cases j with
      | inl j => simpa [Matrix.one_apply] using c.gram_carrier_carrier L (m := 1) (κ := 0) (by norm_num) hκ i j
      | inr j => simp [c.gram_carrier_seed L (m := 1) (κ := 0) (by norm_num) hκ, Matrix.one_apply]
    | inr i => cases j with
      | inl j => simp [c.gram_seed_carrier L (m := 1) (κ := 0) (by norm_num) hκ, Matrix.one_apply]
      | inr j => simpa [Matrix.one_apply] using c.gram_seed_seed L (m := 1) (κ := 0) (by norm_num) hκ i j
  have hw : c.weight L 1 0 = fun _ => 1 := by
    funext p
    simp [weight]
  simpa only [gram, hw] using h

/-- Strict positivity, contraction, and an explicit spectral floor of the actual raw seed Gram. -/
theorem gram_positive_contraction (L : ℕ) {m κ : ℝ} (hm : 0 < m)
    (hm1 : m ≤ (1 / 2 : ℝ) ^ L) (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4) :
    (c.gram L m κ).PosDef ∧ (1 - c.gram L m κ).PosSemidef ∧
      (c.gram L m κ - (seedFloor L m : ℂ) • 1).PosSemidef := by
  exact integralGram_positive_contraction _ (c.weight_measurable L m κ) (seedFloor_pos L hm)
    (fun p => (seedKernel_uniform_bounds L hm.le (hκ p.1) p.2).1)
    (fun p => (seedKernel_bounds L hm hm1 (hκ p.1) p.2).2)
    (c.rows_measurable L) (c.rows_bounded L) (c.rows_reference L)

end SchauderTranslates.SeedCarrier
