import Lean_Code.SchauderTranslates.SeedKernel

noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Unit energy under a probability measure forces every nonnegative pointwise norm bound to be at least one. -/
theorem one_le_bound_of_unit_energy {S : Type*} [MeasurableSpace S] (ρ : Measure S)
    [IsProbabilityMeasure ρ] (e : S → ℂ) (he : Measurable e) {E : ℝ} (hE : 0 ≤ E)
    (hbound : ∀ x, ‖e x‖ ≤ E) (hunit : (∫ x, ‖e x‖ ^ 2 ∂ρ) = 1) : 1 ≤ E := by
  have hint : Integrable (fun x => ‖e x‖ ^ 2) ρ := by
    apply Integrable.of_bound (he.norm.pow_const 2).aestronglyMeasurable (E ^ 2)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖e x‖))] using
      pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2
  have h := integral_mono hint (integrable_const (E ^ 2))
    (fun x => pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2)
  rw [hunit] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  nlinarith

/-- In particular, the global supremum norm used in the paper is at least one. -/
theorem one_le_supNorm_of_unit_energy {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [BorelSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ] (e : BoundedContinuousFunction S ℂ)
    (hunit : (∫ x, ‖e x‖ ^ 2 ∂ρ) = 1) : 1 ≤ ‖e‖ :=
  one_le_bound_of_unit_energy ρ e e.continuous.measurable (norm_nonneg e) e.norm_coe_le_norm hunit

/-- The paper's seed parameter for any certified uniform bound. -/
def seedParameter (E : ℝ) : ℝ := 1 / (4 * E)

theorem seedParameter_bounds {E : ℝ} (hE : 1 ≤ E) :
    0 < seedParameter E ∧ seedParameter E ≤ 1 / 4 := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  constructor
  · unfold seedParameter; positivity
  · unfold seedParameter
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * E)).mpr
    linarith

theorem seedParameter_scaled_bound {E : ℝ} (hE : 1 ≤ E) {a : ℂ} (ha : ‖a‖ ≤ E) :
    ‖(seedParameter E : ℂ) * a‖ ≤ 1 / 4 := by
  have hp := (seedParameter_bounds hE).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  have h := mul_le_mul_of_nonneg_left ha hp.le
  have he : seedParameter E * E = 1 / 4 := by
    unfold seedParameter
    have hE0 : E ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hE)
    field_simp
  exact h.trans_eq he

end SchauderTranslates
