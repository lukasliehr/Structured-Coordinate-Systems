import Lean_Code.SchauderTranslates.Lp.LpAeMeasureEquiv
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α : Type*} [MeasurableSpace α]

def lpPowerDensity (p : ℝ≥0∞) (w : α → ℂ) : α → ℝ≥0∞ := fun x => ‖w x‖ₑ ^ p.toReal

theorem lpPowerDensity_measurable (p : ℝ≥0∞) {w : α → ℂ} (hw : Measurable w) :
    Measurable (lpPowerDensity p w) := hw.enorm.pow_const _

theorem lpPowerDensity_ne_zero_ae (p : ℝ≥0∞) {μ : Measure α} {w : α → ℂ}
    (hw0 : ∀ᵐ x ∂μ, w x ≠ 0) : ∀ᵐ x ∂μ, lpPowerDensity p w x ≠ 0 := by
  filter_upwards [hw0] with x hx
  exact (ENNReal.rpow_pos (by simpa using hx) (by simp)).ne'

theorem lpPowerDensity_reverse_ac (p : ℝ≥0∞) {μ : Measure α} {w : α → ℂ}
    (hw : Measurable w) (hw0 : ∀ᵐ x ∂μ, w x ≠ 0) : μ ≪ μ.withDensity (lpPowerDensity p w) :=
  withDensity_absolutelyContinuous' (lpPowerDensity_measurable p hw).aemeasurable
    (lpPowerDensity_ne_zero_ae p hw0)

/-- The density norm identity for actual complex functions, valid for
every finite positive exponent. -/
theorem eLpNorm_mul_density {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (μ : Measure α) {w f : α → ℂ} (hw : Measurable w) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => w x * f x) p μ = eLpNorm f p (μ.withDensity (lpPowerDensity p w)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpfin,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpfin,
    lintegral_withDensity_eq_lintegral_mul₀ (lpPowerDensity_measurable p hw).aemeasurable
      (hf.aemeasurable.enorm.pow_const _)]
  congr 1
  apply lintegral_congr
  intro x
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
  rfl

theorem memLp_mul_density {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (μ : Measure α) {w f : α → ℂ} (hw : Measurable w)
    (hw0 : ∀ᵐ x ∂μ, w x ≠ 0) (hf : MemLp f p (μ.withDensity (lpPowerDensity p w))) :
    MemLp (fun x => w x * f x) p μ := by
  have hfμ : AEStronglyMeasurable f μ :=
    hf.aestronglyMeasurable.mono_ac (lpPowerDensity_reverse_ac p hw hw0)
  refine ⟨hw.aestronglyMeasurable.mul hfμ, ?_⟩
  rw [eLpNorm_mul_density hp0 hpfin μ hw hfμ]
  exact hf.eLpNorm_lt_top

end SchauderTranslates.LpConstruction
