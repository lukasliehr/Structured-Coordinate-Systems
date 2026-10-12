import Lean_Code.SchauderTranslates.Lp.LpMeasureScaling

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem lpMeasureScaleEquiv_symm_ae {α : Type*} [MeasurableSpace α]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcfin : c ≠ ∞) (g : Lp ℂ p (c • μ)) :
    (lpMeasureScaleEquiv p μ c hc0 hcfin).symm g =ᵐ[μ]
      fun x => ((c.toReal ^ p.toReal⁻¹ : ℝ) : ℂ) * g x := by
  let b := (lpMeasureScaleEquiv p μ c hc0 hcfin).symm g
  have hf : lpMeasureScaleIsometry p μ c hc0 hcfin b = g :=
    (lpMeasureScaleEquiv p μ c hc0 hcfin).apply_symm_apply g
  have hae := lpMeasureScaleIsometry_ae p μ c hc0 hcfin b
  rw [hf] at hae
  have hK : ((c.toReal ^ p.toReal⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (ENNReal.toReal_pos hc0 hcfin) _).ne'
  filter_upwards [(Measure.absolutelyContinuous_smul hc0).ae_eq hae] with x hx
  change b x = _
  rw [hx, ← mul_assoc, mul_inv_cancel₀ hK, one_mul]

end SchauderTranslates.LpConstruction
