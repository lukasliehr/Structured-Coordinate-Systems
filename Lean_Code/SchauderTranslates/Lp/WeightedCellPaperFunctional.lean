import Lean_Code.SchauderTranslates.Lp.WeightedCellFunctional

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
variable {e : LebesgueLp p} (D : DisjointStepData p e)
variable (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

/-- The transported functional is exactly the manuscript's norming
functional for the original Lᵖ class, independent of its step representative. -/
theorem DisjointStepData.normingFunctional_original_apply (hp2 : 2 < p)
    (F : Lp ℂ p D.supportMeasure) :
    D.normingFunctional (q := q) hp0 hpfin he F =
      ∫ x, F x * star (e x) * (((‖e x‖ ^ (p.toReal - 2)) : ℝ) : ℂ) ∂D.supportMeasure := by
  rw [D.normingFunctional_apply hp0 hpfin he hp2]
  apply integral_congr_ae
  filter_upwards [Measure.absolutelyContinuous_restrict.ae_eq D.valueFunction_ae] with x hx
  have hval : e x = D.complexValue x := hx
  rw [hval, haarNormingValue, Complex.real_smul]
  ring

end SchauderTranslates.LpConstruction
