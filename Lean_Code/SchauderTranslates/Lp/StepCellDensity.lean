import Lean_Code.SchauderTranslates.Lp.StepCellMeasureTransport
import Lean_Code.SchauderTranslates.Lp.LpMeasureCongr

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def DisjointStepData.supportMeasure {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : Measure ℝ := volume.restrict D.supportSet

def DisjointStepData.complexValue {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : ℝ → ℂ := fun x => D.valueFunction x

theorem DisjointStepData.complexValue_measurable {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : Measurable D.complexValue :=
  Complex.continuous_ofReal.measurable.comp D.valueFunction_measurable

theorem DisjointStepData.complexValue_ne_zero_ae {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : ∀ᵐ x ∂D.supportMeasure, D.complexValue x ≠ 0 := by
  filter_upwards [ae_restrict_mem (μ := volume) D.supportSet_measurable] with x hx
  exact Complex.ofReal_ne_zero.mpr ((D.valueFunction_ne_zero_iff x).mpr hx)

theorem DisjointStepData.powerDensity_eq_weight {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : lpPowerDensity p D.complexValue = D.weight := by
  funext x
  rw [lpPowerDensity, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]
  simp [complexValue, weight, Complex.norm_real, Real.norm_eq_abs]

theorem DisjointStepData.densityMeasure_eq {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    D.weightedMeasure = D.supportMeasure.withDensity (lpPowerDensity p D.complexValue) := by
  rw [D.powerDensity_eq_weight, supportMeasure, ← restrict_withDensity D.supportSet_measurable]
  exact (Measure.restrict_eq_self_of_ae_mem (D.weightedMeasure_ae_support hp0 hpfin)).symm

theorem DisjointStepData.supportMeasure_ac_weightedMeasure {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    D.supportMeasure ≪ D.weightedMeasure := by
  rw [D.densityMeasure_eq hp0 hpfin]
  exact lpPowerDensity_reverse_ac p D.complexValue_measurable D.complexValue_ne_zero_ae

end SchauderTranslates.LpConstruction
