import Lean_Code.SchauderTranslates.Lp.StepCellSupport

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def DisjointStepData.weight {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) :
    ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (|D.valueFunction x| ^ p.toReal)

def DisjointStepData.weightedMeasure {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) :
    Measure ℝ := volume.withDensity D.weight

theorem DisjointStepData.weight_measurable {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : Measurable D.weight :=
  (D.valueFunction_measurable.abs.pow_const _).ennreal_ofReal

theorem DisjointStepData.weight_ae_norm {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e) :
    D.weight =ᵐ[volume] fun x => ENNReal.ofReal (‖e x‖ ^ p.toReal) := by
  filter_upwards [D.valueFunction_ae] with x hx
  rw [hx]
  simp [DisjointStepData.weight, Complex.norm_real, Real.norm_eq_abs]

theorem DisjointStepData.weightedMeasure_cell {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) {ab : ℝ × ℝ} (hab : ab ∈ D.cells) :
    D.weightedMeasure (Set.Ico ab.1 ab.2) = ENNReal.ofReal (D.mass ab) := by
  rw [DisjointStepData.weightedMeasure, withDensity_apply _ measurableSet_Ico]
  have hconst : D.weight =ᵐ[volume.restrict (Set.Ico ab.1 ab.2)]
      fun _ => ENNReal.ofReal (|D.value ab| ^ p.toReal) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ico] with x hx
    change ENNReal.ofReal (|D.valueFunction x| ^ p.toReal) = _
    rw [D.valueFunction_on_cell hab hx]
  rw [lintegral_congr_ae hconst, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ico, ← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg _) _)]
  rfl

theorem DisjointStepData.weightedMeasure_univ {p : ℝ≥0∞} [Fact (1 ≤ p)] {e : LebesgueLp p}
    (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    D.weightedMeasure Set.univ = ENNReal.ofReal (‖e‖ ^ p.toReal) := by
  rw [DisjointStepData.weightedMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_congr_ae D.weight_ae_norm,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow e hp0 hpfin)
      (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _),
    integral_norm_rpow e hp0 hpfin]

/-- The positive step density has total mass one for every normalized
compact step vector. Its cell masses are the positive numbers already
computed in the actual Lebesgue Lᵖ norm. -/
theorem DisjointStepData.weightedMeasure_probability {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {e : LebesgueLp p} (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1) :
    IsProbabilityMeasure D.weightedMeasure := by
  constructor
  rw [D.weightedMeasure_univ hp0 hpfin, he, Real.one_rpow, ENNReal.ofReal_one]

end SchauderTranslates.LpConstruction
