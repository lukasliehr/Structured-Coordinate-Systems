import Lean_Code.SchauderTranslates.Lp.CellCoefficientMap
import Lean_Code.SchauderTranslates.Lp.WeightedCellPaperFunctional
import Lean_Code.SchauderTranslates.Lp.WeightedCellRootSteps

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem lpRestriction_eq_zero_of_supported {α : Type*} [MeasurableSpace α]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) {A s : Set α}
    (hs : MeasurableSet s) (F : Lp ℂ p μ) (hF : SupportedOn F A) (hdis : Disjoint A s) :
    lpRestriction p μ s F = 0 := by
  apply Lp.ext
  filter_upwards [lpRestriction_ae p μ s F, ae_restrict_of_ae (s := s) hF,
    ae_restrict_mem hs, Lp.coeFn_zero ℂ p (μ.restrict s)] with x hx hF hsx hz
  rw [hx, hz]
  exact hF (fun hAx => Set.disjoint_left.mp hdis hAx hsx)

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {e : LebesgueLp p} (D : DisjointStepData p e)
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

def DisjointStepData.wholeNormingFunctional : LebesgueLp p →L[ℂ] ℂ :=
  (D.normingFunctional (q := q) hp0 hpfin he).comp (lpRestriction p volume D.supportSet)

theorem DisjointStepData.restriction_self_eq_constant :
    lpRestriction p volume D.supportSet e = D.weightedCellEquiv hp0 hpfin he (haarConstant p) := by
  have hEq := congrArg (lpRestriction p volume D.supportSet)
    (D.wholeCellIsometry_constant_eq hp0 hpfin he)
  exact hEq.symm.trans (lpRestriction_extendByZero p volume D.supportSet D.supportSet_measurable
    (D.weightedCellEquiv hp0 hpfin he (haarConstant p)))

theorem DisjointStepData.wholeNormingFunctional_self :
    D.wholeNormingFunctional (q := q) hp0 hpfin he e = 1 := by
  change D.normingFunctional (q := q) hp0 hpfin he (lpRestriction p volume D.supportSet e) = 1
  rw [D.restriction_self_eq_constant hp0 hpfin he]
  exact D.normingFunctional_constant hp0 hpfin he

theorem DisjointStepData.wholeNormingFunctional_bound (hp1 : 1 < p) (F : LebesgueLp p) :
    ‖D.wholeNormingFunctional (q := q) hp0 hpfin he F‖ ≤ ‖F‖ := by
  change ‖D.normingFunctional (q := q) hp0 hpfin he (lpRestriction p volume D.supportSet F)‖ ≤ _
  have h := (D.normingFunctional (q := q) hp0 hpfin he).le_opNorm (lpRestriction p volume D.supportSet F)
  rw [D.normingFunctional_norm hp0 hpfin he hp1, one_mul] at h
  exact h.trans (lpRestrictToSet_norm_le p volume D.supportSet F)

theorem DisjointStepData.wholeNormingFunctional_norm (hp1 : 1 < p) :
    ‖D.wholeNormingFunctional (q := q) hp0 hpfin he‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro F
    simpa only [one_mul] using D.wholeNormingFunctional_bound hp0 hpfin he hp1 F
  · have h := (D.wholeNormingFunctional (q := q) hp0 hpfin he).le_opNorm e
    rw [D.wholeNormingFunctional_self hp0 hpfin he, norm_one, he, mul_one] at h
    exact h

theorem DisjointStepData.wholeNormingFunctional_original_apply (hp2 : 2 < p) (F : LebesgueLp p) :
    D.wholeNormingFunctional (q := q) hp0 hpfin he F =
      ∫ x, F x * star (e x) * (((‖e x‖ ^ (p.toReal - 2)) : ℝ) : ℂ) ∂D.supportMeasure := by
  change D.normingFunctional (q := q) hp0 hpfin he (lpRestriction p volume D.supportSet F) = _
  rw [D.normingFunctional_original_apply hp0 hpfin he hp2]
  apply integral_congr_ae
  filter_upwards [lpRestriction_ae p volume D.supportSet F] with x hx
  rw [hx]

theorem DisjointStepData.wholeNormingFunctional_zero {A : Set ℝ} (F : LebesgueLp p)
    (hF : SupportedOn F A) (hdis : Disjoint A D.supportSet) :
    D.wholeNormingFunctional (q := q) hp0 hpfin he F = 0 := by
  change D.normingFunctional (q := q) hp0 hpfin he (lpRestriction p volume D.supportSet F) = 0
  rw [lpRestriction_eq_zero_of_supported p volume D.supportSet_measurable F hF hdis, map_zero]

end SchauderTranslates.LpConstruction
