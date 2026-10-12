import Lean_Code.SchauderTranslates.Lp.WeightedHaarStep

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {e : LebesgueLp p}
variable (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

theorem DisjointStepData.wholeCellIsometry_constant_eq :
    D.wholeCellIsometry hp0 hpfin he (haarConstant p) = e := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq D.supportSet_measurable).mp
    (D.weightedCellEquiv_constant_ae hp0 hpfin he)
  have hwhole := (lpExtendByZero_ae p volume D.supportSet D.supportSet_measurable
    (D.weightedCellEquiv hp0 hpfin he (haarConstant p))).trans h
  apply Lp.ext
  filter_upwards [hwhole, D.valueFunction_ae] with x hx hval
  change lpExtendByZero p volume D.supportSet D.supportSet_measurable
    (D.weightedCellEquiv hp0 hpfin he (haarConstant p)) x = e x
  rw [hx, hval]
  by_cases hA : x ∈ D.supportSet
  · exact Set.indicator_of_mem hA _
  · rw [Set.indicator_of_notMem hA, D.valueFunction_zero_outside hA, Complex.ofReal_zero]

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem DisjointStepData.complementAtom_isCompactStep (i : HaarMeanZeroIndex) :
    IsCompactStep p (lpExtendByZero p volume D.supportSet D.supportSet_measurable
      (D.complementAtom (q := q) hp0 hpfin he i).val) := by
  change IsCompactStep p (D.wholeCellIsometry hp0 hpfin he (haarNormalizedAtom p (some i)))
  exact D.wholeCellIsometry_normalized_isCompactStep hp0 hpfin he (some i)

theorem DisjointStepData.complementAtom_supported (i : HaarMeanZeroIndex) :
    SupportedOn (lpExtendByZero p volume D.supportSet D.supportSet_measurable
      (D.complementAtom (q := q) hp0 hpfin he i).val) D.supportSet :=
  lpExtendByZero_supported p volume D.supportSet D.supportSet_measurable _

end SchauderTranslates.LpConstruction
