import Lean_Code.SchauderTranslates.Lp.WeightedCellRootSteps
import Lean_Code.SchauderTranslates.Lp.WeightedCellPaperFunctional

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
variable {e : LebesgueLp p} (D : DisjointStepData p e)
variable (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

/-- The norming functional is the actual manuscript integral, its kernel
has the normalized unconditional Haar complement, and every root extends
to a real compact step vector in the whole-line Lebesgue Lᵖ space. -/
def WeightedCellConclusion : Prop :=
  1 ≤ haarStrongConstant q.toReal ∧
  ‖D.normingFunctional (q := q) hp0 hpfin he‖ = 1 ∧
  D.normingFunctional (q := q) hp0 hpfin he
    (D.weightedCellEquiv hp0 hpfin he (haarConstant p)) = 1 ∧
  D.wholeCellIsometry hp0 hpfin he (haarConstant p) = e ∧
  (∀ F : Lp ℂ p D.supportMeasure,
    D.normingFunctional (q := q) hp0 hpfin he F =
      ∫ x, F x * star (e x) * (((‖e x‖ ^ (p.toReal - 2)) : ℝ) : ℂ) ∂D.supportMeasure) ∧
  D.cellComplement (q := q) hp0 hpfin he = (D.normingFunctional (q := q) hp0 hpfin he).ker ∧
  NormalizedUnconditionalSystem (D.complementAtom (q := q) hp0 hpfin he)
    (D.complementCoordinate (q := q) hp0 hpfin he) (haarStrongConstant q.toReal) ∧
  ∀ i : HaarMeanZeroIndex,
    IsCompactStep p (lpExtendByZero p volume D.supportSet D.supportSet_measurable
      (D.complementAtom (q := q) hp0 hpfin he i).val) ∧
    SupportedOn (lpExtendByZero p volume D.supportSet D.supportSet_measurable
      (D.complementAtom (q := q) hp0 hpfin he i).val) D.supportSet

theorem weighted_cell_conclusion (hp2 : 2 < p) : WeightedCellConclusion p q D hp0 hpfin he := by
  refine ⟨haarStrongConstant_ge_one (q := q) hp2 hpfin,
    D.normingFunctional_norm hp0 hpfin he (lt_trans (by norm_num) hp2),
    D.normingFunctional_constant hp0 hpfin he,
    D.wholeCellIsometry_constant_eq hp0 hpfin he,
    D.normingFunctional_original_apply hp0 hpfin he hp2,
    D.cellComplement_eq_ker hp0 hpfin he,
    D.complement_system hp0 hpfin he hp2, ?_⟩
  intro i
  exact ⟨D.complementAtom_isCompactStep hp0 hpfin he i, D.complementAtom_supported hp0 hpfin he i⟩

/-- Blueprint `lp:weighted-cell`. All cell data are constructed from the
given real compact step vector. The exponent and its conjugate are the
actual finite Lebesgue Lᵖ exponents, with no additional cell hypothesis. -/
theorem weighted_cell_basis (p : ℝ≥0∞) (hp2 : 2 < p) (hpfin : p ≠ ∞) :
    letI : Fact (1 ≤ p) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp2.le⟩
    letI : Fact (1 ≤ ENNReal.conjExponent p) :=
      ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
    ∀ (e : LebesgueLp p), IsCompactStep p e → ∀ (he : ‖e‖ = 1),
      ∃ D : DisjointStepData p e,
        WeightedCellConclusion p (ENNReal.conjExponent p) D
          (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin he := by
  let : Fact (1 ≤ p) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp2.le⟩
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  intro e heStep he
  obtain ⟨D⟩ := heStep.disjoint_data
  exact ⟨D, weighted_cell_conclusion p (ENNReal.conjExponent p) D _ hpfin he hp2⟩

end SchauderTranslates.LpConstruction
