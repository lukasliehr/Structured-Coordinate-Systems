import Lean_Code.SchauderTranslates.Lp.WeightedCell

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
variable {e : LebesgueLp p} (D : DisjointStepData p e)
variable (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

def DisjointStepData.fullCellEquiv :
    HaarLp p ≃ₗᵢ[ℂ] supportedLpSubmodule p volume D.supportSet :=
  (D.weightedCellEquiv hp0 hpfin he).trans
    (lpSupportedEquiv p volume D.supportSet D.supportSet_measurable)

def DisjointStepData.fullCellAtom (i : HaarIndex) : supportedLpSubmodule p volume D.supportSet :=
  D.fullCellEquiv hp0 hpfin he (haarNormalizedAtom p i)

def DisjointStepData.fullCellCoordinate (i : HaarIndex) :
    supportedLpSubmodule p volume D.supportSet →L[ℂ] ℂ :=
  (haarNormalizedCoordinate p q i).comp
    ((D.fullCellEquiv hp0 hpfin he).symm : supportedLpSubmodule p volume D.supportSet →L[ℂ] HaarLp p)

theorem DisjointStepData.fullCell_system (hp2 : 2 < p) :
    NormalizedUnconditionalSystem (D.fullCellAtom hp0 hpfin he)
      (D.fullCellCoordinate (q := q) hp0 hpfin he) (haarStrongConstant q.toReal) := by
  apply normalized_unconditional_system_transport (D.fullCellEquiv hp0 hpfin he)
  exact (haar_basis_conclusion p q hp2 hpfin).2.1

theorem DisjointStepData.fullCellAtom_isCompactStep (i : HaarIndex) :
    IsCompactStep p (D.fullCellAtom hp0 hpfin he i).val := by
  change IsCompactStep p (D.wholeCellIsometry hp0 hpfin he (haarNormalizedAtom p i))
  exact D.wholeCellIsometry_normalized_isCompactStep hp0 hpfin he i

theorem DisjointStepData.fullCellCoordinate_atom (i j : HaarIndex) :
    D.fullCellCoordinate (q := q) hp0 hpfin he i (D.fullCellAtom hp0 hpfin he j) =
      if i = j then 1 else 0 := by
  simp [fullCellCoordinate, fullCellAtom, haarNormalizedCoordinate_atom]

def DisjointStepData.wholeComplementIsometry :
    D.cellComplement (q := q) hp0 hpfin he →ₗᵢ[ℂ] LebesgueLp p :=
  (lpExtendByZeroIsometry p volume D.supportSet D.supportSet_measurable).comp
    (D.cellComplement (q := q) hp0 hpfin he).subtypeₗᵢ

def DisjointStepData.wholeComplementSpace : Submodule ℂ (LebesgueLp p) :=
  (D.wholeComplementIsometry (q := q) hp0 hpfin he).toLinearMap.range

def DisjointStepData.wholeComplementEquiv :
    D.cellComplement (q := q) hp0 hpfin he ≃ₗᵢ[ℂ] D.wholeComplementSpace (q := q) hp0 hpfin he :=
  (D.wholeComplementIsometry (q := q) hp0 hpfin he).equivRange

def DisjointStepData.wholeComplementAtom (i : HaarMeanZeroIndex) :
    D.wholeComplementSpace (q := q) hp0 hpfin he :=
  D.wholeComplementEquiv (q := q) hp0 hpfin he (D.complementAtom (q := q) hp0 hpfin he i)

def DisjointStepData.wholeComplementCoordinate (i : HaarMeanZeroIndex) :
    D.wholeComplementSpace (q := q) hp0 hpfin he →L[ℂ] ℂ :=
  (D.complementCoordinate (q := q) hp0 hpfin he i).comp
    ((D.wholeComplementEquiv (q := q) hp0 hpfin he).symm :
      D.wholeComplementSpace (q := q) hp0 hpfin he →L[ℂ] D.cellComplement (q := q) hp0 hpfin he)

theorem DisjointStepData.wholeComplement_system (hp2 : 2 < p) :
    NormalizedUnconditionalSystem (D.wholeComplementAtom (q := q) hp0 hpfin he)
      (D.wholeComplementCoordinate (q := q) hp0 hpfin he) (haarStrongConstant q.toReal) := by
  apply normalized_unconditional_system_transport (D.wholeComplementEquiv (q := q) hp0 hpfin he)
  exact D.complement_system hp0 hpfin he hp2

theorem DisjointStepData.wholeComplementAtom_isCompactStep (i : HaarMeanZeroIndex) :
    IsCompactStep p (D.wholeComplementAtom (q := q) hp0 hpfin he i).val := by
  exact D.complementAtom_isCompactStep hp0 hpfin he i

theorem DisjointStepData.wholeComplementCoordinate_atom (i j : HaarMeanZeroIndex) :
    D.wholeComplementCoordinate (q := q) hp0 hpfin he i
      (D.wholeComplementAtom (q := q) hp0 hpfin he j) = if i = j then 1 else 0 := by
  simp [wholeComplementCoordinate, wholeComplementAtom, complementCoordinate, complementAtom,
    haarMeanZeroCoordinate_atom]

theorem DisjointStepData.wholeComplementSpace_supported
    (F : D.wholeComplementSpace (q := q) hp0 hpfin he) : SupportedOn F.val D.supportSet := by
  obtain ⟨f, hf⟩ := F.property
  rw [← hf]
  exact lpExtendByZero_supported p volume D.supportSet D.supportSet_measurable _

end SchauderTranslates.LpConstruction
