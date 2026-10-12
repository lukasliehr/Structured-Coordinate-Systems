import Lean_Code.SchauderTranslates.Lp.WeightedCellFunctional
import Lean_Code.SchauderTranslates.Lp.HaarBasis

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
variable {e : LebesgueLp p} (D : DisjointStepData p e)
variable (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

def DisjointStepData.cellComplement : Submodule ℂ (Lp ℂ p D.supportMeasure) :=
  (haarMeanZero p q).map (D.weightedCellEquiv hp0 hpfin he).toLinearMap

theorem DisjointStepData.cellComplement_mem_functional (F : Lp ℂ p D.supportMeasure) :
    F ∈ D.cellComplement (q := q) hp0 hpfin he ↔
      D.normingFunctional (q := q) hp0 hpfin he F = 0 := by
  rw [cellComplement, Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    change D.normingFunctional (q := q) hp0 hpfin he (D.weightedCellEquiv hp0 hpfin he f) = 0
    rw [D.normingFunctional_image hp0 hpfin he]
    exact (haarMeanZero_mem_iff p q f).mp hf
  · intro hF
    refine ⟨(D.weightedCellEquiv hp0 hpfin he).symm F, ?_,
      (D.weightedCellEquiv hp0 hpfin he).apply_symm_apply F⟩
    change haarIntegral p q ((D.weightedCellEquiv hp0 hpfin he).symm F) = 0
    exact hF

theorem DisjointStepData.cellComplement_eq_ker :
    D.cellComplement (q := q) hp0 hpfin he = (D.normingFunctional (q := q) hp0 hpfin he).ker := by
  ext F
  exact D.cellComplement_mem_functional hp0 hpfin he F

theorem DisjointStepData.cellComplement_mem_iff (hp2 : 2 < p) (F : Lp ℂ p D.supportMeasure) :
    F ∈ D.cellComplement (q := q) hp0 hpfin he ↔
      (∫ x, F x * haarNormingValue p.toReal (D.complexValue x) ∂D.supportMeasure) = 0 := by
  rw [D.cellComplement_mem_functional hp0 hpfin he,
    D.normingFunctional_apply hp0 hpfin he hp2]

def DisjointStepData.cellComplementEquiv :
    haarMeanZero p q ≃ₗᵢ[ℂ] D.cellComplement (q := q) hp0 hpfin he :=
  LinearIsometryEquiv.submoduleMap (haarMeanZero p q) (D.weightedCellEquiv hp0 hpfin he)

def DisjointStepData.complementAtom (i : HaarMeanZeroIndex) : D.cellComplement (q := q) hp0 hpfin he :=
  D.cellComplementEquiv (q := q) hp0 hpfin he (haarMeanZeroAtom p q i)

def DisjointStepData.complementCoordinate (i : HaarMeanZeroIndex) :
    D.cellComplement (q := q) hp0 hpfin he →L[ℂ] ℂ :=
  (haarMeanZeroCoordinate p q i).comp
    ((D.cellComplementEquiv (q := q) hp0 hpfin he).symm :
      D.cellComplement (q := q) hp0 hpfin he →L[ℂ] haarMeanZero p q)

theorem DisjointStepData.complement_system (hp2 : 2 < p) :
    NormalizedUnconditionalSystem (D.complementAtom (q := q) hp0 hpfin he)
      (D.complementCoordinate (q := q) hp0 hpfin he) (haarStrongConstant q.toReal) := by
  apply normalized_unconditional_system_transport
    (D.cellComplementEquiv (q := q) hp0 hpfin he)
  exact (haar_basis_conclusion p q hp2 hpfin).2.2.1

end SchauderTranslates.LpConstruction
