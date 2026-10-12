import Lean_Code.SchauderTranslates.Lp.StepCellMeasurePieces

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {e : LebesgueLp p}
variable (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

def DisjointStepData.cellMap (i : Fin D.cells.card) : ℝ ≃ᵐ ℝ :=
  affineCell (D.cellOrdering i).val.1 ((D.massPartition hp0 hpfin he).endpoint i.val)
    (D.cellDensity i) (D.cellDensity_pos i)

theorem DisjointStepData.targetEndpoint_eq (i : Fin D.cells.card) :
    (D.massPartition hp0 hpfin he).endpoint (i.val + 1) =
      (D.massPartition hp0 hpfin he).endpoint i.val +
        D.cellDensity i * ((D.cellOrdering i).val.2 - (D.cellOrdering i).val.1) := by
  rw [(D.massPartition hp0 hpfin he).endpoint_succ i.isLt]
  rfl

theorem DisjointStepData.cellMap_preimage (i : Fin D.cells.card) :
    (D.cellMap hp0 hpfin he i) ⁻¹' (D.massPartition hp0 hpfin he).cell i = D.sourceCell i := by
  rw [PositiveMassPartition.cell, D.targetEndpoint_eq hp0 hpfin he i]
  exact affineCell_preimage _ _ _ _ _

theorem DisjointStepData.cellMap_mem_iff (i : Fin D.cells.card) (x : ℝ) :
    D.cellMap hp0 hpfin he i x ∈ (D.massPartition hp0 hpfin he).cell i ↔
      x ∈ D.sourceCell i := by
  change x ∈ (D.cellMap hp0 hpfin he i) ⁻¹' (D.massPartition hp0 hpfin he).cell i ↔
    x ∈ D.sourceCell i
  rw [D.cellMap_preimage hp0 hpfin he]

theorem DisjointStepData.cellMap_symm_mem_iff (i : Fin D.cells.card) (y : ℝ) :
    (D.cellMap hp0 hpfin he i).symm y ∈ D.sourceCell i ↔
      y ∈ (D.massPartition hp0 hpfin he).cell i := by
  rw [← D.cellMap_mem_iff hp0 hpfin he i]
  simp

theorem DisjointStepData.cellMap_measurePreserving (i : Fin D.cells.card) :
    MeasurePreserving (D.cellMap hp0 hpfin he i)
      (ENNReal.ofReal (D.cellDensity i) • volume.restrict (D.sourceCell i))
      (volume.restrict ((D.massPartition hp0 hpfin he).cell i)) := by
  rw [PositiveMassPartition.cell, D.targetEndpoint_eq hp0 hpfin he i]
  exact affineCell_measurePreserving _ _ _ _ _

end SchauderTranslates.LpConstruction
