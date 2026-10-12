import Lean_Code.SchauderTranslates.Lp.PositiveMassPartition

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem DisjointStepData.ordered_mass_sum {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) :
    ∑ i : Fin D.cells.card, D.mass (D.cellOrdering i).val = ∑ ab ∈ D.cells, D.mass ab := by
  rw [D.cellOrdering.sum_comp (fun ab : D.cells => D.mass ab.val), Finset.sum_coe_sort]

/-- The interval partition is derived from the actual norm-one step vector,
with each target interval having exactly its corresponding weighted mass. -/
def DisjointStepData.massPartition {p : ℝ≥0∞} [Fact (1 ≤ p)] {e : LebesgueLp p}
    (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1) :
    PositiveMassPartition D.cells.card where
  mass i := D.mass (D.cellOrdering i).val
  mass_pos i := D.mass_pos (D.cellOrdering i).property
  total := by rw [D.ordered_mass_sum, D.mass_sum_one hp0 hpfin he]

theorem DisjointStepData.massPartition_cell_length {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {e : LebesgueLp p} (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (he : ‖e‖ = 1) (i : Fin D.cells.card) :
    (D.massPartition hp0 hpfin he).endpoint (i.val + 1) -
      (D.massPartition hp0 hpfin he).endpoint i.val = D.mass (D.cellOrdering i).val := by
  rw [(D.massPartition hp0 hpfin he).endpoint_succ i.isLt]
  simp [massPartition]

end SchauderTranslates.LpConstruction
