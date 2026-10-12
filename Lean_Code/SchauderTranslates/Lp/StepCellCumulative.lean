import Lean_Code.SchauderTranslates.Lp.StepCellAffine

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {e : LebesgueLp p}
variable (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

def DisjointStepData.cumulativeMap : ℝ → ℝ := fun x =>
  ∑ i : Fin D.cells.card, (D.sourceCell i).indicator (D.cellMap hp0 hpfin he i) x

def DisjointStepData.inverseCumulative : ℝ → ℝ := fun y =>
  ∑ i : Fin D.cells.card, ((D.massPartition hp0 hpfin he).cell i).indicator
    (D.cellMap hp0 hpfin he i).symm y

theorem DisjointStepData.cumulativeMap_measurable : Measurable (D.cumulativeMap hp0 hpfin he) := by
  apply Finset.measurable_sum
  intro i _
  exact (D.cellMap hp0 hpfin he i).measurable.indicator measurableSet_Ico

theorem DisjointStepData.inverseCumulative_measurable :
    Measurable (D.inverseCumulative hp0 hpfin he) := by
  apply Finset.measurable_sum
  intro i _
  exact (D.cellMap hp0 hpfin he i).symm.measurable.indicator measurableSet_Ico

theorem DisjointStepData.cumulativeMap_on_cell (i : Fin D.cells.card) {x : ℝ}
    (hx : x ∈ D.sourceCell i) :
    D.cumulativeMap hp0 hpfin he x = D.cellMap hp0 hpfin he i x := by
  change (∑ j : Fin D.cells.card, (D.sourceCell j).indicator (D.cellMap hp0 hpfin he j) x) = _
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx _
  · intro j _ hji
    exact Set.indicator_of_notMem
      (fun hxj => Set.disjoint_left.mp (D.sourceCell_disjoint hji) hxj hx) _
  · simp

theorem DisjointStepData.inverseCumulative_on_cell (i : Fin D.cells.card) {y : ℝ}
    (hy : y ∈ (D.massPartition hp0 hpfin he).cell i) :
    D.inverseCumulative hp0 hpfin he y = (D.cellMap hp0 hpfin he i).symm y := by
  change (∑ j : Fin D.cells.card, ((D.massPartition hp0 hpfin he).cell j).indicator
    (D.cellMap hp0 hpfin he j).symm y) = _
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hy _
  · intro j _ hji
    exact Set.indicator_of_notMem
      (fun hyj => Set.disjoint_left.mp ((D.massPartition hp0 hpfin he).cells_disjoint hji)
        hyj hy) _
  · simp

theorem DisjointStepData.cumulativeMap_mem_unit {x : ℝ} (hx : x ∈ D.supportSet) :
    D.cumulativeMap hp0 hpfin he x ∈ Set.Ico (0 : ℝ) 1 := by
  rw [← D.sourceCell_union] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [D.cumulativeMap_on_cell hp0 hpfin he i hi]
  exact (D.massPartition hp0 hpfin he).cell_subset_unit i
    ((D.cellMap_mem_iff hp0 hpfin he i x).mpr hi)

theorem DisjointStepData.inverseCumulative_mem_support {y : ℝ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1) : D.inverseCumulative hp0 hpfin he y ∈ D.supportSet := by
  obtain ⟨i, hi⟩ := (D.massPartition hp0 hpfin he).cells_cover_unit hy
  rw [D.inverseCumulative_on_cell hp0 hpfin he i hi, ← D.sourceCell_union]
  exact Set.mem_iUnion.mpr ⟨i, (D.cellMap_symm_mem_iff hp0 hpfin he i y).mpr hi⟩

theorem DisjointStepData.inverseCumulative_cumulativeMap {x : ℝ}
    (hx : x ∈ D.supportSet) :
    D.inverseCumulative hp0 hpfin he (D.cumulativeMap hp0 hpfin he x) = x := by
  rw [← D.sourceCell_union] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  rw [D.cumulativeMap_on_cell hp0 hpfin he i hi,
    D.inverseCumulative_on_cell hp0 hpfin he i ((D.cellMap_mem_iff hp0 hpfin he i x).mpr hi)]
  exact (D.cellMap hp0 hpfin he i).symm_apply_apply x

theorem DisjointStepData.cumulativeMap_inverseCumulative {y : ℝ}
    (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    D.cumulativeMap hp0 hpfin he (D.inverseCumulative hp0 hpfin he y) = y := by
  obtain ⟨i, hi⟩ := (D.massPartition hp0 hpfin he).cells_cover_unit hy
  rw [D.inverseCumulative_on_cell hp0 hpfin he i hi,
    D.cumulativeMap_on_cell hp0 hpfin he i ((D.cellMap_symm_mem_iff hp0 hpfin he i y).mpr hi)]
  exact (D.cellMap hp0 hpfin he i).apply_symm_apply y

end SchauderTranslates.LpConstruction
