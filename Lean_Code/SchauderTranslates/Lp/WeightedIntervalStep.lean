import Lean_Code.SchauderTranslates.Lp.WeightedCellIsometry
import Lean_Code.SchauderTranslates.Lp.IndexedIntervalStep
import Lean_Code.SchauderTranslates.Lp.AffineIntervalPreimage

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {e : LebesgueLp p}
variable (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

def DisjointStepData.preimageInterval (l u : ℝ) (i : Fin D.cells.card) : ℝ × ℝ :=
  (max (D.cellOrdering i).val.1 ((D.cellMap hp0 hpfin he i).symm l),
    min (D.cellOrdering i).val.2 ((D.cellMap hp0 hpfin he i).symm u))

theorem DisjointStepData.preimageInterval_set (l u : ℝ) (i : Fin D.cells.card) :
    Set.Ico (D.preimageInterval hp0 hpfin he l u i).1
      (D.preimageInterval hp0 hpfin he l u i).2 =
      D.sourceCell i ∩ (D.cellMap hp0 hpfin he i) ⁻¹' Set.Ico l u := by
  rw [preimageInterval, ← Set.Ico_inter_Ico]
  rw [cellMap, affineCell_preimage_Ico]
  rfl

theorem DisjointStepData.preimageInterval_mem_iff (l u : ℝ) (i : Fin D.cells.card) (x : ℝ) :
    x ∈ Set.Ico (D.preimageInterval hp0 hpfin he l u i).1
      (D.preimageInterval hp0 hpfin he l u i).2 ↔
      x ∈ D.sourceCell i ∧ D.cellMap hp0 hpfin he i x ∈ Set.Ico l u := by
  rw [D.preimageInterval_set hp0 hpfin he l u i]
  rfl

theorem DisjointStepData.preimageInterval_subset_source (l u : ℝ) (i : Fin D.cells.card) :
    Set.Ico (D.preimageInterval hp0 hpfin he l u i).1
      (D.preimageInterval hp0 hpfin he l u i).2 ⊆ D.sourceCell i := by
  rw [D.preimageInterval_set hp0 hpfin he]
  exact Set.inter_subset_left

def DisjointStepData.weightedIntervalStep (l u : ℝ) : LebesgueLp p :=
  indexedIntervalStep p (D.preimageInterval hp0 hpfin he l u)
    (fun i => D.value (D.cellOrdering i).val)

theorem DisjointStepData.weightedIntervalStep_isCompactStep (l u : ℝ) :
    IsCompactStep p (D.weightedIntervalStep hp0 hpfin he l u) := indexedIntervalStep_isCompactStep _ _ _

theorem DisjointStepData.weightedIntervalStep_supported (l u : ℝ) :
    SupportedOn (D.weightedIntervalStep hp0 hpfin he l u) D.supportSet := by
  apply indexedIntervalStep_supported
  intro i x hx
  rw [← D.sourceCell_union]
  exact Set.mem_iUnion.mpr ⟨i, D.preimageInterval_subset_source hp0 hpfin he l u i hx⟩

theorem DisjointStepData.weightedIntervalStep_value_on_cell (l u : ℝ) (i : Fin D.cells.card)
    {x : ℝ} (hx : x ∈ D.sourceCell i) :
    (∑ j : Fin D.cells.card, (D.value (D.cellOrdering j).val : ℂ) *
      (Set.Ico (D.preimageInterval hp0 hpfin he l u j).1
        (D.preimageInterval hp0 hpfin he l u j).2).indicator (fun _ => (1 : ℂ)) x) =
      D.complexValue x * (Set.Ico l u).indicator (fun _ => (1 : ℂ))
        (D.cumulativeMap hp0 hpfin he x) := by
  classical
  rw [Finset.sum_eq_single i]
  · have hiff : x ∈ Set.Ico (D.preimageInterval hp0 hpfin he l u i).1
        (D.preimageInterval hp0 hpfin he l u i).2 ↔
        D.cumulativeMap hp0 hpfin he x ∈ Set.Ico l u := by
      rw [D.preimageInterval_mem_iff hp0 hpfin he,
        D.cumulativeMap_on_cell hp0 hpfin he i hx]
      simp only [hx, true_and]
    have hv : D.complexValue x = (D.value (D.cellOrdering i).val : ℂ) := by
      rw [complexValue, D.valueFunction_on_cell (D.cellOrdering i).property hx]
    rw [hv]
    by_cases h : D.cumulativeMap hp0 hpfin he x ∈ Set.Ico l u
    · simp [h, hiff.mpr h]
    · simp [h, mt hiff.mp h]
  · intro j _ hji
    have hout : x ∉ Set.Ico (D.preimageInterval hp0 hpfin he l u j).1
        (D.preimageInterval hp0 hpfin he l u j).2 := fun hj =>
      Set.disjoint_left.mp (D.sourceCell_disjoint hji)
        (D.preimageInterval_subset_source hp0 hpfin he l u j hj) hx
    simp [hout]
  · simp

theorem DisjointStepData.weightedIntervalStep_ae (l u : ℝ) :
    D.weightedIntervalStep hp0 hpfin he l u =ᵐ[volume]
      D.supportSet.indicator (fun x => D.complexValue x *
        (Set.Ico l u).indicator (fun _ => (1 : ℂ)) (D.cumulativeMap hp0 hpfin he x)) := by
  filter_upwards [indexedIntervalStep_ae p (D.preimageInterval hp0 hpfin he l u)
    (fun i => D.value (D.cellOrdering i).val)] with x hx
  change indexedIntervalStep p (D.preimageInterval hp0 hpfin he l u) _ x = _
  rw [hx]
  by_cases hA : x ∈ D.supportSet
  · rw [Set.indicator_of_mem hA]
    rw [← D.sourceCell_union] at hA
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hA
    exact D.weightedIntervalStep_value_on_cell hp0 hpfin he l u i hi
  · rw [Set.indicator_of_notMem hA]
    apply Finset.sum_eq_zero
    intro i _
    have hout : x ∉ Set.Ico (D.preimageInterval hp0 hpfin he l u i).1
        (D.preimageInterval hp0 hpfin he l u i).2 := by
      intro hx
      apply hA
      rw [← D.sourceCell_union]
      exact Set.mem_iUnion.mpr ⟨i, D.preimageInterval_subset_source hp0 hpfin he l u i hx⟩
    simp [hout]

end SchauderTranslates.LpConstruction
