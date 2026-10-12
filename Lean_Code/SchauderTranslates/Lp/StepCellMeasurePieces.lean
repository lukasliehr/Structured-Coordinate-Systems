import Lean_Code.SchauderTranslates.Lp.StepCellMassPartition
import Lean_Code.SchauderTranslates.Lp.AffineCellMeasure

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def DisjointStepData.sourceCell {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e)
    (i : Fin D.cells.card) : Set ℝ :=
  Set.Ico (D.cellOrdering i).val.1 (D.cellOrdering i).val.2

def DisjointStepData.cellDensity {p : ℝ≥0∞} {e : LebesgueLp p} (D : DisjointStepData p e)
    (i : Fin D.cells.card) : ℝ := |D.value (D.cellOrdering i).val| ^ p.toReal

theorem DisjointStepData.cellDensity_pos {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (i : Fin D.cells.card) : 0 < D.cellDensity i :=
  Real.rpow_pos_of_pos (abs_pos.mpr (D.value_ne_zero _ (D.cellOrdering i).property)) _

theorem DisjointStepData.sourceCell_disjoint {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) {i j : Fin D.cells.card} (hij : i ≠ j) :
    Disjoint (D.sourceCell i) (D.sourceCell j) :=
  D.disjoint _ (D.cellOrdering i).property _ (D.cellOrdering j).property
    (fun h => hij (D.cellOrdering.injective (Subtype.ext h)))

theorem DisjointStepData.sourceCell_union {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : (⋃ i : Fin D.cells.card, D.sourceCell i) = D.supportSet := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨(D.cellOrdering i).val,
      Set.mem_iUnion.mpr ⟨(D.cellOrdering i).property, hi⟩⟩
  · intro hx
    obtain ⟨ab, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hab, hxab⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨D.cellOrdering.symm ⟨ab, hab⟩, ?_⟩
    simpa [sourceCell] using hxab

theorem DisjointStepData.weightedMeasure_restrict_cell {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (i : Fin D.cells.card) :
    D.weightedMeasure.restrict (D.sourceCell i) =
      ENNReal.ofReal (D.cellDensity i) • volume.restrict (D.sourceCell i) := by
  rw [weightedMeasure, restrict_withDensity
    (show MeasurableSet (D.sourceCell i) from measurableSet_Ico)]
  have hconst : D.weight =ᵐ[volume.restrict (D.sourceCell i)]
      fun _ => ENNReal.ofReal (D.cellDensity i) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ico] with x hx
    change ENNReal.ofReal (|D.valueFunction x| ^ p.toReal) = _
    rw [D.valueFunction_on_cell (D.cellOrdering i).property hx]
    rfl
  rw [withDensity_congr_ae hconst, withDensity_const]

theorem DisjointStepData.weightedMeasure_ae_support {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    ∀ᵐ x ∂D.weightedMeasure, x ∈ D.supportSet := by
  rw [weightedMeasure, ae_withDensity_iff_ae_restrict D.weight_measurable]
  filter_upwards [ae_restrict_mem (μ := volume)
    (D.weight_measurable (measurableSet_singleton 0)).compl] with x hx
  by_contra hout
  have hzero : D.weight x = 0 := by
    rw [weight, D.valueFunction_zero_outside hout, abs_zero,
      Real.zero_rpow (ENNReal.toReal_pos hp0 hpfin).ne', ENNReal.ofReal_zero]
  exact hx hzero

theorem DisjointStepData.weightedMeasure_pieces {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) :
    D.weightedMeasure = ∑ i : Fin D.cells.card,
      ENNReal.ofReal (D.cellDensity i) • volume.restrict (D.sourceCell i) := by
  calc
    D.weightedMeasure = D.weightedMeasure.restrict D.supportSet :=
      (Measure.restrict_eq_self_of_ae_mem (D.weightedMeasure_ae_support hp0 hpfin)).symm
    _ = ∑ i : Fin D.cells.card, D.weightedMeasure.restrict (D.sourceCell i) := by
      rw [← D.sourceCell_union, Measure.restrict_iUnion
        (fun _ _ hij => D.sourceCell_disjoint hij) (fun _ => measurableSet_Ico),
        Measure.sum_fintype]
    _ = _ := Finset.sum_congr rfl (fun i _ => D.weightedMeasure_restrict_cell i)

theorem PositiveMassPartition.unitMeasure_pieces {N : ℕ} (P : PositiveMassPartition N) :
    haarMeasure = ∑ i : Fin N, volume.restrict (P.cell i) := by
  rw [haarMeasure, ← P.cells_union, Measure.restrict_iUnion
    (fun _ _ hij => P.cells_disjoint hij) (fun _ => measurableSet_Ico), Measure.sum_fintype]

end SchauderTranslates.LpConstruction
