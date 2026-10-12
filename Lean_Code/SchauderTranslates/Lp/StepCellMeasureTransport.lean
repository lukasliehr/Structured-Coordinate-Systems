import Lean_Code.SchauderTranslates.Lp.StepCellCumulative

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {e : LebesgueLp p}
variable (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

theorem DisjointStepData.cumulativeMap_cell_map (i : Fin D.cells.card) :
    Measure.map (D.cumulativeMap hp0 hpfin he)
      (ENNReal.ofReal (D.cellDensity i) • volume.restrict (D.sourceCell i)) =
      volume.restrict ((D.massPartition hp0 hpfin he).cell i) := by
  have hAE : D.cumulativeMap hp0 hpfin he =ᵐ[
      ENNReal.ofReal (D.cellDensity i) • volume.restrict (D.sourceCell i)]
      D.cellMap hp0 hpfin he i := Measure.smul_absolutelyContinuous.ae_eq (by
    filter_upwards [ae_restrict_mem (μ := volume)
      (show MeasurableSet (D.sourceCell i) from measurableSet_Ico)] with x hx
    exact D.cumulativeMap_on_cell hp0 hpfin he i hx)
  rw [Measure.map_congr hAE]
  exact (D.cellMap_measurePreserving hp0 hpfin he i).map_eq

theorem DisjointStepData.inverseCumulative_cell_map (i : Fin D.cells.card) :
    Measure.map (D.inverseCumulative hp0 hpfin he)
      (volume.restrict ((D.massPartition hp0 hpfin he).cell i)) =
      ENNReal.ofReal (D.cellDensity i) • volume.restrict (D.sourceCell i) := by
  have hAE : D.inverseCumulative hp0 hpfin he =ᵐ[
      volume.restrict ((D.massPartition hp0 hpfin he).cell i)]
      (D.cellMap hp0 hpfin he i).symm := by
    filter_upwards [ae_restrict_mem (μ := volume)
      (show MeasurableSet ((D.massPartition hp0 hpfin he).cell i) from measurableSet_Ico)]
      with y hy
    exact D.inverseCumulative_on_cell hp0 hpfin he i hy
  rw [Measure.map_congr hAE]
  exact (D.cellMap_measurePreserving hp0 hpfin he i).symm.map_eq

theorem DisjointStepData.cumulativeMap_measurePreserving :
    MeasurePreserving (D.cumulativeMap hp0 hpfin he) D.weightedMeasure haarMeasure := by
  constructor
  · exact D.cumulativeMap_measurable hp0 hpfin he
  · rw [D.weightedMeasure_pieces hp0 hpfin,
      Measure.map_finset_sum' (D.cumulativeMap_measurable hp0 hpfin he).aemeasurable,
      (D.massPartition hp0 hpfin he).unitMeasure_pieces]
    exact Finset.sum_congr rfl (fun i _ => D.cumulativeMap_cell_map hp0 hpfin he i)

theorem DisjointStepData.inverseCumulative_measurePreserving :
    MeasurePreserving (D.inverseCumulative hp0 hpfin he) haarMeasure D.weightedMeasure := by
  constructor
  · exact D.inverseCumulative_measurable hp0 hpfin he
  · rw [(D.massPartition hp0 hpfin he).unitMeasure_pieces,
      Measure.map_finset_sum' (D.inverseCumulative_measurable hp0 hpfin he).aemeasurable,
      D.weightedMeasure_pieces hp0 hpfin]
    exact Finset.sum_congr rfl (fun i _ => D.inverseCumulative_cell_map hp0 hpfin he i)

theorem DisjointStepData.inverseCumulative_cumulativeMap_ae :
    (D.inverseCumulative hp0 hpfin he) ∘ (D.cumulativeMap hp0 hpfin he) =ᵐ[D.weightedMeasure] id := by
  filter_upwards [D.weightedMeasure_ae_support hp0 hpfin] with x hx
  exact D.inverseCumulative_cumulativeMap hp0 hpfin he hx

theorem DisjointStepData.cumulativeMap_inverseCumulative_ae :
    (D.cumulativeMap hp0 hpfin he) ∘ (D.inverseCumulative hp0 hpfin he) =ᵐ[haarMeasure] id := by
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ico] with y hy
  exact D.cumulativeMap_inverseCumulative hp0 hpfin he hy

/-- The piecewise affine change of variables, with both genuine pushforward
identities and the inverse identities on the actual measure spaces. -/
theorem weighted_cell_measure_equivalence :
    MeasurePreserving (D.cumulativeMap hp0 hpfin he) D.weightedMeasure haarMeasure ∧
    MeasurePreserving (D.inverseCumulative hp0 hpfin he) haarMeasure D.weightedMeasure ∧
    (D.inverseCumulative hp0 hpfin he) ∘ (D.cumulativeMap hp0 hpfin he) =ᵐ[D.weightedMeasure] id ∧
    (D.cumulativeMap hp0 hpfin he) ∘ (D.inverseCumulative hp0 hpfin he) =ᵐ[haarMeasure] id :=
  ⟨D.cumulativeMap_measurePreserving hp0 hpfin he,
    D.inverseCumulative_measurePreserving hp0 hpfin he,
    D.inverseCumulative_cumulativeMap_ae hp0 hpfin he,
    D.cumulativeMap_inverseCumulative_ae hp0 hpfin he⟩

end SchauderTranslates.LpConstruction
