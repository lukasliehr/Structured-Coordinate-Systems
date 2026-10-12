import Lean_Code.SchauderTranslates.BoundedIndependence

noncomputable section
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.BoundedMeasurableComplex
variable {A ι : Type*} [MeasurableSpace A] [Fintype ι]

def linearCombination (f : ι → BoundedMeasurableComplex A) (c : ι → ℂ) :
    BoundedMeasurableComplex A where
  toFun := fun x => ∑ i, c i * f i x
  measurable := Finset.measurable_sum _ (fun i _ => measurable_const.mul (f i).measurable)
  bound := ∑ i, ‖c i‖ * (f i).bound
  bound_nonneg := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (f i).bound_nonneg)
  norm_le := fun x => (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((f i).norm_le x) (norm_nonneg _)))

theorem toL2_linearCombination (f : ι → BoundedMeasurableComplex A) (c : ι → ℂ)
    (μ : Measure A) [IsFiniteMeasure μ] :
    (linearCombination f c).toL2 μ = ∑ i, c i • (f i).toL2 μ := by
  apply Lp.ext
  exact ((linearCombination f c).toL2_ae μ).trans (sum_toL2_ae f μ Finset.univ c).symm

theorem exists_representative_of_mem_span (f : ι → BoundedMeasurableComplex A)
    (μ : Measure A) [IsFiniteMeasure μ] {v : Lp ℂ 2 μ}
    (hv : v ∈ Submodule.span ℂ (Set.range (fun i => (f i).toL2 μ))) :
    ∃ g : BoundedMeasurableComplex A, g.toL2 μ = v := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  exact ⟨linearCombination f c, (toL2_linearCombination f c μ).trans hc⟩

end SchauderTranslates.BoundedMeasurableComplex
