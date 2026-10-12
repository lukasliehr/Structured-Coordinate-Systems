import Lean_Code.SchauderTranslates.FiberKernel

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.FiberKernel
variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν] (K : FiberKernel S Y ν)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- The conditional mass-one identity preserves the slow marginal exactly. -/
theorem measurePreserving_fst : MeasurePreserving Prod.fst (K.measure ρ) ρ := by
  refine ⟨measurable_fst, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_fst hA, measure,
    withDensity_apply _ (hA.preimage measurable_fst), ← lintegral_indicator (hA.preimage measurable_fst)]
  rw [lintegral_prod _ ((K.measurable.ennreal_ofReal).indicator (hA.preimage measurable_fst)).aemeasurable]
  have hm (s : S) : (∫⁻ y, ENNReal.ofReal (K.density (s, y)) ∂ν) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (K.density_fiber_integrable s)
      (Eventually.of_forall (fun y => K.nonneg (s, y))), K.mass, ENNReal.ofReal_one]
  have he (s : S) : (∫⁻ y, (Prod.fst ⁻¹' A).indicator (fun p => ENNReal.ofReal (K.density p)) (s, y) ∂ν) =
      A.indicator (fun _ => (1 : ℝ≥0∞)) s := by
    by_cases hs : s ∈ A
    · simpa [Set.indicator, hs] using hm s
    · simp [Set.indicator_of_notMem hs, hs]
  simp_rw [he]
  exact lintegral_indicator_one hA

/-- The full slow L² space embeds isometrically into the actual weighted joint law. -/
def slowLift : Lp ℂ 2 ρ →ₗᵢ[ℂ] Lp ℂ 2 (K.measure ρ) :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.fst (K.measurePreserving_fst ρ)

/-- The isometric lift agrees with composition of every bounded representative. -/
theorem slowLift_bounded (f : BoundedMeasurableComplex S) :
    K.slowLift ρ (f.toL2 ρ) = (f.pullbackFst Y).toL2 (K.measure ρ) := by
  apply Lp.ext
  have h := Lp.coeFn_compMeasurePreserving (f.toL2 ρ) (K.measurePreserving_fst ρ)
  have hf := (K.measurePreserving_fst ρ).quasiMeasurePreserving.ae_eq_comp (f.toL2_ae ρ)
  filter_upwards [h, hf, (f.pullbackFst Y).toL2_ae (K.measure ρ)] with p hp hfp hright
  exact hp.trans (hfp.trans hright.symm)

end SchauderTranslates.FiberKernel
