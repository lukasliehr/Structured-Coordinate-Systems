import Lean_Code.SchauderTranslates.BoundedRepresentatives
import Lean_Code.SchauderTranslates.FiberMeanProjection

noncomputable section
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace BoundedMeasurableComplex
variable {A ι : Type*} [MeasurableSpace A]

theorem sum_toL2_ae (f : ι → BoundedMeasurableComplex A) (μ : Measure A) [IsFiniteMeasure μ]
    (s : Finset ι) (c : ι → ℂ) :
    ((∑ i ∈ s, c i • (f i).toL2 μ : Lp ℂ 2 μ) : A → ℂ) =ᵐ[μ]
      (fun x => ∑ i ∈ s, c i * f i x) := by
  classical
  have h (i : ι) : (c i • (f i).toL2 μ : Lp ℂ 2 μ) =ᵐ[μ] (fun x => c i * f i x) := by
    filter_upwards [Lp.coeFn_smul (c i) ((f i).toL2 μ), (f i).toL2_ae μ] with x hs hf
    simpa only [Pi.smul_apply, smul_eq_mul, hf] using hs
  filter_upwards [Lp.coeFn_fun_finsetSum s (fun i => c i • (f i).toL2 μ),
    s.eventually_all.mpr (fun i _ => h i)] with x hx hi
  rw [hx]
  exact Finset.sum_congr rfl (fun i his => hi i his)

/-- Changing to a measure with fewer null sets preserves independence of the actual
bounded representatives; no quantitative density floor is needed. -/
theorem linearIndependent_measureChange (f : ι → BoundedMeasurableComplex A)
    (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (hf : LinearIndependent ℂ (fun i => (f i).toL2 μ)) :
    LinearIndependent ℂ (fun i => (f i).toL2 ν) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc
  apply linearIndependent_iff'.mp hf s c
  apply Lp.ext
  have hz : (fun x => ∑ i ∈ s, c i * f i x) =ᵐ[ν] 0 := by
    have h := (sum_toL2_ae f ν s c).symm
    rw [hc] at h
    exact h.trans (Lp.coeFn_zero ℂ 2 ν)
  exact (sum_toL2_ae f μ s c).trans ((hμν.ae_eq hz).trans (Lp.coeFn_zero ℂ 2 μ).symm)

end BoundedMeasurableComplex

theorem linearIndependent_sub_slow {ι H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (F : Submodule ℂ H) [CompleteSpace F]
    (u v : ι → H) (hu : LinearIndependent ℂ u) (huF : ∀ i, u i ∈ Fᗮ) (hvF : ∀ i, v i ∈ F) :
    LinearIndependent ℂ (fun i => u i - v i) := by
  apply LinearIndependent.of_comp (v := fun i => u i - v i) Fᗮ.starProjection.toLinearMap
  have he : (fun i => Fᗮ.starProjection (u i - v i)) = u := by
    funext i
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr (huF i),
      Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_eq_self_iff.mpr (hvF i), sub_self, sub_zero]
  simpa only [Function.comp_def, ContinuousLinearMap.coe_coe, he] using hu

namespace FiberKernel
variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν] (K : FiberKernel S Y ν)

theorem reference_absolutelyContinuous (ρ : Measure S) (hK : ∀ p, 0 < K.density p) :
    ρ.prod ν ≪ K.measure ρ := by
  apply withDensity_absolutelyContinuous' K.measurable.ennreal_ofReal.aemeasurable
  exact Eventually.of_forall (fun p => (ENNReal.ofReal_pos.mpr (hK p)).ne')

end FiberKernel
end SchauderTranslates
