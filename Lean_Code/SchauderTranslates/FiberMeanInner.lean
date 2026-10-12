import Lean_Code.SchauderTranslates.FiberKernel

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace BoundedMeasurableComplex
variable {A : Type*} [MeasurableSpace A]

theorem inner_toL2 (μ : Measure A) [IsFiniteMeasure μ] (f g : BoundedMeasurableComplex A) :
    inner ℂ (f.toL2 μ) (g.toL2 μ) = ∫ x, star (f x) * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.toL2_ae μ, g.toL2_ae μ] with x hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, Complex.star_def]
  ring

end BoundedMeasurableComplex

namespace FiberKernel
variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν] (K : FiberKernel S Y ν)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- Fubini identifies the explicit fiber mean by its pairing with every bounded slow function. -/
theorem mean_pairing (h : BoundedMeasurableComplex S) (f : BoundedMeasurableComplex (S × Y)) :
    (∫ p, star (h p.1) * f p ∂K.measure ρ) = ∫ s, star (h s) * K.mean f s ∂ρ := by
  have hw : Integrable (fun p : S × Y => (K.density p : ℂ)) (ρ.prod ν) :=
    (K.density_integrable ρ).ofReal
  have hwf : Integrable (fun p => (K.density p : ℂ) * f p) (ρ.prod ν) :=
    hw.mul_bdd f.measurable.aestronglyMeasurable (Eventually.of_forall f.norm_le)
  have hh : AEStronglyMeasurable (fun p : S × Y => star (h p.1)) (ρ.prod ν) :=
    (continuous_star.measurable.comp (h.measurable.comp measurable_fst)).aestronglyMeasurable
  have hi : Integrable (fun p : S × Y => star (h p.1) * ((K.density p : ℂ) * f p)) (ρ.prod ν) :=
    hwf.bdd_mul hh (Eventually.of_forall (fun p => by simpa only [norm_star] using h.norm_le p.1))
  rw [K.integral_measure]
  have he (p : S × Y) : (K.density p : ℂ) * (star (h p.1) * f p) =
      star (h p.1) * ((K.density p : ℂ) * f p) := by ring
  simp_rw [he]
  rw [integral_prod _ hi]
  simp_rw [integral_const_mul]
  rfl

@[simp] theorem mean_slow (h : BoundedMeasurableComplex S) (s : S) :
    K.mean (h.pullbackFst Y) s = h s := by
  simp only [mean, BoundedMeasurableComplex.pullbackFst, integral_mul_const,
    integral_complex_ofReal, K.mass, Complex.ofReal_one, one_mul]

/-- Inner products of lifted slow functions equal their original slow inner products. -/
theorem slow_inner (h g : BoundedMeasurableComplex S) :
    inner ℂ ((h.pullbackFst Y).toL2 (K.measure ρ)) ((g.pullbackFst Y).toL2 (K.measure ρ)) =
      inner ℂ (h.toL2 ρ) (g.toL2 ρ) := by
  rw [BoundedMeasurableComplex.inner_toL2, BoundedMeasurableComplex.inner_toL2]
  change (∫ p, star (h p.1) * (g.pullbackFst Y) p ∂K.measure ρ) = _
  rw [K.mean_pairing]
  simp only [K.mean_slow]

theorem slow_atom_inner (h : BoundedMeasurableComplex S) (f : BoundedMeasurableComplex (S × Y)) :
    inner ℂ ((h.pullbackFst Y).toL2 (K.measure ρ)) (f.toL2 (K.measure ρ)) =
      inner ℂ (h.toL2 ρ) ((K.meanRepresentative f).toL2 ρ) := by
  rw [BoundedMeasurableComplex.inner_toL2, BoundedMeasurableComplex.inner_toL2]
  exact K.mean_pairing ρ h f

/-- The centered atom is orthogonal to every bounded slow function in the actual weighted L² law. -/
theorem centered_slow_inner (h : BoundedMeasurableComplex S) (f : BoundedMeasurableComplex (S × Y)) :
    inner ℂ ((h.pullbackFst Y).toL2 (K.measure ρ))
      (f.toL2 (K.measure ρ) - ((K.meanRepresentative f).pullbackFst Y).toL2 (K.measure ρ)) = 0 := by
  rw [inner_sub_right, K.slow_atom_inner, K.slow_inner, sub_self]

end FiberKernel
end SchauderTranslates
