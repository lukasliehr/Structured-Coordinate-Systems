import Lean_Code.SchauderTranslates.IntegralGram

noncomputable section
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A bounded measurable representative, with an explicit bound for later integral proofs. -/
structure BoundedMeasurableComplex (A : Type*) [MeasurableSpace A] where
  toFun : A → ℂ
  measurable : Measurable toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x, ‖toFun x‖ ≤ bound

instance {A : Type*} [MeasurableSpace A] : CoeFun (BoundedMeasurableComplex A) (fun _ => A → ℂ) :=
  ⟨BoundedMeasurableComplex.toFun⟩

namespace BoundedMeasurableComplex
variable {A : Type*} [MeasurableSpace A]

theorem memLp (f : BoundedMeasurableComplex A) (μ : Measure A) [IsFiniteMeasure μ] : MemLp f 2 μ :=
  MemLp.of_bound f.measurable.aestronglyMeasurable f.bound (Eventually.of_forall f.norm_le)

def toL2 (f : BoundedMeasurableComplex A) (μ : Measure A) [IsFiniteMeasure μ] : Lp ℂ 2 μ :=
  (f.memLp μ).toLp f

theorem toL2_ae (f : BoundedMeasurableComplex A) (μ : Measure A) [IsFiniteMeasure μ] :
    f.toL2 μ =ᵐ[μ] f := (f.memLp μ).coeFn_toLp

def pullbackFst (f : BoundedMeasurableComplex A) (Y : Type*) [MeasurableSpace Y] : BoundedMeasurableComplex (A × Y) where
  toFun := fun p => f p.1
  measurable := f.measurable.comp measurable_fst
  bound := f.bound
  bound_nonneg := f.bound_nonneg
  norm_le := fun p => f.norm_le p.1

end BoundedMeasurableComplex

/-- A bounded probability density in the fresh variables, for every fixed slow variable.
The normalized selective kernel is an instance of this data. -/
structure FiberKernel (S Y : Type*) [MeasurableSpace S] [MeasurableSpace Y] (ν : Measure Y) where
  density : S × Y → ℝ
  measurable : Measurable density
  nonneg : ∀ p, 0 ≤ density p
  bound : ℝ
  upper : ∀ p, density p ≤ bound
  mass : ∀ s, (∫ y, density (s, y) ∂ν) = 1

namespace FiberKernel
variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν] (K : FiberKernel S Y ν)

/-- The actual probability-weighted joint law. -/
def measure (ρ : Measure S) : Measure (S × Y) :=
  (ρ.prod ν).withDensity (fun p => ENNReal.ofReal (K.density p))

theorem density_integrable (ρ : Measure S) [IsFiniteMeasure ρ] : Integrable K.density (ρ.prod ν) := by
  apply Integrable.of_bound K.measurable.aestronglyMeasurable K.bound
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs, abs_of_nonneg (K.nonneg p)] using K.upper p

theorem density_fiber_integrable (s : S) : Integrable (fun y => K.density (s, y)) ν := by
  apply Integrable.of_bound (K.measurable.comp measurable_prodMk_left).aestronglyMeasurable K.bound
  filter_upwards [] with y
  simpa only [Function.comp_def, Real.norm_eq_abs, abs_of_nonneg (K.nonneg (s, y))] using K.upper (s, y)

instance measure_finite (ρ : Measure S) [IsFiniteMeasure ρ] : IsFiniteMeasure (K.measure ρ) := by
  apply isFiniteMeasure_withDensity
  have h := ofReal_integral_eq_lintegral_ofReal (K.density_integrable ρ) (Eventually.of_forall K.nonneg)
  rw [← h]
  exact ENNReal.ofReal_ne_top

instance measure_probability (ρ : Measure S) [IsProbabilityMeasure ρ] : IsProbabilityMeasure (K.measure ρ) := by
  constructor
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (K.density_integrable ρ) (Eventually.of_forall K.nonneg),
    integral_prod _ (K.density_integrable ρ)]
  simp only [K.mass, integral_const, probReal_univ, one_smul, ENNReal.ofReal_one]

/-- Conversion to ordinary product integrals is valid for every complex integrand. -/
theorem integral_measure (ρ : Measure S) (f : S × Y → ℂ) :
    (∫ p, f p ∂K.measure ρ) = ∫ p, (K.density p : ℂ) * f p ∂ρ.prod ν := by
  rw [measure, integral_withDensity_eq_integral_toReal_smul (K.measurable.ennreal_ofReal)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [ENNReal.toReal_ofReal (K.nonneg p)]
  rfl

/-- Explicit conditional mean in the fresh variables. -/
def mean (f : BoundedMeasurableComplex (S × Y)) (s : S) : ℂ :=
  ∫ y, (K.density (s, y) : ℂ) * f (s, y) ∂ν

theorem mean_measurable (f : BoundedMeasurableComplex (S × Y)) : Measurable (K.mean f) := by
  have h : StronglyMeasurable (fun p : S × Y => (K.density p : ℂ) * f p) :=
    ((Complex.continuous_ofReal.measurable.comp K.measurable).mul f.measurable).stronglyMeasurable
  exact h.integral_prod_right'.measurable

theorem mean_bound (f : BoundedMeasurableComplex (S × Y)) (s : S) : ‖K.mean f s‖ ≤ f.bound := by
  have h : Integrable (fun y => K.density (s, y) * f.bound) ν := (K.density_fiber_integrable s).mul_const f.bound
  have hn : ∀ᵐ y ∂ν, ‖(K.density (s, y) : ℂ) * f (s, y)‖ ≤ K.density (s, y) * f.bound := by
    filter_upwards [] with y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (K.nonneg (s, y))]
    exact mul_le_mul_of_nonneg_left (f.norm_le (s, y)) (K.nonneg (s, y))
  have hi := norm_integral_le_of_norm_le h hn
  simpa only [mean, integral_mul_const, K.mass, one_mul] using hi

def meanRepresentative (f : BoundedMeasurableComplex (S × Y)) : BoundedMeasurableComplex S where
  toFun := K.mean f
  measurable := K.mean_measurable f
  bound := f.bound
  bound_nonneg := f.bound_nonneg
  norm_le := K.mean_bound f

end FiberKernel
end SchauderTranslates
