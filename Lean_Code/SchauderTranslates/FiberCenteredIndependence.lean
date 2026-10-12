import Lean_Code.SchauderTranslates.BoundedIndependence

noncomputable section
open MeasureTheory Filter
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.FiberKernel
variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable (ν : Measure Y) [IsProbabilityMeasure ν]

/-- The unweighted reference product, with the same slow variables. -/
def unit : FiberKernel S Y ν where
  density := fun _ => 1
  measurable := measurable_const
  nonneg := fun _ => zero_le_one
  bound := 1
  upper := fun _ => le_rfl
  mass := fun _ => by simp

@[simp] theorem unit_measure (ρ : Measure S) : (unit ν (S := S)).measure ρ = ρ.prod ν := by
  simp [measure, unit]

theorem unit_mean (f : BoundedMeasurableComplex (S × Y)) (x : S) :
    (unit ν).mean f x = ∫ y, f (x, y) ∂ν := by simp [mean, unit]

variable {ν} (K : FiberKernel S Y ν)

def centeredRepresentative (f : BoundedMeasurableComplex (S × Y)) :
    BoundedMeasurableComplex (S × Y) :=
  f.sub ((K.meanRepresentative f).pullbackFst Y)

theorem centeredRepresentative_toL2 (ρ : Measure S) [IsFiniteMeasure ρ]
    (f : BoundedMeasurableComplex (S × Y)) :
    (K.centeredRepresentative f).toL2 (K.measure ρ) =
      f.toL2 (K.measure ρ) - ((K.meanRepresentative f).pullbackFst Y).toL2 (K.measure ρ) :=
  BoundedMeasurableComplex.toL2_sub _ _ _

/-- A positive density preserves strict centered independence of a reference-independent
family whose reference conditional means vanish. The density may approach zero. -/
theorem centered_independent_of_reference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Measure S) [IsFiniteMeasure ρ]
    (f : ι → BoundedMeasurableComplex (S × Y)) (hK : ∀ p, 0 < K.density p)
    (hf : LinearIndependent ℂ (fun i => (f i).toL2 (ρ.prod ν)))
    (hz : ∀ i x, (∫ y, f i (x, y) ∂ν) = 0) :
    LinearIndependent ℂ (K.centered ρ f) := by
  let R : FiberKernel S Y ν := unit ν
  let F := R.slowSpace ρ
  let u := fun i => (f i).toL2 (R.measure ρ)
  let v := fun i => ((K.meanRepresentative (f i)).pullbackFst Y).toL2 (R.measure ρ)
  have hu : LinearIndependent ℂ u := by
    apply BoundedMeasurableComplex.linearIndependent_measureChange f (ρ.prod ν) (R.measure ρ) _ hf
    change ρ.prod ν ≪ (unit ν).measure ρ
    rw [unit_measure]
  have huF : ∀ i, u i ∈ Fᗮ := by
    intro i
    apply (Submodule.starProjection_apply_eq_zero_iff F).mp
    change (R.slowSpace ρ).starProjection ((f i).toL2 (R.measure ρ)) = 0
    rw [R.mean_eq_starProjection]
    apply Lp.ext
    filter_upwards [((R.meanRepresentative (f i)).pullbackFst Y).toL2_ae (R.measure ρ),
      Lp.coeFn_zero ℂ 2 (R.measure ρ)] with p hp hzero
    rw [hp, hzero]
    change R.mean (f i) p.1 = 0
    change (unit ν).mean (f i) p.1 = 0
    rw [unit_mean, hz]
  have hvF : ∀ i, v i ∈ F := fun i => R.slow_mem ρ _
  have hli := linearIndependent_sub_slow F u v hu huF hvF
  have hrep : LinearIndependent ℂ (fun i => (K.centeredRepresentative (f i)).toL2 (R.measure ρ)) := by
    have he : (fun i => (K.centeredRepresentative (f i)).toL2 (R.measure ρ)) = fun i => u i - v i := by
      funext i
      exact BoundedMeasurableComplex.toL2_sub _ _ _
    rw [he]
    exact hli
  have hac : R.measure ρ ≪ K.measure ρ := by
    change (unit ν).measure ρ ≪ K.measure ρ
    rw [unit_measure]
    exact K.reference_absolutelyContinuous ρ hK
  have h := BoundedMeasurableComplex.linearIndependent_measureChange
    (fun i => K.centeredRepresentative (f i)) (R.measure ρ) (K.measure ρ) hac hrep
  have he : (fun i => (K.centeredRepresentative (f i)).toL2 (K.measure ρ)) = K.centered ρ f := by
    funext i
    exact K.centeredRepresentative_toL2 ρ (f i)
  rw [he] at h
  exact h

theorem centered_posDef_of_reference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Measure S) [IsFiniteMeasure ρ]
    (f : ι → BoundedMeasurableComplex (S × Y)) (hK : ∀ p, 0 < K.density p)
    (hf : LinearIndependent ℂ (fun i => (f i).toL2 (ρ.prod ν)))
    (hz : ∀ i x, (∫ y, f i (x, y) ∂ν) = 0) :
    (Matrix.gram ℂ (K.centered ρ f)).PosDef :=
  Matrix.posDef_gram_iff_linearIndependent.mpr (K.centered_independent_of_reference ρ f hK hf hz)

end SchauderTranslates.FiberKernel
