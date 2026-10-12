import Lean_Code.SchauderTranslates.FiberMarginalCapture

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

theorem starProjection_congr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E F : Submodule ℂ H)
    [E.HasOrthogonalProjection] [F.HasOrthogonalProjection] (h : E = F) :
    E.starProjection = F.starProjection := by
  subst F
  rfl

/-- Positive centered Grams make information uniquely determined by capture,
even for two different finite presentations of the atom span. -/
theorem information_eq_of_capture_eq {ι κ H : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : ι → H) (w : κ → H) {C : Matrix ι ι ℂ} {D : Matrix κ κ ℂ}
    (hC : C.PosDef) (hD : D.PosDef) (hcap : captureOperator v C = captureOperator w D) :
    informationOperator v C = informationOperator w D := by
  let J := informationOperator v C
  let J' := informationOperator w D
  let K := captureOperator w D
  have hJ : J = K + J * K := by
    have h := (information_capture_equations v hC).1
    rwa [hcap] at h
  have hJ' : J' = K + J' * K := (information_capture_equations w hD).1
  have hinv : (1 - K) * (1 + J') = 1 := (information_resolvent_inverse w hD).2
  have hzero : (J - J') * (1 - K) = 0 := by
    calc
      _ = (J - J * K) - (J' - J' * K) := by noncomm_ring
      _ = 0 := by rw [sub_eq_iff_eq_add.mpr hJ, sub_eq_iff_eq_add.mpr hJ', sub_self]
  apply sub_eq_zero.mp
  change J - J' = 0
  calc
    _ = (J - J') * ((1 - K) * (1 + J')) := by rw [hinv, mul_one]
    _ = 0 := by rw [← mul_assoc, hzero, zero_mul]

namespace FiberKernel
variable {S Y ι κ : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {ν : Measure Y} [IsProbabilityMeasure ν] (K : FiberKernel S Y ν)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- Changing the finite row presentation while preserving the actual weighted atom
span does not change information on the full marginal L² space. -/
theorem marginal_information_invariant
    (f : ι → BoundedMeasurableComplex (S × Y)) (g : κ → BoundedMeasurableComplex (S × Y))
    (hf : (Matrix.gram ℂ (K.centered ρ f)).PosDef) (hg : (Matrix.gram ℂ (K.centered ρ g)).PosDef)
    (hspan : atomSpan (K.atoms ρ f) = atomSpan (K.atoms ρ g)) :
    informationOperator (K.marginalMeans ρ f) (Matrix.gram ℂ (K.centered ρ f)) =
      informationOperator (K.marginalMeans ρ g) (Matrix.gram ℂ (K.centered ρ g)) := by
  apply information_eq_of_capture_eq _ _ hf hg
  rw [← K.marginal_capture_projection ρ f hf, ← K.marginal_capture_projection ρ g hg]
  rw [starProjection_congr _ _ hspan]

end FiberKernel
end SchauderTranslates
