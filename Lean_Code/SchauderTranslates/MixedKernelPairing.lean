import Lean_Code.SchauderTranslates.BoundedRepresentatives

noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open BoundedMeasurableComplex

/-- A separated test function against `w + (1-w)v`, before normalization.
This identity retains both terms, including the seed mean. -/
theorem mixed_kernel_pairing {Z T : Type*} [MeasurableSpace Z] [MeasurableSpace T]
    (ν : Measure Z) (η : Measure T) [IsFiniteMeasure ν] [IsFiniteMeasure η]
    (v f : BoundedMeasurableComplex Z) (w q : BoundedMeasurableComplex T) :
    (∫ p, (w p.2 + (1 - w p.2) * v p.1) * (f p.1 * q p.2) ∂ν.prod η) =
      (∫ z, f z ∂ν) * (∫ t, w t * q t ∂η) +
        (∫ z, v z * f z ∂ν) * ((∫ t, q t ∂η) - ∫ t, w t * q t ∂η) := by
  have h₁ : Integrable (fun p : Z × T => f p.1 * (w p.2 * q p.2)) (ν.prod η) :=
    (f.tensor (w.mul q)).integrable _
  have h₂ : Integrable (fun p : Z × T => (v p.1 * f p.1) * ((1 - w p.2) * q p.2)) (ν.prod η) :=
    ((v.mul f).tensor (((const T 1).sub w).mul q)).integrable _
  have he (p : Z × T) : (w p.2 + (1 - w p.2) * v p.1) * (f p.1 * q p.2) =
      f p.1 * (w p.2 * q p.2) + (v p.1 * f p.1) * ((1 - w p.2) * q p.2) := by ring
  simp_rw [he]
  have ht₁ := f.integral_tensor (w.mul q) ν η
  have ht₂ := (v.mul f).integral_tensor (((const T 1).sub w).mul q) ν η
  dsimp only [BoundedMeasurableComplex.mul, BoundedMeasurableComplex.sub,
    BoundedMeasurableComplex.const] at ht₁ ht₂
  rw [integral_add h₁ h₂, ht₁, ht₂]
  have hi : (∫ t, (1 - w t) * q t ∂η) = (∫ t, q t ∂η) - ∫ t, w t * q t ∂η := by
    simp_rw [sub_mul, one_mul]
    exact integral_sub (q.integrable η) ((w.mul q).integrable η)
  change (∫ z, f z ∂ν) * (∫ t, w t * q t ∂η) +
    (∫ z, v z * f z ∂ν) * (∫ t, (1 - w t) * q t ∂η) = _
  rw [hi]

end SchauderTranslates
