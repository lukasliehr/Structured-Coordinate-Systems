import Lean_Code.SchauderTranslates.SelectivePacket

noncomputable section
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SelectiveKernelData
open BoundedMeasurableComplex
variable {S : Type*} [MeasurableSpace S] {L d n : ℕ}
variable (a : SelectiveKernelData S L d n) (ρ : Measure S) [IsFiniteMeasure ρ]

def seedOnProduct : BoundedMeasurableComplex (S × UnitAddTorus (Fin L)) where
  toFun := fun p => (seedKernel L a.m ((a.κ : ℂ) * a.e p.1) p.2 : ℂ)
  measurable := Complex.continuous_ofReal.measurable.comp (seedKernel_measurable a.e a.e.measurable L a.m a.κ)
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := fun p => by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (seedKernel_bounds L a.mass_pos a.mass_le (a.coupling_bound p.1) p.2).1]
    exact (seedKernel_bounds L a.mass_pos a.mass_le (a.coupling_bound p.1) p.2).2

/-- Integrate a general separated row/column against the actual normalized joint law.
There is exactly one normalization factor. -/
theorem integral_rowColumn (r : BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (q : BoundedMeasurableComplex (UnitAddTorus (Fin d))) :
    (∫ p, rowColumn r q p ∂a.kernel.measure ρ) =
      ((∫ p, r p ∂ρ.prod (torusMeasure L)) *
          (∫ t, (a.scalar.density t : ℂ) * q t ∂torusMeasure d) +
        (∫ p, (seedKernel L a.m ((a.κ : ℂ) * a.e p.1) p.2 : ℂ) * r p ∂ρ.prod (torusMeasure L)) *
          ((∫ t, q t ∂torusMeasure d) - ∫ t, (a.scalar.density t : ℂ) * q t ∂torusMeasure d)) / (a.mass : ℂ) := by
  have hp := a.kernel.mean_pairing ρ (const S 1) (rowColumn r q)
  simp only [const, star_one, one_mul] at hp
  rw [hp]
  simp_rw [a.mean_rowColumn]
  rw [integral_div]
  have hr : Integrable (fun p => r p) (ρ.prod (torusMeasure L)) := r.integrable _
  have hvr : Integrable (fun p : S × UnitAddTorus (Fin L) =>
      (seedKernel L a.m ((a.κ : ℂ) * a.e p.1) p.2 : ℂ) * r p) (ρ.prod (torusMeasure L)) :=
    (a.seedOnProduct.mul r).integrable _
  rw [integral_add (hr.integral_prod_left.mul_const _) (hvr.integral_prod_left.mul_const _),
    integral_mul_const, integral_mul_const, ← integral_prod _ hr, ← integral_prod _ hvr]

/-- Full mixed inner product before any choice of orthonormal row coordinates. -/
theorem inner_rowColumn (r u : BoundedMeasurableComplex (S × UnitAddTorus (Fin L)))
    (q v : BoundedMeasurableComplex (UnitAddTorus (Fin d))) :
    inner ℂ ((rowColumn r q).toL2 (a.kernel.measure ρ)) ((rowColumn u v).toL2 (a.kernel.measure ρ)) =
      (inner ℂ (r.toL2 (ρ.prod (torusMeasure L))) (u.toL2 (ρ.prod (torusMeasure L))) *
          (∫ t, (a.scalar.density t : ℂ) * star (q t) * v t ∂torusMeasure d) +
        (∫ p, (seedKernel L a.m ((a.κ : ℂ) * a.e p.1) p.2 : ℂ) * star (r p) * u p
          ∂ρ.prod (torusMeasure L)) *
          (inner ℂ (q.toL2 (torusMeasure d)) (v.toL2 (torusMeasure d)) -
            ∫ t, (a.scalar.density t : ℂ) * star (q t) * v t ∂torusMeasure d)) / (a.mass : ℂ) := by
  rw [inner_toL2]
  have he : (∫ p, star (rowColumn r q p) * rowColumn u v p ∂a.kernel.measure ρ) =
      ∫ p, rowColumn (r.conjugate.mul u) (q.conjugate.mul v) p ∂a.kernel.measure ρ := by
    apply integral_congr_ae
    filter_upwards [] with p
    change star (r (p.1, p.2.1) * q p.2.2) * (u (p.1, p.2.1) * v p.2.2) =
      (star (r (p.1, p.2.1)) * u (p.1, p.2.1)) * (star (q p.2.2) * v p.2.2)
    rw [star_mul]
    ring
  rw [he, a.integral_rowColumn]
  simp only [mul, conjugate, inner_toL2, mul_assoc]

end SchauderTranslates.SelectiveKernelData
