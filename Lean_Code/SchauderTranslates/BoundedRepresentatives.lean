import Lean_Code.SchauderTranslates.FiberMeanInner

noncomputable section
open MeasureTheory Filter
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.BoundedMeasurableComplex
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

def const (A : Type*) [MeasurableSpace A] (c : ℂ) : BoundedMeasurableComplex A where
  toFun := fun _ => c
  measurable := measurable_const
  bound := ‖c‖
  bound_nonneg := norm_nonneg _
  norm_le := fun _ => le_rfl

def comp (f : BoundedMeasurableComplex B) (g : A → B) (hg : Measurable g) :
    BoundedMeasurableComplex A where
  toFun := fun x => f (g x)
  measurable := f.measurable.comp hg
  bound := f.bound
  bound_nonneg := f.bound_nonneg
  norm_le := fun x => f.norm_le (g x)

def mul (f g : BoundedMeasurableComplex A) : BoundedMeasurableComplex A where
  toFun := fun x => f x * g x
  measurable := f.measurable.mul g.measurable
  bound := f.bound * g.bound
  bound_nonneg := mul_nonneg f.bound_nonneg g.bound_nonneg
  norm_le := fun x => by
    rw [norm_mul]
    exact mul_le_mul (f.norm_le x) (g.norm_le x) (norm_nonneg _) f.bound_nonneg

def sub (f g : BoundedMeasurableComplex A) : BoundedMeasurableComplex A where
  toFun := fun x => f x - g x
  measurable := f.measurable.sub g.measurable
  bound := f.bound + g.bound
  bound_nonneg := add_nonneg f.bound_nonneg g.bound_nonneg
  norm_le := fun x => (norm_sub_le _ _).trans (add_le_add (f.norm_le x) (g.norm_le x))

def scale (c : ℂ) (f : BoundedMeasurableComplex A) : BoundedMeasurableComplex A :=
  (const A c).mul f

def conjugate (f : BoundedMeasurableComplex A) : BoundedMeasurableComplex A where
  toFun := fun x => star (f x)
  measurable := continuous_star.measurable.comp f.measurable
  bound := f.bound
  bound_nonneg := f.bound_nonneg
  norm_le := fun x => by simpa only [norm_star] using f.norm_le x

def tensor (f : BoundedMeasurableComplex A) (g : BoundedMeasurableComplex B) :
    BoundedMeasurableComplex (A × B) :=
  (f.comp Prod.fst measurable_fst).mul (g.comp Prod.snd measurable_snd)

theorem integrable (f : BoundedMeasurableComplex A) (μ : Measure A) [IsFiniteMeasure μ] :
    Integrable f μ :=
  Integrable.of_bound f.measurable.aestronglyMeasurable f.bound (Eventually.of_forall f.norm_le)

theorem toL2_congr (f g : BoundedMeasurableComplex A) (μ : Measure A) [IsFiniteMeasure μ]
    (h : f =ᵐ[μ] g) : f.toL2 μ = g.toL2 μ := by
  apply Lp.ext
  exact (f.toL2_ae μ).trans (h.trans (g.toL2_ae μ).symm)

theorem toL2_sub (f g : BoundedMeasurableComplex A) (μ : Measure A) [IsFiniteMeasure μ] :
    (f.sub g).toL2 μ = f.toL2 μ - g.toL2 μ := by
  apply Lp.ext
  filter_upwards [(f.sub g).toL2_ae μ, f.toL2_ae μ, g.toL2_ae μ,
    Lp.coeFn_sub (f.toL2 μ) (g.toL2 μ)] with x h h₁ h₂ h₃
  change ((f.sub g).toL2 μ : A → ℂ) x = f x - g x at h
  exact h.trans (by simpa only [Pi.sub_apply, h₁, h₂] using h₃.symm)

theorem toL2_scale (c : ℂ) (f : BoundedMeasurableComplex A) (μ : Measure A) [IsFiniteMeasure μ] :
    (f.scale c).toL2 μ = c • f.toL2 μ := by
  apply Lp.ext
  filter_upwards [(f.scale c).toL2_ae μ, f.toL2_ae μ, Lp.coeFn_smul c (f.toL2 μ)] with x h h₁ h₂
  change ((f.scale c).toL2 μ : A → ℂ) x = c * f x at h
  exact h.trans (by simpa only [Pi.smul_apply, h₁, smul_eq_mul] using h₂.symm)

theorem integral_tensor (f : BoundedMeasurableComplex A) (g : BoundedMeasurableComplex B)
    (μ : Measure A) (ν : Measure B) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (∫ p, f p.1 * g p.2 ∂μ.prod ν) = (∫ x, f x ∂μ) * ∫ y, g y ∂ν := by
  have hi : Integrable (fun p : A × B => f p.1 * g p.2) (μ.prod ν) :=
    (f.tensor g).integrable (μ.prod ν)
  rw [integral_prod _ hi]
  simp only [integral_const_mul, integral_mul_const]

end SchauderTranslates.BoundedMeasurableComplex
