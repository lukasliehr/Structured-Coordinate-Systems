import Lean_Code.SchauderTranslates.FejerDensity

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped Convolution
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {d : ℕ}

theorem torus_character_add_apply (k : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier k (x + y) = UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    smul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem torus_character_sub_apply (k : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier k (x - y) = UnitAddTorus.mFourier k x * star (UnitAddTorus.mFourier k y) := by
  rw [sub_eq_add_neg, torus_character_add_apply]
  congr 1
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
    circle_character_neg_apply, star_prod]

/-- Fourier coefficients with the normalized Haar probability measure and explicit conjugation. -/
def torusFourierMoment (f : UnitAddTorus (Fin d) → ℂ) (k : Fin d → ℤ) : ℂ :=
  ∫ x, f x * star (UnitAddTorus.mFourier k x) ∂torusMeasure d

theorem integrable_torusFourierTwist {f : UnitAddTorus (Fin d) → ℂ}
    (hf : Integrable f (torusMeasure d)) (k : Fin d → ℤ) :
    Integrable (fun x => f x * star (UnitAddTorus.mFourier k x)) (torusMeasure d) :=
  hf.mul_bdd ((UnitAddTorus.mFourier k).continuous.star.aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun x => by simp only [norm_star, torus_character_norm]; rfl))

/-- Multiplication by a character intertwines convolution and the corresponding twists. -/
theorem torus_convolution_twist (f g : UnitAddTorus (Fin d) → ℂ)
    (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, torusMeasure d] g) x * star (UnitAddTorus.mFourier k x) =
      ((fun y => f y * star (UnitAddTorus.mFourier k y)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, torusMeasure d]
        (fun y => g y * star (UnitAddTorus.mFourier k y))) x := by
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with y
  have hxy : y + (x - y) = x := by abel
  have hc := torus_character_add_apply k y (x - y)
  rw [hxy] at hc
  rw [hc, star_mul]
  ring

/-- Fourier moments turn convolution into multiplication, with all integrability hypotheses exposed. -/
theorem torusFourierMoment_convolution {f g : UnitAddTorus (Fin d) → ℂ}
    (hf : Integrable f (torusMeasure d)) (hg : Integrable g (torusMeasure d)) (k : Fin d → ℤ) :
    torusFourierMoment (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, torusMeasure d] g) k =
      torusFourierMoment f k * torusFourierMoment g k := by
  unfold torusFourierMoment
  simp_rw [torus_convolution_twist]
  exact integral_convolution (ContinuousLinearMap.lsmul ℂ ℂ)
    (integrable_torusFourierTwist hf k) (integrable_torusFourierTwist hg k)

/-- A single-character convolution has its exact coefficient and remains a character. -/
theorem torus_convolution_character (f : UnitAddTorus (Fin d) → ℂ)
    (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    (∫ y, f y * UnitAddTorus.mFourier k (x - y) ∂torusMeasure d) =
      torusFourierMoment f k * UnitAddTorus.mFourier k x := by
  have he (y : UnitAddTorus (Fin d)) : f y * UnitAddTorus.mFourier k (x - y) =
      (f y * star (UnitAddTorus.mFourier k y)) * UnitAddTorus.mFourier k x := by
    rw [torus_character_sub_apply]
    ring
  simp_rw [he]
  exact integral_mul_const _ _

theorem integrable_torus_convolution_character {f : UnitAddTorus (Fin d) → ℂ}
    (hf : Integrable f (torusMeasure d)) (k : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    Integrable (fun y => f y * UnitAddTorus.mFourier k (x - y)) (torusMeasure d) := by
  apply hf.mul_bdd ((UnitAddTorus.mFourier k).continuous.comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => (torus_character_norm k (x - y)).le)

/-- Convolving any integrable function with a finite Fourier polynomial is again a finite polynomial. -/
theorem torus_convolution_isPolynomial {f g : UnitAddTorus (Fin d) → ℂ}
    (hf : Integrable f (torusMeasure d)) (hg : IsTorusPolynomial g) :
    IsTorusPolynomial (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ, torusMeasure d] g) := by
  obtain ⟨K, a, hK⟩ := hg
  refine ⟨K, fun k => a k * torusFourierMoment f k, ?_⟩
  intro x
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hK, Finset.mul_sum]
  have he (k : Fin d → ℤ) (y : UnitAddTorus (Fin d)) :
      f y * (a k * UnitAddTorus.mFourier k (x - y)) = a k * (f y * UnitAddTorus.mFourier k (x - y)) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun k _ => (integrable_torus_convolution_character hf k x).const_mul (a k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_const_mul, torus_convolution_character]
  ring

end SchauderTranslates
