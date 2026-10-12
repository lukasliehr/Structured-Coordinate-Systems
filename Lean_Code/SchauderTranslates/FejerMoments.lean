import Lean_Code.SchauderTranslates.TorusFourierConvolution
import Lean_Code.SchauderTranslates.FejerMultipliers

noncomputable section
open MeasureTheory ContinuousLinearMap Filter
open scoped Convolution Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {d : ℕ}

/-- The coefficient-Gram convention is the moment at the first frequency minus the second. -/
theorem torus_character_difference (k l : Fin d → ℤ) (x : UnitAddTorus (Fin d)) :
    star (UnitAddTorus.mFourier (k - l) x) =
      star (UnitAddTorus.mFourier k x) * UnitAddTorus.mFourier l x := by
  rw [sub_eq_add_neg, UnitAddTorus.mFourier_add, star_mul, UnitAddTorus.mFourier_neg]
  simp only [← Complex.star_def, star_star]
  exact mul_comm _ _

namespace TorusWeight

theorem vector_inner_moment (w : TorusWeight d) (k l : Fin d → ℤ) :
    inner ℂ (w.vector k) (w.vector l) =
      torusFourierMoment (fun x => (w.density x : ℂ)) (k - l) := by
  rw [w.vector_inner]
  unfold torusFourierMoment
  simp_rw [torus_character_difference, mul_assoc]

theorem fejerDensity_complex (w : TorusWeight d) (N : ℕ) (x : UnitAddTorus (Fin d)) :
    (w.fejerDensity N x : ℂ) =
      ((fun y => (w.density y : ℂ)) ⋆[lsmul ℂ ℂ, torusMeasure d]
        (fun y => (torusFejerKernel d N y : ℂ))) x := by
  simp only [fejerDensity, convolution_def, lsmul_apply, smul_eq_mul]
  simpa only [Complex.ofReal_mul] using
    (integral_complex_ofReal (μ := torusMeasure d)
      (f := fun y => w.density y * torusFejerKernel d N (x - y))).symm

theorem fejerDensity_polynomial (w : TorusWeight d) (N : ℕ) :
    IsTorusPolynomial (fun x => (w.fejerDensity N x : ℂ)) := by
  simp_rw [fejerDensity_complex]
  exact torus_convolution_isPolynomial w.integrable.ofReal (torusFejerKernel_isPolynomial d N)

/-- Every Fourier moment has the explicit finite-product Fejer multiplier. -/
theorem fejerDensity_moment (w : TorusWeight d) (N : ℕ) (k : Fin d → ℤ) :
    torusFourierMoment (fun x => (w.fejerDensity N x : ℂ)) k =
      torusFourierMoment (fun x => (w.density x : ℂ)) k * (torusFejerMultiplier N k : ℂ) := by
  simp_rw [fejerDensity_complex]
  have h := torusFourierMoment_convolution (w.integrable.ofReal (𝕜 := ℂ))
    ((torusFejerKernel_integrable d N).ofReal (𝕜 := ℂ)) k
  have hk : torusFourierMoment (fun x => (torusFejerKernel d N x : ℂ)) k =
      (torusFejerMultiplier N k : ℂ) := torusFejerKernel_moment N k
  exact h.trans (congrArg (fun z => torusFourierMoment (fun x => (w.density x : ℂ)) k * z) hk)

theorem fejerDensity_moment_tendsto (w : TorusWeight d) (k : Fin d → ℤ) :
    Tendsto (fun N => torusFourierMoment (fun x => (w.fejerDensity N x : ℂ)) k)
      atTop (𝓝 (torusFourierMoment (fun x => (w.density x : ℂ)) k)) := by
  simp_rw [fejerDensity_moment]
  simpa using tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp
    (torusFejerMultiplier_tendsto k))

theorem fejerDensity_even (w : TorusWeight d) (hw : ∀ x, w.density (-x) = w.density x)
    (N : ℕ) (x : UnitAddTorus (Fin d)) : w.fejerDensity N (-x) = w.fejerDensity N x := by
  unfold fejerDensity
  rw [← integral_neg_eq_self (fun y => w.density y * torusFejerKernel d N (-x - y)) (torusMeasure d)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [hw]
  have he : -x - -y = -(x - y) := by abel
  rw [he, torusFejerKernel_even]

end TorusWeight
end SchauderTranslates
