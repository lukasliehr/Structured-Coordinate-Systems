import Lean_Code.SchauderTranslates.TorusPolynomial
import Lean_Code.SchauderTranslates.ActivationWeight
import Mathlib.Analysis.Convolution

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped Convolution
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

instance torusMeasure_addHaar (d : ℕ) : (torusMeasure d).IsAddHaarMeasure := by
  rw [torusMeasure_eq_volume]
  infer_instance

namespace TorusWeight
variable {d : ℕ}

/-- Convolution with the positive product Fejer kernel, as a pointwise real density. -/
def fejerDensity (w : TorusWeight d) (N : ℕ) (x : UnitAddTorus (Fin d)) : ℝ :=
  ∫ y, w.density y * torusFejerKernel d N (x - y) ∂torusMeasure d

theorem fejerDensity_continuous (w : TorusWeight d) (N : ℕ) : Continuous (w.fejerDensity N) := by
  have h := (HasCompactSupport.of_compactSpace (torusFejerKernel d N)).continuous_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) w.integrable.locallyIntegrable (torusFejerKernel_continuous d N)
  exact h

theorem fejerDensity_integrand (w : TorusWeight d) (N : ℕ) (x : UnitAddTorus (Fin d)) :
    Integrable (fun y => w.density y * torusFejerKernel d N (x - y)) (torusMeasure d) := by
  have hk : Integrable (fun y => torusFejerKernel d N (x - y)) (torusMeasure d) :=
    ((torusFejerKernel_continuous d N).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact hk.bdd_mul w.measurable.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (w.positive y)]
    exact w.le_one y))

/-- Both pointwise bounds are preserved, with no exceptional set. -/
theorem fejerDensity_bounds (w : TorusWeight d) (N : ℕ) {b : ℝ}
    (hb : ∀ y, b ≤ w.density y) (x : UnitAddTorus (Fin d)) :
    b ≤ w.fejerDensity N x ∧ w.fejerDensity N x ≤ 1 := by
  have hk : Integrable (fun y => torusFejerKernel d N (x - y)) (torusMeasure d) :=
    ((torusFejerKernel_continuous d N).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi : (∫ y, torusFejerKernel d N (x - y) ∂torusMeasure d) = 1 := by
    rw [integral_sub_left_eq_self, torusFejerKernel_integral]
  constructor
  · have h := integral_mono (hk.const_mul b) (w.fejerDensity_integrand N x)
      (fun y => mul_le_mul_of_nonneg_right (hb y) (torusFejerKernel_nonneg d N (x - y)))
    rw [integral_const_mul, hi, mul_one] at h
    exact h
  · have h := integral_mono (w.fejerDensity_integrand N x) hk (fun y =>
      mul_le_of_le_one_left (torusFejerKernel_nonneg d N (x - y)) (w.le_one y))
    rw [hi] at h
    exact h

/-- Haar mass is exactly unchanged by smoothing. -/
theorem fejerDensity_mass (w : TorusWeight d) (N : ℕ) :
    (∫ x, w.fejerDensity N x ∂torusMeasure d) = w.mass := by
  change (∫ x, (w.density ⋆[ContinuousLinearMap.lsmul ℝ ℝ, torusMeasure d]
    torusFejerKernel d N) x ∂torusMeasure d) = w.mass
  rw [integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) w.integrable
    (torusFejerKernel_integrable d N), torusFejerKernel_integral]
  simp [mass]

/-- A genuine torus weight obtained by smoothing a weight with a positive pointwise floor. -/
def fejer (w : TorusWeight d) {b : ℝ} (hb : 0 < b) (hfloor : ∀ x, b ≤ w.density x)
    (N : ℕ) : TorusWeight d where
  density := w.fejerDensity N
  measurable := (w.fejerDensity_continuous N).measurable
  positive x := hb.trans_le (w.fejerDensity_bounds N hfloor x).1
  le_one x := (w.fejerDensity_bounds N hfloor x).2

@[simp] theorem fejer_mass (w : TorusWeight d) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ w.density x) (N : ℕ) : (w.fejer hb hfloor N).mass = w.mass :=
  w.fejerDensity_mass N

theorem fejer_floor (w : TorusWeight d) {b : ℝ} (hb : 0 < b)
    (hfloor : ∀ x, b ≤ w.density x) (N : ℕ) (x : UnitAddTorus (Fin d)) :
    b ≤ (w.fejer hb hfloor N).density x := (w.fejerDensity_bounds N hfloor x).1

end TorusWeight
end SchauderTranslates
