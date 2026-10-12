import Lean_Code.SchauderTranslates.CircleFejerKernel
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The product Fejer kernel on the actual finite probability torus. -/
def torusFejerKernel (d N : ℕ) (x : UnitAddTorus (Fin d)) : ℝ :=
  ∏ i, circleFejerKernel N (x i)

theorem torusFejerKernel_nonneg (d N : ℕ) (x : UnitAddTorus (Fin d)) :
    0 ≤ torusFejerKernel d N x := Finset.prod_nonneg (fun i _ => circleFejerKernel_nonneg N (x i))

theorem torusFejerKernel_continuous (d N : ℕ) : Continuous (torusFejerKernel d N) := by
  unfold torusFejerKernel
  exact continuous_finsetProd _ (fun i _ => (circleFejerKernel_continuous N).comp (continuous_apply i))

theorem torusFejerKernel_integrable (d N : ℕ) :
    Integrable (torusFejerKernel d N) (torusMeasure d) :=
  (torusFejerKernel_continuous d N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem torusFejerKernel_even (d N : ℕ) (x : UnitAddTorus (Fin d)) :
    torusFejerKernel d N (-x) = torusFejerKernel d N x := by
  simp only [torusFejerKernel, Pi.neg_apply, circleFejerKernel_even]

theorem torusFejerKernel_integral (d N : ℕ) :
    (∫ x, torusFejerKernel d N x ∂torusMeasure d) = 1 := by
  change (∫ x, ∏ i : Fin d, circleFejerKernel N (x i)
    ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := 1))) = 1
  rw [integral_fintype_prod_eq_prod (fun _ : Fin d => circleFejerKernel N)]
  simp [circleFejerKernel_integral]

/-- The Fourier multiplier is the product of the triangular one-dimensional multipliers. -/
def torusFejerMultiplier {d : ℕ} (N : ℕ) (k : Fin d → ℤ) : ℝ := ∏ i, fejerMultiplier N (k i)

theorem torusFejerKernel_moment {d : ℕ} (N : ℕ) (k : Fin d → ℤ) :
    (∫ x, (torusFejerKernel d N x : ℂ) * star (UnitAddTorus.mFourier k x) ∂torusMeasure d) =
      (torusFejerMultiplier N k : ℂ) := by
  have he (x : UnitAddTorus (Fin d)) :
      (torusFejerKernel d N x : ℂ) * star (UnitAddTorus.mFourier k x) =
        ∏ i, (circleFejerKernel N (x i) : ℂ) * star (fourier (k i) (x i)) := by
    simp only [torusFejerKernel, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Complex.ofReal_prod, Complex.star_def, map_prod, Finset.prod_mul_distrib]
  simp_rw [he]
  change (∫ x, ∏ i : Fin d, (circleFejerKernel N (x i) : ℂ) * star (fourier (k i) (x i))
    ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle (T := 1))) = _
  rw [integral_fintype_prod_eq_prod (fun i x => (circleFejerKernel N x : ℂ) * star (fourier (k i) x))]
  simp only [circleFejerKernel_moment, torusFejerMultiplier, Complex.ofReal_prod]

end SchauderTranslates
