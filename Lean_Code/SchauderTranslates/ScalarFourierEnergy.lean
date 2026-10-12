import Lean_Code.SchauderTranslates.ActivationMoments
import Lean_Code.SchauderTranslates.LpIndicator
import Lean_Code.SchauderTranslates.TensorActivationGram
import Lean_Code.SchauderTranslates.ScalarReality

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The canonical real L² inner product is the real part of the complex one. -/
theorem lp_complex_real_inner {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f g : Lp ℂ 2 μ) : inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  have h := integral_re (L2.integrable_inner (𝕜 := ℂ) f g)
  change (∫ x, (inner ℂ (f x) (g x)).re ∂μ) = (∫ x, inner ℂ (f x) (g x) ∂μ).re at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [Complex.inner, RCLike.inner_apply, mul_comm]

/-- Complex Fourier modes remain orthonormal when viewed as vectors in real L². -/
theorem circleFourier_real_orthonormal : Orthonormal ℝ (fourierLp (T := 1) 2) := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [lp_complex_real_inner, orthonormal_iff_ite.mp (orthonormal_fourier (T := 1)) k l]
  split_ifs <;> simp

namespace ScalarData
variable {d n : ℕ}

/-- Actual product-weight moments split into active and inactive scalar L² inner products. -/
theorem activatedMoment_scalar_inner (s : ScalarData d n) (p : ℝ)
    (i j : Unit ⊕ Fin n) (k l : ℤ) :
    let Q := lpIndicatorCLM (𝕜 := ℂ) (E := ℂ) (μ := AddCircle.haarAddCircle (T := 1))
      (activationSet p) (activationSet_measurable p)
    let u := fourierLp (T := 1) 2 k
    let v := fourierLp (T := 1) 2 l
    s.activatedMoment p i j k l = s.rawGram i j * inner ℂ (Q u) (Q v) +
      (if i = j then 1 else 0) * inner ℂ (u - Q u) (v - Q v) := by
  dsimp only
  let Q := lpIndicatorCLM (𝕜 := ℂ) (E := ℂ) (μ := AddCircle.haarAddCircle (T := 1))
    (activationSet p) (activationSet_measurable p)
  let u := fourierLp (T := 1) 2 k
  let v := fourierLp (T := 1) 2 l
  change s.activatedMoment p i j k l = s.rawGram i j * inner ℂ (Q u) (Q v) +
    (if i = j then 1 else 0) * inner ℂ (u - Q u) (v - Q v)
  rw [s.activatedMoment_fubini, L2.inner_def, L2.inner_def,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((L2.integrable_inner (𝕜 := ℂ) (Q u) (Q v)).const_mul _)
      ((L2.integrable_inner (𝕜 := ℂ) (u - Q u) (v - Q v)).const_mul _)]
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 2 k, coeFn_fourierLp 2 l,
    lpIndicatorCLM_ae (𝕜 := ℂ) (activationSet p) (activationSet_measurable p) u,
    lpIndicatorCLM_ae (𝕜 := ℂ) (activationSet p) (activationSet_measurable p) v,
    Lp.coeFn_sub u (Q u), Lp.coeFn_sub v (Q v)] with y hu hv hqu hqv hsu hsv
  change u y = fourier k y at hu
  change v y = fourier l y at hv
  change Q u y = (activationSet p).indicator u y at hqu
  change Q v y = (activationSet p).indicator v y at hqv
  rw [hsu, hsv]
  simp only [Pi.sub_apply]
  rw [hqu, hqv]
  by_cases hy : y ∈ activationSet p
  · simp [hy, hu, hv, RCLike.inner_apply, mul_comm, mul_left_comm]
  · simp [hy, hu, hv, RCLike.inner_apply, mul_comm, mul_left_comm]

/-- The real part of the actual finite Fourier Gram is exactly the real tensor activation Gram. -/
theorem activatedMoment_real_tensor (s : ScalarData d n) (hs : s.IsEven) (p : ℝ)
    (i j : Unit ⊕ Fin n) (k l : ℤ) :
    (s.activatedMoment p i j k l).re =
      s.realRawGram i j * inner ℝ
        (lpIndicatorCLM (𝕜 := ℝ) (E := ℂ) (activationSet p) (activationSet_measurable p) (fourierLp (T := 1) 2 k))
        (lpIndicatorCLM (𝕜 := ℝ) (E := ℂ) (activationSet p) (activationSet_measurable p) (fourierLp (T := 1) 2 l)) +
      (if i = j then 1 else 0) * inner ℝ
        (fourierLp (T := 1) 2 k - lpIndicatorCLM (𝕜 := ℝ) (E := ℂ) (activationSet p) (activationSet_measurable p) (fourierLp (T := 1) 2 k))
        (fourierLp (T := 1) 2 l - lpIndicatorCLM (𝕜 := ℝ) (E := ℂ) (activationSet p) (activationSet_measurable p) (fourierLp (T := 1) 2 l)) := by
  have hfield (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
      lpIndicatorCLM (𝕜 := ℂ) (activationSet p) (activationSet_measurable p) f =
        lpIndicatorCLM (𝕜 := ℝ) (activationSet p) (activationSet_measurable p) f := rfl
  rw [s.activatedMoment_scalar_inner]
  simp only [hfield]
  simp only [Complex.add_re, Complex.mul_re, s.rawGram_real hs, zero_mul, sub_zero,
    lp_complex_real_inner, realRawGram, Matrix.map_apply]
  split_ifs <;> simp

end ScalarData
end SchauderTranslates
