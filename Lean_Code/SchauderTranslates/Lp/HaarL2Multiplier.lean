import Lean_Code.SchauderTranslates.Lp.HaarOrthogonal

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem orthonormal_finite_sum_norm_square {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} (u : ι → E) (hu : Orthonormal ℂ u)
    (s : Finset ι) (c : ι → ℂ) : ‖∑ i ∈ s, c i • u i‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 := by
  have hi : inner ℂ (∑ i ∈ s, c i • u i) (∑ i ∈ s, c i • u i) =
      ∑ i ∈ s, (starRingEnd ℂ (c i)) * c i := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_smul_left, hu.inner_right_sum c hi]
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hi]
  change Complex.re (∑ i ∈ s, (starRingEnd ℂ (c i)) * c i) = _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [RCLike.inner_apply, RCLike.re_eq_complex_re, mul_comm]
    using (norm_sq_eq_re_inner (𝕜 := ℂ) (c i)).symm

def haarL2Multiplier (s : Finset HaarIndex) (a : HaarIndex → ℂ) : HaarLp 2 →L[ℂ] HaarLp 2 :=
  ∑ i ∈ s, a i • (innerSL ℂ (haarAtom 2 i)).smulRight (haarAtom 2 i)

@[simp] theorem haarL2Multiplier_apply (s : Finset HaarIndex) (a : HaarIndex → ℂ) (f : HaarLp 2) :
    haarL2Multiplier s a f = ∑ i ∈ s, (a i * inner ℂ (haarAtom 2 i) f) • haarAtom 2 i := by
  simp [haarL2Multiplier, smul_smul]

theorem haar_l2_coefficient_integral (i : HaarIndex) (f : HaarLp 2) :
    inner ℂ (haarAtom 2 i) f =
      ∫ x, f x * star (haarAtom 2 i x) ∂haarMeasure := by
  rw [MeasureTheory.L2.inner_def]
  congr 1

/-- This is precisely the paper's integral-defined finite multiplier,
with mathlib's inner product linear in its second argument. -/
theorem haarL2Multiplier_apply_integral (s : Finset HaarIndex) (a : HaarIndex → ℂ)
    (f : HaarLp 2) :
    haarL2Multiplier s a f =
      ∑ i ∈ s, (a i * ∫ x, f x * star (haarAtom 2 i x) ∂haarMeasure) • haarAtom 2 i := by
  simp_rw [haarL2Multiplier_apply, haar_l2_coefficient_integral]

/-- Every finite multiplier with coefficients in the complex unit disk is
contractive in the actual L² norm. -/
theorem haar_l2_multiplier_bound (s : Finset HaarIndex) (a : HaarIndex → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (f : HaarLp 2) : ‖haarL2Multiplier s a f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg f)).mp
  rw [haarL2Multiplier_apply, orthonormal_finite_sum_norm_square _ haar_orthonormal]
  calc
    _ ≤ ∑ i ∈ s, ‖inner ℂ (haarAtom 2 i) f‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      have hm : ‖a i‖ * ‖inner ℂ (haarAtom 2 i) f‖ ≤ ‖inner ℂ (haarAtom 2 i) f‖ := by
        simpa using mul_le_mul_of_nonneg_right (ha i hi) (norm_nonneg _)
      exact pow_le_pow_left₀ (by positivity) hm _
    _ ≤ ‖f‖ ^ 2 := haar_orthonormal.sum_inner_products_le f

theorem haar_l2_multiplier_norm (s : Finset HaarIndex) (a : HaarIndex → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) : ‖haarL2Multiplier s a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using haar_l2_multiplier_bound s a ha f

end SchauderTranslates.LpConstruction
