import Lean_Code.SchauderTranslates.ScalarData
import Lean_Code.SchauderTranslates.FejerCount

noncomputable section
open MeasureTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The normalized positive Fejer kernel on the unit circle. -/
def circleFejerKernel (N : ℕ) (x : UnitAddCircle) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ * ‖∑ r ∈ Finset.range (N + 1), fourier (r : ℤ) x‖ ^ 2

theorem circleFejerKernel_nonneg (N : ℕ) (x : UnitAddCircle) : 0 ≤ circleFejerKernel N x := by
  unfold circleFejerKernel
  positivity

theorem circleFejerKernel_continuous (N : ℕ) : Continuous (circleFejerKernel N) := by
  unfold circleFejerKernel
  fun_prop

theorem circleFejerKernel_integrable (N : ℕ) :
    Integrable (circleFejerKernel N) (AddCircle.haarAddCircle (T := 1)) :=
  (circleFejerKernel_continuous N).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem circle_character_neg_apply (k : ℤ) (x : UnitAddCircle) :
    fourier k (-x) = star (fourier k x) := by
  simp [fourier_apply, smul_neg, Complex.star_def]

theorem circleFejerKernel_even (N : ℕ) (x : UnitAddCircle) :
    circleFejerKernel N (-x) = circleFejerKernel N x := by
  simp only [circleFejerKernel, circle_character_neg_apply, Complex.star_def, ← map_sum, Complex.norm_conj]

/-- The square modulus is the finite Fourier expansion indexed by frequency differences. -/
theorem circleFejerKernel_expansion (N : ℕ) (x : UnitAddCircle) :
    (circleFejerKernel N x : ℂ) = ((N + 1 : ℕ) : ℂ)⁻¹ *
      ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1), fourier ((r : ℤ) - s) x := by
  simp only [circleFejerKernel, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_pow]
  rw [← Complex.mul_conj']
  congr 1
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [sub_eq_add_neg, fourier_add, fourier_neg]

theorem integral_circle_character (k : ℤ) :
    (∫ x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle) = if k = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := 1))) 0 k
  simpa only [ContinuousMap.inner_toLp, fourier_zero, map_one, mul_one, eq_comm] using h

/-- Pair expansion gives every Fourier coefficient before simplifying the exact count. -/
theorem circleFejerKernel_moment_sum (N : ℕ) (k : ℤ) :
    (∫ x : UnitAddCircle, (circleFejerKernel N x : ℂ) * star (fourier k x) ∂AddCircle.haarAddCircle) =
      ((N + 1 : ℕ) : ℂ)⁻¹ * ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
        if (r : ℤ) - (s : ℤ) = k then 1 else 0 := by
  have hexp (x : UnitAddCircle) :
      (circleFejerKernel N x : ℂ) * star (fourier k x) = ((N + 1 : ℕ) : ℂ)⁻¹ *
        ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
          fourier ((r : ℤ) - s - k) x := by
    rw [circleFejerKernel_expansion, mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    simp only [sub_eq_add_neg, fourier_add, fourier_neg, Complex.star_def]
  simp_rw [hexp]
  rw [integral_const_mul]
  congr 1
  have hint (r s : ℕ) : Integrable (fun x : UnitAddCircle =>
      fourier ((r : ℤ) - (s : ℤ) - k) x) (AddCircle.haarAddCircle (T := 1)) :=
    (fourier ((r : ℤ) - (s : ℤ) - k)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ => hint r s))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum _ (fun s _ => hint r s)]
  simp only [integral_circle_character, sub_eq_zero]

/-- Exact triangular Fourier multiplier of the positive kernel. -/
def fejerMultiplier (N : ℕ) (k : ℤ) : ℝ :=
  ((N + 1 - k.natAbs : ℕ) : ℝ) / ((N + 1 : ℕ) : ℝ)

theorem circleFejerKernel_moment (N : ℕ) (k : ℤ) :
    (∫ x : UnitAddCircle, (circleFejerKernel N x : ℂ) * star (fourier k x) ∂AddCircle.haarAddCircle) =
      (fejerMultiplier N k : ℂ) := by
  rw [circleFejerKernel_moment_sum]
  have hc : (∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
      if (r : ℤ) - (s : ℤ) = k then (1 : ℂ) else 0) = ((N + 1 - k.natAbs : ℕ) : ℂ) := by
    exact_mod_cast fejer_difference_count (N + 1) k
  rw [hc]
  simp [fejerMultiplier, div_eq_mul_inv, mul_comm]

theorem circleFejerKernel_integral (N : ℕ) :
    (∫ x : UnitAddCircle, circleFejerKernel N x ∂AddCircle.haarAddCircle) = 1 := by
  have h := circleFejerKernel_moment N 0
  simp only [fourier_zero, star_one, mul_one] at h
  have hcast : (∫ x : UnitAddCircle, (circleFejerKernel N x : ℂ) ∂AddCircle.haarAddCircle) =
      (((∫ x : UnitAddCircle, circleFejerKernel N x ∂AddCircle.haarAddCircle) : ℝ) : ℂ) :=
    integral_ofReal
  rw [hcast] at h
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hzero : fejerMultiplier N 0 = 1 := by
    simp only [fejerMultiplier, Int.natAbs_zero, Nat.sub_zero, div_self hN]
  rw [hzero] at h
  exact_mod_cast h

end SchauderTranslates
