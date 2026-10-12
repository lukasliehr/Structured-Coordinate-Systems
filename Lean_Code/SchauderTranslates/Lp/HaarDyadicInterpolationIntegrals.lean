import Lean_Code.SchauderTranslates.Lp.DyadicIntegralFormula
import Lean_Code.SchauderTranslates.Lp.HaarTruncatedPowers

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem dyadic_large_weight_sum (N : ℕ) (c : Fin (2 ^ N) → ℂ) (s a : ℝ) :
    a ^ (s - 2) * ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖ =
      ∑ k : Fin (2 ^ N), haarMeasure.real (dyadicInterval N k) *
        (a ^ (s - 2) * (if a < ‖c k‖ then ‖c k‖ else 0)) := by
  rw [dyadic_large_norm_finite_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem dyadic_small_weight_sum (N : ℕ) (c : Fin (2 ^ N) → ℂ) (s a : ℝ) :
    a ^ (s - 3) * ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a)‖ ^ 2 =
      ∑ k : Fin (2 ^ N), haarMeasure.real (dyadicInterval N k) *
        (a ^ (s - 3) * (if ‖c k‖ ≤ a then ‖c k‖ ^ 2 else 0)) := by
  rw [dyadic_small_square_finite_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem dyadic_large_weight_integrable (N : ℕ) (c : Fin (2 ^ N) → ℂ) {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun a : ℝ => a ^ (s - 2) * ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖)
      (Set.Ioi 0) := by
  simp_rw [dyadic_large_weight_sum]
  exact integrable_finsetSum _ (fun k _ => (haar_low_weight_integrable (r := ‖c k‖) hs).const_mul _)

theorem dyadic_small_weight_integrable (N : ℕ) (c : Fin (2 ^ N) → ℂ) {s : ℝ} (hs : s < 2) :
    IntegrableOn (fun a : ℝ => a ^ (s - 3) * ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a)‖ ^ 2)
      (Set.Ioi 0) := by
  simp_rw [dyadic_small_weight_sum]
  exact integrable_finsetSum _ (fun k _ => (haar_high_weight_integrable hs (norm_nonneg (c k))).const_mul _)

/-- The finite-sum instance of Tonelli evaluates the large-part
interpolation integral exactly, including zero coefficients. -/
theorem dyadic_large_weight_integral (N : ℕ) (c : Fin (2 ^ N) → ℂ) {s : ℝ} (hs : 1 < s) :
    (∫ a in Set.Ioi (0 : ℝ), a ^ (s - 2) * ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖) =
      (∫ x, ‖dyadicStepValue N c x‖ ^ s ∂haarMeasure) / (s - 1) := by
  simp_rw [dyadic_large_weight_sum]
  rw [integral_finsetSum _ (fun k _ => (haar_low_weight_integrable (r := ‖c k‖) hs).const_mul _)]
  simp_rw [integral_const_mul, haar_low_weight_integral hs (norm_nonneg _)]
  rw [dyadic_norm_power_integral, Finset.sum_div]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The small-part interpolation integral uses the convergent tail power
for positive coefficients; the zero-coefficient case is identically zero. -/
theorem dyadic_small_weight_integral (N : ℕ) (c : Fin (2 ^ N) → ℂ) {s : ℝ}
    (hs : s < 2) (hspos : 0 < s) :
    (∫ a in Set.Ioi (0 : ℝ), a ^ (s - 3) * ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a)‖ ^ 2) =
      (∫ x, ‖dyadicStepValue N c x‖ ^ s ∂haarMeasure) / (2 - s) := by
  simp_rw [dyadic_small_weight_sum]
  rw [integral_finsetSum _ (fun k _ => (haar_high_weight_integrable hs (norm_nonneg (c k))).const_mul _)]
  simp_rw [integral_const_mul, haar_high_weight_integral hs (norm_nonneg _) hspos]
  rw [dyadic_norm_power_integral, Finset.sum_div]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

end SchauderTranslates.LpConstruction
