import Lean_Code.SchauderTranslates.Lp.HaarLevelSets
import Lean_Code.SchauderTranslates.Lp.HaarL2Layercake
import Lean_Code.SchauderTranslates.Lp.HaarDyadicInterpolationIntegrals

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haar_multiplier_weighted_level_set_bound (N : ℕ) (c : Fin (2 ^ N) → ℂ)
    (t : Finset HaarIndex) (w : HaarIndex → ℂ) (hw : ∀ i ∈ t, ‖w i‖ ≤ 1)
    (s : ℝ) {a : ℝ} (ha : 0 < a) :
    haarMeasure.real {x | a < ‖haarL2Multiplier t w (haarDyadicStep 2 N c) x‖} * a ^ (s - 1) ≤
      6 * (a ^ (s - 2) * ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖) +
      4 * (a ^ (s - 3) * ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a)‖ ^ 2) := by
  have hb := haar_multiplier_level_set_bound N c t w hw ha
  rw [← dyadic_large_norm_integral N c ha, ← dyadic_small_square_integral N c a] at hb
  have hpow1 : a ^ (s - 1) / a = a ^ (s - 2) := by
    simpa only [Real.rpow_one, show s - 1 - 1 = s - 2 by ring] using (Real.rpow_sub ha (s - 1) 1).symm
  have hpow2 : a ^ (s - 1) / a ^ 2 = a ^ (s - 3) := by
    simpa only [Real.rpow_two, show s - 1 - 2 = s - 3 by ring] using (Real.rpow_sub ha (s - 1) 2).symm
  calc
    _ ≤ ((6 / a) * ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖ +
        (4 / a ^ 2) * ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a)‖ ^ 2) * a ^ (s - 1) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg ha.le _)
    _ = _ := by rw [← hpow1, ← hpow2]; ring

/-- The strong power estimate on every finite dyadic step function,
with the exact manuscript constant. Density extension remains a separate
checkpoint, requiring the continuous integral coefficient maps. -/
theorem haar_dyadic_strong_power_bound (N : ℕ) (c : Fin (2 ^ N) → ℂ) (t : Finset HaarIndex)
    (w : HaarIndex → ℂ) (hw : ∀ i ∈ t, ‖w i‖ ≤ 1) {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    (∫ x, ‖haarL2Multiplier t w (haarDyadicStep 2 N c) x‖ ^ s ∂haarMeasure) ≤
      (s * (6 / (s - 1) + 4 / (2 - s))) * ∫ x, ‖dyadicStepValue N c x‖ ^ s ∂haarMeasure := by
  let T := haarL2Multiplier t w
  have h6 := (dyadic_large_weight_integrable N c hs1).const_mul (6 : ℝ)
  have h4 := (dyadic_small_weight_integrable N c hs2).const_mul (4 : ℝ)
  have hmono : (∫ a in Set.Ioi (0 : ℝ),
      haarMeasure.real {x | a < ‖T (haarDyadicStep 2 N c) x‖} * a ^ (s - 1)) ≤
      ∫ a in Set.Ioi (0 : ℝ),
        6 * (a ^ (s - 2) * ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖) +
        4 * (a ^ (s - 3) * ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a)‖ ^ 2) := by
    refine integral_mono_of_nonneg ?_ (h6.add h4) ?_
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with a ha
      exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ha.le _)
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with a ha
      exact haar_multiplier_weighted_level_set_bound N c t w hw s ha
  calc
    _ = s * ∫ a in Set.Ioi (0 : ℝ),
        haarMeasure.real {x | a < ‖T (haarDyadicStep 2 N c) x‖} * a ^ (s - 1) :=
      haar_l2_power_layercake hs1.le hs2.le _
    _ ≤ s * ∫ a in Set.Ioi (0 : ℝ),
        6 * (a ^ (s - 2) * ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖) +
        4 * (a ^ (s - 3) * ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmono (by linarith)
    _ = _ := by
      rw [integral_add h6 h4, integral_const_mul, integral_const_mul,
        dyadic_large_weight_integral N c hs1,
        dyadic_small_weight_integral N c hs2 (by linarith)]
      ring

end SchauderTranslates.LpConstruction
