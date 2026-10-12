import Lean_Code.SchauderTranslates.Lp.DyadicLevelSplit
import Lean_Code.SchauderTranslates.Lp.HaarDistribution

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- The large/small level split gives precisely the two distribution
terms used in the manuscript's interpolation proof, with constants 6 and 4. -/
theorem haar_multiplier_level_set_bound (N : ℕ) (c : Fin (2 ^ N) → ℂ) (t : Finset HaarIndex)
    (w : HaarIndex → ℂ) (hw : ∀ i ∈ t, ‖w i‖ ≤ 1) {a : ℝ} (ha : 0 < a) :
    haarMeasure.real {x | a < ‖haarL2Multiplier t w (haarDyadicStep 2 N c) x‖} ≤
      (6 / a) * (∫ x in {x | a < ‖dyadicStepValue N c x‖}, ‖dyadicStepValue N c x‖ ∂haarMeasure) +
      (4 / a ^ 2) * (∫ x in {x | ‖dyadicStepValue N c x‖ ≤ a},
        ‖dyadicStepValue N c x‖ ^ 2 ∂haarMeasure) := by
  let T := haarL2Multiplier t w
  let L := haarDyadicStep 2 N (dyadicLargeCoefficients c a)
  let S := haarDyadicStep 2 N (dyadicSmallCoefficients c a)
  have hhalf : 0 < a / 2 := by positivity
  have hsplit : T (haarDyadicStep 2 N c) = T L + T S := by
    rw [haarDyadicStep_split 2 N c a, map_add]
  have hsubset : {x | a < ‖T (haarDyadicStep 2 N c) x‖} ≤ᵐ[haarMeasure]
      ({x | a / 2 < ‖T L x‖} ∪ {x | a / 2 < ‖T S x‖} : Set ℝ) := by
    filter_upwards [Lp.coeFn_add (T L) (T S)] with x hsum
    intro hx
    change a < ‖T (haarDyadicStep 2 N c) x‖ at hx
    rw [hsplit, hsum, Pi.add_apply] at hx
    change a / 2 < ‖T L x‖ ∨ a / 2 < ‖T S x‖
    by_contra h
    push Not at h
    have hn := norm_add_le (T L x) (T S x)
    linarith [h.1, h.2]
  calc
    _ ≤ haarMeasure.real ({x | a / 2 < ‖T L x‖} ∪ {x | a / 2 < ‖T S x‖}) :=
      haar_measureReal_mono_ae hsubset
    _ ≤ haarMeasure.real {x | a / 2 < ‖T L x‖} + haarMeasure.real {x | a / 2 < ‖T S x‖} :=
      measureReal_union_le _ _
    _ ≤ 3 * ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖ / (a / 2) +
        ‖T S‖ ^ 2 / (a / 2) ^ 2 :=
      add_le_add (haar_weak_bound N (dyadicLargeCoefficients c a) t w hw hhalf)
        (haar_l2_chebyshev (T S) hhalf)
    _ ≤ 3 * ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖ / (a / 2) +
        ‖S‖ ^ 2 / (a / 2) ^ 2 := add_le_add le_rfl
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
        (haar_l2_multiplier_bound t w hw S) 2) (sq_nonneg _))
    _ = _ := by
      dsimp only [S]
      rw [dyadic_large_norm_integral N c ha, dyadic_small_square_integral N c a]
      field_simp [ha.ne']
      ring

end SchauderTranslates.LpConstruction
