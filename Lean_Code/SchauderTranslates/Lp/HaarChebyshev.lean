import Lean_Code.SchauderTranslates.Lp.HaarL2Multiplier

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haar_measureReal_mono_ae {s t : Set ℝ} (h : s ≤ᵐ[haarMeasure] t) :
    haarMeasure.real s ≤ haarMeasure.real t :=
  ENNReal.toReal_mono (measure_ne_top haarMeasure t) (measure_mono_ae h)

theorem haar_l2_square_integral (f : HaarLp 2) :
    (∫ x, ‖f x‖ ^ 2 ∂haarMeasure) = ‖f‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    integral_norm_rpow f (by norm_num) (by norm_num)

theorem haar_l2_chebyshev (f : HaarLp 2) {a : ℝ} (ha : 0 < a) :
    haarMeasure.real {x | a < ‖f x‖} ≤ ‖f‖ ^ 2 / a ^ 2 := by
  have hsq : Integrable (fun x => ‖f x‖ ^ 2) haarMeasure := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      integrable_norm_rpow f (by norm_num) (by norm_num)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun x => sq_nonneg ‖f x‖)) hsq (a ^ 2)
  rw [haar_l2_square_integral] at hm
  apply (le_div_iff₀ (pow_pos ha 2)).mpr
  calc
    _ ≤ haarMeasure.real {x | a ^ 2 ≤ ‖f x‖ ^ 2} * a ^ 2 :=
      mul_le_mul_of_nonneg_right (measureReal_mono
        (fun x hx => by dsimp at hx ⊢; nlinarith [norm_nonneg (f x)])) (sq_nonneg a)
    _ ≤ _ := by simpa only [mul_comm] using hm

end SchauderTranslates.LpConstruction
