import Lean_Code.SchauderTranslates.Lp.HaarModel

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem norm_haarIntervalAtom_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (n k : ℕ) (hk : k < 2 ^ n) :
    ‖haarIntervalAtom p n k‖ ^ p.toReal = 1 / (2 : ℝ) ^ n := by
  have hpr : p.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp0, hpfin⟩
  rw [norm_haarIntervalAtom p hp0 hpfin n k hk,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ n),
    div_mul_cancel₀ _ hpr, Real.rpow_one]

theorem haarScale_square (n : ℕ) : haarScale n ^ (2 : ℝ) = (2 : ℝ) ^ n := by
  rw [haarScale, ← Real.rpow_mul (dyadic_denominator_pos n).le]
  norm_num

theorem norm_haar_difference_rpow {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (n k : ℕ) (hk : k < 2 ^ n) :
    ‖haarIntervalAtom p (n + 1) (2 * k) - haarIntervalAtom p (n + 1) (2 * k + 1)‖ ^ p.toReal =
      1 / (2 : ℝ) ^ n := by
  have hl : 2 * k < 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hr : 2 * k + 1 < 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hd := (haarIntervalAtom_supported p (n + 1) (2 * k)).ae_disjoint
    (haarIntervalAtom_supported p (n + 1) (2 * k + 1)) (dyadicInterval_children_disjoint n k)
  have hd' : ∀ᵐ x ∂haarMeasure, haarIntervalAtom p (n + 1) (2 * k) x = 0 ∨
      (-haarIntervalAtom p (n + 1) (2 * k + 1)) x = 0 := by
    filter_upwards [hd, Lp.coeFn_neg (haarIntervalAtom p (n + 1) (2 * k + 1))] with x hx hn
    rcases hx with hx | hx
    · exact Or.inl hx
    · right
      rw [hn]
      change -haarIntervalAtom p (n + 1) (2 * k + 1) x = 0
      simp [hx]
  rw [sub_eq_add_neg, norm_add_rpow_of_ae_disjoint _ _ hp0 hpfin hd', norm_neg,
    norm_haarIntervalAtom_rpow hp0 hpfin (n + 1) (2 * k) hl,
    norm_haarIntervalAtom_rpow hp0 hpfin (n + 1) (2 * k + 1) hr, pow_succ]
  field_simp
  norm_num

theorem norm_haarFunction_two (n k : ℕ) (hk : k < 2 ^ n) : ‖haarFunction 2 n k‖ = 1 := by
  have hp : ‖haarFunction 2 n k‖ ^ (2 : ℝ) = 1 := by
    rw [haarFunction, norm_smul, Real.norm_eq_abs, abs_of_pos (haarScale_pos n),
      Real.mul_rpow (haarScale_pos n).le (norm_nonneg _), haarScale_square]
    have he := norm_haar_difference_rpow (p := 2) (by norm_num) (by norm_num) n k hk
    norm_num only [ENNReal.toReal_ofNat] at he
    rw [he]
    exact mul_one_div_cancel (dyadic_denominator_pos n).ne'
  apply (Real.rpow_left_inj (norm_nonneg _) zero_le_one (by norm_num : (2 : ℝ) ≠ 0)).mp
  simpa using hp

theorem norm_haarAtom_two (a : HaarIndex) : ‖haarAtom 2 a‖ = 1 := by
  rcases a with _ | ⟨n, k⟩
  · exact norm_haarConstant 2 (by norm_num) (by norm_num)
  · exact norm_haarFunction_two n k k.isLt

end SchauderTranslates.LpConstruction
