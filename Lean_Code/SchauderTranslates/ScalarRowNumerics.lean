import Mathlib

namespace SchauderTranslates

/-- The separate constant row stays strictly below the initial squared-prefix budget. -/
theorem scalar_constant_row_lt_two {ε Z : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1 / 10)
    (hZ : 0 ≤ Z) (hZ1 : Z ≤ 1 / 323) :
    1 + Z + ε * (Z + ε) / (4 * (1 - ε)) < 2 := by
  have hd : 0 < 4 * (1 - ε) := by linarith
  have heZ : ε * Z ≤ (1 / 10 : ℝ) * (1 / 323) :=
    mul_le_mul hε1 hZ1 hZ (by norm_num)
  have he2 : ε ^ 2 ≤ (1 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ hε hε1 2
  have hsmall : ε * (Z + ε) / (4 * (1 - ε)) < (1 / 100 : ℝ) := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  linarith

/-- In the scalar range, the independent-copy denominator has a uniform numerical margin. -/
theorem scalar_copy_prefix_cost {q Z η : ℝ} (hq : 2 ≤ q) (hq3 : q < 3)
    (hZ : Z ≤ 1 / 323) (hη : 0 ≤ η) :
    q + q ^ 2 * η / (q - 1 - Z) ≤ q + 10 * η := by
  have hd : 0 < q - 1 - Z := by linarith
  have hq2 : q ^ 2 < 9 := by nlinarith
  have hc : q ^ 2 ≤ 10 * (q - 1 - Z) := by nlinarith
  apply add_le_add le_rfl
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_right hc hη]

end SchauderTranslates
