import Lean_Code.SchauderTranslates.ScalarNumerics

noncomputable section
namespace SchauderTranslates

/-- The reciprocal-square margin provided by the quadratic decrease in mass deficit. -/
theorem scalar_floor_reciprocal_margin {x y : ℝ} (hx : 0 < x) (hxmax : x ≤ 1 / 10)
    (hy : 0 < y) (hymax : y ≤ x - 3 * x ^ 2 / 4) :
    1 / x ^ 2 + 1 / (2 * x) < (1 - y) / y ^ 2 := by
  let t := x * (1 - 3 * x / 4)
  have hq : 0 < 1 - 3 * x / 4 := by linarith
  have ht : 0 < t := mul_pos hx hq
  have hyt : y ≤ t := by dsimp [t]; nlinarith
  have htx : t ≤ x := by dsimp [t]; nlinarith [sq_nonneg x]
  have ht1 : t < 1 := by linarith
  have hid : (1 - t) / t ^ 2 - 1 / x ^ 2 - 1 / (2 * x) =
      3 * (10 - 3 * x) / (32 * (1 - 3 * x / 4) ^ 2) := by
    dsimp [t]
    have hq' : 4 - 3 * x ≠ 0 := by linarith
    field_simp [hx.ne', hq.ne', hq']
    ring_nf
    have hd : 16 - x * 24 + x ^ 2 * 9 ≠ 0 := by
      nlinarith [sq_pos_of_ne_zero hq']
    field_simp [hd]
    ring
  have hp : 0 < 3 * (10 - 3 * x) / (32 * (1 - 3 * x / 4) ^ 2) := by
    apply div_pos
    · have : 0 < 10 - 3 * x := by linarith
      positivity
    · positivity
  have hlow : 1 / x ^ 2 + 1 / (2 * x) < (1 - t) / t ^ 2 := by linarith
  refine hlow.trans_le ?_
  exact div_le_div₀ (by linarith) (by linarith) (sq_pos_of_pos hy)
    (pow_le_pow_left₀ hy.le hyt 2)

/-- The real numerical implication used after the inverse block estimate. -/
theorem scalar_floor_norm_step {x y h h' : ℝ} (hx : 0 < x) (hxmax : x ≤ 1 / 10)
    (hy : 0 < y) (hymax : y ≤ x - 3 * x ^ 2 / 4)
    (hh : h ≤ x⁻¹ ^ 2) (hh' : h' ≤ (h + 1 + 1 / 323) / (1 - y)) :
    h' ≤ y⁻¹ ^ 2 := by
  have hyx : y ≤ x := by nlinarith [sq_nonneg x]
  have hm : 0 < 1 - y := by linarith
  have hmargin := scalar_floor_reciprocal_margin hx hxmax hy hymax
  have hlarge : (5 : ℝ) ≤ 1 / (2 * x) :=
    (le_div_iff₀ (by positivity : 0 < 2 * x)).mpr (by linarith)
  have hu : h + 1 + 1 / 323 ≤ (1 - y) / y ^ 2 := by
    rw [inv_pow, ← one_div] at hh
    linarith
  calc
    h' ≤ (h + 1 + 1 / 323) / (1 - y) := hh'
    _ ≤ ((1 - y) / y ^ 2) / (1 - y) := div_le_div_of_nonneg_right hu hm.le
    _ = y⁻¹ ^ 2 := by field_simp

end SchauderTranslates
