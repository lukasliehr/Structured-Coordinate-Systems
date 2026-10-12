import Lean_Code.SchauderTranslates.RowSplit

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The first split endpoint adds only an orthogonal identity coordinate. -/
theorem splitRow_zero_norm_sq_le (P : E →L[ℝ] E) (x y : E) :
    ‖splitRowOperator P x y 0 0‖ ^ 2 ≤ max 1 (‖P‖ ^ 2) := by
  apply opNorm_sq_le_of_pointwise _ (le_trans zero_le_one (le_max_left _ _))
  intro z
  simp only [splitRowOperator_apply, zero_mul, zero_add, zero_smul, add_zero, sub_zero, one_mul]
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖P z.fst‖ ^ 2 + ‖z.snd‖ ^ 2 ≤ max 1 (‖P‖ ^ 2) * (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2)
  have hP := pow_le_pow_left₀ (norm_nonneg _) (P.le_opNorm z.fst) 2
  have h1 := mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (‖P‖ ^ 2)) (sq_nonneg ‖z.snd‖)
  have h2 := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (‖P‖ ^ 2)) (sq_nonneg ‖z.fst‖)
  nlinarith

/-- The second endpoint is the next old prefix with an orthogonal zero coordinate. -/
theorem splitRow_one_norm_sq_le (P : E →L[ℝ] E) (x y : E) :
    ‖splitRowOperator P x y 1 0‖ ^ 2 ≤ ‖P + rankOne ℝ x y‖ ^ 2 := by
  apply opNorm_sq_le_of_pointwise _ (sq_nonneg _)
  intro z
  simp only [splitRowOperator_apply, one_mul, zero_mul, add_zero, sub_self]
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖(P + rankOne ℝ x y) z.fst‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2 ≤
    ‖P + rankOne ℝ x y‖ ^ 2 * (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2)
  have hP := pow_le_pow_left₀ (norm_nonneg _) ((P + rankOne ℝ x y).le_opNorm z.fst) 2
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  nlinarith [mul_nonneg (sq_nonneg ‖P + rankOne ℝ x y‖) (sq_nonneg ‖z.snd‖)]

/-- A nonzero vector fixed by the next old prefix forces its norm to be at least one. -/
theorem nextPrefix_norm_sq_ge_one (P : E →L[ℝ] E) (x y : E)
    (hPx : P x = 0) (hxy : inner ℝ x y = 1) : 1 ≤ ‖P + rankOne ℝ x y‖ ^ 2 := by
  have hxy' : inner ℝ y x = 1 := by rw [real_inner_comm, hxy]
  have hx : x ≠ 0 := by intro hx; simp [hx] at hxy
  have hfix : (P + rankOne ℝ x y) x = x := by simp [rankOne_apply, hPx, hxy']
  have h := (P + rankOne ℝ x y).le_opNorm x
  rw [hfix] at h
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : 1 ≤ ‖P + rankOne ℝ x y‖ := by nlinarith
  nlinarith

/-- Cauchy–Schwarz and the primal norm bound make the row-splitting cost nonnegative. -/
theorem rowSplit_cost_nonneg (x y : E) (hxy : inner ℝ x y = 1) (hm : ‖x‖ ^ 2 ≤ 1) :
    0 ≤ (1 - ‖x‖ ^ 2) * (‖y‖ ^ 2 - 1) := by
  have hx : ‖x‖ ≤ 1 := by nlinarith [norm_nonneg x]
  have hh := real_inner_le_norm x y
  rw [hxy] at hh
  have hmul := mul_le_mul_of_nonneg_right hx (norm_nonneg y)
  have hy : 1 ≤ ‖y‖ := by nlinarith
  exact mul_nonneg (sub_nonneg.mpr hm) (by nlinarith)

section Finite
variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Uniform split-row cost in terms of the two original endpoint prefixes, including the empty one. -/
theorem real_row_split_quarter (P : E →L[ℝ] E) (x y : E)
    (hP : ∀ z, P (P z) = P z) (hPx : P x = 0)
    (hyP : ∀ z, inner ℝ y (P z) = 0) (hxy : inner ℝ x y = 1)
    (hm : ‖x‖ ^ 2 ≤ 1) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖splitRowOperator P x y t (Real.sqrt (t * (1 - t)))‖ ^ 2 ≤
      max (‖P‖ ^ 2) (‖P + rankOne ℝ x y‖ ^ 2) +
        (1 / 4) * (1 - ‖x‖ ^ 2) * (‖y‖ ^ 2 - 1) := by
  have h := real_row_split P x y hP hPx hyP hxy hm ht ht1
  have hnext := nextPrefix_norm_sq_ge_one P x y hPx hxy
  have h0 := (splitRow_zero_norm_sq_le P x y).trans
    (max_le (hnext.trans (le_max_right _ _)) (le_max_left _ _))
  have h1 := (splitRow_one_norm_sq_le P x y).trans (le_max_right (‖P‖ ^ 2) _)
  have hend := max_le h0 h1
  have htq : t * (1 - t) ≤ (1 / 4 : ℝ) := by nlinarith [sq_nonneg (t - 1 / 2)]
  have hcost := mul_le_mul_of_nonneg_right htq (rowSplit_cost_nonneg x y hxy hm)
  nlinarith

end Finite
end SchauderTranslates
