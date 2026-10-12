import Lean_Code.SchauderTranslates.UniformRowSplit

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Row splitting on two full coefficient copies; inactive old rows are kept in `R`. -/
def extendedSplitRowOperator (P : E →L[ℝ] E) (x y : E) (R : K →L[ℝ] K) (u : K) (t s : ℝ) :
    WithLp 2 (E × K) →L[ℝ] WithLp 2 (E × K) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E K).symm.toContinuousLinearMap.comp
    (((P + t • rankOne ℝ x y).comp (WithLp.fstL 2 ℝ E K) +
      (s • (toSpanSingleton ℝ x).comp (innerSL ℝ u)).comp (WithLp.sndL 2 ℝ E K)).prod
      ((s • (toSpanSingleton ℝ u).comp (innerSL ℝ y)).comp (WithLp.fstL 2 ℝ E K) +
        (R + (1 - t) • rankOne ℝ u u).comp (WithLp.sndL 2 ℝ E K)))

@[simp] theorem extendedSplitRowOperator_apply (P : E →L[ℝ] E) (x y : E)
    (R : K →L[ℝ] K) (u : K) (t s : ℝ) (z : WithLp 2 (E × K)) :
    extendedSplitRowOperator P x y R u t s z = WithLp.toLp 2
      (P z.fst + (t * inner ℝ y z.fst + s * inner ℝ u z.snd) • x,
        R z.snd + (s * inner ℝ y z.fst + (1 - t) * inner ℝ u z.snd) • u) := by
  simp [extendedSplitRowOperator, rankOne_apply, smul_smul, add_smul, add_assoc, add_comm, add_left_comm]

/-- A contraction annihilating a unit vector leaves enough energy for its scalar coordinate. -/
theorem contraction_orthogonal_coordinate (R : K →L[ℝ] K) (u : K) (hu : ‖u‖ = 1)
    (hRu : R u = 0) (hR : ‖R‖ ≤ 1) (w : K) :
    ‖R w‖ ^ 2 + (inner ℝ u w) ^ 2 ≤ ‖w‖ ^ 2 := by
  have he : R (w - inner ℝ u w • u) = R w := by simp [hRu]
  have h := R.le_opNorm (w - inner ℝ u w • u)
  rw [he] at h
  have h1 := h.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hR (norm_nonneg (w - inner ℝ u w • u)))
  have hs := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [norm_sub_sq_real, real_norm_smul_sq, hu, one_pow, mul_one,
    real_inner_smul_right] at hs
  have hi : inner ℝ w u = inner ℝ u w := real_inner_comm _ _
  simp only [hi] at hs
  nlinarith

/-- Orthogonal inactive rows cost at most the maximum of one and the small split-row norm. -/
theorem extendedSplitRow_norm_sq_le (P : E →L[ℝ] E) (x y : E)
    (R : K →L[ℝ] K) (u : K) (t s : ℝ) (hu : ‖u‖ = 1)
    (hRu : R u = 0) (huR : ∀ w, inner ℝ u (R w) = 0) (hR : ‖R‖ ≤ 1)
    {C : ℝ} (hC : 1 ≤ C) (hsmall : ‖splitRowOperator P x y t s‖ ^ 2 ≤ C) :
    ‖extendedSplitRowOperator P x y R u t s‖ ^ 2 ≤ C := by
  apply opNorm_sq_le_of_pointwise _ (zero_le_one.trans hC)
  intro z
  have hsmallv := pow_le_pow_left₀ (norm_nonneg _)
    ((splitRowOperator P x y t s).le_opNorm (WithLp.toLp 2 (z.fst, inner ℝ u z.snd))) 2
  have hsmallC := mul_le_mul_of_nonneg_right hsmall
    (sq_nonneg ‖(WithLp.toLp 2 (z.fst, inner ℝ u z.snd) : WithLp 2 (E × ℝ))‖)
  have hc := contraction_orthogonal_coordinate R u hu hRu hR z.snd
  have hz : inner ℝ (R z.snd) u = 0 := by rw [real_inner_comm, huR]
  rw [extendedSplitRowOperator_apply, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2]
  change ‖P z.fst + (t * inner ℝ y z.fst + s * inner ℝ u z.snd) • x‖ ^ 2 +
    ‖R z.snd + (s * inner ℝ y z.fst + (1 - t) * inner ℝ u z.snd) • u‖ ^ 2 ≤
      C * (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2)
  have hnorm (a : ℝ) : ‖R z.snd + a • u‖ ^ 2 = ‖R z.snd‖ ^ 2 + a ^ 2 := by
    rw [norm_add_sq_real, real_norm_smul_sq, hu, one_pow, mul_one,
      real_inner_smul_right, hz, mul_zero, mul_zero, add_zero]
  rw [hnorm]
  rw [splitRowOperator_apply, mul_pow, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2] at hsmallv
  rw [WithLp.prod_norm_sq_eq_of_L2] at hsmallC
  change ‖P z.fst + (t * inner ℝ y z.fst + s * inner ℝ u z.snd) • x‖ ^ 2 +
    ‖s * inner ℝ y z.fst + (1 - t) * inner ℝ u z.snd‖ ^ 2 ≤
    ‖splitRowOperator P x y t s‖ ^ 2 * (‖z.fst‖ ^ 2 + ‖inner ℝ u z.snd‖ ^ 2) at hsmallv
  change ‖splitRowOperator P x y t s‖ ^ 2 * (‖z.fst‖ ^ 2 + ‖inner ℝ u z.snd‖ ^ 2) ≤
    C * (‖z.fst‖ ^ 2 + ‖inner ℝ u z.snd‖ ^ 2) at hsmallC
  simp only [Real.norm_eq_abs, sq_abs] at hsmallv hsmallC
  have hrem := mul_nonneg (sub_nonneg.mpr hC) (sq_nonneg ‖R z.snd‖)
  nlinarith

end SchauderTranslates
