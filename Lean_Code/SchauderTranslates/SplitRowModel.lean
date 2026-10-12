import Lean_Code.SchauderTranslates.SkewCompression

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The row-splitting projection, with the off-diagonal scalar explicit. -/
def splitRowOperator (P : E →L[ℝ] E) (x y : E) (t s : ℝ) :
    WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.toContinuousLinearMap.comp
    (((P + t • rankOne ℝ x y).comp (WithLp.fstL 2 ℝ E ℝ) +
      (s • toSpanSingleton ℝ x).comp (WithLp.sndL 2 ℝ E ℝ)).prod
      ((s • innerSL ℝ y).comp (WithLp.fstL 2 ℝ E ℝ) +
        (1 - t) • WithLp.sndL 2 ℝ E ℝ))

@[simp] theorem splitRowOperator_apply (P : E →L[ℝ] E) (x y : E) (t s : ℝ)
    (z : WithLp 2 (E × ℝ)) :
    splitRowOperator P x y t s z = WithLp.toLp 2
      (P z.fst + (t * inner ℝ y z.fst + s * z.snd) • x,
        s * inner ℝ y z.fst + (1 - t) * z.snd) := by
  simp [splitRowOperator, rankOne_apply, smul_smul, add_smul, add_assoc]

theorem splitRowOperator_idempotent (P : E →L[ℝ] E) (x y : E) (t s : ℝ)
    (hP : ∀ z, P (P z) = P z) (hPx : P x = 0)
    (hyP : ∀ z, inner ℝ y (P z) = 0) (hyx : inner ℝ y x = 1)
    (hs : s ^ 2 = t * (1 - t)) :
    ∀ z, splitRowOperator P x y t s (splitRowOperator P x y t s z) =
      splitRowOperator P x y t s z := by
  intro z
  simp only [splitRowOperator_apply]
  apply (WithLp.equiv 2 (E × ℝ)).injective
  apply Prod.ext
  · change P (P z.fst + (t * inner ℝ y z.fst + s * z.snd) • x) +
        (t * inner ℝ y (P z.fst + (t * inner ℝ y z.fst + s * z.snd) • x) +
          s * (s * inner ℝ y z.fst + (1 - t) * z.snd)) • x =
      P z.fst + (t * inner ℝ y z.fst + s * z.snd) • x
    simp only [map_add, map_smul, hP, hPx, smul_zero, add_zero,
      inner_add_right, real_inner_smul_right, hyP, hyx, mul_one, zero_add]
    congr 2
    nlinarith [congrArg (fun r : ℝ => r * inner ℝ y z.fst) hs]
  · change s * inner ℝ y (P z.fst + (t * inner ℝ y z.fst + s * z.snd) • x) +
        (1 - t) * (s * inner ℝ y z.fst + (1 - t) * z.snd) =
      s * inner ℝ y z.fst + (1 - t) * z.snd
    simp only [inner_add_right, real_inner_smul_right, hyP, hyx, mul_one, zero_add]
    nlinarith [congrArg (fun r : ℝ => r * z.snd) hs]

theorem splitRowOperator_ne_zero (P : E →L[ℝ] E) (x y : E) (t s : ℝ)
    (hPx : P x = 0) (hyx : inner ℝ y x = 1) : splitRowOperator P x y t s ≠ 0 := by
  intro hz
  have hx : x ≠ 0 := by intro hx; simp [hx] at hyx
  by_cases ht : t = 1
  · have h := congrArg (fun Q : WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ) =>
      (Q (WithLp.toLp 2 (x, (0 : ℝ)))).fst) hz
    simp [splitRowOperator_apply, ht, hPx, hyx] at h
    exact hx h
  · have h := congrArg (fun Q : WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ) =>
      (Q (WithLp.toLp 2 ((0 : E), (1 : ℝ)))).snd) hz
    simp [splitRowOperator_apply] at h
    exact ht (by linarith)

section Complete
variable [CompleteSpace E]

theorem splitRowOperator_adjoint_apply (P : E →L[ℝ] E) (x y : E) (t s : ℝ)
    (z : WithLp 2 (E × ℝ)) :
    ((splitRowOperator P x y t s)†) z = WithLp.toLp 2
      ((P†) z.fst + (t * inner ℝ x z.fst + s * z.snd) • y,
        s * inner ℝ x z.fst + (1 - t) * z.snd) := by
  apply ext_inner_right ℝ
  intro w
  rw [adjoint_inner_left]
  simp only [splitRowOperator_apply, WithLp.prod_inner_apply, inner_add_right,
    inner_add_left, real_inner_smul_right, real_inner_smul_left, adjoint_inner_left,
    Real.inner_apply]
  change inner ℝ z.fst (P w.fst) +
      (t * inner ℝ y w.fst + s * w.snd) * inner ℝ z.fst x +
      (z.snd * (s * inner ℝ y w.fst) + z.snd * ((1 - t) * w.snd)) =
    inner ℝ z.fst (P w.fst) +
      (t * inner ℝ x z.fst + s * z.snd) * inner ℝ y w.fst +
      (s * inner ℝ x z.fst * w.snd + (1 - t) * z.snd * w.snd)
  rw [real_inner_comm x z.fst]
  ring

theorem splitRowOperator_skew (P : E →L[ℝ] E) (x y : E) (t s : ℝ) :
    splitRowOperator P x y t s - (splitRowOperator P x y t s)† =
      skewArrowhead (P - P† + t • rankTwoSkew x y) (x - y) s := by
  ext z
  simp only [sub_apply, splitRowOperator_apply, splitRowOperator_adjoint_apply,
    skewArrowhead_apply]
  apply (WithLp.equiv 2 (E × ℝ)).injective
  apply Prod.ext
  · change (P z.fst + (t * inner ℝ y z.fst + s * z.snd) • x) -
        ((P†) z.fst + (t * inner ℝ x z.fst + s * z.snd) • y) =
      (P - P† + t • rankTwoSkew x y) z.fst + (s * z.snd) • (x - y)
    simp only [add_apply, sub_apply, smul_apply, rankTwoSkew_apply]
    module
  · change (s * inner ℝ y z.fst + (1 - t) * z.snd) -
        (s * inner ℝ x z.fst + (1 - t) * z.snd) =
      -s * inner ℝ (x - y) z.fst
    rw [inner_sub_left]
    ring

theorem rankOne_real_adjoint (x y : E) : (rankOne ℝ x y)† = rankOne ℝ y x := by
  ext z
  apply ext_inner_right ℝ
  intro w
  rw [adjoint_inner_left]
  simp only [rankOne_apply, real_inner_smul_right, real_inner_smul_left]
  rw [real_inner_comm x z]
  ring

theorem operator_skew_is_skew (P : E →L[ℝ] E) (z w : E) :
    inner ℝ ((P - P†) z) w = -inner ℝ z ((P - P†) w) := by
  simp only [sub_apply, inner_sub_left, inner_sub_right, adjoint_inner_left,
    adjoint_inner_right]
  ring

/-- The full split-row skew estimate, without any projection assumptions on `P`. -/
theorem split_row_skew_compression [FiniteDimensional ℝ E]
    (P : E →L[ℝ] E) (x y : E) (hxy : inner ℝ x y = 1) (hm : ‖x‖ ^ 2 ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖splitRowOperator P x y t (Real.sqrt (t * (1 - t))) -
      (splitRowOperator P x y t (Real.sqrt (t * (1 - t))))†‖ ^ 2 ≤
    max (‖P - P†‖ ^ 2)
      (‖(P + rankOne ℝ x y) - (P + rankOne ℝ x y)†‖ ^ 2) +
        t * (1 - t) * (1 - ‖x‖ ^ 2) * (‖y‖ ^ 2 - 1) := by
  let J₀ := P - P†
  let J₁ := (P + rankOne ℝ x y) - (P + rankOne ℝ x y)†
  have hdiff : J₁ - J₀ = rankTwoSkew x y := by
    dsimp [J₀, J₁]
    rw [map_add, rankOne_real_adjoint]
    unfold rankTwoSkew
    abel
  have hα : (Real.sqrt (1 - t)) ^ 2 = 1 - t := Real.sq_sqrt (sub_nonneg.mpr ht1)
  have hβ : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht
  have hprod : Real.sqrt (1 - t) * Real.sqrt t = Real.sqrt (t * (1 - t)) := by
    rw [← Real.sqrt_mul (sub_nonneg.mpr ht1), mul_comm]
  have hc := rankTwo_skew_interpolation_bound J₀ J₁ (operator_skew_is_skew P)
    (operator_skew_is_skew (P + rankOne ℝ x y)) x y hxy hm hdiff
    (Real.sqrt (1 - t)) (Real.sqrt t) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (by rw [hα, hβ]; ring)
  have hinter : (1 - t) • J₀ + t • J₁ = J₀ + t • rankTwoSkew x y := by
    rw [← hdiff]
    module
  rw [hα, hβ, hprod, Real.sq_sqrt (mul_nonneg ht (sub_nonneg.mpr ht1)), hinter] at hc
  rw [splitRowOperator_skew]
  exact hc

end Complete
end SchauderTranslates
