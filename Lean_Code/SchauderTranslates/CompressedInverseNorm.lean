import Lean_Code.SchauderTranslates.PositiveOperatorNorm

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Inverse compression also bounds the Hilbert operator norm of the compressed inverse. -/
theorem compressed_inverse_norm_le (B C : H →L[ℂ] H) {b : ℝ} (hb : 0 < b)
    (hB : ∀ x, b * ‖x‖ ^ 2 ≤ (inner ℂ (B x) x).re)
    (hs : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (hBC : ∀ x, B (C x) = x) (F : Submodule ℂ H) [CompleteSpace F] :
    ‖((coerciveEquiv (compressedOperator B F) hb
      (compressedOperator_coercive B hB F)).symm : F →L[ℂ] F)‖ ≤ ‖C‖ := by
  let D : F →L[ℂ] F := (coerciveEquiv (compressedOperator B F) hb
    (compressedOperator_coercive B hB F)).symm
  have hBD (x : F) : compressedOperator B F (D x) = x :=
    (coerciveEquiv (compressedOperator B F) hb
      (compressedOperator_coercive B hB F)).apply_symm_apply x
  have hsF (x y : F) : inner ℂ (compressedOperator B F x) y =
      inner ℂ x (compressedOperator B F y) := by
    rw [compressedOperator_inner]
    change inner ℂ (B (x : H)) (y : H) =
      inner ℂ x (F.orthogonalProjectionOnto (B (y : H)))
    rw [F.inner_orthogonalProjectionOnto_eq_of_mem_left, hs]
  have hnF (x : F) : 0 ≤ (inner ℂ (compressedOperator B F x) x).re :=
    (mul_nonneg hb.le (sq_nonneg _)).trans (compressedOperator_coercive B hB F x)
  have hD := inverse_operator_positive (compressedOperator B F) D hsF hnF hBD
  apply positive_operator_norm_le D (norm_nonneg C) hD.1 hD.2
  intro x
  have he : (coerciveEquiv B hb hB).symm (x : H) = C (x : H) := by
    apply (coercive_bijective B hb hB).injective
    exact ((coerciveEquiv B hb hB).apply_symm_apply _).trans (hBC _).symm
  have hc := inverse_compression B hb hB hs F x
  rw [he] at hc
  have hx : (inner ℂ (D x) x).re = (inner ℂ x (D x)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hx]
  refine hc.trans ?_
  calc
    (inner ℂ (x : H) (C (x : H))).re ≤ ‖(x : H)‖ * ‖C (x : H)‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    _ ≤ ‖(x : H)‖ * (‖C‖ * ‖(x : H)‖) :=
      mul_le_mul_of_nonneg_left (C.le_opNorm _) (norm_nonneg _)
    _ = ‖C‖ * ‖x‖ ^ 2 := by rw [Submodule.coe_norm]; ring

end SchauderTranslates
