import Lean_Code.SchauderTranslates.RowSplit
import Lean_Code.SchauderTranslates.SelectiveColumnCuts

/-!
# Norm of a sum of two idempotents (paper: `h2:eq:selective-prefix`)

For every idempotent `Q` on a finite-dimensional Hilbert space,
`max 1 ‖Q‖² = 1 + ‖Q − Q†‖²` (`projection_max_norm_skew`). If `P`, `R` and `P + R` are
idempotent, the triangle inequality for the skew parts gives
`‖P + R‖² ≤ 1 + (√(A − 1) + √(B − 1))²` whenever `‖P‖² ≤ A`, `‖R‖² ≤ B` and `1 ≤ A, B`.

Coordinate masks (diagonal `0/1` matrices) conjugated by the square root of a positive
definite Gram matrix are idempotent, so the bound applies to
`gramConjugate H (D₁ + D₂)` for coordinate masks `D₁`, `D₂`, `D₁ + D₂`.
-/

noncomputable section
open Matrix ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates

section Abstract
variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- The skew part of an idempotent of squared norm at most `A ≥ 1`. -/
theorem idempotent_skew_norm_sq_le (P : E →L[𝕜] E) (hP : ∀ x, P (P x) = P x)
    {A : ℝ} (hA : 1 ≤ A) (hPA : ‖P‖ ^ 2 ≤ A) : ‖P - P†‖ ^ 2 ≤ A - 1 := by
  have h := projection_max_norm_skew P hP
  have hm : max 1 (‖P‖ ^ 2) ≤ A := max_le hA hPA
  linarith

theorem idempotent_skew_norm_le (P : E →L[𝕜] E) (hP : ∀ x, P (P x) = P x)
    {A : ℝ} (hA : 1 ≤ A) (hPA : ‖P‖ ^ 2 ≤ A) : ‖P - P†‖ ≤ Real.sqrt (A - 1) :=
  Real.le_sqrt_of_sq_le (idempotent_skew_norm_sq_le P hP hA hPA)

/-- Paper `h2:eq:selective-prefix`: the norm of a sum of two idempotents whose sum is
idempotent. -/
theorem idempotent_sum_norm_sq_le (P R : E →L[𝕜] E) (hP : ∀ x, P (P x) = P x)
    (hR : ∀ x, R (R x) = R x) (hPR : ∀ x, (P + R) ((P + R) x) = (P + R) x)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hPA : ‖P‖ ^ 2 ≤ A) (hRB : ‖R‖ ^ 2 ≤ B) :
    ‖P + R‖ ^ 2 ≤ 1 + (Real.sqrt (A - 1) + Real.sqrt (B - 1)) ^ 2 := by
  have h := projection_max_norm_skew (P + R) hPR
  have hs : (P + R) - (P + R)† = (P - P†) + (R - R†) := by
    rw [map_add]
    abel
  have h1 := idempotent_skew_norm_le P hP hA hPA
  have h2 := idempotent_skew_norm_le R hR hB hRB
  have h3 : ‖(P + R) - (P + R)†‖ ≤ Real.sqrt (A - 1) + Real.sqrt (B - 1) := by
    rw [hs]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have h4 : ‖(P + R) - (P + R)†‖ ^ 2 ≤ (Real.sqrt (A - 1) + Real.sqrt (B - 1)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h3 2
  have h5 : ‖P + R‖ ^ 2 ≤ max 1 (‖P + R‖ ^ 2) := le_max_right _ _
  linarith

end Abstract

section Gram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugating an idempotent coefficient matrix by a positive definite Gram root gives an
idempotent operator. -/
theorem gramConjugate_idempotent {H : Matrix ι ι ℂ} (hH : H.PosDef) {D : Matrix ι ι ℂ}
    (hD : D * D = D) (x : EuclideanSpace ℂ ι) :
    gramConjugate H D (gramConjugate H D x) = gramConjugate H D x := by
  have hi (z : EuclideanSpace ℂ ι) : gramRootInv H (gramRoot H z) = z := by
    rw [← ContinuousLinearMap.comp_apply, gramRoot_inv_mul hH, one_apply_eq_self]
  have hm (z : EuclideanSpace ℂ ι) :
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) D ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) D z) =
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) D z := by
    have h := congrArg (fun f : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι => f z)
      (map_mul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) D D)
    rw [hD] at h
    exact h.symm
  simp only [gramConjugate, ContinuousLinearMap.comp_apply, hi, hm]

/-- A diagonal `0/1` matrix is idempotent. -/
theorem diagonal_mask_mul_self (p : ι → Prop) [DecidablePred p] :
    (Matrix.diagonal fun i => if p i then (1 : ℂ) else 0) *
      (Matrix.diagonal fun i => if p i then (1 : ℂ) else 0) =
      Matrix.diagonal fun i => if p i then (1 : ℂ) else 0 := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

/-- The sharp bound for the sum of two coordinate masks whose sum is a coordinate mask. -/
theorem gramConjugate_mask_sum_sq_le {H : Matrix ι ι ℂ} (hH : H.PosDef)
    {D₁ D₂ : Matrix ι ι ℂ} (h₁ : D₁ * D₁ = D₁) (h₂ : D₂ * D₂ = D₂)
    (h₁₂ : (D₁ + D₂) * (D₁ + D₂) = D₁ + D₂)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hPA : ‖gramConjugate H D₁‖ ^ 2 ≤ A) (hRB : ‖gramConjugate H D₂‖ ^ 2 ≤ B) :
    ‖gramConjugate H (D₁ + D₂)‖ ^ 2 ≤ 1 + (Real.sqrt (A - 1) + Real.sqrt (B - 1)) ^ 2 := by
  have hsum := gramConjugate_idempotent hH h₁₂
  rw [gramConjugate_add] at hsum ⊢
  exact idempotent_sum_norm_sq_le _ _ (gramConjugate_idempotent hH h₁)
    (gramConjugate_idempotent hH h₂) hsum hA hB hPA hRB

end Gram

end SchauderTranslates.Sharp
