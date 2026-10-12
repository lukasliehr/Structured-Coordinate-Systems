import Lean_Code.SchauderTranslates.RepeatedMatrix
import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open Matrix ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- One copy's coefficient vector in the flat, copy-major ordering. -/
def coefficientCopy {L n : ℕ} (x : EuclideanSpace ℂ (Fin (L * n))) (i : Fin L) :
    EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun a => x (finProdFinEquiv (i, a)))

theorem repeatedMatrix_mulVec_entry {L n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (x : Fin (L * n) → ℂ) (i : Fin L) (a : Fin n) :
    (repeatedMatrix L B *ᵥ x) (finProdFinEquiv (i, a)) =
      (B *ᵥ (fun b => x (finProdFinEquiv (i, b)))) a := by
  simp only [Matrix.mulVec, dotProduct, ← finProdFinEquiv.sum_comp,
    Fintype.sum_prod_type, repeatedMatrix_entry]
  simp

theorem repeatedMatrix_quadratic_sum {L n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin (L * n))) :
    coefficientQuadratic (repeatedMatrix L B) x =
      ∑ i : Fin L, coefficientQuadratic B (coefficientCopy x i) := by
  simp only [coefficientQuadratic_eq_dot, dotProduct]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, Pi.star_apply, repeatedMatrix_mulVec_entry, map_sum]
  rfl

theorem coefficientCopy_norm_sq {L n : ℕ} (x : EuclideanSpace ℂ (Fin (L * n))) :
    ‖x‖ ^ 2 = ∑ i : Fin L, ‖coefficientCopy x i‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  rfl

/-- A direct sum retains every scalar quadratic upper bound with the same constant. -/
theorem repeatedMatrix_quadratic_le {L n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    {b : ℝ} (h : ∀ v : EuclideanSpace ℂ (Fin n), coefficientQuadratic B v ≤ b * ‖v‖ ^ 2)
    (x : EuclideanSpace ℂ (Fin (L * n))) :
    coefficientQuadratic (repeatedMatrix L B) x ≤ b * ‖x‖ ^ 2 := by
  rw [repeatedMatrix_quadratic_sum, coefficientCopy_norm_sq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun _ _ => h _)

/-- The elementary Hilbert-norm upper bound for any matrix quadratic form. -/
theorem coefficientQuadratic_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (x : EuclideanSpace ℂ ι) :
    coefficientQuadratic B x ≤ ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) B‖ * ‖x‖ ^ 2 := by
  let T := (Matrix.toEuclideanCLM (𝕜 := ℂ)) B
  change RCLike.re (inner ℂ x (T x)) ≤ ‖T‖ * ‖x‖ ^ 2
  calc
    _ ≤ ‖inner ℂ x (T x)‖ := RCLike.re_le_norm _
    _ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

end SchauderTranslates
