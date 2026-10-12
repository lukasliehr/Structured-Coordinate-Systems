import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open Matrix
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Orthonormal columns act isometrically for the Euclidean norm. -/
theorem matrix_orthonormal_columns_inner {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) (x y : EuclideanSpace ℂ κ) :
    inner ℂ (U.toEuclideanLin x) (U.toEuclideanLin y) = inner ℂ x y := by
  simp only [Matrix.toEuclideanLin_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp]
  rw [dotProduct_comm (U *ᵥ y.ofLp), Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hU, Matrix.one_mulVec, dotProduct_comm]

theorem matrix_orthonormal_columns_norm {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {U : Matrix ι κ ℂ} (hU : Uᴴ * U = 1) (x : EuclideanSpace ℂ κ) :
    ‖U.toEuclideanLin x‖ = ‖x‖ := by
  have h := congrArg Complex.re (matrix_orthonormal_columns_inner hU x x)
  change RCLike.re (inner ℂ (U.toEuclideanLin x) (U.toEuclideanLin x)) = RCLike.re (inner ℂ x x) at h
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (U.toEuclideanLin x), norm_nonneg x]

end SchauderTranslates
