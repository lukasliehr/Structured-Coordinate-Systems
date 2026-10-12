import Lean_Code.SchauderTranslates.BasisOperatorMatrix

noncomputable section
open Matrix
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Relabeling Euclidean coordinates preserves the operator norm, regardless of the order. -/
theorem matrix_reindex_norm (B : Matrix κ κ ℂ) (e : ι ≃ κ) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) (B.submatrix e e)‖ =
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) B‖ := by
  let b := (EuclideanSpace.basisFun κ ℂ).reindex e.symm
  have he : basisOperatorMatrix b ((Matrix.toEuclideanCLM (𝕜 := ℂ)) B) = B.submatrix e e := by
    ext i j
    simp [basisOperatorMatrix, b, OrthonormalBasis.reindex_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_single]
  rw [← he]
  exact basisOperatorMatrix_norm b _

end SchauderTranslates
