import Lean_Code.SchauderTranslates.HilbertSynthesis

noncomputable section
open Matrix ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Matrix entries of an operator in an actual orthonormal basis. -/
def basisOperatorMatrix (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H) : Matrix ι ι ℂ :=
  fun i j => inner ℂ (b i) (T (b j))

/-- Matrix coordinates agree with conjugation by the orthonormal coordinate isometry. -/
theorem basisOperatorMatrix_apply (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H)
    (c : EuclideanSpace ℂ ι) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (basisOperatorMatrix b T) c =
      b.repr (T (b.repr.symm c)) := by
  rw [← b.sum_repr_symm c]
  ext i
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, basisOperatorMatrix,
    map_sum, map_smul, b.repr_apply_apply, mul_comm]

theorem basisOperatorMatrix_comp (b : OrthonormalBasis ι ℂ H) (T S : H →L[ℂ] H) :
    basisOperatorMatrix b (T.comp S) = basisOperatorMatrix b T * basisOperatorMatrix b S := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).injective
  rw [map_mul]
  ext1 c
  change (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (basisOperatorMatrix b (T.comp S)) c =
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (basisOperatorMatrix b T)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (basisOperatorMatrix b S) c)
  simp only [basisOperatorMatrix_apply, LinearIsometryEquiv.symm_apply_apply, ContinuousLinearMap.comp_apply]

@[simp] theorem basisOperatorMatrix_one (b : OrthonormalBasis ι ℂ H) :
    basisOperatorMatrix b 1 = 1 := by
  ext i j
  exact orthonormal_iff_ite.mp b.orthonormal i j

/-- No matrix invertibility assumption is introduced: the inverse comes from the operator inverse. -/
theorem basisOperatorMatrix_inverse (b : OrthonormalBasis ι ℂ H) (T C : H →L[ℂ] H)
    (hTC : T.comp C = 1) : (basisOperatorMatrix b T)⁻¹ = basisOperatorMatrix b C := by
  apply Matrix.inv_eq_right_inv
  rw [← basisOperatorMatrix_comp, hTC, basisOperatorMatrix_one]

/-- These matrix norms are Euclidean operator norms, exactly equal to the original Hilbert norm. -/
theorem basisOperatorMatrix_norm (b : OrthonormalBasis ι ℂ H) (T : H →L[ℂ] H) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (basisOperatorMatrix b T)‖ = ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro c
    rw [basisOperatorMatrix_apply, b.repr.norm_map]
    simpa only [b.repr.symm.norm_map] using T.le_opNorm (b.repr.symm c)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (basisOperatorMatrix b T)).le_opNorm (b.repr x)
    simpa only [basisOperatorMatrix_apply, b.repr.symm_apply_apply, b.repr.norm_map] using h

end SchauderTranslates
