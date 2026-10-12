import Lean_Code.SchauderTranslates.HilbertSynthesis

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct MatrixOrder ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Primal and dual coordinate vectors for a positive coefficient metric. -/
def metricColumn (B : Matrix ι ι 𝕜) (i : ι) : EuclideanSpace 𝕜 ι :=
  gramRoot B (EuclideanSpace.single i 1)

def metricDual (B : Matrix ι ι 𝕜) (i : ι) : EuclideanSpace 𝕜 ι :=
  gramRootInv B (EuclideanSpace.single i 1)

theorem metricColumn_inner {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) (i j : ι) :
    inner 𝕜 (metricColumn B i) (metricColumn B j) = B i j := by
  unfold metricColumn
  rw [← adjoint_inner_right, gramRoot_adjoint]
  have hs : gramRoot B (gramRoot B (EuclideanSpace.single j 1)) =
      (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) B (EuclideanSpace.single j 1) :=
    congrArg (fun T : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι => T _) (gramRoot_square hB)
  rw [hs, EuclideanSpace.inner_single_left]
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_single]

theorem metricDual_eq_column_inverse {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) (i : ι) :
    metricDual B i = metricColumn B⁻¹ i := by
  unfold metricDual metricColumn
  rw [gramRootInv_eq_root_inverse hB]

theorem metricDual_inner {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) (i j : ι) :
    inner 𝕜 (metricDual B i) (metricDual B j) = B⁻¹ i j := by
  rw [metricDual_eq_column_inverse hB, metricDual_eq_column_inverse hB]
  exact metricColumn_inner hB.inv i j

theorem metricDual_inner_column {B : Matrix ι ι 𝕜} (hB : B.PosDef) (i j : ι) :
    inner 𝕜 (metricDual B i) (metricColumn B j) = if i = j then 1 else 0 := by
  unfold metricDual metricColumn
  rw [← adjoint_inner_right, gramRootInv_adjoint hB.posSemidef]
  have hs : gramRootInv B (gramRoot B (EuclideanSpace.single j 1)) = EuclideanSpace.single j 1 :=
    congrArg (fun T : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 ι => T _) (gramRoot_inv_mul hB)
  rw [hs, EuclideanSpace.inner_single_left]
  simp

omit [Fintype κ] [DecidableEq κ] in
theorem metricColumn_gram {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) (e : κ → ι) :
    Matrix.gram 𝕜 (fun i => metricColumn B (e i)) = B.submatrix e e := by
  ext i j
  exact metricColumn_inner hB (e i) (e j)

omit [Fintype κ] [DecidableEq κ] in
theorem metricDual_gram {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) (e : κ → ι) :
    Matrix.gram 𝕜 (fun i => metricDual B (e i)) = B⁻¹.submatrix e e := by
  ext i j
  exact metricDual_inner hB (e i) (e j)

theorem selectionColumns_apply (e : κ → ι) (c : EuclideanSpace 𝕜 κ) :
    matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e) c =
      ∑ i, c i • EuclideanSpace.single (e i) 1 := by
  ext j
  simp [matrixHilbertMap, Matrix.toLpLin_apply, selectionColumns, Matrix.mulVec,
    dotProduct, Matrix.one_apply, Pi.single_apply, mul_comm]

theorem metricColumn_synthesis (B : Matrix ι ι 𝕜) (e : κ → ι) :
    hilbertSynthesis (fun i => metricColumn B (e i)) =
      (gramRoot B).comp (matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e)) := by
  apply ContinuousLinearMap.ext
  intro c
  simp [hilbertSynthesis_apply, selectionColumns_apply, metricColumn, map_sum]

theorem metricDual_synthesis (B : Matrix ι ι 𝕜) (e : κ → ι) :
    hilbertSynthesis (fun i => metricDual B (e i)) =
      (gramRootInv B).comp (matrixHilbertMap (selectionColumns (𝕜 := 𝕜) e)) := by
  apply ContinuousLinearMap.ext
  intro c
  simp [hilbertSynthesis_apply, selectionColumns_apply, metricDual, map_sum]

theorem metric_prefix_sum {B : Matrix ι ι 𝕜} (hB : B.PosSemidef) (e : κ → ι) :
    (∑ i, rankOne 𝕜 (metricColumn B (e i)) (metricDual B (e i))) =
      gramConjugate B (selectionColumns (𝕜 := 𝕜) e *
        (selectionColumns (𝕜 := 𝕜) e).conjTranspose) := by
  rw [← hilbertSynthesis_cross, metricColumn_synthesis, metricDual_synthesis]
  exact gram_selected_factorization hB e

section Real
variable {B : Matrix ι ι ℝ}

theorem metricColumn_norm_sq (hB : B.PosSemidef) (j : ι) :
    ‖metricColumn B j‖ ^ 2 = B j j := by
  rw [← real_inner_self_eq_norm_sq]
  exact metricColumn_inner hB j j

theorem metricDual_norm_sq (hB : B.PosSemidef) (j : ι) :
    ‖metricDual B j‖ ^ 2 = B⁻¹ j j := by
  rw [← real_inner_self_eq_norm_sq]
  exact metricDual_inner hB j j

theorem metricColumn_norm_sq_le_one (hB : B.PosSemidef) (hBI : B ≤ 1) (j : ι) :
    ‖metricColumn B j‖ ^ 2 ≤ 1 := by
  rw [metricColumn_norm_sq hB]
  have hp : (1 - B).PosSemidef := hBI
  have h := hp.diag_nonneg (i := j)
  simpa using h

end Real
end SchauderTranslates
