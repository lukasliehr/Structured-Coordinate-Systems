import Lean_Code.SchauderTranslates.SplitRowMetric

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The orthogonal projection onto a specified family of coordinate axes. -/
def coordinateSelection (e : κ → ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  ∑ i, rankOne ℝ (EuclideanSpace.single (e i) 1) (EuclideanSpace.single (e i) 1)

omit [DecidableEq κ] in
theorem coordinateSelection_apply (e : κ → ι) (z : EuclideanSpace ℝ ι) :
    coordinateSelection e z = ∑ i, z (e i) • EuclideanSpace.single (e i) 1 := by
  simp [coordinateSelection, sum_apply, rankOne_apply, EuclideanSpace.inner_single_left]

theorem coordinateSelection_matrix (e : κ → ι) :
    coordinateSelection e = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι))
      (selectionColumns (𝕜 := ℝ) e * (selectionColumns (𝕜 := ℝ) e).conjTranspose) := by
  have hs : hilbertSynthesis (𝕜 := ℝ) (fun i => EuclideanSpace.single (e i) (1 : ℝ)) =
      matrixHilbertMap (selectionColumns (𝕜 := ℝ) e) := by
    ext c
    simp [hilbertSynthesis_apply, selectionColumns_apply]
  unfold coordinateSelection
  rw [← hilbertSynthesis_cross, hs, ← matrixHilbertMap_adjoint, ← matrixHilbertMap_mul,
    matrixHilbertMap_square]

theorem coordinateSelection_idempotent (e : κ → ι) (he : Function.Injective e) :
    ∀ z, coordinateSelection e (coordinateSelection e z) = coordinateSelection e z := by
  unfold coordinateSelection
  apply biorthogonal_rankOne_idempotent
  intro i j
  simp [EuclideanSpace.inner_single_left, he.eq_iff]

theorem coordinateSelection_symmetric (e : κ → ι) (z w : EuclideanSpace ℝ ι) :
    inner ℝ (coordinateSelection e z) w = inner ℝ z (coordinateSelection e w) := by
  simp only [coordinateSelection_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp [mul_comm]

theorem coordinateSelection_norm_le_one (e : κ → ι) (he : Function.Injective e) :
    ‖coordinateSelection e‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro z
  have h := real_inner_le_norm (coordinateSelection e z) z
  have hn : inner ℝ (coordinateSelection e z) z = ‖coordinateSelection e z‖ ^ 2 := by
    rw [← coordinateSelection_idempotent e he z, coordinateSelection_symmetric]
    rw [coordinateSelection_idempotent e he, real_inner_self_eq_norm_sq]
  rw [hn] at h
  have : ‖coordinateSelection e z‖ ≤ ‖z‖ := by nlinarith [norm_nonneg (coordinateSelection e z), norm_nonneg z]
  simpa using this

theorem coordinateSelection_single_zero (e : κ → ι) (j : ι) (hj : ∀ i, e i ≠ j) :
    coordinateSelection e (EuclideanSpace.single j 1) = 0 := by
  simp [coordinateSelection_apply, hj]

theorem coordinateSelection_inner_zero (e : κ → ι) (j : ι) (hj : ∀ i, e i ≠ j)
    (z : EuclideanSpace ℝ ι) :
    inner ℝ (EuclideanSpace.single j 1) (coordinateSelection e z) = 0 := by
  rw [← coordinateSelection_symmetric, coordinateSelection_single_zero e j hj, inner_zero_left]

/-- The positive square root intertwines the coordinate and metric projections. -/
theorem metricPrefix_root_apply {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (e : κ → ι) (z : EuclideanSpace ℝ ι) :
    metricPrefix B e (gramRoot B z) = gramRoot B (coordinateSelection e z) := by
  have hi : gramRootInv B (gramRoot B z) = z :=
    congrArg (fun T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι => T z) (gramRoot_inv_mul hB)
  simp only [metricPrefix, gramConjugate, ContinuousLinearMap.comp_apply, hi,
    coordinateSelection_matrix]

/-- The dual column reads the original coefficient after applying the square root. -/
theorem metricDual_inner_root {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (j : ι) (z : EuclideanSpace ℝ ι) :
    inner ℝ (metricDual B j) (gramRoot B z) = z j := by
  unfold metricDual
  rw [← adjoint_inner_right, gramRootInv_adjoint hB.posSemidef]
  have hi : gramRootInv B (gramRoot B z) = z :=
    congrArg (fun T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι => T z) (gramRoot_inv_mul hB)
  rw [hi, EuclideanSpace.inner_single_left]
  simp

end SchauderTranslates
