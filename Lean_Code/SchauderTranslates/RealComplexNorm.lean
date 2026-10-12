import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open ContinuousLinearMap Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def euclideanRe (z : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (z i).re)

def euclideanIm (z : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => (z i).im)

def euclideanComplex (x : EuclideanSpace ℝ ι) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

omit [DecidableEq ι] in
theorem euclidean_complex_norm_sq (z : EuclideanSpace ℂ ι) :
    ‖z‖ ^ 2 = ‖euclideanRe z‖ ^ 2 + ‖euclideanIm z‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, euclideanRe, euclideanIm,
    Real.norm_eq_abs, sq_abs]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [Complex.normSq_apply, pow_two] using Complex.sq_norm (z i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem euclideanRe_complex (x : EuclideanSpace ℝ ι) :
    euclideanRe (euclideanComplex x) = x := by
  ext i
  simp [euclideanRe, euclideanComplex]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem euclideanIm_complex (x : EuclideanSpace ℝ ι) :
    euclideanIm (euclideanComplex x) = 0 := by
  ext i
  simp [euclideanIm, euclideanComplex]

omit [DecidableEq ι] in
@[simp] theorem euclideanComplex_norm (x : EuclideanSpace ℝ ι) :
    ‖euclideanComplex x‖ = ‖x‖ := by
  have h := euclidean_complex_norm_sq (euclideanComplex x)
  simp only [euclideanRe_complex, euclideanIm_complex, norm_zero, zero_pow (by decide : 2 ≠ 0),
    add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

omit [DecidableEq ι] in
theorem matrixHilbertMap_complex_re (A : Matrix ι κ ℝ) (z : EuclideanSpace ℂ κ) :
    euclideanRe (matrixHilbertMap (A.map Complex.ofReal) z) =
      matrixHilbertMap A (euclideanRe z) := by
  ext i
  change (∑ j, (A i j : ℂ) * z j).re = ∑ j, A i j * (z j).re
  simp

omit [DecidableEq ι] in
theorem matrixHilbertMap_complex_im (A : Matrix ι κ ℝ) (z : EuclideanSpace ℂ κ) :
    euclideanIm (matrixHilbertMap (A.map Complex.ofReal) z) =
      matrixHilbertMap A (euclideanIm z) := by
  ext i
  change (∑ j, (A i j : ℂ) * z j).im = ∑ j, A i j * (z j).im
  simp

omit [DecidableEq ι] in
/-- Passing a real matrix to complex Euclidean spaces preserves its operator norm. -/
theorem real_complex_matrix_norm (A : Matrix ι κ ℝ) :
    ‖matrixHilbertMap (A.map Complex.ofReal)‖ = ‖matrixHilbertMap A‖ := by
  have hup : ‖matrixHilbertMap (A.map Complex.ofReal)‖ ^ 2 ≤ ‖matrixHilbertMap A‖ ^ 2 := by
    apply opNorm_sq_le_of_pointwise _ (sq_nonneg _)
    intro z
    rw [euclidean_complex_norm_sq, matrixHilbertMap_complex_re, matrixHilbertMap_complex_im,
      euclidean_complex_norm_sq z]
    have hr := (matrixHilbertMap A).le_opNorm (euclideanRe z)
    have hi := (matrixHilbertMap A).le_opNorm (euclideanIm z)
    have hr2 := pow_le_pow_left₀ (norm_nonneg (matrixHilbertMap A (euclideanRe z))) hr 2
    have hi2 := pow_le_pow_left₀ (norm_nonneg (matrixHilbertMap A (euclideanIm z))) hi 2
    nlinarith
  have hlow : ‖matrixHilbertMap A‖ ≤ ‖matrixHilbertMap (A.map Complex.ofReal)‖ := by
    apply opNorm_le_bound _ (norm_nonneg (matrixHilbertMap (A.map Complex.ofReal)))
    intro x
    have h := (matrixHilbertMap (A.map Complex.ofReal)).le_opNorm (euclideanComplex x)
    have hn : ‖matrixHilbertMap (A.map Complex.ofReal) (euclideanComplex x)‖ =
        ‖matrixHilbertMap A x‖ := by
      have hs := euclidean_complex_norm_sq
        (matrixHilbertMap (A.map Complex.ofReal) (euclideanComplex x))
      rw [matrixHilbertMap_complex_re, matrixHilbertMap_complex_im] at hs
      simp only [euclideanRe_complex, euclideanIm_complex, map_zero, norm_zero,
        zero_pow (by decide : 2 ≠ 0), add_zero] at hs
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
    simpa only [hn, euclideanComplex_norm] using h
  nlinarith [norm_nonneg (matrixHilbertMap A), norm_nonneg (matrixHilbertMap (A.map Complex.ofReal))]

end SchauderTranslates
