import Lean_Code.SchauderTranslates.RealComplexNorm

noncomputable section
open ContinuousLinearMap Matrix
open scoped InnerProductSpace InnerProduct ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real coefficient matrix splits its complex quadratic energy into real and imaginary parts. -/
theorem coefficientQuadratic_complex_parts (B : Matrix ι ι ℝ) (z : EuclideanSpace ℂ ι) :
    coefficientQuadratic (B.map Complex.ofReal) z =
      coefficientQuadratic B (euclideanRe z) + coefficientQuadratic B (euclideanIm z) := by
  simp only [coefficientQuadratic_eq_dot, dotProduct, Matrix.mulVec, Matrix.map_apply,
    Pi.star_apply, Finset.mul_sum]
  simp only [map_sum, RCLike.re_to_real, star_trivial, euclideanRe, euclideanIm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change ((starRingEnd ℂ) (z i) * ((B i j : ℂ) * z j)).re = _
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem matrixEuclidean_complex_re (D : Matrix ι ι ℝ) (z : EuclideanSpace ℂ ι) :
    euclideanRe ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (D.map Complex.ofReal) z) =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) D (euclideanRe z) := by
  simpa only [matrixHilbertMap_square] using matrixHilbertMap_complex_re D z

theorem matrixEuclidean_complex_im (D : Matrix ι ι ℝ) (z : EuclideanSpace ℂ ι) :
    euclideanIm ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (D.map Complex.ofReal) z) =
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) D (euclideanIm z) := by
  simpa only [matrixHilbertMap_square] using matrixHilbertMap_complex_im D z

/-- A real coefficient inequality extends to all complex coefficients with the identical constant. -/
theorem coefficientQuadratic_bound_complex (B D : Matrix ι ι ℝ) (C : ℝ)
    (h : ∀ x : EuclideanSpace ℝ ι,
      coefficientQuadratic B ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) D x) ≤
        C * coefficientQuadratic B x) (z : EuclideanSpace ℂ ι) :
    coefficientQuadratic (B.map Complex.ofReal)
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (D.map Complex.ofReal) z) ≤
      C * coefficientQuadratic (B.map Complex.ofReal) z := by
  rw [coefficientQuadratic_complex_parts, matrixEuclidean_complex_re, matrixEuclidean_complex_im,
    coefficientQuadratic_complex_parts, mul_add]
  exact add_le_add (h _) (h _)

/-- Restriction to real coefficients recovers any bound for a real complex matrix. -/
theorem coefficientQuadratic_bound_real (B D : Matrix ι ι ℝ) (C : ℝ)
    (h : ∀ z : EuclideanSpace ℂ ι,
      coefficientQuadratic (B.map Complex.ofReal)
        ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (D.map Complex.ofReal) z) ≤
        C * coefficientQuadratic (B.map Complex.ofReal) z) (x : EuclideanSpace ℝ ι) :
    coefficientQuadratic B ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) D x) ≤
      C * coefficientQuadratic B x := by
  have hx := h (euclideanComplex x)
  rw [coefficientQuadratic_complex_parts, matrixEuclidean_complex_re, matrixEuclidean_complex_im,
    coefficientQuadratic_complex_parts, euclideanRe_complex, euclideanIm_complex] at hx
  simpa [coefficientQuadratic] using hx

theorem gramConjugate_quadratic_bound_iff {𝕜 : Type*} [RCLike 𝕜]
    {B : Matrix ι ι 𝕜} (hB : B.PosDef) (D : Matrix ι ι 𝕜) {C : ℝ} (hC : 0 ≤ C) :
    ‖gramConjugate B D‖ ^ 2 ≤ C ↔ ∀ x : EuclideanSpace 𝕜 ι,
      coefficientQuadratic B ((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) D x) ≤
        C * coefficientQuadratic B x := by
  rw [gramConjugate_bound_iff hB D hC]
  simp only [gramRoot_norm_sq hB.posSemidef, coefficientQuadratic]

/-- The original real and complex Hilbert prefix norms agree for a real positive Gram. -/
theorem gramConjugate_real_complex_norm {B : Matrix ι ι ℝ} (hB : B.PosDef)
    (hBC : (B.map Complex.ofReal).PosDef) (D : Matrix ι ι ℝ) :
    ‖gramConjugate (B.map Complex.ofReal) (D.map Complex.ofReal)‖ = ‖gramConjugate B D‖ := by
  have hupper : ‖gramConjugate (B.map Complex.ofReal) (D.map Complex.ofReal)‖ ^ 2 ≤
      ‖gramConjugate B D‖ ^ 2 := by
    apply (gramConjugate_quadratic_bound_iff hBC _ (sq_nonneg _)).mpr
    exact coefficientQuadratic_bound_complex B D _
      ((gramConjugate_quadratic_bound_iff hB D (sq_nonneg _)).mp le_rfl)
  have hlower : ‖gramConjugate B D‖ ^ 2 ≤
      ‖gramConjugate (B.map Complex.ofReal) (D.map Complex.ofReal)‖ ^ 2 := by
    apply (gramConjugate_quadratic_bound_iff hB D (sq_nonneg _)).mpr
    exact coefficientQuadratic_bound_real B D _
      ((gramConjugate_quadratic_bound_iff hBC _ (sq_nonneg _)).mp le_rfl)
  nlinarith [norm_nonneg (gramConjugate B D),
    norm_nonneg (gramConjugate (B.map Complex.ofReal) (D.map Complex.ofReal))]

end SchauderTranslates
