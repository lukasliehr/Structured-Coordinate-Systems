import Lean_Code.SchauderTranslates.TensorCaptureBasics

noncomputable section
open Matrix
open scoped ComplexOrder Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Restricting the row factor to an eigenspace gives exactly the soft scalar Gram. -/
theorem tensorGram_eigen (G : Matrix ι ι ℂ) {B : Matrix κ κ ℂ} {β : ℝ}
    {x : κ → ℂ} (hx : B *ᵥ x = (β : ℂ) • x) (y : ι → ℂ) :
    tensorGram G B *ᵥ tensorVector y x = tensorVector (softGram G β *ᵥ y) x := by
  rw [tensorGram, Matrix.add_mulVec, kronecker_mulVec_tensor, kronecker_mulVec_tensor,
    Matrix.one_mulVec, hx]
  funext p
  simp only [tensorVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.sub_mulVec,
    Matrix.one_mulVec, Pi.sub_apply, softGram, Matrix.add_mulVec, Matrix.smul_mulVec,
    Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The inverse action is derived from two actual positive definite matrices. -/
theorem tensorGram_inverse_eigen {G : Matrix ι ι ℂ} {B : Matrix κ κ ℂ}
    (hG : G.PosDef) (hA : (tensorGram G B).PosDef) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    {x : κ → ℂ} (hx : B *ᵥ x = (β : ℂ) • x) (y : ι → ℂ) :
    (tensorGram G B)⁻¹ *ᵥ tensorVector y x = tensorVector ((softGram G β)⁻¹ *ᵥ y) x := by
  have hH := softGram_posDef hG hβ0 hβ1
  have hdetH := (Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit
  have hdetA := (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit
  have ha := tensorGram_eigen G hx ((softGram G β)⁻¹ *ᵥ y)
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetH, Matrix.one_mulVec] at ha
  calc
    _ = (tensorGram G B)⁻¹ *ᵥ (tensorGram G B *ᵥ tensorVector ((softGram G β)⁻¹ *ᵥ y) x) := by rw [ha]
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdetA, Matrix.one_mulVec]

theorem tensorSource_eigen (b : ι → ℂ) {B : Matrix κ κ ℂ} {β : ℝ}
    {x : κ → ℂ} (hx : B *ᵥ x = (β : ℂ) • x) :
    tensorSource b B *ᵥ x = (1 - (β : ℂ)) • tensorVector b x := by
  rw [tensorSource_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hx]
  funext p
  simp only [tensorVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tensorSource_adjoint_eigen (b y : ι → ℂ) {B : Matrix κ κ ℂ} (hB : B.IsHermitian)
    {β : ℝ} {x : κ → ℂ} (hx : B *ᵥ x = (β : ℂ) • x) :
    (tensorSource b B)ᴴ *ᵥ tensorVector y x =
      ((star b ⬝ᵥ y) * (1 - (β : ℂ))) • x := by
  rw [tensorSource_adjoint_tensor b y hB, Matrix.sub_mulVec, Matrix.one_mulVec, hx]
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem gramCapture_complex {G : Matrix ι ι ℂ} (hG : G.PosDef) (b : ι → ℂ) :
    star b ⬝ᵥ G⁻¹ *ᵥ b = (gramCapture G b : ℂ) := by
  apply Complex.ext
  · rfl
  · exact hG.inv.isHermitian.im_star_dotProduct_mulVec_self b

/-- Spectral evaluation of the entire raw source sandwich, without assuming an
orthogonal diagonalization as an additional input. -/
theorem tensorCapture_eigen {G : Matrix ι ι ℂ} (hG : G.PosDef) (b : ι → ℂ)
    {B : Matrix κ κ ℂ} (hB : B.PosDef) (hB1 : (1 - B).PosSemidef)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {x : κ → ℂ}
    (hx : B *ᵥ x = (β : ℂ) • x) :
    tensorCapture G b B *ᵥ x = (softCapture G b β : ℂ) • x := by
  have hA := tensorGram_posDef hG hB hB1
  rw [tensorCapture, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    tensorSource_eigen b hx, Matrix.mulVec_smul,
    tensorGram_inverse_eigen hG hA hβ0 hβ1 hx, Matrix.mulVec_smul,
    tensorSource_adjoint_eigen b _ hB.isHermitian hx,
    gramCapture_complex (softGram_posDef hG hβ0 hβ1), smul_smul]
  congr 1
  simp only [softCapture, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- The spectral interval is a consequence of positivity and contraction whenever
the eigenvector is nonzero. -/
theorem positive_contraction_eigenvalue_bounds {B : Matrix κ κ ℂ}
    (hB : B.PosDef) (hB1 : (1 - B).PosSemidef) {β : ℝ} {x : κ → ℂ}
    (hx : B *ᵥ x = (β : ℂ) • x) (hx0 : x ≠ 0) : 0 < β ∧ β ≤ 1 := by
  have hnorm := (Matrix.PosDef.one (n := κ) (R := ℂ)).re_dotProduct_pos hx0
  simp only [Matrix.one_mulVec] at hnorm
  have hpos := hB.re_dotProduct_pos hx0
  rw [hx, dotProduct_smul] at hpos
  have hupper := hB1.re_dotProduct_nonneg x
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hx, dotProduct_sub, dotProduct_smul] at hupper
  change 0 < (star x ⬝ᵥ x).re at hnorm
  change 0 < ((β : ℂ) * (star x ⬝ᵥ x)).re at hpos
  change 0 ≤ (star x ⬝ᵥ x - (β : ℂ) * (star x ⬝ᵥ x)).re at hupper
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.sub_re] at hpos hupper
  constructor <;> nlinarith

/-- The full sandwich evaluation, with the eigenvalue interval discharged internally. -/
theorem tensorCapture_eigen_of_contraction {G : Matrix ι ι ℂ} (hG : G.PosDef) (b : ι → ℂ)
    {B : Matrix κ κ ℂ} (hB : B.PosDef) (hB1 : (1 - B).PosSemidef)
    {β : ℝ} {x : κ → ℂ} (hx : B *ᵥ x = (β : ℂ) • x) :
    tensorCapture G b B *ᵥ x = (softCapture G b β : ℂ) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hβ := positive_contraction_eigenvalue_bounds hB hB1 hx hx0
    exact tensorCapture_eigen hG b hB hB1 hβ.1.le hβ.2 hx

end SchauderTranslates
