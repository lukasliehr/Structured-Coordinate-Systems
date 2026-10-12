import Lean_Code.SchauderTranslates.SchurSmoothing
import Lean_Code.SchauderTranslates.FiniteGram

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive matrix padded by a zero block is still positive. -/
theorem posSemidef_zero_padding {κ : Type*} [Fintype κ]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (Matrix.fromBlocks A (0 : Matrix ι κ ℂ) 0 0).PosSemidef := by
  have h := hA.conjTranspose_mul_mul_same (Matrix.fromCols (1 : Matrix ι ι ℂ) (0 : Matrix ι κ ℂ))
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols] at h
  simpa only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, one_mul, zero_mul,
    mul_one, mul_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul] using h

/-- The corresponding padding in the second diagonal block. -/
theorem posSemidef_zero_padding_right {κ : Type*} [Fintype κ]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (Matrix.fromBlocks (0 : Matrix κ κ ℂ) 0 0 A).PosSemidef := by
  have h := (posSemidef_zero_padding (κ := κ) hA).submatrix (Equiv.sumComm κ ι)
  convert h using 1
  ext (i | i) (j | j) <;> rfl

/-- Matrix inversion reverses positive definite order, proved through the inverse block certificate. -/
theorem matrix_inverse_antitone {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (B - A).PosSemidef) : (A⁻¹ - B⁻¹).PosSemidef := by
  have h := (inverse_block_posSemidef hA).add (posSemidef_zero_padding hAB)
  have he : Matrix.fromBlocks A 1 1 A⁻¹ + Matrix.fromBlocks (B - A) 0 0 0 =
      Matrix.fromBlocks B (1 : Matrix ι ι ℂ) 1 A⁻¹ := by
    ext (i | i) (j | j) <;> simp [Matrix.add_apply, Matrix.sub_apply]
  rw [he] at h
  let : Invertible B := hB.isUnit.invertible
  have hs := Matrix.PosDef.fromBlocks₁₁ (1 : Matrix ι ι ℂ) A⁻¹ hB
  simp only [Matrix.conjTranspose_one, one_mul, mul_one] at hs
  exact hs.mp h

/-- Inverse quadratic forms inherit the reversed matrix order. -/
theorem gramCapture_antitone {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : (B - A).PosSemidef) (v : ι → ℂ) : gramCapture B v ≤ gramCapture A v := by
  have h := (matrix_inverse_antitone hA hB hAB).re_dotProduct_nonneg v
  change 0 ≤ (star v ⬝ᵥ (A⁻¹ - B⁻¹) *ᵥ v).re at h
  simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg, gramCapture] using h

theorem gramCapture_nonneg {A : Matrix ι ι ℂ} (hA : A.PosDef) (v : ι → ℂ) :
    0 ≤ gramCapture A v := hA.inv.posSemidef.re_dotProduct_nonneg v

/-- Positive real rescaling has the reciprocal effect on a capture quadratic form. -/
theorem gramCapture_real_smul {A : Matrix ι ι ℂ} (hA : A.PosDef) {r : ℝ} (hr : 0 < r)
    (v : ι → ℂ) : gramCapture (r • A) v = r⁻¹ * gramCapture A v := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let : Invertible (r : ℂ) := (isUnit_iff_ne_zero.mpr hrC).invertible
  have he : r • A = (r : ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [gramCapture, he, Matrix.inv_smul A (r : ℂ) ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit)]
  simp only [invOf_eq_inv, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

theorem gramCapture_one (v : ι → ℂ) :
    gramCapture (1 : Matrix ι ι ℂ) v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ ^ 2 := by
  simp only [gramCapture, inv_one, Matrix.one_mulVec]
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (WithLp.toLp 2 v : EuclideanSpace ℂ ι)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa only [WithLp.ofLp_toLp, dotProduct_comm] using! h

end SchauderTranslates
