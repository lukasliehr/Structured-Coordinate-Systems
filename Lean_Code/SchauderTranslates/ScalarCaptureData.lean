import Lean_Code.SchauderTranslates.ScalarReality
import Lean_Code.SchauderTranslates.MatrixInverseOrder

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ScalarData
variable {d n : ℕ}

theorem nonconstantGram_posDef (s : ScalarData d n) : s.nonconstantGram.PosDef :=
  s.rawGram_posDef.submatrix Sum.inr_injective

theorem nonconstantGram_le_one (s : ScalarData d n) : (1 - s.nonconstantGram).PosSemidef := by
  have h := (Matrix.le_iff.mp s.rawGram_le_one).submatrix (Sum.inr : Fin n → Unit ⊕ Fin n)
  convert! h using 1
  ext i j
  simp [nonconstantGram, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply]

theorem nonconstantGram_floor (s : ScalarData d n) {σ : ℝ}
    (hf : (s.rawGram - (σ : ℂ) • 1).PosSemidef) :
    (s.nonconstantGram - σ • 1).PosSemidef := by
  have h := hf.submatrix (Sum.inr : Fin n → Unit ⊕ Fin n)
  convert! h using 1
  ext i j
  simp [nonconstantGram, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Complex.real_smul]

/-- The moment-column energy is bounded by the mass deficit. This is the finite Haar
Bessel bound, obtained from the already checked positive contraction Gram. -/
theorem moment_norm_sq_le_deficit (s : ScalarData d n) :
    ‖(WithLp.toLp 2 s.moment : EuclideanSpace ℂ (Fin n))‖ ^ 2 ≤ 1 - s.mass := by
  have hp := (Matrix.le_iff.mp s.rawGram_le_one).add
    (posSemidef_zero_padding_right (κ := Unit) s.nonconstantGram_posDef.posSemidef)
  have he : 1 - s.rawGram + Matrix.fromBlocks (0 : Matrix Unit Unit ℂ) 0 0 s.nonconstantGram =
      Matrix.fromBlocks (massBlock (1 - s.mass)) (-momentRow s.moment) (-momentColumn s.moment) 1 := by
    rw [s.rawGram_fromBlocks]
    ext (i | i) (j | j)
    · cases i; cases j
      simp [massBlock, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply]
    · simp [momentRow, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply]
    · simp [momentColumn, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply]
    · simp [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply]
  rw [he] at hp
  have hstar : (-momentRow s.moment).conjTranspose = -momentColumn s.moment := by
    ext i j
    simp [momentRow, momentColumn, Matrix.conjTranspose_apply, Complex.star_def]
  let : Invertible (1 : Matrix (Fin n) (Fin n) ℂ) :=
    (Matrix.PosDef.one (n := Fin n) (R := ℂ)).isUnit.invertible
  have hs := Matrix.PosDef.fromBlocks₂₂ (massBlock (1 - s.mass)) (-momentRow s.moment)
    (Matrix.PosDef.one (n := Fin n) (R := ℂ))
  rw [hstar] at hs
  have hq := (hs.mp hp).diag_nonneg (i := ())
  have hr := (RCLike.nonneg_iff.mp hq).1
  change 0 ≤ ((massBlock (1 - s.mass) - (-momentRow s.moment) *
    (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (-momentColumn s.moment)) () ()).re at hr
  simp only [inv_one, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.sub_apply, massBlock, Matrix.mul_apply,
    momentRow, momentColumn, Complex.sub_re, Complex.ofReal_re] at hr
  rw [← gramCapture_one s.moment]
  simpa only [gramCapture, inv_one, Matrix.one_mulVec, dotProduct, Pi.star_apply, sub_nonneg] using hr

end ScalarData
end SchauderTranslates
