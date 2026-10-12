import Lean_Code.SchauderTranslates.RepeatedQuadratic
import Lean_Code.SchauderTranslates.ScaledGramBound

noncomputable section
open Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An inverse Hilbert operator norm bound gives the corresponding quadratic spectral floor. -/
theorem inverse_norm_quadratic_floor {B : Matrix ι ι ℂ} (hB : B.PosDef) {ε : ℝ}
    (hε : 0 < ε) (hn : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) B⁻¹‖ ≤ ε⁻¹ ^ 2)
    (x : EuclideanSpace ℂ ι) : ε ^ 2 * ‖x‖ ^ 2 ≤ coefficientQuadratic B x := by
  have hi : gramRootInv B (gramRoot B x) = x :=
    congrArg (fun T : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι => T x) (gramRoot_inv_mul hB)
  have he : coefficientQuadratic B⁻¹ (gramRoot B x) = ‖x‖ ^ 2 := by
    have he := gramRoot_norm_sq hB.inv.posSemidef (gramRoot B x)
    rw [← gramRootInv_eq_root_inverse hB.posSemidef, hi] at he
    exact he.symm
  have hh := (coefficientQuadratic_le_opNorm B⁻¹ (gramRoot B x)).trans
    (mul_le_mul_of_nonneg_right hn (sq_nonneg ‖gramRoot B x‖))
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
  have hcancel : ε ^ 2 * (ε⁻¹ ^ 2 * ‖gramRoot B x‖ ^ 2) = ‖gramRoot B x‖ ^ 2 := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hε.ne', one_pow, one_mul]
  rw [hcancel, gramRoot_norm_sq hB.posSemidef] at hm
  exact hm

/-- The same floor as an explicit positive-semidefinite matrix difference. -/
theorem inverse_norm_matrix_floor {B : Matrix ι ι ℂ} (hB : B.PosDef) {ε : ℝ}
    (hε : 0 < ε) (hn : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) B⁻¹‖ ≤ ε⁻¹ ^ 2) :
    (B - ((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef := by
  have hI : (((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast sq_nonneg ε)
  apply (matrix_posSemidef_iff_quadratic (hB.isHermitian.sub hI.isHermitian)).mpr
  intro x
  have hh := inverse_norm_quadratic_floor hB hε hn x
  change 0 ≤ RCLike.re (inner ℂ x ((Matrix.toEuclideanCLM (𝕜 := ℂ))
    (B - ((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) x))
  rw [map_sub, _root_.sub_apply, inner_sub_right, map_sub]
  change 0 ≤ coefficientQuadratic B x -
    coefficientQuadratic (((ε ^ 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)) x
  rw [coefficientQuadratic_ofReal_smul]
  have hOne : coefficientQuadratic (1 : Matrix ι ι ℂ) x = ‖x‖ ^ 2 := by
    unfold coefficientQuadratic
    rw [map_one]
    change RCLike.re (inner ℂ x x) = ‖x‖ ^ 2
    exact inner_self_eq_norm_sq x
  rw [hOne]
  linarith

end SchauderTranslates
