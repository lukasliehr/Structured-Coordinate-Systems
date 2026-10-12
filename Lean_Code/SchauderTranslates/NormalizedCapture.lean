import Lean_Code.SchauderTranslates.EuclideanMatrixOperators
import Lean_Code.SchauderTranslates.InformationCentering

noncomputable section
open Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ H E : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Compressing the actual atom-span projection is the inverse Gram sandwich of its
actual source adjoint. This statement does not assume the compression is finite dimensional. -/
theorem compressed_projection_source (u : ι → H) (hu : LinearIndependent ℂ u) (L : E →L[ℂ] H) :
    (L†).comp ((atomSpan u).starProjection.comp L) =
      ((((hilbertSynthesis u)†).comp L)†).comp
        ((euclideanMatrixOperator ((Matrix.gram ℂ u)⁻¹)).comp (((hilbertSynthesis u)†).comp L)) := by
  rw [atomSpan_projection_formula u hu, adjoint_comp, adjoint_adjoint,
    euclideanMatrixOperator_square]
  simp only [comp_assoc]

theorem matrix_inverse_normalized {A : Matrix ι ι ℂ} (hA : A.PosDef) (M : ℝ) (hM : M ≠ 0) :
    ((M : ℂ)⁻¹ • A)⁻¹ = (M : ℂ) • A⁻¹ := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  let : Invertible ((M : ℂ)⁻¹) := (isUnit_iff_ne_zero.mpr (inv_ne_zero hMC)).invertible
  rw [Matrix.inv_smul A _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit), invOf_eq_inv, inv_inv]

/-- Raw source and Gram both acquire `1/M`; the resulting capture acquires exactly
one such factor. Every map is between the actual Hilbert spaces. -/
theorem normalized_capture_sandwich (u : ι → H) (hu : LinearIndependent ℂ u) (L : E →L[ℂ] H)
    (T : EuclideanSpace ℂ κ →L[ℂ] E) (R : Matrix ι κ ℂ) {A : Matrix ι ι ℂ}
    (hA : A.PosDef) (M : ℝ) (hM : 0 < M)
    (hgram : Matrix.gram ℂ u = (M : ℂ)⁻¹ • A)
    (hsource : ((hilbertSynthesis u)†).comp L =
      (M : ℂ)⁻¹ • ((euclideanMatrixOperator R).comp (T†))) :
    (L†).comp ((atomSpan u).starProjection.comp L) =
      (M : ℂ)⁻¹ • T.comp ((euclideanMatrixOperator (Rᴴ * A⁻¹ * R)).comp (T†)) := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [compressed_projection_source u hu L, hsource, hgram, matrix_inverse_normalized hA M hM.ne',
    euclideanMatrixOperator_smul]
  simp only [map_smulₛₗ, adjoint_comp, adjoint_adjoint, map_inv₀, Complex.star_def,
    Complex.conj_ofReal, smul_comp, comp_smul, smul_smul]
  simp only [euclideanMatrixOperator_mul, ← euclideanMatrixOperator_adjoint,
    comp_assoc, inv_mul_cancel₀ hMC, one_mul]

end SchauderTranslates
