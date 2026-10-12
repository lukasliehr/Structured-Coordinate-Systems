import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem coefficientQuadratic_mono {A B : Matrix κ κ ℂ} (h : (B - A).PosSemidef)
    (x : EuclideanSpace ℂ κ) : coefficientQuadratic A x ≤ coefficientQuadratic B x := by
  have hh := h.re_dotProduct_nonneg x.ofLp
  change 0 ≤ (star x.ofLp ⬝ᵥ (B - A) *ᵥ x.ofLp).re at hh
  simp only [coefficientQuadratic_eq_dot]
  change (star x.ofLp ⬝ᵥ A *ᵥ x.ofLp).re ≤ (star x.ofLp ⬝ᵥ B *ᵥ x.ofLp).re
  simpa only [Matrix.sub_mulVec, dotProduct_sub,
    Complex.sub_re, sub_nonneg] using hh

theorem coefficientQuadratic_real_scale (A : Matrix κ κ ℂ) (C : ℝ) (x : EuclideanSpace ℂ κ) :
    coefficientQuadratic ((C : ℂ) • A) x = C * coefficientQuadratic A x := by
  simp only [coefficientQuadratic_eq_dot, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  change ((C : ℂ) * (star x.ofLp ⬝ᵥ A *ᵥ x.ofLp)).re = C * (star x.ofLp ⬝ᵥ A *ᵥ x.ofLp).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem selected_root_norm_sq {H : Matrix ι ι ℂ} (hH : H.PosSemidef)
    (e : κ → ι) (x : EuclideanSpace ℂ κ) :
    ‖gramRoot H (matrixHilbertMap (selectionColumns (𝕜 := ℂ) e) x)‖ ^ 2 =
      coefficientQuadratic (H.submatrix e e) x := by
  let X := (gramRoot H).comp (matrixHilbertMap (selectionColumns (𝕜 := ℂ) e))
  have hh := gram_selected_columns hH e
  have hi : inner ℂ x ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := κ)) (H.submatrix e e) x) =
      inner ℂ (X x) (X x) := by
    rw [← hh, ContinuousLinearMap.comp_apply, adjoint_inner_right]
  rw [coefficientQuadratic, hi, inner_self_eq_norm_sq]
  rfl

/-- Synthesis from a selected column is a contraction in its reference metric. -/
theorem selected_primal_contraction {H : Matrix ι ι ℂ} {Ω : Matrix κ κ ℂ}
    (hH : H.PosSemidef) (hΩ : Ω.PosDef) (e : κ → ι)
    (hcol : (Ω - H.submatrix e e).PosSemidef) :
    ‖(gramRoot H).comp ((matrixHilbertMap (selectionColumns (𝕜 := ℂ) e)).comp (gramRootInv Ω))‖ ≤ 1 := by
  let X := (gramRoot H).comp ((matrixHilbertMap (selectionColumns (𝕜 := ℂ) e)).comp (gramRootInv Ω))
  have hn : ‖X‖ ^ 2 ≤ 1 := by
    apply opNorm_sq_le_of_pointwise _ zero_le_one
    intro x
    have hx : gramRoot Ω (gramRootInv Ω x) = x := by
      rw [← ContinuousLinearMap.comp_apply, gramRoot_mul_inv hΩ, one_apply_eq_self]
    change ‖gramRoot H (matrixHilbertMap (selectionColumns (𝕜 := ℂ) e) (gramRootInv Ω x))‖ ^ 2 ≤ _
    rw [selected_root_norm_sq hH]
    calc
      _ ≤ coefficientQuadratic Ω (gramRootInv Ω x) := coefficientQuadratic_mono hcol _
      _ = ‖gramRoot Ω (gramRootInv Ω x)‖ ^ 2 := (gramRoot_norm_sq hΩ.posSemidef _).symm
      _ = 1 * ‖x‖ ^ 2 := by rw [hx, one_mul]
  dsimp only [X] at hn
  nlinarith [norm_nonneg X]

/-- Extraction into a selected column has the square-root inverse-metric bound. -/
theorem selected_dual_bound {H : Matrix ι ι ℂ} {Ω : Matrix κ κ ℂ}
    (hH : H.PosSemidef) (hΩ : Ω.PosDef) (e : κ → ι) {C : ℝ} (hC : 0 ≤ C)
    (hcol : ((C : ℂ) • Ω⁻¹ - H⁻¹.submatrix e e).PosSemidef) :
    ‖(gramRootInv H).comp ((matrixHilbertMap (selectionColumns (𝕜 := ℂ) e)).comp (gramRoot Ω))‖ ≤ Real.sqrt C := by
  let Y := (gramRootInv H).comp ((matrixHilbertMap (selectionColumns (𝕜 := ℂ) e)).comp (gramRoot Ω))
  have hn : ‖Y‖ ^ 2 ≤ C := by
    apply opNorm_sq_le_of_pointwise _ hC
    intro x
    have hx : gramRoot Ω⁻¹ (gramRoot Ω x) = x := by
      rw [← gramRootInv_eq_root_inverse hΩ.posSemidef, ← ContinuousLinearMap.comp_apply, gramRoot_inv_mul hΩ, one_apply_eq_self]
    change ‖gramRootInv H (matrixHilbertMap (selectionColumns (𝕜 := ℂ) e) (gramRoot Ω x))‖ ^ 2 ≤ _
    rw [gramRootInv_eq_root_inverse hH, selected_root_norm_sq hH.inv]
    calc
      _ ≤ coefficientQuadratic ((C : ℂ) • Ω⁻¹) (gramRoot Ω x) := coefficientQuadratic_mono hcol _
      _ = C * ‖gramRoot Ω⁻¹ (gramRoot Ω x)‖ ^ 2 := by
        rw [coefficientQuadratic_real_scale, coefficientQuadratic, ← gramRoot_norm_sq hΩ.inv.posSemidef]
      _ = C * ‖x‖ ^ 2 := by rw [hx]
  change ‖Y‖ ≤ Real.sqrt C
  exact (Real.le_sqrt (norm_nonneg Y) hC).mpr hn

end SchauderTranslates
