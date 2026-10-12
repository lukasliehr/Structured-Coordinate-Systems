import Lean_Code.SchauderTranslates.SelectedColumnBounds

noncomputable section
open Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Insert a row-coordinate operator between a selected column's synthesis
and extraction maps. The reference metric cancels exactly on both sides. -/
theorem selected_mask_factorization {H : Matrix ι ι ℂ} {Ω : Matrix κ κ ℂ}
    (hH : H.PosSemidef) (hΩ : Ω.PosDef) (e : κ → ι) (D : Matrix κ κ ℂ) :
    let E := matrixHilbertMap (selectionColumns (𝕜 := ℂ) e)
    let X := (gramRoot H).comp (E.comp (gramRootInv Ω))
    let Y := (gramRootInv H).comp (E.comp (gramRoot Ω))
    X.comp ((gramConjugate Ω D).comp (Y†)) =
      gramConjugate H (selectionColumns (𝕜 := ℂ) e * D *
        (selectionColumns (𝕜 := ℂ) e).conjTranspose) := by
  have hi (z : EuclideanSpace ℂ κ) : gramRootInv Ω (gramRoot Ω z) = z := by
    rw [← ContinuousLinearMap.comp_apply, gramRoot_inv_mul hΩ, one_apply_eq_self]
  change _ = (gramRoot H).comp ((matrixHilbertMap (selectionColumns (𝕜 := ℂ) e * D *
    (selectionColumns (𝕜 := ℂ) e).conjTranspose)).comp (gramRootInv H))
  rw [matrixHilbertMap_mul, matrixHilbertMap_mul, matrixHilbertMap_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  simp only [gramConjugate, adjoint_comp, gramRoot_adjoint, gramRootInv_adjoint hH,
    ContinuousLinearMap.comp_apply, hi]
  rfl

/-- The norm of an arbitrary row cut inside one column is at most the row
prefix constant times the square root of the inverse-column constant. -/
theorem selected_mask_bound {H : Matrix ι ι ℂ} {Ω : Matrix κ κ ℂ}
    (hH : H.PosSemidef) (hΩ : Ω.PosDef) (e : κ → ι) (D : Matrix κ κ ℂ)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hcol : (Ω - H.submatrix e e).PosSemidef)
    (hinv : ((C : ℂ) • Ω⁻¹ - H⁻¹.submatrix e e).PosSemidef)
    (hD : ‖gramConjugate Ω D‖ ≤ K) :
    ‖gramConjugate H (selectionColumns (𝕜 := ℂ) e * D *
      (selectionColumns (𝕜 := ℂ) e).conjTranspose)‖ ≤ Real.sqrt C * K := by
  let E := matrixHilbertMap (selectionColumns (𝕜 := ℂ) e)
  let X := (gramRoot H).comp (E.comp (gramRootInv Ω))
  let Y := (gramRootInv H).comp (E.comp (gramRoot Ω))
  have hx : ‖X‖ ≤ 1 := selected_primal_contraction hH hΩ e hcol
  have hy : ‖Y‖ ≤ Real.sqrt C := selected_dual_bound hH hΩ e hC hinv
  rw [← selected_mask_factorization hH hΩ e D]
  change ‖X.comp ((gramConjugate Ω D).comp (Y†))‖ ≤ _
  calc
    _ ≤ ‖X‖ * (‖gramConjugate Ω D‖ * ‖Y†‖) :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg X))
    _ ≤ 1 * (K * Real.sqrt C) := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul hx (mul_le_mul hD hy (norm_nonneg Y) hK)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    _ = Real.sqrt C * K := by ring

end SchauderTranslates
