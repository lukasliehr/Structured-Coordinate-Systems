import Lean_Code.SchauderTranslates.ScalarGram

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Block inversion under invertibility alone, before proving positivity of the Schur complement. -/
theorem scalar_schur_inverse_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℝ} (hm : 0 < m) (b : ι → ℂ) (G : Matrix ι ι ℂ)
    (hB : IsUnit (Matrix.fromBlocks (massBlock m) (momentRow b) (momentColumn b) G)) :
    (Matrix.fromBlocks (massBlock m) (momentRow b) (momentColumn b) G)⁻¹ =
      let A := G - (m : ℂ)⁻¹ • Matrix.vecMulVec b (star b)
      Matrix.fromBlocks
        ((massBlock m)⁻¹ + (massBlock m)⁻¹ * momentRow b * A⁻¹ * momentColumn b * (massBlock m)⁻¹)
        (-((massBlock m)⁻¹ * momentRow b * A⁻¹))
        (-(A⁻¹ * momentColumn b * (massBlock m)⁻¹)) A⁻¹ := by
  let : Invertible (massBlock m) := (massBlock_posDef hm).isUnit.invertible
  let : Invertible (Matrix.fromBlocks (massBlock m) (momentRow b) (momentColumn b) G) :=
    hB.invertible
  let := Matrix.invertibleOfFromBlocks₁₁Invertible
    (massBlock m) (momentRow b) (momentColumn b) G
  have hi := Matrix.invOf_fromBlocks₁₁_eq (massBlock m) (momentRow b) (momentColumn b) G
  rw [Matrix.invOf_eq_nonsing_inv] at hi
  simp only [Matrix.invOf_eq_nonsing_inv, massBlock_schur hm.ne' b G] at hi
  exact hi

/-- The scalar Schur complement of a positive augmented Gram is positive definite. -/
theorem scalar_schur_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℝ} (hm : 0 < m) (b : ι → ℂ) (G : Matrix ι ι ℂ)
    (hB : (Matrix.fromBlocks (massBlock m) (momentRow b) (momentColumn b) G).PosDef) :
    (G - (m : ℂ)⁻¹ • Matrix.vecMulVec b (star b)).PosDef := by
  let A := G - (m : ℂ)⁻¹ • Matrix.vecMulVec b (star b)
  let : Invertible (massBlock m) := (massBlock_posDef hm).isUnit.invertible
  have hunit : IsUnit A := by
    have h := Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mp hB.isUnit
    simpa only [Matrix.invOf_eq_nonsing_inv, massBlock_schur hm.ne' b G] using h
  have hi : A⁻¹.PosDef := by
    have h := hB.inv.submatrix Sum.inr_injective
    rw [scalar_schur_inverse_of_isUnit hm b G hB.isUnit] at h
    exact h
  have h := hi.inv
  rwa [Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det _).mp hunit)] at h

end SchauderTranslates
