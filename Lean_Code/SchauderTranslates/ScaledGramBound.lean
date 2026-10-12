import Lean_Code.SchauderTranslates.RealComplexQuadratic

noncomputable section
open Matrix
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coefficientQuadratic_ofReal_smul (B : Matrix ι ι ℂ) (r : ℝ) (x : EuclideanSpace ℂ ι) :
    coefficientQuadratic ((r : ℂ) • B) x = r * coefficientQuadratic B x := by
  rw [coefficientQuadratic_eq_dot, coefficientQuadratic_eq_dot,
    Matrix.smul_mulVec, dotProduct_smul]
  change ((r : ℂ) * (star x.ofLp ⬝ᵥ B *ᵥ x.ofLp)).re = r * _
  simp

/-- Normalizing a positive Gram by its mass does not change any coefficient projection bound. -/
theorem gramConjugate_scaled_bound {B : Matrix ι ι ℂ} (hB : B.PosDef) (D : Matrix ι ι ℂ)
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C) (h : ‖gramConjugate B D‖ ^ 2 ≤ C) :
    ‖gramConjugate ((r : ℂ) • B) D‖ ^ 2 ≤ C := by
  have hscaled : ((r : ℂ) • B).PosDef := hB.smul (by exact_mod_cast hr)
  apply (gramConjugate_quadratic_bound_iff hscaled D hC).mpr
  intro x
  have hx := (gramConjugate_quadratic_bound_iff hB D hC).mp h x
  rw [coefficientQuadratic_ofReal_smul, coefficientQuadratic_ofReal_smul]
  have hh := mul_le_mul_of_nonneg_left hx hr.le
  nlinarith

end SchauderTranslates
