import Lean_Code.SchauderTranslates.FiniteScalarGram
import Lean_Code.SchauderTranslates.PositiveBlockNorm
import Lean_Code.SchauderTranslates.ScaledGramBound

noncomputable section
open Matrix
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace FiniteScalarGram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inverse normalization, retaining the raw mass. -/
theorem rawCenteredGram_inverse_normalized (s : FiniteScalarGram ι) :
    s.rawCenteredGram⁻¹ = (s.mass : ℂ)⁻¹ • s.centeredGram⁻¹ := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.mass_pos.ne'
  rw [s.centeredGram_inverse, smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- The augmented inverse norm is bounded by the scalar corner and a centered inverse bound.
This is a Hilbert operator estimate; its constant does not depend on the list length. -/
theorem rawInverse_norm_le (s : FiniteScalarGram ι) {D : ℝ} (hD : 0 ≤ D)
    (hcenter : ∀ v : EuclideanSpace ℂ ι,
      coefficientQuadratic s.centeredGram⁻¹ v ≤ D * ‖v‖ ^ 2) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) s.rawGram⁻¹‖ ≤
      (1 + s.gain + D) / s.mass := by
  have ha : 0 ≤ (1 + s.gain) / s.mass :=
    div_nonneg (by linarith [s.gain_nonneg]) s.mass_pos.le
  have hb : 0 ≤ D / s.mass := div_nonneg hD s.mass_pos.le
  have h := positive_augmented_norm_le s.rawGram⁻¹ s.rawGram_posDef.inv.posSemidef ha hb
    (by rw [s.rawGram_inverse_constant_gain]; simp) (fun v => by
      rw [s.rawGram_inverse_nonconstant, s.rawCenteredGram_inverse_normalized,
        ← Complex.ofReal_inv, coefficientQuadratic_ofReal_smul]
      calc
        _ ≤ s.mass⁻¹ * (D * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hcenter v) (inv_nonneg.mpr s.mass_pos.le)
        _ = _ := by ring)
  exact h.trans_eq (by ring)

end FiniteScalarGram

namespace ScalarData
variable {d n : ℕ}

/-- Forgetting the torus representation preserves the scalar Gram interface exactly. -/
def finiteGram (s : ScalarData d n) : FiniteScalarGram (Fin n) where
  mass := s.mass
  mass_pos := s.toTorusWeight.mass_pos
  rawGram := s.rawGram
  rawGram_posDef := s.rawGram_posDef
  constant_mass := s.rawGram_diagonal _

theorem rawInverse_norm_le (s : ScalarData d n) {D : ℝ} (hD : 0 ≤ D)
    (hcenter : ∀ v : EuclideanSpace ℂ (Fin n),
      coefficientQuadratic s.centeredGram⁻¹ v ≤ D * ‖v‖ ^ 2) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) s.rawGram⁻¹‖ ≤
      (1 + s.gain + D) / s.mass := s.finiteGram.rawInverse_norm_le hD hcenter

end ScalarData
end SchauderTranslates
