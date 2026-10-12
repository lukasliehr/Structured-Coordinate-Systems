import Lean_Code.SchauderTranslates.ScalarInverseNorm
import Lean_Code.SchauderTranslates.ScalarProducts
import Lean_Code.SchauderTranslates.RepeatedQuadratic
import Lean_Code.SchauderTranslates.ScalarFloorNumerics

noncomputable section
open Matrix
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace FiniteScalarGram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Centering takes a principal block of the raw inverse; normalization contributes the mass. -/
theorem centeredInverse_quadratic_le (s : FiniteScalarGram ι) (v : EuclideanSpace ℂ ι) :
    coefficientQuadratic s.centeredGram⁻¹ v ≤
      s.mass * ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) s.rawGram⁻¹‖ * ‖v‖ ^ 2 := by
  let x : EuclideanSpace ℂ (Unit ⊕ ι) := WithLp.toLp 2 (Sum.elim (fun _ => 0) v)
  have hright : augmentedRight x = x := by
    ext (i | i) <;> simp [augmentedRight, x]
  have htail : augmentedTail x = v := by ext i; rfl
  have hn : ‖x‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [augmented_norm_sq, htail]
    simp [x]
  have h := coefficientQuadratic_le_opNorm s.rawGram⁻¹ x
  have he := coefficientQuadratic_augmentedRight s.rawGram⁻¹ x
  rw [hright, htail, s.rawGram_inverse_nonconstant] at he
  rw [he, hn] at h
  rw [s.centeredGram_inverse, coefficientQuadratic_ofReal_smul]
  have hh := mul_le_mul_of_nonneg_left h s.mass_pos.le
  simpa only [mul_assoc] using hh

end FiniteScalarGram

namespace ScalarData
variable {d n : ℕ}

theorem centeredInverse_quadratic_le (s : ScalarData d n) (v : EuclideanSpace ℂ (Fin n)) :
    coefficientQuadratic s.centeredGram⁻¹ v ≤
      s.mass * ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) s.rawGram⁻¹‖ * ‖v‖ ^ 2 :=
  s.finiteGram.centeredInverse_quadratic_le v

/-- Direct sums preserve the cutoff inverse bound with precisely one copy's mass. -/
theorem product_centeredInverse_quadratic_le (s : ScalarData d n) (L : ℕ)
    {h : ℝ} (hcut : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) s.rawGram⁻¹‖ ≤ h)
    (v : EuclideanSpace ℂ (Fin (L * n))) :
    coefficientQuadratic (s.product L).centeredGram⁻¹ v ≤ s.mass * h * ‖v‖ ^ 2 := by
  rw [s.product_centeredGram, repeatedMatrix_inverse _ _ s.centeredGram_posDef.isUnit]
  apply repeatedMatrix_quadratic_le _ _ v
  intro u
  exact (s.centeredInverse_quadratic_le u).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcut s.toTorusWeight.mass_pos.le) (sq_nonneg _))

/-- Augmented inverse estimate for the actual independent product of the finite cutoff block. -/
theorem product_rawInverse_norm_le (s : ScalarData d n) (L : ℕ)
    {h : ℝ} (hcut : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) s.rawGram⁻¹‖ ≤ h) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) (s.product L).rawGram⁻¹‖ ≤
      (1 + L * s.gain + s.mass * h) / s.mass ^ L := by
  have hh : 0 ≤ h := (norm_nonneg _).trans hcut
  have hbound := (s.product L).rawInverse_norm_le (mul_nonneg s.toTorusWeight.mass_pos.le hh)
    (s.product_centeredInverse_quadratic_le L hcut)
  simpa only [s.product_gain, s.product_mass] using hbound

end ScalarData

/-- Spectral-floor propagation for one activation/cutoff/product step.
`cut` is the finite scalar cutoff. The cutoff lemma supplies `hcut`; the numerical rare-step
lemma supplies the product gain and deficit bounds. The product itself is the actual torus
block `cut.product L`, not an arbitrary positive matrix. -/
theorem scalar_floor_step {d n : ℕ} (cut : ScalarData d n) (L : ℕ)
    {ε ε' h : ℝ} (he : 0 < ε) (hemax : ε ≤ 1 / 10)
    (he' : 0 < ε') (hdecrease : ε' ≤ ε - 3 * ε ^ 2 / 4)
    (hmass : (cut.product L).mass = 1 - ε')
    (hgain : (cut.product L).gain ≤ 1 / 323)
    (hcut : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) cut.rawGram⁻¹‖ ≤ h)
    (hold : h ≤ ε⁻¹ ^ 2) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) (cut.product L).rawGram⁻¹‖ ≤ ε'⁻¹ ^ 2 := by
  apply scalar_floor_norm_step he hemax he' hdecrease hold
  have hh : 0 ≤ h := (norm_nonneg _).trans hcut
  have hm : 0 < 1 - ε' := hmass ▸ (cut.product L).toTorusWeight.mass_pos
  have hM : cut.mass * h ≤ h := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right cut.toTorusWeight.mass_le_one hh
  have hbound := cut.product_rawInverse_norm_le L hcut
  rw [← cut.product_mass, hmass, ← cut.product_gain] at hbound
  refine hbound.trans (div_le_div_of_nonneg_right ?_ hm.le)
  linarith

end SchauderTranslates
