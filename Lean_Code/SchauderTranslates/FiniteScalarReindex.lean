import Lean_Code.SchauderTranslates.FiniteScalarGram
import Lean_Code.SchauderTranslates.MatrixReindexNorm

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace FiniteScalarGram
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The mass and full augmented Gram determine finite scalar data. -/
@[ext] theorem ext {s t : FiniteScalarGram ι} (hm : s.mass = t.mass)
    (hB : s.rawGram = t.rawGram) : s = t := by
  cases s
  cases t
  cases hm
  cases hB
  rfl

/-- Relabel the nonconstant entries, leaving the distinguished constant first. -/
def reindex (s : FiniteScalarGram κ) (e : ι ≃ κ) : FiniteScalarGram ι where
  mass := s.mass
  mass_pos := s.mass_pos
  rawGram := s.rawGram.submatrix (Equiv.sumCongr (Equiv.refl Unit) e)
    (Equiv.sumCongr (Equiv.refl Unit) e)
  rawGram_posDef := s.rawGram_posDef.submatrix (Equiv.sumCongr (Equiv.refl Unit) e).injective
  constant_mass := s.constant_mass

@[simp] theorem reindex_mass (s : FiniteScalarGram κ) (e : ι ≃ κ) : (s.reindex e).mass = s.mass := rfl

@[simp] theorem reindex_mean (s : FiniteScalarGram κ) (e : ι ≃ κ) :
    (s.reindex e).mean = s.mean ∘ e := rfl

@[simp] theorem reindex_rawCenteredGram (s : FiniteScalarGram κ) (e : ι ≃ κ) :
    (s.reindex e).rawCenteredGram = s.rawCenteredGram.submatrix e e := rfl

@[simp] theorem reindex_centeredGram (s : FiniteScalarGram κ) (e : ι ≃ κ) :
    (s.reindex e).centeredGram = s.centeredGram.submatrix e e := rfl

/-- Gain can be read from the raw constant inverse entry, without choosing coordinates. -/
theorem gain_eq_mass_constant_inverse (s : FiniteScalarGram κ) :
    s.gain = s.mass * (s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re - 1 := by
  have he := congrArg Complex.re s.rawGram_inverse_constant_gain
  change (s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re = (1 + s.gain) / s.mass at he
  have h := (eq_div_iff s.mass_pos.ne').mp he
  linarith

@[simp] theorem reindex_gain (s : FiniteScalarGram κ) (e : ι ≃ κ) :
    (s.reindex e).gain = s.gain := by
  rw [gain_eq_mass_constant_inverse, gain_eq_mass_constant_inverse]
  change s.mass * (((s.rawGram.submatrix (Equiv.sumCongr (Equiv.refl Unit) e)
    (Equiv.sumCongr (Equiv.refl Unit) e))⁻¹) (Sum.inl ()) (Sum.inl ())).re - 1 = _
  rw [Matrix.inv_submatrix_equiv]
  rfl

/-- The raw augmented inverse norm is unchanged under a finite relabeling. -/
theorem reindex_rawInverse_norm (s : FiniteScalarGram κ) (e : ι ≃ κ) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) (s.reindex e).rawGram⁻¹‖ =
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) s.rawGram⁻¹‖ := by
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℂ))
    (s.rawGram.submatrix (Equiv.sumCongr (Equiv.refl Unit) e)
      (Equiv.sumCongr (Equiv.refl Unit) e))⁻¹‖ = _
  rw [Matrix.inv_submatrix_equiv, matrix_reindex_norm]

end FiniteScalarGram
end SchauderTranslates
