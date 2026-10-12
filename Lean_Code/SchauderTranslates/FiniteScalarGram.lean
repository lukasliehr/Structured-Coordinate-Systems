import Lean_Code.SchauderTranslates.ScalarSchur

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A finite positive Gram with its distinguished constant coordinate and raw mass.
No probability normalization or torus representation is built into this algebraic interface. -/
structure FiniteScalarGram (ι : Type*) [Fintype ι] where
  mass : ℝ
  mass_pos : 0 < mass
  rawGram : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ
  rawGram_posDef : rawGram.PosDef
  constant_mass : rawGram (Sum.inl ()) (Sum.inl ()) = (mass : ℂ)

namespace FiniteScalarGram
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def moment (s : FiniteScalarGram ι) : ι → ℂ := fun i => s.rawGram (Sum.inr i) (Sum.inl ())

def nonconstantGram (s : FiniteScalarGram ι) : Matrix ι ι ℂ :=
  s.rawGram.submatrix Sum.inr Sum.inr

def rawCenteredGram (s : FiniteScalarGram ι) : Matrix ι ι ℂ :=
  s.nonconstantGram - (s.mass : ℂ)⁻¹ • Matrix.vecMulVec s.moment (star s.moment)

def centeredGram (s : FiniteScalarGram ι) : Matrix ι ι ℂ :=
  (s.mass : ℂ)⁻¹ • s.rawCenteredGram

def mean (s : FiniteScalarGram ι) : ι → ℂ := (s.mass : ℂ)⁻¹ • s.moment

def gain (s : FiniteScalarGram ι) : ℝ :=
  (star s.mean ⬝ᵥ s.centeredGram⁻¹ *ᵥ s.mean).re

omit [DecidableEq ι] in
theorem rawGram_fromBlocks (s : FiniteScalarGram ι) :
    s.rawGram = Matrix.fromBlocks (massBlock s.mass) (momentRow s.moment)
      (momentColumn s.moment) s.nonconstantGram := by
  ext (i | i) (j | j)
  · cases i; cases j
    exact s.constant_mass
  · cases i
    exact (s.rawGram_posDef.isHermitian.apply (Sum.inl ()) (Sum.inr j)).symm
  · cases j
    rfl
  · rfl

theorem rawCenteredGram_posDef (s : FiniteScalarGram ι) : s.rawCenteredGram.PosDef := by
  apply scalar_schur_posDef s.mass_pos s.moment s.nonconstantGram
  rw [← s.rawGram_fromBlocks]
  exact s.rawGram_posDef

theorem centeredGram_posDef (s : FiniteScalarGram ι) : s.centeredGram.PosDef := by
  unfold centeredGram
  apply s.rawCenteredGram_posDef.smul
  exact_mod_cast inv_pos.mpr s.mass_pos

theorem rawGram_inverse (s : FiniteScalarGram ι) :
    s.rawGram⁻¹ = Matrix.fromBlocks
      ((massBlock s.mass)⁻¹ + (massBlock s.mass)⁻¹ * momentRow s.moment *
        s.rawCenteredGram⁻¹ * momentColumn s.moment * (massBlock s.mass)⁻¹)
      (-((massBlock s.mass)⁻¹ * momentRow s.moment * s.rawCenteredGram⁻¹))
      (-(s.rawCenteredGram⁻¹ * momentColumn s.moment * (massBlock s.mass)⁻¹))
      s.rawCenteredGram⁻¹ := by
  rw [s.rawGram_fromBlocks]
  exact scalar_schur_inverse s.mass_pos s.moment s.nonconstantGram
    s.rawCenteredGram_posDef

/-- The nonconstant principal block of the augmented inverse is the raw centered inverse. -/
theorem rawGram_inverse_nonconstant (s : FiniteScalarGram ι) :
    s.rawGram⁻¹.submatrix Sum.inr Sum.inr = s.rawCenteredGram⁻¹ := by
  rw [s.rawGram_inverse]
  rfl

/-- Normalized and raw centered inverses differ by exactly the mass. -/
theorem centeredGram_inverse (s : FiniteScalarGram ι) :
    s.centeredGram⁻¹ = (s.mass : ℂ) • s.rawCenteredGram⁻¹ := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.mass_pos.ne'
  let : Invertible ((s.mass : ℂ)⁻¹) := (isUnit_iff_ne_zero.mpr (inv_ne_zero hm)).invertible
  rw [centeredGram, Matrix.inv_smul _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp s.rawCenteredGram_posDef.isUnit)]
  simp only [invOf_eq_inv, inv_inv]

/-- The constant entry of the raw inverse, before introducing the normalized gain. -/
theorem rawGram_inverse_constant (s : FiniteScalarGram ι) :
    s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ()) = (s.mass : ℂ)⁻¹ +
      (s.mass : ℂ)⁻¹ ^ 2 * (star s.moment ⬝ᵥ s.rawCenteredGram⁻¹ *ᵥ s.moment) := by
  rw [s.rawGram_inverse, massBlock_inverse s.mass_pos.ne']
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.mul_apply,
    momentRow, momentColumn, dotProduct, Matrix.mulVec, Pi.star_apply,
    Finset.univ_unique, Finset.sum_singleton, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The gain's complex quadratic form is the raw mean capture divided by the mass. -/
theorem gain_quadratic (s : FiniteScalarGram ι) :
    star s.mean ⬝ᵥ s.centeredGram⁻¹ *ᵥ s.mean =
      (s.mass : ℂ)⁻¹ * (star s.moment ⬝ᵥ s.rawCenteredGram⁻¹ *ᵥ s.moment) := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.mass_pos.ne'
  rw [s.centeredGram_inverse]
  simp only [mean, Matrix.smul_mulVec, Matrix.mulVec_smul, star_smul,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
    map_inv₀]
  field_simp

theorem gain_nonneg (s : FiniteScalarGram ι) : 0 ≤ s.gain :=
  s.centeredGram_posDef.inv.posSemidef.re_dotProduct_nonneg s.mean

/-- The gain is real because the normalized centered inverse is Hermitian. -/
theorem gain_quadratic_eq_real (s : FiniteScalarGram ι) :
    star s.mean ⬝ᵥ s.centeredGram⁻¹ *ᵥ s.mean = (s.gain : ℂ) := by
  apply Complex.ext
  · rfl
  · have hi := s.centeredGram_posDef.inv.isHermitian.im_star_dotProduct_mulVec_self s.mean
    exact hi

/-- The mass/gain identity used in the cutoff and activation arguments. -/
theorem rawGram_inverse_constant_gain (s : FiniteScalarGram ι) :
    s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ()) = (((1 + s.gain) / s.mass : ℝ) : ℂ) := by
  calc
    _ = (s.mass : ℂ)⁻¹ + (s.mass : ℂ)⁻¹ *
        (star s.mean ⬝ᵥ s.centeredGram⁻¹ *ᵥ s.mean) := by
      rw [s.rawGram_inverse_constant, s.gain_quadratic]
      ring
    _ = _ := by
      rw [s.gain_quadratic_eq_real]
      push_cast
      ring


end FiniteScalarGram
end SchauderTranslates
