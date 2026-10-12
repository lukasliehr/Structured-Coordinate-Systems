import Lean_Code.SchauderTranslates.ScalarData

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The singleton mass block, kept explicit for block inversion. -/
def massBlock (m : ℝ) : Matrix Unit Unit ℂ := fun _ _ => (m : ℂ)

def momentRow {ι : Type*} (b : ι → ℂ) : Matrix Unit ι ℂ := fun _ i => star (b i)

def momentColumn {ι : Type*} (b : ι → ℂ) : Matrix ι Unit ℂ := fun i _ => b i

theorem massBlock_posDef {m : ℝ} (hm : 0 < m) : (massBlock m).PosDef := by
  have h : (m : ℂ) > 0 := by exact_mod_cast hm
  convert! (Matrix.PosDef.one (n := Unit) (R := ℂ)).smul h using 1
  ext i j
  simp [massBlock, Matrix.smul_apply, Subsingleton.elim i j]

theorem massBlock_inverse {m : ℝ} (hm : m ≠ 0) :
    (massBlock m)⁻¹ = fun _ _ => (m : ℂ)⁻¹ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  apply Matrix.inv_eq_right_inv
  ext i j
  simp [massBlock, Matrix.mul_apply, Subsingleton.elim i j, hm']

/-- The singleton Schur complement is precisely the raw centered Gram. -/
theorem massBlock_schur {ι : Type*} [Fintype ι] {m : ℝ} (hm : m ≠ 0)
    (b : ι → ℂ) (G : Matrix ι ι ℂ) :
    G - momentColumn b * (massBlock m)⁻¹ * momentRow b =
      G - (m : ℂ)⁻¹ • Matrix.vecMulVec b (star b) := by
  rw [massBlock_inverse hm]
  ext i j
  simp only [Matrix.sub_apply, Matrix.mul_apply, momentColumn, momentRow,
    Finset.univ_unique, Finset.sum_singleton, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, smul_eq_mul]
  ring

/-- Full block inversion with the scalar mass and raw centered Gram. -/
theorem scalar_schur_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℝ} (hm : 0 < m) (b : ι → ℂ) (G : Matrix ι ι ℂ)
    (hA : (G - (m : ℂ)⁻¹ • Matrix.vecMulVec b (star b)).PosDef) :
    (Matrix.fromBlocks (massBlock m) (momentRow b) (momentColumn b) G)⁻¹ =
      let A := G - (m : ℂ)⁻¹ • Matrix.vecMulVec b (star b)
      Matrix.fromBlocks
        ((massBlock m)⁻¹ + (massBlock m)⁻¹ * momentRow b * A⁻¹ * momentColumn b * (massBlock m)⁻¹)
        (-((massBlock m)⁻¹ * momentRow b * A⁻¹))
        (-(A⁻¹ * momentColumn b * (massBlock m)⁻¹)) A⁻¹ := by
  let A := G - (m : ℂ)⁻¹ • Matrix.vecMulVec b (star b)
  let : Invertible (massBlock m) := (massBlock_posDef hm).isUnit.invertible
  have hs : G - momentColumn b * ⅟(massBlock m) * momentRow b = A := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact massBlock_schur hm.ne' b G
  let : Invertible (G - momentColumn b * ⅟(massBlock m) * momentRow b) :=
    (show IsUnit (G - momentColumn b * ⅟(massBlock m) * momentRow b) by
      rw [hs]; exact hA.isUnit).invertible
  let := Matrix.fromBlocks₁₁Invertible (massBlock m) (momentRow b) (momentColumn b) G
  have hi := Matrix.invOf_fromBlocks₁₁_eq (massBlock m) (momentRow b) (momentColumn b) G
  rw [Matrix.invOf_eq_nonsing_inv] at hi
  simp only [Matrix.invOf_eq_nonsing_inv, massBlock_schur hm.ne' b G] at hi
  exact hi

namespace ScalarData
variable {d n : ℕ}

theorem rawGram_inverse (s : ScalarData d n) :
    s.rawGram⁻¹ = Matrix.fromBlocks
      ((massBlock s.mass)⁻¹ + (massBlock s.mass)⁻¹ * momentRow s.moment *
        s.rawCenteredGram⁻¹ * momentColumn s.moment * (massBlock s.mass)⁻¹)
      (-((massBlock s.mass)⁻¹ * momentRow s.moment * s.rawCenteredGram⁻¹))
      (-(s.rawCenteredGram⁻¹ * momentColumn s.moment * (massBlock s.mass)⁻¹))
      s.rawCenteredGram⁻¹ := by
  rw [s.rawGram_fromBlocks]
  exact scalar_schur_inverse s.toTorusWeight.mass_pos s.moment s.nonconstantGram
    s.rawCenteredGram_posDef

/-- The nonconstant principal block of the augmented inverse is the raw centered inverse. -/
theorem rawGram_inverse_nonconstant (s : ScalarData d n) :
    s.rawGram⁻¹.submatrix Sum.inr Sum.inr = s.rawCenteredGram⁻¹ := by
  rw [s.rawGram_inverse]
  rfl

/-- Normalized and raw centered inverses differ by exactly the mass. -/
theorem centeredGram_inverse (s : ScalarData d n) :
    s.centeredGram⁻¹ = (s.mass : ℂ) • s.rawCenteredGram⁻¹ := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.toTorusWeight.mass_pos.ne'
  let : Invertible ((s.mass : ℂ)⁻¹) := (isUnit_iff_ne_zero.mpr (inv_ne_zero hm)).invertible
  rw [centeredGram, Matrix.inv_smul _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp s.rawCenteredGram_posDef.isUnit)]
  simp only [invOf_eq_inv, inv_inv]

/-- The constant entry of the raw inverse, before introducing the normalized gain. -/
theorem rawGram_inverse_constant (s : ScalarData d n) :
    s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ()) = (s.mass : ℂ)⁻¹ +
      (s.mass : ℂ)⁻¹ ^ 2 * (star s.moment ⬝ᵥ s.rawCenteredGram⁻¹ *ᵥ s.moment) := by
  rw [s.rawGram_inverse, massBlock_inverse s.toTorusWeight.mass_pos.ne']
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
theorem gain_quadratic (s : ScalarData d n) :
    star s.mean ⬝ᵥ s.centeredGram⁻¹ *ᵥ s.mean =
      (s.mass : ℂ)⁻¹ * (star s.moment ⬝ᵥ s.rawCenteredGram⁻¹ *ᵥ s.moment) := by
  have hm : (s.mass : ℂ) ≠ 0 := by exact_mod_cast s.toTorusWeight.mass_pos.ne'
  rw [s.centeredGram_inverse]
  simp only [mean, Matrix.smul_mulVec, Matrix.mulVec_smul, star_smul,
    dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
    map_inv₀]
  field_simp

theorem gain_nonneg (s : ScalarData d n) : 0 ≤ s.gain :=
  s.centeredGram_posDef.inv.posSemidef.re_dotProduct_nonneg s.mean

/-- The gain is real because the normalized centered inverse is Hermitian. -/
theorem gain_quadratic_eq_real (s : ScalarData d n) :
    star s.mean ⬝ᵥ s.centeredGram⁻¹ *ᵥ s.mean = (s.gain : ℂ) := by
  apply Complex.ext
  · rfl
  · have hi := s.centeredGram_posDef.inv.isHermitian.im_star_dotProduct_mulVec_self s.mean
    exact hi

/-- The mass/gain identity used in the cutoff and activation arguments. -/
theorem rawGram_inverse_constant_gain (s : ScalarData d n) :
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

end ScalarData
end SchauderTranslates
