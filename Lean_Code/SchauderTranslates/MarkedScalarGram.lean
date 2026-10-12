import Lean_Code.SchauderTranslates.FiniteScalarGram

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Separates one distinguished coordinate, preserving all other coordinate labels. -/
def splitConstantEquiv (q₀ : κ) : Unit ⊕ {q : κ // q ≠ q₀} ≃ κ where
  toFun := Sum.elim (fun _ => q₀) Subtype.val
  invFun q := if h : q = q₀ then Sum.inl () else Sum.inr ⟨q,h⟩
  left_inv := by
    rintro (u | ⟨q,hq⟩)
    · cases u
      simp
    · simp [hq]
  right_inv := by
    intro q
    dsimp only
    split_ifs with h
    · exact h.symm
    · rfl

omit [Fintype κ] in
@[simp] theorem splitConstantEquiv_inl (q₀ : κ) (u : Unit) :
    splitConstantEquiv q₀ (Sum.inl u) = q₀ := rfl

omit [Fintype κ] in
@[simp] theorem splitConstantEquiv_inr (q₀ : κ) (q : {q : κ // q ≠ q₀}) :
    splitConstantEquiv q₀ (Sum.inr q) = q.1 := rfl

/-- A positive Gram becomes scalar Gram data once its actual constant entry and mass are identified. -/
def markedScalarGram (B : Matrix κ κ ℂ) (hB : B.PosDef) (q₀ : κ)
    (m : ℝ) (hm : 0 < m) (hmass : B q₀ q₀ = (m : ℂ)) :
    FiniteScalarGram {q : κ // q ≠ q₀} where
  mass := m
  mass_pos := hm
  rawGram := B.submatrix (splitConstantEquiv q₀) (splitConstantEquiv q₀)
  rawGram_posDef := hB.submatrix (splitConstantEquiv q₀).injective
  constant_mass := hmass

theorem markedScalarGram_inverse (B : Matrix κ κ ℂ) (hB : B.PosDef) (q₀ : κ)
    (m : ℝ) (hm : 0 < m) (hmass : B q₀ q₀ = (m : ℂ)) :
    (markedScalarGram B hB q₀ m hm hmass).rawGram⁻¹ =
      B⁻¹.submatrix (splitConstantEquiv q₀) (splitConstantEquiv q₀) :=
  Matrix.inv_submatrix_equiv B (splitConstantEquiv q₀) (splitConstantEquiv q₀)

/-- The raw centered inverse is the nonconstant block of the original inverse, without a mass factor. -/
theorem markedScalarGram_centered_inverse (B : Matrix κ κ ℂ) (hB : B.PosDef) (q₀ : κ)
    (m : ℝ) (hm : 0 < m) (hmass : B q₀ q₀ = (m : ℂ)) :
    (markedScalarGram B hB q₀ m hm hmass).rawCenteredGram⁻¹ =
      B⁻¹.submatrix (fun q : {q : κ // q ≠ q₀} => q.1) (fun q => q.1) := by
  rw [← FiniteScalarGram.rawGram_inverse_nonconstant, markedScalarGram_inverse]
  rfl

/-- The normalized quadratic gain equals `mass * raw constant inverse entry - 1`. -/
theorem markedScalarGram_gain (B : Matrix κ κ ℂ) (hB : B.PosDef) (q₀ : κ)
    (m : ℝ) (hm : 0 < m) (hmass : B q₀ q₀ = (m : ℂ)) :
    (markedScalarGram B hB q₀ m hm hmass).gain = m * (B⁻¹ q₀ q₀).re - 1 := by
  let s := markedScalarGram B hB q₀ m hm hmass
  have he := congrArg Complex.re s.rawGram_inverse_constant_gain
  rw [markedScalarGram_inverse] at he
  change (B⁻¹ q₀ q₀).re = (1 + s.gain) / m at he
  have hh := (eq_div_iff hm.ne').mp he
  change s.gain = _
  nlinarith

end SchauderTranslates
