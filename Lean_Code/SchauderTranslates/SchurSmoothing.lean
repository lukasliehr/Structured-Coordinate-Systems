import Lean_Code.SchauderTranslates.ScaledGramBound
import Mathlib.Analysis.Matrix.Order

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A correlation Schur multiplier fixes the identity. -/
theorem correlation_one_hadamard (Φ : Matrix ι ι ℂ) (hdiag : ∀ i, Φ i i = 1) :
    (1 : Matrix ι ι ℂ) ⊙ Φ = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.hadamard_apply, Matrix.one_apply, hij, hdiag]

/-- Entrywise smoothing retains any specified spectral floor. -/
theorem schur_preserves_floor {B Φ : Matrix ι ι ℂ} (hΦ : Φ.PosSemidef)
    (hdiag : ∀ i, Φ i i = 1) {σ : ℝ}
    (hfloor : (B - (σ : ℂ) • 1).PosSemidef) :
    (B ⊙ Φ - (σ : ℂ) • 1).PosSemidef := by
  have he : (B - (σ : ℂ) • 1) ⊙ Φ = B ⊙ Φ - (σ : ℂ) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.smul_apply, hdiag]
    · simp [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hij]
  rw [← he]
  exact hfloor.hadamard hΦ

theorem schur_posDef_of_floor {B Φ : Matrix ι ι ℂ} (hΦ : Φ.PosSemidef)
    (hdiag : ∀ i, Φ i i = 1) {σ : ℝ} (hσ : 0 < σ)
    (hfloor : (B - (σ : ℂ) • 1).PosSemidef) : (B ⊙ Φ).PosDef := by
  have hI : ((σ : ℂ) • (1 : Matrix ι ι ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hσ)
  have h := hI.add_posSemidef (schur_preserves_floor hΦ hdiag hfloor)
  simpa only [add_sub_cancel] using h

/-- Diagonal coefficient compression commutes with a Schur multiplier. -/
theorem schur_diagonal_congruence (B Φ : Matrix ι ι ℂ) (δ : ι → ℂ) :
    (Matrix.diagonal δ).conjTranspose * (B ⊙ Φ) * Matrix.diagonal δ =
      ((Matrix.diagonal δ).conjTranspose * B * Matrix.diagonal δ) ⊙ Φ := by
  rw [Matrix.diagonal_conjTranspose]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.hadamard_apply, Pi.star_apply]
  ring

theorem schur_gramDifference (B Φ : Matrix ι ι ℂ) (δ : ι → ℂ) (q : ℝ) :
    gramDifference q (Matrix.diagonal δ) (B ⊙ Φ) =
      gramDifference q (Matrix.diagonal δ) B ⊙ Φ := by
  unfold gramDifference
  rw [schur_diagonal_congruence]
  ext i j
  simp only [Matrix.hadamard_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
  ring

/-- Every diagonal coefficient prefix inequality survives correlation smoothing exactly. -/
theorem schur_preserves_prefix {B Φ : Matrix ι ι ℂ} (hB : B.PosDef)
    (hΦ : Φ.PosSemidef) (hBΦ : (B ⊙ Φ).PosDef) (δ : ι → ℂ) {q : ℝ} (hq : 0 ≤ q)
    (hp : ‖gramConjugate B (Matrix.diagonal δ)‖ ^ 2 ≤ q) :
    ‖gramConjugate (B ⊙ Φ) (Matrix.diagonal δ)‖ ^ 2 ≤ q := by
  have he (A : Matrix ι ι ℂ) (hA : A.PosDef) :
      ‖gramConjugate A (Matrix.diagonal δ)‖ ^ 2 ≤ q ↔
        (gramDifference q (Matrix.diagonal δ) A).PosSemidef := by
    simpa only [Real.sq_sqrt hq] using gram_prefix_iff hA (Matrix.diagonal δ) (Real.sqrt q)
  apply (he _ hBΦ).mpr
  rw [schur_gramDifference]
  exact ((he _ hB).mp hp).hadamard hΦ

/-- The inverse block certificate for a positive definite matrix. -/
theorem inverse_block_posSemidef {B : Matrix ι ι ℂ} (hB : B.PosDef) :
    (Matrix.fromBlocks B 1 1 B⁻¹).PosSemidef := by
  let : Invertible B := hB.isUnit.invertible
  have h := Matrix.PosDef.fromBlocks₁₁ (1 : Matrix ι ι ℂ) B⁻¹ hB
  simp only [Matrix.conjTranspose_one, one_mul, mul_one, sub_self] at h
  exact h.mpr Matrix.PosSemidef.zero

/-- Repeating a correlation matrix in four blocks preserves positivity. -/
theorem correlation_four_blocks {Φ : Matrix ι ι ℂ} (hΦ : Φ.PosSemidef) :
    (Matrix.fromBlocks Φ Φ Φ Φ).PosSemidef := by
  have h := hΦ.submatrix (Sum.elim (id : ι → ι) id)
  convert h using 1
  ext (i | i) (j | j) <;> rfl

/-- The inverse Schur inequality, expressed as a positive semidefinite difference. -/
theorem schur_inverse_le {B Φ : Matrix ι ι ℂ} (hB : B.PosDef) (hΦ : Φ.PosSemidef)
    (hdiag : ∀ i, Φ i i = 1) (hBΦ : (B ⊙ Φ).PosDef) :
    (B⁻¹ ⊙ Φ - (B ⊙ Φ)⁻¹).PosSemidef := by
  have hp := (inverse_block_posSemidef hB).hadamard (correlation_four_blocks hΦ)
  have he : (Matrix.fromBlocks B 1 1 B⁻¹) ⊙ (Matrix.fromBlocks Φ Φ Φ Φ) =
      Matrix.fromBlocks (B ⊙ Φ) 1 1 (B⁻¹ ⊙ Φ) := by
    have hI := correlation_one_hadamard Φ hdiag
    ext (i | i) (j | j)
    · rfl
    · exact congrArg (fun M : Matrix ι ι ℂ => M i j) hI
    · exact congrArg (fun M : Matrix ι ι ℂ => M i j) hI
    · rfl
  rw [he] at hp
  let : Invertible (B ⊙ Φ) := hBΦ.isUnit.invertible
  have h := Matrix.PosDef.fromBlocks₁₁ (1 : Matrix ι ι ℂ) (B⁻¹ ⊙ Φ) hBΦ
  simp only [Matrix.conjTranspose_one, one_mul, mul_one] at h
  exact h.mp hp

/-- Smoothing cannot increase any raw inverse diagonal. -/
theorem schur_inverse_diagonal_le {B Φ : Matrix ι ι ℂ} (hB : B.PosDef) (hΦ : Φ.PosSemidef)
    (hdiag : ∀ i, Φ i i = 1) (hBΦ : (B ⊙ Φ).PosDef) (i : ι) :
    ((B ⊙ Φ)⁻¹ i i).re ≤ (B⁻¹ i i).re := by
  have h := (schur_inverse_le hB hΦ hdiag hBΦ).diag_nonneg (i := i)
  have hr := (RCLike.nonneg_iff.mp h).1
  change 0 ≤ ((B⁻¹ ⊙ Φ - (B ⊙ Φ)⁻¹) i i).re at hr
  simpa only [Matrix.sub_apply, Matrix.hadamard_apply, hdiag, mul_one, Complex.sub_re,
    sub_nonneg] using hr

end SchauderTranslates
