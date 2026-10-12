import Lean_Code.SchauderTranslates.SeedCaptureSpectrum

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq α] [DecidableEq ι]

def carrierInclusion (ι : Type*) [Fintype ι] [DecidableEq ι] (L : ℕ) : Matrix (ι ⊕ Fin L) ι ℂ :=
  Matrix.fromRows 1 0

theorem carrierInclusion_mulVec (L : ℕ) (v : ι → ℂ) :
    carrierInclusion ι L *ᵥ v = Sum.elim v (0 : Fin L → ℂ) := by
  funext i
  cases i <;> simp [carrierInclusion, Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem carrierInclusion_compression (L : ℕ) (C : Matrix (ι ⊕ Fin L) (ι ⊕ Fin L) ℂ) :
    (carrierInclusion ι L)ᴴ * C * carrierInclusion ι L = C.submatrix Sum.inl Sum.inl := by
  apply Matrix.ext
  intro i j
  simp [carrierInclusion, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply,
    Matrix.one_apply, mul_ite, ite_mul, Matrix.submatrix_apply]

/-- Raw source from the original carrier coordinates into all auxiliary/row coordinates. -/
def carrierSource (b : α → ℂ) (i₀ : ι) (κ m : ℝ) (L : ℕ) : Matrix (α × (ι ⊕ Fin L)) ι ℂ :=
  tensorSource b ((m : ℂ) • seedBlock i₀ L κ) * carrierInclusion ι L

theorem carrierSource_mulVec (b : α → ℂ) (i₀ : ι) (κ m : ℝ) (L : ℕ) (v : ι → ℂ) :
    carrierSource b i₀ κ m L *ᵥ v = fun p : α × (ι ⊕ Fin L) => b p.1 *
      Sum.elim (fun i => (1 - (m : ℂ)) * v i) (fun _ => -(m : ℂ) * κ * v i₀) p.2 := by
  rw [carrierSource, ← Matrix.mulVec_mulVec, carrierInclusion_mulVec, tensorSource_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  funext p
  rcases p with ⟨k, i | j⟩
  · simp only [tensorVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      seedBlock_carrier_action, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      Finset.sum_const_zero, mul_zero, add_zero]
    ring
  · simp only [tensorVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      seedBlock_seed_action, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      Finset.sum_const_zero, mul_zero, add_zero]
    ring

/-- The finite inverse Gram sandwich agrees exactly with compression to carrier rows. -/
theorem carrierSource_sandwich (G : Matrix α α ℂ) (b : α → ℂ) (i₀ : ι) (κ m : ℝ) (L : ℕ) :
    (carrierSource b i₀ κ m L)ᴴ * (tensorGram G ((m : ℂ) • seedBlock i₀ L κ))⁻¹ *
      carrierSource b i₀ κ m L = seedCompressedCapture G b i₀ κ m L := by
  rw [carrierSource, Matrix.conjTranspose_mul]
  have he : (carrierInclusion ι L)ᴴ *
      (tensorSource b ((m : ℂ) • seedBlock i₀ L κ))ᴴ *
      (tensorGram G ((m : ℂ) • seedBlock i₀ L κ))⁻¹ *
      (tensorSource b ((m : ℂ) • seedBlock i₀ L κ) * carrierInclusion ι L) =
      (carrierInclusion ι L)ᴴ * tensorCapture G b ((m : ℂ) • seedBlock i₀ L κ) * carrierInclusion ι L := by
    simp only [tensorCapture, Matrix.mul_assoc]
  rw [he, carrierInclusion_compression]
  rfl

end SchauderTranslates
