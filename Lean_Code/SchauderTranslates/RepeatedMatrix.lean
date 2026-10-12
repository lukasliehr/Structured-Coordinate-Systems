import Lean_Code.SchauderTranslates.ScalarGram

noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A direct sum in copy-major order, as used by the concatenated character list. -/
def repeatedMatrix {n : ℕ} (L : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (L * n)) (Fin (L * n)) ℂ :=
  (Matrix.blockDiagonal (fun _ : Fin L => B)).submatrix
    (finProdFinEquiv.symm.trans (Equiv.prodComm _ _))
    (finProdFinEquiv.symm.trans (Equiv.prodComm _ _))

@[simp] theorem repeatedMatrix_entry {n L : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin L) (a b : Fin n) :
    repeatedMatrix L B (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      if i = j then B a b else 0 := by
  simp [repeatedMatrix, Matrix.blockDiagonal_apply]

/-- Direct-sum inversion proved by multiplying the proposed inverse. -/
theorem blockDiagonal_inverse {ι ν : Type*} [Fintype ι] [Fintype ν]
    [DecidableEq ι] [DecidableEq ν] (B : ι → Matrix ν ν ℂ)
    (hB : ∀ i, IsUnit (B i)) :
    (Matrix.blockDiagonal B)⁻¹ = Matrix.blockDiagonal (fun i => (B i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.blockDiagonal_mul]
  have h (i : ι) : B i * (B i)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hB i))
  simp_rw [h]
  exact Matrix.blockDiagonal_one

theorem repeatedMatrix_inverse {n : ℕ} (L : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) : (repeatedMatrix L B)⁻¹ = repeatedMatrix L B⁻¹ := by
  unfold repeatedMatrix
  rw [Matrix.inv_submatrix_equiv, blockDiagonal_inverse _ (fun _ => hB)]

/-- Repeating a column in the same copy-major order. -/
def repeatedVector {n : ℕ} (L : ℕ) (v : Fin n → ℂ) : Fin (L * n) → ℂ :=
  fun q => v (finProdFinEquiv.symm q).2

@[simp] theorem repeatedVector_entry {n L : ℕ} (v : Fin n → ℂ) (i : Fin L) (a : Fin n) :
    repeatedVector L v (finProdFinEquiv (i, a)) = v a := by
  simp [repeatedVector]

/-- The repeated matrix acts separately on each repeated column. -/
theorem repeatedMatrix_mulVec {n : ℕ} (L : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) :
    repeatedMatrix L B *ᵥ repeatedVector L v = repeatedVector L (B *ᵥ v) := by
  funext q
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [Matrix.mulVec, dotProduct, ← finProdFinEquiv.sum_comp,
    Fintype.sum_prod_type, repeatedMatrix_entry, repeatedVector_entry]
  simp

/-- The capture quadratic form is additive across independent copies. -/
theorem repeatedMatrix_quadratic {n : ℕ} (L : ℕ) (B : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) :
    star (repeatedVector L v) ⬝ᵥ repeatedMatrix L B *ᵥ repeatedVector L v =
      (L : ℂ) * (star v ⬝ᵥ B *ᵥ v) := by
  rw [repeatedMatrix_mulVec]
  simp only [dotProduct, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    Pi.star_apply, repeatedVector_entry]
  simp [nsmul_eq_mul]

end SchauderTranslates
