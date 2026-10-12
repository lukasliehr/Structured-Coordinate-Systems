import Lean_Code.SchauderTranslates.TensorCaptureBasics
import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open Matrix
open scoped ComplexOrder Kronecker
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Raw mixed tensor metric in the original row coordinates. `Ω` is their
reference Gram and `B` their seed Gram. -/
def mixedTensorGram (G : Matrix ι ι ℂ) (Ω B : Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  G ⊗ₖ Ω + (1 - G) ⊗ₖ B

theorem mixedTensorGram_lower {G : Matrix ι ι ℂ} {Ω B : Matrix κ κ ℂ}
    (hG1 : (1 - G).PosSemidef) (hB : B.PosSemidef) :
    (mixedTensorGram G Ω B - G ⊗ₖ Ω).PosSemidef := by
  simpa only [mixedTensorGram, add_sub_cancel_left] using hG1.kronecker hB

theorem mixedTensorGram_posDef {G : Matrix ι ι ℂ} {Ω B : Matrix κ κ ℂ}
    (hG : G.PosDef) (hG1 : (1 - G).PosSemidef) (hΩ : Ω.PosDef) (hB : B.PosSemidef) :
    (mixedTensorGram G Ω B).PosDef :=
  (hG.kronecker hΩ).add_posSemidef (hG1.kronecker hB)

theorem mixedTensorGram_upper {G : Matrix ι ι ℂ} {Ω B : Matrix κ κ ℂ}
    (hG1 : (1 - G).PosSemidef) (hBΩ : (Ω - B).PosSemidef) :
    ((1 : Matrix ι ι ℂ) ⊗ₖ Ω - mixedTensorGram G Ω B).PosSemidef := by
  have he : (1 : Matrix ι ι ℂ) ⊗ₖ Ω - mixedTensorGram G Ω B = (1 - G) ⊗ₖ (Ω - B) := by
    ext i j
    change (1 : Matrix ι ι ℂ) i.1 j.1 * Ω i.2 j.2 -
      (G i.1 j.1 * Ω i.2 j.2 + ((1 : Matrix ι ι ℂ) i.1 j.1 - G i.1 j.1) * B i.2 j.2) =
      ((1 : Matrix ι ι ℂ) i.1 j.1 - G i.1 j.1) * (Ω i.2 j.2 - B i.2 j.2)
    ring
  rw [he]
  exact hG1.kronecker hBΩ

theorem kronecker_column_compression (G : Matrix ι ι ℂ) (Ω : Matrix κ κ ℂ) (k : ι) :
    (G ⊗ₖ Ω).submatrix (fun i => (k, i)) (fun i => (k, i)) = G k k • Ω := by
  ext i j
  rfl

/-- Every original column has synthesis metric bounded by its reference row metric. -/
theorem mixedTensorGram_column_upper {G : Matrix ι ι ℂ} {Ω B : Matrix κ κ ℂ}
    (hG1 : (1 - G).PosSemidef) (hBΩ : (Ω - B).PosSemidef) (k : ι) :
    (Ω - (mixedTensorGram G Ω B).submatrix (fun i => (k, i)) (fun i => (k, i))).PosSemidef := by
  have h := (mixedTensorGram_upper hG1 hBΩ).submatrix (fun i : κ => (k, i))
  simpa only [Matrix.submatrix_sub, Pi.sub_apply, kronecker_column_compression, Matrix.one_apply_eq,
    one_smul] using h

/-- Inversion gives a column extraction bound in the inverse reference metric. -/
theorem mixedTensorGram_inverse_column {G : Matrix ι ι ℂ} {Ω B : Matrix κ κ ℂ}
    (hG : G.PosDef) (hG1 : (1 - G).PosSemidef) (hΩ : Ω.PosDef) (hB : B.PosSemidef)
    (k : ι) {C : ℝ} (hdiag : G⁻¹ k k ≤ (C : ℂ)) :
    ((C : ℂ) • Ω⁻¹ - (mixedTensorGram G Ω B)⁻¹.submatrix
      (fun i => (k, i)) (fun i => (k, i))).PosSemidef := by
  have hh := matrix_inverse_antitone (hG.kronecker hΩ) (mixedTensorGram_posDef hG hG1 hΩ hB)
    (mixedTensorGram_lower hG1 hB)
  have h := hh.submatrix (fun i : κ => (k, i))
  simp only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.inv_kronecker, kronecker_column_compression] at h
  have hg := hΩ.inv.posSemidef.smul (sub_nonneg.mpr hdiag)
  convert h.add hg using 1
  simp only [sub_smul]
  abel

/-- A complete-column mask inherits any common auxiliary and Euclidean
quadratic bound without changing or orthonormalizing the original row basis. -/
theorem mixedTensorGram_column_difference (G D : Matrix ι ι ℂ) (Ω B : Matrix κ κ ℂ) (C : ℝ) :
    gramDifference C (D ⊗ₖ (1 : Matrix κ κ ℂ)) (mixedTensorGram G Ω B) =
      gramDifference C D G ⊗ₖ (Ω - B) + gramDifference C D 1 ⊗ₖ B := by
  have hform : mixedTensorGram G Ω B = G ⊗ₖ (Ω - B) + (1 : Matrix ι ι ℂ) ⊗ₖ B := by
    ext i j
    change G i.1 j.1 * Ω i.2 j.2 + ((1 : Matrix ι ι ℂ) i.1 j.1 - G i.1 j.1) * B i.2 j.2 =
      G i.1 j.1 * (Ω i.2 j.2 - B i.2 j.2) + (1 : Matrix ι ι ℂ) i.1 j.1 * B i.2 j.2
    ring
  rw [hform]
  simp only [gramDifference, smul_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, ← Matrix.smul_kronecker]
  ext i j
  change (C • G i.1 j.1) * (Ω - B) i.2 j.2 + (C • (1 : Matrix ι ι ℂ) i.1 j.1) * B i.2 j.2 -
    ((Dᴴ * G * D) i.1 j.1 * (Ω - B) i.2 j.2 + (Dᴴ * D) i.1 j.1 * B i.2 j.2) =
    (C • G i.1 j.1 - (Dᴴ * G * D) i.1 j.1) * (Ω - B) i.2 j.2 +
    (C • (1 : Matrix ι ι ℂ) i.1 j.1 - (Dᴴ * D) i.1 j.1) * B i.2 j.2
  simp only [Complex.real_smul]
  ring

theorem mixedTensorGram_complete_column_bound {G D : Matrix ι ι ℂ} {Ω B : Matrix κ κ ℂ}
    {C : ℝ} (hG : (gramDifference C D G).PosSemidef)
    (hI : (gramDifference C D 1).PosSemidef) (hB : B.PosSemidef) (hBΩ : (Ω - B).PosSemidef) :
    (gramDifference C (D ⊗ₖ (1 : Matrix κ κ ℂ)) (mixedTensorGram G Ω B)).PosSemidef := by
  rw [mixedTensorGram_column_difference]
  exact (hG.kronecker hBΩ).add (hI.kronecker hB)

end SchauderTranslates
