import Lean_Code.SchauderTranslates.SeedSpectralProjection

noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

def seedComplexLowerProjection (a s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (seedLowerProjection a s).map Complex.ofReal

lemma ofReal_matrix_mul {ι κ ν : Type*} [Fintype κ] (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal :=
  Matrix.map_mul (f := Complex.ofRealHom)

lemma ofReal_matrix_smul {ι κ : Type*} (a : ℝ) (A : Matrix ι κ ℝ) :
    (a • A).map Complex.ofReal = (a : ℂ) • A.map Complex.ofReal := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

lemma ofReal_matrix_adjoint {ι κ : Type*} (A : Matrix ι κ ℝ) :
    Aᴴ.map Complex.ofReal = (A.map Complex.ofReal)ᴴ := by
  ext i j
  simp [Matrix.map_apply, Matrix.conjTranspose_apply]

theorem seedComplexLowerProjection_hermitian (a s : ℝ) :
    (seedComplexLowerProjection a s).IsHermitian := by
  change ((seedLowerProjection a s).map Complex.ofReal)ᴴ = _
  rw [← ofReal_matrix_adjoint, (seedLowerProjection_hermitian a s).eq]
  rfl

theorem seedComplexLowerProjection_idempotent {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    seedComplexLowerProjection a s * seedComplexLowerProjection a s = seedComplexLowerProjection a s := by
  unfold seedComplexLowerProjection
  rw [← ofReal_matrix_mul, seedLowerProjection_idempotent ha0 ha1 hs]

theorem seedComplexLowerProjection_eigen {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    (seedPlane a s).map Complex.ofReal * seedComplexLowerProjection a s =
      (seedLowerEigenvalue a s : ℂ) • seedComplexLowerProjection a s := by
  unfold seedComplexLowerProjection
  rw [← ofReal_matrix_mul, seedLowerProjection_eigen ha0 ha1 hs, ofReal_matrix_smul]

theorem seedComplexLowerProjection_mass {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    ‖(seedComplexLowerProjection a s).toEuclideanLin (EuclideanSpace.single 0 (1 : ℂ))‖ ^ 2 =
      seedSpectralMass a s := by
  have h := seedSpectralMass_projection_norm ha0 ha1 hs
  rw [Matrix.toEuclideanLin_apply, EuclideanSpace.norm_sq_eq] at h ⊢
  simpa [seedComplexLowerProjection, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    EuclideanSpace.single, Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs] using h

end SchauderTranslates
