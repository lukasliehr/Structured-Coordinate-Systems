import Lean_Code.SchauderTranslates.SeedEigenvalues

noncomputable section
open Matrix
open scoped MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The lower-eigenvalue spectral projection, with entries in the distinguished plane coordinates. -/
def seedLowerProjection (a s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (seedUpperEigenvalue a s - seedLowerEigenvalue a s)⁻¹ •
    !![seedUpperEigenvalue a s - 1, -s; -s, 1 - seedLowerEigenvalue a s]

def seedSpectralMass (a s : ℝ) : ℝ :=
  (seedUpperEigenvalue a s - 1) / (seedUpperEigenvalue a s - seedLowerEigenvalue a s)

theorem seedLowerProjection_hermitian (a s : ℝ) : (seedLowerProjection a s).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [seedLowerProjection, Matrix.smul_apply]

theorem seedLowerProjection_idempotent {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    seedLowerProjection a s * seedLowerProjection a s = seedLowerProjection a s := by
  have hb := seedEigenvalues_bounds ha0 ha1 hs
  have hd : seedUpperEigenvalue a s - seedLowerEigenvalue a s ≠ 0 := (sub_pos.mpr hb.2.2.2).ne'
  have hgap := seedEigenvalue_gap_product (a := a) hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seedLowerProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply] <;>
    field_simp <;> nlinarith

theorem seedLowerProjection_eigen {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    seedPlane a s * seedLowerProjection a s = seedLowerEigenvalue a s • seedLowerProjection a s := by
  have hb := seedEigenvalues_bounds ha0 ha1 hs
  have hd : seedUpperEigenvalue a s - seedLowerEigenvalue a s ≠ 0 := (sub_pos.mpr hb.2.2.2).ne'
  have hgap := seedEigenvalue_gap_product (a := a) hs
  have ht : a + s ^ 2 = seedLowerEigenvalue a s + seedUpperEigenvalue a s - 1 := by
    linarith [seedEigenvalues_sum a hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seedPlane, seedLowerProjection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, ht] <;>
    field_simp <;> nlinarith

theorem seedPlane_spectral_decomposition {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    seedPlane a s = seedLowerEigenvalue a s • seedLowerProjection a s +
      seedUpperEigenvalue a s • (1 - seedLowerProjection a s) := by
  have hb := seedEigenvalues_bounds ha0 ha1 hs
  have hd : seedUpperEigenvalue a s - seedLowerEigenvalue a s ≠ 0 := (sub_pos.mpr hb.2.2.2).ne'
  have ht : a + s ^ 2 = seedLowerEigenvalue a s + seedUpperEigenvalue a s - 1 := by
    linarith [seedEigenvalues_sum a hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seedPlane, seedLowerProjection, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, ht] <;>
    field_simp <;> ring

/-- The displayed coefficient is the squared norm of the actual lower spectral projection of the first unit vector. -/
theorem seedSpectralMass_projection_norm {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    ‖(seedLowerProjection a s).toEuclideanLin (EuclideanSpace.single 0 (1 : ℝ))‖ ^ 2 =
      seedSpectralMass a s := by
  have hb := seedEigenvalues_bounds ha0 ha1 hs
  have hd : seedUpperEigenvalue a s - seedLowerEigenvalue a s ≠ 0 := (sub_pos.mpr hb.2.2.2).ne'
  have hgap := seedEigenvalue_gap_product (a := a) hs
  rw [Matrix.toEuclideanLin_apply, EuclideanSpace.norm_sq_eq]
  simp [seedLowerProjection, seedSpectralMass, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    EuclideanSpace.single, Matrix.smul_apply, Real.norm_eq_abs, sq_abs]
  field_simp
  simp only [sq_abs]
  nlinarith [congrArg (fun r : ℝ => r * (seedUpperEigenvalue a s - seedLowerEigenvalue a s)) hgap]

theorem seedSpectralMass_bounds {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    0 < seedSpectralMass a s ∧ seedSpectralMass a s < 1 := by
  have hb := seedEigenvalues_bounds ha0 ha1 hs
  have hd := sub_pos.mpr hb.2.2.2
  constructor
  · exact div_pos (sub_pos.mpr hb.2.2.1) hd
  · apply (div_lt_one hd).mpr
    linarith [hb.2.1]

end SchauderTranslates
