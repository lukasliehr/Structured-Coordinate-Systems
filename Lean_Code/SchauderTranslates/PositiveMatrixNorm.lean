import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixHilbert_nonneg {B : Matrix ι ι ℂ} (hB : B.PosSemidef) :
    0 ≤ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) B := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  exact Matrix.isPositive_toEuclideanLin_iff.mpr hB

/-- A positive-matrix order bound controls the actual Euclidean operator norm. -/
theorem positive_matrix_norm_le {B : Matrix ι ι ℂ} (hB : B.PosSemidef)
    {r : ℝ} (hr : 0 ≤ r) (hupper : ((r : ℂ) • (1 : Matrix ι ι ℂ) - B).PosSemidef) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) B‖ ≤ r := by
  let Φ := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap (Φ B) hr (matrixHilbert_nonneg hB)).mpr
  have h := matrixHilbert_nonneg hupper
  change 0 ≤ Φ ((r : ℂ) • 1 - B) at h
  rw [map_sub, map_smul, map_one] at h
  change 0 ≤ algebraMap ℝ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) r - Φ B at h
  exact sub_nonneg.mp h

end SchauderTranslates
