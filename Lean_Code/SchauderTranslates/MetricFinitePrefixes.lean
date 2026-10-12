import Lean_Code.SchauderTranslates.FiniteRowMask

noncomputable section
open ContinuousLinearMap InnerProductSpace Matrix
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Selecting the coordinates in a finite set is precisely its zero-one diagonal matrix. -/
theorem selectionColumns_finset_projection (s : Finset ι) :
    selectionColumns (𝕜 := ℝ) (fun i : s => (i : ι)) *
      (selectionColumns (𝕜 := ℝ) (fun i : s => (i : ι))).conjTranspose =
      Matrix.diagonal (fun i : ι => if i ∈ s then (1 : ℝ) else 0) := by
  apply (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)).injective
  change (Matrix.toEuclideanCLM (𝕜 := ℝ)) _ = (Matrix.toEuclideanCLM (𝕜 := ℝ)) _
  rw [← coordinateSelection_matrix]
  ext x i
  rw [coordinateSelection_apply_coordinate]
  change familyCoordinateSelection (fun k : s => (k : ι)) (WithLp.ofLp x) i = _
  rw [familyCoordinateSelection_finset]
  simp [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal]

theorem metricPrefix_finset_diagonal (B : Matrix ι ι ℝ) (s : Finset ι) :
    metricPrefix B (fun i : s => (i : ι)) =
      gramConjugate B (Matrix.diagonal (fun i : ι => if i ∈ s then (1 : ℝ) else 0)) := by
  unfold metricPrefix
  rw [selectionColumns_finset_projection]

theorem metricPrefix_finset_sum {B : Matrix ι ι ℝ} (hB : B.PosSemidef) (s : Finset ι) :
    metricPrefix B (fun i : s => (i : ι)) =
      ∑ i ∈ s, rankOne ℝ (metricColumn B i) (metricDual B i) := by
  rw [metricPrefix_as_sum hB]
  exact Finset.sum_coe_sort s (fun i : ι => rankOne ℝ (metricColumn B i) (metricDual B i))

@[simp] theorem metricPrefix_finset_empty {B : Matrix ι ι ℝ} (hB : B.PosSemidef) :
    metricPrefix B (fun i : (∅ : Finset ι) => (i : ι)) = 0 := by
  rw [metricPrefix_finset_sum hB]
  simp

theorem metricPrefix_finset_insert {B : Matrix ι ι ℝ} (hB : B.PosSemidef)
    (s : Finset ι) (j : ι) (hj : j ∉ s) :
    metricPrefix B (fun i : (insert j s : Finset ι) => (i : ι)) =
      metricPrefix B (fun i : s => (i : ι)) + rankOne ℝ (metricColumn B j) (metricDual B j) := by
  rw [metricPrefix_finset_sum hB, metricPrefix_finset_sum hB, Finset.sum_insert hj]
  exact add_comm _ _

/-- The single-coordinate metric prefix has squared norm equal to the primal/dual diagonal product. -/
theorem metricPrefix_finset_singleton_norm_sq {B : Matrix ι ι ℝ} (hB : B.PosSemidef) (j : ι) :
    ‖metricPrefix B (fun i : ({j} : Finset ι) => (i : ι))‖ ^ 2 = B j j * B⁻¹ j j := by
  rw [metricPrefix_finset_sum hB]
  simp only [Finset.sum_singleton, norm_rankOne, mul_pow, metricColumn_norm_sq hB,
    metricDual_norm_sq hB]

end SchauderTranslates
