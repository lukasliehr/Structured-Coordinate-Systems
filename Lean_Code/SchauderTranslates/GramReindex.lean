import Lean_Code.SchauderTranslates.RealComplexQuadratic
import Lean_Code.SchauderTranslates.MatrixReindexNorm

noncomputable section
open Matrix ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Coordinate relabeling intertwines the corresponding genuine Hilbert matrix operators. -/
theorem euclidean_reindex_matrix (e : ι ≃ κ) (B : Matrix κ κ ℂ) (x : EuclideanSpace ℂ ι) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        ((Matrix.toEuclideanCLM (𝕜 := ℂ)) (B.submatrix e e) x) =
      (Matrix.toEuclideanCLM (𝕜 := ℂ)) B (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x) := by
  ext k
  change (∑ i, B (e (e.symm k)) (e i) * x i) =
    ∑ j, B k j * x (e.symm j)
  rw [← e.sum_comp (fun j => B k j * x (e.symm j))]
  simp

/-- The coefficient quadratic form is invariant under relabeling its Hilbert coordinates. -/
theorem coefficientQuadratic_reindex (e : ι ≃ κ) (B : Matrix κ κ ℂ)
    (x : EuclideanSpace ℂ ι) :
    coefficientQuadratic (B.submatrix e e) x =
      coefficientQuadratic B (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x) := by
  let R := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  change RCLike.re (inner ℂ x ((Matrix.toEuclideanCLM (𝕜 := ℂ)) (B.submatrix e e) x)) = _
  rw [← R.inner_map_map, euclidean_reindex_matrix]
  rfl

/-- Prefix estimates are invariant under a simultaneous relabeling of the Gram and mask. -/
theorem gramConjugate_reindex_bound {B : Matrix κ κ ℂ} (hB : B.PosDef) (D : Matrix κ κ ℂ)
    (e : ι ≃ κ) {C : ℝ} (hC : 0 ≤ C) (h : ‖gramConjugate B D‖ ^ 2 ≤ C) :
    ‖gramConjugate (B.submatrix e e) (D.submatrix e e)‖ ^ 2 ≤ C := by
  apply (gramConjugate_quadratic_bound_iff (hB.submatrix e.injective) _ hC).mpr
  intro x
  rw [coefficientQuadratic_reindex, coefficientQuadratic_reindex, euclidean_reindex_matrix]
  exact (gramConjugate_quadratic_bound_iff hB D hC).mp h _

/-- Relabeling a diagonal mask simply composes its coefficient function with the equivalence. -/
theorem diagonal_submatrix_equiv (e : ι ≃ κ) (δ : κ → ℂ) :
    (Matrix.diagonal δ).submatrix e e = Matrix.diagonal (δ ∘ e) := by
  ext i j
  simp [Matrix.diagonal_apply, e.injective.eq_iff]

end SchauderTranslates
