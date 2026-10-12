import Lean_Code.SchauderTranslates.HilbertRowCut
import Lean_Code.SchauderTranslates.ProjectionPlaneRotation

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ η K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype η] [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The abstract coefficient estimate applies to the actual eigenplanes of two projections. -/
theorem projection_eigenplane_row_bound {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (old : κ → ι) (hold : Function.Injective old) (j : ι) (hj : ∀ k, old k ≠ j)
    (V : Submodule ℝ K) [V.HasOrthogonalProjection] (Q : K →L[ℝ] K)
    (hQ : ∀ x, Q (Q x) = Q x) (hQS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (e : OrthonormalBasis η ℝ V) (t : η → ℝ) (D : ProjectionPairDecomposition V Q e t)
    (i : η) (hi0 : 0 < t i) (hi1 : t i < 1) (a b : EuclideanSpace ℝ ι) :
    let v := projectionPlaneActive (t i) (e i : K) (projectionCompanion Q (t i) (e i))
    let w := projectionPlaneInactive (t i) (e i : K) (projectionCompanion Q (t i) (e i))
    activationEnergy B Q (familyRowCut old j V.starProjection (fun k => a k • v + b k • w)) ≤
      metricRowBound B old j * activationEnergy B Q (fun k => a k • v + b k • w) := by
  have hv : ‖(e i : K)‖ = 1 := e.orthonormal.norm_eq_one i
  have hw := projectionCompanion_norm V Q hQ hQS (e i) (e.orthonormal.norm_eq_one i)
    (t i) hi0 hi1 (D.compression i)
  have hvw : inner ℝ (e i : K) (projectionCompanion Q (t i) (e i)) = 0 :=
    D.orthogonal_companions i (e i) (e i).property
  obtain ⟨hQv, hQw⟩ := D.plane_action i hi0 hi1
  have hr := projectionPlane_rotation V.starProjection Q (e i)
    (projectionCompanion Q (t i) (e i)) hv hw hvw hi0.le hi1.le
    (D.first_on_basis i) (D.first_on_companion i) hQv hQw
  dsimp only at hr ⊢
  exact familyRowCut_plane_bound hB hBI old hold j hj V.starProjection Q _ _ hr.1 hr.2.1
    hr.2.2.2.1 hr.2.2.2.2.1 hi0.le hi1.le hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 a b

end SchauderTranslates
