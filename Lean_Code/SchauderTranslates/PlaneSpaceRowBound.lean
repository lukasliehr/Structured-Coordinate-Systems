import Lean_Code.SchauderTranslates.EigenplaneRowBound
import Lean_Code.SchauderTranslates.RowCutEndpoints
import Lean_Code.SchauderTranslates.ProjectionPlaneSpaces

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ η K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype η] [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- A whole eigenblock obeys the row bound, including either degenerate endpoint. -/
theorem projectionPlaneSpace_row_bound {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (old : κ → ι) (hold : Function.Injective old) (j : ι) (hj : ∀ k, old k ≠ j)
    (V : Submodule ℝ K) [V.HasOrthogonalProjection] (Q : K →L[ℝ] K)
    (hQ : ∀ x, Q (Q x) = Q x) (hQS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (e : OrthonormalBasis η ℝ V) (t : η → ℝ) (D : ProjectionPairDecomposition V Q e t)
    (i : η) (f : ι → K) (hf : ∀ k, f k ∈ projectionPlaneSpace Q (t i) (e i)) :
    activationEnergy B Q (familyRowCut old j V.starProjection f) ≤
      metricRowBound B old j * activationEnergy B Q f := by
  classical
  choose a b hab using fun k => Submodule.mem_span_pair.mp (hf k)
  by_cases hi : 0 < t i ∧ t i < 1
  · have hv : ‖(e i : K)‖ = 1 := e.orthonormal.norm_eq_one i
    have hw := projectionCompanion_norm V Q hQ hQS (e i) (e.orthonormal.norm_eq_one i)
      (t i) hi.1 hi.2 (D.compression i)
    have hvw : inner ℝ (e i : K) (projectionCompanion Q (t i) (e i)) = 0 :=
      D.orthogonal_companions i (e i) (e i).property
    obtain ⟨hQv, hQw⟩ := D.plane_action i hi.1 hi.2
    have hr := projectionPlane_rotation V.starProjection Q (e i)
      (projectionCompanion Q (t i) (e i)) hv hw hvw hi.1.le hi.2.le
      (D.first_on_basis i) (D.first_on_companion i) hQv hQw
    dsimp only at hr
    let c : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun k => Real.sqrt (t i) * a k + Real.sqrt (1 - t i) * b k)
    let d : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun k => Real.sqrt (1 - t i) * a k - Real.sqrt (t i) * b k)
    have hrepr : f = fun k =>
        c k • projectionPlaneActive (t i) (e i : K) (projectionCompanion Q (t i) (e i)) +
        d k • projectionPlaneInactive (t i) (e i : K) (projectionCompanion Q (t i) (e i)) := by
      ext k
      have hv' := hr.2.2.2.2.2.2.2.1
      have hw' := hr.2.2.2.2.2.2.2.2
      calc
        f k = a k • (e i : K) + b k • projectionCompanion Q (t i) (e i) := (hab k).symm
        _ = _ := (congrArg₂ (fun x y : K => x + y)
          (congrArg (fun x : K => a k • x) hv') (congrArg (fun x : K => b k • x) hw')).trans (by
            dsimp only [c, d, WithLp.toLp_ofLp, WithLp.ofLp_toLp]
            module)
    rw [hrepr]
    exact projection_eigenplane_row_bound hB hBI old hold j hj V Q hQ hQS e t D i hi.1 hi.2 c d
  · have he : t i = 0 ∨ t i = 1 := by
      by_contra hn
      push Not at hn
      have h0 := (D.eigenvalues i).1
      have h1 := (D.eigenvalues i).2
      exact hi ⟨lt_of_le_of_ne h0 hn.1.symm, lt_of_le_of_ne h1 hn.2⟩
    have hw := D.endpoint_companion i he
    have hrepr : f = fun k => a k • (e i : K) := by
      ext k
      simpa [hw] using (hab k).symm
    rw [hrepr]
    apply familyRowCut_common_eigenvector_bound hB hBI old hold j hj V.starProjection Q
      (e i) (δ := 1) (Or.inr rfl) (by simpa using D.first_on_basis i) _ (WithLp.toLp 2 a)
    rcases he with he | he
    · exact Or.inl (D.zero_eigenvalue i he)
    · exact Or.inr (D.one_eigenvalue i he)

end SchauderTranslates
