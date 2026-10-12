import Lean_Code.SchauderTranslates.PlaneSpaceRowBound
import Lean_Code.SchauderTranslates.OrthogonalRowAssembly

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι κ η K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype η] [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Assemble all eigenplanes, endpoint eigenspaces and the infinite remainder of a row cut. -/
theorem projection_row_bound_of_decomposition {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (old : κ → ι) (hold : Function.Injective old) (j : ι) (hj : ∀ k, old k ≠ j)
    (V : Submodule ℝ K) [V.HasOrthogonalProjection] (Q : K →L[ℝ] K)
    (hQ : ∀ x, Q (Q x) = Q x) (hQS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (e : OrthonormalBasis η ℝ V) (t : η → ℝ) (D : ProjectionPairDecomposition V Q e t)
    (f : ι → K) :
    activationEnergy B Q (familyRowCut old j V.starProjection f) ≤
      metricRowBound B old j * activationEnergy B Q f := by
  classical
  let S : Option η → Submodule ℝ K := fun a => match a with
    | none => (projectionPairSpan V Q)ᗮ
    | some i => projectionPlaneSpace Q (t i) (e i)
  have hS : ∀ a b, a ≠ b → ∀ x ∈ S a, ∀ y ∈ S b, inner ℝ x y = 0 := by
    intro a b hab x hx y hy
    cases a with
    | none =>
      cases b with
      | none => exact (hab rfl).elim
      | some k =>
        rw [real_inner_comm]
        exact hx y (projectionPlaneSpace_le_pairSpan V Q e t D k hy)
    | some k =>
      cases b with
      | none => exact hy x (projectionPlaneSpace_le_pairSpan V Q e t D k hx)
      | some l =>
        exact projectionPlaneSpaces_orthogonal V Q hQ hQS e t D k l
          (fun h => hab (congrArg some h)) x hx y hy
  have hF : ∀ a, ∀ x ∈ S a, V.starProjection x ∈ S a := by
    intro a x hx
    cases a with
    | none => rw [(D.remainder x hx).1]; exact (S none).zero_mem
    | some k => exact projectionPlaneSpace_first_invariant V Q e t D k x hx
  have hQ' : ∀ a, ∀ x ∈ S a, Q x ∈ S a := by
    intro a x hx
    cases a with
    | none => exact (D.remainder x hx).2.1
    | some k => exact projectionPlaneSpace_second_invariant V Q hQ hQS e t D k x hx
  choose a b r hr hrepr using fun i => projectionPair_vector_decomposition V Q e t D (f i)
  let g : Option η → ι → K := fun k i => match k with
    | none => r i
    | some k => a i k • (e k : K) + b i k • projectionCompanion Q (t k) (e k)
  have hg : ∀ k i, g k i ∈ S k := by
    intro k i
    cases k with
    | none => exact hr i
    | some k =>
      exact (S (some k)).add_mem
        ((S (some k)).smul_mem _ (projectionPlaneSpace_first _ _ _))
        ((S (some k)).smul_mem _ (projectionPlaneSpace_companion _ _ _))
  have hf : f = ∑ k, g k := by
    ext i
    rw [hrepr i]
    simp only [Finset.sum_apply, Fintype.sum_option, g]
    abel
  have hbnd (k) : activationEnergy B Q (familyRowCut old j V.starProjection (g k)) ≤
      metricRowBound B old j * activationEnergy B Q (g k) := by
    cases k with
    | none =>
      exact familyRowCut_remainder_bound hB hBI old hold j hj V.starProjection Q _
        (D.remainder (r j) (hr j)).1
    | some k =>
      exact projectionPlaneSpace_row_bound hB hBI old hold j hj V Q hQ hQS e t D
        k (g (some k)) (hg (some k))
  rw [hf]
  exact familyRowCut_bound_of_subspaces B old j V.starProjection Q S hS hF hQ' g hg _ hbnd

/-- Uniform rare-activation row estimate for any finite-rank first projection and any
orthogonal second projection, on an arbitrary real Hilbert space. -/
theorem real_projection_row_bound {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (old : κ → ι) (hold : Function.Injective old) (j : ι) (hj : ∀ k, old k ≠ j)
    (V : Submodule ℝ K) [FiniteDimensional ℝ V] (Q : K →L[ℝ] K)
    (hQ : ∀ x, Q (Q x) = Q x) (hQS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (f : ι → K) :
    activationEnergy B Q (familyRowCut old j V.starProjection f) ≤
      metricRowBound B old j * activationEnergy B Q f := by
  obtain ⟨e, t, D⟩ := finite_projection_pair_decomposition V Q hQ hQS
  exact projection_row_bound_of_decomposition hB hBI old hold j hj V Q hQ hQS e t D f

/-- Operator formulation: a finite-rank orthogonal first projection need not be supplied as a subspace. -/
theorem real_projection_row_bound_of_maps {B : Matrix ι ι ℝ} (hB : B.PosDef) (hBI : B ≤ 1)
    (old : κ → ι) (hold : Function.Injective old) (j : ι) (hj : ∀ k, old k ≠ j)
    (F Q : K →L[ℝ] K) [FiniteDimensional ℝ (LinearMap.range F.toLinearMap)]
    (hF : ∀ x, F (F x) = F x) (hFS : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y))
    (hQ : ∀ x, Q (Q x) = Q x) (hQS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (f : ι → K) :
    activationEnergy B Q (familyRowCut old j F f) ≤ metricRowBound B old j * activationEnergy B Q f := by
  obtain ⟨hFEq, e, t, D⟩ := finite_projection_pair_decomposition_of_maps F Q hF hFS hQ hQS
  rw [hFEq]
  exact projection_row_bound_of_decomposition hB hBI old hold j hj _ Q hQ hQS e t D f

end SchauderTranslates
