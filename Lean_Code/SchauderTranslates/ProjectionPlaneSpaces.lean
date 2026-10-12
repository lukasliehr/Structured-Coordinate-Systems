import Lean_Code.SchauderTranslates.ProjectionPlaneRotation

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {η K : Type*} [Fintype η] [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- One eigenvector and its possibly zero companion span a reducing block. -/
def projectionPlaneSpace (Q : K →L[ℝ] K) (t : ℝ) (v : K) : Submodule ℝ K :=
  Submodule.span ℝ {v, projectionCompanion Q t v}

theorem projectionPlaneSpace_first (Q : K →L[ℝ] K) (t : ℝ) (v : K) :
    v ∈ projectionPlaneSpace Q t v := Submodule.subset_span (by simp)

theorem projectionPlaneSpace_companion (Q : K →L[ℝ] K) (t : ℝ) (v : K) :
    projectionCompanion Q t v ∈ projectionPlaneSpace Q t v := Submodule.subset_span (by simp)

theorem projectionPlaneSpace_first_invariant (V : Submodule ℝ K) [V.HasOrthogonalProjection]
    (Q : K →L[ℝ] K) (e : OrthonormalBasis η ℝ V) (t : η → ℝ)
    (D : ProjectionPairDecomposition V Q e t) (i : η) (x : K)
    (hx : x ∈ projectionPlaneSpace Q (t i) (e i)) :
    V.starProjection x ∈ projectionPlaneSpace Q (t i) (e i) := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  simp only [map_add, map_smul, D.first_on_basis, D.first_on_companion, smul_zero, add_zero]
  exact (projectionPlaneSpace Q (t i) (e i)).smul_mem a (projectionPlaneSpace_first _ _ _)

theorem projectionPlaneSpace_second_invariant (V : Submodule ℝ K) [V.HasOrthogonalProjection]
    (Q : K →L[ℝ] K) (hQ : ∀ x, Q (Q x) = Q x)
    (hQS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (e : OrthonormalBasis η ℝ V) (t : η → ℝ)
    (D : ProjectionPairDecomposition V Q e t) (i : η) (x : K)
    (hx : x ∈ projectionPlaneSpace Q (t i) (e i)) :
    Q x ∈ projectionPlaneSpace Q (t i) (e i) := by
  let S := projectionPlaneSpace Q (t i) (e i : K)
  have hv : Q (e i) ∈ S := by
    have he : Q (e i) = t i • (e i : K) + Real.sqrt (t i * (1 - t i)) •
        projectionCompanion Q (t i) (e i) := by
      rw [projectionCompanion_rescale V Q hQ hQS (e i) (e.orthonormal.norm_eq_one i)
        (t i) (D.eigenvalues i).1 (D.eigenvalues i).2 (D.compression i)]
      simp [projectionResidual]
    rw [he]
    exact S.add_mem (S.smul_mem _ (projectionPlaneSpace_first _ _ _))
      (S.smul_mem _ (projectionPlaneSpace_companion _ _ _))
  have hw : Q (projectionCompanion Q (t i) (e i)) ∈ S := by
    simp only [projectionCompanion, projectionResidual, map_smul, map_sub, hQ]
    exact S.smul_mem _ (S.sub_mem hv (S.smul_mem _ hv))
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [map_add, map_smul, map_smul]
  exact S.add_mem (S.smul_mem a hv) (S.smul_mem b hw)

/-- Distinct eigenblocks are orthogonal, including degenerate endpoint blocks. -/
theorem projectionPlaneSpaces_orthogonal (V : Submodule ℝ K) [V.HasOrthogonalProjection]
    (Q : K →L[ℝ] K) (hQ : ∀ x, Q (Q x) = Q x)
    (hQS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (e : OrthonormalBasis η ℝ V) (t : η → ℝ) (D : ProjectionPairDecomposition V Q e t)
    (i j : η) (hij : i ≠ j) (x : K) (hx : x ∈ projectionPlaneSpace Q (t i) (e i))
    (y : K) (hy : y ∈ projectionPlaneSpace Q (t j) (e j)) : inner ℝ x y = 0 := by
  have hvv : inner ℝ (e i : K) (e j : K) = 0 := e.orthonormal.inner_eq_zero hij
  have hvw : inner ℝ (e i : K) (projectionCompanion Q (t j) (e j)) = 0 :=
    D.orthogonal_companions j (e i) (e i).property
  have hwv : inner ℝ (projectionCompanion Q (t i) (e i)) (e j : K) = 0 := by
    rw [real_inner_comm]
    exact D.orthogonal_companions i (e j) (e j).property
  have hww := projectionCompanion_inner_zero V Q hQ hQS (e i) (e j) (t i) (t j)
    (D.compression j) (e.orthonormal.inner_eq_zero hij)
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
  simp [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hvv, hvw, hwv, hww]

theorem projectionPlaneSpace_le_pairSpan (V : Submodule ℝ K) [V.HasOrthogonalProjection]
    (Q : K →L[ℝ] K) (e : OrthonormalBasis η ℝ V) (t : η → ℝ)
    (D : ProjectionPairDecomposition V Q e t) (i : η) :
    projectionPlaneSpace Q (t i) (e i) ≤ projectionPairSpan V Q := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [D.finite_span]
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ ((show V ≤ V ⊔ Submodule.span ℝ (Set.range (fun k => projectionCompanion Q (t k) (e k))) from le_sup_left) (e i).property)
  · exact Submodule.smul_mem _ _ ((show Submodule.span ℝ (Set.range (fun k => projectionCompanion Q (t k) (e k))) ≤
      V ⊔ Submodule.span ℝ (Set.range (fun k => projectionCompanion Q (t k) (e k))) from le_sup_right)
      (Submodule.subset_span (Set.mem_range_self i)))

/-- Every vector is a finite sum of eigenblock vectors and an orthogonal remainder. -/
theorem projectionPair_vector_decomposition (V : Submodule ℝ K) [V.HasOrthogonalProjection]
    (Q : K →L[ℝ] K) (e : OrthonormalBasis η ℝ V) (t : η → ℝ)
    (D : ProjectionPairDecomposition V Q e t) (x : K) :
    ∃ (a b : η → ℝ) (r : K), r ∈ (projectionPairSpan V Q)ᗮ ∧
      x = (∑ i, (a i • (e i : K) + b i • projectionCompanion Q (t i) (e i))) + r := by
  have hx : x ∈ projectionPairSpan V Q ⊔ (projectionPairSpan V Q)ᗮ := by rw [D.total_span]; trivial
  obtain ⟨u, hu, r, hr, hxr⟩ := Submodule.mem_sup.mp hx
  rw [D.finite_span] at hu
  obtain ⟨v, hv, w, hw, huv⟩ := Submodule.mem_sup.mp hu
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hw
  refine ⟨fun i => inner ℝ (e i) (⟨v, hv⟩ : V), b, r, hr, ?_⟩
  have hv' := congrArg V.subtype (e.sum_repr' (⟨v, hv⟩ : V))
  simp only [map_sum, map_smul, Submodule.subtype_apply] at hv'
  rw [Finset.sum_add_distrib, hv', hb, huv, hxr]

end SchauderTranslates
