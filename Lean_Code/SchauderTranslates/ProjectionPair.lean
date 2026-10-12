import Lean_Code.SchauderTranslates.HilbertBlocks

noncomputable section
open scoped InnerProductSpace

namespace SchauderTranslates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Pythagorean identity for a symmetric idempotent, without a dimension hypothesis. -/
theorem symmetric_projection_norm_sq (Q : E →L[ℝ] E)
    (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) (x : E) :
    ‖Q x‖ ^ 2 = inner ℝ x (Q x) := by
  rw [← real_inner_self_eq_norm_sq, hS, hQ]

theorem symmetric_projection_remainder_sq (Q : E →L[ℝ] E)
    (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) (x : E) :
    ‖x - Q x‖ ^ 2 = ‖x‖ ^ 2 - ‖Q x‖ ^ 2 := by
  rw [norm_sub_sq_real, ← symmetric_projection_norm_sq Q hQ hS]
  ring

/-- Compression to the finite-dimensional range of the first projection. -/
def projectionCompression (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) : V →L[ℝ] V :=
  V.orthogonalProjectionOnto.comp (Q.comp V.subtypeL)

theorem projectionCompression_symmetric (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) :
    (projectionCompression V Q).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (V.orthogonalProjectionOnto (Q x)) y =
    inner ℝ x (V.orthogonalProjectionOnto (Q y))
  simpa only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
    Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left] using hS x y

/-- Every eigenvalue of a compressed orthogonal projection lies in the closed unit interval. -/
theorem projectionCompression_eigenvalue_mem (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (v : V) (hv : ‖v‖ = 1) (t : ℝ) (ht : projectionCompression V Q v = t • v) :
    0 ≤ t ∧ t ≤ 1 := by
  have hi : inner ℝ (v : E) (Q v) = t := by
    calc
      _ = inner ℝ v (projectionCompression V Q v) := by
        simp [projectionCompression]
      _ = t := by rw [ht, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]; ring
  have hn : ‖Q (v : E)‖ ^ 2 = t := by
    rw [symmetric_projection_norm_sq Q hQ hS, hi]
  have hr := symmetric_projection_remainder_sq Q hQ hS (v : E)
  have hv' : ‖(v : E)‖ = 1 := hv
  rw [hn, hv'] at hr
  exact ⟨by nlinarith [sq_nonneg ‖Q (v : E)‖], by nlinarith [sq_nonneg ‖(v : E) - Q v‖]⟩

/-- Diagonalize the compression; the ambient space may be infinite dimensional. -/
theorem exists_projection_eigenbasis (V : Submodule ℝ E) [FiniteDimensional ℝ V]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) :
    ∃ (e : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V) (t : Fin (Module.finrank ℝ V) → ℝ),
      (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
      ∀ i, projectionCompression V Q (e i) = t i • e i := by
  let h := projectionCompression_symmetric V Q hS
  refine ⟨h.eigenvectorBasis rfl, h.eigenvalues rfl, ?_, ?_⟩
  · intro i
    exact projectionCompression_eigenvalue_mem V Q hQ hS _
      ((h.eigenvectorBasis rfl).orthonormal.norm_eq_one i) _ (h.apply_eigenvectorBasis rfl i)
  · exact h.apply_eigenvectorBasis rfl

/-- The unnormalized companion of an eigenvector of the compression. -/
def projectionResidual (Q : E →L[ℝ] E) (t : ℝ) (v : E) : E := Q v - t • v

theorem projectionResidual_orthogonal (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (v : V) (t : ℝ)
    (ht : projectionCompression V Q v = t • v) : projectionResidual Q t v ∈ Vᗮ := by
  intro x hx
  let u : V := ⟨x, hx⟩
  have hi : inner ℝ x (Q v) = t * inner ℝ x (v : E) := by
    calc
      _ = inner ℝ u (projectionCompression V Q v) := by simp [projectionCompression, u]
      _ = _ := by rw [ht, real_inner_smul_right]; rfl
  simpa only [projectionResidual, inner_sub_right, real_inner_smul_right, sub_eq_zero] using hi

theorem projectionResidual_action (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (v : E) (t : ℝ) :
    Q (projectionResidual Q t v) = (1 - t) • (t • v + projectionResidual Q t v) := by
  simp only [projectionResidual, map_sub, map_smul, hQ, add_sub_cancel]
  rw [sub_smul, one_smul]

/-- Mixed Gram entries of a compressed eigenvector. -/
theorem projection_eigen_inner (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (v w : V) (s : ℝ)
    (hw : projectionCompression V Q w = s • w) :
    inner ℝ (v : E) (Q w) = s * inner ℝ (v : E) (w : E) := by
  calc
    _ = inner ℝ v (projectionCompression V Q w) := by simp [projectionCompression]
    _ = _ := by rw [hw, real_inner_smul_right]; rfl

/-- Residual Gram identity; it includes both endpoint eigenvalues. -/
theorem projectionResidual_inner (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (v w : V) (t s : ℝ) (hw : projectionCompression V Q w = s • w) :
    inner ℝ (projectionResidual Q t v) (projectionResidual Q s w) =
      s * (1 - s) * inner ℝ (v : E) (w : E) := by
  simp only [projectionResidual, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hS, hQ, map_smul,
    projection_eigen_inner V Q v w s hw]
  ring

theorem projectionResidual_norm_sq (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (v : V) (hv : ‖v‖ = 1) (t : ℝ) (ht : projectionCompression V Q v = t • v) :
    ‖projectionResidual Q t v‖ ^ 2 = t * (1 - t) := by
  rw [← real_inner_self_eq_norm_sq, projectionResidual_inner V Q hQ hS v v t t ht,
    real_inner_self_eq_norm_sq]
  change t * (1 - t) * ‖v‖ ^ 2 = _
  rw [hv]
  ring

theorem projection_eigen_zero (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (v : V) (ht : projectionCompression V Q v = 0) : Q (v : E) = 0 := by
  have hi := projection_eigen_inner V Q v v 0 (by simpa using ht)
  have hn := symmetric_projection_norm_sq Q hQ hS (v : E)
  rw [hi, zero_mul] at hn
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem projection_eigen_one (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (v : V) (ht : projectionCompression V Q v = v) : Q (v : E) = v := by
  have hi := projection_eigen_inner V Q v v 1 (by simpa using ht)
  have hn := symmetric_projection_norm_sq Q hQ hS (v : E)
  have hr := symmetric_projection_remainder_sq Q hQ hS (v : E)
  rw [hi, one_mul, real_inner_self_eq_norm_sq] at hn
  rw [hn, sub_self] at hr
  exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hr))).symm

/-- Unit companion on a genuine two-dimensional plane. -/
def projectionCompanion (Q : E →L[ℝ] E) (t : ℝ) (v : E) : E :=
  (Real.sqrt (t * (1 - t)))⁻¹ • projectionResidual Q t v

theorem projectionCompanion_orthogonal (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (v : V) (t : ℝ)
    (ht : projectionCompression V Q v = t • v) : projectionCompanion Q t v ∈ Vᗮ :=
  Vᗮ.smul_mem _ (projectionResidual_orthogonal V Q v t ht)

theorem projectionCompanion_norm (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (v : V) (hv : ‖v‖ = 1) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (ht : projectionCompression V Q v = t • v) : ‖projectionCompanion Q t v‖ = 1 := by
  have hp : 0 < t * (1 - t) := mul_pos ht0 (sub_pos.mpr ht1)
  have hr : ‖projectionResidual Q t v‖ = Real.sqrt (t * (1 - t)) := by
    have hn := projectionResidual_norm_sq V Q hQ hS v hv t ht
    nlinarith [Real.sq_sqrt hp.le, Real.sqrt_nonneg (t * (1 - t)),
      norm_nonneg (projectionResidual Q t v)]
  simp only [projectionCompanion, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), hr]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hp))

/-- Rescaling recovers the residual, also at eigenvalues zero and one. -/
theorem projectionCompanion_rescale (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (v : V) (hv : ‖v‖ = 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ht : projectionCompression V Q v = t • v) :
    Real.sqrt (t * (1 - t)) • projectionCompanion Q t v = projectionResidual Q t v := by
  by_cases hc : Real.sqrt (t * (1 - t)) = 0
  · have hp : t * (1 - t) = 0 := (Real.sqrt_eq_zero (mul_nonneg ht0 (sub_nonneg.mpr ht1))).mp hc
    have hn := projectionResidual_norm_sq V Q hQ hS v hv t ht
    rw [hp] at hn
    have hr : projectionResidual Q t v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    simp [hc, hr]
  · simp [projectionCompanion, smul_smul, hc]

/-- The two columns of the projection on a genuine eigenplane. -/
theorem projectionCompanion_actions (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (v : V) (hv : ‖v‖ = 1) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (ht : projectionCompression V Q v = t • v) :
    Q (v : E) = t • (v : E) + Real.sqrt (t * (1 - t)) • projectionCompanion Q t v ∧
    Q (projectionCompanion Q t v) = Real.sqrt (t * (1 - t)) • (v : E) +
      (1 - t) • projectionCompanion Q t v := by
  have hp : 0 < t * (1 - t) := mul_pos ht0 (sub_pos.mpr ht1)
  have hc : Real.sqrt (t * (1 - t)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hs : (Real.sqrt (t * (1 - t)))⁻¹ * ((1 - t) * t) = Real.sqrt (t * (1 - t)) := by
    rw [inv_mul_eq_div]
    apply (div_eq_iff hc).mpr
    nlinarith [Real.sq_sqrt hp.le]
  constructor
  · rw [projectionCompanion_rescale V Q hQ hS v hv t ht0.le ht1.le ht]
    simp [projectionResidual]
  · simp only [projectionCompanion, map_smul, projectionResidual_action Q hQ,
      smul_add, smul_smul]
    rw [hs]
    congr 1
    congr 1
    ring

theorem projectionCompanion_inner_zero (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (v w : V) (t s : ℝ) (hw : projectionCompression V Q w = s • w)
    (hvw : inner ℝ v w = 0) :
    inner ℝ (projectionCompanion Q t v) (projectionCompanion Q s w) = 0 := by
  simp only [projectionCompanion, real_inner_smul_left, real_inner_smul_right,
    projectionResidual_inner V Q hQ hS v w t s hw]
  change _ * (_ * (s * (1 - s) * inner ℝ v w)) = 0
  simp [hvw]

/-- The finite span needed by both projections, before choosing plane coordinates. -/
def projectionPairSpan (V : Submodule ℝ E) (Q : E →L[ℝ] E) : Submodule ℝ E :=
  V ⊔ V.map Q.toLinearMap

theorem projectionPairSpan_invariant (V : Submodule ℝ E) (Q : E →L[ℝ] E)
    (hQ : ∀ x, Q (Q x) = Q x) {x : E} (hx : x ∈ projectionPairSpan V Q) :
    Q x ∈ projectionPairSpan V Q := by
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u, hu, rfl⟩ := hw
  change Q (v + Q u) ∈ projectionPairSpan V Q
  rw [map_add, hQ]
  exact (projectionPairSpan V Q).add_mem
    (le_sup_right (b := V.map Q.toLinearMap) ⟨v, hv, rfl⟩)
    (le_sup_right (b := V.map Q.toLinearMap) ⟨u, hu, rfl⟩)

theorem projectionPairSpan_orthogonal_invariant (V : Submodule ℝ E) (Q : E →L[ℝ] E)
    (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    {x : E} (hx : x ∈ (projectionPairSpan V Q)ᗮ) : Q x ∈ (projectionPairSpan V Q)ᗮ := by
  intro y hy
  rw [← hS]
  exact hx (Q y) (projectionPairSpan_invariant V Q hQ hy)

/-- On the remaining orthogonal summand, the first projection vanishes and the second
splits every vector into its orthogonal range and kernel components. -/
theorem projectionPair_remainder (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    {x : E} (hx : x ∈ (projectionPairSpan V Q)ᗮ) :
    V.starProjection x = 0 ∧ Q x ∈ (projectionPairSpan V Q)ᗮ ∧
      x - Q x ∈ (projectionPairSpan V Q)ᗮ ∧ Q (Q x) = Q x ∧
      Q (x - Q x) = 0 ∧ inner ℝ (Q x) (x - Q x) = 0 ∧ x = Q x + (x - Q x) := by
  have hqx := projectionPairSpan_orthogonal_invariant V Q hQ hS hx
  refine ⟨(V.starProjection_apply_eq_zero_iff).mpr ?_, hqx,
    (projectionPairSpan V Q)ᗮ.sub_mem hx hqx, hQ x, ?_, ?_, by abel⟩
  · intro v hv
    exact hx v ((show V ≤ projectionPairSpan V Q from le_sup_left) hv)
  · rw [map_sub, hQ, sub_self]
  · rw [hS, map_sub, hQ, sub_self, inner_zero_right]

/-- A finite orthonormal basis spans its ambient submodule after coercion. -/
theorem orthonormalBasis_submodule_le {ι : Type*} [Fintype ι]
    (V S : Submodule ℝ E) (e : OrthonormalBasis ι ℝ V)
    (he : ∀ i, (e i : E) ∈ S) : V ≤ S := by
  intro x hx
  have h := congrArg V.subtype (e.sum_repr ⟨x, hx⟩)
  simp only [map_sum, map_smul, Submodule.subtype_apply] at h
  rw [← h]
  exact S.sum_mem (fun i _ => S.smul_mem _ (he i))

/-- The finite part is exactly the span of the eigenvectors and their companions. -/
theorem projectionPairSpan_eq_companions {ι : Type*} [Fintype ι]
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (e : OrthonormalBasis ι ℝ V) (t : ι → ℝ)
    (hb : ∀ i, 0 ≤ t i ∧ t i ≤ 1)
    (he : ∀ i, projectionCompression V Q (e i) = t i • e i) :
    projectionPairSpan V Q = V ⊔ Submodule.span ℝ
      (Set.range (fun i => projectionCompanion Q (t i) (e i))) := by
  let S := V ⊔ Submodule.span ℝ (Set.range (fun i => projectionCompanion Q (t i) (e i)))
  have hv : V ≤ S := le_sup_left
  have hu (i : ι) : projectionCompanion Q (t i) (e i) ∈ S :=
    (show Submodule.span ℝ _ ≤ S from le_sup_right) (Submodule.subset_span ⟨i, rfl⟩)
  apply le_antisymm
  · apply sup_le hv
    rintro x ⟨v, hv', rfl⟩
    have hm : V ≤ S.comap Q.toLinearMap := by
      apply orthonormalBasis_submodule_le V _ e
      intro i
      change Q (e i) ∈ S
      have ha : Q (e i) = t i • (e i : E) +
          Real.sqrt (t i * (1 - t i)) • projectionCompanion Q (t i) (e i) := by
        rw [projectionCompanion_rescale V Q hQ hS (e i) (e.orthonormal.norm_eq_one i)
          (t i) (hb i).1 (hb i).2 (he i)]
        simp [projectionResidual]
      rw [ha]
      exact S.add_mem (S.smul_mem _ (hv (e i).property)) (S.smul_mem _ (hu i))
    exact hm hv'
  · apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    apply (projectionPairSpan V Q).smul_mem
    apply (projectionPairSpan V Q).sub_mem
    · exact (show V.map Q.toLinearMap ≤ projectionPairSpan V Q from le_sup_right)
        ⟨e i, (e i).property, rfl⟩
    · exact (projectionPairSpan V Q).smul_mem _
        ((show V ≤ projectionPairSpan V Q from le_sup_left) (e i).property)

/-- Companions of the strictly interior eigenvalues form an orthonormal family. -/
theorem projectionCompanions_orthonormal {ι : Type*} [Fintype ι]
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y))
    (e : OrthonormalBasis ι ℝ V) (t : ι → ℝ)
    (he : ∀ i, projectionCompression V Q (e i) = t i • e i) :
    Orthonormal ℝ (fun i : {i // 0 < t i ∧ t i < 1} =>
      projectionCompanion Q (t i) (e i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, real_inner_self_eq_norm_sq,
      projectionCompanion_norm V Q hQ hS (e i) (e.orthonormal.norm_eq_one i)
        (t i) i.property.1 i.property.2 (he i)]
    norm_num
  · rw [if_neg hij]
    exact projectionCompanion_inner_zero V Q hQ hS (e i) (e j) (t i) (t j) (he j)
      (e.orthonormal.inner_eq_zero (fun h => hij (Subtype.ext h)))

/-- The full data of the two-projection decomposition. The first projection is `V.starProjection`.
The finite part consists of the compression eigenvectors and their companions; the orthogonal
remainder can have arbitrary dimension. Interior companions are unit vectors, mutually orthogonal
and perpendicular to all eigenvectors. At endpoints they vanish. -/
structure ProjectionPairDecomposition {ι : Type*} [Fintype ι]
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] (Q : E →L[ℝ] E)
    (e : OrthonormalBasis ι ℝ V) (t : ι → ℝ) : Prop where
  eigenvalues : ∀ i, 0 ≤ t i ∧ t i ≤ 1
  compression : ∀ i, projectionCompression V Q (e i) = t i • e i
  orthonormal_companions : Orthonormal ℝ (fun i : {i // 0 < t i ∧ t i < 1} =>
    projectionCompanion Q (t i) (e i))
  orthogonal_companions : ∀ i, projectionCompanion Q (t i) (e i) ∈ Vᗮ
  first_on_basis : ∀ i, V.starProjection (e i) = (e i : E)
  first_on_companion : ∀ i, V.starProjection (projectionCompanion Q (t i) (e i)) = 0
  plane_action : ∀ i, 0 < t i → t i < 1 →
    Q (e i) = t i • (e i : E) +
      Real.sqrt (t i * (1 - t i)) • projectionCompanion Q (t i) (e i) ∧
    Q (projectionCompanion Q (t i) (e i)) = Real.sqrt (t i * (1 - t i)) • (e i : E) +
      (1 - t i) • projectionCompanion Q (t i) (e i)
  zero_eigenvalue : ∀ i, t i = 0 → Q (e i : E) = 0
  one_eigenvalue : ∀ i, t i = 1 → Q (e i : E) = (e i : E)
  endpoint_companion : ∀ i, t i = 0 ∨ t i = 1 → projectionCompanion Q (t i) (e i) = 0
  finite_span : projectionPairSpan V Q =
    V ⊔ Submodule.span ℝ (Set.range (fun i => projectionCompanion Q (t i) (e i)))
  total_span : projectionPairSpan V Q ⊔ (projectionPairSpan V Q)ᗮ = ⊤
  remainder : ∀ x ∈ (projectionPairSpan V Q)ᗮ,
    V.starProjection x = 0 ∧ Q x ∈ (projectionPairSpan V Q)ᗮ ∧
      x - Q x ∈ (projectionPairSpan V Q)ᗮ ∧ Q (Q x) = Q x ∧
      Q (x - Q x) = 0 ∧ inner ℝ (Q x) (x - Q x) = 0 ∧ x = Q x + (x - Q x)

/-- A finite-rank first projection and any real orthogonal second projection admit the
explicit eigenplane and residual decomposition, including both endpoint eigenspaces. -/
theorem finite_projection_pair_decomposition (V : Submodule ℝ E) [FiniteDimensional ℝ V]
    (Q : E →L[ℝ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) :
    ∃ (e : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V)
      (t : Fin (Module.finrank ℝ V) → ℝ), ProjectionPairDecomposition V Q e t := by
  obtain ⟨e, t, hb, he⟩ := exists_projection_eigenbasis V Q hQ hS
  refine ⟨e, t, ?_⟩
  have ho (i) := projectionCompanion_orthogonal V Q (e i) (t i) (he i)
  refine {
    eigenvalues := hb
    compression := he
    orthonormal_companions := projectionCompanions_orthonormal V Q hQ hS e t he
    orthogonal_companions := ho
    first_on_basis := fun i => Submodule.starProjection_eq_self_iff.mpr (e i).property
    first_on_companion := fun i => (V.starProjection_apply_eq_zero_iff).mpr (ho i)
    plane_action := fun i h0 h1 => projectionCompanion_actions V Q hQ hS (e i)
      (e.orthonormal.norm_eq_one i) (t i) h0 h1 (he i)
    zero_eigenvalue := ?_
    one_eigenvalue := ?_
    endpoint_companion := ?_
    finite_span := projectionPairSpan_eq_companions V Q hQ hS e t hb he
    total_span := ?_
    remainder := fun _ hx => projectionPair_remainder V Q hQ hS hx }
  · intro i hi
    apply projection_eigen_zero V Q hQ hS (e i)
    simpa [hi] using he i
  · intro i hi
    apply projection_eigen_one V Q hQ hS (e i)
    simpa [hi] using he i
  · intro i hi
    rcases hi with h | h <;> simp [projectionCompanion, h]
  · have : FiniteDimensional ℝ (projectionPairSpan V Q) := by
      unfold projectionPairSpan
      infer_instance
    exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- The submodule formulation covers any given finite-rank symmetric idempotent. -/
theorem finite_projection_pair_decomposition_of_maps (F Q : E →L[ℝ] E)
    [FiniteDimensional ℝ (LinearMap.range F.toLinearMap)]
    (hF : ∀ x, F (F x) = F x)
    (hFS : ∀ x y, inner ℝ (F x) y = inner ℝ x (F y))
    (hQ : ∀ x, Q (Q x) = Q x)
    (hQS : ∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) :
    F = (LinearMap.range F.toLinearMap).starProjection ∧
      ∃ (e : OrthonormalBasis (Fin (Module.finrank ℝ (LinearMap.range F.toLinearMap)))
          ℝ (LinearMap.range F.toLinearMap))
        (t : Fin (Module.finrank ℝ (LinearMap.range F.toLinearMap)) → ℝ),
        ProjectionPairDecomposition (LinearMap.range F.toLinearMap) Q e t := by
  have hf : F.toLinearMap.IsSymmetricProjection := ⟨by ext x; exact hF x, hFS⟩
  refine ⟨?_, finite_projection_pair_decomposition _ Q hQ hQS⟩
  obtain ⟨_, heq⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hf
  exact ContinuousLinearMap.coe_injective heq

end SchauderTranslates
