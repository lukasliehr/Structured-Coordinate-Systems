import Lean_Code.SchauderTranslates.SkewDecomposition

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Appending a scaled vector as one real column of a Hilbert row. -/
def extendedHilbertRow (Z : F →L[ℝ] E) (b : E) (s : ℝ) : WithLp 2 (F × ℝ) →L[ℝ] E :=
  Z.comp (WithLp.fstL 2 ℝ F ℝ) +
    (s • toSpanSingleton ℝ b).comp (WithLp.sndL 2 ℝ F ℝ)

@[simp] theorem extendedHilbertRow_apply (Z : F →L[ℝ] E) (b : E) (s : ℝ)
    (x : WithLp 2 (F × ℝ)) :
    extendedHilbertRow Z b s x = Z x.fst + (s * x.snd) • b := by
  simp [extendedHilbertRow, smul_smul]

section Complete
variable [CompleteSpace E] [CompleteSpace F]

theorem extendedHilbertRow_adjoint_apply (Z : F →L[ℝ] E) (b : E) (s : ℝ) (x : E) :
    ((extendedHilbertRow Z b s)†) x =
      WithLp.toLp 2 ((Z†) x, s * inner ℝ b x) := by
  apply ext_inner_right ℝ
  intro y
  rw [adjoint_inner_left]
  simp only [extendedHilbertRow_apply, inner_add_right, real_inner_smul_right,
    WithLp.prod_inner_apply, adjoint_inner_left, Real.inner_apply]
  rw [real_inner_comm b x]
  change inner ℝ x (Z y.fst) + s * y.snd * inner ℝ b x =
    inner ℝ x (Z y.fst) + (s * inner ℝ b x) * y.snd
  ring

theorem extendedHilbertRow_mul_adjoint (Z : F →L[ℝ] E) (b : E) (s : ℝ) :
    (extendedHilbertRow Z b s).comp ((extendedHilbertRow Z b s)†) =
      Z.comp (Z†) + s ^ 2 • rankOne ℝ b b := by
  ext x
  simp [extendedHilbertRow_adjoint_apply, extendedHilbertRow_apply, rankOne_apply,
    smul_smul, pow_two, mul_assoc]

theorem extendedHilbertRow_norm_sq (Z : F →L[ℝ] E) (b : E) (s : ℝ) :
    ‖extendedHilbertRow Z b s‖ ^ 2 = ‖Z.comp (Z†) + s ^ 2 • rankOne ℝ b b‖ := by
  have h := norm_adjoint_comp_self ((extendedHilbertRow Z b s)†)
  rw [adjoint_adjoint, extendedHilbertRow_mul_adjoint] at h
  simpa only [LinearIsometryEquiv.norm_map, pow_two] using h.symm

theorem extendedHilbertRow_growth (Z : F →L[ℝ] E) (b : E) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    ‖extendedHilbertRow Z b s‖ ^ 2 ≤ ‖extendedHilbertRow Z b r‖ ^ 2 +
      (s ^ 2 - r ^ 2) * ‖b‖ ^ 2 := by
  have hdiff : 0 ≤ s ^ 2 - r ^ 2 := sub_nonneg.mpr (pow_le_pow_left₀ hr hrs 2)
  rw [extendedHilbertRow_norm_sq, extendedHilbertRow_norm_sq]
  have he : Z.comp (Z†) + s ^ 2 • rankOne ℝ b b =
      (Z.comp (Z†) + r ^ 2 • rankOne ℝ b b) +
        (s ^ 2 - r ^ 2) • rankOne ℝ b b := by
    module
  rw [he]
  calc
    _ ≤ ‖Z.comp (Z†) + r ^ 2 • rankOne ℝ b b‖ +
        ‖(s ^ 2 - r ^ 2) • rankOne ℝ b b‖ := norm_add_le _ _
    _ = _ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff, norm_rankOne]
      ring

end Complete

/-- The real skew arrowhead `(x,c) ↦ (Jx + scb, -s⟨b,x⟩)`. -/
def skewArrowhead (J : E →L[ℝ] E) (b : E) (s : ℝ) :
    WithLp 2 (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.toContinuousLinearMap.comp
    ((J.comp (WithLp.fstL 2 ℝ E ℝ) +
      (s • toSpanSingleton ℝ b).comp (WithLp.sndL 2 ℝ E ℝ)).prod
      ((-s • innerSL ℝ b).comp (WithLp.fstL 2 ℝ E ℝ)))

@[simp] theorem skewArrowhead_apply (J : E →L[ℝ] E) (b : E) (s : ℝ)
    (x : WithLp 2 (E × ℝ)) :
    skewArrowhead J b s x = WithLp.toLp 2
      (J x.fst + (s * x.snd) • b, -s * inner ℝ b x.fst) := by
  simp [skewArrowhead, smul_smul]

section Conjugation
variable [CompleteSpace E] [CompleteSpace F]

theorem skewArrowhead_conjugate (e : E ≃ₗᵢ[ℝ] F) (J : E →L[ℝ] E) (b : E) (s : ℝ) :
    (LinearIsometryEquiv.withLpProdCongr 2 e (LinearIsometryEquiv.refl ℝ ℝ)).conjStarAlgEquiv
      (skewArrowhead J b s) = skewArrowhead (e.conjStarAlgEquiv J) (e b) s := by
  ext x
  have hi : inner ℝ b (e.symm x.fst) = inner ℝ (e b) x.fst := by
    rw [← e.inner_map_map, e.apply_symm_apply]
  simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.withLpProdCongr_apply, LinearIsometryEquiv.withLpProdCongr_symm_apply,
    skewArrowhead_apply, map_add, map_smul, hi]
  rfl

theorem skewArrowhead_block_conjugate (Z : F →L[ℝ] E) (b : E) (s : ℝ) :
    (LinearIsometryEquiv.withLpProdAssoc 2 ℝ E F ℝ).conjStarAlgEquiv
      (skewArrowhead (hilbertBlockProjection Z - (hilbertBlockProjection Z)†)
        (WithLp.toLp 2 (b, (0 : F))) s) =
      hilbertBlockProjection (extendedHilbertRow Z b s) -
        (hilbertBlockProjection (extendedHilbertRow Z b s))† := by
  ext x
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.withLpProdAssoc_symm_apply, skewArrowhead_apply,
    hilbertBlockProjection_skew_apply, extendedHilbertRow_apply,
    extendedHilbertRow_adjoint_apply, LinearIsometryEquiv.withLpProdAssoc_apply,
    WithLp.prod_inner_apply]
  apply (WithLp.equiv 2 (E × WithLp 2 (F × ℝ))).injective
  ext <;> simp [neg_mul]
  rfl

/-- The arrowhead norm is the norm of one extended rectangular row. -/
theorem skewArrowhead_norm_as_row [FiniteDimensional ℝ E]
    (J : E →L[ℝ] E) (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y)) (b : E) :
    ∃ (S : Submodule ℝ E) (hb : b ∈ S) (Z : Sᗮ →L[ℝ] S),
      ∀ s : ℝ, ‖skewArrowhead J b s‖ = ‖extendedHilbertRow Z ⟨b, hb⟩ s‖ := by
  obtain ⟨S, hb, Z, hZ⟩ := skew_normal_form_with_vector J hJ b
  refine ⟨S, hb, Z, fun s => ?_⟩
  let e := S.orthogonalDecomposition
  have heb : e b = WithLp.toLp 2 ((⟨b, hb⟩ : S), (0 : Sᗮ)) := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change b = S.orthogonalDecomposition.symm (WithLp.toLp 2 ((⟨b, hb⟩ : S), (0 : Sᗮ)))
    simp [Submodule.orthogonalDecomposition_symm_apply]
  calc
    ‖skewArrowhead J b s‖ =
        ‖skewArrowhead (e.conjStarAlgEquiv J) (e b) s‖ := by
      rw [← skewArrowhead_conjugate, hilbertConjugate_norm]
    _ = ‖skewArrowhead (hilbertBlockProjection Z - (hilbertBlockProjection Z)†)
        (WithLp.toLp 2 ((⟨b, hb⟩ : S), (0 : Sᗮ))) s‖ := by rw [hZ, heb]
    _ = ‖hilbertBlockProjection (extendedHilbertRow Z ⟨b, hb⟩ s) -
        (hilbertBlockProjection (extendedHilbertRow Z ⟨b, hb⟩ s))†‖ := by
      rw [← skewArrowhead_block_conjugate, hilbertConjugate_norm]
    _ = ‖extendedHilbertRow Z ⟨b, hb⟩ s‖ := hilbertBlockProjection_skew_norm _

end Conjugation

/-- Enlarging a real skew arrowhead has at most the rank-one squared norm cost. -/
theorem skew_arrowhead_bound [CompleteSpace E] [FiniteDimensional ℝ E]
    (J : E →L[ℝ] E) (hJ : ∀ x y, inner ℝ (J x) y = -inner ℝ x (J y))
    (b : E) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    ‖skewArrowhead J b s‖ ^ 2 ≤ ‖skewArrowhead J b r‖ ^ 2 +
      (s ^ 2 - r ^ 2) * ‖b‖ ^ 2 := by
  obtain ⟨S, hb, Z, he⟩ := skewArrowhead_norm_as_row J hJ b
  rw [he s, he r]
  exact extendedHilbertRow_growth Z ⟨b, hb⟩ hr hrs

end SchauderTranslates
