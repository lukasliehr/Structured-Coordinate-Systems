import Mathlib

noncomputable section
open scoped InnerProductSpace InnerProduct

namespace SchauderTranslates

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Squared operator bounds can be verified on vectors, using the Hilbert norm. -/
theorem opNorm_sq_le_of_pointwise (A : E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, ‖A x‖ ^ 2 ≤ C * ‖x‖ ^ 2) : ‖A‖ ^ 2 ≤ C := by
  have hA : ‖A‖ ≤ Real.sqrt C := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro x
    have hs := Real.sq_sqrt hC
    have hx := h x
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, hs] using hx
  nlinarith [norm_nonneg A, Real.sqrt_nonneg C, Real.sq_sqrt hC]

/-- An isometric coordinate plus another coordinate gives the exact column norm. -/
theorem opNorm_sq_eq_one_add_of_pointwise [Nontrivial E]
    (A : E →L[𝕜] F) (B : E →L[𝕜] G)
    (h : ∀ x, ‖A x‖ ^ 2 = ‖x‖ ^ 2 + ‖B x‖ ^ 2) :
    ‖A‖ ^ 2 = 1 + ‖B‖ ^ 2 := by
  have hup : ‖A‖ ^ 2 ≤ 1 + ‖B‖ ^ 2 := by
    apply opNorm_sq_le_of_pointwise A (by positivity)
    intro x
    have hb := B.le_opNorm x
    have hb2 : ‖B x‖ ^ 2 ≤ (‖B‖ * ‖x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [h x]
    nlinarith
  have hge : 1 ≤ ‖A‖ ^ 2 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    have ha := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm x) 2
    have hh := h x
    nlinarith [sq_nonneg ‖B x‖]
  have hlow : ‖B‖ ^ 2 ≤ ‖A‖ ^ 2 - 1 := by
    apply opNorm_sq_le_of_pointwise B (by linarith)
    intro x
    have ha := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm x) 2
    have hh := h x
    nlinarith
  linarith

/-- The Hilbert column `x ↦ (x, Bx)`. -/
def hilbertColumn (B : E →L[𝕜] F) : E →L[𝕜] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 𝕜 E F).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id 𝕜 E).prod B)

@[simp] theorem hilbertColumn_apply (B : E →L[𝕜] F) (x : E) :
    hilbertColumn B x = WithLp.toLp 2 (x, B x) := rfl

theorem hilbertColumn_norm_sq [Nontrivial E] (B : E →L[𝕜] F) :
    ‖hilbertColumn B‖ ^ 2 = 1 + ‖B‖ ^ 2 := by
  apply opNorm_sq_eq_one_add_of_pointwise _ B
  intro x
  exact WithLp.prod_norm_sq_eq_of_L2 _

/-- The Hilbert row `(x,y) ↦ x + Zy`. -/
def hilbertRow (Z : F →L[𝕜] E) : WithLp 2 (E × F) →L[𝕜] E :=
  WithLp.fstL 2 𝕜 E F + Z.comp (WithLp.sndL 2 𝕜 E F)

@[simp] theorem hilbertRow_apply (Z : F →L[𝕜] E) (x : WithLp 2 (E × F)) :
    hilbertRow Z x = x.fst + Z x.snd := rfl

section Complete
variable [CompleteSpace E] [CompleteSpace F]

theorem hilbertRow_adjoint (Z : F →L[𝕜] E) :
    (hilbertRow Z)† = hilbertColumn (Z†) := by
  ext x
  apply ext_inner_right 𝕜
  intro y
  simp [ContinuousLinearMap.adjoint_inner_left, WithLp.prod_inner_apply,
    hilbertRow_apply, inner_add_right]

theorem hilbertRow_norm_sq [Nontrivial E] (Z : F →L[𝕜] E) :
    ‖hilbertRow Z‖ ^ 2 = 1 + ‖Z‖ ^ 2 := by
  have h := hilbertColumn_norm_sq (Z†)
  rw [← hilbertRow_adjoint] at h
  simpa using h

/-- The block projection with matrix `[[1,Z],[0,0]]`. -/
def hilbertBlockProjection (Z : F →L[𝕜] E) :
    WithLp 2 (E × F) →L[𝕜] WithLp 2 (E × F) :=
  (hilbertColumn (0 : E →L[𝕜] F)).comp (hilbertRow Z)

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem hilbertBlockProjection_apply (Z : F →L[𝕜] E)
    (x : WithLp 2 (E × F)) :
    hilbertBlockProjection Z x = WithLp.toLp 2 (x.fst + Z x.snd, 0) := rfl

theorem hilbertBlockProjection_adjoint_apply (Z : F →L[𝕜] E)
    (x : WithLp 2 (E × F)) :
    ((hilbertBlockProjection Z)†) x = WithLp.toLp 2 (x.fst, (Z†) x.fst) := by
  apply ext_inner_right 𝕜
  intro y
  simp [ContinuousLinearMap.adjoint_inner_left, WithLp.prod_inner_apply,
    inner_add_right]

theorem hilbertBlockProjection_norm_sq [Nontrivial E] (Z : F →L[𝕜] E) :
    ‖hilbertBlockProjection Z‖ ^ 2 = 1 + ‖Z‖ ^ 2 := by
  have h : ‖hilbertBlockProjection Z‖ = ‖hilbertRow Z‖ := by
    apply ContinuousLinearMap.opNorm_ext
    intro x
    exact WithLp.norm_toLp_fst 2 E F _
  rw [h, hilbertRow_norm_sq]

theorem hilbertBlockProjection_skew_apply (Z : F →L[𝕜] E)
    (x : WithLp 2 (E × F)) :
    (hilbertBlockProjection Z - (hilbertBlockProjection Z)†) x =
      WithLp.toLp 2 (Z x.snd, -(Z†) x.fst) := by
  simp only [sub_apply, hilbertBlockProjection_apply,
    hilbertBlockProjection_adjoint_apply]
  apply (WithLp.equiv 2 (E × F)).injective
  ext <;> simp

theorem hilbertBlockProjection_skew_norm (Z : F →L[𝕜] E) :
    ‖hilbertBlockProjection Z - (hilbertBlockProjection Z)†‖ = ‖Z‖ := by
  let S := hilbertBlockProjection Z - (hilbertBlockProjection Z)†
  have hs (x : WithLp 2 (E × F)) :
      ‖S x‖ ^ 2 = ‖Z x.snd‖ ^ 2 + ‖(Z†) x.fst‖ ^ 2 := by
    rw [show S x = WithLp.toLp 2 (Z x.snd, -(Z†) x.fst) from
      hilbertBlockProjection_skew_apply Z x, WithLp.prod_norm_sq_eq_of_L2]
    simp
  apply le_antisymm
  · have hup : ‖S‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
      apply opNorm_sq_le_of_pointwise S (sq_nonneg _)
      intro x
      have hy := pow_le_pow_left₀ (norm_nonneg _) (Z.le_opNorm x.snd) 2
      have hx := pow_le_pow_left₀ (norm_nonneg _) ((Z†).le_opNorm x.fst) 2
      simp only [LinearIsometryEquiv.norm_map] at hx
      rw [hs, WithLp.prod_norm_sq_eq_of_L2]
      nlinarith
    exact (sq_le_sq₀ (norm_nonneg S) (norm_nonneg Z)).mp hup
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S)
    intro y
    have hy := S.le_opNorm (WithLp.toLp 2 ((0 : E), y))
    change ‖(hilbertBlockProjection Z - (hilbertBlockProjection Z)†) _‖ ≤ _ at hy
    rw [hilbertBlockProjection_skew_apply] at hy
    simpa [WithLp.norm_toLp_fst, WithLp.norm_toLp_snd] using hy

end Complete

section Conjugation
variable [CompleteSpace E] [CompleteSpace F]

theorem hilbertConjugate_norm_le (e : E ≃ₗᵢ[𝕜] F) (A : E →L[𝕜] E) :
    ‖e.conjStarAlgEquiv A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simpa using A.le_opNorm (e.symm x)

theorem hilbertConjugate_norm (e : E ≃ₗᵢ[𝕜] F) (A : E →L[𝕜] E) :
    ‖e.conjStarAlgEquiv A‖ = ‖A‖ := by
  apply le_antisymm (hilbertConjugate_norm_le e A)
  simpa only [← LinearIsometryEquiv.symm_conjStarAlgEquiv,
    StarAlgEquiv.symm_apply_apply] using
    hilbertConjugate_norm_le e.symm (e.conjStarAlgEquiv A)

theorem hilbertConjugate_adjoint (e : E ≃ₗᵢ[𝕜] F) (A : E →L[𝕜] E) :
    e.conjStarAlgEquiv (A†) = (e.conjStarAlgEquiv A)† := by
  exact map_star e.conjStarAlgEquiv A

end Conjugation
end SchauderTranslates
