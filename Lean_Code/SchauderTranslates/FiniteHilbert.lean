import Lean_Code.SchauderTranslates.Contracts

noncomputable section
open scoped Topology InnerProductSpace

namespace SchauderTranslates

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def invariantRestriction (P : H →L[ℂ] H) (S : Submodule ℂ H)
    (hS : ∀ x ∈ S, P x ∈ S) : S →L[ℂ] S :=
  (P.comp S.subtypeL).codRestrict S (fun x => hS x x.property)

@[simp] theorem invariantRestriction_apply (P : H →L[ℂ] H) (S : Submodule ℂ H)
    (hS : ∀ x ∈ S, P x ∈ S) (x : S) :
    (invariantRestriction P S hS x : H) = P x := rfl

theorem invariantRestriction_norm_le (P : H →L[ℂ] H) (S : Submodule ℂ H)
    (hS : ∀ x ∈ S, P x ∈ S) : ‖invariantRestriction P S hS‖ ≤ ‖P‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg P)
  intro x
  exact P.le_opNorm x

def invariantQuotient (P : H →L[ℂ] H) (F : Submodule ℂ H)
    (hF : ∀ x ∈ F, P x ∈ F) : (H ⧸ F) →L[ℂ] (H ⧸ F) :=
  F.liftQL (F.mkQL.comp P) (by
    intro x hx
    change (Submodule.Quotient.mk (P x) : H ⧸ F) = 0
    simpa using (Submodule.Quotient.eq F).mpr (show P x - 0 ∈ F by simpa using hF x hx))

@[simp] theorem invariantQuotient_mk (P : H →L[ℂ] H) (F : Submodule ℂ H)
    (hF : ∀ x ∈ F, P x ∈ F) (x : H) :
    invariantQuotient P F hF (Submodule.Quotient.mk x) = Submodule.Quotient.mk (P x) := rfl

theorem invariantQuotient_norm_le (P : H →L[ℂ] H) (F : Submodule ℂ H)
    (hF : ∀ x ∈ F, P x ∈ F) : ‖invariantQuotient P F hF‖ ≤ ‖P‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg P)
  intro q
  apply le_of_forall_pos_le_add
  intro ε hε
  have hd : 0 < ‖P‖ + 1 := by positivity
  obtain ⟨x, hx, hnorm⟩ := Submodule.Quotient.norm_mk_lt q (div_pos hε hd)
  have hε' : ‖P‖ * (ε / (‖P‖ + 1)) ≤ ε := by
    have he := mul_le_mul_of_nonneg_right
      (show ‖P‖ ≤ ‖P‖ + 1 by linarith) (div_pos hε hd).le
    simpa only [mul_div_cancel₀ _ hd.ne'] using he
  calc
    ‖invariantQuotient P F hF q‖ = ‖(Submodule.Quotient.mk (P x) : H ⧸ F)‖ := by
      rw [← hx, invariantQuotient_mk]
    _ ≤ ‖P x‖ := Submodule.Quotient.norm_mk_le _ _
    _ ≤ ‖P‖ * ‖x‖ := P.le_opNorm x
    _ ≤ ‖P‖ * (‖q‖ + ε / (‖P‖ + 1)) :=
      mul_le_mul_of_nonneg_left hnorm.le (norm_nonneg P)
    _ ≤ ‖P‖ * ‖q‖ + ε := by nlinarith

theorem invariantRestriction_idempotent (P : H →L[ℂ] H)
    (hP : ∀ x, P (P x) = P x) (S : Submodule ℂ H) (hS : ∀ x ∈ S, P x ∈ S) :
    ∀ x, invariantRestriction P S hS (invariantRestriction P S hS x) =
      invariantRestriction P S hS x := by
  intro x
  exact Subtype.ext (hP x)

theorem invariantQuotient_idempotent (P : H →L[ℂ] H)
    (hP : ∀ x, P (P x) = P x) (F : Submodule ℂ H) (hF : ∀ x ∈ F, P x ∈ F) :
    ∀ x, invariantQuotient P F hF (invariantQuotient P F hF x) =
      invariantQuotient P F hF x := by
  intro q
  induction q using Submodule.Quotient.induction_on F with
  | H x => simp only [invariantQuotient_mk, hP]

/-- Restricting and then quotienting an invariant subspace cannot increase a prefix bound. -/
theorem prefix_restrict_quotient (P : H →L[ℂ] H)
    (S : Submodule ℂ H) (hS : ∀ x ∈ S, P x ∈ S)
    (F : Submodule ℂ S)
    (hF : ∀ x ∈ F, invariantRestriction P S hS x ∈ F) :
    ‖invariantRestriction P S hS‖ ≤ ‖P‖ ∧
    ‖invariantQuotient (invariantRestriction P S hS) F hF‖ ≤ ‖P‖ :=
  ⟨invariantRestriction_norm_le P S hS,
    (invariantQuotient_norm_le _ F hF).trans (invariantRestriction_norm_le P S hS)⟩

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : Submodule ℂ E) [F.HasOrthogonalProjection]

/-- The quotient representative is exactly the orthogonal remainder used for centering. -/
theorem quotientEquivOrthogonal_remainder (x : E) :
    F.quotientEquivOrthogonal (Submodule.Quotient.mk x) =
      ⟨x - F.starProjection x, F.sub_starProjection_mem_orthogonal x⟩ := by
  have hq : (Submodule.Quotient.mk x : E ⧸ F) =
      Submodule.Quotient.mk (x - F.starProjection x) := by
    apply (Submodule.Quotient.eq F).mpr
    simpa only [sub_sub_cancel] using F.starProjection_apply_mem x
  rw [hq, F.quotientEquivOrthogonal_mk _ (F.sub_starProjection_mem_orthogonal x)]

end Hilbert
end SchauderTranslates
