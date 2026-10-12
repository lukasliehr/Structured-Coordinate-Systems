import Lean_Code.SchauderTranslates.FiniteHilbert
import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Quotienting an invariant subspace bounds the norm of the actual orthogonal representatives. -/
theorem centeredProjection_norm_le (P : H →L[ℂ] H) (F : Submodule ℂ H) [F.HasOrthogonalProjection]
    (hF : ∀ x ∈ F, P x ∈ F) (z : H) :
    ‖Fᗮ.starProjection (P z)‖ ≤ ‖P‖ * ‖Fᗮ.starProjection z‖ := by
  have hz : Fᗮ.starProjection (P (F.starProjection z)) = 0 :=
    F.starProjection_orthogonal_apply_eq_zero (hF _ (F.starProjection_apply_mem z))
  have he : Fᗮ.starProjection (P (Fᗮ.starProjection z)) = Fᗮ.starProjection (P z) := by
    rw [F.starProjection_orthogonal_val z, map_sub, map_sub, hz, sub_zero]
  calc
    _ = ‖Fᗮ.starProjection (P (Fᗮ.starProjection z))‖ := congrArg norm he.symm
    _ ≤ ‖P (Fᗮ.starProjection z)‖ := Fᗮ.norm_starProjection_apply_le _
    _ ≤ _ := P.le_opNorm _

/-- Centered synthesis inherits a diagonal coefficient operator bound from the original vectors. -/
theorem centeredSynthesis_norm_sq_le {ι : Type*} [Fintype ι]
    (P : H →L[ℂ] H) (F : Submodule ℂ H) [F.HasOrthogonalProjection]
    (hF : ∀ x ∈ F, P x ∈ F) (u : ι → H) (δ c : ι → ℂ)
    (hu : ∀ i, P (u i) = δ i • u i) :
    ‖finiteSynthesis (fun i => Fᗮ.starProjection (u i)) (fun i => δ i * c i)‖ ^ 2 ≤
      ‖P‖ ^ 2 * ‖finiteSynthesis (fun i => Fᗮ.starProjection (u i)) c‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (centeredProjection_norm_le P F hF (finiteSynthesis u c)) 2
  have h1 : Fᗮ.starProjection (P (finiteSynthesis u c)) =
      finiteSynthesis (fun i => Fᗮ.starProjection (u i)) (fun i => δ i * c i) := by
    simp [finiteSynthesis, hu, smul_smul, mul_comm]
  have h2 : Fᗮ.starProjection (finiteSynthesis u c) =
      finiteSynthesis (fun i => Fᗮ.starProjection (u i)) c := by simp [finiteSynthesis]
  simpa only [h1, h2, mul_pow] using h

/-- The Gram after centering is the Schur complement of the distinguished vector. -/
theorem orthogonal_centering_inner (v x y : H) :
    inner ℂ ((ℂ ∙ v)ᗮ.starProjection x) ((ℂ ∙ v)ᗮ.starProjection y) =
      inner ℂ x y - (inner ℂ v y / ((‖v‖ ^ 2 : ℝ) : ℂ)) * inner ℂ x v := by
  let F := ℂ ∙ v
  have he : Fᗮ.starProjection (Fᗮ.starProjection y) = Fᗮ.starProjection y :=
    Submodule.starProjection_eq_self_iff.mpr (Fᗮ.starProjection_apply_mem y)
  change inner ℂ (Fᗮ.starProjection x) (Fᗮ.starProjection y) = _
  rw [Fᗮ.inner_starProjection_left_eq_right, he, F.starProjection_orthogonal_val,
    inner_sub_right, Submodule.starProjection_singleton, inner_smul_right]
  rfl

end SchauderTranslates
