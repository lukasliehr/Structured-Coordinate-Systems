import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {𝕜 ι H : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Finite synthesis from Euclidean coefficient space into a Hilbert space. -/
def hilbertSynthesis (u : ι → H) : EuclideanSpace 𝕜 ι →L[𝕜] H :=
  (show EuclideanSpace 𝕜 ι →ₗ[𝕜] H from
    { toFun := fun c => ∑ i, c i • u i
      map_add' := by intro c d; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro a c; simp [Finset.smul_sum, smul_smul] }).toContinuousLinearMap

omit [DecidableEq ι] in
@[simp] theorem hilbertSynthesis_apply (u : ι → H) (c : EuclideanSpace 𝕜 ι) :
    hilbertSynthesis u c = ∑ i, c i • u i := rfl

/-- Biorthogonal columns define the corresponding finite coordinate projection. -/
theorem biorthogonal_rankOne_idempotent (u v : ι → H)
    (hbi : ∀ i j, inner 𝕜 (v i) (u j) = if i = j then 1 else 0) :
    ∀ z, (∑ i, rankOne 𝕜 (u i) (v i)) ((∑ i, rankOne 𝕜 (u i) (v i)) z) =
      (∑ i, rankOne 𝕜 (u i) (v i)) z := by
  let P := ∑ i, rankOne 𝕜 (u i) (v i)
  have hval (z : H) : P z = ∑ i, inner 𝕜 (v i) z • u i := by
    simp [P, rankOne_apply]
  have hfix (i : ι) : P (u i) = u i := by simp [hval, hbi]
  intro z
  change P (P z) = P z
  rw [hval z, map_sum]
  simp only [map_smul, hfix]

section Complete
variable [CompleteSpace H]

omit [DecidableEq ι] in
theorem hilbertSynthesis_adjoint_apply (u : ι → H) (z : H) :
    ((hilbertSynthesis u)†) z = WithLp.toLp 2 (fun i => inner 𝕜 (u i) z) := by
  apply ext_inner_right 𝕜
  intro c
  rw [adjoint_inner_left]
  simp [hilbertSynthesis_apply, PiLp.inner_apply, RCLike.inner_apply,
    inner_conj_symm, inner_sum, inner_smul_right, mul_comm]

omit [DecidableEq ι] in
theorem hilbertSynthesis_cross (u v : ι → H) :
    (hilbertSynthesis u).comp ((hilbertSynthesis v)†) = ∑ i, rankOne 𝕜 (u i) (v i) := by
  ext z
  simp [hilbertSynthesis_adjoint_apply, rankOne_apply]

theorem hilbertSynthesis_gram (u : ι → H) :
    ((hilbertSynthesis u)†).comp (hilbertSynthesis u) =
      (Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (Matrix.gram 𝕜 u) := by
  ext c i
  simp [hilbertSynthesis_adjoint_apply, hilbertSynthesis_apply,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, mul_comm]

set_option maxHeartbeats 400000 in
/-- Gram formula for a finite sum of rank-one maps. -/
theorem sum_rankOne_norm_sq (u v : ι → H) :
    ‖∑ i, rankOne 𝕜 (u i) (v i)‖ ^ 2 =
      ‖(gramRoot (Matrix.gram 𝕜 u)).comp
        (((Matrix.toEuclideanCLM (𝕜 := 𝕜) (n := ι)) (Matrix.gram 𝕜 v)).comp
          (gramRoot (Matrix.gram 𝕜 u)))‖ := by
  let X : EuclideanSpace 𝕜 ι →L[𝕜] H := hilbertSynthesis u
  let Y : EuclideanSpace 𝕜 ι →L[𝕜] H := hilbertSynthesis v
  let S := gramRoot (Matrix.gram 𝕜 u)
  have hS : S.comp S = (X†).comp X :=
    (gramRoot_square (Matrix.posSemidef_gram 𝕜 u)).trans
      (hilbertSynthesis_gram (𝕜 := 𝕜) u).symm
  have hself : S† = S := gramRoot_adjoint (Matrix.gram 𝕜 u)
  have hn := selected_gram_norm X Y S hself hS
  have htail : S.comp ((Y†).comp (Y.comp S)) = S.comp (((Y†).comp Y).comp S) :=
    congrArg (fun A => S.comp A) (comp_assoc (Y†) Y S).symm
  rw [htail, hilbertSynthesis_gram, hilbertSynthesis_cross] at hn
  exact hn

end Complete
end SchauderTranslates
