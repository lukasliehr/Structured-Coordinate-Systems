import Lean_Code.SchauderTranslates.HilbertSynthesis

noncomputable section
open Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The finite atom span is closed, including for an empty list. -/
def atomSpan (u : ι → H) : Submodule ℂ H := Submodule.span ℂ (Set.range u)
instance atomSpan_finite (u : ι → H) : FiniteDimensional ℂ (atomSpan u) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range u)

theorem gramProjection_eq_starProjection (u : ι → H) (hu : LinearIndependent ℂ u) :
    ∀ f, (atomSpan u).starProjection f = gramProjection u f := by
  intro f
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
    exact ⟨_, rfl⟩
  · intro w hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
    exact inner_eq_zero_symm.mpr (gramProjection_orthogonal u hu f c)

/-- The finite normal-equation formula is the actual orthogonal projection, as a bounded operator. -/
theorem atomSpan_projection_formula (u : ι → H) (hu : LinearIndependent ℂ u) :
    (atomSpan u).starProjection =
      (hilbertSynthesis u).comp (((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (Matrix.gram ℂ u)⁻¹).comp ((hilbertSynthesis u)†)) := by
  ext f
  rw [gramProjection_eq_starProjection u hu]
  change gramProjection u f = hilbertSynthesis u (((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)) (Matrix.gram ℂ u)⁻¹) (((hilbertSynthesis u)†) f))
  rw [hilbertSynthesis_adjoint_apply]
  simp only [gramProjection, hilbertSynthesis_apply, finiteSynthesis, sourceMoments, Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_toLp]
  rfl

variable (F : Submodule ℂ H) [F.HasOrthogonalProjection]

def atomMeans (u : ι → H) : ι → H := fun i => F.starProjection (u i)
def centeredAtoms (u : ι → H) : ι → H := fun i => Fᗮ.starProjection (u i)

/-- Orthogonal centering gives the exact Gram sum, with the mathlib inner-product convention. -/
theorem centered_gram_sum (u : ι → H) :
    Matrix.gram ℂ u = Matrix.gram ℂ (centeredAtoms F u) + Matrix.gram ℂ (atomMeans F u) := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.add_apply, centeredAtoms, atomMeans]
  rw [Fᗮ.inner_starProjection_left_eq_right,
    show Fᗮ.starProjection (Fᗮ.starProjection (u j)) = Fᗮ.starProjection (u j) by exact Submodule.starProjection_eq_self_iff.mpr (Fᗮ.starProjection_apply_mem _),
    F.inner_starProjection_left_eq_right,
    show F.starProjection (F.starProjection (u j)) = F.starProjection (u j) by exact Submodule.starProjection_eq_self_iff.mpr (F.starProjection_apply_mem _),
    F.starProjection_orthogonal_val, inner_sub_right]
  ring

theorem centered_posDef_implies_independent (u : ι → H)
    (hC : (Matrix.gram ℂ (centeredAtoms F u)).PosDef) : LinearIndependent ℂ u := by
  apply Matrix.linearIndependent_of_posDef_gram
  rw [centered_gram_sum F u]
  exact hC.add_posSemidef (Matrix.posSemidef_gram ℂ _)

theorem atomMeans_synthesis (u : ι → H) :
    hilbertSynthesis (atomMeans F u) = F.starProjection.comp (hilbertSynthesis u) := by
  ext c
  simp [atomMeans, hilbertSynthesis_apply]

theorem atomMeans_synthesis_adjoint (u : ι → H) :
    (hilbertSynthesis (atomMeans F u))† = ((hilbertSynthesis u)†).comp F.starProjection := by
  rw [atomMeans_synthesis, adjoint_comp]
  congr 1
  exact (isSelfAdjoint_starProjection F).adjoint_eq

end SchauderTranslates
