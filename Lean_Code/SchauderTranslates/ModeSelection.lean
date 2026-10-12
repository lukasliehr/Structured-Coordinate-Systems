import Lean_Code.SchauderTranslates.ProjectionRowBound

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ν K : Type*} [Fintype ν] [DecidableEq ν]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Real span of a finite selected set of spatial modes. -/
def modeSelectionSpace (u : ν → K) (s : Finset ν) : Submodule ℝ K :=
  Submodule.span ℝ (Set.range (fun a : s => u a))

instance modeSelectionSpace_finiteDimensional (u : ν → K) (s : Finset ν) :
    FiniteDimensional ℝ (modeSelectionSpace u s) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- Projection onto selected orthonormal modes acts as the exact coordinate mask. -/
theorem modeSelectionSpace_apply {u : ν → K} (hu : Orthonormal ℝ u) (s : Finset ν) (a : ν) :
    (modeSelectionSpace u s).starProjection (u a) = if a ∈ s then u a else 0 := by
  by_cases ha : a ∈ s
  · rw [if_pos ha]
    apply Submodule.starProjection_eq_self_iff.mpr
    exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  · rw [if_neg ha]
    apply ((modeSelectionSpace u s).starProjection_apply_eq_zero_iff).mpr
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact hu.inner_eq_zero (fun h => ha (h ▸ b.property))
    | zero => simp
    | add x y hx hy hix hiy => simp [inner_add_left, hix, hiy]
    | smul c x hx hix => simp [real_inner_smul_left, hix]

end SchauderTranslates
