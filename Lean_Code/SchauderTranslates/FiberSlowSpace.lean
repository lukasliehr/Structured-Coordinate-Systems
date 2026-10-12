import Lean_Code.SchauderTranslates.FiberSlowLift
import Lean_Code.SchauderTranslates.FiberMeanProjection
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Bounded measurable representatives are dense in the full L² space, with no regularity assumption on the measure. -/
theorem boundedMeasurable_toL2_dense {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsFiniteMeasure ρ] :
    DenseRange (fun f : BoundedMeasurableComplex S => f.toL2 ρ) := by
  apply (Lp.simpleFunc.denseRange (E := ℂ) (μ := ρ) (p := 2) (by norm_num)).mono
  rintro z ⟨f, rfl⟩
  obtain ⟨B, hB⟩ := (Lp.simpleFunc.toSimpleFunc f).exists_forall_norm_le
  let g : BoundedMeasurableComplex S := {
    toFun := Lp.simpleFunc.toSimpleFunc f
    measurable := (Lp.simpleFunc.toSimpleFunc f).measurable
    bound := max B 0
    bound_nonneg := le_max_right _ _
    norm_le := fun x => (hB x).trans (le_max_left _ _) }
  refine ⟨g, ?_⟩
  apply Lp.ext
  exact (g.toL2_ae ρ).trans (Lp.simpleFunc.toSimpleFunc_eq_toFun f)

namespace FiberKernel
variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν] (K : FiberKernel S Y ν)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- The completed bounded slow space is exactly the image of all of L² of the slow marginal. -/
theorem slowSpace_eq_range : K.slowSpace ρ = (K.slowLift ρ).toLinearMap.range := by
  apply le_antisymm
  · unfold slowSpace
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro z ⟨f, rfl⟩
      exact ⟨f.toL2 ρ, K.slowLift_bounded ρ f⟩
    · exact (K.slowLift ρ).isometry.isClosedEmbedding.isClosed_range
  · rintro z ⟨f, rfl⟩
    refine (boundedMeasurable_toL2_dense ρ).induction_on (p := fun f => K.slowLift ρ f ∈ K.slowSpace ρ) f ?_ ?_
    · exact (Submodule.isClosed_topologicalClosure _).preimage (K.slowLift ρ).continuous
    · intro g
      rw [K.slowLift_bounded]
      exact K.slow_mem ρ g

end FiberKernel
end SchauderTranslates
