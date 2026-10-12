import Lean_Code.SchauderTranslates.Lp.LpMeasureScaling

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem lpMeasurePreserving_surjective {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) (ν : Measure β)
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Function.Surjective (Lp.compMeasurePreservingₗᵢ ℂ e.symm he.symm :
      Lp ℂ p μ →ₗᵢ[ℂ] Lp ℂ p ν) := by
  intro g
  refine ⟨Lp.compMeasurePreserving e he g, ?_⟩
  change Lp.compMeasurePreserving e.symm he.symm (Lp.compMeasurePreserving e he g) = g
  rw [← Lp.compMeasurePreserving_comp_apply g he he.symm]
  have hid : (e : α → β) ∘ e.symm = id := funext e.apply_symm_apply
  simpa only [hid] using Lp.compMeasurePreserving_id_apply g

/-- Pullback by the inverse of a measure-preserving measurable equivalence
is an onto complex linear isometry of the actual Lᵖ spaces. -/
def lpMeasurePreservingEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) (ν : Measure β)
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Lp ℂ p μ ≃ₗᵢ[ℂ] Lp ℂ p ν :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ e.symm he.symm)
    (lpMeasurePreserving_surjective p μ ν e he)

theorem lpMeasurePreservingEquiv_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α) (ν : Measure β)
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) (f : Lp ℂ p μ) :
    lpMeasurePreservingEquiv p μ ν e he f =ᵐ[ν] fun x => f (e.symm x) :=
  Lp.coeFn_compMeasurePreserving f he.symm

end SchauderTranslates.LpConstruction
