import Lean_Code.SchauderTranslates.ProductEngines
import Lean_Code.SchauderTranslates.ProductSetup

/-!
# Slow vectors in the combined product law

Line functions and lifted residuals are slow in the combined law of tags and engines.
Their inner products are computed in the slow law, and those of line functions in the
normalized line law.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace ProductEngines

variable {S : Type*} [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
variable {L de ne mE : ℕ} (a : Fin mE → SelectiveKernelData S L de ne)

/-- A bounded slow function in the combined law. -/
def slowVec (g : BoundedMeasurableComplex S) : Lp ℂ 2 (law ρ a) :=
  (g.pullbackFst (Fin mE → EngineFresh L de)).toL2 (law ρ a)

theorem slowVec_eq_slowLift (g : BoundedMeasurableComplex S) :
    slowVec ρ a g = (FiberKernel.piKernel (kernels a)).slowLift ρ (g.toL2 ρ) :=
  ((FiberKernel.piKernel (kernels a)).slowLift_bounded ρ g).symm

theorem slowVec_mem (g : BoundedMeasurableComplex S) :
    slowVec ρ a g ∈ (FiberKernel.piKernel (kernels a)).slowSpace ρ :=
  (FiberKernel.piKernel (kernels a)).slow_mem ρ g

theorem slowVec_inner (g h : BoundedMeasurableComplex S) :
    inner ℂ (slowVec ρ a g) (slowVec ρ a h) = inner ℂ (g.toL2 ρ) (h.toL2 ρ) :=
  (FiberKernel.piKernel (kernels a)).slow_inner ρ g h

theorem slowVec_sum {ι : Type*} [Fintype ι] (g : ι → BoundedMeasurableComplex S) (b : ι → ℂ) :
    ∑ i, b i • slowVec ρ a (g i) =
      (FiberKernel.piKernel (kernels a)).slowLift ρ (∑ i, b i • (g i).toL2 ρ) := by
  simp only [slowVec_eq_slowLift, map_sum, map_smul]

end ProductEngines

section LineSlow
variable {dt nt M : ℕ} (s : ScalarData dt nt) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]

/-- Line functions pulled back to the tag law. -/
theorem tag_slow_inner (g h : BoundedMeasurableComplex ℝ) :
    inner ℂ ((g.pullbackFst (Fin M → UnitAddTorus (Fin dt))).toL2 (tagLaw s ρ M))
        ((h.pullbackFst (Fin M → UnitAddTorus (Fin dt))).toL2 (tagLaw s ρ M)) =
      inner ℂ (g.toL2 ρ) (h.toL2 ρ) :=
  (tagKernel ℝ s M).slow_inner ρ g h

end LineSlow
end SchauderTranslates
