import Lean_Code.SchauderTranslates.Lp.HaarApproximation

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haar_continuous_mem_closed_span {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : BoundedContinuousFunction ℝ ℂ) :
    BoundedContinuousFunction.toLp p haarMeasure ℂ g ∈ (haarAtomSpan p).topologicalClosure := by
  apply (haarAtomSpan p).isClosed_topologicalClosure.mem_of_tendsto
    (haar_approximation_tendsto g)
  exact Eventually.of_forall fun n => (haarAtomSpan p).le_topologicalClosure
    (haarDyadicStep_mem_span p n _)

/-- The actual complex Haar span is dense in every finite Banach Lᵖ on
the restricted Lebesgue unit interval. -/
theorem haar_dense_span {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense (haarAtomSpan p : Set (HaarLp p)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro f _
  exact (BoundedContinuousFunction.toLp_denseRange ℂ haarMeasure ℂ hp).induction_on f
    (haarAtomSpan p).isClosed_topologicalClosure (haar_continuous_mem_closed_span (p := p))

end SchauderTranslates.LpConstruction
