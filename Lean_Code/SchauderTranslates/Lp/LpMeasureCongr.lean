import Lean_Code.SchauderTranslates.Lp.LpDensityMultiply

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace SchauderTranslates.LpConstruction

theorem lpMeasureCongr_preserving {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (h : μ = ν) : MeasurePreserving (MeasurableEquiv.refl α) μ ν := by
  constructor
  · exact measurable_id
  · change Measure.map id μ = ν
    rw [Measure.map_id, h]

def lpMeasureCongr {α : Type*} [MeasurableSpace α] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ ν : Measure α) (h : μ = ν) : Lp ℂ p μ ≃ₗᵢ[ℂ] Lp ℂ p ν :=
  lpMeasurePreservingEquiv p μ ν (MeasurableEquiv.refl α) (lpMeasureCongr_preserving μ ν h)

theorem lpMeasureCongr_ae {α : Type*} [MeasurableSpace α] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ ν : Measure α) (h : μ = ν) (f : Lp ℂ p μ) : lpMeasureCongr p μ ν h f =ᵐ[ν] f := by
  exact lpMeasurePreservingEquiv_ae p μ ν (MeasurableEquiv.refl α)
    (lpMeasureCongr_preserving μ ν h) f

end SchauderTranslates.LpConstruction
