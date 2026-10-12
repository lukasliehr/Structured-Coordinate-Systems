import Lean_Code.SchauderTranslates.Lp.StepCellDensity

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {e : LebesgueLp p}
variable (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

def DisjointStepData.cumulativeEquiv : HaarLp p ≃ₗᵢ[ℂ] Lp ℂ p D.weightedMeasure :=
  lpMeasurePreservingAeEquiv p (D.cumulativeMap_measurePreserving hp0 hpfin he)
    (D.inverseCumulative_measurePreserving hp0 hpfin he)
    (D.inverseCumulative_cumulativeMap_ae hp0 hpfin he)

/-- The paper's onto isometry `ψ ↦ e (ψ ∘ C)`, into the actual Lebesgue
Lᵖ space on the nonzero support of the compact step vector. -/
def DisjointStepData.weightedCellEquiv : HaarLp p ≃ₗᵢ[ℂ] Lp ℂ p D.supportMeasure :=
  (D.cumulativeEquiv hp0 hpfin he).trans
    ((lpMeasureCongr p D.weightedMeasure
      (D.supportMeasure.withDensity (lpPowerDensity p D.complexValue))
      (D.densityMeasure_eq hp0 hpfin)).trans
      (lpDensityEquiv p hp0 hpfin D.supportMeasure D.complexValue
        D.complexValue_measurable D.complexValue_ne_zero_ae))

theorem DisjointStepData.cumulativeEquiv_ae (f : HaarLp p) :
    D.cumulativeEquiv hp0 hpfin he f =ᵐ[D.weightedMeasure] f ∘ D.cumulativeMap hp0 hpfin he :=
  lpMeasurePreservingAeEquiv_ae p _ _ _ f

theorem DisjointStepData.weightedCellEquiv_ae (f : HaarLp p) :
    D.weightedCellEquiv hp0 hpfin he f =ᵐ[D.supportMeasure]
      fun x => D.complexValue x * f (D.cumulativeMap hp0 hpfin he x) := by
  let Q := lpMeasureCongr p D.weightedMeasure
    (D.supportMeasure.withDensity (lpPowerDensity p D.complexValue))
    (D.densityMeasure_eq hp0 hpfin)
  let g := Q (D.cumulativeEquiv hp0 hpfin he f)
  have hg := lpMeasureCongr_ae p D.weightedMeasure
    (D.supportMeasure.withDensity (lpPowerDensity p D.complexValue))
    (D.densityMeasure_eq hp0 hpfin) (D.cumulativeEquiv hp0 hpfin he f)
  have hw := lpDensityEquiv_ae p hp0 hpfin D.supportMeasure D.complexValue
    D.complexValue_measurable D.complexValue_ne_zero_ae g
  filter_upwards [hw,
    (lpPowerDensity_reverse_ac p D.complexValue_measurable D.complexValue_ne_zero_ae).ae_eq hg,
    (D.supportMeasure_ac_weightedMeasure hp0 hpfin).ae_eq
      (D.cumulativeEquiv_ae hp0 hpfin he f)] with x hw hg hc
  change lpDensityEquiv p hp0 hpfin D.supportMeasure D.complexValue
    D.complexValue_measurable D.complexValue_ne_zero_ae g x = _
  rw [hw]
  change D.complexValue x * Q (D.cumulativeEquiv hp0 hpfin he f) x = _
  rw [hg, hc]
  rfl

set_option maxHeartbeats 1000000 in
theorem DisjointStepData.weightedCellEquiv_constant_ae :
    D.weightedCellEquiv hp0 hpfin he (haarConstant p) =ᵐ[D.supportMeasure] D.complexValue := by
  have hP : ∀ᵐ y ∂haarMeasure, haarConstant p y = 1 := haarConstant_ae_one p
  have hpres : MeasurePreserving (D.cumulativeMap hp0 hpfin he) D.weightedMeasure haarMeasure :=
    D.cumulativeMap_measurePreserving hp0 hpfin he
  have hc : ∀ᵐ x ∂D.weightedMeasure, haarConstant p (D.cumulativeMap hp0 hpfin he x) = 1 :=
    hpres.quasiMeasurePreserving.ae (p := fun y => haarConstant p y = 1) hP
  filter_upwards [D.weightedCellEquiv_ae hp0 hpfin he (haarConstant p),
    (D.supportMeasure_ac_weightedMeasure hp0 hpfin).ae_eq hc] with x hx hc
  rw [hx, hc, mul_one]

theorem weighted_cell_onto_isometry :
    Function.Surjective (D.weightedCellEquiv hp0 hpfin he) ∧
    (∀ f : HaarLp p, ‖D.weightedCellEquiv hp0 hpfin he f‖ = ‖f‖) ∧
    (∀ f : HaarLp p, D.weightedCellEquiv hp0 hpfin he f =ᵐ[D.supportMeasure]
      fun x => D.complexValue x * f (D.cumulativeMap hp0 hpfin he x)) :=
  ⟨(D.weightedCellEquiv hp0 hpfin he).surjective,
    (D.weightedCellEquiv hp0 hpfin he).norm_map,
    D.weightedCellEquiv_ae hp0 hpfin he⟩

end SchauderTranslates.LpConstruction
