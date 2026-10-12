import Lean_Code.SchauderTranslates.Lp.WeightedCellIsometry
import Lean_Code.SchauderTranslates.Lp.HaarIntegralNorm

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
variable {e : LebesgueLp p} (D : DisjointStepData p e)
variable (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

def DisjointStepData.normingFunctional : Lp ℂ p D.supportMeasure →L[ℂ] ℂ :=
  (haarIntegral p q).comp
    ((D.weightedCellEquiv hp0 hpfin he).symm : Lp ℂ p D.supportMeasure →L[ℂ] HaarLp p)

theorem DisjointStepData.normingFunctional_image (f : HaarLp p) :
    D.normingFunctional (q := q) hp0 hpfin he (D.weightedCellEquiv hp0 hpfin he f) =
      ∫ x, f x ∂haarMeasure := by
  simp [normingFunctional, haarIntegral_apply]

theorem DisjointStepData.normingFunctional_norm (hp1 : 1 < p) :
    ‖D.normingFunctional (q := q) hp0 hpfin he‖ = 1 := by
  rw [normingFunctional, ContinuousLinearMap.opNorm_comp_linearIsometryEquiv,
    haarIntegral_norm p q hp1 hpfin]

theorem DisjointStepData.normingFunctional_constant :
    D.normingFunctional (q := q) hp0 hpfin he
      (D.weightedCellEquiv hp0 hpfin he (haarConstant p)) = 1 := by
  simp [normingFunctional, haarIntegral_constant]

theorem lpPowerDensity_toReal (p : ℝ≥0∞) {α : Type*} (w : α → ℂ) (x : α) :
    (lpPowerDensity p w x).toReal = ‖w x‖ ^ p.toReal := by
  rw [lpPowerDensity, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)]

theorem lpPowerDensity_lt_top (p : ℝ≥0∞) {α : Type*} (w : α → ℂ) (x : α) :
    lpPowerDensity p w x < ∞ := by
  rw [lpPowerDensity, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_lt_top

include hp0 hpfin he in
theorem DisjointStepData.normingIntegral_image (hp2 : 2 < p) (f : HaarLp p) :
    (∫ x, D.weightedCellEquiv hp0 hpfin he f x *
      haarNormingValue p.toReal (D.complexValue x) ∂D.supportMeasure) = ∫ x, f x ∂haarMeasure := by
  have hs2 : 2 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by norm_num) hpfin).mpr hp2
  have hAE : (fun x => D.weightedCellEquiv hp0 hpfin he f x *
      haarNormingValue p.toReal (D.complexValue x)) =ᵐ[D.supportMeasure]
      fun x => ((lpPowerDensity p D.complexValue x).toReal : ℂ) *
        f (D.cumulativeMap hp0 hpfin he x) := by
    filter_upwards [D.weightedCellEquiv_ae hp0 hpfin he f] with x hx
    rw [hx, lpPowerDensity_toReal]
    calc
      _ = (D.complexValue x * haarNormingValue p.toReal (D.complexValue x)) *
          f (D.cumulativeMap hp0 hpfin he x) := by ring
      _ = _ := by rw [haarNormingValue_product hs2]
  rw [integral_congr_ae hAE]
  have hd := integral_withDensity_eq_integral_toReal_smul
    (μ := D.supportMeasure) (lpPowerDensity_measurable p D.complexValue_measurable)
    (Eventually.of_forall (lpPowerDensity_lt_top p D.complexValue))
    (fun x => f (D.cumulativeMap hp0 hpfin he x))
  simp only [Complex.real_smul] at hd
  rw [← hd, ← D.densityMeasure_eq hp0 hpfin]
  have hmap := (D.cumulativeMap_measurePreserving hp0 hpfin he).map_eq
  have hf : AEStronglyMeasurable (f : ℝ → ℂ)
      (Measure.map (D.cumulativeMap hp0 hpfin he) D.weightedMeasure) := by
    rw [hmap]
    exact Lp.aestronglyMeasurable f
  have hi := integral_map (D.cumulativeMap_measurable hp0 hpfin he).aemeasurable hf
  rw [hmap] at hi
  exact hi.symm

theorem DisjointStepData.normingFunctional_apply (hp2 : 2 < p) (F : Lp ℂ p D.supportMeasure) :
    D.normingFunctional (q := q) hp0 hpfin he F =
      ∫ x, F x * haarNormingValue p.toReal (D.complexValue x) ∂D.supportMeasure := by
  obtain ⟨f, rfl⟩ := (D.weightedCellEquiv hp0 hpfin he).surjective F
  rw [D.normingFunctional_image hp0 hpfin he, D.normingIntegral_image hp0 hpfin he hp2]

end SchauderTranslates.LpConstruction
