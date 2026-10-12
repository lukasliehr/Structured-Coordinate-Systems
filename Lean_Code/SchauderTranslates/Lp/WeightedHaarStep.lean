import Lean_Code.SchauderTranslates.Lp.WeightedIntervalStep
import Lean_Code.SchauderTranslates.Lp.WeightedCellComplement
import Lean_Code.SchauderTranslates.Lp.LpSupportedSubmodule

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {e : LebesgueLp p}
variable (D : DisjointStepData p e) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (he : ‖e‖ = 1)

def DisjointStepData.wholeCellIsometry : HaarLp p →ₗᵢ[ℂ] LebesgueLp p :=
  (lpExtendByZeroIsometry p volume D.supportSet D.supportSet_measurable).comp
    (D.weightedCellEquiv hp0 hpfin he).toLinearIsometry

theorem DisjointStepData.wholeCellIsometry_ae (f : HaarLp p) :
    D.wholeCellIsometry hp0 hpfin he f =ᵐ[volume]
      D.supportSet.indicator (fun x => D.complexValue x * f (D.cumulativeMap hp0 hpfin he x)) := by
  have h := (ae_eq_restrict_iff_indicator_ae_eq D.supportSet_measurable).mp
    (D.weightedCellEquiv_ae hp0 hpfin he f)
  exact (lpExtendByZero_ae p volume D.supportSet D.supportSet_measurable
    (D.weightedCellEquiv hp0 hpfin he f)).trans h

theorem DisjointStepData.wholeCellIsometry_supported (f : HaarLp p) :
    SupportedOn (D.wholeCellIsometry hp0 hpfin he f) D.supportSet :=
  lpExtendByZero_supported p volume D.supportSet D.supportSet_measurable _

theorem DisjointStepData.wholeCellIsometry_interval_eq (n k : ℕ) :
    D.wholeCellIsometry hp0 hpfin he (haarIntervalAtom p n k) =
      D.weightedIntervalStep hp0 hpfin he (dyadicEndpoint n k) (dyadicEndpoint n (k + 1)) := by
  have hi : ∀ᵐ x ∂D.weightedMeasure,
      haarIntervalAtom p n k (D.cumulativeMap hp0 hpfin he x) =
        (dyadicInterval n k).indicator (fun _ => (1 : ℂ)) (D.cumulativeMap hp0 hpfin he x) :=
    (D.cumulativeMap_measurePreserving hp0 hpfin he).quasiMeasurePreserving.ae
      (p := fun y => haarIntervalAtom p n k y = (dyadicInterval n k).indicator (fun _ => (1 : ℂ)) y)
      (haarIntervalAtom_ae p n k)
  have hs : ∀ᵐ x ∂D.supportMeasure,
      D.complexValue x * haarIntervalAtom p n k (D.cumulativeMap hp0 hpfin he x) =
        D.complexValue x * (dyadicInterval n k).indicator (fun _ => (1 : ℂ))
          (D.cumulativeMap hp0 hpfin he x) := by
    filter_upwards [(D.supportMeasure_ac_weightedMeasure hp0 hpfin).ae_eq hi] with x hx
    rw [hx]
  have hwhole := (ae_eq_restrict_iff_indicator_ae_eq D.supportSet_measurable).mp hs
  apply Lp.ext
  exact ((D.wholeCellIsometry_ae hp0 hpfin he (haarIntervalAtom p n k)).trans hwhole).trans
    (D.weightedIntervalStep_ae hp0 hpfin he _ _).symm

theorem DisjointStepData.wholeCellIsometry_interval_isCompactStep (n k : ℕ) :
    IsCompactStep p (D.wholeCellIsometry hp0 hpfin he (haarIntervalAtom p n k)) := by
  rw [D.wholeCellIsometry_interval_eq hp0 hpfin he]
  exact D.weightedIntervalStep_isCompactStep hp0 hpfin he _ _

theorem DisjointStepData.wholeCellIsometry_haar_isCompactStep (i : HaarIndex) :
    IsCompactStep p (D.wholeCellIsometry hp0 hpfin he (haarAtom p i)) := by
  let U : HaarLp p →ₗ[ℝ] LebesgueLp p := (D.wholeCellIsometry hp0 hpfin he).toLinearMap.restrictScalars ℝ
  cases i with
  | none => exact D.wholeCellIsometry_interval_isCompactStep hp0 hpfin he 0 0
  | some i =>
      rcases i with ⟨n, k⟩
      change IsCompactStep p (U (haarScale n •
        (haarIntervalAtom p (n + 1) (2 * k.val) - haarIntervalAtom p (n + 1) (2 * k.val + 1))))
      rw [U.map_smul, U.map_sub]
      apply IsCompactStep.smul
      exact (stepSpace p).sub_mem
        (D.wholeCellIsometry_interval_isCompactStep hp0 hpfin he _ _)
        (D.wholeCellIsometry_interval_isCompactStep hp0 hpfin he _ _)

theorem DisjointStepData.wholeCellIsometry_normalized_isCompactStep (i : HaarIndex) :
    IsCompactStep p (D.wholeCellIsometry hp0 hpfin he (haarNormalizedAtom p i)) := by
  let U : HaarLp p →ₗ[ℝ] LebesgueLp p := (D.wholeCellIsometry hp0 hpfin he).toLinearMap.restrictScalars ℝ
  have heq : haarNormalizedAtom p i = (‖haarAtom p i‖⁻¹ : ℝ) • haarAtom p i := by
    rw [haarNormalizedAtom, ← Complex.ofReal_inv]
    exact_mod_cast IsScalarTower.algebraMap_smul ℂ (‖haarAtom p i‖⁻¹) (haarAtom p i)
  change IsCompactStep p (U (haarNormalizedAtom p i))
  rw [heq, U.map_smul]
  exact (D.wholeCellIsometry_haar_isCompactStep hp0 hpfin he i).smul _

end SchauderTranslates.LpConstruction
