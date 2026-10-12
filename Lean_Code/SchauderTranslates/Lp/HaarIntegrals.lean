import Lean_Code.SchauderTranslates.Lp.HaarModel

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haar_interval_indicator_integrable (n k : ℕ) :
    Integrable ((dyadicInterval n k).indicator (fun _ => (1 : ℂ))) haarMeasure :=
  (integrable_const (1 : ℂ)).indicator (dyadicInterval_measurable n k)

theorem haarIntervalAtom_integrable (p : ℝ≥0∞) (n k : ℕ) :
    Integrable (haarIntervalAtom p n k) haarMeasure :=
  (haar_interval_indicator_integrable n k).congr (haarIntervalAtom_ae p n k).symm

theorem haar_interval_indicator_integral (n k : ℕ) (hk : k < 2 ^ n) :
    (∫ x, (dyadicInterval n k).indicator (fun _ => (1 : ℂ)) x ∂haarMeasure) =
      (1 / (2 : ℝ) ^ n : ℝ) := by
  rw [integral_indicator (dyadicInterval_measurable n k)]
  simp [measureReal_def, haarInterval_measure n k hk, Complex.real_smul]

theorem haarIntervalAtom_integral (p : ℝ≥0∞) (n k : ℕ) (hk : k < 2 ^ n) :
    (∫ x, haarIntervalAtom p n k x ∂haarMeasure) = (1 / (2 : ℝ) ^ n : ℝ) := by
  rw [integral_congr_ae (haarIntervalAtom_ae p n k)]
  exact haar_interval_indicator_integral n k hk

theorem haarFunction_integrable (p : ℝ≥0∞) (n k : ℕ) :
    Integrable (haarFunction p n k) haarMeasure :=
  (((haar_interval_indicator_integrable (n + 1) (2 * k)).sub
    (haar_interval_indicator_integrable (n + 1) (2 * k + 1))).const_mul (haarScale n : ℂ)).congr
    (haarFunction_ae p n k).symm

theorem haarFunction_integral_zero (p : ℝ≥0∞) (n k : ℕ) (hk : k < 2 ^ n) :
    (∫ x, haarFunction p n k x ∂haarMeasure) = 0 := by
  have hl : 2 * k < 2 ^ (n + 1) := by rw [pow_succ]; omega
  have hr : 2 * k + 1 < 2 ^ (n + 1) := by rw [pow_succ]; omega
  rw [integral_congr_ae (haarFunction_ae p n k), integral_const_mul,
    integral_sub (haar_interval_indicator_integrable (n + 1) (2 * k))
      (haar_interval_indicator_integrable (n + 1) (2 * k + 1)),
    haar_interval_indicator_integral (n + 1) (2 * k) hl,
    haar_interval_indicator_integral (n + 1) (2 * k + 1) hr, sub_self, mul_zero]

theorem haarConstant_ae_one (p : ℝ≥0∞) : (haarConstant p : ℝ → ℂ) =ᵐ[haarMeasure] (fun _ => 1) := by
  have hm : ∀ᵐ x ∂haarMeasure, x ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico
  filter_upwards [haarIntervalAtom_ae p 0 0, hm] with x hi hx
  simpa [haarConstant, dyadicInterval_zero, hx] using hi

end SchauderTranslates.LpConstruction
