import Lean_Code.SchauderTranslates.Lp.HaarAffineMeasure
import Lean_Code.SchauderTranslates.Lp.LpMeasureScalingInverse

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

abbrev HaarIntervalLp (p : ℝ≥0∞) (a l : ℝ) := Lp ℂ p (haarIntervalMeasure a l)

theorem haarInterval_scale_ne_zero {l : ℝ} (hl : 0 < l) : ENNReal.ofReal l⁻¹ ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (inv_pos.mpr hl)).ne'

/-- The onto normalized affine transport uses Lebesgue measure on the
actual target interval; the scalar measure factor is removed isometrically. -/
def haarIntervalEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] (a l : ℝ) (hl : 0 < l) :
    HaarLp p ≃ₗᵢ[ℂ] HaarIntervalLp p a l :=
  (lpMeasurePreservingEquiv p haarMeasure
    (ENNReal.ofReal l⁻¹ • haarIntervalMeasure a l) (haarAffine a l hl)
      (haarAffine_measurePreserving a l hl)).trans
    (lpMeasureScaleEquiv p (haarIntervalMeasure a l) (ENNReal.ofReal l⁻¹)
      (haarInterval_scale_ne_zero hl) ENNReal.ofReal_ne_top).symm

theorem haarIntervalEquiv_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (a l : ℝ) (hl : 0 < l)
    (f : HaarLp p) :
    haarIntervalEquiv p a l hl f =ᵐ[haarIntervalMeasure a l]
      fun x => ((l⁻¹ ^ p.toReal⁻¹ : ℝ) : ℂ) * f ((x - a) / l) := by
  let P := lpMeasurePreservingEquiv p haarMeasure
    (ENNReal.ofReal l⁻¹ • haarIntervalMeasure a l) (haarAffine a l hl)
      (haarAffine_measurePreserving a l hl)
  have hp := lpMeasurePreservingEquiv_ae p haarMeasure
    (ENNReal.ofReal l⁻¹ • haarIntervalMeasure a l) (haarAffine a l hl)
      (haarAffine_measurePreserving a l hl) f
  have hb := lpMeasureScaleEquiv_symm_ae p (haarIntervalMeasure a l) (ENNReal.ofReal l⁻¹)
    (haarInterval_scale_ne_zero hl) ENNReal.ofReal_ne_top (P f)
  filter_upwards [hb, (Measure.absolutelyContinuous_smul (haarInterval_scale_ne_zero hl)).ae_eq hp]
    with x hb hp
  change (lpMeasureScaleEquiv p (haarIntervalMeasure a l) (ENNReal.ofReal l⁻¹)
    (haarInterval_scale_ne_zero hl) ENNReal.ofReal_ne_top).symm (P f) x = _
  rw [hb, hp, ENNReal.toReal_ofReal (inv_nonneg.mpr hl.le)]
  rfl

theorem haarIntervalEquiv_integral (p : ℝ≥0∞) [Fact (1 ≤ p)] (a l : ℝ) (hl : 0 < l)
    (f : HaarLp p) :
    (∫ x, haarIntervalEquiv p a l hl f x ∂haarIntervalMeasure a l) =
      (((l⁻¹ ^ p.toReal⁻¹) * l : ℝ) : ℂ) * ∫ x, f x ∂haarMeasure := by
  have hp := (haarAffine_measurePreserving a l hl).symm.integral_comp
    (haarAffine a l hl).symm.measurableEmbedding (f : ℝ → ℂ)
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hl.le), Complex.real_smul] at hp
  have hi : (∫ x, f ((x - a) / l) ∂haarIntervalMeasure a l) =
      (l : ℂ) * ∫ x, f x ∂haarMeasure := by
    have hmul := congrArg (fun z : ℂ => (l : ℂ) * z) hp
    change (l : ℂ) * ((l⁻¹ : ℝ) * ∫ x, f ((x - a) / l) ∂haarIntervalMeasure a l) =
      (l : ℂ) * ∫ x, f x ∂haarMeasure at hmul
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hl.ne', Complex.ofReal_one, one_mul] at hmul
    exact hmul
  rw [integral_congr_ae (haarIntervalEquiv_ae p a l hl f), integral_const_mul, hi]
  rw [Complex.ofReal_mul]
  ring

end SchauderTranslates.LpConstruction
