import Lean_Code.SchauderTranslates.Lp.HaarValues
import Lean_Code.SchauderTranslates.Lp.HaarL2Multiplier

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

/-- Hölder's continuous bilinear integral pairing supplies the genuine
Haar coefficient map on Lᵖ. The Haar functions are real; no conjugate-linear
scalar convention is imposed on the input. -/
def haarCoefficientMap (i : HaarIndex) : HaarLp p →L[ℂ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing haarMeasure p q).flip (haarAtom q i)

theorem haarCoefficientMap_apply (i : HaarIndex) (f : HaarLp p) :
    haarCoefficientMap p q i f = ∫ x, f x * star (haarAtom p i x) ∂haarMeasure := by
  rw [haarCoefficientMap, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [haarAtom_ae_value q i, haarAtom_ae_value p i] with x hq hp
  change f x * haarAtom q i x = _
  rw [hq, hp, star_haarValue]

def haarLpMultiplier (t : Finset HaarIndex) (w : HaarIndex → ℂ) : HaarLp p →L[ℂ] HaarLp p :=
  ∑ i ∈ t, w i • (haarCoefficientMap p q i).smulRight (haarAtom p i)

theorem haarLpMultiplier_apply (t : Finset HaarIndex) (w : HaarIndex → ℂ) (f : HaarLp p) :
    haarLpMultiplier p q t w f = ∑ i ∈ t, (w i * haarCoefficientMap p q i f) • haarAtom p i := by
  simp [haarLpMultiplier, smul_smul]

theorem haarLpMultiplier_apply_integral (t : Finset HaarIndex) (w : HaarIndex → ℂ) (f : HaarLp p) :
    haarLpMultiplier p q t w f =
      ∑ i ∈ t, (w i * ∫ x, f x * star (haarAtom p i x) ∂haarMeasure) • haarAtom p i := by
  simp_rw [haarLpMultiplier_apply, haarCoefficientMap_apply]

theorem haarLpMultiplier_two (t : Finset HaarIndex) (w : HaarIndex → ℂ) :
    haarLpMultiplier 2 2 t w = haarL2Multiplier t w := by
  ext f
  rw [haarLpMultiplier_apply_integral, haarL2Multiplier_apply_integral]

end SchauderTranslates.LpConstruction
