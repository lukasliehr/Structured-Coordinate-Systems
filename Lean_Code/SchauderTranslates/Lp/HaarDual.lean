import Lean_Code.SchauderTranslates.Lp.HaarNormingIdentities
import Lean_Code.SchauderTranslates.Lp.HaarConjugation
import Lean_Code.SchauderTranslates.Lp.HaarDualExponents

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haar_dual_multiplier_bound {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp2 : 2 < p) (hpfin : p ≠ ∞)
    (t : Finset HaarIndex) (w : HaarIndex → ℂ) (hw : ∀ i ∈ t, ‖w i‖ ≤ 1)
    (f : HaarLp p) :
    ‖haarLpMultiplier p q t w f‖ ≤ haarStrongConstant q.toReal * ‖f‖ := by
  obtain ⟨hq1, hq2⟩ := haar_dual_exponents (q := q) hp2 hpfin
  have hs1 : 1 < q.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by norm_num) (ne_top_of_lt hq2)).mpr hq1
  have hs2 : q.toReal < 2 := by
    simpa using (ENNReal.toReal_lt_toReal (ne_top_of_lt hq2) (by norm_num)).mpr hq2
  apply haar_norm_le_of_pairing_bound (q := q) hp2 hpfin _
    (mul_nonneg (haarStrongConstant_pos hs1 hs2).le (norm_nonneg f))
  intro g
  rw [haar_multiplier_pairing_transpose]
  calc
    _ ≤ ‖f‖ * ‖haarLpMultiplier q p t w g‖ := haarPairing_norm_le p q f _
    _ ≤ ‖f‖ * (haarStrongConstant q.toReal * ‖g‖) :=
      mul_le_mul_of_nonneg_left (haar_strong_multiplier_bound hq1 hq2 t w hw g) (norm_nonneg f)
    _ = _ := by ring

/-- Blueprint `lp:haar-dual`: all finite Haar multipliers on every
finite exponent above two have the paper's conjugate-exponent bound.
The Banach and conjugate-exponent instances are derived, not assumed. -/
theorem haar_dual_bound (p : ℝ≥0∞) (hp2 : 2 < p) (hpfin : p ≠ ∞) :
    letI : Fact (1 ≤ p) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp2.le⟩
    ∀ (t : Finset HaarIndex) (w : HaarIndex → ℂ), (∀ i ∈ t, ‖w i‖ ≤ 1) →
      ∀ f : HaarLp p,
        ‖haarMultiplier p t w f‖ ≤ haarStrongConstant (ENNReal.conjExponent p).toReal * ‖f‖ := by
  let : Fact (1 ≤ p) := ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hp2.le⟩
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  intro t w hw f
  exact haar_dual_multiplier_bound hp2 hpfin t w hw f

end SchauderTranslates.LpConstruction
