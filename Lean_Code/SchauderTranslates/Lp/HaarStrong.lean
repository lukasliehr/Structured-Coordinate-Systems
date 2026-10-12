import Lean_Code.SchauderTranslates.Lp.HaarDyadicNorm

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- Density extension uses the same continuous integral coefficient maps,
so its limit is the original finite multiplier. -/
theorem haar_strong_multiplier_bound {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp1 : 1 < p) (hp2 : p < 2) (t : Finset HaarIndex)
    (w : HaarIndex → ℂ) (hw : ∀ i ∈ t, ‖w i‖ ≤ 1) (f : HaarLp p) :
    ‖haarLpMultiplier p q t w f‖ ≤ haarStrongConstant p.toReal * ‖f‖ := by
  let T := haarLpMultiplier p q t w
  let C := haarStrongConstant p.toReal
  have hpfin : p ≠ ∞ := ne_top_of_lt hp2
  have hclosed : IsClosed {f : HaarLp p | ‖T f‖ ≤ C * ‖f‖} :=
    isClosed_le (continuous_norm.comp T.continuous) (continuous_const.mul continuous_norm)
  refine (BoundedContinuousFunction.toLp_denseRange ℂ haarMeasure ℂ hpfin).induction_on f hclosed ?_
  intro g
  have hconv := haar_approximation_tendsto (p := p) g
  exact le_of_tendsto_of_tendsto ((T.continuous.tendsto _).comp hconv).norm
    (hconv.norm.const_mul C) (Eventually.of_forall fun n =>
      haar_dyadic_strong_norm_bound hp1 hp2 n _ t w hw)

/-- Canonical finite integral-defined multiplier on every Banach Lᵖ.
The Hölder conjugate exponent is supplied by mathlib, not a construction
assumption or an additional hypothesis. -/
def haarMultiplier (p : ℝ≥0∞) [Fact (1 ≤ p)] (t : Finset HaarIndex)
    (w : HaarIndex → ℂ) : HaarLp p →L[ℂ] HaarLp p := by
  letI : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  exact haarLpMultiplier p (ENNReal.conjExponent p) t w

theorem haarMultiplier_apply_integral (p : ℝ≥0∞) [Fact (1 ≤ p)] (t : Finset HaarIndex)
    (w : HaarIndex → ℂ) (f : HaarLp p) :
    haarMultiplier p t w f =
      ∑ i ∈ t, (w i * ∫ x, f x * star (haarAtom p i x) ∂haarMeasure) • haarAtom p i := by
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  exact haarLpMultiplier_apply_integral p (ENNReal.conjExponent p) t w f

/-- Blueprint `lp:haar-strong`: every finite Haar multiplier is bounded
on every exponent strictly between one and two, with the exact constant
[s(6/(s-1)+4/(2-s))]^(1/s). The Banach exponent condition is derived here. -/
theorem haar_strong_bound (p : ℝ≥0∞) (hp1 : 1 < p) (hp2 : p < 2) :
    letI : Fact (1 ≤ p) := ⟨hp1.le⟩
    ∀ (t : Finset HaarIndex) (w : HaarIndex → ℂ), (∀ i ∈ t, ‖w i‖ ≤ 1) →
      ∀ f : HaarLp p, ‖haarMultiplier p t w f‖ ≤ haarStrongConstant p.toReal * ‖f‖ := by
  let : Fact (1 ≤ p) := ⟨hp1.le⟩
  let : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  intro t w hw f
  exact haar_strong_multiplier_bound hp1 hp2 t w hw f

end SchauderTranslates.LpConstruction
