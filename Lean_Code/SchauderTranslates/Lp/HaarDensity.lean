import Lean_Code.SchauderTranslates.Lp.HaarDenseSpan
import Lean_Code.SchauderTranslates.Lp.HaarL2Multiplier

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace SchauderTranslates.LpConstruction

/-- Blueprint `lp:haar-density`: orthonormality, finite dyadic spanning,
density for every finite Banach exponent, and the integral-defined finite
L² multiplier contraction, all on actual restricted Lebesgue Lᵖ spaces. -/
theorem haar_density :
    Orthonormal ℂ (haarAtom 2) ∧
    (∀ (p : ℝ≥0∞) (n : ℕ) (c : Fin (2 ^ n) → ℂ), haarDyadicStep p n c ∈ haarAtomSpan p) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → Dense (haarAtomSpan p : Set (HaarLp p))) ∧
    (∀ (s : Finset HaarIndex) (a : HaarIndex → ℂ), (∀ i ∈ s, ‖a i‖ ≤ 1) →
      ∀ f : HaarLp 2,
        ‖∑ i ∈ s, (a i * ∫ x, f x * star (haarAtom 2 i x) ∂haarMeasure) •
          haarAtom 2 i‖ ≤ ‖f‖) := by
  refine ⟨haar_orthonormal, haarDyadicStep_mem_span, ?_, ?_⟩
  · intro p hp hpfin
    exact haar_dense_span hpfin
  · intro s a ha f
    rw [← haarL2Multiplier_apply_integral]
    exact haar_l2_multiplier_bound s a ha f

end SchauderTranslates.LpConstruction
