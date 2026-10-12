import Lean_Code.Main.PositiveBridge
import Lean_Code.PositiveL1.Existence
import Lean_Code.PositiveL1.NotMonotone

/-!
# Theorem 1.1: non-negative Schauder bases of `Lᵖ(ℝ)`, `1 ≤ p < ∞`

Assembly of the four ingredients:

* existence for `1 < p < ∞` (`Lean_Code/PositiveBiorthogonal`),
* existence for `p = 1` (`Lean_Code/PositiveL1/Existence.lean`),
* the first coordinate projection of a non-negative basis is not contractive for
  `1 < p < ∞` (`Lean_Code/PositiveBiorthogonal`),
* a non-negative basis of `L¹(ℝ)` is never monotone (`Lean_Code/PositiveL1/NotMonotone.lean`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexOrder

namespace StructuredBases

/-- **Theorem 1.1.** For `1 ≤ p < ∞` and either scalar field, non-negative Schauder bases of
`Lᵖ(ℝ)` exist with basis constant below `1 + ε` for every `ε > 0`, and none has basis
constant `1`. -/
theorem nonneg_basis_main (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (∀ ε : ℝ, 0 < ε → ∃ b : SchauderBasis 𝕜 (Lp 𝕜 p (volume : Measure ℝ)),
        (∀ n, ∀ᵐ x : ℝ, 0 ≤ b n x) ∧ (b.nnnormProjBound : ℝ) < 1 + ε) ∧
    (∀ b : SchauderBasis 𝕜 (Lp 𝕜 p (volume : Measure ℝ)),
        (∀ n, ∀ᵐ x : ℝ, 0 ≤ b n x) → b.nnnormProjBound ≠ 1) := by
  rcases eq_or_lt_of_le (Fact.out : (1 : ℝ≥0∞) ≤ p) with h1 | h1
  · subst h1
    refine ⟨fun ε hε => ?_, fun b hb => nnnormProjBound_ne_one_of_nonneg_L1 b hb⟩
    have hθ : (0 : ℝ) < min (ε / 4) (1 / 4) := lt_min (by positivity) (by norm_num)
    have hθ' : min (ε / 4) (1 / 4) < (1 : ℝ) / 2 :=
      (min_le_right _ _).trans_lt (by norm_num)
    obtain ⟨b, hb, hN⟩ := exists_nonneg_schauderBasis_L1 𝕜 hθ hθ'
    refine ⟨b, hb, nnnormProjBound_lt_of_le b hN ?_⟩
    have := min_le_left (ε / 4) (1 / 4 : ℝ)
    linarith
  · refine ⟨fun ε hε => exists_nonneg_schauderBasis_of_one_lt 𝕜 p h1 hp hε, fun b hb => ?_⟩
    exact nnnormProjBound_ne_one_of_lt b (one_lt_norm_proj_one_of_nonneg p h1 hp b hb)

end StructuredBases
