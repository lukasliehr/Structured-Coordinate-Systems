import Lean_Code.SchauderTranslates.Sharp.LineStepSharp

/-!
# The sharp finite extension on the line (paper: Proposition `h2:prop:extension`)

From the sharp scalar contracts `ScalarSupplySharp` and `ScalarTuneSharp` (hypotheses of
this file) the finite extension principle holds with the absolute constant `12` replaced by
any `Kstar > 1`, for even weights and with an even new factor.

Given `Kstar > 1` choose `0 < u ≤ 1/100` with `1 + 10u ≤ Kstar`. The product-space
extension (`product_space_extension_sharp`) has prefix constant `max K (1+10u) + τ` and
contraction factor `ϑ = 1 - c_*/2`, `c_* = u/(1+2u)`; it transfers to the line
(`finiteExtensionStep_of_product`), and finitely many repetitions give the factor `1/2`
(`finiteExtensionSharp_of_step`).
-/

noncomputable section

namespace SchauderTranslates.Sharp
open SchauderTranslates Construction

/-- Paper Proposition `h2:prop:extension`: the sharp finite extension principle, from the
sharp scalar supply. -/
theorem finiteExtensionSharp
    (hS : ∀ dd : ℝ, 0 < dd → dd ≤ 1 → ScalarSupplySharp dd ∧ ScalarTuneSharp dd)
    {Kstar : ℝ} (hK : 1 < Kstar) : FiniteExtensionSharp Kstar := by
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = min (1 / 100) ((Kstar - 1) / 10) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hudef]
    exact lt_min (by norm_num) (by linarith)
  have hu1 : u ≤ 1 / 100 := by rw [hudef]; exact min_le_left _ _
  have huK : 1 + 10 * u ≤ Kstar := by
    have h : u ≤ (Kstar - 1) / 10 := by rw [hudef]; exact min_le_right _ _
    linarith
  obtain ⟨hSup, hTune⟩ := hS u hu0 (by linarith)
  have hstep := finiteExtensionStep_of_product
    (product_space_extension_sharp hu0 hu1 hSup hTune)
  have hc0 : 0 < u / (1 + 2 * u) := by positivity
  have hc1 : u / (1 + 2 * u) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  exact (finiteExtensionSharp_of_step (by linarith) (by linarith) hstep).mono huK

end SchauderTranslates.Sharp
