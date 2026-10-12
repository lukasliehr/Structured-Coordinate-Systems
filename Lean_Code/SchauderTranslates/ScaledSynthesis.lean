import Lean_Code.SchauderTranslates.ScaledGramBound

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A common positive Gram rescaling cancels from every synthesis inequality. -/
theorem scaled_gram_synthesis_bound {ι H : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : ι → H) {B : Matrix ι ι ℂ} (hB : B.PosDef) (r : ℝ) (hr : 0 < r)
    (hgram : Matrix.gram ℂ u = (r : ℂ) • B) (D : Matrix ι ι ℂ) (K : ℝ)
    (hb : ‖gramConjugate B D‖ ≤ K) (c : ι → ℂ) :
    ‖finiteSynthesis u (D *ᵥ c)‖ ^ 2 ≤ K ^ 2 * ‖finiteSynthesis u c‖ ^ 2 := by
  have hu : LinearIndependent ℂ u := by
    apply Matrix.posDef_gram_iff_linearIndependent.mp
    rw [hgram]
    exact hB.smul (by exact_mod_cast hr)
  have hs := gramConjugate_scaled_bound hB D hr (sq_nonneg K)
    (pow_le_pow_left₀ (norm_nonneg _) hb 2)
  rw [← hgram] at hs
  exact (synthesis_gram_prefix_iff u hu D K).mp hs c

end SchauderTranslates
