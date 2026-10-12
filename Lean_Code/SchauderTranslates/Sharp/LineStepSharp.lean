import Lean_Code.SchauderTranslates.FiniteExtension
import Lean_Code.SchauderTranslates.Sharp.ProductExtensionSharp
import Lean_Code.SchauderTranslates.Sharp.Iteration

/-!
# One sharp extension step on the line (paper: `h2:ss:transfer`)

The sharp product-space extension `ProductExtensionSharp Kstar θ` is transferred to the line
by the substitution `y = A ω t`, exactly as in `FiniteExtension.lean`
(`LineTransfer.line_extension_core` is reused unchanged). The new point is evenness: the
product kernel is invariant under simultaneous inversion and the phase is odd, so
`W(t) = 𝒲(t, A ω t)` is even.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Topology ComplexOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates Construction LineTransfer

/-- The linear phase is odd. -/
theorem phase_neg {D : ℕ} (ω : Fin D → ℝ) (A t : ℝ) : phase ω A (-t) = -phase ω A t := by
  funext i
  simp [phase]

/-- A kernel invariant under simultaneous inversion restricts to an even function on the
line `y = A ω t`. -/
theorem lineKernel_even {D : ℕ} (W : ℝ → UnitAddTorus (Fin D) → ℝ)
    (hW : ∀ t y, W (-t) (-y) = W t y) (ω : Fin D → ℝ) (A t : ℝ) :
    lineKernel W ω A (-t) = lineKernel W ω A t := by
  unfold lineKernel
  rw [phase_neg, hW]

/-- Paper `h2:prop:extension` with the factor `θ`: the sharp product-space extension
transfers to the line, and the new factor of the weight is even. -/
theorem finiteExtensionStep_of_product {Kstar θ : ℝ} (h : ProductExtensionSharp Kstar θ) :
    FiniteExtensionStep Kstar θ := by
  intro w w₀ hw₀ hw d μ K ξ δ τ hμ hK hpb hdist hδ hτ
  obtain ⟨D, r, W, M, lam, k, hWpoly, hWpos, hWneg, hWmass, hM, hk0, hkinj, hBpos, hBpref,
    hBcap⟩ := h w hw d μ K ξ δ τ hμ hK hpb hdist hδ hτ
  obtain ⟨ω, A, hinj, hloss, hdistA, hpref⟩ := line_extension_core w w₀ hw₀ W M
    (Fin.append μ lam) (Fin.append 0 k) ξ δ (max K Kstar + τ) (θ * distanceSq w μ ξ)
    hWpoly hWpos hWmass hM (append_pairs_injective μ lam k hμ hk0 hkinj) hBpos hBpref hBcap
  refine ⟨r, fun a => Fin.append μ lam a + A * frequencyDot (Fin.append 0 k a) ω,
    lineKernel W ω A, lineWeight W ω w hWpoly hWpos A, hinj, ?_,
    isTrigPolynomial_lineKernel ω hWpoly A, fun t => hWpos t (phase ω A t),
    fun t => lineKernel_even W hWneg ω A t, fun t => rfl, hloss, hdistA.le, hpref⟩
  intro i
  simp [Fin.append_left]

end SchauderTranslates.Sharp
