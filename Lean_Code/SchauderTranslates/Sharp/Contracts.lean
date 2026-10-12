import Lean_Code.SchauderTranslates.ScalarSupply
import Lean_Code.SchauderTranslates.ScalarTuning
import Lean_Code.SchauderTranslates.LimitStagesBasic
import Lean_Code.SchauderTranslates.SchauderCriterion
import Lean_Code.SchauderTranslates.Characters

/-!
# Interfaces for the sharp `L²` construction (basis constant `< 1 + ε`)

These are propositions to PROVE, never assumptions of the library. They are the sharp
counterparts of `scalar_blocks`, `scalar_gain_tuning`,
`Construction.FiniteExtensionPrinciple` and `Construction.WeightedExponentialBasisExists`:
the absolute constants of the first formalization are replaced by a parameter, and the
evenness of the weights (needed for a real-valued generator) and the Gaussian majorant
(needed for an entire generator) are recorded.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Topology ComplexOrder

namespace SchauderTranslates.Sharp
open SchauderTranslates Construction

/-- Sharp scalar supply (paper: Proposition `h2:lem:scalar`). For the fixed excess `dd`
there is a gain `cd > 0` such that scalar blocks with arbitrarily small loss `ε` exist
whose centered and augmented prefix constants are `< 1 + dd`. -/
def ScalarSupplySharp (dd : ℝ) : Prop :=
  ∃ cd : ℝ, 0 < cd ∧ ∀ δ : ℝ, 0 < δ →
    ∃ (d n : ℕ) (s : ScalarData d n) (ε q K : ℝ),
      s.IsPolynomial ∧ s.IsEven ∧ s.HasPositiveFloor ∧
      (∀ i j, (s.rawGram i j).im = 0) ∧
      0 < ε ∧ ε < δ ∧ ε ≤ 1 / 10 ∧ s.mass = 1 - ε ∧
      cd ≤ s.gain ∧ 0 ≤ q ∧ q < (1 + dd) ^ 2 ∧ s.CenteredPrefixSqBound q ∧
      0 ≤ K ∧ K < 1 + dd ∧ s.AugmentedPrefixSqBound (K ^ 2) ∧
      (s.rawGram - ((ε ^ 2 : ℝ) : ℂ) • 1).PosSemidef ∧
      (∀ i : Fin n, (s.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re ≤ 1 + 2 * ε) ∧
      (s.rawGram⁻¹ (Sum.inl ()) (Sum.inl ())).re < 2

/-- Sharp prescribed gain (paper: Corollary `h2:cor:tune`). -/
def ScalarTuneSharp (dd : ℝ) : Prop :=
  ∃ cd : ℝ, 0 < cd ∧ ∀ z δ : ℝ, 0 < z → z < cd → 0 < δ →
    ∃ (d n : ℕ) (s : ScalarData d n) (ε K : ℝ),
      s.IsPolynomial ∧ s.IsEven ∧ s.HasPositiveFloor ∧
      (∀ i j, (s.rawGram i j).im = 0) ∧
      0 < ε ∧ ε < δ ∧ ε ≤ 1 / 10 ∧ s.mass = 1 - ε ∧ s.gain = z ∧
      0 ≤ K ∧ K < 1 + dd ∧ s.CenteredPrefixSqBound (K ^ 2) ∧ s.AugmentedPrefixSqBound (K ^ 2)

/-- Sharp finite extension on the line (paper: Proposition `h2:prop:extension`).
Compared with `Construction.FiniteExtensionPrinciple`, the absolute constant `12` is
replaced by `Kstar`, the old weight is assumed even and the new factor is even. -/
def FiniteExtensionSharp (Kstar : ℝ) : Prop :=
  ∀ (w w₀ : Weight), (∫ t, w₀.density t) = 1 → (∀ t, w.density (-t) = w.density t) →
    ∀ (d : ℕ) (μ : Fin d → ℝ) (K ξ δ τ : ℝ),
      Function.Injective μ → 1 ≤ K → PrefixBound w μ K →
      0 < distanceSq w μ ξ → 0 < δ → 0 < τ →
      ∃ (r : ℕ) (ν : Fin (d + r) → ℝ) (W : ℝ → ℝ) (w' : Weight),
        Function.Injective ν ∧
        (∀ i : Fin d, ν (Fin.castAdd r i) = μ i) ∧
        IsTrigPolynomial W ∧ (∀ t, 0 < W t ∧ W t ≤ 1) ∧ (∀ t, W (-t) = W t) ∧
        (∀ t, w'.density t = w.density t * W t) ∧
        (∫ t, w₀.density t * (1 - W t)) < δ ∧
        distanceSq w' ν ξ ≤ (1 / 2 : ℝ) * distanceSq w μ ξ ∧
        PrefixBound w' ν (max K Kstar + τ)

/-- Sharp weighted exponential basis (paper: Theorem `h2:thm:weighted`): an even weight
dominated by the Gaussian `exp (-π t²)`, with an injective frequency sequence whose
characters have dense span in `L²(w)` and whose finite prefixes are bounded by `C`. -/
def WeightedExponentialBasisSharp (C : ℝ) : Prop :=
  ∃ (w : Weight) (μ : ℕ → ℝ),
    (∀ t, w.density (-t) = w.density t) ∧
    (∀ᵐ t ∂volume, w.density t ≤ LimitAssembly.gaussWeight.density t) ∧
    Function.Injective μ ∧
    Dense (↑(Submodule.span ℂ (Set.range fun i => weightedCharacter w (μ i))) :
      Set (WeightedL2 w)) ∧
    ∀ (N : ℕ) (c : ℕ →₀ ℂ),
      ‖finitePrefix (fun i => weightedCharacter w (μ i)) N c‖ ≤
        C * ‖Finsupp.linearCombination ℂ (fun i => weightedCharacter w (μ i)) c‖

end SchauderTranslates.Sharp
