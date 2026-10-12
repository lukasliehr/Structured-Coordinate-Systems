import Lean_Code.SchauderTranslates.Sharp.ScalarSupplySharp
import Lean_Code.SchauderTranslates.Sharp.FiniteExtensionSharp
import Lean_Code.SchauderTranslates.Sharp.LimitAssemblySharp
import Lean_Code.SchauderTranslates.Sharp.Return

/-!
# Translates in `L²(ℝ)`: assembly

From the sharp one-step extension on the line (`FiniteExtensionSharp`) to a real-valued
generator that extends to an entire function and whose translates form a Schauder basis of
`L²(ℝ)`, over both scalar fields, with basis constant below `1 + ε`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace StructuredBases

open SchauderTranslates.Sharp in
/-- The `L²` statements, conditional on the sharp finite extension. -/
theorem translate_basis_L2_of_finiteExtension
    (hfe : ∀ Kstar : ℝ, 1 < Kstar → FiniteExtensionSharp Kstar) {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f 2 volume ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧ Function.Injective lam ∧
      (∃ b : SchauderBasis ℂ (Lp ℂ 2 (volume : Measure ℝ)),
        (∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ)) ∧
        (b.nnnormProjBound : ℝ) < 1 + ε) ∧
      (∃ b : SchauderBasis ℝ (Lp ℝ 2 (volume : Measure ℝ)),
        (∀ n, (b n : ℝ → ℝ) =ᵐ[volume] fun x => f (x - lam n)) ∧
        (b.nnnormProjBound : ℝ) < 1 + ε) := by
  obtain ⟨C, hC, hW⟩ := weightedExponentialBasisSharp_of_finiteExtension hfe hε
  obtain ⟨f, lam, hf, hf0, hF, hlam, ⟨b, hb, hbC⟩, ⟨b', hb', hbC'⟩⟩ :=
    translates_of_weightedExponentialBasisSharp hW
  exact ⟨f, lam, hf, hf0, hF, hlam, ⟨b, hb, nnnormProjBound_lt_of_le b hbC hC⟩,
    ⟨b', hb', nnnormProjBound_lt_of_le b' hbC' hC⟩⟩

open SchauderTranslates.Sharp in
/-- **Translates in `L²(ℝ)`.** For every `ε > 0` there are a nonzero real-valued function
`f ∈ L²(ℝ)` extending to an entire function and distinct real numbers `λₙ` such that the
translates `f(· - λₙ)` form a Schauder basis of `L²(ℝ)` over `ℂ` and over `ℝ`, with basis
constant below `1 + ε` in both cases. -/
theorem translate_basis_L2 {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f 2 volume ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧ Function.Injective lam ∧
      (∃ b : SchauderBasis ℂ (Lp ℂ 2 (volume : Measure ℝ)),
        (∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ)) ∧
        (b.nnnormProjBound : ℝ) < 1 + ε) ∧
      (∃ b : SchauderBasis ℝ (Lp ℝ 2 (volume : Measure ℝ)),
        (∀ n, (b n : ℝ → ℝ) =ᵐ[volume] fun x => f (x - lam n)) ∧
        (b.nnnormProjBound : ℝ) < 1 + ε) :=
  translate_basis_L2_of_finiteExtension
    (fun _ hK => finiteExtensionSharp
      (fun _ h0 h1 => ⟨scalarSupplySharp h0 h1, scalarTuneSharp h0 h1⟩) hK) hε

end StructuredBases
