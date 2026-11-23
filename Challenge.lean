module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! Main results of "Structured coordinate systems in Lᵖ(ℝ)" by Freeman, Liehr and Taylor. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder

namespace SchauderLp

/-- The space Lᵖ(ℝ) of 𝕜-valued functions. -/
abbrev L (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) := Lp 𝕜 p (volume : Measure ℝ)

/-- The basis constant K(b) = supₙ ‖Pₙ‖ of a Schauder basis b. -/
local notation "K" => SchauderBasis.nnnormProjBound

-- Throughout, the scalar field 𝕜 is ℝ or ℂ, and 1 ≤ p ≤ ∞.
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A Schauder basis b is non-negative if every bₙ is non-negative almost everywhere. -/
def IsNonneg (b : SchauderBasis 𝕜 (L 𝕜 p)) : Prop :=
  ∀ n, ∀ᵐ x, 0 ≤ b n x

/-- The Schauder basis b is the sequence of translates (T_{λₙ} f), where T_λ f = f(· - λ). -/
def IsTranslateBasis (b : SchauderBasis 𝕜 (L 𝕜 p)) (f : ℝ → ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ n, b n =ᵐ[volume] fun x => (f (x - lam n) : 𝕜)

/-- The function f extends to an entire function. -/
def ExtendsToEntire (f : ℝ → ℝ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x

/-- Theorem 1.1: non-negative Schauder bases with basis constant arbitrarily close to one. -/
theorem nonneg_basis (hp : p < ∞) {ε : ℝ} (hε : 0 < ε) :
    (∃ f : SchauderBasis 𝕜 (L 𝕜 p), IsNonneg f ∧ K f < 1 + ε) ∧
    (∀ g : SchauderBasis 𝕜 (L 𝕜 p), IsNonneg g → K g ≠ 1) := by
  sorry

/-- Theorem 1.3: Schauder bases of translates of a single function, for 2 ≤ p < ∞. -/
theorem translate_basis (hp : 2 ≤ p) (hp' : p < ∞) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ b : SchauderBasis ℝ (L ℝ p), IsTranslateBasis b f lam) ∧
      (∃ b : SchauderBasis ℂ (L ℂ p), IsTranslateBasis b f lam) := by
  sorry

/-- Theorem 1.4 (i): for p = 2, the generator is entire and the basis constant is below 1 + ε. -/
theorem translate_basis_L2 {ε : ℝ} (hε : 0 < ε) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f 2 ∧ ¬ f =ᵐ[volume] 0 ∧ ExtendsToEntire f ∧
      (∃ b : SchauderBasis ℝ (L ℝ 2), IsTranslateBasis b f lam ∧ K b < 1 + ε) ∧
      (∃ b : SchauderBasis ℂ (L ℂ 2), IsTranslateBasis b f lam ∧ K b < 1 + ε) := by
  sorry

/-- Theorem 1.4 (ii): for p > 2, the generator is non-negative and entire, with all λₙ in S. -/
theorem translate_basis_nonneg (hp : 2 < p) (hp' : p < ∞) {S : Set ℝ}
    (hS : ¬ Bornology.IsBounded S) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p ∧ (∀ x, 0 ≤ f x) ∧ ExtendsToEntire f ∧
      (∀ n, lam n ∈ S) ∧
      (∃ b : SchauderBasis ℝ (L ℝ p), IsTranslateBasis b f lam) ∧
      (∃ b : SchauderBasis ℂ (L ℂ p), IsTranslateBasis b f lam) := by
  sorry

end SchauderLp
