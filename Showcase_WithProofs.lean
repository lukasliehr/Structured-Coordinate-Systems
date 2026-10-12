import Lean_Code

/-!
# Structured coordinate systems in `Lᵖ(ℝ)`: the main results, with proofs

Proof-carrying counterpart of `Showcase.lean` (Theorem 1.1, Theorem 1.3 and the three parts
of Theorem 1.4 of the paper). The definitions and the five theorem statements are literally
those of `Showcase.lean`; the proofs are supplied by the internal library `Lean_Code`
(assembled in `Lean_Code/Main/`). Each of the five theorems depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexOrder

namespace SchauderLp

/-- The space `Lᵖ(ℝ)` of `𝕜`-valued functions, for Lebesgue measure. -/
abbrev L (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) := Lp 𝕜 p (volume : Measure ℝ)

/-- The basis constant `K(b) = supₙ ‖Pₙ‖`, where `Pₙ = b.proj n` is the `n`-th partial sum
projection. This is Mathlib's `SchauderBasis.nnnormProjBound`. -/
local notation "K" => SchauderBasis.nnnormProjBound

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A Schauder basis of `Lᵖ(ℝ)` is *non-negative* if every basis vector is non-negative
almost everywhere. (For `𝕜 = ℂ`, `0 ≤ z` means that `z` is real and non-negative.) -/
def IsNonneg (b : SchauderBasis 𝕜 (L 𝕜 p)) : Prop :=
  ∀ n, ∀ᵐ x, 0 ≤ b n x

/-- The Schauder basis `b` of `Lᵖ(ℝ)` is the sequence of translates `(T_{λₙ} f)ₙ` of the
real-valued function `f`, where `(T_λ f)(x) = f (x - λ)`. -/
def IsTranslateBasis (b : SchauderBasis 𝕜 (L 𝕜 p)) (f : ℝ → ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ n, b n =ᵐ[volume] fun x => (f (x - lam n) : 𝕜)

/-- The function `f : ℝ → ℝ` extends to an entire function. -/
def ExtendsToEntire (f : ℝ → ℝ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x

/-- Let `1 ≤ p < ∞` and `ε > 0`. There is a non-negative Schauder basis
of `Lᵖ(ℝ)` with basis constant less than `1 + ε`. Moreover, no non-negative Schauder
basis of `Lᵖ(ℝ)` has basis constant `1`. -/
theorem nonneg_basis (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    (∀ ε : ℝ, 0 < ε → ∃ b : SchauderBasis 𝕜 (L 𝕜 p), IsNonneg b ∧ K b < 1 + ε) ∧
    (∀ b : SchauderBasis 𝕜 (L 𝕜 p), IsNonneg b → K b ≠ 1) :=
  StructuredBases.nonneg_basis_main 𝕜 p hp

/-- For every `2 ≤ p < ∞` there are a nonzero real-valued function
`f ∈ Lᵖ(ℝ)` and a sequence of real numbers `(λₙ)` such that `(T_{λₙ} f)` is a Schauder
basis of `Lᵖ(ℝ)` over either scalar field. -/
theorem translate_basis (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 ≤ p) (hp' : p ≠ ∞) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ b : SchauderBasis ℝ (L ℝ p), IsTranslateBasis b f lam) ∧
      (∃ b : SchauderBasis ℂ (L ℂ p), IsTranslateBasis b f lam) := by
  obtain ⟨f, lam, hf, hf0, -, ⟨b, hb⟩, ⟨b', hb'⟩⟩ :=
    StructuredBases.translate_basis_entire_main p hp hp'
  exact ⟨f, lam, hf, hf0, ⟨b', hb'⟩, ⟨b, hb⟩⟩

/-- For every `2 ≤ p < ∞`, the generator `f` in Theorem 1.3 can be
chosen to extend to an entire function. -/
theorem translate_basis_entire (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 ≤ p) (hp' : p ≠ ∞) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p ∧ ¬ f =ᵐ[volume] 0 ∧ ExtendsToEntire f ∧
      (∃ b : SchauderBasis ℝ (L ℝ p), IsTranslateBasis b f lam) ∧
      (∃ b : SchauderBasis ℂ (L ℂ p), IsTranslateBasis b f lam) := by
  obtain ⟨f, lam, hf, hf0, hF, ⟨b, hb⟩, ⟨b', hb'⟩⟩ :=
    StructuredBases.translate_basis_entire_main p hp hp'
  exact ⟨f, lam, hf, hf0, hF, ⟨b', hb'⟩, ⟨b, hb⟩⟩

/-- If `p = 2`, then for every `ε > 0` one can choose `f` and `(λₙ)`
in Theorem 1.3 so that the basis constant of `(T_{λₙ} f)` is less than `1 + ε`. -/
theorem translate_basis_almost_monotone (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f 2 ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ b : SchauderBasis ℝ (L ℝ 2), IsTranslateBasis b f lam ∧ K b < 1 + ε) ∧
      (∃ b : SchauderBasis ℂ (L ℂ 2), IsTranslateBasis b f lam ∧ K b < 1 + ε) := by
  obtain ⟨f, lam, hf, hf0, -, -, ⟨b, hb, hbK⟩, ⟨b', hb', hbK'⟩⟩ :=
    StructuredBases.translate_basis_L2 hε
  exact ⟨f, lam, hf, hf0, ⟨b', hb', hbK'⟩, ⟨b, hb, hbK⟩⟩

/-- If `2 < p < ∞` and `S ⊆ ℝ` is unbounded, there are distinct
parameters `λₙ ∈ S` and a non-negative function `f ∈ Lᵖ(ℝ)` extending to an entire
function such that `(T_{λₙ} f)` is a Schauder basis of `Lᵖ(ℝ)` over either scalar field. -/
theorem translate_basis_nonneg (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p) (hp' : p ≠ ∞)
    (S : Set ℝ) (hS : ¬ Bornology.IsBounded S) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f p ∧ (∀ x, 0 ≤ f x) ∧ ExtendsToEntire f ∧
      Function.Injective lam ∧ (∀ n, lam n ∈ S) ∧
      (∃ b : SchauderBasis ℝ (L ℝ p), IsTranslateBasis b f lam) ∧
      (∃ b : SchauderBasis ℂ (L ℂ p), IsTranslateBasis b f lam) := by
  obtain ⟨f, lam, hf, hf0, -, hF, hinj, hS', ⟨b, hb⟩, ⟨b', hb'⟩⟩ :=
    StructuredBases.translate_basis_nonneg_main p hp hp' S hS
  exact ⟨f, lam, hf, hf0, hF, hinj, hS', ⟨b', hb'⟩, ⟨b, hb⟩⟩

end SchauderLp
