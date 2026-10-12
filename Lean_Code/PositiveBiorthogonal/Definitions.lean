import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic


/-! Exact statement definitions from the immutable root Showcase.lean. -/

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ComplexOrder

namespace PositiveBiorthogonal

/-- The space Lᵖ(ℝ; 𝕜), modulo equality almost everywhere. -/
abbrev L (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) : Type _ :=
  Lp 𝕜 p (volume : Measure ℝ)

/-- The paper's bilinear pairing ⟨f,g⟩ = ∫ f g. -/
def pairing {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
    (f : L 𝕜 p) (g : L 𝕜 q) : 𝕜 :=
  ∫ x : ℝ, f x * g x

local notation "⟨" f ", " g "⟩" => pairing f g

/-- A Schauder basis: continuous coefficient functionals, biorthogonality,
and convergence of the initial partial sums in the Lᵖ norm.
Continuity and biorthogonality also ensure uniqueness of every expansion. -/
structure SchauderBasis (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  b : ℕ → L 𝕜 p
  coeff : ℕ → (L 𝕜 p →L[𝕜] 𝕜)
  biorthogonal : ∀ n l, coeff l (b n) = if n = l then 1 else 0
  expansion : ∀ f : L 𝕜 p,
    Tendsto (fun N => ∑ n ∈ Finset.range N, coeff n f • b n) atTop (𝓝 f)

/-- P_N f = ∑_{n < N} b_n^*(f) b_n, as a continuous linear operator. -/
def P {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : SchauderBasis 𝕜 p) (N : ℕ) : L 𝕜 p →L[𝕜] L 𝕜 p :=
  ∑ n ∈ Finset.range N, (B.coeff n).smulRight (B.b n)

/-- The basis constant K(B) = sup_N ‖P_N‖.
For a Schauder basis in Lᵖ, 1 ≤ p ≤ ∞, these norms are uniformly bounded. -/
def K {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : SchauderBasis 𝕜 p) : ℝ :=
  ⨆ N : ℕ, ‖P B N‖

/-- Nonnegative almost everywhere. For complex scalars this means real and
nonnegative, using the standard partial order supplied by `ComplexOrder`. -/
def Nonnegative {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} (f : L 𝕜 p) : Prop :=
  ∀ᵐ x : ℝ, 0 ≤ f x

/-- An Lᵖ class represented by a compactly supported step function: a finite
linear combination of indicators of bounded intervals. Endpoint conventions
are immaterial because the equality is almost everywhere. -/
def CompactlySupportedStep {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}
    (f : L 𝕜 p) : Prop :=
  ∃ (m : ℕ) (a b : Fin m → ℝ) (c : Fin m → 𝕜),
    ∀ᵐ x : ℝ, f x = ∑ j : Fin m, (Set.Ioc (a j) (b j)).indicator (fun _ => c j) x

/-- The coefficient functions γ_n represent the biorthogonal functionals. -/
def Represents {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : SchauderBasis 𝕜 p) (γ : ℕ → L 𝕜 q) : Prop :=
  ∀ n (f : L 𝕜 p), B.coeff n f = ⟨f, γ n⟩

/-- A basis with positive biorthogonal functionals, represented in Lᑫ. -/
def HasPositiveBiorthogonal {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (q : ℝ≥0∞) (B : SchauderBasis 𝕜 p) : Prop :=
  ∃ γ : ℕ → L 𝕜 q, Represents B γ ∧ ∀ n, Nonnegative (γ n)

/-- A positive basis has nonnegative basis vectors. -/
def PositiveBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : SchauderBasis 𝕜 p) : Prop :=
  ∀ n, Nonnegative (B.b n)

/-- Basis constants of all bases with positive biorthogonal functionals.
There is no step-function or normalization restriction in this set. -/
def biorthogonalConstants (𝕜 : Type*) [RCLike 𝕜]
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] : Set ℝ :=
  {k | ∃ B : SchauderBasis 𝕜 p, HasPositiveBiorthogonal q B ∧ K B = k}

/-- Basis constants of all positive Schauder bases. -/
def positiveConstants (𝕜 : Type*) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set ℝ :=
  {k | ∃ B : SchauderBasis 𝕜 p, PositiveBasis B ∧ K B = k}

end PositiveBiorthogonal
