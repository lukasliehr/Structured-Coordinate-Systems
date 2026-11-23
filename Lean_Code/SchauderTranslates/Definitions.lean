import Mathlib

/-!
# Definitions for the weighted Fourier construction

Weights on the line, characters, the raw weighted norm, prefix bounds and the distance of a
character to a finite span. The finite extension principle and the existence of a weighted
exponential basis are stated as propositions.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace SchauderTranslates.Construction

/-- Every vector has a unique norm-convergent expansion with respect to `u`. -/
def OrderedSchauderBasis {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (u : ℕ → H) : Prop :=
  ∀ f : H, ∃! c : ℕ → ℂ,
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, c n • u n) atTop (𝓝 f)

/-- Positive-sign Fourier character; translation parameters will be negated. -/
def character (ξ : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ξ * t)

/-- A finite, almost everywhere positive density on the whole line. -/
structure Weight where
  density : ℝ → ℝ
  measurable : Measurable density
  integrable : Integrable density volume
  positive : ∀ᵐ t ∂volume, 0 < density t

def Weight.measure (w : Weight) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (w.density t))

abbrev WeightedL2 (w : Weight) := Lp ℂ 2 w.measure

/-- Raw squared weighted norm, used only for bounded character polynomials. -/
def normSq (w : Weight) (f : ℝ → ℂ) : ℝ :=
  ∫ t, ‖f t‖ ^ 2 * w.density t

def synthesis {d : ℕ} (μ : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) : ℂ :=
  ∑ i, c i * character (μ i) t

/-- Every cut of a finite list, not merely the endpoints of appended blocks. -/
def PrefixBound (w : Weight) {d : ℕ} (μ : Fin d → ℝ) (K : ℝ) : Prop :=
  ∀ (k : ℕ) (c : Fin d → ℂ),
    normSq w (fun t => ∑ i : Fin d, if i.val < k then
      c i * character (μ i) t else 0) ≤ K ^ 2 * normSq w (synthesis μ c)

/-- Infimum of all finite coefficient approximation errors. -/
def distanceSq (w : Weight) {d : ℕ} (μ : Fin d → ℝ) (ξ : ℝ) : ℝ :=
  sInf (Set.range (fun c : Fin d → ℂ =>
    normSq w (fun t => character ξ t - synthesis μ c t)))

def IsTrigPolynomial (W : ℝ → ℝ) : Prop :=
  ∃ (d : ℕ) (ξ : Fin d → ℝ) (c : Fin d → ℂ),
    ∀ t, (W t : ℂ) = synthesis ξ c t

/-- The finite extension principle on the line, as a proposition. -/
def FiniteExtensionPrinciple : Prop :=
  ∀ (w w₀ : Weight), (∫ t, w₀.density t) = 1 →
    ∀ (d : ℕ) (μ : Fin d → ℝ) (K ξ δ τ : ℝ),
      Function.Injective μ → 1 ≤ K → PrefixBound w μ K →
      0 < distanceSq w μ ξ → 0 < δ → 0 < τ →
      ∃ (r : ℕ) (ν : Fin (d + r) → ℝ) (W : ℝ → ℝ) (w' : Weight),
        Function.Injective ν ∧
        (∀ i : Fin d, ν (Fin.castAdd r i) = μ i) ∧
        IsTrigPolynomial W ∧ (∀ t, 0 < W t ∧ W t ≤ 1) ∧
        (∀ t, w'.density t = w.density t * W t) ∧
        (∫ t, w₀.density t * (1 - W t)) < δ ∧
        distanceSq w' ν ξ ≤ (1 / 2 : ℝ) * distanceSq w μ ξ ∧
        PrefixBound w' ν (max K 12 + τ)

/-- The existence of a weighted exponential basis, as a proposition. -/
def WeightedExponentialBasisExists : Prop :=
  ∃ (w : Weight) (μ : ℕ → ℝ) (u : ℕ → WeightedL2 w),
    Function.Injective μ ∧
    (∀ n, (u n : ℝ → ℂ) =ᵐ[w.measure] character (μ n)) ∧
    OrderedSchauderBasis u

end SchauderTranslates.Construction
