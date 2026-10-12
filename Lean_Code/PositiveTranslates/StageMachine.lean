import Lean_Code.SchauderTranslates.Lp.Packet

/-!
# Interface between the reference construction and the analytic generator (`p > 2`)

For the non-negative entire generator of the paper (Theorem `thm:translate-properties`(iii))
the proof has two halves.

* The *reference construction* produces, stage by stage, exact translates
  `T_{λ_{t,i}} V_t` of compactly supported non-negative step functions
  `V_t = v_t + a_t ∑ᵢ T_{-λ_{t,i}} h_t` and proves that they form a Schauder basis
  whatever admissible inputs `v_t` are supplied.
* The *analytic half* chooses the inputs `v_t` as step approximations of an entire
  function `G_{t-1}`, updates `G_t = G_{t-1} + a_t ∑ᵢ T_{-λ_{t,i}} (h_t * Gaussian)`, and
  passes to the limit.

`StageMachine` is the contract between the two halves. It is a structure to CONSTRUCT
(file `…/PositiveTranslates/Machine*.lean`), never an assumption of the library.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexOrder BigOperators

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Real and non-negative almost everywhere. -/
def IsNonneg (g : LebesgueLp p) : Prop := ∀ᵐ x : ℝ, 0 ≤ g x

/-- Admissible input of a stage: a non-negative compactly supported step function
with `1/2 ≤ ‖v‖ ≤ 2`. -/
structure Admissible (v : LebesgueLp p) : Prop where
  step : IsCompactStep p v
  nonneg : IsNonneg v
  lower : 1 / 2 ≤ ‖v‖
  upper : ‖v‖ ≤ 2

/-- `2^p (N-1) N^{-(p-1)}`, the deficit in the positive packet (paper, proof of
`thm:translate-properties`(iii)). -/
def posDeficit (r : ℝ) (N : ℕ) : ℝ := 2 ^ r * ((N : ℝ) - 1) * (N : ℝ) ^ (-(r - 1))

/-- The scale `d` with `d^p = ‖v‖^p / (1 - 2^p (N-1) N^{-(p-1)})`. -/
def posScale (r V : ℝ) (N : ℕ) : ℝ := V / (1 - posDeficit r N) ^ (1 / r)

/-- The amplitude `a = 2 d N^{-1/q}`, `1/q = (p-1)/p`. -/
def posAmplitude (r d : ℝ) (N : ℕ) : ℝ := 2 * d * (N : ℝ) ^ (-(r - 1) / r)

/-- The reference function `V = v + a ∑ᵢ T_{-λᵢ} h`. -/
def referenceFunction (p : ℝ≥0∞) [Fact (1 ≤ p)] {N : ℕ} (v h : LebesgueLp p) (lam : Fin N → ℝ) :
    LebesgueLp p :=
  v + posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N • ∑ i, translate p (-(lam i)) h

/-- The reference construction as a machine driven by admissible inputs.
`Γ` is the set from which translation parameters are taken. -/
structure StageMachine (p : ℝ≥0∞) [Fact (1 ≤ p)] (Γ : Set ℝ) where
  /-- Finite-stage data. -/
  State : Type
  /-- The initial state: one vector `𝟙_[0,1)` with parameter `0`. -/
  init : State
  /-- Translation parameters and reference vectors created so far, in order. -/
  births : State → List (ℝ × LebesgueLp p)
  /-- The function to be approximated at the next stage. -/
  target : State → LebesgueLp p
  /-- Smallest admissible packet size at the next stage. -/
  minSize : State → ℕ
  /-- The parameters chosen at the next stage, for packet size `N`, input `v`, and a
  lower bound `Λ₀` requested by the caller. -/
  params : State → (N : ℕ) → LebesgueLp p → ℝ → Fin N → ℝ
  /-- The next state. -/
  next : State → ℕ → LebesgueLp p → ℝ → State
  /-- The basis constant of every run. -/
  K : ℝ
  births_init : births init = [(0, intervalAtom p (0, 1))]
  target_step : ∀ S, IsCompactStep p (target S)
  target_nonneg : ∀ S, IsNonneg (target S)
  target_norm : ∀ S, ‖target S‖ = 1
  minSize_pos : ∀ S, 1 ≤ minSize S
  deficit_le : ∀ S N, minSize S ≤ N → posDeficit p.toReal N ≤ 1 / 2
  params_mem : ∀ S N v Λ₀ i, params S N v Λ₀ i ∈ Γ
  params_gt : ∀ S N v Λ₀ i, Λ₀ < params S N v Λ₀ i
  params_gt_old : ∀ S N v Λ₀ i, ∀ b ∈ births S, b.1 < params S N v Λ₀ i
  params_injective : ∀ S N v Λ₀, Function.Injective (params S N v Λ₀)
  births_next : ∀ S N v Λ₀, minSize S ≤ N → Admissible v →
    births (next S N v Λ₀) = births S ++ List.ofFn fun i : Fin N =>
      (params S N v Λ₀ i,
        translate p (params S N v Λ₀ i) (referenceFunction p v (target S) (params S N v Λ₀)))
  /-- The added copies are disjoint from each other: `‖V - v‖ = a N^{1/p}`. -/
  reference_edit_norm : ∀ S N v Λ₀, minSize S ≤ N → Admissible v →
    ‖referenceFunction p v (target S) (params S N v Λ₀) - v‖ =
      posAmplitude p.toReal (posScale p.toReal ‖v‖ N) N * (N : ℝ) ^ (1 / p.toReal)
  /-- The added copies are disjoint from `v`. -/
  reference_norm_ge : ∀ S N v Λ₀, minSize S ≤ N → Admissible v →
    ‖v‖ ≤ ‖referenceFunction p v (target S) (params S N v Λ₀)‖
  /-- Every run driven by admissible inputs produces a Schauder basis. -/
  basis_of_run : ∀ (S : ℕ → State) (N : ℕ → ℕ) (v : ℕ → LebesgueLp p) (Λ₀ : ℕ → ℝ),
    S 0 = init → (∀ t, S (t + 1) = next (S t) (N t) (v t) (Λ₀ t)) →
    (∀ t, minSize (S t) ≤ N t) → (∀ t, Admissible (v t)) →
    ∃ B : SchauderBasis ℂ (LebesgueLp p),
      (∀ t n (h : n < (births (S t)).length), B n = ((births (S t)).get ⟨n, h⟩).2) ∧
      ∀ M, ‖B.proj M‖ ≤ K

end StructuredBases.PositiveTranslates
