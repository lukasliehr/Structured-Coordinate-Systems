import Lean_Code.SchauderTranslates.Contracts

/-!
# The finite-exponent Lᵖ target

These are propositions to prove, not construction assumptions. Exponents are
ENNReal values, with an explicit exclusion of infinity in the range statements.
The scalar field, measure, translation sign and ordered expansion property
are exactly those of the existing L² theorem.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SchauderTranslates.LpConstruction

abbrev LebesgueLp (p : ℝ≥0∞) := Lp ℂ p (volume : Measure ℝ)

/-- The Lᵖ class of `x ↦ g (x - a)`, for every exponent. -/
def translate (p : ℝ≥0∞) (a : ℝ) (g : LebesgueLp p) : LebesgueLp p :=
  Lp.compMeasurePreserving (fun x : ℝ => x - a)
    (measurePreserving_sub_right volume a) g

theorem translate_ae (p : ℝ≥0∞) (a : ℝ) (g : LebesgueLp p) :
    (translate p a g : ℝ → ℂ) =ᵐ[volume] (fun x => g (x - a)) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_sub_right volume a)

theorem norm_translate (p : ℝ≥0∞) (a : ℝ) (g : LebesgueLp p) :
    ‖translate p a g‖ = ‖g‖ :=
  Lp.norm_compMeasurePreserving g (measurePreserving_sub_right volume a)

/-- Exact target at one exponent. No regularity or real-valuedness condition
is imposed on the generator, and the translation parameters are injective. -/
def BasisExists (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∃ (g : LebesgueLp p) (Λ : ℕ → ℝ),
    g ≠ 0 ∧ Function.Injective Λ ∧
    Construction.OrderedSchauderBasis (fun n => translate p (Λ n) g)

/-- The new obligation supplied by the `p > 2` manuscript. -/
def StrictRange : Prop :=
  ∀ (p : ℝ≥0∞) (hp : 2 < p), p ≠ ∞ →
    letI : Fact (1 ≤ p) := ⟨le_trans (by norm_num) hp.le⟩
    BasisExists p

/-- The requested whole finite range, including the existing endpoint.
This definition states an open obligation; it does not prove the obligation. -/
def FullRange : Prop :=
  ∀ (p : ℝ≥0∞) (hp : 2 ≤ p), p ≠ ∞ →
    letI : Fact (1 ≤ p) := ⟨le_trans (by norm_num) hp⟩
    BasisExists p

end SchauderTranslates.LpConstruction
