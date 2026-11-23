module

public import Lean_Code.SchauderTranslates.Definitions

/-!
# Translation on `Lᵖ(ℝ)`

The complex space `Lᵖ(ℝ)` and the translation operator `g ↦ g(· - a)` on it.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ENNReal

namespace SchauderTranslates.LpConstruction

abbrev LebesgueLp (p : ℝ≥0∞) := Lp ℂ p (volume : Measure ℝ)

/-- The Lᵖ class of `x ↦ g (x - a)`. -/
def translate (p : ℝ≥0∞) (a : ℝ) (g : LebesgueLp p) : LebesgueLp p :=
  Lp.compMeasurePreserving (fun x : ℝ => x - a)
    (measurePreserving_sub_right volume a) g

theorem translate_ae (p : ℝ≥0∞) (a : ℝ) (g : LebesgueLp p) :
    (translate p a g : ℝ → ℂ) =ᵐ[volume] (fun x => g (x - a)) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_sub_right volume a)

theorem norm_translate (p : ℝ≥0∞) (a : ℝ) (g : LebesgueLp p) :
    ‖translate p a g‖ = ‖g‖ :=
  Lp.norm_compMeasurePreserving g (measurePreserving_sub_right volume a)

end SchauderTranslates.LpConstruction
