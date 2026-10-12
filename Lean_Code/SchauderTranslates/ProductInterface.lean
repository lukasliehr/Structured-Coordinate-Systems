import Lean_Code.SchauderTranslates.TorusTransfer

/-!
# The product-space finite extension interface

`ProductExtension` is the finite extension on `ℝ × 𝕋^D` (blueprint `extend:product`),
stated through the raw product Gram of the old characters followed by the new mixed
characters. It is a proposition to PROVE; `FiniteExtension.lean` transfers it to the
line, giving `Construction.FiniteExtensionPrinciple`.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Topology ComplexOrder

namespace SchauderTranslates
open Construction

/-- A character of the line times a character of a finite torus. -/
def mixedCharacter {D : ℕ} (lam : ℝ) (k : Fin D → ℤ) (t : ℝ)
    (y : UnitAddTorus (Fin D)) : ℂ :=
  character lam t * UnitAddTorus.mFourier k y

/-- Finite complex linear combinations of mixed characters. -/
def IsMixedTrigPoly {D : ℕ} (F : ℝ → UnitAddTorus (Fin D) → ℂ) : Prop :=
  ∃ (s : Finset (ℝ × (Fin D → ℤ))) (c : ℝ × (Fin D → ℤ) → ℂ),
    ∀ t y, F t y = ∑ p ∈ s, c p * mixedCharacter p.1 p.2 t y

/-- Raw Gram of mixed characters for the measure `w(t) W(t,y) dt dy`, in the
convention `G a b = inner (u a) (u b)`. -/
def productGram (w : Weight) {D n : ℕ} (W : ℝ → UnitAddTorus (Fin D) → ℝ)
    (lam : Fin n → ℝ) (k : Fin n → (Fin D → ℤ)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => ∫ t, (w.density t : ℂ) * ∫ y, (W t y : ℂ) *
    (star (mixedCharacter (lam a) (k a) t y) * mixedCharacter (lam b) (k b) t y)
      ∂torusMeasure D

/-- Raw source moments `inner (u a) e_ξ` of a line character. -/
def productSource (w : Weight) {D n : ℕ} (W : ℝ → UnitAddTorus (Fin D) → ℝ)
    (lam : Fin n → ℝ) (k : Fin n → (Fin D → ℤ)) (ξ : ℝ) : Fin n → ℂ :=
  fun a => ∫ t, (w.density t : ℂ) * ∫ y, (W t y : ℂ) *
    (star (mixedCharacter (lam a) (k a) t y) * character ξ t) ∂torusMeasure D

/-- The coordinate projection onto the first `j` entries. -/
def cutMatrix {n : ℕ} (j : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => if i.val < j then 1 else 0

/-- Blueprint `extend:product`, in the raw (unnormalized) product measure
`w(t) dt ⊗ W(t,y) dy`. The old characters come first with zero torus frequency;
every new character has a nonzero torus frequency. The kernel has constant conditional
mass `M`. Strict Gram conditions are stated so that they survive the line transfer. -/
def ProductExtension : Prop :=
  ∀ (w : Weight) (d : ℕ) (μ : Fin d → ℝ) (K ξ δ τ : ℝ),
    Function.Injective μ → 1 ≤ K → PrefixBound w μ K →
    0 < distanceSq w μ ξ → 0 < δ → 0 < τ →
    ∃ (D r : ℕ) (W : ℝ → UnitAddTorus (Fin D) → ℝ) (M : ℝ)
      (lam : Fin r → ℝ) (k : Fin r → (Fin D → ℤ)),
      IsMixedTrigPoly (fun t y => (W t y : ℂ)) ∧
      (∀ t y, 0 < W t y ∧ W t y ≤ 1) ∧
      (∀ t, (∫ y, W t y ∂torusMeasure D) = M) ∧ 1 - M < δ ∧
      (∀ a, k a ≠ 0) ∧ Function.Injective (fun a => (lam a, k a)) ∧
      (productGram w W (Fin.append μ lam) (Fin.append 0 k)).PosDef ∧
      (∀ j : ℕ, (prefixGramDifference (max K 12 + τ) (cutMatrix j)
        (productGram w W (Fin.append μ lam) (Fin.append 0 k))).PosDef) ∧
      M * (∫ t, w.density t) -
          gramCapture (productGram w W (Fin.append μ lam) (Fin.append 0 k))
            (productSource w W (Fin.append μ lam) (Fin.append 0 k) ξ) <
        (1 / 2 : ℝ) * distanceSq w μ ξ

end SchauderTranslates
