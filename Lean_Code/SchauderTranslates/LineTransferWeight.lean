import Lean_Code.SchauderTranslates.LineTransferBasics

/-!
# The substituted line weight and the convergence of its finite moments

For a product kernel `W(t, y)` and a direction `ω`, the line weight at scale `A` is
`w(t) W(t, A ω t)`. All Gram entries, source moments, the target norm and the reference
loss converge to their product-space values as `A → ∞`; finite Gram stability then fixes
one scale at which all strict finite conclusions hold on the line.
-/

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators Topology ComplexOrder

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LineTransfer
open Construction

section LineWeight
variable {D : ℕ}

/-- The kernel restricted to the line `y = A ω t`. -/
def lineKernel (W : ℝ → UnitAddTorus (Fin D) → ℝ) (ω : Fin D → ℝ) (A t : ℝ) : ℝ :=
  W t (phase ω A t)

theorem lineKernel_complex {W : ℝ → UnitAddTorus (Fin D) → ℝ} (ω : Fin D → ℝ)
    {s : Finset (ℝ × (Fin D → ℤ))} {c : ℝ × (Fin D → ℤ) → ℂ}
    (hW : ∀ t y, (W t y : ℂ) = ∑ p ∈ s, c p * mixedCharacter p.1 p.2 t y) (A t : ℝ) :
    (lineKernel W ω A t : ℂ) =
      ∑ p ∈ s, c p * character (p.1 + A * frequencyDot p.2 ω) t := by
  simp only [lineKernel, hW, mixedCharacter_phase]

theorem continuous_lineKernel {W : ℝ → UnitAddTorus (Fin D) → ℝ} (ω : Fin D → ℝ)
    (hW : IsMixedTrigPoly (fun t y => (W t y : ℂ))) (A : ℝ) :
    Continuous (lineKernel W ω A) := by
  obtain ⟨s, c, hc⟩ := hW
  have h1 : Continuous (fun t => (lineKernel W ω A t : ℂ)) := by
    simp_rw [lineKernel_complex ω hc A]
    exact continuous_finsetSum _ (fun p _ => continuous_const.mul (continuous_character _))
  have h2 := Complex.continuous_re.comp h1
  simpa [Function.comp_def] using h2

theorem isTrigPolynomial_lineKernel {W : ℝ → UnitAddTorus (Fin D) → ℝ} (ω : Fin D → ℝ)
    (hW : IsMixedTrigPoly (fun t y => (W t y : ℂ))) (A : ℝ) :
    IsTrigPolynomial (lineKernel W ω A) := by
  obtain ⟨s, c, hc⟩ := hW
  refine ⟨s.card,
    fun i => (s.equivFin.symm i).1.1 + A * frequencyDot (s.equivFin.symm i).1.2 ω,
    fun i => c (s.equivFin.symm i).1, fun t => ?_⟩
  rw [lineKernel_complex ω hc A t, synthesis, ← Finset.sum_coe_sort s]
  exact (Equiv.sum_comp s.equivFin.symm
    (fun x : s => c x.1 * character (x.1.1 + A * frequencyDot x.1.2 ω) t)).symm

/-- The line weight `w(t) W(t, A ω t)`. -/
def lineWeight (W : ℝ → UnitAddTorus (Fin D) → ℝ) (ω : Fin D → ℝ) (w : Weight)
    (hWpoly : IsMixedTrigPoly (fun t y => (W t y : ℂ)))
    (hWpos : ∀ t y, 0 < W t y ∧ W t y ≤ 1) (A : ℝ) : Weight where
  density t := w.density t * lineKernel W ω A t
  measurable := w.measurable.mul (continuous_lineKernel ω hWpoly A).measurable
  integrable := by
    refine w.integrable.mul_bdd (c := 1)
      (continuous_lineKernel ω hWpoly A).aestronglyMeasurable ?_
    refine Eventually.of_forall (fun t => ?_)
    have h := hWpos t (phase ω A t)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by unfold lineKernel; linarith [h.1], h.2⟩
  positive := by
    filter_upwards [w.positive] with t ht
    exact mul_pos ht (hWpos t (phase ω A t)).1

@[simp] theorem lineWeight_density (W : ℝ → UnitAddTorus (Fin D) → ℝ) (ω : Fin D → ℝ)
    (w : Weight) (hWpoly : IsMixedTrigPoly (fun t y => (W t y : ℂ)))
    (hWpos : ∀ t y, 0 < W t y ∧ W t y ≤ 1) (A t : ℝ) :
    (lineWeight W ω w hWpoly hWpos A).density t = w.density t * lineKernel W ω A t := rfl

/-! ### Convergence of the finitely many line moments -/

variable {W : ℝ → UnitAddTorus (Fin D) → ℝ} {ω : Fin D → ℝ} {w : Weight}
  {hWpoly : IsMixedTrigPoly (fun t y => (W t y : ℂ))}
  {hWpos : ∀ t y, 0 < W t y ∧ W t y ≤ 1}
  {s : Finset (ℝ × (Fin D → ℤ))} {c : ℝ × (Fin D → ℤ) → ℂ}

theorem tendsto_line_gram {n : ℕ} (Λ : Fin n → ℝ) (κ : Fin n → (Fin D → ℤ))
    (hc : ∀ t y, (W t y : ℂ) = ∑ p ∈ s, c p * mixedCharacter p.1 p.2 t y)
    (hω : ∀ a b, ∀ p ∈ s, p.2 - κ a + κ b ≠ 0 → frequencyDot (p.2 - κ a + κ b) ω ≠ 0) :
    Tendsto (fun A => Matrix.gram ℂ (atoms (lineWeight W ω w hWpoly hWpos A)
      (fun a => Λ a + A * frequencyDot (κ a) ω))) atTop (𝓝 (productGram w W Λ κ)) := by
  refine tendsto_pi_nhds.mpr fun a => tendsto_pi_nhds.mpr fun b => ?_
  have hrep := kernel_pairing_rep (F := fun t y => (W t y : ℂ)) hc (Λ a) (Λ b) (κ a) (κ b)
  have ht := line_transfer s c (fun p => p.1 - Λ a + Λ b) (fun p => p.2 - κ a + κ b)
    (fun t y => (W t y : ℂ) *
      (star (mixedCharacter (Λ a) (κ a) t y) * mixedCharacter (Λ b) (κ b) t y))
    hrep (fun t => (w.density t : ℂ)) w.integrable.ofReal ω (hω a b)
  refine ht.congr (fun A => ?_)
  rw [gram_atoms_apply]
  congr 1
  funext t
  simp only [lineWeight_density, mixedCharacter_phase, lineKernel]
  push_cast
  ring

theorem tendsto_line_source {n : ℕ} (Λ : Fin n → ℝ) (κ : Fin n → (Fin D → ℤ)) (ξ : ℝ)
    (hc : ∀ t y, (W t y : ℂ) = ∑ p ∈ s, c p * mixedCharacter p.1 p.2 t y)
    (hω : ∀ a, ∀ p ∈ s, p.2 - κ a + 0 ≠ 0 → frequencyDot (p.2 - κ a + 0) ω ≠ 0) :
    Tendsto (fun A => sourceMoments (atoms (lineWeight W ω w hWpoly hWpos A)
      (fun a => Λ a + A * frequencyDot (κ a) ω))
        (weightedCharacter (lineWeight W ω w hWpoly hWpos A) ξ)) atTop
      (𝓝 (productSource w W Λ κ ξ)) := by
  refine tendsto_pi_nhds.mpr fun a => ?_
  have hrep := kernel_pairing_rep (F := fun t y => (W t y : ℂ)) hc (Λ a) ξ (κ a) 0
  have ht := line_transfer s c (fun p => p.1 - Λ a + ξ) (fun p => p.2 - κ a + 0)
    (fun t y => (W t y : ℂ) *
      (star (mixedCharacter (Λ a) (κ a) t y) * mixedCharacter ξ 0 t y))
    hrep (fun t => (w.density t : ℂ)) w.integrable.ofReal ω (hω a)
  have hlim : productSource w W Λ κ ξ a = ∫ t, (w.density t : ℂ) * ∫ y, (W t y : ℂ) *
      (star (mixedCharacter (Λ a) (κ a) t y) * mixedCharacter ξ 0 t y) ∂torusMeasure D := by
    simp only [productSource, mixedCharacter_zero]
  rw [hlim]
  refine ht.congr (fun A => ?_)
  rw [sourceMoments_atoms_apply]
  congr 1
  funext t
  simp only [lineWeight_density, mixedCharacter_phase, lineKernel, frequencyDot_zero_left,
    mul_zero, add_zero]
  push_cast
  ring

theorem tendsto_line_norm (M : ℝ) (hWmass : ∀ t, (∫ y, W t y ∂torusMeasure D) = M)
    (hc : ∀ t y, (W t y : ℂ) = ∑ p ∈ s, c p * mixedCharacter p.1 p.2 t y)
    (hω : ∀ p ∈ s, p.2 ≠ 0 → frequencyDot p.2 ω ≠ 0) (ξ : ℝ) :
    Tendsto (fun A => ‖weightedCharacter (lineWeight W ω w hWpoly hWpos A) ξ‖ ^ 2) atTop
      (𝓝 (M * ∫ t, w.density t)) := by
  have ht := line_transfer_real W s c hc w.density w.integrable ω hω
  simp_rw [hWmass] at ht
  rw [integral_mul_const, mul_comm] at ht
  refine ht.congr (fun A => ?_)
  rw [norm_sq_weightedCharacter]
  rfl

theorem tendsto_line_loss (hWpoly : IsMixedTrigPoly (fun t y => (W t y : ℂ)))
    (hWpos : ∀ t y, 0 < W t y ∧ W t y ≤ 1)
    (w₀ : Weight) (hw₀ : (∫ t, w₀.density t) = 1) (M : ℝ)
    (hWmass : ∀ t, (∫ y, W t y ∂torusMeasure D) = M)
    (hc : ∀ t y, (W t y : ℂ) = ∑ p ∈ s, c p * mixedCharacter p.1 p.2 t y)
    (hω : ∀ p ∈ s, p.2 ≠ 0 → frequencyDot p.2 ω ≠ 0) :
    Tendsto (fun A => ∫ t, w₀.density t * (1 - lineKernel W ω A t)) atTop (𝓝 (1 - M)) := by
  have ht := line_transfer_real W s c hc w₀.density w₀.integrable ω hω
  simp_rw [hWmass] at ht
  rw [integral_mul_const, hw₀, one_mul] at ht
  refine ((tendsto_const_nhds (x := (1 : ℝ))).sub ht).congr (fun A => ?_)
  have hi := (lineWeight W ω w₀ hWpoly hWpos A).integrable
  have he : (fun t => w₀.density t * (1 - lineKernel W ω A t)) =
      fun t => w₀.density t - (lineWeight W ω w₀ hWpoly hWpos A).density t := by
    funext t
    rw [lineWeight_density]
    ring
  rw [he, integral_sub w₀.integrable hi, hw₀]
  rfl

end LineWeight

end SchauderTranslates.LineTransfer
