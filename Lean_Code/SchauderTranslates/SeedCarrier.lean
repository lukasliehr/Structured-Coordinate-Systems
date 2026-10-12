import Lean_Code.SchauderTranslates.SeedKernelFloor
import Lean_Code.SchauderTranslates.IntegralGramOrder

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]

/-- Bounded measurable orthonormal coordinates for a finite carrier.
The distinguished coordinate is the unit vector denoted by `e` in the paper. -/
structure SeedCarrier (ρ : Measure S) where
  row : ι → S → ℂ
  measurable : ∀ i, Measurable (row i)
  bounded : ∀ i, ∃ B : ℝ, ∀ x, ‖row i x‖ ≤ B
  reference : integralGram ρ (fun _ => 1) row = 1
  distinguished : ι

namespace SeedCarrier
variable {ρ : Measure S} [IsProbabilityMeasure ρ] (c : SeedCarrier (ι := ι) ρ)

abbrev e : S → ℂ := c.row c.distinguished

@[simp] theorem reference_entry (i j : ι) :
    (∫ x, star (c.row i x) * c.row j x ∂ρ) = if i = j then 1 else 0 := by
  have h := congrFun (congrFun c.reference i) j
  simpa only [integralGram, Complex.ofReal_one, one_mul, Matrix.one_apply] using h

theorem unit_energy : (∫ x, ‖c.e x‖ ^ 2 ∂ρ) = 1 := by
  have h := c.reference_entry c.distinguished c.distinguished
  simp only [ite_true, Complex.star_def, Complex.conj_mul', ← integral_complex_ofReal] at h
  exact_mod_cast h

/-- Actual representatives of carrier and seed rows on the product space. -/
def rows (L : ℕ) : ι ⊕ Fin L → S × UnitAddTorus (Fin L) → ℂ
  | Sum.inl i, p => c.row i p.1
  | Sum.inr j, p => fourier (1 : ℤ) (p.2 j)

theorem rows_measurable (L : ℕ) (i : ι ⊕ Fin L) : Measurable (c.rows L i) := by
  cases i with
  | inl i => exact (c.measurable i).comp measurable_fst
  | inr j => exact (fourier (1 : ℤ)).continuous.measurable.comp ((measurable_pi_apply j).comp measurable_snd)

theorem rows_bounded (L : ℕ) (i : ι ⊕ Fin L) : ∃ B : ℝ, ∀ x, ‖c.rows L i x‖ ≤ B := by
  cases i with
  | inl i => obtain ⟨B, hB⟩ := c.bounded i; exact ⟨B, fun x => hB x.1⟩
  | inr j => exact ⟨1, fun x => by simp [rows, fourier_apply]⟩

def weight (L : ℕ) (m κ : ℝ) (p : S × UnitAddTorus (Fin L)) : ℝ :=
  seedKernel L m ((κ : ℂ) * c.e p.1) p.2

theorem weight_measurable (L : ℕ) (m κ : ℝ) : Measurable (c.weight L m κ) :=
  seedKernel_measurable c.e (c.measurable _) L m κ

theorem weight_nonneg (L : ℕ) {m κ : ℝ} (hm : 0 ≤ m)
    (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4) (p : S × UnitAddTorus (Fin L)) :
    0 ≤ c.weight L m κ p := by
  have h := (seedKernel_uniform_bounds L hm (hκ p.1) p.2).1
  exact (by unfold seedFloor; positivity : 0 ≤ seedFloor L m).trans h

theorem weight_bound (L : ℕ) {m κ : ℝ} (hm : 0 ≤ m)
    (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4) (p : S × UnitAddTorus (Fin L)) :
    |c.weight L m κ p| ≤ m / (1 / 2 : ℝ) ^ L := by
  rw [abs_of_nonneg (c.weight_nonneg L hm hκ p)]
  exact (seedKernel_uniform_bounds L hm (hκ p.1) p.2).2

/-- The raw seed Gram is an integral Gram, not an assumed matrix model. -/
def gram (L : ℕ) (m κ : ℝ) : Matrix (ι ⊕ Fin L) (ι ⊕ Fin L) ℂ :=
  integralGram (ρ.prod (torusMeasure L)) (c.weight L m κ) (c.rows L)

theorem gram_integrable (L : ℕ) {m κ : ℝ} (hm : 0 ≤ m)
    (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4) (i j : ι ⊕ Fin L) :
    Integrable (fun p => (c.weight L m κ p : ℂ) * star (c.rows L i p) * c.rows L j p)
      (ρ.prod (torusMeasure L)) :=
  integralGram_integrand _ (c.weight_measurable L m κ) (c.weight_bound L hm hκ)
    (c.rows_measurable L) (c.rows_bounded L) i j

theorem gram_posSemidef (L : ℕ) {m κ : ℝ} (hm : 0 ≤ m)
    (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4) : (c.gram L m κ).PosSemidef :=
  integralGram_posSemidef _ (c.weight_measurable L m κ) (c.weight_nonneg L hm hκ)
    (fun p => (le_abs_self _).trans (c.weight_bound L hm hκ p))
    (c.rows_measurable L) (c.rows_bounded L)

end SeedCarrier
end SchauderTranslates
