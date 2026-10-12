import Lean_Code.SchauderTranslates.SeedCarrierGram

noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The unscaled seed matrix, in orthonormal carrier and phase coordinates. -/
def seedBlock (i₀ : ι) (L : ℕ) (κ : ℂ) : Matrix (ι ⊕ Fin L) (ι ⊕ Fin L) ℂ :=
  Matrix.fromBlocks 1 (fun i _ => if i = i₀ then κ else 0)
    (fun _ i => if i = i₀ then κ else 0)
    ((1 - κ ^ 2) • (1 : Matrix (Fin L) (Fin L) ℂ) + Matrix.of (fun _ _ => κ ^ 2))

theorem seedBlock_carrier_action (i₀ : ι) (L : ℕ) (κ : ℂ) (v : ι ⊕ Fin L → ℂ) (i : ι) :
    (seedBlock i₀ L κ *ᵥ v) (Sum.inl i) =
      v (Sum.inl i) + (if i = i₀ then κ else 0) * ∑ j, v (Sum.inr j) := by
  simp [seedBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    ← Finset.mul_sum, ite_mul]

theorem seedBlock_seed_action (i₀ : ι) (L : ℕ) (κ : ℂ) (v : ι ⊕ Fin L → ℂ) (j : Fin L) :
    (seedBlock i₀ L κ *ᵥ v) (Sum.inr j) =
      κ * v (Sum.inl i₀) + (1 - κ ^ 2) * v (Sum.inr j) + κ ^ 2 * ∑ k, v (Sum.inr k) := by
  simp [seedBlock, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    Finset.sum_add_distrib, ← Finset.mul_sum, ite_mul, mul_ite, add_mul]
  ring

/-- The carrier orthogonal complement has unscaled eigenvalue one. -/
theorem seedBlock_carrier_perp (i₀ : ι) (L : ℕ) (κ : ℂ) (v : ι → ℂ) (hv : v i₀ = 0) :
    seedBlock i₀ L κ *ᵥ Sum.elim v 0 = Sum.elim v 0 := by
  funext i
  cases i with
  | inl i => simp [seedBlock_carrier_action]
  | inr j => simp [seedBlock_seed_action, hv]

/-- The zero-sum seed space has unscaled eigenvalue `1 - κ²`. -/
theorem seedBlock_seed_perp (i₀ : ι) (L : ℕ) (κ : ℂ) (v : Fin L → ℂ) (hv : ∑ j, v j = 0) :
    seedBlock i₀ L κ *ᵥ Sum.elim (0 : ι → ℂ) v = (1 - κ ^ 2) • Sum.elim (0 : ι → ℂ) v := by
  funext i
  cases i with
  | inl i => simp [seedBlock_carrier_action, hv]
  | inr j => simp [seedBlock_seed_action, hv]

namespace SeedCarrier
open MeasureTheory
variable {S : Type*} [MeasurableSpace S] {ρ : Measure S} [IsProbabilityMeasure ρ]

theorem gram_eq_seedBlock (c : SeedCarrier (ι := ι) ρ) (L : ℕ) {m κ : ℝ} (hm : 0 ≤ m)
    (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4) :
    c.gram L m κ = (m : ℂ) • seedBlock c.distinguished L κ := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j => simpa [seedBlock, Matrix.one_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.smul_apply] using c.gram_carrier_carrier L hm hκ i j
    | inr j => rw [c.gram_carrier_seed L hm hκ]; simp [seedBlock, Matrix.smul_apply]
  | inr i => cases j with
    | inl j => rw [c.gram_seed_carrier L hm hκ]; simp [seedBlock, Matrix.smul_apply]
    | inr j => simpa [seedBlock, Matrix.smul_apply, Matrix.one_apply, Matrix.add_apply, Matrix.of_apply] using c.gram_seed_seed L hm hκ i j

end SeedCarrier
end SchauderTranslates
