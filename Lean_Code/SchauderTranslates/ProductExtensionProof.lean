module

public import Lean_Code.SchauderTranslates.ProductRaw

/-!
# Arithmetic for the finite extension on a product space

Two elementary bounds used in the proof of the product-space extension: the loss of a product
of masses in `[0,1]`, and the margin of the prefix constant.
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Matrix
open scoped BigOperators InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction ProductEngines

/-- Bernoulli-type loss bound for products of masses in `[0,1]`. -/
theorem one_sub_mul_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    1 - x * y ≤ (1 - x) + (1 - y) := by nlinarith

theorem one_sub_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    1 - x ^ k ≤ k * (1 - x) := by
  have h := one_add_le_pow_of_two_add_nonneg (a := x - 1) (by linarith) k
  have he : (1 + (x - 1)) = x := by ring
  rw [he] at h
  nlinarith

/-- The arithmetic of the prefix margin. -/
theorem prefix_margin {K τ ρs lam : ℝ} (hK : 1 ≤ K) (hτ : 0 < τ)
    (hρ0 : 0 ≤ ρs) (hρ3 : ρs ≤ 1 / 3) (hρτ : ρs ≤ τ / (4 * max K 12))
    (hlam : lam ≤ 3) :
    (1 + ρs) / (1 - ρs) * max (K ^ 2) ((1 + lam) * 6 ^ 2) < (max K 12 + τ) ^ 2 := by
  set K₁ := max K 12
  have hK₁ : 12 ≤ K₁ := le_max_right _ _
  have hKK : K ≤ K₁ := le_max_left _ _
  have hm : max (K ^ 2) ((1 + lam) * 6 ^ 2) ≤ K₁ ^ 2 := by
    apply max_le
    · exact pow_le_pow_left₀ (by linarith) hKK 2
    · nlinarith
  have hfrac : (1 + ρs) / (1 - ρs) ≤ 1 + 3 * ρs := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpos : 0 ≤ max (K ^ 2) ((1 + lam) * 6 ^ 2) := le_max_of_le_left (sq_nonneg _)
  have h3 : 3 * ρs * K₁ ^ 2 ≤ (3 / 4) * τ * K₁ := by
    have h4 : ρs * (4 * K₁) ≤ τ := (le_div_iff₀ (by positivity)).mp hρτ
    nlinarith
  calc (1 + ρs) / (1 - ρs) * max (K ^ 2) ((1 + lam) * 6 ^ 2)
      ≤ (1 + 3 * ρs) * K₁ ^ 2 := by
        apply mul_le_mul hfrac hm hpos (by linarith)
    _ = K₁ ^ 2 + 3 * ρs * K₁ ^ 2 := by ring
    _ ≤ K₁ ^ 2 + (3 / 4) * τ * K₁ := by linarith
    _ < (K₁ + τ) ^ 2 := by nlinarith

end SchauderTranslates
