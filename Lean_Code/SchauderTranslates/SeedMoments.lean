import Lean_Code.SchauderTranslates.SeedParameters

noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The scaled-factor implementation is exactly the real-part formula in the paper. -/
theorem seedKernel_formula (L : ℕ) (m κ : ℝ) (e : ℂ) (z : UnitAddTorus (Fin L)) :
    seedKernel L m ((κ : ℂ) * e) z = (m / (1 / 2 : ℝ) ^ L) *
      ∏ i : Fin L, (1 / 2 : ℝ) * (1 + 2 * κ * (e * star (fourier (1 : ℤ) (z i))).re) := by
  unfold seedKernel seedProduct
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [seedFactor, mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- Joint measurability is available before any slow-variable integration. -/
theorem seedKernel_measurable {S : Type*} [MeasurableSpace S] (e : S → ℂ) (he : Measurable e)
    (L : ℕ) (m κ : ℝ) :
    Measurable (fun p : S × UnitAddTorus (Fin L) => seedKernel L m ((κ : ℂ) * e p.1) p.2) := by
  unfold seedKernel seedProduct seedFactor
  fun_prop

/-- The seed kernel and its exact conditional moments. `E` is any certified global bound;
choosing the supremum norm gives precisely the paper's parameter `κ = 1/(4‖e‖∞)`.
No abstract conditional-expectation or asymptotic hypothesis is used. -/
theorem seed_kernel_moments {S : Type*} [MeasurableSpace S] (ρ : Measure S)
    [IsProbabilityMeasure ρ] (e : S → ℂ) (he : Measurable e) {E : ℝ} (hE0 : 0 ≤ E)
    (hbound : ∀ x, ‖e x‖ ≤ E) (hunit : (∫ x, ‖e x‖ ^ 2 ∂ρ) = 1)
    (L : ℕ) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ (1 / 2 : ℝ) ^ L) :
    let κ := seedParameter E
    let V := fun x z => seedKernel L m ((κ : ℂ) * e x) z
    0 < κ ∧ κ ≤ 1 / 4 ∧
      Measurable (fun p : S × UnitAddTorus (Fin L) => V p.1 p.2) ∧
      (∀ x, Continuous (V x)) ∧
      (∀ x z, 0 < V x z ∧ V x z ≤ 1) ∧
      (∀ x, (∫ z, V x z ∂torusMeasure L) = m) ∧
      (∀ x (j : Fin L),
        (∫ z, (V x z : ℂ) * fourier (1 : ℤ) (z j) ∂torusMeasure L) / (m : ℂ) = (κ : ℂ) * e x) ∧
      (∀ x (j k : Fin L), j ≠ k →
        (∫ z, (V x z : ℂ) * (fourier (1 : ℤ) (z j) * star (fourier (1 : ℤ) (z k)))
          ∂torusMeasure L) / (m : ℂ) = ((κ ^ 2 : ℝ) : ℂ) * ((‖e x‖ ^ 2 : ℝ) : ℂ)) := by
  have hE := one_le_bound_of_unit_energy ρ e he hE0 hbound hunit
  have hκ := seedParameter_bounds hE
  refine ⟨hκ.1, hκ.2, seedKernel_measurable e he L m _,
    fun x => seedKernel_continuous L m _,
    fun x z => seedKernel_bounds L hm hm1 (seedParameter_scaled_bound hE (hbound x)) z,
    fun x => seedKernel_integral L m _, fun x j => seedKernel_normalized_first L hm.ne' _ j, ?_⟩
  intro x j k hjk
  rw [seedKernel_normalized_cross L hm.ne' _ j k hjk]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ.1, mul_pow, Complex.ofReal_mul]

end SchauderTranslates
