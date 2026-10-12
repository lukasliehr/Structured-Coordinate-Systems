import Lean_Code.SchauderTranslates.SeedCarrier

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.SeedCarrier
variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {ρ : Measure S} [IsProbabilityMeasure ρ] (c : SeedCarrier (ι := ι) ρ)
variable (L : ℕ) {m κ : ℝ} (hm : 0 ≤ m) (hκ : ∀ x, ‖(κ : ℂ) * c.e x‖ ≤ 1 / 4)

include hm hκ

theorem gram_carrier_carrier (i j : ι) :
    c.gram L m κ (Sum.inl i) (Sum.inl j) = (m : ℂ) * (if i = j then 1 else 0) := by
  rw [gram, integralGram, integral_prod _ (c.gram_integrable L hm hκ _ _)]
  simp only [rows, weight]
  simp_rw [integral_mul_const, integral_complex_ofReal, seedKernel_integral]
  simp_rw [mul_assoc, integral_const_mul]
  rw [c.reference_entry]

theorem gram_carrier_seed (i : ι) (j : Fin L) :
    c.gram L m κ (Sum.inl i) (Sum.inr j) = (m : ℂ) * κ * (if i = c.distinguished then 1 else 0) := by
  rw [gram, integralGram, integral_prod _ (c.gram_integrable L hm hκ _ _)]
  simp only [rows, weight]
  have he (x : S) (z : UnitAddTorus (Fin L)) :
      (seedKernel L m ((κ : ℂ) * c.e x) z : ℂ) * star (c.row i x) * fourier (1 : ℤ) (z j) =
      star (c.row i x) * ((seedKernel L m ((κ : ℂ) * c.e x) z : ℂ) * fourier (1 : ℤ) (z j)) := by ring
  simp_rw [he, integral_const_mul, seedKernel_first_moment]
  have he' (x : S) : star (c.row i x) * ((m : ℂ) * ((κ : ℂ) * c.e x)) =
      ((m : ℂ) * κ) * (star (c.row i x) * c.e x) := by ring
  simp_rw [he', integral_const_mul]
  rw [c.reference_entry]

theorem gram_seed_carrier (j : Fin L) (i : ι) :
    c.gram L m κ (Sum.inr j) (Sum.inl i) = (m : ℂ) * κ * (if i = c.distinguished then 1 else 0) := by
  rw [← (c.gram_posSemidef L hm hκ).isHermitian.apply, c.gram_carrier_seed L hm hκ]
  split_ifs <;> simp_all [star_mul, Complex.star_def, mul_comm]

theorem gram_seed_diagonal (j : Fin L) : c.gram L m κ (Sum.inr j) (Sum.inr j) = m := by
  rw [gram, integralGram, integral_prod _ (c.gram_integrable L hm hκ _ _)]
  simp only [rows, weight, mul_assoc, Complex.star_def, Complex.conj_mul']
  simp only [fourier_apply, Circle.norm_coe, one_pow, Complex.ofReal_one, mul_one]
  simp_rw [integral_complex_ofReal, seedKernel_integral]
  simp

theorem gram_seed_offdiagonal (j k : Fin L) (hjk : j ≠ k) :
    c.gram L m κ (Sum.inr j) (Sum.inr k) = (m : ℂ) * κ ^ 2 := by
  rw [gram, integralGram, integral_prod _ (c.gram_integrable L hm hκ _ _)]
  simp only [rows, weight]
  have he (x : S) (z : UnitAddTorus (Fin L)) :
      (seedKernel L m ((κ : ℂ) * c.e x) z : ℂ) * star (fourier (1 : ℤ) (z j)) * fourier (1 : ℤ) (z k) =
      (seedKernel L m ((κ : ℂ) * c.e x) z : ℂ) * (fourier (1 : ℤ) (z k) * star (fourier (1 : ℤ) (z j))) := by ring
  simp_rw [he, seedKernel_cross_moment L m _ k j hjk.symm]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Complex.ofReal_mul]
  simp_rw [← mul_assoc, integral_const_mul, integral_complex_ofReal]
  rw [c.unit_energy]
  simp

/-- Exact full seed block, including its diagonal normalization. -/
theorem gram_seed_seed (j k : Fin L) :
    c.gram L m κ (Sum.inr j) (Sum.inr k) =
      (m : ℂ) * ((1 - (κ : ℂ) ^ 2) * (if j = k then 1 else 0) + (κ : ℂ) ^ 2) := by
  by_cases h : j = k
  · subst k; rw [c.gram_seed_diagonal L hm hκ]; simp
  · rw [c.gram_seed_offdiagonal L hm hκ j k h]; simp [h]

end SchauderTranslates.SeedCarrier
