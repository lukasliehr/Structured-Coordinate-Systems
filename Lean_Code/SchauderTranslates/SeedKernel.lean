import Lean_Code.SchauderTranslates.SeedProduct

noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Rescale the seed product to an arbitrary permitted positive conditional mass. -/
def seedKernel (L : ℕ) (m : ℝ) (a : ℂ) (z : UnitAddTorus (Fin L)) : ℝ :=
  (m / (1 / 2 : ℝ) ^ L) * seedProduct L a z

theorem seedKernel_continuous (L : ℕ) (m : ℝ) (a : ℂ) : Continuous (seedKernel L m a) :=
  continuous_const.mul (seedProduct_continuous L a)

theorem seedKernel_bounds (L : ℕ) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ (1 / 2 : ℝ) ^ L)
    {a : ℂ} (ha : ‖a‖ ≤ 1 / 4) (z : UnitAddTorus (Fin L)) :
    0 < seedKernel L m a z ∧ seedKernel L m a z ≤ 1 := by
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ L := by positivity
  have hscale : m / (1 / 2 : ℝ) ^ L ≤ 1 := (div_le_one hp).mpr hm1
  have hb := seedProduct_bounds L ha z
  exact ⟨mul_pos (div_pos hm hp) hb.1, mul_le_one₀ hscale hb.1.le hb.2⟩

@[simp] theorem seedKernel_integral (L : ℕ) (m : ℝ) (a : ℂ) :
    (∫ z, seedKernel L m a z ∂torusMeasure L) = m := by
  have hp : (1 / 2 : ℝ) ^ L ≠ 0 := by positivity
  simp only [seedKernel]
  rw [integral_const_mul, seedProduct_integral, div_mul_cancel₀ _ hp]

theorem seedKernel_first_moment (L : ℕ) (m : ℝ) (a : ℂ) (j : Fin L) :
    (∫ z, (seedKernel L m a z : ℂ) * fourier (1 : ℤ) (z j) ∂torusMeasure L) = (m : ℂ) * a := by
  simp only [seedKernel, Complex.ofReal_mul, mul_assoc]
  rw [integral_const_mul, seedProduct_first_moment]
  have hp : (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1 / 2 : ℝ) ^ L ≠ 0)
  rw [Complex.ofReal_div]
  field_simp
  simp only [Complex.ofReal_pow]

theorem seedKernel_cross_moment (L : ℕ) (m : ℝ) (a : ℂ) (j k : Fin L) (hjk : j ≠ k) :
    (∫ z, (seedKernel L m a z : ℂ) *
      (fourier (1 : ℤ) (z j) * star (fourier (1 : ℤ) (z k))) ∂torusMeasure L) =
      (m : ℂ) * (‖a‖ ^ 2 : ℝ) := by
  simp only [seedKernel, Complex.ofReal_mul, mul_assoc]
  rw [integral_const_mul, seedProduct_cross_moment L a j k hjk]
  have hp : (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1 / 2 : ℝ) ^ L ≠ 0)
  rw [Complex.ofReal_div]
  field_simp
  simp only [Complex.ofReal_pow]

/-- The normalized conditional first moment has no remaining mass factor. -/
theorem seedKernel_normalized_first (L : ℕ) {m : ℝ} (hm : m ≠ 0) (a : ℂ) (j : Fin L) :
    (∫ z, (seedKernel L m a z : ℂ) * fourier (1 : ℤ) (z j) ∂torusMeasure L) / (m : ℂ) = a := by
  rw [seedKernel_first_moment]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  field_simp

theorem seedKernel_normalized_cross (L : ℕ) {m : ℝ} (hm : m ≠ 0) (a : ℂ)
    (j k : Fin L) (hjk : j ≠ k) :
    (∫ z, (seedKernel L m a z : ℂ) *
      (fourier (1 : ℤ) (z j) * star (fourier (1 : ℤ) (z k))) ∂torusMeasure L) / (m : ℂ) =
      (‖a‖ ^ 2 : ℝ) := by
  rw [seedKernel_cross_moment L m a j k hjk]
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  field_simp

end SchauderTranslates
