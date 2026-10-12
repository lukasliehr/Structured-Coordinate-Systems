import Lean_Code.SchauderTranslates.CircleFejerKernel

noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- One seed phase, whose normalized first moment is the prescribed small complex number. -/
def seedFactor (a : ℂ) (x : UnitAddCircle) : ℝ :=
  1 / 2 + (a * star (fourier (1 : ℤ) x)).re

theorem seedFactor_bounds {a : ℂ} (ha : ‖a‖ ≤ 1 / 4) (x : UnitAddCircle) :
    1 / 4 ≤ seedFactor a x ∧ seedFactor a x ≤ 3 / 4 := by
  have hn : ‖a * star (fourier (1 : ℤ) x)‖ = ‖a‖ := by simp
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hn.le.trans ha)))
  change (1 / 4 : ℝ) ≤ 1 / 2 + (a * star (fourier (1 : ℤ) x)).re ∧
    1 / 2 + (a * star (fourier (1 : ℤ) x)).re ≤ 3 / 4
  constructor <;> linarith

theorem seedFactor_continuous (a : ℂ) : Continuous (seedFactor a) := by
  unfold seedFactor
  fun_prop

theorem seedFactor_integrable (a : ℂ) : Integrable (seedFactor a) (AddCircle.haarAddCircle (T := 1)) :=
  (seedFactor_continuous a).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The factor is a three-term Fourier polynomial. -/
theorem seedFactor_expansion (a : ℂ) (x : UnitAddCircle) :
    (seedFactor a x : ℂ) = 1 / 2 + (a / 2) * fourier (-1 : ℤ) x +
      (star a / 2) * fourier (1 : ℤ) x := by
  simp only [seedFactor, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.re_eq_add_conj, fourier_neg, Complex.star_def,
    map_mul, Complex.conj_conj]
  ring

/-- All signed Fourier moments follow from the three-term expansion. -/
theorem seedFactor_fourier (a : ℂ) (k : ℤ) :
    (∫ x : UnitAddCircle, (seedFactor a x : ℂ) * fourier k x ∂AddCircle.haarAddCircle) =
      (1 / 2 : ℂ) * (if k = 0 then 1 else 0) +
        (a / 2) * (if k - 1 = 0 then 1 else 0) +
        (star a / 2) * (if k + 1 = 0 then 1 else 0) := by
  have he (x : UnitAddCircle) : (seedFactor a x : ℂ) * fourier k x =
      (1 / 2 : ℂ) * fourier k x + (a / 2) * fourier (k - 1) x +
        (star a / 2) * fourier (k + 1) x := by
    rw [seedFactor_expansion]
    simp only [add_mul, mul_assoc, ← fourier_add]
    rw [show (-1 : ℤ) + k = k - 1 by omega, show (1 : ℤ) + k = k + 1 by omega]
  have hi (j : ℤ) : Integrable (fourier j : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
    (fourier j).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [he]
  have h01 : Integrable (fun x : UnitAddCircle => (1 / 2 : ℂ) * fourier k x +
      (a / 2) * fourier (k - 1) x) AddCircle.haarAddCircle :=
    ((hi k).const_mul (1 / 2 : ℂ)).add ((hi (k - 1)).const_mul (a / 2))
  rw [integral_add h01
    ((hi (k + 1)).const_mul (star a / 2)), integral_add ((hi k).const_mul (1 / 2 : ℂ))
      ((hi (k - 1)).const_mul (a / 2))]
  simp_rw [integral_const_mul, integral_circle_character]

@[simp] theorem seedFactor_integral (a : ℂ) :
    (∫ x : UnitAddCircle, seedFactor a x ∂AddCircle.haarAddCircle) = 1 / 2 := by
  have h := seedFactor_fourier a 0
  simp only [fourier_zero, mul_one] at h
  norm_num at h
  have hr := congrArg Complex.re h
  rw [integral_complex_ofReal] at hr
  simpa using hr

@[simp] theorem seedFactor_first_moment (a : ℂ) :
    (∫ x : UnitAddCircle, (seedFactor a x : ℂ) * fourier (1 : ℤ) x ∂AddCircle.haarAddCircle) = a / 2 := by
  simpa using seedFactor_fourier a 1

@[simp] theorem seedFactor_conjugate_moment (a : ℂ) :
    (∫ x : UnitAddCircle, (seedFactor a x : ℂ) * star (fourier (1 : ℤ) x) ∂AddCircle.haarAddCircle) =
      star a / 2 := by
  have h : (∫ x : UnitAddCircle, (seedFactor a x : ℂ) * fourier (-1 : ℤ) x ∂AddCircle.haarAddCircle) =
      star a / 2 := by
    rw [seedFactor_fourier]
    norm_num
  simpa only [fourier_neg, Complex.star_def] using h

end SchauderTranslates
