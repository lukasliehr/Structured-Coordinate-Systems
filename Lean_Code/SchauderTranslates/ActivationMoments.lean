import Lean_Code.SchauderTranslates.ActivationWeight
import Lean_Code.SchauderTranslates.ScalarOrder

noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Product of an old torus character with an arbitrary new circle mode. -/
def activationCharacter {d : ℕ} (k : Fin d → ℤ) (l : ℤ)
    (z : UnitAddTorus (Fin d) × UnitAddCircle) : ℂ :=
  UnitAddTorus.mFourier k z.1 * fourier l z.2

theorem activationCharacter_continuous {d : ℕ} (k : Fin d → ℤ) (l : ℤ) :
    Continuous (activationCharacter k l) := by
  unfold activationCharacter
  fun_prop

@[simp] theorem activationCharacter_norm {d : ℕ} (k : Fin d → ℤ) (l : ℤ)
    (z : UnitAddTorus (Fin d) × UnitAddCircle) : ‖activationCharacter k l z‖ = 1 := by
  simp [activationCharacter, fourier_apply]

theorem activationCharacter_neg {d : ℕ} (k : Fin d → ℤ) (l : ℤ)
    (z : UnitAddTorus (Fin d) × UnitAddCircle) :
    activationCharacter k l (-z) = star (activationCharacter k l z) := by
  simp only [activationCharacter, Prod.fst_neg, Prod.snd_neg, torus_character_neg_apply,
    fourier_apply, smul_neg, fourier_neg', map_mul, Complex.star_def]

instance activationMeasure_negInvariant (d : ℕ) :
    ((torusMeasure d).prod (AddCircle.haarAddCircle (T := 1))).IsNegInvariant := by
  constructor
  exact ((Measure.measurePreserving_neg (torusMeasure d)).prod
    (Measure.measurePreserving_neg (AddCircle.haarAddCircle (T := 1)))).map_eq

namespace ScalarData
variable {d n : ℕ}

/-- The actual product-weight Fourier Gram coefficient, with the constant old row included. -/
def activatedMoment (s : ScalarData d n) (p : ℝ)
    (i j : Unit ⊕ Fin n) (k l : ℤ) : ℂ :=
  ∫ z, (activatedDensity s.toTorusWeight p z : ℂ) *
    star (activationCharacter (s.augmentedFrequency i) k z) *
    activationCharacter (s.augmentedFrequency j) l z
    ∂((torusMeasure d).prod AddCircle.haarAddCircle)

theorem activatedMoment_integrable (s : ScalarData d n) (p : ℝ)
    (i j : Unit ⊕ Fin n) (k l : ℤ) :
    Integrable (fun z => (activatedDensity s.toTorusWeight p z : ℂ) *
      star (activationCharacter (s.augmentedFrequency i) k z) *
      activationCharacter (s.augmentedFrequency j) l z)
      ((torusMeasure d).prod AddCircle.haarAddCircle) := by
  apply Integrable.of_bound (C := 1)
  · exact ((Complex.continuous_ofReal.measurable.comp
      (activatedDensity_measurable s.toTorusWeight p)).mul
      (activationCharacter_continuous _ _).star.measurable |>.mul
      (activationCharacter_continuous _ _).measurable).aestronglyMeasurable
  · filter_upwards [] with z
    simp only [norm_mul, norm_star, activationCharacter_norm, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (activatedDensity_bounds s.toTorusWeight p z).1]
    exact (activatedDensity_bounds s.toTorusWeight p z).2

/-- Simultaneous inversion, rather than separate parity assumptions on each mode, gives reality. -/
theorem activatedMoment_real (s : ScalarData d n) (hs : s.IsEven) (p : ℝ)
    (i j : Unit ⊕ Fin n) (k l : ℤ) : (s.activatedMoment p i j k l).im = 0 := by
  apply integral_real_of_neg_conj
  intro z
  rw [activatedDensity_even s hs, activationCharacter_neg, activationCharacter_neg]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem rawGram_integral (s : ScalarData d n) (i j : Unit ⊕ Fin n) :
    (∫ x, (s.density x : ℂ) * star (UnitAddTorus.mFourier (s.augmentedFrequency i) x) *
      UnitAddTorus.mFourier (s.augmentedFrequency j) x ∂torusMeasure d) = s.rawGram i j :=
  (s.toTorusWeight.vector_inner _ _).symm

theorem haarGram_integral (s : ScalarData d n) (i j : Unit ⊕ Fin n) :
    (∫ x, star (UnitAddTorus.mFourier (s.augmentedFrequency i) x) *
      UnitAddTorus.mFourier (s.augmentedFrequency j) x ∂torusMeasure d) = if i = j then 1 else 0 := by
  have he := (unitTorusWeight d).vector_inner (s.augmentedFrequency i) (s.augmentedFrequency j)
  simp only [unitTorusWeight, Complex.ofReal_one, one_mul] at he
  rw [← he]
  exact orthonormal_iff_ite.mp
    (unitTorusWeight_orthonormal.comp s.augmentedFrequency s.augmentedFrequency_injective) i j

/-- Fubini identifies every Fourier matrix entry with the active/inactive row operator. -/
theorem activatedMoment_fubini (s : ScalarData d n) (p : ℝ)
    (i j : Unit ⊕ Fin n) (k l : ℤ) :
    s.activatedMoment p i j k l =
      ∫ y, (if y ∈ activationSet p then s.rawGram i j else if i = j then 1 else 0) *
        star (fourier k y) * fourier l y ∂AddCircle.haarAddCircle := by
  unfold activatedMoment
  rw [integral_prod_symm _ (s.activatedMoment_integrable p i j k l)]
  apply integral_congr_ae
  filter_upwards [] with y
  have he (x : UnitAddTorus (Fin d)) :
      (activatedDensity s.toTorusWeight p (x,y) : ℂ) *
        star (activationCharacter (s.augmentedFrequency i) k (x,y)) *
        activationCharacter (s.augmentedFrequency j) l (x,y) =
      ((activatedDensity s.toTorusWeight p (x,y) : ℂ) *
        star (UnitAddTorus.mFourier (s.augmentedFrequency i) x) *
        UnitAddTorus.mFourier (s.augmentedFrequency j) x) * star (fourier k y) * fourier l y := by
    simp only [activationCharacter, star_mul]
    ring
  simp_rw [he]
  rw [integral_mul_const, integral_mul_const]
  by_cases hy : y ∈ activationSet p
  · simp only [activatedDensity, hy, if_true, s.rawGram_integral]
  · simp only [activatedDensity, hy, if_false, Complex.ofReal_one, one_mul, s.haarGram_integral]

end ScalarData
end SchauderTranslates
