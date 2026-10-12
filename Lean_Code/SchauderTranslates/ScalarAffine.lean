import Lean_Code.SchauderTranslates.ScalarFejerLimits
import Lean_Code.SchauderTranslates.TorusPolynomialAlgebra

noncomputable section
open MeasureTheory Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {d : ℕ}

/-- The Haar Fourier moment of the constant density, with the same conjugation convention. -/
theorem torusFourierMoment_one (k : Fin d → ℤ) :
    torusFourierMoment (fun _ => (1 : ℂ)) k = if k = 0 then 1 else 0 := by
  classical
  unfold torusFourierMoment
  simp only [one_mul, Complex.star_def, ← UnitAddTorus.mFourier_neg]
  rw [integral_torus_character]
  simp

theorem torusFourierMoment_affine (w : TorusWeight d) (θ : ℝ) (k : Fin d → ℤ) :
    torusFourierMoment (fun x => ((1 - θ + θ * w.density x : ℝ) : ℂ)) k =
      ((1 - θ : ℝ) : ℂ) * (if k = 0 then 1 else 0) +
        (θ : ℂ) * torusFourierMoment (fun x => (w.density x : ℂ)) k := by
  classical
  have h1 := integrable_torusFourierTwist (integrable_const (1 : ℂ)) k
  simp only [one_mul] at h1
  have hw : Integrable (fun x => (w.density x : ℂ) * star (UnitAddTorus.mFourier k x)) (torusMeasure d) :=
    integrable_torusFourierTwist (w.integrable.ofReal (𝕜 := ℂ)) k
  unfold torusFourierMoment
  simp only [Complex.ofReal_add, Complex.ofReal_mul, add_mul, mul_assoc]
  rw [integral_add (h1.const_mul ((1 - θ : ℝ) : ℂ)) (hw.const_mul (θ : ℂ)),
    integral_const_mul, integral_const_mul]
  have he := torusFourierMoment_one k
  simp only [torusFourierMoment, one_mul] at he
  rw [he]

namespace ScalarData
variable {n : ℕ}

/-- Affine path from the Haar density to the given block, with the character order fixed. -/
def affine (s : ScalarData d n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : ScalarData d n where
  density x := 1 - θ + θ * s.density x
  measurable := measurable_const.add (measurable_const.mul s.measurable)
  positive x := by
    by_cases hθ : θ = 0
    · simp [hθ]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr h1) (mul_pos (lt_of_le_of_ne h0 (Ne.symm hθ)) (s.positive x))
  le_one x := by nlinarith [s.le_one x]
  frequencies := s.frequencies
  injective := s.injective
  nonconstant := s.nonconstant

@[simp] theorem affine_mass (s : ScalarData d n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (s.affine θ h0 h1).mass = 1 - θ + θ * s.mass := by
  change (∫ x, 1 - θ + θ * s.density x ∂torusMeasure d) = _
  rw [integral_add (integrable_const _) (s.toTorusWeight.integrable.const_mul θ), integral_const_mul]
  simp [TorusWeight.mass]

theorem affine_even (s : ScalarData d n) (hs : s.IsEven) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (s.affine θ h0 h1).IsEven := by
  intro x
  change 1 - θ + θ * s.density (-x) = _
  rw [hs]
  rfl

theorem affine_floor (s : ScalarData d n) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x, b ≤ s.density x) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ∀ x, b ≤ (s.affine θ h0 h1).density x := by
  intro x
  have hb1 : b ≤ 1 := (hf x).trans (s.le_one x)
  have hθb := mul_le_mul_of_nonneg_left (hf x) h0
  change b ≤ 1 - θ + θ * s.density x
  nlinarith

theorem affine_polynomial (s : ScalarData d n) (hs : s.IsPolynomial)
    (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : (s.affine θ h0 h1).IsPolynomial := by
  have h := (IsTorusPolynomial.const ((1 - θ : ℝ) : ℂ)).add
    ((show IsTorusPolynomial (fun x => (s.density x : ℂ)) from hs).const_mul (θ : ℂ))
  simpa only [IsPolynomial, IsTorusPolynomial, affine, Complex.ofReal_add, Complex.ofReal_mul] using h

/-- The Gram along the affine density path, defined at every real parameter for continuity. -/
def affineGram (s : ScalarData d n) (θ : ℝ) : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) ℂ :=
  (1 - θ) • 1 + θ • s.rawGram

theorem affine_rawGram (s : ScalarData d n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (s.affine θ h0 h1).rawGram = s.affineGram θ := by
  classical
  ext i j
  rw [rawGram_moment]
  change torusFourierMoment (fun x => ((1 - θ + θ * s.density x : ℝ) : ℂ))
    (s.augmentedFrequency i - s.augmentedFrequency j) = _
  rw [torusFourierMoment_affine]
  simp only [affineGram, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
    Matrix.one_apply, rawGram_moment, sub_eq_zero, s.augmentedFrequency_injective.eq_iff]

end ScalarData
end SchauderTranslates
