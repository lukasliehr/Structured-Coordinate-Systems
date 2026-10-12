import Lean_Code.SchauderTranslates.ProductCharacters

noncomputable section
open MeasureTheory Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

@[simp] theorem flattenFrequency_zero {L d : ℕ} :
    flattenFrequency (0 : Fin L → Fin d → ℤ) = 0 := rfl

namespace TorusWeight
variable {d : ℕ}

/-- A moment supported in one copy is unchanged after probability normalization. -/
theorem product_normalizedMoment_same (w : TorusWeight d) {L : ℕ} (i : Fin L)
    (k l : Fin d → ℤ) :
    (w.product L).normalizedMoment (copyFrequency i k) (copyFrequency i l) =
      w.normalizedMoment k l := by
  rw [copyFrequency, copyFrequency, product_normalizedMoment]
  apply (Finset.prod_eq_single i _ (by simp)).trans
  · simp
  · intro a _ hai
    simp [hai]

@[simp] theorem copyFrequency_zero {L : ℕ} (i : Fin L) :
    copyFrequency i (0 : Fin d → ℤ) = 0 := by
  simp only [copyFrequency, ite_self, ← Pi.zero_def, flattenFrequency_zero]

theorem product_normalizedMoment_left (w : TorusWeight d) {L : ℕ} (i : Fin L)
    (k : Fin d → ℤ) :
    (w.product L).normalizedMoment (copyFrequency i k) 0 = w.normalizedMoment k 0 := by
  simpa only [copyFrequency_zero] using w.product_normalizedMoment_same i k 0

theorem product_normalizedMoment_right (w : TorusWeight d) {L : ℕ} (i : Fin L)
    (l : Fin d → ℤ) :
    (w.product L).normalizedMoment 0 (copyFrequency i l) = w.normalizedMoment 0 l := by
  simpa only [copyFrequency_zero] using w.product_normalizedMoment_same i 0 l

/-- Mixed-copy moments factor into their two means. -/
theorem product_normalizedMoment_ne (w : TorusWeight d) {L : ℕ} {i j : Fin L}
    (hij : i ≠ j) (k l : Fin d → ℤ) :
    (w.product L).normalizedMoment (copyFrequency i k) (copyFrequency j l) =
      w.normalizedMoment k 0 * w.normalizedMoment 0 l := by
  rw [copyFrequency, copyFrequency, product_normalizedMoment]
  have h (a : Fin L) :
      w.normalizedMoment (if a = i then k else 0) (if a = j then l else 0) =
        (if a = i then w.normalizedMoment k 0 else 1) *
        (if a = j then w.normalizedMoment 0 l else 1) := by
    by_cases hi : a = i
    · subst a
      simp [hij]
    · by_cases hj : a = j
      · subst a
        simp [hi]
      · simp [hi, hj]
  simp_rw [h, Finset.prod_mul_distrib]
  simp

end TorusWeight

namespace ScalarData
variable {d n : ℕ}

theorem normalizedMoment_mean (s : ScalarData d n) (a : Fin n) :
    s.normalizedMoment (s.frequencies a) 0 = s.mean a := rfl

theorem normalizedMoment_conj_mean (s : ScalarData d n) (a : Fin n) :
    s.normalizedMoment 0 (s.frequencies a) = star (s.mean a) := by
  rw [← s.normalizedMoment_mean a]
  simp only [TorusWeight.normalizedMoment, star_mul, star_inv₀,
    Complex.star_def, Complex.conj_ofReal, inner_conj_symm]
  rw [← inner_conj_symm]
  ring

theorem centeredGram_normalizedMoment (s : ScalarData d n) (a b : Fin n) :
    s.centeredGram a b = s.normalizedMoment (s.frequencies a) (s.frequencies b) -
      s.mean a * star (s.mean b) := by
  simp only [centeredGram, rawCenteredGram, nonconstantGram, mean,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.submatrix_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul, star_inv₀, Complex.star_def, Complex.conj_ofReal,
    TorusWeight.normalizedMoment]
  change (s.mass : ℂ)⁻¹ * (inner ℂ (s.vector (s.frequencies a))
    (s.vector (s.frequencies b)) - (s.mass : ℂ)⁻¹ * (s.moment a * star (s.moment b))) = _
  simp only [Complex.star_def]
  ring

/-- Every copy has exactly the same normalized mean vector. -/
theorem product_mean (s : ScalarData d n) (L : ℕ) (i : Fin L) (a : Fin n) :
    (s.product L).mean (finProdFinEquiv (i, a)) = s.mean a := by
  rw [← normalizedMoment_mean, product_frequency]
  exact s.toTorusWeight.product_normalizedMoment_left i (s.frequencies a)

/-- The actual centered Gram, including all cross-copy zero entries. -/
theorem product_centeredGram_entry (s : ScalarData d n) (L : ℕ)
    (i j : Fin L) (a b : Fin n) :
    (s.product L).centeredGram (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      if i = j then s.centeredGram a b else 0 := by
  rw [centeredGram_normalizedMoment, product_frequency, product_frequency,
    product_mean, product_mean]
  change (s.toTorusWeight.product L).normalizedMoment (copyFrequency i (s.frequencies a))
    (copyFrequency j (s.frequencies b)) - s.mean a * star (s.mean b) = _
  by_cases hij : i = j
  · subst j
    rw [s.toTorusWeight.product_normalizedMoment_same]
    simp only [ite_true, s.centeredGram_normalizedMoment]
  · rw [s.toTorusWeight.product_normalizedMoment_ne hij,
      s.normalizedMoment_mean, s.normalizedMoment_conj_mean]
    simp [hij]

end ScalarData
end SchauderTranslates
