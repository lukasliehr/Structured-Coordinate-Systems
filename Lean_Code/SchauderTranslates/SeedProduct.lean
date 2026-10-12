import Lean_Code.SchauderTranslates.SeedFactor
import Lean_Code.SchauderTranslates.FejerMoments

noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

def seedProduct (L : ℕ) (a : ℂ) (z : UnitAddTorus (Fin L)) : ℝ :=
  ∏ i : Fin L, seedFactor a (z i)

theorem seedProduct_continuous (L : ℕ) (a : ℂ) : Continuous (seedProduct L a) := by
  unfold seedProduct seedFactor
  fun_prop

theorem seedProduct_bounds (L : ℕ) {a : ℂ} (ha : ‖a‖ ≤ 1 / 4) (z : UnitAddTorus (Fin L)) :
    0 < seedProduct L a z ∧ seedProduct L a z ≤ 1 := by
  constructor
  · exact Finset.prod_pos (fun i _ => lt_of_lt_of_le (by norm_num) (seedFactor_bounds ha (z i)).1)
  · exact Finset.prod_le_one (fun i _ => (lt_of_lt_of_le (by norm_num) (seedFactor_bounds ha (z i)).1).le)
      (fun i _ => (seedFactor_bounds ha (z i)).2.trans (by norm_num))

@[simp] theorem seedProduct_integral (L : ℕ) (a : ℂ) :
    (∫ z, seedProduct L a z ∂torusMeasure L) = (1 / 2 : ℝ) ^ L := by
  change (∫ z : Fin L → UnitAddCircle, ∏ i, seedFactor a (z i)
    ∂Measure.pi (fun _ : Fin L => AddCircle.haarAddCircle)) = _
  rw [integral_fintype_prod_eq_prod]
  simp

/-- Independence factors every raw character moment into the one-phase moments. -/
theorem seedProduct_character_moment (L : ℕ) (a : ℂ) (k : Fin L → ℤ) :
    (∫ z, (seedProduct L a z : ℂ) * UnitAddTorus.mFourier k z ∂torusMeasure L) =
      ∏ i : Fin L, ∫ x : UnitAddCircle, (seedFactor a x : ℂ) * fourier (k i) x ∂AddCircle.haarAddCircle := by
  have he (z : UnitAddTorus (Fin L)) : (seedProduct L a z : ℂ) * UnitAddTorus.mFourier k z =
      ∏ i : Fin L, (seedFactor a (z i) : ℂ) * fourier (k i) (z i) := by
    simp only [seedProduct, Complex.ofReal_prod, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      Finset.prod_mul_distrib]
  simp_rw [he]
  exact integral_fintype_prod_eq_prod (fun (i : Fin L) (x : UnitAddCircle) =>
    (seedFactor a x : ℂ) * fourier (k i) x)
    (μ := fun _ : Fin L => AddCircle.haarAddCircle)

theorem seedProduct_first_moment (L : ℕ) (a : ℂ) (j : Fin L) :
    (∫ z, (seedProduct L a z : ℂ) * fourier (1 : ℤ) (z j) ∂torusMeasure L) =
      ((1 / 2 : ℝ) ^ L : ℂ) * a := by
  have h := seedProduct_character_moment L a (Pi.single j 1)
  simp only [UnitAddTorus.mFourier_single] at h
  rw [h]
  have hi (i : Fin L) :
      (∫ x : UnitAddCircle, (seedFactor a x : ℂ) * fourier ((Pi.single j 1 : Fin L → ℤ) i) x ∂AddCircle.haarAddCircle) =
        (1 / 2 : ℂ) * (if i = j then a else 1) := by
    by_cases hij : i = j
    · subst i
      simp only [Pi.single_eq_same, seedFactor_first_moment, if_true]
      ring
    · simp only [Pi.single_eq_of_ne hij, seedFactor_fourier, hij, if_false]
      norm_num
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_ite_eq', Complex.ofReal_pow]

theorem seedProduct_cross_moment (L : ℕ) (a : ℂ) (j k : Fin L) (hjk : j ≠ k) :
    (∫ z, (seedProduct L a z : ℂ) *
      (fourier (1 : ℤ) (z j) * star (fourier (1 : ℤ) (z k))) ∂torusMeasure L) =
      ((1 / 2 : ℝ) ^ L : ℂ) * (‖a‖ ^ 2 : ℝ) := by
  have h := seedProduct_character_moment L a (Pi.single j 1 - Pi.single k 1)
  have hchar (z : UnitAddTorus (Fin L)) : UnitAddTorus.mFourier (Pi.single j 1 - Pi.single k 1) z =
      fourier (1 : ℤ) (z j) * star (fourier (1 : ℤ) (z k)) := by
    rw [sub_eq_add_neg, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_neg,
      UnitAddTorus.mFourier_single, UnitAddTorus.mFourier_single]
    rfl
  simp_rw [hchar] at h
  rw [h]
  have hi (i : Fin L) :
      (∫ x : UnitAddCircle, (seedFactor a x : ℂ) *
        fourier ((Pi.single j 1 - Pi.single k 1 : Fin L → ℤ) i) x ∂AddCircle.haarAddCircle) =
        (1 / 2 : ℂ) * (if i = j then a else 1) * (if i = k then star a else 1) := by
    by_cases hij : i = j
    · subst i
      simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hjk, sub_zero,
        seedFactor_first_moment, if_true, hjk, if_false, mul_one]
      ring
    · by_cases hik : i = k
      · subst i
        simp only [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hjk), zero_sub,
          seedFactor_fourier, hij, if_false, if_true, mul_one]
        norm_num
        ring
      · simp only [Pi.sub_apply, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hik, sub_self,
          seedFactor_fourier, hij, hik, if_false, mul_one]
        norm_num
  simp_rw [hi]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  rw [mul_assoc, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow]
  push_cast
  ring

end SchauderTranslates
