import Lean_Code.SchauderTranslates.Lp.HaarInterpolationPowers

noncomputable section
open MeasureTheory Filter

namespace SchauderTranslates.LpConstruction

theorem haar_low_weight_integral {s r : ℝ} (hs : 1 < s) (hr : 0 ≤ r) :
    (∫ a in Set.Ioi (0 : ℝ), a ^ (s - 2) * (if a < r then r else 0)) =
      r ^ s / (s - 1) := by
  by_cases hr0 : r = 0
  · subst r
    simp [Real.zero_rpow (by linarith : s ≠ 0)]
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have he : (fun a : ℝ => a ^ (s - 2) * (if a < r then r else 0)) =
      (fun a => r * (Set.Iio r).indicator (fun a : ℝ => a ^ (s - 2)) a) := by
    funext a
    by_cases h : a < r <;> simp [h, mul_comm]
  have hset : Set.Iio r ∩ Set.Ioi (0 : ℝ) = Set.Ioo 0 r := by ext a; simp [and_comm]
  rw [he, integral_const_mul, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, hset, haar_interpolation_low_integral hs hr,
    ← mul_div_assoc]
  congr 1
  calc
    _ = r ^ (1 : ℝ) * r ^ (s - 1) := by rw [Real.rpow_one]
    _ = r ^ (1 + (s - 1)) := (Real.rpow_add hrpos _ _).symm
    _ = r ^ s := by congr 1; ring

theorem haar_low_weight_integrable {s r : ℝ} (hs : 1 < s) :
    IntegrableOn (fun a : ℝ => a ^ (s - 2) * (if a < r then r else 0)) (Set.Ioi 0) := by
  have hset : Set.Iio r ∩ Set.Ioi (0 : ℝ) = Set.Ioo 0 r := by ext a; simp [and_comm]
  have hi : IntegrableOn ((Set.Iio r).indicator (fun a : ℝ => a ^ (s - 2))) (Set.Ioi 0) :=
    (integrableOn_indicator_iff measurableSet_Iio).mpr (hset ▸ haar_interpolation_low_integrable hs)
  apply IntegrableOn.congr_fun (hi.const_mul r) _ measurableSet_Ioi
  intro a _
  by_cases h : a < r <;> simp [h, mul_comm]

theorem haar_high_weight_integral {s r : ℝ} (hs : s < 2) (hr : 0 ≤ r) (hspos : 0 < s) :
    (∫ a in Set.Ioi (0 : ℝ), a ^ (s - 3) * (if r ≤ a then r ^ 2 else 0)) =
      r ^ s / (2 - s) := by
  by_cases hr0 : r = 0
  · subst r
    simp [Real.zero_rpow hspos.ne']
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have he : (fun a : ℝ => a ^ (s - 3) * (if r ≤ a then r ^ 2 else 0)) =
      (fun a => r ^ 2 * (Set.Ici r).indicator (fun a : ℝ => a ^ (s - 3)) a) := by
    funext a
    by_cases h : r ≤ a <;> simp [h, mul_comm]
  have hset : Set.Ici r ∩ Set.Ioi (0 : ℝ) = Set.Ici r :=
    Set.inter_eq_left.mpr (fun _ hx => hrpos.trans_le hx)
  rw [he, integral_const_mul, integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, hset, integral_Ici_eq_integral_Ioi,
    haar_interpolation_high_integral hs hrpos, ← mul_div_assoc]
  congr 1
  calc
    _ = r ^ (2 : ℝ) * r ^ (s - 2) := by rw [Real.rpow_two]
    _ = r ^ (2 + (s - 2)) := (Real.rpow_add hrpos _ _).symm
    _ = r ^ s := by congr 1; ring

theorem haar_high_weight_integrable {s r : ℝ} (hs : s < 2) (hr : 0 ≤ r) :
    IntegrableOn (fun a : ℝ => a ^ (s - 3) * (if r ≤ a then r ^ 2 else 0)) (Set.Ioi 0) := by
  by_cases hr0 : r = 0
  · subst r
    simp
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hset : Set.Ici r ∩ Set.Ioi (0 : ℝ) = Set.Ici r :=
    Set.inter_eq_left.mpr (fun _ hx => hrpos.trans_le hx)
  have hbase : IntegrableOn (fun a : ℝ => a ^ (s - 3)) (Set.Ici r) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact haar_interpolation_high_integrable hs hrpos
  have hi : IntegrableOn ((Set.Ici r).indicator (fun a : ℝ => a ^ (s - 3))) (Set.Ioi 0) :=
    (integrableOn_indicator_iff measurableSet_Ici).mpr (by rw [hset]; exact hbase)
  apply IntegrableOn.congr_fun (hi.const_mul (r ^ 2)) _ measurableSet_Ioi
  intro a _
  by_cases h : r ≤ a <;> simp [h, mul_comm]

end SchauderTranslates.LpConstruction
