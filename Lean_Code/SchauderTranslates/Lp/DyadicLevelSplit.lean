import Lean_Code.SchauderTranslates.Lp.HaarWeak

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def dyadicLargeCoefficients {N : ℕ} (c : Fin (2 ^ N) → ℂ) (a : ℝ) (k : Fin (2 ^ N)) : ℂ :=
  if a < ‖c k‖ then c k else 0

def dyadicSmallCoefficients {N : ℕ} (c : Fin (2 ^ N) → ℂ) (a : ℝ) (k : Fin (2 ^ N)) : ℂ :=
  if ‖c k‖ ≤ a then c k else 0

theorem dyadic_coefficients_split {N : ℕ} (c : Fin (2 ^ N) → ℂ) (a : ℝ) (k : Fin (2 ^ N)) :
    dyadicLargeCoefficients c a k + dyadicSmallCoefficients c a k = c k := by
  by_cases h : a < ‖c k‖
  · simp [dyadicLargeCoefficients, dyadicSmallCoefficients, h, not_le.mpr h]
  · simp [dyadicLargeCoefficients, dyadicSmallCoefficients, h, le_of_not_gt h]

theorem haarDyadicStep_split (p : ℝ≥0∞) (N : ℕ) (c : Fin (2 ^ N) → ℂ) (a : ℝ) :
    haarDyadicStep p N c = haarDyadicStep p N (dyadicLargeCoefficients c a) +
      haarDyadicStep p N (dyadicSmallCoefficients c a) := by
  rw [haarDyadicStep, haarDyadicStep, haarDyadicStep, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by rw [← add_smul, dyadic_coefficients_split])

theorem dyadicStepValue_measurable (N : ℕ) (c : Fin (2 ^ N) → ℂ) :
    Measurable (dyadicStepValue N c) :=
  Finset.measurable_sum _ (fun k _ => measurable_const.mul
    (measurable_const.indicator (dyadicInterval_measurable N k)))

theorem dyadicStepValue_large_indicator (N : ℕ) (c : Fin (2 ^ N) → ℂ) {a : ℝ} (ha : 0 < a) :
    dyadicStepValue N (dyadicLargeCoefficients c a) =
      {x | a < ‖dyadicStepValue N c x‖}.indicator (dyadicStepValue N c) := by
  funext x
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · obtain ⟨k, hk, hxk⟩ := dyadicInterval_unit_cover N hx
    let i : Fin (2 ^ N) := ⟨k, hk⟩
    rw [dyadicStepValue_on_cell N _ i hxk]
    by_cases h : a < ‖c i‖
    · have hxlarge : x ∈ {x | a < ‖dyadicStepValue N c x‖} := by
        simpa only [Set.mem_ofPred_eq, dyadicStepValue_on_cell N c i hxk] using h
      rw [Set.indicator_of_mem hxlarge, dyadicStepValue_on_cell N c i hxk]
      simp [dyadicLargeCoefficients, h]
    · have hxsmall : x ∉ {x | a < ‖dyadicStepValue N c x‖} := by
        simpa only [Set.mem_ofPred_eq, dyadicStepValue_on_cell N c i hxk] using h
      rw [Set.indicator_of_notMem hxsmall]
      simp [dyadicLargeCoefficients, h]
  · rw [dyadicStepValue_zero_outside_unit N _ hx]
    have hout : x ∉ {x | a < ‖dyadicStepValue N c x‖} := by
      simp [dyadicStepValue_zero_outside_unit N c hx, ha.le.not_gt]
    rw [Set.indicator_of_notMem hout]

theorem dyadicStepValue_small_indicator (N : ℕ) (c : Fin (2 ^ N) → ℂ) (a : ℝ) :
    dyadicStepValue N (dyadicSmallCoefficients c a) =
      {x | ‖dyadicStepValue N c x‖ ≤ a}.indicator (dyadicStepValue N c) := by
  funext x
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · obtain ⟨k, hk, hxk⟩ := dyadicInterval_unit_cover N hx
    let i : Fin (2 ^ N) := ⟨k, hk⟩
    rw [dyadicStepValue_on_cell N _ i hxk]
    by_cases h : ‖c i‖ ≤ a
    · have hxsmall : x ∈ {x | ‖dyadicStepValue N c x‖ ≤ a} := by
        simpa only [Set.mem_ofPred_eq, dyadicStepValue_on_cell N c i hxk] using h
      rw [Set.indicator_of_mem hxsmall, dyadicStepValue_on_cell N c i hxk]
      simp [dyadicSmallCoefficients, h]
    · have hxlarge : x ∉ {x | ‖dyadicStepValue N c x‖ ≤ a} := by
        simpa only [Set.mem_ofPred_eq, dyadicStepValue_on_cell N c i hxk] using h
      rw [Set.indicator_of_notMem hxlarge]
      simp [dyadicSmallCoefficients, h]
  · rw [dyadicStepValue_zero_outside_unit N _ hx]
    exact (Set.indicator_apply_eq_zero.mpr (fun _ => dyadicStepValue_zero_outside_unit N c hx)).symm

theorem dyadic_large_norm_integral (N : ℕ) (c : Fin (2 ^ N) → ℂ) {a : ℝ} (ha : 0 < a) :
    ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖ =
      ∫ x in {x | a < ‖dyadicStepValue N c x‖}, ‖dyadicStepValue N c x‖ ∂haarMeasure := by
  rw [← dyadicStepValue_norm_integral, dyadicStepValue_large_indicator N c ha]
  simp_rw [norm_indicator_eq_indicator_norm]
  exact integral_indicator (measurableSet_lt measurable_const (dyadicStepValue_measurable N c).norm)

theorem dyadic_small_square_integral (N : ℕ) (c : Fin (2 ^ N) → ℂ) (a : ℝ) :
    ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a)‖ ^ 2 =
      ∫ x in {x | ‖dyadicStepValue N c x‖ ≤ a}, ‖dyadicStepValue N c x‖ ^ 2 ∂haarMeasure := by
  rw [← haar_l2_square_integral]
  have hi : (∫ x, ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a) x‖ ^ 2 ∂haarMeasure) =
      ∫ x, ‖dyadicStepValue N (dyadicSmallCoefficients c a) x‖ ^ 2 ∂haarMeasure := by
    simpa only [Function.comp_def] using integral_congr_ae
      ((haarDyadicStep_ae_value 2 N (dyadicSmallCoefficients c a)).fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  rw [hi, dyadicStepValue_small_indicator]
  have he : (fun x => ‖({x | ‖dyadicStepValue N c x‖ ≤ a}.indicator (dyadicStepValue N c)) x‖ ^ 2) =
      {x | ‖dyadicStepValue N c x‖ ≤ a}.indicator (fun x => ‖dyadicStepValue N c x‖ ^ 2) := by
    funext x
    by_cases hx : ‖dyadicStepValue N c x‖ ≤ a <;> simp [hx]
  rw [he, integral_indicator (measurableSet_le (dyadicStepValue_measurable N c).norm measurable_const)]

end SchauderTranslates.LpConstruction
