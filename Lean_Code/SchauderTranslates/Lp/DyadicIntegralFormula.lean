import Lean_Code.SchauderTranslates.Lp.DyadicLevelSplit

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem dyadic_transform_ae (N : ℕ) (c : Fin (2 ^ N) → ℂ) (Φ : ℂ → ℝ) :
    (fun x => Φ (dyadicStepValue N c x)) =ᵐ[haarMeasure]
      (fun x => ∑ k : Fin (2 ^ N), (dyadicInterval N k).indicator (fun _ => Φ (c k)) x) := by
  classical
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ico] with x hx
  obtain ⟨k, hk, hxk⟩ := dyadicInterval_unit_cover N hx
  let i : Fin (2 ^ N) := ⟨k, hk⟩
  rw [dyadicStepValue_on_cell N c i hxk, Finset.sum_eq_single i]
  · simp [i, hxk]
  · intro j _ hji
    have hne : (j : ℕ) ≠ i := fun he => hji (Fin.ext he)
    have hxj : x ∉ dyadicInterval N j := fun h =>
      Set.disjoint_left.mp (dyadicInterval_disjoint_same N hne) h hxk
    simp [hxj]
  · simp

/-- A finite dyadic partition gives an exact integral formula for any
real transform of its finitely many complex values. No continuity of
the transform is needed. -/
theorem dyadic_transform_integral (N : ℕ) (c : Fin (2 ^ N) → ℂ) (Φ : ℂ → ℝ) :
    (∫ x, Φ (dyadicStepValue N c x) ∂haarMeasure) =
      ∑ k : Fin (2 ^ N), haarMeasure.real (dyadicInterval N k) * Φ (c k) := by
  rw [integral_congr_ae (dyadic_transform_ae N c Φ), integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_indicator (dyadicInterval_measurable N k), setIntegral_const, smul_eq_mul]
  · exact fun k _ => (integrable_const _).indicator (dyadicInterval_measurable N k)

theorem dyadic_transform_integrable (N : ℕ) (c : Fin (2 ^ N) → ℂ) (Φ : ℂ → ℝ) :
    Integrable (fun x => Φ (dyadicStepValue N c x)) haarMeasure :=
  (integrable_finsetSum Finset.univ (fun k _ =>
    (integrable_const (Φ (c k))).indicator (dyadicInterval_measurable N k))).congr
      (dyadic_transform_ae N c Φ).symm

theorem dyadic_norm_power_integral (N : ℕ) (c : Fin (2 ^ N) → ℂ) (s : ℝ) :
    (∫ x, ‖dyadicStepValue N c x‖ ^ s ∂haarMeasure) =
      ∑ k : Fin (2 ^ N), haarMeasure.real (dyadicInterval N k) * ‖c k‖ ^ s :=
  dyadic_transform_integral N c (fun z => ‖z‖ ^ s)

theorem dyadic_large_norm_finite_sum (N : ℕ) (c : Fin (2 ^ N) → ℂ) (a : ℝ) :
    ‖haarDyadicStep 1 N (dyadicLargeCoefficients c a)‖ =
      ∑ k : Fin (2 ^ N), haarMeasure.real (dyadicInterval N k) * (if a < ‖c k‖ then ‖c k‖ else 0) := by
  rw [← dyadicStepValue_norm_integral, dyadic_transform_integral]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : a < ‖c k‖ <;> simp [dyadicLargeCoefficients, h]

theorem dyadic_small_square_finite_sum (N : ℕ) (c : Fin (2 ^ N) → ℂ) (a : ℝ) :
    ‖haarDyadicStep 2 N (dyadicSmallCoefficients c a)‖ ^ 2 =
      ∑ k : Fin (2 ^ N), haarMeasure.real (dyadicInterval N k) * (if ‖c k‖ ≤ a then ‖c k‖ ^ 2 else 0) := by
  rw [dyadic_small_square_integral N c a, ← integral_indicator
    (measurableSet_le (dyadicStepValue_measurable N c).norm measurable_const)]
  have hi : (fun x => {x | ‖dyadicStepValue N c x‖ ≤ a}.indicator
      (fun y => ‖dyadicStepValue N c y‖ ^ 2) x) =
      (fun x => (if ‖dyadicStepValue N c x‖ ≤ a then ‖dyadicStepValue N c x‖ ^ 2 else 0)) := by
    funext x
    by_cases h : ‖dyadicStepValue N c x‖ ≤ a <;> simp [h]
  rw [hi]
  exact dyadic_transform_integral N c (fun z => if ‖z‖ ≤ a then ‖z‖ ^ 2 else 0)

end SchauderTranslates.LpConstruction
