import Lean_Code.SchauderTranslates.Lp.HaarDistribution

noncomputable section
open MeasureTheory

namespace SchauderTranslates.LpConstruction

theorem haar_interpolation_low_integral {s r : ℝ} (hs : 1 < s) (hr : 0 ≤ r) :
    (∫ a in Set.Ioo (0 : ℝ) r, a ^ (s - 2)) = r ^ (s - 1) / (s - 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr,
    integral_rpow (Or.inl (by linarith : -1 < s - 2)),
    show s - 2 + 1 = s - 1 by ring,
    Real.zero_rpow (by linarith : s - 1 ≠ 0), sub_zero]

theorem haar_interpolation_high_integral {s r : ℝ} (hs : s < 2) (hr : 0 < r) :
    (∫ a in Set.Ioi r, a ^ (s - 3)) = r ^ (s - 2) / (2 - s) := by
  rw [integral_Ioi_rpow_of_lt (by linarith : s - 3 < -1) hr,
    show s - 3 + 1 = s - 2 by ring]
  have he : 2 - s = -(s - 2) := by ring
  rw [he, div_neg, neg_div]

theorem haar_interpolation_low_integrable {s r : ℝ} (hs : 1 < s) :
    IntegrableOn (fun a : ℝ => a ^ (s - 2)) (Set.Ioo 0 r) :=
  (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r)
    (by linarith : -1 < s - 2)).1.mono_set (fun _ hx => ⟨hx.1, hx.2.le⟩)

theorem haar_interpolation_high_integrable {s r : ℝ} (hs : s < 2) (hr : 0 < r) :
    IntegrableOn (fun a : ℝ => a ^ (s - 3)) (Set.Ioi r) :=
  integrableOn_Ioi_rpow_of_lt (by linarith : s - 3 < -1) hr

end SchauderTranslates.LpConstruction
