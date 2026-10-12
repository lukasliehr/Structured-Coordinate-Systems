import Lean_Code.SchauderTranslates.SeedSpectralLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A constant multiple inside a logarithm does not change its sublinear growth. -/
theorem log_const_mul_div_tendsto {C : ℝ} (hC : 0 < C) :
    Tendsto (fun X : ℝ => Real.log (C * X) / X) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun X : ℝ => Real.log C / X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h₂ : Tendsto (fun X : ℝ => Real.log X / X) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h : Tendsto (fun X : ℝ => Real.log C / X + Real.log X / X) atTop (𝓝 0) := by simpa using h₁.add h₂
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [Real.log_mul hC.ne' hX.ne', add_div]

/-- A positive function bounded by a linear function has negligible logarithm relative to `X`. -/
theorem log_ratio_div_tendsto {R : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hR : Tendsto R atTop atTop) (hbound : ∀ᶠ X in atTop, R X ≤ C * X) :
    Tendsto (fun X => Real.log (R X) / X) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (log_const_mul_div_tendsto hC)
  · filter_upwards [hR.eventually (eventually_ge_atTop 1), eventually_gt_atTop (0 : ℝ)] with X hRX hX
    exact div_nonneg (Real.log_nonneg hRX) hX.le
  · filter_upwards [hbound, hR.eventually (eventually_gt_atTop 0), eventually_gt_atTop (0 : ℝ)] with X hb hRX hX
    exact div_le_div_of_nonneg_right (Real.log_le_log hRX hb) hX.le

theorem ratio_exp_decay {R : ℝ → ℝ} {C b : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hR : Tendsto R atTop atTop) (hbound : ∀ᶠ X in atTop, R X ≤ C * X) :
    Tendsto (fun X => R X * Real.exp (-b * X)) atTop (𝓝 0) := by
  have h : Tendsto (fun X : ℝ => C * X * Real.exp (-b * X)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, mul_zero, ← mul_assoc] using
      (tendsto_const_nhds.mul (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb) :
        Tendsto (fun X : ℝ => C * (X ^ (1 : ℝ) * Real.exp (-b * X))) atTop (𝓝 (C * 0)))
  apply squeeze_zero' _ _ h
  · filter_upwards [hR.eventually (eventually_ge_atTop 0)] with X hRX
    positivity
  · filter_upwards [hbound] with X hX
    exact mul_le_mul_of_nonneg_right hX (Real.exp_pos _).le

theorem exp_negative_scale_tendsto {b : ℝ} (hb : 0 < b) :
    Tendsto (fun X : ℝ => Real.exp (-b * X)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hb)
  simpa only [Function.comp_def, id_eq, neg_mul] using h

/-- Simultaneous numerical margins, uniform over the later choice of scalar block. -/
theorem eventually_soft_window_margins {R : ℝ → ℝ} {C : ℝ} (hC : 0 < C)
    (hR : Tendsto R atTop atTop) (hbound : ∀ᶠ X in atTop, R X ≤ C * X) :
    ∀ᶠ X in atTop, 0 < X ∧ 1 < R X ∧ Real.exp (-X / 4) < 1 / 4000 ∧
      R X * Real.exp (-X / 2) < 1 / 2 ∧
      R X * Real.exp (-X / 2) ≤ Real.exp (-X / 4) ∧
      Real.log 4 + (17 / 16 : ℝ) * Real.log (R X) < (5 / 32 : ℝ) * X := by
  have hlog := log_ratio_div_tendsto hC hR hbound
  have hc : Tendsto (fun X : ℝ => Real.log 4 / X) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hmargin : Tendsto (fun X => (Real.log 4 + (17 / 16 : ℝ) * Real.log (R X)) / X) atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hc.add (hlog.const_mul (17 / 16 : ℝ))
  have he : Tendsto (fun X : ℝ => Real.exp (-X / 4)) atTop (𝓝 0) := by
    convert exp_negative_scale_tendsto (by norm_num : (0 : ℝ) < 1 / 4) using 1 <;> congr 1 <;> funext X <;> congr 1 <;> ring
  have hhalf : Tendsto (fun X : ℝ => R X * Real.exp (-X / 2)) atTop (𝓝 0) := by
    convert ratio_exp_decay hC (by norm_num : (0 : ℝ) < 1 / 2) hR hbound using 1 <;> congr 1 <;> funext X <;> congr 2 <;> ring
  have hquarter : Tendsto (fun X : ℝ => R X * Real.exp (-X / 4)) atTop (𝓝 0) := by
    convert ratio_exp_decay hC (by norm_num : (0 : ℝ) < 1 / 4) hR hbound using 1 <;> congr 1 <;> funext X <;> congr 2 <;> ring
  filter_upwards [eventually_gt_atTop (0 : ℝ), hR.eventually (eventually_gt_atTop 1),
    he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4000)),
    hhalf.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hquarter.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hmargin.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 5 / 32))] with X hX hRX he hhalf hquarter hmargin
  refine ⟨hX, hRX, he, hhalf, ?_, (div_lt_iff₀ hX).mp hmargin⟩
  have heq : Real.exp (-X / 2) = Real.exp (-X / 4) * Real.exp (-X / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hquarter.le (Real.exp_pos _).le).trans_eq (one_mul _)

end SchauderTranslates
