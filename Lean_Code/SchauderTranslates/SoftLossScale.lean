import Lean_Code.SchauderTranslates.SoftSeedLength
import Lean_Code.SchauderTranslates.SoftWindowAsymptotics

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

def softLossLog (ε : ℝ) : ℝ := Real.log (1 / ε)
def softLossLength (ε : ℝ) : ℕ := softSeedLength (softLossLog ε)
def softLossRatio (κ ε : ℝ) : ℝ := seedRatio κ (softLossLength ε)

@[simp] theorem softLossLog_eq (ε : ℝ) : softLossLog ε = -Real.log ε := by
  simp [softLossLog, one_div]

theorem softLossLog_tendsto : Tendsto softLossLog (𝓝[>] (0 : ℝ)) atTop := by
  change Tendsto (fun ε : ℝ => Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) atTop
  simpa only [one_div, Function.comp_def] using
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))

theorem softLossLength_tendsto : Tendsto softLossLength (𝓝[>] (0 : ℝ)) atTop :=
  softSeedLength_tendsto.comp softLossLog_tendsto

theorem softLossRatio_tendsto {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tendsto (softLossRatio κ) (𝓝[>] (0 : ℝ)) atTop :=
  (seedRatio_tendsto_atTop hκ0 hκ1).comp softLossLength_tendsto

/-- The exact floor in the paper diverges as the loss tends to zero from above. -/
theorem softLossLength_eventually_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < softLossLength ε :=
  softLossLength_tendsto.eventually (eventually_gt_atTop 0)

theorem softLossRatio_linear_bounds {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), softRatioLower κ * softLossLog ε ≤ softLossRatio κ ε ∧
      softLossRatio κ ε ≤ softRatioUpper κ * softLossLog ε := by
  filter_upwards [softLossLog_tendsto.eventually (eventually_ge_atTop (8 * Real.log 2))] with ε hε
  exact softSeedRatio_linear_bounds hκ0 hκ1 hε

theorem softLossRatio_log_div_tendsto {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tendsto (fun ε => Real.log (softLossRatio κ ε) / softLossLog ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hb : ∀ᶠ X in atTop, softSeedRatio κ X ≤ softRatioUpper κ * X := by
    filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with X hX
    exact (softSeedRatio_linear_bounds hκ0 hκ1 hX).2
  exact (log_ratio_div_tendsto (softRatio_constants_pos hκ0 hκ1).2
    (softSeedRatio_tendsto hκ0 hκ1) hb).comp softLossLog_tendsto

theorem softLossOmega_tendsto {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tendsto (fun ε => seedOmega κ (softLossLength ε)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  (seedOmega_tendsto_one hκ0 hκ1).comp softLossLength_tendsto

@[simp] theorem exp_neg_softLossLog {ε : ℝ} (hε : 0 < ε) : Real.exp (-softLossLog ε) = ε := by
  rw [softLossLog_eq, neg_neg, Real.exp_log hε]

theorem exp_neg_softLossLog_div {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    Real.exp (-softLossLog ε / r) = ε ^ (1 / r) := by
  rw [softLossLog_eq, neg_neg, Real.rpow_def_of_pos hε]
  congr 1
  ring

theorem exp_neg_softLossLog_half {ε : ℝ} (hε : 0 < ε) :
    Real.exp (-softLossLog ε / 2) = Real.sqrt ε := by
  rw [exp_neg_softLossLog_div hε, Real.sqrt_eq_rpow]

theorem exp_neg_two_softLossLog {ε : ℝ} (hε : 0 < ε) :
    Real.exp (-2 * softLossLog ε) = ε ^ 2 := by
  rw [show -2 * softLossLog ε = -softLossLog ε + -softLossLog ε by ring,
    Real.exp_add, exp_neg_softLossLog hε]
  ring

theorem softLossRatio_drop_tendsto {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    Tendsto (fun ε => softLossRatio κ ε ^ (-(1 / 16 : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp (softLossRatio_tendsto hκ0 hκ1)

theorem softLoss_sqrt_tendsto : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa using (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

end SchauderTranslates
