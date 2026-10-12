import Lean_Code.SchauderTranslates.SoftLossScale
import Lean_Code.SchauderTranslates.SoftWindowGridSelection
import Lean_Code.SchauderTranslates.SoftCaptureBounds

noncomputable section
open MeasureTheory Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Only the already proved soft-capture estimates are needed for selection. -/
structure SoftWindowCaptureBounds (g : ℝ → ℝ) (ε : ℝ) : Prop where
  antitone : AntitoneOn g (Set.Icc 0 1)
  nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g t
  initial : (1 / 4000 : ℝ) ≤ g (ε ^ 2)
  final : g (Real.sqrt ε) ≤ Real.sqrt ε
  step : ∀ R t : ℝ, 1 ≤ R → 0 ≤ t → R * t ≤ 1 / 2 → g t / (4 * R) ≤ g (R * t)

/-- The chosen mass and the two ratios, with nonnegative bounds exposing their limits. -/
structure SoftWindowResult (g : ℝ → ℝ) (κ ε m : ℝ) : Prop where
  mass_pos : 0 < m
  mass_le : m ≤ (1 / 2 : ℝ) ^ softLossLength ε
  capture_lower : Real.sqrt ε < g (m * seedGamma κ (softLossLength ε))
  capture_upper : g (m * seedGamma κ (softLossLength ε)) ≤ ε ^ (1 / 4 : ℝ)
  ratio_nonneg : 0 ≤ g m / g (m * seedGamma κ (softLossLength ε))
  ratio_upper : g m / g (m * seedGamma κ (softLossLength ε)) ≤ softLossRatio κ ε ^ (-(1 / 16 : ℝ))
  error_nonneg : 0 ≤ ε / g (m * seedGamma κ (softLossLength ε))
  error_upper : ε / g (m * seedGamma κ (softLossLength ε)) ≤ Real.sqrt ε

/-- The simultaneous margins hold before the capture function is chosen. -/
theorem soft_window_log_choice {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ X in atTop, ∀ (g : ℝ → ℝ),
      AntitoneOn g (Set.Icc 0 1) →
      (1 / 4000 : ℝ) ≤ g (Real.exp (-2 * X)) →
      g (Real.exp (-X / 2)) ≤ Real.exp (-X / 2) →
      (∀ t : ℝ, 0 ≤ t → softSeedRatio κ X * t ≤ 1 / 2 →
        g t / (4 * softSeedRatio κ X) ≤ g (softSeedRatio κ X * t)) →
      ∃ m : ℝ, 0 < m ∧ m ≤ (1 / 2 : ℝ) ^ softSeedLength X ∧
        Real.exp (-X / 2) < g (m * seedGamma κ (softSeedLength X)) ∧
        g (m * seedGamma κ (softSeedLength X)) ≤ Real.exp (-X / 4) ∧
        g m / g (m * seedGamma κ (softSeedLength X)) ≤ softSeedRatio κ X ^ (-(1 / 16 : ℝ)) := by
  have hbound : ∀ᶠ X in atTop, softSeedRatio κ X ≤ softRatioUpper κ * X := by
    filter_upwards [eventually_ge_atTop (8 * Real.log 2)] with X hX
    exact (softSeedRatio_linear_bounds hκ0 hκ1 hX).2
  have hmargins := eventually_soft_window_margins (softRatio_constants_pos hκ0 hκ1).2
    (softSeedRatio_tendsto hκ0 hκ1) hbound
  filter_upwards [hmargins] with X hX
  intro g hmono hstart hend hstep
  obtain ⟨m, hm0, hm1, hlow, hhigh, hratio⟩ := soft_window_on_grid hX.1 hX.2.1
    hX.2.2.1 hX.2.2.2.1 hX.2.2.2.2.2 g hmono hstart hend hstep
  have hm : m ≤ (1 / 2 : ℝ) ^ softSeedLength X :=
    hm1.trans (hX.2.2.2.2.1.trans (softSeedLength_mass_bound hX.1.le))
  have he : m / softSeedRatio κ X = m * seedGamma κ (softSeedLength X) := by
    simp only [softSeedRatio, seedRatio, div_inv_eq_mul]
  rw [he] at hlow hhigh hratio
  exact ⟨m, hm0, hm, hlow, hhigh, hratio⟩

/-- Uniform selection for every capture function satisfying the checked estimates. -/
theorem soft_spectral_window_of_bounds {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ g : ℝ → ℝ,
      SoftWindowCaptureBounds g ε → ∃ m, SoftWindowResult g κ ε m := by
  have hchoice := softLossLog_tendsto.eventually (soft_window_log_choice hκ0 hκ1)
  have hratio := (softLossRatio_tendsto hκ0 hκ1).eventually (eventually_ge_atTop 1)
  filter_upwards [hchoice, hratio, self_mem_nhdsWithin] with ε hchoice hratio hε
  have hε0 : 0 < ε := hε
  intro g hg
  have hstart : (1 / 4000 : ℝ) ≤ g (Real.exp (-2 * softLossLog ε)) := by
    rw [exp_neg_two_softLossLog hε0]; exact hg.initial
  have hend : g (Real.exp (-softLossLog ε / 2)) ≤ Real.exp (-softLossLog ε / 2) := by
    rw [exp_neg_softLossLog_half hε0]; exact hg.final
  have hstep (t : ℝ) (ht : 0 ≤ t) (hRt : softSeedRatio κ (softLossLog ε) * t ≤ 1 / 2) :
      g t / (4 * softSeedRatio κ (softLossLog ε)) ≤ g (softSeedRatio κ (softLossLog ε) * t) :=
    hg.step _ t hratio ht hRt
  obtain ⟨m, hm0, hm1, hlow, hhigh, hrat⟩ := hchoice g hg.antitone hstart hend hstep
  rw [exp_neg_softLossLog_half hε0] at hlow
  rw [exp_neg_softLossLog_div hε0] at hhigh
  have hmle : m ≤ 1 := hm1.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hu : 0 < g (m * seedGamma κ (softLossLength ε)) :=
    (Real.sqrt_pos.mpr hε0).trans hlow
  refine ⟨m, ⟨hm0, hm1, hlow, hhigh, div_nonneg (hg.nonneg m ⟨hm0.le, hmle⟩) hu.le,
    hrat, div_nonneg hε0.le hu.le, ?_⟩⟩
  apply (div_le_iff₀ hu).mpr
  have hs := Real.sq_sqrt hε0.le
  have hmul := mul_le_mul_of_nonneg_left hlow.le (Real.sqrt_nonneg ε)
  dsimp only [softLossLength]
  nlinarith

/-- Blueprint `select:window`: apply the uniform selection to actual scalar-supply blocks. -/
theorem soft_spectral_window {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (d n : ℕ) (s : ScalarData d n),
      s.mass = 1 - ε → (1 / 646 : ℝ) ≤ s.gain →
      (s.rawGram - ((ε ^ 2 : ℝ) : ℂ) • 1).PosSemidef →
      ∃ m, SoftWindowResult s.softCapture κ ε m := by
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 / 10 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 10)).filter_mono nhdsWithin_le_nhds
  filter_upwards [soft_spectral_window_of_bounds hκ0 hκ1, hsmall, self_mem_nhdsWithin] with ε hchoice hε1 hε0
  intro d n s hm hz hfloor
  have h := soft_capture_bounds s hε0 hε1 hm hz hfloor
  apply hchoice s.softCapture
  exact ⟨h.1, h.2.2.1, by convert h.2.2.2.2.1 using 1 <;> norm_num, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- Any choices meeting the window bounds have both claimed ratios tending to zero.
The capture function and selected mass may vary with the scalar loss. -/
theorem soft_spectral_window_limits {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (g : ℝ → ℝ → ℝ) (m : ℝ → ℝ)
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), SoftWindowResult (g ε) κ ε (m ε)) :
    Tendsto (fun ε => g ε (m ε) / g ε (m ε * seedGamma κ (softLossLength ε))) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun ε => ε / g ε (m ε * seedGamma κ (softLossLength ε))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact ⟨squeeze_zero' (h.mono fun _ h => h.ratio_nonneg) (h.mono fun _ h => h.ratio_upper)
      (softLossRatio_drop_tendsto hκ0 hκ1),
    squeeze_zero' (h.mono fun _ h => h.error_nonneg) (h.mono fun _ h => h.error_upper) softLoss_sqrt_tendsto⟩

end SchauderTranslates
