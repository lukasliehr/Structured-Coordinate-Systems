import Lean_Code.SchauderTranslates.SoftWindowChoice

/-!
# Soft spectral window for an arbitrary gain lower bound

Parameterized copies of the chain
`eventually_soft_window_margins → soft_window_on_grid → soft_window_log_choice →
soft_spectral_window_of_bounds → soft_spectral_window`.
The first formalization hard-codes the start threshold `1 / 4000`, which comes from the gain
lower bound `1 / 646` of the scalar blocks. Here the start threshold is an arbitrary `c₁ > 0`,
and the gain lower bound an arbitrary `z₀ > 0` (with `c₁ = (9/10) * z₀ / (1 + z₀) / 4`).
-/

noncomputable section
open MeasureTheory Matrix Filter
open scoped Topology ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates

/-- Simultaneous numerical margins with an arbitrary positive start threshold `c₁`. -/
theorem eventually_soft_window_margins_sharp {R : ℝ → ℝ} {C c₁ : ℝ} (hC : 0 < C) (hc₁ : 0 < c₁)
    (hR : Tendsto R atTop atTop) (hbound : ∀ᶠ X in atTop, R X ≤ C * X) :
    ∀ᶠ X in atTop, 0 < X ∧ 1 < R X ∧ Real.exp (-X / 4) < c₁ ∧
      R X * Real.exp (-X / 2) < 1 / 2 ∧
      R X * Real.exp (-X / 2) ≤ Real.exp (-X / 4) ∧
      Real.log 4 + (17 / 16 : ℝ) * Real.log (R X) < (5 / 32 : ℝ) * X := by
  have he : Tendsto (fun X : ℝ => Real.exp (-X / 4)) atTop (𝓝 0) := by
    refine (exp_negative_scale_tendsto (by norm_num : (0 : ℝ) < 1 / 4)).congr fun X => ?_
    congr 1
    ring
  filter_upwards [eventually_soft_window_margins hC hR hbound,
    he.eventually (gt_mem_nhds hc₁)] with X hX he
  exact ⟨hX.1, hX.2.1, he, hX.2.2.2.1, hX.2.2.2.2.1, hX.2.2.2.2.2⟩

/-- The finite selection argument of `soft_window_on_grid`, with the start threshold `1 / 4000`
replaced by an arbitrary `c₁ > 0`. -/
theorem soft_window_on_grid_sharp {X R c₁ : ℝ} (hX : 0 < X) (hR : 1 < R) (hc₁ : 0 < c₁)
    (hA : Real.exp (-X / 4) < c₁)
    (hhalf : R * Real.exp (-X / 2) < 1 / 2)
    (hmargin : Real.log 4 + (17 / 16 : ℝ) * Real.log R < (5 / 32 : ℝ) * X)
    (g : ℝ → ℝ) (hmono : AntitoneOn g (Set.Icc 0 1))
    (hstart : c₁ ≤ g (Real.exp (-2 * X)))
    (hend : g (Real.exp (-X / 2)) ≤ Real.exp (-X / 2))
    (hstep : ∀ t : ℝ, 0 ≤ t → R * t ≤ 1 / 2 → g t / (4 * R) ≤ g (R * t)) :
    ∃ m : ℝ, 0 < m ∧ m ≤ R * Real.exp (-X / 2) ∧
      Real.exp (-X / 2) < g (m / R) ∧ g (m / R) ≤ Real.exp (-X / 4) ∧
      g m / g (m / R) ≤ R ^ (-(1 / 16 : ℝ)) := by
  let N := softGridCount X R
  let v : ℕ → ℝ := fun k => g (softGrid X R k)
  have hR0 := zero_lt_one.trans hR
  have hN := softGrid_end_bounds hX hR
  have hgrid (k : ℕ) (hk : k ≤ N) : softGrid X R k ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(softGrid_pos X hR0 k).le, ?_⟩
    have hle := (softGrid_mono X hR.le hk).trans hN.2
    linarith
  have hprev (k : ℕ) (hk : 0 < k) : R * softGrid X R (k - 1) = softGrid X R k := by
    rw [← softGrid_step, Nat.sub_add_cancel hk]
  have hvstep (k : ℕ) (hk : 0 < k) (hkN : k ≤ N) : v (k - 1) / (4 * R) ≤ v k := by
    have ht : R * softGrid X R (k - 1) ≤ 1 / 2 := by
      rw [hprev k hk]
      exact ((softGrid_mono X hR.le hkN).trans hN.2).trans hhalf.le
    have h := hstep (softGrid X R (k - 1)) (softGrid_pos X hR0 _).le ht
    simpa only [hprev k hk] using h
  have hv0 : c₁ ≤ v 0 := by simpa [v, softGrid] using hstart
  have hvpos (k : ℕ) : k ≤ N → 0 < v k := by
    induction k with
    | zero => intro _; exact lt_of_lt_of_le hc₁ hv0
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hs := hvstep (k + 1) (by omega) hk
      simp only [Nat.add_sub_cancel] at hs
      exact (div_pos hp (by positivity)).trans_le hs
  have hvmono (i j : ℕ) (hij : i ≤ j) (hjN : j ≤ N) : v j ≤ v i :=
    hmono (hgrid i (hij.trans hjN)) (hgrid j hjN) (softGrid_mono X hR.le hij)
  have hB : 0 < Real.exp (-X / 2) := Real.exp_pos _
  have hAB : Real.exp (-X / 2) < Real.exp (-X / 4) := Real.exp_lt_exp.mpr (by linarith)
  have hvN : v N ≤ Real.exp (-X / 2) := by
    apply le_trans (hmono _ (hgrid N le_rfl) hN.1) hend
    exact ⟨hB.le, (Real.exp_le_one_iff.mpr (by linarith))⟩
  obtain ⟨a, haN, ha, haMin⟩ := first_crossing_exists v (Real.exp (-X / 4)) N (hvN.trans hAB.le)
  obtain ⟨b, hbN, hb, hbMin⟩ := first_crossing_exists v (Real.exp (-X / 2)) N hvN
  obtain ⟨k, hak, hkb, hratio, hlow, hhigh⟩ := finite_grid_drop v hR hB hvpos hvmono hvstep
    (hA.trans_le hv0) haN hbN ha haMin hb hbMin (softGrid_gap hX hR hmargin)
  have hk : 0 < k := by omega
  have he : softGrid X R k / R = softGrid X R (k - 1) := by
    rw [← hprev k hk]
    field_simp
  refine ⟨softGrid X R k, softGrid_pos X hR0 k,
    (softGrid_mono X hR.le (hkb.trans hbN)).trans hN.2, ?_⟩
  rw [he]
  exact ⟨hlow, hhigh, hratio⟩

/-- The soft-capture estimates needed for selection, with start threshold `c₁`. Identical to
`SoftWindowCaptureBounds` except for the field `initial`. -/
structure SoftWindowCaptureBoundsSharp (g : ℝ → ℝ) (ε c₁ : ℝ) : Prop where
  antitone : AntitoneOn g (Set.Icc 0 1)
  nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g t
  initial : c₁ ≤ g (ε ^ 2)
  final : g (Real.sqrt ε) ≤ Real.sqrt ε
  step : ∀ R t : ℝ, 1 ≤ R → 0 ≤ t → R * t ≤ 1 / 2 → g t / (4 * R) ≤ g (R * t)

/-- The simultaneous margins hold before the capture function is chosen. -/
theorem soft_window_log_choice_sharp {κ c₁ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hc₁ : 0 < c₁) :
    ∀ᶠ X in atTop, ∀ (g : ℝ → ℝ),
      AntitoneOn g (Set.Icc 0 1) →
      c₁ ≤ g (Real.exp (-2 * X)) →
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
  have hmargins := eventually_soft_window_margins_sharp (softRatio_constants_pos hκ0 hκ1).2 hc₁
    (softSeedRatio_tendsto hκ0 hκ1) hbound
  filter_upwards [hmargins] with X hX
  intro g hmono hstart hend hstep
  obtain ⟨m, hm0, hm1, hlow, hhigh, hratio⟩ := soft_window_on_grid_sharp hX.1 hX.2.1 hc₁
    hX.2.2.1 hX.2.2.2.1 hX.2.2.2.2.2 g hmono hstart hend hstep
  have hm : m ≤ (1 / 2 : ℝ) ^ softSeedLength X :=
    hm1.trans (hX.2.2.2.2.1.trans (softSeedLength_mass_bound hX.1.le))
  have he : m / softSeedRatio κ X = m * seedGamma κ (softSeedLength X) := by
    simp only [softSeedRatio, seedRatio, div_inv_eq_mul]
  rw [he] at hlow hhigh hratio
  exact ⟨m, hm0, hm, hlow, hhigh, hratio⟩

/-- Uniform selection for every capture function satisfying the estimates with threshold `c₁`. -/
theorem soft_spectral_window_of_bounds_sharp {κ c₁ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hc₁ : 0 < c₁) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ g : ℝ → ℝ,
      SoftWindowCaptureBoundsSharp g ε c₁ → ∃ m, SoftWindowResult g κ ε m := by
  have hchoice := softLossLog_tendsto.eventually (soft_window_log_choice_sharp hκ0 hκ1 hc₁)
  have hratio := (softLossRatio_tendsto hκ0 hκ1).eventually (eventually_ge_atTop 1)
  filter_upwards [hchoice, hratio, self_mem_nhdsWithin] with ε hchoice hratio hε
  have hε0 : 0 < ε := hε
  intro g hg
  have hstart : c₁ ≤ g (Real.exp (-2 * softLossLog ε)) := by
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

/-- Capture at zero for a gain bounded below by `z₀`: `softCapture 0 = mass * gain / (1 + gain)`
and `x ↦ x / (1 + x)` is increasing. -/
theorem softCapture_zero_lower_sharp {d n : ℕ} (s : ScalarData d n) {ε z₀ : ℝ}
    (hε : ε ≤ 1 / 10) (hm : s.mass = 1 - ε) (hz₀ : 0 < z₀) (hz : z₀ ≤ s.gain) :
    (9 / 10 : ℝ) * z₀ / (1 + z₀) ≤ s.softCapture 0 := by
  rw [ScalarData.softCapture, softCapture_zero, s.raw_capture_gain]
  have hden : 0 < 1 + s.gain := by linarith [s.gain_nonneg]
  have hden₀ : 0 < 1 + z₀ := by linarith
  have hmass : 9 / 10 ≤ s.mass := by rw [hm]; linarith
  rw [div_le_div_iff₀ hden₀ hden]
  have hprod := mul_nonneg (sub_nonneg.mpr hmass) (mul_nonneg s.gain_nonneg hden₀.le)
  nlinarith

/-- Capture at the squared deficit for a gain bounded below by `z₀`. -/
theorem softCapture_sq_lower_sharp {d n : ℕ} (s : ScalarData d n) {ε z₀ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) (hm : s.mass = 1 - ε) (hz₀ : 0 < z₀) (hz : z₀ ≤ s.gain)
    (hfloor : (s.rawGram - ((ε ^ 2 : ℝ) : ℂ) • 1).PosSemidef) :
    (9 / 10 : ℝ) * z₀ / (1 + z₀) / 4 ≤ s.softCapture (ε ^ 2) := by
  have hzero := softCapture_zero_lower_sharp s hε1 hm hz₀ hz
  have hlow := softCapture_floor_lower s.nonconstantGram_posDef s.moment hε0.le hε1
    (s.nonconstantGram_floor hfloor)
  have hz' : (9 / 10 : ℝ) * z₀ / (1 + z₀) ≤ gramCapture s.nonconstantGram s.moment := by
    simpa only [ScalarData.softCapture, softCapture_zero] using hzero
  exact (div_le_div_of_nonneg_right hz' (by norm_num)).trans hlow

/-- All soft-capture estimates used for selection, for an actual scalar block whose gain is
bounded below by `z₀ > 0`; the start threshold is `c₁ = (9/10) * z₀ / (1 + z₀) / 4`. -/
theorem soft_capture_bounds_sharp {d n : ℕ} (s : ScalarData d n) {ε z₀ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 10) (hm : s.mass = 1 - ε) (hz₀ : 0 < z₀) (hz : z₀ ≤ s.gain)
    (hfloor : (s.rawGram - ((ε ^ 2 : ℝ) : ℂ) • 1).PosSemidef) :
    SoftWindowCaptureBoundsSharp s.softCapture ε ((9 / 10 : ℝ) * z₀ / (1 + z₀) / 4) :=
  ⟨softCapture_antitone s.nonconstantGram_posDef s.nonconstantGram_le_one s.moment,
    fun _ ht => softCapture_nonneg s.nonconstantGram_posDef s.moment ht.1 ht.2,
    softCapture_sq_lower_sharp s hε0 hε1 hm hz₀ hz hfloor,
    s.softCapture_sqrt_upper hε0 hε1 hm,
    fun _ _ hR ht hRt => softCapture_scale_lower s.nonconstantGram_posDef s.moment hR ht hRt⟩

/-- Window selection for scalar blocks whose gain is bounded below by an arbitrary `z₀ > 0`. -/
theorem soft_spectral_window_sharp {κ z₀ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hz₀ : 0 < z₀) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (d n : ℕ) (s : ScalarData d n),
      s.mass = 1 - ε → z₀ ≤ s.gain →
      (s.rawGram - ((ε ^ 2 : ℝ) : ℂ) • 1).PosSemidef →
      ∃ m, SoftWindowResult s.softCapture κ ε m := by
  have hc₁ : 0 < (9 / 10 : ℝ) * z₀ / (1 + z₀) / 4 := by positivity
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 / 10 :=
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 10)).filter_mono nhdsWithin_le_nhds
  filter_upwards [soft_spectral_window_of_bounds_sharp hκ0 hκ1 hc₁, hsmall,
    self_mem_nhdsWithin] with ε hchoice hε1 hε0
  intro d n s hm hz hfloor
  exact hchoice s.softCapture (soft_capture_bounds_sharp s hε0 hε1 hm hz₀ hz hfloor)

end SchauderTranslates.Sharp
