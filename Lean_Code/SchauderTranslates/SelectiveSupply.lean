import Lean_Code.SchauderTranslates.SelectiveCapture
import Lean_Code.SchauderTranslates.SelectivePrefixes

noncomputable section
open MeasureTheory Matrix Filter
open scoped ComplexOrder Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The finite numerical margins of the quantified supply hold for all sufficiently small
scalar losses, before a scalar block or a selective mass is chosen. -/
theorem selective_supply_margins_eventually {κ η : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hη : 0 < η) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ε ^ (1 / 4 : ℝ) + ε < 1 ∧
      ε ^ (1 / 4 : ℝ) < η * (1 - ε - ε ^ (1 / 4 : ℝ)) ∧
      (4 / 3 : ℝ) * softLossRatio κ ε ^ (-(1 / 16 : ℝ)) < η * (1 - ε - ε ^ (1 / 4 : ℝ)) ∧
      Real.sqrt ε < (3 / 4 : ℝ) * η := by
  have h4 : Tendsto (fun ε : ℝ => ε ^ (1 / 4 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0 : ℝ) (1 / 4 : ℝ)
      (Or.inr (by norm_num))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using h
  have h1 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hR := softLossRatio_drop_tendsto hκ0 hκ1
  have hs := softLoss_sqrt_tendsto
  have hD : Tendsto (fun ε : ℝ => η * (1 - ε - ε ^ (1 / 4 : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 η) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub h1 |>.sub h4).const_mul η
  have ha : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (1 / 4 : ℝ) + ε < 1 :=
    (h4.add h1).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) + 0 < 1))
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (1 / 4 : ℝ) - η * (1 - ε - ε ^ (1 / 4 : ℝ)) < 0 :=
    (h4.sub hD).eventually (gt_mem_nhds (by linarith))
  have hc : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (4 / 3 : ℝ) * softLossRatio κ ε ^ (-(1 / 16 : ℝ)) - η * (1 - ε - ε ^ (1 / 4 : ℝ)) < 0 :=
    ((hR.const_mul (4 / 3 : ℝ)).sub hD).eventually (gt_mem_nhds (by linarith))
  have hd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Real.sqrt ε < (3 / 4 : ℝ) * η :=
    hs.eventually (gt_mem_nhds (by linarith))
  filter_upwards [ha, hb, hc, hd] with ε ha hb hc hd
  exact ⟨ha, by linarith, by linarith, hd⟩

/-- The arithmetic of the supply margins, with all analytic quantities opaque. -/
theorem selective_supply_numeric {ε m g u v M η R sε q4 : ℝ}
    (hε0 : 0 < ε) (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hM : M = 1 - (1 - m) * ε)
    (hulow : sε < u) (hs0 : 0 ≤ sε) (huup : u ≤ q4) (hgR : g ≤ R * u) (hR0 : 0 ≤ R)
    (hεu : ε ≤ sε * u) (hvlow : (3 / 4 : ℝ) * u ≤ v) (hvup : v ≤ u) (hg0 : 0 ≤ g)
    (hgu : g ≤ u) (hη : 0 < η)
    (h1 : q4 + ε < 1) (h2 : q4 < η * (1 - ε - q4)) (h3 : (4 / 3 : ℝ) * R < η * (1 - ε - q4))
    (h4 : sε < (3 / 4 : ℝ) * η) :
    0 < v / (M - v) ∧ v / (M - v) < η ∧ 0 ≤ g / (M - g) ∧ g / (M - g) < η * (v / (M - v)) ∧
      1 - M < η * (v / (M - v)) := by
  have hu0 : 0 < u := hs0.trans_lt hulow
  have hMlow : 1 - ε ≤ M := by rw [hM]; nlinarith
  have hMle : M ≤ 1 := by rw [hM]; nlinarith
  have hv0 : 0 < v := by linarith
  have hMv : 0 < M - v := by linarith
  have hMg : 0 < M - g := by linarith
  have hdenv : 1 - ε - q4 ≤ M - v := by linarith
  have hdeng : 1 - ε - q4 ≤ M - g := by linarith
  have hj0 : 0 < v / (M - v) := div_pos hv0 hMv
  have hjle : v ≤ v / (M - v) := by
    rw [le_div_iff₀ hMv]
    nlinarith
  refine ⟨hj0, ?_, div_nonneg hg0 hMg.le, ?_, ?_⟩
  · rw [div_lt_iff₀ hMv]
    nlinarith
  · have e1 : g * (M - v) ≤ R * u := by nlinarith
    have e2 : R * u ≤ (4 / 3 : ℝ) * R * v := by nlinarith
    have e3 : (4 / 3 : ℝ) * R * v < η * (1 - ε - q4) * v := by nlinarith
    have e4 : η * (1 - ε - q4) * v ≤ η * v * (M - g) := by nlinarith
    have he : η * (v / (M - v)) * (M - g) = η * v * (M - g) / (M - v) := by
      field_simp
    rw [div_lt_iff₀ hMg, he, lt_div_iff₀ hMv]
    linarith
  · have e1 : 1 - M ≤ ε := by rw [hM]; nlinarith
    have e2 : sε * u < (3 / 4 : ℝ) * η * u := by nlinarith
    have e3 : (3 / 4 : ℝ) * η * u ≤ η * v := by nlinarith
    have e4 : η * v ≤ η * (v / (M - v)) := mul_le_mul_of_nonneg_left hjle hη.le
    linarith

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]

/-- Blueprint `select:supply`. For the fixed slow law and coupling parameter, one finite
polynomial selective block serves every bounded unit vector in the span of independent
carrier rows. Its information is `c P_{V ∩ e⊥} + j P_e` with `0 < j < η`, `0 ≤ c < η j`
and loss `1 - M < η j`. The scalar block also carries the bounds used by the prefix
estimate of `select:prefix`. -/
theorem selective_blocks (ρ : Measure S) [IsProbabilityMeasure ρ]
    {κ η : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hη : 0 < η) :
    ∃ (L d n : ℕ) (s : ScalarData d n) (m c j : ℝ),
      0 < m ∧ m ≤ (1 / 2 : ℝ) ^ L ∧
      s.IsPolynomial ∧ s.AugmentedPrefixSqBound 4 ∧ (∀ k, (s.rawGram⁻¹ k k).re ≤ 2) ∧
      ∀ (a : SelectiveKernelData S L d n) (φ : ι → BoundedMeasurableComplex S),
        a.scalar = s → a.m = m → a.κ = κ →
        LinearIndependent ℂ (fun i => (φ i).toL2 ρ) →
        a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ) → ‖a.e.toL2 ρ‖ = 1 →
        informationOperator (a.kernel.marginalMeans ρ (a.packet φ))
            (Matrix.gram ℂ (a.kernel.centered ρ (a.packet φ))) =
          (c : ℂ) • (atomSpan (fun i => (φ i).toL2 ρ) ⊓ (ℂ ∙ a.e.toL2 ρ)ᗮ).starProjection +
            (j : ℂ) • (ℂ ∙ a.e.toL2 ρ).starProjection ∧
        0 < j ∧ j < η ∧ 0 ≤ c ∧ c < η * j ∧ 1 - a.mass < η * j := by
  have hev := (selective_capture (S := S) (ι := ι) (ρ := ρ) hκ0 hκ1).and
    ((soft_spectral_window hκ0 hκ1).and
      ((selective_supply_margins_eventually hκ0 hκ1 hη).and softLossLength_eventually_pos))
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  obtain ⟨d, n, s, ε, q, K, hpoly, heven, hfloor, hreal, hε0, hεδ, hε1, hmass, hgain, hq0,
    hq3, hcent, hK0, hK2, haug, hmat, hdiag, hconst⟩ := scalar_blocks hδ₀
  obtain ⟨hcapε, hwinε, ⟨hm1, hm2, hm3, hm4⟩, hL⟩ := hsub ⟨hε0, hεδ⟩
  obtain ⟨m, hm⟩ := hwinε d n s hmass hgain hmat
  set L := softLossLength ε with hLdef
  set M : ℝ := s.mass + (1 - s.mass) * m with hMdef
  set g : ℝ := SchauderTranslates.softCapture s.nonconstantGram s.moment m with hgdef
  set u : ℝ := SchauderTranslates.softCapture s.nonconstantGram s.moment
    (m * seedGamma κ L) with hudef
  set v : ℝ := seedCaptureValue s.nonconstantGram s.moment κ m L with hvdef
  refine ⟨L, d, n, s, m, g / (M - g), v / (M - v), hm.mass_pos, hm.mass_le, hpoly,
    haug.mono (by nlinarith), ?_, ?_⟩
  · intro k
    rcases k with k | k
    · cases k
      exact hconst.le
    · linarith [hdiag k]
  intro a φ hs hma hk hφ he he1
  have hwin : SoftWindowResult a.scalar.softCapture κ ε a.m := by rw [hs, hma]; exact hm
  have hD := hcapε d n a φ hk (by rw [hs]; exact hmass) hφ he he1 hwin
  have hM : a.mass = M := by simp only [SelectiveKernelData.mass, hs, hma, hMdef]
  obtain ⟨_, hinfo, hgM, hvM, hvlow, hvup⟩ := hD
  simp only [hs, hma, hk, hM] at hinfo hgM hvM hvlow hvup
  change g < M at hgM
  change v < M at hvM
  change (3 / 4 : ℝ) * u ≤ v at hvlow
  change v ≤ u at hvup
  refine ⟨hinfo, ?_⟩
  -- Scalar facts about the window and the selective mass.
  have hm0 : 0 < m := hm.mass_pos
  have hmle : m ≤ 1 := hm.mass_le.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hulow : Real.sqrt ε < u := hm.capture_lower
  have huup : u ≤ ε ^ (1 / 4 : ℝ) := hm.capture_upper
  have hu0 : 0 < u := (Real.sqrt_nonneg ε).trans_lt hulow
  have hratio : g / u ≤ softLossRatio κ ε ^ (-(1 / 16 : ℝ)) := hm.ratio_upper
  have herr : ε / u ≤ Real.sqrt ε := hm.error_upper
  have hgamma := seed_spectral_order hκ0 hκ1 hL
  have hg0 : 0 ≤ g := softCapture_nonneg s.nonconstantGram_posDef s.moment hm0.le hmle
  have hgu : g ≤ u :=
    softCapture_antitone s.nonconstantGram_posDef s.nonconstantGram_le_one s.moment
      ⟨mul_nonneg hm0.le hgamma.1.le,
        (mul_le_of_le_one_right hm0.le hgamma.2.1.le).trans hmle⟩ ⟨hm0.le, hmle⟩
      (mul_le_of_le_one_right hm0.le hgamma.2.1.le)
  have hMeq : M = 1 - (1 - m) * ε := by rw [hMdef, hmass]; ring
  have hgR : g ≤ softLossRatio κ ε ^ (-(1 / 16 : ℝ)) * u := (div_le_iff₀ hu0).mp hratio
  have hεu : ε ≤ Real.sqrt ε * u := (div_le_iff₀ hu0).mp herr
  have hR0 : 0 ≤ softLossRatio κ ε ^ (-(1 / 16 : ℝ)) := by
    have hr : 0 ≤ softLossRatio κ ε := by
      unfold softLossRatio seedRatio
      exact inv_nonneg.mpr hgamma.1.le
    exact Real.rpow_nonneg hr _
  clear_value g u v M L
  rw [hM]
  exact selective_supply_numeric hε0 hm0.le hmle hMeq hulow (Real.sqrt_nonneg ε) huup hgR hR0
    hεu hvlow hvup hg0 hgu hη hm1 hm2 hm3 hm4

end SchauderTranslates
