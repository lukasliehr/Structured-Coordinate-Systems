import Lean_Code.SchauderTranslates.OriginalCarrierCapture
import Lean_Code.SchauderTranslates.SoftWindowChoice

noncomputable section
open MeasureTheory Matrix Filter
open scoped ComplexOrder Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A uniform late-loss margin, before a scalar block or selective mass is chosen. -/
theorem selective_capture_margin_eventually :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (1 / 4 : ℝ) < 1 - ε := by
  have ht : Tendsto (fun ε : ℝ => ε ^ (1 / 4 : ℝ) + ε) (𝓝 0) (𝓝 0) := by
    convert ((Real.continuousAt_rpow_const (0 : ℝ) (1 / 4 : ℝ) (Or.inr (by norm_num))).tendsto.add
      (tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0))) using 1 <;> norm_num
  have hh : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ (1 / 4 : ℝ) + ε < 1 :=
    (ht.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hh] with ε hε
  linarith

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]
variable {ρ : Measure S} [IsProbabilityMeasure ρ]

/-- Blueprint `select:capture`: the exact normalized capture and information on
full slow L², using the original independent bounded carrier. The strict
information denominators and the spectral-average bounds are consequences of
the checked late window, not additional construction assumptions. -/
theorem selective_capture {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ (d n : ℕ)
      (a : SelectiveKernelData S (softLossLength ε) d n)
      (φ : ι → BoundedMeasurableComplex S),
      a.κ = κ → a.scalar.mass = 1 - ε →
      LinearIndependent ℂ (fun i => (φ i).toL2 ρ) →
      a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ) → ‖a.e.toL2 ρ‖ = 1 →
      SoftWindowResult a.scalar.softCapture κ ε a.m → SelectiveCaptureData a ρ φ := by
  filter_upwards [selective_capture_margin_eventually, softLossLength_eventually_pos,
    softLossOmega_eventually_three_quarters hκ0 hκ1, self_mem_nhdsWithin] with ε hsmall hL hω hε
  intro d n a φ hk hmass hφ he he1 hw
  have hk0 : 0 < a.κ := by rwa [hk]
  have hk1 : a.κ < 1 := by rwa [hk]
  have homega : (3 / 4 : ℝ) ≤ seedOmega a.κ (softLossLength ε) := by rwa [hk]
  have hε0 : 0 < ε := hε
  obtain ⟨c, hc, hs⟩ := a.orthonormal_carrier_exists φ hφ he he1
  have hB := c.gram_positive_contraction (softLossLength ε) a.mass_pos a.mass_le
    (c.kernel_coupling_bound a hc)
  rw [c.gram_eq_seedBlock (softLossLength ε) a.mass_pos.le (c.kernel_coupling_bound a hc)] at hB
  have hb := seedCaptureValue_bounds a.scalar.nonconstantGram_posDef a.scalar.nonconstantGram_le_one
    a.scalar.moment c.distinguished hk0 hk1 hL a.mass_pos hB.1 hB.2.1 homega
  have hgamma := seed_spectral_order hk0 hk1 hL
  have ht : a.m * seedGamma a.κ (softLossLength ε) ≤ a.m :=
    mul_le_of_le_one_right a.mass_pos.le hgamma.2.1.le
  have hxle : softCapture a.scalar.nonconstantGram a.scalar.moment a.m ≤
      softCapture a.scalar.nonconstantGram a.scalar.moment (a.m * seedGamma a.κ (softLossLength ε)) :=
    softCapture_antitone a.scalar.nonconstantGram_posDef a.scalar.nonconstantGram_le_one a.scalar.moment
      ⟨mul_nonneg a.mass_pos.le hgamma.1.le, ht.trans a.m_le_one⟩ ⟨a.mass_pos.le, a.m_le_one⟩ ht
  have hu : softCapture a.scalar.nonconstantGram a.scalar.moment
      (a.m * seedGamma a.κ (softLossLength ε)) ≤ ε ^ (1 / 4 : ℝ) := by
    simpa only [ScalarData.softCapture, hk] using hw.capture_upper
  have hm : 1 - ε ≤ a.mass := by
    rw [a.mass_eq hmass]
    nlinarith [mul_nonneg a.mass_pos.le hε0.le]
  exact a.capture_data_of_margins φ hφ he he1 hL hk0 hk1 homega
    (hxle.trans_lt (hu.trans_lt (hsmall.trans_le hm)))
    (hb.2.trans_lt (hu.trans_lt (hsmall.trans_le hm)))

end SchauderTranslates
