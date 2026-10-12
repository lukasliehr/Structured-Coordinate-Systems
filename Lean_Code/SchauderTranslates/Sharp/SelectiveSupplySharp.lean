import Lean_Code.SchauderTranslates.SelectiveSupply
import Lean_Code.SchauderTranslates.Sharp.Contracts
import Lean_Code.SchauderTranslates.Sharp.SoftWindowSharp

/-!
# The sharp selective supply (paper: Proposition `h2:lem:selective`, limits `h2:eq:selective-J`)

The quantified selective supply of blueprint `select:supply`, built from the sharp scalar
supply `ScalarSupplySharp dd` instead of `scalar_blocks`. The information formula
`J = c P_{V ∩ e⊥} + j P_e` with `0 < j < η`, `0 ≤ c < η j`, `1 - M < η j` is unchanged; the
scalar block now carries an augmented prefix constant `K_s < 1 + dd`, a nonconstant raw
inverse diagonal `≤ 1 + 2ε` with an arbitrarily small loss `ε < ε₀`, and is even.
-/

noncomputable section
open MeasureTheory Matrix Filter
open scoped ComplexOrder Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.Sharp
open SchauderTranslates

variable {S ι : Type*} [MeasurableSpace S] [Fintype ι] [DecidableEq ι]

/-- Sharp version of blueprint `select:supply`. -/
theorem selective_blocks_sharp {dd : ℝ} (hS : ScalarSupplySharp dd)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    {κ η ε₀ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hη : 0 < η) (hε₀ : 0 < ε₀) :
    ∃ (L d n : ℕ) (s : ScalarData d n) (m c j ε Ks : ℝ),
      0 < m ∧ m ≤ (1 / 2 : ℝ) ^ L ∧
      s.IsPolynomial ∧ s.IsEven ∧ 0 < ε ∧ ε < ε₀ ∧
      0 ≤ Ks ∧ Ks < 1 + dd ∧ s.AugmentedPrefixSqBound (Ks ^ 2) ∧
      (∀ k : Fin n, (s.rawGram⁻¹ (Sum.inr k) (Sum.inr k)).re ≤ 1 + 2 * ε) ∧
      ∀ (a : SelectiveKernelData S L d n) (φ : ι → BoundedMeasurableComplex S),
        a.scalar = s → a.m = m → a.κ = κ →
        LinearIndependent ℂ (fun i => (φ i).toL2 ρ) →
        a.e.toL2 ρ ∈ atomSpan (fun i => (φ i).toL2 ρ) → ‖a.e.toL2 ρ‖ = 1 →
        informationOperator (a.kernel.marginalMeans ρ (a.packet φ))
            (Matrix.gram ℂ (a.kernel.centered ρ (a.packet φ))) =
          (c : ℂ) • (atomSpan (fun i => (φ i).toL2 ρ) ⊓ (ℂ ∙ a.e.toL2 ρ)ᗮ).starProjection +
            (j : ℂ) • (ℂ ∙ a.e.toL2 ρ).starProjection ∧
        0 < j ∧ j < η ∧ 0 ≤ c ∧ c < η * j ∧ 1 - a.mass < η * j := by
  obtain ⟨cd, hcd, hsupply⟩ := hS
  have hev := (selective_capture (S := S) (ι := ι) (ρ := ρ) hκ0 hκ1).and
    ((soft_spectral_window_sharp hκ0 hκ1 hcd).and
      ((selective_supply_margins_eventually hκ0 hκ1 hη).and softLossLength_eventually_pos))
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  obtain ⟨d, n, s, ε, q, K, hpoly, heven, hfloor, hreal, hε0, hεδ, hε1, hmass, hgain, hq0,
    hq3, hcent, hK0, hK2, haug, hmat, hdiag, hconst⟩ := hsupply (min δ₀ ε₀) (lt_min hδ₀ hε₀)
  have hεδ₀ : ε < δ₀ := hεδ.trans_le (min_le_left _ _)
  have hεε₀ : ε < ε₀ := hεδ.trans_le (min_le_right _ _)
  obtain ⟨hcapε, hwinε, ⟨hm1, hm2, hm3, hm4⟩, hL⟩ := hsub ⟨hε0, hεδ₀⟩
  obtain ⟨m, hm⟩ := hwinε d n s hmass hgain hmat
  set L := softLossLength ε with hLdef
  set M : ℝ := s.mass + (1 - s.mass) * m with hMdef
  set g : ℝ := SchauderTranslates.softCapture s.nonconstantGram s.moment m with hgdef
  set u : ℝ := SchauderTranslates.softCapture s.nonconstantGram s.moment
    (m * seedGamma κ L) with hudef
  set v : ℝ := seedCaptureValue s.nonconstantGram s.moment κ m L with hvdef
  refine ⟨L, d, n, s, m, g / (M - g), v / (M - v), ε, K, hm.mass_pos, hm.mass_le, hpoly,
    heven, hε0, hεε₀, hK0, hK2, haug, hdiag, ?_⟩
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

end SchauderTranslates.Sharp
