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

end SchauderTranslates
