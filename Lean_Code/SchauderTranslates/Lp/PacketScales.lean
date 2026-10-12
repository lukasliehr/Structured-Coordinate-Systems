import Mathlib

noncomputable section
open Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def packetDeficit (p : ℝ) (N : ℕ) : ℝ :=
  ((N : ℝ) - 1) * (N : ℝ) ^ (-(p - 1))

def packetScale (p V : ℝ) (N : ℕ) : ℝ :=
  (V ^ p / (1 - packetDeficit p N)) ^ (1 / p)

def packetCost (p V : ℝ) (N : ℕ) : ℝ :=
  packetScale p V N * (N : ℝ) ^ (2 / p - 1)

theorem packet_deficit_tendsto {p : ℝ} (hp : 2 < p) :
    Tendsto (packetDeficit p) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (2 - p)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hp)).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' ?_ ?_ hpow
  · filter_upwards [eventually_ge_atTop 1] with N hN
    dsimp [packetDeficit]
    have hcast : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hcast : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpos : (0 : ℝ) < N := by linarith
    calc
      packetDeficit p N ≤ (N : ℝ) * (N : ℝ) ^ (-(p - 1)) := by
        unfold packetDeficit
        gcongr
        linarith
      _ = (N : ℝ) ^ (2 - p) := by
        calc
          (N : ℝ) * (N : ℝ) ^ (-(p - 1)) =
              (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(p - 1)) := by rw [Real.rpow_one]
          _ = (N : ℝ) ^ (1 + (-(p - 1))) := (Real.rpow_add hpos _ _).symm
          _ = (N : ℝ) ^ (2 - p) := by congr 1; ring

theorem packet_scale_tendsto {p V : ℝ} (hp : 2 < p) (hV : 0 < V) :
    Tendsto (packetScale p V) atTop (𝓝 V) := by
  have hden : Tendsto (fun N => 1 - packetDeficit p N) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (packet_deficit_tendsto hp)
  have hquot : Tendsto (fun N => V ^ p / (1 - packetDeficit p N)) atTop (𝓝 (V ^ p)) := by
    convert! (tendsto_const_nhds (x := V ^ p)).div hden
      (by norm_num : (1 : ℝ) ≠ 0) using 1
    simp
  have hp0 : 0 < p := by linarith
  have hpow : Tendsto (fun N => (V ^ p / (1 - packetDeficit p N)) ^ (1 / p))
      atTop (𝓝 ((V ^ p) ^ (1 / p))) :=
    hquot.rpow_const (Or.inr (by positivity))
  have hroot : (V ^ p) ^ (1 / p) = V := by
    rw [← Real.rpow_mul hV.le]
    have hpn : p ≠ 0 := by linarith
    simp [hpn]
  change Tendsto (fun N => (V ^ p / (1 - packetDeficit p N)) ^ (1 / p)) atTop (𝓝 V)
  simpa only [hroot] using hpow

theorem packet_cost_tendsto {p V : ℝ} (hp : 2 < p) (hV : 0 < V) :
    Tendsto (packetCost p V) atTop (𝓝 0) := by
  have hneg : 0 < 1 - 2 / p := by
    have hpos : 0 < p := by linarith
    have hlt : 2 / p < 1 := (div_lt_one hpos).mpr hp
    linarith
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (2 / p - 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop
  change Tendsto (fun N => packetScale p V N * (N : ℝ) ^ (2 / p - 1)) atTop (𝓝 0)
  simpa only [mul_zero] using (packet_scale_tendsto hp hV).mul hpow

/-- Blueprint `lp:scales`. Choose the integer packet size before its support
placement. This lemma retains the exact denominator and the strict p > 2 input. -/
theorem packet_scales {p V : ℝ} (hp : 2 < p) (hV : 0 < V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (d : ℝ), 1 ≤ N ∧
      (1 / 2 : ℝ) ≤ 1 - packetDeficit p N ∧
      d = (V ^ p / (1 - packetDeficit p N)) ^ (1 / p) ∧
      0 < d ∧ d * (N : ℝ) ^ (2 / p - 1) ≤ ε := by
  have hdef : ∀ᶠ N in atTop, packetDeficit p N < (1 / 2 : ℝ) :=
    (packet_deficit_tendsto hp).eventually (eventually_lt_nhds (by norm_num))
  have hcost : ∀ᶠ N in atTop, packetCost p V N < ε :=
    (packet_cost_tendsto hp hV).eventually (eventually_lt_nhds hε)
  obtain ⟨N, hN, hd, hc⟩ := ((eventually_ge_atTop 1).and (hdef.and hcost)).exists
  refine ⟨N, packetScale p V N, hN, by linarith, rfl, ?_, hc.le⟩
  unfold packetScale
  apply Real.rpow_pos_of_pos
  exact div_pos (Real.rpow_pos_of_pos hV _) (by linarith)

end SchauderTranslates.LpConstruction
