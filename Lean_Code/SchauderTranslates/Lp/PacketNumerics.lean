import Lean_Code.SchauderTranslates.Lp.PacketScales

noncomputable section

namespace SchauderTranslates.LpConstruction

def packetAmplitude (P d : ℝ) (N : ℕ) : ℝ :=
  d * (N : ℝ) ^ (-(P - 1) / P)

theorem packet_amplitude_pos {P d : ℝ} {N : ℕ} (hd : 0 < d) (hN : 1 ≤ N) :
    0 < packetAmplitude P d N := by
  unfold packetAmplitude
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hN)
  exact mul_pos hd (Real.rpow_pos_of_pos hNR _)

theorem packet_amplitude_rpow {P d : ℝ} {N : ℕ}
    (hP : 0 < P) (hd : 0 ≤ d) (hN : 1 ≤ N) :
    packetAmplitude P d N ^ P = d ^ P * (N : ℝ) ^ (-(P - 1)) := by
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  unfold packetAmplitude
  rw [Real.mul_rpow hd (Real.rpow_nonneg hNR _), ← Real.rpow_mul hNR]
  congr 2
  exact div_mul_cancel₀ _ (ne_of_gt hP)

theorem packet_scale_rpow {P V : ℝ} {N : ℕ} (hP : 0 < P) (hV : 0 ≤ V)
    (hden : 0 < 1 - packetDeficit P N) :
    packetScale P V N ^ P = V ^ P / (1 - packetDeficit P N) := by
  unfold packetScale
  rw [one_div, Real.rpow_inv_rpow (div_nonneg (Real.rpow_nonneg hV _) hden.le) (ne_of_gt hP)]

theorem packet_scale_balance {P V d : ℝ} {N : ℕ}
    (hP : 0 < P) (hV : 0 ≤ V) (hden : 0 < 1 - packetDeficit P N)
    (hd : d = packetScale P V N) :
    d ^ P * (1 - packetDeficit P N) = V ^ P := by
  rw [hd, packet_scale_rpow hP hV hden, div_mul_cancel₀ _ (ne_of_gt hden)]

theorem packet_noise_power {P V d : ℝ} {N : ℕ}
    (hP : 0 < P) (hd : 0 ≤ d) (hN : 1 ≤ N)
    (hbal : d ^ P * (1 - packetDeficit P N) = V ^ P) :
    V ^ P + ((N - 1 : ℕ) : ℝ) * packetAmplitude P d N ^ P = d ^ P := by
  rw [packet_amplitude_rpow hP hd hN, Nat.cast_sub hN, Nat.cast_one]
  unfold packetDeficit at hbal
  nlinarith [hbal]

theorem packet_edit_cost_power {P d : ℝ} {N : ℕ}
    (hP : 0 < P) (hd : 0 ≤ d) (hN : 1 ≤ N) :
    (d * (N : ℝ) ^ (2 / P - 1)) ^ P = (N : ℝ) * packetAmplitude P d N ^ P := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hN)
  rw [Real.mul_rpow hd (Real.rpow_nonneg hNR.le _), ← Real.rpow_mul hNR.le,
    packet_amplitude_rpow hP hd hN]
  have he : (2 / P - 1) * P = 2 - P := by field_simp
  rw [he]
  have hpow : (N : ℝ) ^ (2 - P) = (N : ℝ) * (N : ℝ) ^ (-(P - 1)) := by
    calc
      (N : ℝ) ^ (2 - P) = (N : ℝ) ^ (1 + (-(P - 1))) := by congr 1; ring
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(P - 1)) := Real.rpow_add hNR _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hpow]
  ring

end SchauderTranslates.LpConstruction
