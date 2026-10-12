import Lean_Code.SchauderTranslates.Lp.HaarDyadicStrong

noncomputable section

namespace SchauderTranslates.LpConstruction

def haarStrongPower (s : ℝ) : ℝ := s * (6 / (s - 1) + 4 / (2 - s))

def haarStrongConstant (s : ℝ) : ℝ := haarStrongPower s ^ (1 / s)

theorem haarStrongPower_pos {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) : 0 < haarStrongPower s := by
  unfold haarStrongPower
  have h1 : 0 < s - 1 := by linarith
  have h2 : 0 < 2 - s := by linarith
  positivity

theorem haarStrongConstant_pos {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) : 0 < haarStrongConstant s :=
  Real.rpow_pos_of_pos (haarStrongPower_pos hs1 hs2) _

theorem haarStrongConstant_rpow {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    haarStrongConstant s ^ s = haarStrongPower s := by
  rw [haarStrongConstant, one_div]
  exact Real.rpow_inv_rpow (haarStrongPower_pos hs1 hs2).le (by linarith : s ≠ 0)

end SchauderTranslates.LpConstruction
