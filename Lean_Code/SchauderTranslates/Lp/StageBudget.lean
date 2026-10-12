import Lean_Code.SchauderTranslates.Lp.HaarStrongConstants

noncomputable section
open scoped ENNReal

namespace SchauderTranslates.LpConstruction

def stagePrefixConstant (H : ℝ) : ℝ := 6 * H + 10
def stageKappa (H : ℝ) : ℝ := (8 * stagePrefixConstant H)⁻¹
def stageEditBudget (H : ℝ) (t M : ℕ) : ℝ := stageKappa H * (1 / 2 : ℝ) ^ t / (M : ℝ)

theorem stagePrefixConstant_pos {H : ℝ} (hH : 1 ≤ H) : 0 < stagePrefixConstant H := by
  unfold stagePrefixConstant
  linarith

theorem stageKappa_pos {H : ℝ} (hH : 1 ≤ H) : 0 < stageKappa H :=
  inv_pos.mpr (mul_pos (by norm_num) (stagePrefixConstant_pos hH))

/-- The denominator is the old atom count; the packet size is absent. -/
theorem stageEditBudget_pos {H : ℝ} (hH : 1 ≤ H) (t : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    0 < stageEditBudget H t M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) hM)
  exact div_pos (mul_pos (stageKappa_pos hH) (pow_pos (by norm_num) _)) hMR

theorem stageEditBudget_old_count {H : ℝ} (t : ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (M : ℝ) * stageEditBudget H t M = stageKappa H * (1 / 2 : ℝ) ^ t := by
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 1) hM))
  unfold stageEditBudget
  field_simp

end SchauderTranslates.LpConstruction
