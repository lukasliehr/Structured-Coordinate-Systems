import Lean_Code.PositiveBiorthogonal.Definitions
import Mathlib.Tactic

/-! Error parameters (`lem:parameters`) used by the construction in FinalExistence.lean. -/
noncomputable section
set_option autoImplicit false

namespace PositiveBiorthogonal

theorem error_parameters (ε : ℝ) (hε : 0 < ε) :
    let t := min ε 1 / 8
    0 < t / 2 ∧ 0 < t ∧ t < 1 ∧
      ((1 + t) / (1 - t)) * (1 + t / 2 + t / 2) < 1 + ε := by
  dsimp only
  set t := min ε 1 / 8 with ht
  have ht0 : 0 < t := div_pos (lt_min hε (by norm_num)) (by norm_num)
  have ht8 : t ≤ 1 / 8 := div_le_div_of_nonneg_right (min_le_right ε 1) (by norm_num)
  have hte : t ≤ ε / 8 := div_le_div_of_nonneg_right (min_le_left ε 1) (by norm_num)
  refine ⟨by positivity, ht0, by linarith, ?_⟩
  have hd : 0 < 1 - t := by linarith
  have hstep : ((1 + t) / (1 - t)) * (1 + t / 2 + t / 2) < 1 + 4 * t := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith
  linarith

end PositiveBiorthogonal
