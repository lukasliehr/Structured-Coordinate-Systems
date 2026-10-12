import Lean_Code.SchauderTranslates.Lp.PacketNumerics
import Mathlib.Analysis.Normed.Lp.lpSpace

noncomputable section

namespace SchauderTranslates.LpConstruction

def layerPrimalScale (P : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-1 / P)
def layerDualScale (P : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-(P - 1) / P)
def branchBeta (P : ℝ) : ℝ := (2 : ℝ) ^ (-1 / P)
def branchRatio (P : ℝ) : ℝ := (2 : ℝ) ^ (-(P - 1) / P)

theorem layer_scale_pos (P : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    0 < layerPrimalScale P N ∧ 0 < layerDualScale P N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) hN)
  exact ⟨Real.rpow_pos_of_pos hn _, Real.rpow_pos_of_pos hn _⟩

theorem layer_scale_product {P : ℝ} (hP : 0 < P) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * layerPrimalScale P N * layerDualScale P N = 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) hN)
  rw [layerPrimalScale, layerDualScale, mul_assoc, ← Real.rpow_add hn]
  have he : -1 / P + -(P - 1) / P = -1 := by field_simp; ring
  rw [he, Real.rpow_neg_one, mul_inv_cancel₀ (ne_of_gt hn)]

theorem layer_primal_power {P : ℝ} (hP : 0 < P) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * layerPrimalScale P N ^ P = 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 1) hN)
  rw [layerPrimalScale, ← Real.rpow_mul hn.le, div_mul_cancel₀ _ (ne_of_gt hP),
    Real.rpow_neg_one, mul_inv_cancel₀ (ne_of_gt hn)]

theorem branch_beta_ratio {P : ℝ} (hP : 0 < P) :
    branchBeta P * branchRatio P = 1 / 2 := by
  rw [branchBeta, branchRatio, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have he : -1 / P + -(P - 1) / P = -1 := by field_simp; ring
  rw [he, Real.rpow_neg_one]
  norm_num

theorem branch_beta_power {P : ℝ} (hP : 0 < P) : branchBeta P ^ P = 1 / 2 := by
  rw [branchBeta, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    div_mul_cancel₀ _ (ne_of_gt hP), Real.rpow_neg_one]
  norm_num

theorem branch_beta_pos (P : ℝ) : 0 < branchBeta P := Real.rpow_pos_of_pos (by norm_num) _
theorem branch_ratio_pos (P : ℝ) : 0 < branchRatio P := Real.rpow_pos_of_pos (by norm_num) _

theorem branch_beta_lt_one {P : ℝ} (hP : 0 < P) : branchBeta P < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (div_neg_of_neg_of_pos (by norm_num) hP)

theorem branch_ratio_lt_one {P : ℝ} (hP : 1 < P) : branchRatio P < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (div_neg_of_neg_of_pos (neg_neg_of_pos (by linarith)) (by linarith))

theorem coupling_exponent {P : ℝ} (hP : 1 < P) :
    -(P - 1) / P = -1 / (P / (P - 1)) := by
  field_simp

end SchauderTranslates.LpConstruction
