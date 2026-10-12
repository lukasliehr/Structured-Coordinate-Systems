import Lean_Code.SchauderTranslates.Lp.ForestDiagonal

noncomputable section
open Filter
open scoped BigOperators ENNReal Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

/-- Root index zero corresponds to the manuscript's root index one. -/
def forestWarmWeight (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j + 1)

theorem forestWarmWeight_pos (j : ℕ) : 0 < forestWarmWeight j :=
  pow_pos (by norm_num) _

theorem forestWarmWeight_sum_range (n : ℕ) :
    (∑ j ∈ Finset.range n, forestWarmWeight j) = 1 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp only [forestWarmWeight, pow_succ]; ring

theorem forestWarmWeight_sum_le (s : Finset ℕ) : (∑ j ∈ s, forestWarmWeight j) ≤ 1 := by
  have hs : s ⊆ Finset.range (s.sup id + 1) := by
    intro j hj
    have hj' : j ≤ s.sup id := Finset.le_sup (f := id) hj
    exact Finset.mem_range.mpr (by omega)
  calc
    _ ≤ ∑ j ∈ Finset.range (s.sup id + 1), forestWarmWeight j :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun j _ _ => (forestWarmWeight_pos j).le)
    _ = 1 - (1 / 2 : ℝ) ^ (s.sup id + 1) := forestWarmWeight_sum_range _
    _ ≤ 1 := by have h := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (s.sup id + 1); linarith

theorem exists_forest_warm_depth {P : ℝ} (hP : 0 < P) (j : ℕ) :
    ∃ L : ℕ, 1 ≤ L ∧ 3 * branchBeta P ^ L ≤ forestWarmWeight j := by
  have ht : Tendsto (fun n : ℕ => 3 * branchBeta P ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (branch_beta_pos P).le (branch_beta_lt_one hP))
  have he : ∀ᶠ n : ℕ in atTop, 3 * branchBeta P ^ n < forestWarmWeight j :=
    (tendsto_order.mp ht).2 _ (forestWarmWeight_pos j)
  obtain ⟨n, hn, hsmall⟩ := ((eventually_ge_atTop 1).and he).exists
  exact ⟨n, hn, hsmall.le⟩

theorem exists_forest_warm_depths {P : ℝ} (hP : 0 < P) :
    ∃ L : ℕ → ℕ, ∀ j, 1 ≤ L j ∧ 3 * branchBeta P ^ L j ≤ forestWarmWeight j := by
  choose L hL using exists_forest_warm_depth hP
  exact ⟨L, hL⟩

theorem forest_warm_depth_bound {P : ℝ} (hP : 0 < P) {L n j : ℕ} (hLn : L ≤ n)
    (hL : 3 * branchBeta P ^ L ≤ forestWarmWeight j) :
    3 * branchBeta P ^ n ≤ forestWarmWeight j :=
  (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (branch_beta_pos P).le
    (branch_beta_lt_one hP).le hLn) (by norm_num)).trans hL

/-- All warmed branches cost at most one private norm, and the possible
newest branch costs at most three. -/
theorem forest_private_root_sum_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ℕ) (newest : ℕ) (f : ℕ → E) (hf : ∀ j, ‖f j‖ = 1)
    (c : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hnew : ∀ j ∈ s, ‖c j‖ ≤ 3 * C)
    (hwarm : ∀ j ∈ s, j ≠ newest → ‖c j‖ ≤ forestWarmWeight j * C) :
    ‖∑ j ∈ s, c j • f j‖ ≤ 4 * C := by
  classical
  have hb (j : ℕ) (hj : j ∈ s) :
      ‖c j • f j‖ ≤ (forestWarmWeight j + if j = newest then 3 else 0) * C := by
    rw [norm_smul, hf, mul_one]
    by_cases hje : j = newest
    · rw [if_pos hje]
      exact (hnew j hj).trans (by nlinarith [forestWarmWeight_pos j])
    · simpa only [if_neg hje, add_zero] using hwarm j hj hje
  have hi : (∑ j ∈ s, if j = newest then (3 : ℝ) else 0) ≤ 3 := by
    simp only [Finset.sum_ite_eq']
    split_ifs <;> norm_num
  calc
    _ ≤ ∑ j ∈ s, ‖c j • f j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s, (forestWarmWeight j + if j = newest then 3 else 0) * C :=
      Finset.sum_le_sum hb
    _ = ((∑ j ∈ s, forestWarmWeight j) + ∑ j ∈ s, if j = newest then 3 else 0) * C := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
    _ ≤ (1 + 3) * C := mul_le_mul_of_nonneg_right (add_le_add (forestWarmWeight_sum_le s) hi) hC
    _ = 4 * C := by ring

end SchauderTranslates.LpConstruction
