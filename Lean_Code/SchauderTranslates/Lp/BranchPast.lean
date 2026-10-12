import Lean_Code.SchauderTranslates.Lp.BranchCuts

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem reverse_half_geometric (n : ℕ) :
    (∑ l ∈ Finset.range n, (1 / 2 : ℝ) ^ (n - l)) = 1 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hs : (∑ l ∈ Finset.range n, (1 / 2 : ℝ) ^ (n + 1 - l)) =
        (1 / 2 : ℝ) * ∑ l ∈ Finset.range n, (1 / 2 : ℝ) ^ (n - l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [show n + 1 - l = (n - l) + 1 from by have := Finset.mem_range.mp hl; omega, pow_succ]
      ring
    rw [hs, ih, show n + 1 - n = 1 from by omega, pow_succ]
    ring

theorem branch_ratio_dual_power {P : ℝ} (hP : 1 < P) :
    branchRatio P ^ Real.conjExponent P = 1 / 2 := by
  have h := layer_dual_power hP (by decide : 1 ≤ 2)
  change (2 : ℝ) * branchRatio P ^ Real.conjExponent P = 1 at h
  linarith

theorem branch_scalar_formula {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (n : ℕ) (z : BranchSpace p N) :
    branchScalar p N n z = (branchRatio p.toReal : ℂ) ^ n * z none -
      ∑ l ∈ Finset.range n, (branchRatio p.toReal : ℂ) ^ (n - l) * branchMean p N l z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [branchScalar_succ, ih, Finset.sum_range_succ]
    have hs : (∑ l ∈ Finset.range n,
        (branchRatio p.toReal : ℂ) ^ (n + 1 - l) * branchMean p N l z) =
        (branchRatio p.toReal : ℂ) * ∑ l ∈ Finset.range n,
          (branchRatio p.toReal : ℂ) ^ (n - l) * branchMean p N l z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [show n + 1 - l = (n - l) + 1 from by have := Finset.mem_range.mp hl; omega, pow_succ]
      ring
    rw [hs, show n + 1 - n = 1 from by omega, pow_succ, pow_one]
    ring

def pastPrivateIndices (N : ℕ → ℕ) (n : ℕ) : Finset (BranchIndex N) :=
  ((Finset.range n).sigma fun l => (Finset.univ : Finset (Fin (N l)))).image some

def branchPastWeight (p : ℝ≥0∞) (N : ℕ → ℕ) (n : ℕ) : BranchIndex N → ℂ
  | none => 0
  | some ⟨l, _⟩ => (branchRatio p.toReal : ℂ) ^ (n - l) * (layerDualScale p.toReal (N l) : ℂ)

theorem branch_past_sum {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (n : ℕ) (z : BranchSpace p N) :
    (∑ l ∈ Finset.range n, (branchRatio p.toReal : ℂ) ^ (n - l) * branchMean p N l z) =
      ∑ k ∈ pastPrivateIndices N n, branchPastWeight p N n k * z k := by
  rw [pastPrivateIndices, Finset.sum_image (fun _ _ _ _ h => Option.some_injective _ h), Finset.sum_sigma]
  simp [branchPastWeight, Finset.mul_sum, mul_assoc]

theorem branch_past_weight_power {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) :
    (∑ k ∈ pastPrivateIndices N n,
      ‖branchPastWeight p N n k‖ ^ Real.conjExponent p.toReal) = 1 - (1 / 2 : ℝ) ^ n := by
  rw [pastPrivateIndices, Finset.sum_image (fun _ _ _ _ h => Option.some_injective _ h), Finset.sum_sigma]
  have hs : (∑ l ∈ Finset.range n, ∑ _ : Fin (N l),
      ‖(branchRatio p.toReal : ℂ) ^ (n - l) * (layerDualScale p.toReal (N l) : ℂ)‖ ^
        Real.conjExponent p.toReal) = ∑ l ∈ Finset.range n, (1 / 2 : ℝ) ^ (n - l) := by
    apply Finset.sum_congr rfl
    intro l _
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (branch_ratio_pos _), abs_of_pos (layer_scale_pos p.toReal (hN l)).2,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.mul_rpow (pow_nonneg (branch_ratio_pos _).le _) (layer_scale_pos p.toReal (hN l)).2.le,
      ← Real.rpow_pow_comm (branch_ratio_pos _).le, branch_ratio_dual_power hp]
    have h := layer_dual_power hp (hN l)
    linear_combination (1 / 2 : ℝ) ^ (n - l) * h
  exact hs.trans (reverse_half_geometric n)

theorem branch_past_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) (z : BranchSpace p N) :
    ‖∑ l ∈ Finset.range n, (branchRatio p.toReal : ℂ) ^ (n - l) * branchMean p N l z‖ ≤ ‖z‖ := by
  rw [branch_past_sum]
  have hconj := Real.HolderConjugate.conjExponent hp
  have hsum : (∑ k ∈ pastPrivateIndices N n,
      ‖branchPastWeight p N n k‖ ^ Real.conjExponent p.toReal) ≤ 1 := by
    rw [branch_past_weight_power hp N hN]
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
    linarith
  have hfactor : (∑ k ∈ pastPrivateIndices N n,
      ‖branchPastWeight p N n k‖ ^ Real.conjExponent p.toReal) ^
        (1 / Real.conjExponent p.toReal) ≤ 1 := by
    simpa using Real.rpow_le_rpow (by positivity) hsum (one_div_nonneg.mpr hconj.symm.nonneg)
  calc
    _ ≤ _ := finite_lp_functional_bound hp (pastPrivateIndices N n) (branchPastWeight p N n) z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg z)
    _ = ‖z‖ := one_mul _

theorem branchScalar_private_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p.toReal)
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) (z : BranchSpace p N) (hz : z none = 0) :
    ‖branchScalar p N n z‖ ≤ ‖z‖ := by
  rw [branch_scalar_formula, hz, mul_zero, zero_sub, norm_neg]
  exact branch_past_bound hp N hN n z

end SchauderTranslates.LpConstruction
