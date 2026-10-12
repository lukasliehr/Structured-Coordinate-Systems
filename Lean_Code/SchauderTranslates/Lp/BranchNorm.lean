import Lean_Code.SchauderTranslates.Lp.BranchModel

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem lp_norm_add_power_disjoint {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (f g : lp (fun _ : ι => ℂ) p)
    (hdis : ∀ i, f i = 0 ∨ g i = 0) :
    ‖f + g‖ ^ p.toReal = ‖f‖ ^ p.toReal + ‖g‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp, lp.norm_rpow_eq_tsum hp f, lp.norm_rpow_eq_tsum hp g,
    ← Summable.tsum_add ((lp.memℓp f).summable hp) ((lp.memℓp g).summable hp)]
  apply tsum_congr
  intro i
  rcases hdis i with hf | hg
  · simp [lp.coeFn_add, hf, hp.ne']
  · simp [lp.coeFn_add, hg, hp.ne']

theorem branchRoot_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ) :
    ‖branchRoot p N‖ = 1 := by
  rw [branchRoot, lp.norm_single (zero_lt_one.trans_le Fact.out)]
  exact norm_one

theorem branchUnit_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ → ℕ)
    (n : ℕ) (i : Fin (N n)) : ‖branchUnit p N n i‖ = 1 := by
  rw [branchUnit, lp.norm_single (zero_lt_one.trans_le Fact.out)]
  exact norm_one

theorem branchMeanVector_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) : ‖branchMeanVector p N n‖ = 1 := by
  have hinj : Function.Injective (fun i : Fin (N n) => (some ⟨n, i⟩ : BranchIndex N)) := by
    intro i j hij
    simpa only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using hij
  have hsum : (∑ i : Fin (N n), branchUnit p N n i) =
      ∑ k ∈ Finset.univ.image (fun i : Fin (N n) => (some ⟨n, i⟩ : BranchIndex N)),
        lp.single p k (1 : ℂ) := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    rfl
  have hpow : ‖branchMeanVector p N n‖ ^ p.toReal = 1 := by
    rw [branchMeanVector, norm_smul, Real.norm_eq_abs,
      abs_of_pos (layer_scale_pos p.toReal (hN n)).1,
      Real.mul_rpow (layer_scale_pos p.toReal (hN n)).1.le (norm_nonneg _), hsum,
      lp.norm_sum_single hp]
    simpa [Finset.card_image_of_injective _ hinj, mul_comm] using layer_primal_power hp (hN n)
  apply (Real.rpow_left_inj (norm_nonneg _) zero_le_one hp.ne').mp
  simpa using hpow

theorem branchResidual_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) : ‖branchResidual p N n‖ = 1 := by
  induction n with
  | zero => exact branchRoot_norm N
  | succ n ih =>
    have hdis : ∀ k, branchResidual p N n k = 0 ∨ (-branchMeanVector p N n) k = 0 := by
      intro k
      rcases k with _ | ⟨l, i⟩
      · right; simp [lp.coeFn_neg]
      · by_cases hln : l = n
        · subst l
          left
          exact branchResidual_private_future p N le_rfl i
        · right
          simp [lp.coeFn_neg, branchMeanVector_other p N hln]
    have hpow : ‖branchResidual p N (n + 1)‖ ^ p.toReal = 1 := by
      rw [branchResidual, norm_smul, Real.norm_eq_abs, abs_of_pos (branch_beta_pos _),
        Real.mul_rpow (branch_beta_pos _).le (norm_nonneg _), branch_beta_power hp,
        sub_eq_add_neg, lp_norm_add_power_disjoint hp _ _ hdis,
        ih, norm_neg, branchMeanVector_norm hp N hN]
      norm_num
    apply (Real.rpow_left_inj (norm_nonneg _) zero_le_one hp.ne').mp
    simpa using hpow

theorem branchMean_meanVector {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    (N : ℕ → ℕ) (hN : ∀ n, 1 ≤ N n) (n : ℕ) :
    branchMean p N n (branchMeanVector p N n) = 1 := by
  have hc : ((N n : ℝ) : ℂ) * (layerPrimalScale p.toReal (N n) : ℂ) *
      (layerDualScale p.toReal (N n) : ℂ) = 1 := by
    exact_mod_cast layer_scale_product hp (hN n)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hc

end SchauderTranslates.LpConstruction
