import Lean_Code.SchauderTranslates.Lp.ForestPrivate
import Lean_Code.SchauderTranslates.Lp.IndexNorm

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal) (N : ℕ → ℕ → ℕ)

theorem forestInitial_norm : ‖forestInitial p N‖ = 1 := by
  rw [forestInitial, lp.norm_single (zero_lt_one.trans_le Fact.out)]
  exact norm_one

theorem forestInsert_norm_of_none_zero (j : ℕ) (z : BranchSpace p (N j)) (hz : z none = 0) :
    ‖forestInsert hp N j z‖ = ‖z‖ := by
  apply le_antisymm (forestInsert_bound hp N j z)
  have h := forestExtract_bound hp N j (forestInsert hp N j z)
  simpa only [forestExtract_insert, branchPrivateProjection_apply, hz, zero_smul, sub_zero] using h

theorem forestInsert_disjoint {j k : ℕ} (hjk : j ≠ k)
    (z : BranchSpace p (N j)) (w : BranchSpace p (N k)) (a : ForestPrivateIndex N) :
    forestInsert hp N j z a = 0 ∨ forestInsert hp N k w a = 0 := by
  rcases a with _ | ⟨l, ⟨n, i⟩⟩
  · left; simp
  · by_cases hlj : l = j
    · subst l; right; exact forestInsert_other hp N hjk n i w
    · left; exact forestInsert_other hp N hlj n i z

theorem forest_insert_sum_power (s : Finset ℕ) (z : ∀ j, BranchSpace p (N j))
    (hz : ∀ j, z j none = 0) :
    ‖∑ j ∈ s, forestInsert hp N j (z j)‖ ^ p.toReal = ∑ j ∈ s, ‖z j‖ ^ p.toReal := by
  rw [lp_norm_sum_power_disjoint hp s _ (fun j _ k _ hjk => forestInsert_disjoint hp N hjk _ _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [forestInsert_norm_of_none_zero hp N j (z j) (hz j)]

theorem forestInsert_extract_private (j k n : ℕ) (i : Fin (N k n))
    (y : ForestPrivateSpace p N) :
    forestInsert hp N j (forestExtract hp N j y) (some ⟨k, ⟨n, i⟩⟩) =
      if j = k then y (some ⟨k, ⟨n, i⟩⟩) else 0 := by
  by_cases hjk : j = k
  · subst j; simp
  · rw [if_neg hjk]
    exact forestInsert_other hp N (Ne.symm hjk) n i _

theorem forest_insert_extract_sum_private (s : Finset ℕ) (k n : ℕ) (i : Fin (N k n))
    (y : ForestPrivateSpace p N) :
    (∑ j ∈ s, forestInsert hp N j (forestExtract hp N j y)) (some ⟨k, ⟨n, i⟩⟩) =
      if k ∈ s then y (some ⟨k, ⟨n, i⟩⟩) else 0 := by
  classical
  simp only [lp.coeFn_sum, Finset.sum_apply, forestInsert_extract_private]
  simp

theorem forest_insert_extract_sum_bound (s : Finset ℕ) (y : ForestPrivateSpace p N) :
    ‖∑ j ∈ s, forestInsert hp N j (forestExtract hp N j y)‖ ≤ ‖y‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro a
  rcases a with _ | ⟨k, ⟨n, i⟩⟩
  · simp
  · rw [forest_insert_extract_sum_private]
    split_ifs <;> simp

theorem forest_extract_sum_power_le (s : Finset ℕ) (y : ForestPrivateSpace p N) :
    (∑ j ∈ s, ‖forestExtract hp N j y‖ ^ p.toReal) ≤ ‖y‖ ^ p.toReal := by
  rw [← forest_insert_sum_power hp N s _ (fun j => forestExtract_none hp N j y)]
  exact Real.rpow_le_rpow (norm_nonneg _) (forest_insert_extract_sum_bound hp N s y) hp.le

theorem forest_initial_insert_sum_power (s : Finset ℕ) (c : ℂ)
    (z : ∀ j, BranchSpace p (N j)) (hz : ∀ j, z j none = 0) :
    ‖c • forestInitial p N + ∑ j ∈ s, forestInsert hp N j (z j)‖ ^ p.toReal =
      ‖c‖ ^ p.toReal + ∑ j ∈ s, ‖z j‖ ^ p.toReal := by
  have hdis : ∀ a, (c • forestInitial p N) a = 0 ∨
      (∑ j ∈ s, forestInsert hp N j (z j)) a = 0 := by
    intro a
    rcases a with _ | ⟨k, ⟨n, i⟩⟩
    · right; simp
    · left; simp [forestInitial, Pi.single_apply, lp.coeFn_smul]
  rw [lp_norm_add_power_disjoint hp _ _ hdis, norm_smul, forestInitial_norm N, mul_one,
    forest_insert_sum_power hp N s z hz]

theorem forest_initial_extract_sum_bound (s : Finset ℕ) (y : ForestPrivateSpace p N) :
    ‖y none • forestInitial p N + ∑ j ∈ s, forestInsert hp N j (forestExtract hp N j y)‖ ≤ ‖y‖ := by
  apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  intro a
  rcases a with _ | ⟨k, ⟨n, i⟩⟩
  · simp [lp.coeFn_smul, forestInitial]
  · simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
      forestInitial, lp.coeFn_single, Pi.single_apply, reduceCtorEq, if_false, smul_zero, zero_add]
    rw [forest_insert_extract_sum_private]
    split_ifs <;> simp

theorem forest_initial_extract_sum_power_le (s : Finset ℕ) (y : ForestPrivateSpace p N) :
    ‖y none‖ ^ p.toReal + (∑ j ∈ s, ‖forestExtract hp N j y‖ ^ p.toReal) ≤ ‖y‖ ^ p.toReal := by
  rw [← forest_initial_insert_sum_power hp N s (y none) _
    (fun j => forestExtract_none hp N j y)]
  exact Real.rpow_le_rpow (norm_nonneg _) (forest_initial_extract_sum_bound hp N s y) hp.le

end SchauderTranslates.LpConstruction
