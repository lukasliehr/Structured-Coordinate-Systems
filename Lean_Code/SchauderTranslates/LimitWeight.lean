import Lean_Code.SchauderTranslates.Contracts

noncomputable section
open Filter
open scoped BigOperators Topology

namespace SchauderTranslates

/-- Fairness means that every target occurs arbitrarily late. -/
def FairSchedule {α : Type*} (s : ℕ → α) : Prop :=
  ∀ a N, ∃ n ≥ N, s n = a

/-- Pairing supplies repeated visits without any assumptions on an enumeration's order. -/
theorem fair_schedule_of_surjective {α : Type*} (q : ℕ → α)
    (hq : Function.Surjective q) : FairSchedule (fun n => q (Nat.unpair n).1) := by
  intro a N
  obtain ⟨j, rfl⟩ := hq a
  exact ⟨Nat.pair j N, Nat.right_le_pair j N, by simp⟩

def lossBudget (n : ℕ) : ℝ := (1 / 16) * (1 / 2) ^ n
def prefixBudget (n : ℕ) : ℝ := (1 / 8) * (1 / 2) ^ n

theorem lossBudget_pos (n : ℕ) : 0 < lossBudget n := by
  unfold lossBudget
  positivity

theorem prefixBudget_pos (n : ℕ) : 0 < prefixBudget n := by
  unfold prefixBudget
  positivity

theorem hasSum_lossBudget : HasSum lossBudget (1 / 8) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 16)
  norm_num at h
  exact h

theorem hasSum_prefixBudget : HasSum prefixBudget (1 / 4) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (1 / 8)
  norm_num at h
  exact h

/-- A rational schedule and the two summable positive budgets used by the construction. -/
theorem fair_schedule : ∃ s : ℕ → ℚ, FairSchedule s ∧
    (∀ n, 0 < lossBudget n ∧ 0 < prefixBudget n) ∧
    HasSum lossBudget (1 / 8) ∧ HasSum prefixBudget (1 / 4) ∧
    (1 / 8 : ℝ) < 1 / 2 ∧ (1 / 4 : ℝ) < 1 := by
  obtain ⟨q, hq⟩ := exists_surjective_nat ℚ
  exact ⟨fun n => q (Nat.unpair n).1, fair_schedule_of_surjective q hq,
    fun n => ⟨lossBudget_pos n, prefixBudget_pos n⟩,
    hasSum_lossBudget, hasSum_prefixBudget, by norm_num, by norm_num⟩

end SchauderTranslates
