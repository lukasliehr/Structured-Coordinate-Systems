import Lean_Code.SchauderTranslates.ScalarRowNumerics

noncomputable section
namespace SchauderTranslates

/-- The total centered-prefix budget from the scalar paper construction. -/
def scalarPrefixBudget : ℝ := 2 + 15 / 323 + 1 / 15

theorem scalarPrefixBudget_lt_three : scalarPrefixBudget < 3 := by norm_num [scalarPrefixBudget]

/-- A reserve in the combined prefix/deficit budget makes the induction noncircular. -/
theorem scalar_stage_budget_step {k : ℕ} {ε ε' q η η' : ℝ}
    (hbudget : q + (2 / 3) * ε + 10 * η ≤ scalarPrefixBudget - (5 / 323) * (1 / 2) ^ k)
    (he : ε' ≤ ε - 3 * ε ^ 2 / 4)
    (hη : η' ≤ (1 / 323) / 8 * (1 / 2) ^ k) :
    (q + 10 * η + ε ^ 2 / 2) + (2 / 3) * ε' + 10 * η' ≤
      scalarPrefixBudget - (5 / 323) * (1 / 2) ^ (k + 1) := by
  rw [pow_succ (1 / 2 : ℝ) k]
  have hn : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  nlinarith

/-- The matching gain reserve pays for the new copy's gain loss at each stage. -/
theorem scalar_stage_gain_step {k : ℕ} {Z Z' η' : ℝ}
    (hZ : (3 / 4) * (1 / 323) + (1 / 4) * (1 / 323) * (1 / 2) ^ k ≤ Z)
    (hloss : Z - η' ≤ Z') (hη : η' ≤ (1 / 323) / 8 * (1 / 2) ^ k) :
    (3 / 4) * (1 / 323) + (1 / 4) * (1 / 323) * (1 / 2) ^ (k + 1) ≤ Z' := by
  rw [pow_succ (1 / 2 : ℝ) k]
  linarith

end SchauderTranslates
