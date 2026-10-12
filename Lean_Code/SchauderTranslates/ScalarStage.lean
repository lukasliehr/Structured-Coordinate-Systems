import Lean_Code.SchauderTranslates.ScalarInductionInitial
import Lean_Code.SchauderTranslates.ScalarStageBudget

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The full scalar-stage invariant. The reserve inequalities keep the next choice step
inside the admissible gain and prefix ranges before those ranges are used in its proof. -/
structure ScalarStage (k : ℕ) where
  dimension : ℕ
  length : ℕ
  data : ScalarData dimension length
  ε : ℝ
  q : ℝ
  η : ℝ
  deficit_pos : 0 < ε
  deficit_le : ε ≤ 1 / 10
  mass_eq : data.mass = 1 - ε
  even : data.IsEven
  positiveFloor : data.HasPositiveFloor
  gain_lower : (3 / 4) * (1 / 323) + (1 / 4) * (1 / 323) * (1 / 2) ^ k ≤ data.gain
  gain_upper : data.gain ≤ 1 / 323
  inverse_norm : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ)) data.rawGram⁻¹‖ ≤ ε⁻¹ ^ 2
  inverse_excess : ∀ i : Fin length, (data.rawGram⁻¹ (Sum.inr i) (Sum.inr i)).re - 1 ≤ 2 * ε
  q_lower : 2 ≤ q
  η_nonneg : 0 ≤ η
  centered : data.CenteredPrefixSqBound q
  augmented : data.AugmentedPrefixSqBound (q + 10 * η)
  budget : q + (2 / 3) * ε + 10 * η ≤ scalarPrefixBudget - (5 / 323) * (1 / 2) ^ k

namespace ScalarStage
variable {k : ℕ}

theorem gain_admissible (s : ScalarStage k) : 1 / 646 ≤ s.data.gain := by
  have hg := s.gain_lower
  have hp : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  nlinarith

theorem augmented_budget_lt_three (s : ScalarStage k) : s.q + 10 * s.η < 3 := by
  have hp : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  have hb := s.budget
  have he := s.deficit_pos
  have hA := scalarPrefixBudget_lt_three
  nlinarith

theorem q_lt_three (s : ScalarStage k) : s.q < 3 := by
  linarith [s.augmented_budget_lt_three, s.η_nonneg]

/-- The starting block satisfies the complete invariant, including the augmented prefix bound. -/
def initial : ScalarStage 0 where
  dimension := 1
  length := 1
  data := scalarInductionInitial
  ε := 1 / 10
  q := 2
  η := 1 / 323
  deficit_pos := by norm_num
  deficit_le := le_rfl
  mass_eq := by rw [scalarInductionInitial_mass]; norm_num
  even := scalarInductionInitial_even
  positiveFloor := scalarInductionInitial_floor
  gain_lower := by rw [scalarInductionInitial_gain]; norm_num
  gain_upper := scalarInductionInitial_gain.le
  inverse_norm := by convert scalarInductionInitial_inverse_norm using 1 <;> norm_num
  inverse_excess := fun i => by rw [scalarInductionInitial_inverse_excess]; norm_num
  q_lower := le_rfl
  η_nonneg := by norm_num
  centered := scalarInductionInitial_centered
  augmented := scalarInductionInitial_augmented
  budget := by norm_num [scalarPrefixBudget]

end ScalarStage
end SchauderTranslates
