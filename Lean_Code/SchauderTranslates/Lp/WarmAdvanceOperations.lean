import Lean_Code.SchauderTranslates.Lp.WarmAdvance

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

theorem StageRun.trans_operations {S T U : FiniteStage p q hp2 hpfin}
    (R : StageRun S T) (Q : StageRun T U) :
    (R.trans Q).operations = R.operations ++ Q.operations := by
  induction Q with
  | nil => simp [StageRun.trans, StageRun.operations]
  | root past a b hfresh ih => exact ih
  | layer past j E ih =>
      change (R.trans past).operations ++ [_] = R.operations ++ (past.operations ++ [_])
      rw [ih, List.append_assoc]

theorem BranchAdvanceResult.warm_except {S : FiniteStage p q hp2 hpfin}
    {j : Fin S.branches.length} {n : ℕ} (R : BranchAdvanceResult S j n)
    (hS : S.WarmExcept j.val) : R.stage.WarmExcept j.val := by
  intro k hkj
  have hk : k.val < S.branches.length := by rw [← R.branch_count]; exact k.isLt
  rw [R.other_branch k.val hk (Ne.symm hkj)]
  exact hS ⟨k.val, hk⟩ hkj

/-- Even during an incomplete warm-up, all other roots retain their warm
bounds. This statement concerns every operation, not just the final stage. -/
theorem advanceBranchLayers_operations (S : FiniteStage p q hp2 hpfin)
    (j : Fin S.branches.length) (hS : S.WarmExcept j.val) (n : ℕ) :
    ∀ op ∈ (advanceBranchLayers S j n).run.operations,
      op.before.branches.length = S.branches.length ∧ op.before.WarmExcept j.val := by
  induction n with
  | zero => simp [advanceBranchLayers, StageRun.operations]
  | succ n ih =>
      let R := advanceBranchLayers S j n
      let jt : Fin R.stage.branches.length := ⟨j.val, by rw [R.branch_count]; exact j.isLt⟩
      let E := Classical.choice (stage_update R.stage jt)
      change ∀ op ∈ R.run.operations ++ [⟨R.stage, jt, E⟩], _
      intro op hop
      rcases List.mem_append.mp hop with hop | hop
      · exact ih op hop
      · obtain rfl := List.mem_singleton.mp hop
        exact ⟨R.branch_count, R.warm_except hS⟩

end SchauderTranslates.LpConstruction
