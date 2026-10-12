import Lean_Code.SchauderTranslates.Lp.BranchSweep

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

structure FiniteRoundResult (S : FiniteStage p q hp2 hpfin) where
  stage : FiniteStage p q hp2 hpfin
  run : StageRun S stage
  branch_count : stage.branches.length = S.branches.length + 1
  origins : stage.branches.map PhysicalBranch.origin = S.branches.map PhysicalBranch.origin ++ [S.leastAvailable]
  warm : stage.Warm
  operation_pos : 1 ≤ run.operationCount
  old_depth : ∀ k (hk : k < S.branches.length),
    (stage.branches[k]'(by rw [branch_count]; omega)).layers.length = (S.branches[k]).layers.length + 1
  operations_warm : ∀ op ∈ run.operations,
    op.before.WarmExcept (op.before.branches.length - 1)

/-- One round consists only of finitely many actual operations: introduce
the least-priority unused root, warm it, then advance every branch once. -/
theorem finite_round (S : FiniteStage p q hp2 hpfin) (hS : S.Warm) : Nonempty (FiniteRoundResult S) := by
  let W := Classical.choice (warm_introduction S hS)
  let R := sweepAllBranches W.stage
  refine ⟨{
    stage := R.stage
    run := W.run.trans R.run
    branch_count := R.branch_count.trans W.branch_count
    origins := R.origins.trans W.origins
    warm := R.warm W.warm
    operation_pos := ?_
    old_depth := ?_
    operations_warm := ?_ }⟩
  · rw [StageRun.trans_operationCount]
    exact W.operation_pos.trans (Nat.le_add_right _ _)
  · intro k hk
    have hkW : k < W.stage.branches.length := by rw [W.branch_count]; omega
    have hd := sweepAllBranches_depth W.stage ⟨k, hkW⟩
    simp only [Fin.val_mk] at hd
    rw [hd, W.old_branch k hk]
  · intro op hop
    rw [StageRun.trans_operations] at hop
    rcases List.mem_append.mp hop with hop | hop
    · exact W.operations_warm op hop
    · have hw : op.before.Warm :=
        sweepFirstBranches_operations W.stage W.warm W.stage.branches.length le_rfl op hop
      exact fun k _ => hw k

theorem FiniteRoundResult.time_strict {S : FiniteStage p q hp2 hpfin} (R : FiniteRoundResult S) :
    S.time < R.stage.time := by
  rw [R.run.time_eq]
  have h := R.operation_pos
  omega

theorem FiniteRoundResult.birth_count_strict {S : FiniteStage p q hp2 hpfin} (R : FiniteRoundResult S) :
    S.births.length < R.stage.births.length := by
  have hg := R.run.birth_count_growth
  have hp := R.operation_pos
  omega

end SchauderTranslates.LpConstruction
