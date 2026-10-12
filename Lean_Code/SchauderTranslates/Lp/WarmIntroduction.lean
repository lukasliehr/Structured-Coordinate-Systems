import Lean_Code.SchauderTranslates.Lp.WarmAdvanceOperations

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

structure WarmIntroductionResult (S : FiniteStage p q hp2 hpfin) where
  stage : FiniteStage p q hp2 hpfin
  run : StageRun S stage
  branch_count : stage.branches.length = S.branches.length + 1
  origins : stage.branches.map PhysicalBranch.origin = S.branches.map PhysicalBranch.origin ++ [S.leastAvailable]
  warm : stage.Warm
  old_branch : ∀ k (hk : k < S.branches.length),
    stage.branches[k]'(by rw [branch_count]; omega) = S.branches[k]
  operation_pos : 1 ≤ run.operationCount
  operations_warm : ∀ op ∈ run.operations,
    op.before.WarmExcept (op.before.branches.length - 1)

/-- Introduce the least-priority available root and complete a finite
warm-up before the next root introduction. All older branches are kept. -/
theorem warm_introduction (S : FiniteStage p q hp2 hpfin) (hS : S.Warm) :
    Nonempty (WarmIntroductionResult S) := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin
  obtain ⟨n, hn, hwarm⟩ := exists_forest_warm_depth hpR S.branches.length
  let U := S.introduceLeast
  let j : Fin U.branches.length := ⟨S.branches.length, by
    change S.branches.length < S.introduceLeast.branches.length
    rw [S.introduceLeast_branch_count]
    omega⟩
  let R := advanceBranchLayers U j n
  let introRun : StageRun S U := .root (.nil S)
    ⟨S.leastAvailable.1, S.leastAvailable_available.1⟩ S.leastAvailable.2 S.leastAvailable_available.2
  refine ⟨{
    stage := R.stage
    run := introRun.trans R.run
    branch_count := R.branch_count.trans S.introduceLeast_branch_count
    origins := ?_
    warm := R.warm (S.introduceLeast_warm_except hS) hwarm
    old_branch := ?_
    operation_pos := ?_
    operations_warm := ?_ }⟩
  · rw [R.origins]
    exact S.introduceRoot_origins _ _ _
  · intro k hk
    have hkU : k < U.branches.length := by
      change k < S.introduceLeast.branches.length
      rw [S.introduceLeast_branch_count]
      omega
    have hjk : j.val ≠ k := by change S.branches.length ≠ k; omega
    rw [R.other_branch k hkU hjk]
    exact List.getElem_append_left hk
  · rw [StageRun.trans_operationCount, R.operation_count]
    change 1 ≤ 0 + n
    simpa only [Nat.zero_add] using hn
  · intro op hop
    rw [StageRun.trans_operations] at hop
    have hopR : op ∈ R.run.operations := by
      simpa only [introRun, StageRun.operations, List.nil_append] using hop
    obtain ⟨hcount, hw⟩ := advanceBranchLayers_operations U j
      (S.introduceLeast_warm_except hS) n op hopR
    have he : op.before.branches.length - 1 = j.val := by
      rw [hcount]
      change S.introduceLeast.branches.length - 1 = S.branches.length
      rw [S.introduceLeast_branch_count]
      omega
    rw [he]
    exact hw

end SchauderTranslates.LpConstruction
