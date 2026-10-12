import Lean_Code.SchauderTranslates.Lp.WarmIntroduction

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

structure BranchSweepResult (S : FiniteStage p q hp2 hpfin) (k : ℕ) where
  stage : FiniteStage p q hp2 hpfin
  branch_count : stage.branches.length = S.branches.length
  run : StageRun S stage
  operation_count : run.operationCount = k
  origins : stage.branches.map PhysicalBranch.origin = S.branches.map PhysicalBranch.origin
  depths : ∀ i : Fin S.branches.length,
    (stage.branches[i.val]'(by rw [branch_count]; exact i.isLt)).layers.length =
      (S.branches[i.val]).layers.length + if i.val < k then 1 else 0

/-- Execute one next-layer operation for each of the first k branches,
with their number fixed before starting this finite sweep. -/
def sweepFirstBranches (S : FiniteStage p q hp2 hpfin) :
    (k : ℕ) → k ≤ S.branches.length → BranchSweepResult S k
  | 0, _ => {
      stage := S
      branch_count := rfl
      run := .nil S
      operation_count := rfl
      origins := rfl
      depths := by intro i; simp }
  | k + 1, hk => by
      let R := sweepFirstBranches S k (by omega)
      have hkold : k < S.branches.length := by omega
      let jt : Fin R.stage.branches.length := ⟨k, by rw [R.branch_count]; exact hkold⟩
      let E := Classical.choice (stage_update R.stage jt)
      refine {
        stage := E.next
        branch_count := E.next_branch_count.trans R.branch_count
        run := .layer R.run jt E
        operation_count := ?_
        origins := E.next_origins.trans R.origins
        depths := ?_ }
      · change R.run.operationCount + 1 = k + 1
        rw [R.operation_count]
      · intro i
        have hiR : i.val < R.stage.branches.length := by rw [R.branch_count]; exact i.isLt
        have hiE : i.val < E.next.branches.length := by rw [E.next_branch_count]; exact hiR
        by_cases hik : i.val = k
        · have hd := E.selected_depth
          change (E.next.branches[k]'_).layers.length = (R.stage.branches[k]'_).layers.length + 1 at hd
          have hstep : (E.next.branches[i.val]'hiE).layers.length =
              (R.stage.branches[i.val]'hiR).layers.length + 1 := by simpa only [hik] using hd
          rw [hstep, R.depths i]
          have hlt : i.val < k + 1 := by omega
          have hnot : ¬i.val < k := by omega
          simp only [if_pos hlt, if_neg hnot, Nat.add_zero]
        · rw [E.other_branch hiR (Ne.symm hik), R.depths i]
          have hlt : i.val < k + 1 ↔ i.val < k := by omega
          simp only [hlt]

theorem BranchSweepResult.warm {S : FiniteStage p q hp2 hpfin} {k : ℕ}
    (R : BranchSweepResult S k) (hS : S.Warm) : R.stage.Warm := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin
  intro i
  have hi : i.val < S.branches.length := by rw [← R.branch_count]; exact i.isLt
  have hd := R.depths ⟨i.val, hi⟩
  apply forest_warm_depth_bound hpR (L := (S.branches[i.val]).layers.length)
  · simp only [Fin.val_mk] at hd
    omega
  · exact hS ⟨i.val, hi⟩

/-- Every intermediate stage of the sweep is warm, so stopping inside any
of its nonempty packets is compatible with the forest-prefix estimate. -/
theorem sweepFirstBranches_operations (S : FiniteStage p q hp2 hpfin) (hS : S.Warm)
    (k : ℕ) (hk : k ≤ S.branches.length) :
    ∀ op ∈ (sweepFirstBranches S k hk).run.operations, op.before.Warm := by
  induction k with
  | zero => simp [sweepFirstBranches, StageRun.operations]
  | succ k ih =>
      let R := sweepFirstBranches S k (by omega)
      have hkold : k < S.branches.length := by omega
      let jt : Fin R.stage.branches.length := ⟨k, by rw [R.branch_count]; exact hkold⟩
      let E := Classical.choice (stage_update R.stage jt)
      change ∀ op ∈ R.run.operations ++ [⟨R.stage, jt, E⟩], _
      intro op hop
      rcases List.mem_append.mp hop with hop | hop
      · exact ih (by omega) op hop
      · obtain rfl := List.mem_singleton.mp hop
        exact R.warm hS

def sweepAllBranches (S : FiniteStage p q hp2 hpfin) : BranchSweepResult S S.branches.length :=
  sweepFirstBranches S S.branches.length le_rfl

theorem sweepAllBranches_depth (S : FiniteStage p q hp2 hpfin) (i : Fin S.branches.length) :
    ((sweepAllBranches S).stage.branches[i.val]'(by rw [(sweepAllBranches S).branch_count]; exact i.isLt)).layers.length =
      (S.branches[i.val]).layers.length + 1 := by
  rw [(sweepAllBranches S).depths i, if_pos i.isLt]

end SchauderTranslates.LpConstruction
