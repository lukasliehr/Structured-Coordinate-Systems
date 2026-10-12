import Lean_Code.SchauderTranslates.Lp.StageRuns

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

def StageExtension.layerRecord {S : FiniteStage p q hp2 hpfin} {j : Fin S.branches.length}
    (E : StageExtension S j) : PhysicalBirthLayer p :=
  PhysicalBirthLayer.ofPacket E.packet (S.time + 1)
    ((S.branches[j.val]).residual_unit (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin)
    (S.branches[j.val]).residual_step

theorem StageExtension.selected_layers {S : FiniteStage p q hp2 hpfin} {j : Fin S.branches.length}
    (E : StageExtension S j) :
    (E.next.branches[j.val]'(by rw [E.next_branch_count]; exact j.isLt)).layers =
      (S.branches[j.val]).layers ++ [E.layerRecord] := by
  change ((S.branches.set j.val _)[j.val]).layers = _
  rw [List.getElem_set_self (by simpa only [List.length_set] using j.isLt)]
  rfl

theorem StageExtension.births_eq {S : FiniteStage p q hp2 hpfin} {j : Fin S.branches.length}
    (E : StageExtension S j) : E.next.births = S.births ++ E.layerRecord.births := rfl

/-- Advancing one branch finitely many times produces a genuine finite
execution, preserving all other branch records and every root address. -/
structure BranchAdvanceResult (S : FiniteStage p q hp2 hpfin) (j : Fin S.branches.length) (n : ℕ) where
  stage : FiniteStage p q hp2 hpfin
  branch_count : stage.branches.length = S.branches.length
  run : StageRun S stage
  operation_count : run.operationCount = n
  origins : stage.branches.map PhysicalBranch.origin = S.branches.map PhysicalBranch.origin
  selected_depth : (stage.branches[j.val]'(by rw [branch_count]; exact j.isLt)).layers.length =
    (S.branches[j.val]).layers.length + n
  other_branch : ∀ k (hk : k < S.branches.length), j.val ≠ k →
    stage.branches[k]'(by rw [branch_count]; exact hk) = S.branches[k]

def advanceBranchLayers (S : FiniteStage p q hp2 hpfin) (j : Fin S.branches.length) :
    (n : ℕ) → BranchAdvanceResult S j n
  | 0 => {
      stage := S
      branch_count := rfl
      run := .nil S
      operation_count := rfl
      origins := rfl
      selected_depth := by simp
      other_branch := fun _ _ _ => rfl }
  | n + 1 => by
      let R := advanceBranchLayers S j n
      let jt : Fin R.stage.branches.length := ⟨j.val, by rw [R.branch_count]; exact j.isLt⟩
      let E := Classical.choice (stage_update R.stage jt)
      refine {
        stage := E.next
        branch_count := E.next_branch_count.trans R.branch_count
        run := .layer R.run jt E
        operation_count := ?_
        origins := E.next_origins.trans R.origins
        selected_depth := ?_
        other_branch := ?_ }
      · change R.run.operationCount + 1 = n + 1
        rw [R.operation_count]
      · have hd := E.selected_depth
        change (E.next.branches[j.val]'_).layers.length =
          (R.stage.branches[j.val]'_).layers.length + 1 at hd
        rw [hd, R.selected_depth]
        omega
      · intro k hk hjk
        have hkR : k < R.stage.branches.length := by rw [R.branch_count]; exact hk
        exact (E.other_branch hkR hjk).trans (R.other_branch k hk hjk)

theorem BranchAdvanceResult.time_eq {S : FiniteStage p q hp2 hpfin} {j : Fin S.branches.length} {n : ℕ}
    (R : BranchAdvanceResult S j n) : R.stage.time = S.time + n := by
  rw [R.run.time_eq, R.operation_count]

theorem BranchAdvanceResult.birth_count_growth {S : FiniteStage p q hp2 hpfin}
    {j : Fin S.branches.length} {n : ℕ} (R : BranchAdvanceResult S j n) :
    S.births.length + n ≤ R.stage.births.length := by
  simpa only [R.operation_count] using R.run.birth_count_growth

theorem BranchAdvanceResult.available_root {S : FiniteStage p q hp2 hpfin}
    {j : Fin S.branches.length} {n : ℕ} (R : BranchAdvanceResult S j n) (ab : ℕ × ℕ)
    (hab : S.AvailableRoot ab) : R.stage.AvailableRoot ab := by
  refine ⟨hab.1.trans_le R.run.cells_prefix.length_le, ?_⟩
  rw [R.origins]
  exact hab.2

end SchauderTranslates.LpConstruction
