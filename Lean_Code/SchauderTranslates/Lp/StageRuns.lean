import Lean_Code.SchauderTranslates.Lp.AvailableRoots

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

theorem StageExtension.next_origins {S : FiniteStage p q hp2 hpfin} {j : Fin S.branches.length}
    (E : StageExtension S j) : E.next.branches.map PhysicalBranch.origin = S.branches.map PhysicalBranch.origin := by
  change (S.branches.set j.val _).map PhysicalBranch.origin = _
  rw [List.map_set]
  have hj : j.val < (S.branches.map PhysicalBranch.origin).length := by simpa using j.isLt
  have hval : (S.branches[j.val].extend E.packet (S.time + 1)
      (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin (S.branch_support _ (List.getElem_mem j.isLt))).origin =
      (S.branches.map PhysicalBranch.origin)[j.val] := by
    rw [List.getElem_map]
    rfl
  rw [hval, List.set_getElem_self hj]

theorem FiniteStage.introduceRoot_origins (S : FiniteStage p q hp2 hpfin) (a : Fin S.cells.length) (b : ℕ)
    (hfresh : (a.val, b) ∉ S.branches.map PhysicalBranch.origin) :
    (S.introduceRoot a b hfresh).branches.map PhysicalBranch.origin =
      S.branches.map PhysicalBranch.origin ++ [(a.val, b)] := by
  change (S.branches ++ [S.newBranch a b]).map PhysicalBranch.origin = _
  rw [List.map_append, List.map_singleton]
  rfl

/-- A finite execution records root introductions and genuine packet
extensions separately; only packet extensions count as operations. -/
inductive StageRun : FiniteStage p q hp2 hpfin → FiniteStage p q hp2 hpfin → Type where
  | nil (S) : StageRun S S
  | root {S T} (past : StageRun S T) (a : Fin T.cells.length) (b : ℕ)
      (hfresh : (a.val, b) ∉ T.branches.map PhysicalBranch.origin) :
      StageRun S (T.introduceRoot a b hfresh)
  | layer {S T} (past : StageRun S T) (j : Fin T.branches.length) (E : StageExtension T j) :
      StageRun S E.next

def StageRun.operationCount {S T : FiniteStage p q hp2 hpfin} : StageRun S T → ℕ
  | .nil _ => 0
  | .root past _ _ _ => past.operationCount
  | .layer past _ _ => past.operationCount + 1

def StageRun.totalBirths {S T : FiniteStage p q hp2 hpfin} : StageRun S T → ℕ
  | .nil _ => 0
  | .root past _ _ _ => past.totalBirths
  | .layer past _ E => past.totalBirths + E.packet.size

def StageRun.trans {S T U : FiniteStage p q hp2 hpfin} (R : StageRun S T) :
    StageRun T U → StageRun S U
  | .nil _ => R
  | .root past a b h => .root (R.trans past) a b h
  | .layer past j E => .layer (R.trans past) j E

theorem StageRun.trans_operationCount {S T U : FiniteStage p q hp2 hpfin}
    (R : StageRun S T) (Q : StageRun T U) :
    (R.trans Q).operationCount = R.operationCount + Q.operationCount := by
  induction Q with
  | nil => simp [StageRun.trans, StageRun.operationCount]
  | root past _ _ _ ih => exact ih
  | layer past _ _ ih =>
      change (R.trans past).operationCount + 1 = R.operationCount + (past.operationCount + 1)
      rw [ih, Nat.add_assoc]

theorem StageRun.birth_count_eq {S T : FiniteStage p q hp2 hpfin} (R : StageRun S T) :
    T.births.length = S.births.length + R.totalBirths := by
  induction R with
  | nil => simp [StageRun.totalBirths]
  | root past _ _ _ ih => exact ih
  | layer past _ E ih =>
      rw [E.next_birth_count]
      change _ + E.packet.size = _ + (past.totalBirths + E.packet.size)
      rw [ih, Nat.add_assoc]

theorem StageRun.cells_prefix {S T : FiniteStage p q hp2 hpfin} (R : StageRun S T) : S.cells <+: T.cells := by
  induction R with
  | nil => exact ⟨[], by simp⟩
  | root past _ _ _ ih => exact ih
  | layer past _ E ih => exact ih.trans E.next_cells_prefix

theorem StageRun.births_prefix {S T : FiniteStage p q hp2 hpfin} (R : StageRun S T) : S.births <+: T.births := by
  induction R with
  | nil => exact ⟨[], by simp⟩
  | root past _ _ _ ih => exact ih
  | layer past _ E ih => exact ih.trans E.next_births_prefix

theorem StageRun.origins_prefix {S T : FiniteStage p q hp2 hpfin} (R : StageRun S T) :
    S.branches.map PhysicalBranch.origin <+: T.branches.map PhysicalBranch.origin := by
  induction R with
  | nil => exact ⟨[], by simp⟩
  | root past a b hfresh ih =>
      rw [FiniteStage.introduceRoot_origins]
      exact ih.trans (List.prefix_append _ _)
  | layer past _ E ih => rw [E.next_origins]; exact ih

theorem StageRun.branch_count_le {S T : FiniteStage p q hp2 hpfin} (R : StageRun S T) :
    S.branches.length ≤ T.branches.length := by
  simpa only [List.length_map] using R.origins_prefix.length_le

theorem StageRun.time_eq {S T : FiniteStage p q hp2 hpfin} (R : StageRun S T) :
    T.time = S.time + R.operationCount := by
  induction R with
  | nil => simp [StageRun.operationCount]
  | root past _ _ _ ih => exact ih
  | layer past _ E ih =>
      rw [E.next_time]
      change _ = _ + (past.operationCount + 1)
      rw [ih]
      omega

theorem StageRun.birth_count_growth {S T : FiniteStage p q hp2 hpfin} (R : StageRun S T) :
    S.births.length + R.operationCount ≤ T.births.length := by
  induction R with
  | nil => simp [StageRun.operationCount]
  | root past _ _ _ ih => exact ih
  | layer past _ E ih =>
      rw [E.next_birth_count]
      change _ + (past.operationCount + 1) ≤ _
      have hN := E.packet.size_pos
      omega

structure LayerOperation (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp2 : 2 < p) (hpfin : p ≠ ∞) where
  before : FiniteStage p q hp2 hpfin
  branch : Fin before.branches.length
  extension : StageExtension before branch

def StageRun.operations {S T : FiniteStage p q hp2 hpfin} :
    StageRun S T → List (LayerOperation p q hp2 hpfin)
  | .nil _ => []
  | .root past _ _ _ => past.operations
  | @StageRun.layer _ _ _ _ _ _ _ _ U past j E => past.operations ++ [⟨U, j, E⟩]

theorem StageRun.operations_length {S T : FiniteStage p q hp2 hpfin} (R : StageRun S T) :
    R.operations.length = R.operationCount := by
  induction R with
  | nil => rfl
  | root past _ _ _ ih => exact ih
  | layer past _ E ih =>
      change (past.operations ++ [_]).length = past.operationCount + 1
      simp only [List.length_append, List.length_singleton, ih]

end SchauderTranslates.LpConstruction
