import Lean_Code.SchauderTranslates.Lp.RootFairness

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

theorem StageExtension.next_cell_count_ge {S : FiniteStage p q hp2 hpfin} {j : Fin S.branches.length}
    (E : StageExtension S j) : S.cells.length + E.packet.size ≤ E.next.cells.length := by
  change _ ≤ (completeCells (S.cells ++ E.packet.cells) E.allocation.radius).length
  simp only [completeCells, List.length_append, PhysicalPacket.cells, List.length_ofFn]
  omega

theorem StageRun.cell_count_growth {S T : FiniteStage p q hp2 hpfin} (R : StageRun S T) :
    S.cells.length + R.operationCount ≤ T.cells.length := by
  induction R with
  | nil => simp [StageRun.operationCount]
  | root past _ _ _ ih => exact ih
  | layer past _ E ih =>
      have hg := E.next_cell_count_ge
      have hN := E.packet.size_pos
      change _ + (past.operationCount + 1) ≤ _
      omega

variable (p q hp2 hpfin)

theorem roundStage_cell_count_ge (n : ℕ) : 2 + n ≤ (roundStage p q hp2 hpfin n).cells.length := by
  induction n with
  | zero => norm_num [roundStage_zero, FiniteStage.initial, initialCells]
  | succ n ih =>
      have hg := (roundStep p q hp2 hpfin n).run.cell_count_growth
      have hp := (roundStep p q hp2 hpfin n).operation_pos
      change (roundStage p q hp2 hpfin n).cells.length +
        (roundStep p q hp2 hpfin n).run.operationCount ≤
        (roundStage p q hp2 hpfin (n + 1)).cells.length at hg
      omega

theorem introducedRoot_surjective : Function.Surjective (introducedRoot p q hp2 hpfin) := by
  intro ab
  apply introducedRoot_exhausts_installed p q hp2 hpfin ab ab.1
  have h := roundStage_cell_count_ge p q hp2 hpfin ab.1
  omega

/-- The actual order of introduction visits every permanent cell root
exactly once; cell and internal indices remain separate from rounds. -/
def rootAddressOrdering : ℕ ≃ ℕ × ℕ :=
  Equiv.ofBijective (introducedRoot p q hp2 hpfin)
    ⟨introducedRoot_injective p q hp2 hpfin, introducedRoot_surjective p q hp2 hpfin⟩

end SchauderTranslates.LpConstruction
