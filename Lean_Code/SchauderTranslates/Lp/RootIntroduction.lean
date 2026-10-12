import Lean_Code.SchauderTranslates.Lp.FiniteStage

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

def FiniteStage.newBranch (S : FiniteStage p q hp2 hpfin) (a : Fin S.cells.length) (b : ℕ) :
    PhysicalBranch p :=
  PhysicalBranch.start (a.val, b) (((S.cells[a.val]).roots p q hp2 hpfin).root b).val
    ((S.cells[a.val]).roots_normalized p q hp2 hpfin b)
    ((S.cells[a.val]).roots_isCompactStep p q hp2 hpfin b)

theorem FiniteStage.newBranch_supported (S : FiniteStage p q hp2 hpfin)
    (a : Fin S.cells.length) (b : ℕ) : (S.newBranch a b).Supported S.radius := by
  refine ⟨?_, by simp [FiniteStage.newBranch, PhysicalBranch.start]⟩
  apply ((S.cells[a.val]).roots_supported p q hp2 hpfin b).mono
  exact permanentCell_supported_in_radius S.cells S.cells_partition (List.getElem_mem a.isLt)

/-- Introduce an available, unused Haar root without a layer operation.
Every cell and every birth snapshot remains permanent. -/
def FiniteStage.introduceRoot (S : FiniteStage p q hp2 hpfin)
    (a : Fin S.cells.length) (b : ℕ)
    (hfresh : (a.val, b) ∉ S.branches.map PhysicalBranch.origin) : FiniteStage p q hp2 hpfin := by
  refine { S with
    branches := S.branches ++ [S.newBranch a b]
    branch_origins := ?_
    branch_root := ?_
    branch_support := ?_
    branch_cells := ?_ }
  · rw [List.map_append, List.map_singleton, List.nodup_append]
    refine ⟨S.branch_origins, by simp, ?_⟩
    intro u hu w hw huw
    have hw : w = (a.val, b) := List.mem_singleton.mp hw
    exact hfresh (hw ▸ huw ▸ hu)
  · intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact S.branch_root B hB
    · obtain rfl := List.mem_singleton.mp hB
      exact ⟨a.isLt, rfl⟩
  · intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact S.branch_support B hB
    · obtain rfl := List.mem_singleton.mp hB
      exact S.newBranch_supported a b
  · intro B hB L hL i
    rcases List.mem_append.mp hB with hB | hB
    · exact S.branch_cells B hB L hL i
    · obtain rfl := List.mem_singleton.mp hB
      simp [FiniteStage.newBranch, PhysicalBranch.start] at hL

theorem FiniteStage.introduceRoot_branch_count (S : FiniteStage p q hp2 hpfin)
    (a : Fin S.cells.length) (b : ℕ)
    (hfresh : (a.val, b) ∉ S.branches.map PhysicalBranch.origin) :
    (S.introduceRoot a b hfresh).branches.length = S.branches.length + 1 := by
  simp [FiniteStage.introduceRoot]

end SchauderTranslates.LpConstruction
