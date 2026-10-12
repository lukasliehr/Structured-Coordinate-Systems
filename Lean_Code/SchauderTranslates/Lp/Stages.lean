import Lean_Code.SchauderTranslates.Lp.StagePacketUpdate
import Lean_Code.SchauderTranslates.Lp.RootIntroduction

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

structure StageExtension (S : FiniteStage p q hp2 hpfin) (j : Fin S.branches.length) where
  packet : PhysicalPacket p S.radius S.generator (S.branches[j.val]).residual S.parameters S.editBudget
  allocation : PhysicalPacketAllocation packet S.cells (S.time + 1)

def StageExtension.next {S : FiniteStage p q hp2 hpfin} {j : Fin S.branches.length}
    (E : StageExtension S j) : FiniteStage p q hp2 hpfin :=
  S.packetStage j E.packet E.allocation

/-- Blueprint `lp:stages`: every introduced branch of a finite physical
stage admits its next layer, with the old-count budget fixed in advance.
The returned data produce an actual next `FiniteStage`, preserving all
cell, root, residual, parameter and immutable birth invariants. -/
theorem stage_update (S : FiniteStage p q hp2 hpfin) (j : Fin S.branches.length) :
    Nonempty (StageExtension S j) := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp2)
  let B := S.branches[j.val]
  have hB := S.branch_support B (List.getElem_mem j.isLt)
  obtain ⟨P⟩ := physical_packet_exists hp2 hpfin S.radius_nonneg S.generator B.residual
    S.generator_step B.residual_step S.generator_ne_zero (B.residual_unit hp0 hpfin)
    S.generator_support (B.residual_supported hB) S.parameters S.editBudget_pos
  obtain ⟨A⟩ := physical_packet_allocation P S.cells (S.time + 1)
    S.cells_disjoint S.cells_partition (B.residual_supported hB)
  exact ⟨⟨P, A⟩⟩

variable {S : FiniteStage p q hp2 hpfin} {j : Fin S.branches.length} (E : StageExtension S j)

theorem StageExtension.next_time : E.next.time = S.time + 1 := rfl

theorem StageExtension.next_branch_count : E.next.branches.length = S.branches.length := by
  change (S.branches.set j.val _).length = _
  exact List.length_set

theorem StageExtension.next_birth_count :
    E.next.births.length = S.births.length + E.packet.size :=
  S.packetStage_birth_count j E.packet E.allocation

theorem StageExtension.next_birth_count_strict : S.births.length < E.next.births.length := by
  rw [E.next_birth_count]
  have h := E.packet.size_pos
  omega

theorem StageExtension.next_cells_prefix : S.cells <+: E.next.cells :=
  S.packetStage_cells_prefix j E.packet E.allocation

theorem StageExtension.next_births_prefix : S.births <+: E.next.births :=
  S.packetStage_births_prefix j E.packet E.allocation

theorem StageExtension.generator_edit : ‖E.next.generator - S.generator‖ ≤ S.editBudget :=
  E.packet.editBound

theorem StageExtension.selected_depth :
    (E.next.branches[j.val]'(by rw [E.next_branch_count]; exact j.isLt)).layers.length =
      (S.branches[j.val]).layers.length + 1 := by
  change ((S.branches.set j.val _)[j.val]).layers.length = _
  rw [List.getElem_set_self (by simpa only [List.length_set] using j.isLt)]
  change ((S.branches[j.val]).layers ++ [_]).length = _
  simp only [List.length_append, List.length_singleton]

theorem StageExtension.other_branch {k : ℕ} (hk : k < S.branches.length) (hjk : j.val ≠ k) :
    E.next.branches[k]'(by rw [E.next_branch_count]; exact hk) = S.branches[k] := by
  change (S.branches.set j.val _)[k]'(by simpa only [List.length_set] using hk) = _
  exact List.getElem_set_ne hjk _

end SchauderTranslates.LpConstruction
