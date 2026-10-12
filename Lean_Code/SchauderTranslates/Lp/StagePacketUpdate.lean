import Lean_Code.SchauderTranslates.Lp.FiniteStage

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

/-- Assemble the next physical stage from an actual packet and its checked
allocation. Only the selected branch gains a layer; old cells and births
are retained as list prefixes. -/
def FiniteStage.packetStage (S : FiniteStage p q hp2 hpfin) (j : Fin S.branches.length)
    (P : PhysicalPacket p S.radius S.generator (S.branches[j.val]).residual S.parameters S.editBudget)
    (A : PhysicalPacketAllocation P S.cells (S.time + 1)) : FiniteStage p q hp2 hpfin := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp2)
  let B := S.branches[j.val]
  have hBmem : B ∈ S.branches := List.getElem_mem j.isLt
  have hB := S.branch_support B hBmem
  let L := PhysicalBirthLayer.ofPacket P (S.time + 1) (B.residual_unit hp0 hpfin) B.residual_step
  let Bnew := B.extend P (S.time + 1) hp0 hpfin hB
  have hroots : ∀ C ∈ S.branches, ∃ hi : C.origin.1 < (A.cells P S.cells).length,
      C.root = ((((A.cells P S.cells)[C.origin.1]).roots p q hp2 hpfin).root C.origin.2).val := by
    intro C hC
    obtain ⟨hi, hroot⟩ := S.branch_root C hC
    refine ⟨hi.trans_le (A.old_cells_prefix P S.cells).length_le, ?_⟩
    rw [prefix_getElem_eq (A.old_cells_prefix P S.cells) hi]
    exact hroot
  refine {
    time := S.time + 1
    radius := A.radius
    radius_nonneg := A.radius_nonneg
    radius_time := A.radius_time
    generator := P.generator
    generator_step := P.generator_step
    generator_unit_lower := S.generator_unit_lower.trans (P.generator_norm_ge hp0 hpfin)
    generator_support := A.generator_support
    cells := A.cells P S.cells
    initial_cells_prefix := S.initial_cells_prefix.trans (A.old_cells_prefix P S.cells)
    cells_disjoint := A.disjoint
    cells_partition := A.partition
    branches := S.branches.set j.val Bnew
    branch_origins := ?_
    branch_root := ?_
    branch_support := ?_
    branch_cells := ?_
    births := S.births ++ L.births
    birth_initial := ?_
    birth_parameters := packet_births_parameters P (S.time + 1) _ _ S.births S.birth_parameters rfl
    birth_time := ?_
    birth_support := ?_
    birth_step := ?_
    birth_unit_lower := ?_ }
  · have heq : (S.branches.set j.val Bnew).map PhysicalBranch.origin =
        S.branches.map PhysicalBranch.origin := by
      rw [List.map_set]
      have hj : j.val < (S.branches.map PhysicalBranch.origin).length := by simpa using j.isLt
      have hval : Bnew.origin = (S.branches.map PhysicalBranch.origin)[j.val] := by
        rw [List.getElem_map]
        rfl
      rw [hval, List.set_getElem_self hj]
    rw [heq]
    exact S.branch_origins
  · intro C hC
    rcases List.mem_or_eq_of_mem_set hC with hC | rfl
    · exact hroots C hC
    · exact hroots B hBmem
  · intro C hC
    rcases List.mem_or_eq_of_mem_set hC with hC | rfl
    · exact C.supported_mono (S.branch_support C hC) A.radius_old
    · exact B.extend_supported P (S.time + 1) hp0 hpfin hB S.cells A
  · intro C hC K hK i
    rcases List.mem_or_eq_of_mem_set hC with hC | rfl
    · exact (A.old_cells_prefix P S.cells).subset (S.branch_cells C hC K hK i)
    · exact B.extend_cells P (S.time + 1) hp0 hpfin hB S.cells A (S.branch_cells B hBmem) K hK i
  · rw [List.head?_append, S.birth_initial]
    rfl
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact (S.birth_time b hb).trans (Nat.le_succ S.time)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
      exact le_rfl
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact A.old_support P S.cells (S.birth_support b hb)
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
      exact A.birth_support i
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact S.birth_step b hb
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
      exact P.generator_step.translate (P.parameter i)
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact S.birth_unit_lower b hb
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
      change 1 ≤ ‖translate p (P.parameter i) P.generator‖
      rw [norm_translate]
      exact S.generator_unit_lower.trans (P.generator_norm_ge hp0 hpfin)

theorem FiniteStage.packetStage_time (S : FiniteStage p q hp2 hpfin) (j : Fin S.branches.length)
    (P : PhysicalPacket p S.radius S.generator (S.branches[j.val]).residual S.parameters S.editBudget)
    (A : PhysicalPacketAllocation P S.cells (S.time + 1)) :
    (S.packetStage j P A).time = S.time + 1 := rfl

theorem FiniteStage.packetStage_birth_count (S : FiniteStage p q hp2 hpfin) (j : Fin S.branches.length)
    (P : PhysicalPacket p S.radius S.generator (S.branches[j.val]).residual S.parameters S.editBudget)
    (A : PhysicalPacketAllocation P S.cells (S.time + 1)) :
    (S.packetStage j P A).births.length = S.births.length + P.size := by
  change (S.births ++ _).length = _
  rw [List.length_append, PhysicalBirthLayer.births_length]
  rfl

theorem FiniteStage.packetStage_cells_prefix (S : FiniteStage p q hp2 hpfin) (j : Fin S.branches.length)
    (P : PhysicalPacket p S.radius S.generator (S.branches[j.val]).residual S.parameters S.editBudget)
    (A : PhysicalPacketAllocation P S.cells (S.time + 1)) :
    S.cells <+: (S.packetStage j P A).cells := A.old_cells_prefix P S.cells

theorem FiniteStage.packetStage_births_prefix (S : FiniteStage p q hp2 hpfin) (j : Fin S.branches.length)
    (P : PhysicalPacket p S.radius S.generator (S.branches[j.val]).residual S.parameters S.editBudget)
    (A : PhysicalPacketAllocation P S.cells (S.time + 1)) :
    S.births <+: (S.packetStage j P A).births := List.prefix_append _ _

end SchauderTranslates.LpConstruction
