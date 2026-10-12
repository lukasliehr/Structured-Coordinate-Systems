import Lean_Code.SchauderTranslates.Lp.PhysicalPacket
import Lean_Code.SchauderTranslates.Lp.PermanentAllocation

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ} {v h : LebesgueLp p}
    {old : Finset ℝ} {ε : ℝ} (P : PhysicalPacket p R v h old ε)

def PhysicalPacket.cell (i : Fin P.size) : PermanentCell p :=
  .privateCell (P.privateVector i) (P.privateData i) (P.privateUnit i)

def PhysicalPacket.cells : List (PermanentCell p) := List.ofFn P.cell

theorem PhysicalPacket.cell_support (i : Fin P.size) :
    (P.cell i).support = (P.privateData i).supportSet := rfl

theorem PhysicalPacket.cells_mem (c : PermanentCell p) :
    c ∈ P.cells ↔ ∃ i, P.cell i = c := List.mem_ofFn

theorem PhysicalPacket.cells_disjoint :
    List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support) P.cells := by
  rw [PhysicalPacket.cells, List.pairwise_ofFn]
  intro i j hij
  exact P.privateCellDisjoint i j (ne_of_lt hij)

theorem PhysicalPacket.append_cells_disjoint (cs : List (PermanentCell p))
    (hcs : List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support) cs)
    (hpartition : permanentSupport cs = Set.Ico (-R) R) :
    List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support) (cs ++ P.cells) := by
  rw [List.pairwise_append]
  refine ⟨hcs, P.cells_disjoint, ?_⟩
  intro c hc d hd
  obtain ⟨i, rfl⟩ := (P.cells_mem d).mp hd
  apply (P.privateCellFresh i).symm.mono_left
  intro x hx
  rw [← hpartition]
  exact Set.mem_iUnion₂.mpr ⟨c, hc, hx⟩

theorem DisjointStepData.supported {p : ℝ≥0∞} {e : LebesgueLp p}
    (D : DisjointStepData p e) : SupportedOn e D.supportSet := by
  filter_upwards [D.nonzero_iff_support_ae] with x hx
  intro hout
  by_contra hne
  exact hout (hx.mp hne)

theorem permanentCell_supported_in_radius (cs : List (PermanentCell p)) {S : ℝ}
    (hpartition : permanentSupport cs = Set.Ico (-S) S) {c : PermanentCell p} (hc : c ∈ cs) :
    c.support ⊆ Set.Icc (-S) S := by
  intro x hx
  have hx : x ∈ permanentSupport cs := Set.mem_iUnion₂.mpr ⟨c, hc, hx⟩
  rw [hpartition] at hx
  exact ⟨hx.1, hx.2.le⟩

theorem PhysicalPacket.private_supported_in_radius (cs : List (PermanentCell p)) {S : ℝ}
    (hpartition : permanentSupport (completeCells (cs ++ P.cells) S) = Set.Ico (-S) S)
    (i : Fin P.size) : SupportedOn (P.privateVector i) (Set.Icc (-S) S) := by
  apply (P.privateData i).supported.mono
  apply permanentCell_supported_in_radius _ hpartition (c := P.cell i)
  apply (completeCells_prefix (cs ++ P.cells) S).subset
  exact List.mem_append_right cs ((P.cells_mem (P.cell i)).mpr ⟨i, rfl⟩)

theorem PhysicalPacket.mean_supported_in_radius (cs : List (PermanentCell p)) {S : ℝ}
    (hpartition : permanentSupport (completeCells (cs ++ P.cells) S) = Set.Ico (-S) S) :
    SupportedOn P.mean (Set.Icc (-S) S) :=
  (SupportedOn.finset_sum Finset.univ P.privateVector
    (fun i _ => P.private_supported_in_radius cs hpartition i)).real_smul _

theorem PhysicalPacket.nextResidual_supported_in_radius (cs : List (PermanentCell p)) {S : ℝ}
    (hpartition : permanentSupport (completeCells (cs ++ P.cells) S) = Set.Ico (-S) S)
    (hh : SupportedOn h (Set.Icc (-S) S)) :
    SupportedOn P.nextResidual (Set.Icc (-S) S) := by
  have hs := hh.add ((P.mean_supported_in_radius cs hpartition).real_smul (-1))
  have hs : SupportedOn (h - P.mean) (Set.Icc (-S) S) := by simpa [sub_eq_add_neg] using hs
  exact hs.real_smul _

theorem PhysicalPacket.birth_supported_in_radius (cs : List (PermanentCell p)) {S : ℝ}
    (hpartition : permanentSupport (completeCells (cs ++ P.cells) S) = Set.Ico (-S) S)
    (hh : SupportedOn h (Set.Icc (-S) S)) (i : Fin P.size) :
    SupportedOn (translate p (P.parameter i) P.generator) (Set.Icc (-S) S) := by
  rw [P.birthIdentity]
  exact ((P.private_supported_in_radius cs hpartition i).add (hh.real_smul _)).real_smul _

end SchauderTranslates.LpConstruction
