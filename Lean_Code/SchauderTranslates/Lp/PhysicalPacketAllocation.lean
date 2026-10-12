import Lean_Code.SchauderTranslates.Lp.PhysicalPacketCells

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R : ℝ} {v h : LebesgueLp p}
    {old : Finset ℝ} {ε : ℝ}

/-- The finite allocation produced by a packet. Its new list is the old
list followed by the private cells and the ordinary cells filling all gaps. -/
structure PhysicalPacketAllocation (P : PhysicalPacket p R v h old ε)
    (cs : List (PermanentCell p)) (t : ℕ) where
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  radius_old : R ≤ radius
  radius_time : (t : ℝ) ≤ radius
  disjoint : List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support)
    (completeCells (cs ++ P.cells) radius)
  partition : permanentSupport (completeCells (cs ++ P.cells) radius) = Set.Ico (-radius) radius
  generator_support : SupportedOn P.generator (Set.Icc (-radius) radius)
  residual_support : SupportedOn P.nextResidual (Set.Icc (-radius) radius)
  birth_support : ∀ i, SupportedOn (translate p (P.parameter i) P.generator) (Set.Icc (-radius) radius)

def PhysicalPacketAllocation.cells (P : PhysicalPacket p R v h old ε)
    (cs : List (PermanentCell p)) {t : ℕ} (A : PhysicalPacketAllocation P cs t) : List (PermanentCell p) :=
  completeCells (cs ++ P.cells) A.radius

theorem PhysicalPacketAllocation.old_cells_prefix (P : PhysicalPacket p R v h old ε)
    (cs : List (PermanentCell p)) {t : ℕ} (A : PhysicalPacketAllocation P cs t) :
    cs <+: A.cells P cs :=
  (List.prefix_append cs P.cells).trans (completeCells_prefix (cs ++ P.cells) A.radius)

/-- Choose the enlarged interval after the packet, retaining every old
cell and covering the whole generator, including its negative edit packets. -/
theorem physical_packet_allocation (P : PhysicalPacket p R v h old ε)
    (cs : List (PermanentCell p)) (t : ℕ)
    (hcs : List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support) cs)
    (hpartition : permanentSupport cs = Set.Ico (-R) R)
    (hh : SupportedOn h (Set.Icc (-R) R)) :
    Nonempty (PhysicalPacketAllocation P cs t) := by
  obtain ⟨Rg, hRg, hg⟩ := P.generator_step.bounded_support
  obtain ⟨S, hS, hmax, hbound⟩ := permanentIntervals_bounded (cs ++ P.cells)
    (max R (max (t : ℝ) Rg))
  have hRS : R ≤ S := (le_max_left _ _).trans hmax
  have htS : (t : ℝ) ≤ S := (le_max_left _ _).trans ((le_max_right _ _).trans hmax)
  have hgS : Rg ≤ S := (le_max_right _ _).trans ((le_max_right _ _).trans hmax)
  have hpart := completeCells_partition (cs ++ P.cells) hS hbound
  have hhs : SupportedOn h (Set.Icc (-S) S) :=
    hh.mono (fun _ hx => ⟨by linarith [hx.1], hx.2.trans hRS⟩)
  exact ⟨{
    radius := S
    radius_nonneg := hS
    radius_old := hRS
    radius_time := htS
    disjoint := completeCells_disjoint (cs ++ P.cells) S (P.append_cells_disjoint cs hcs hpartition)
    partition := hpart
    generator_support := hg.mono (fun _ hx => ⟨by linarith [hx.1], hx.2.trans hgS⟩)
    residual_support := P.nextResidual_supported_in_radius cs hpart hhs
    birth_support := P.birth_supported_in_radius cs hpart hhs }⟩

theorem PhysicalPacketAllocation.old_support (P : PhysicalPacket p R v h old ε)
    (cs : List (PermanentCell p)) {t : ℕ} (A : PhysicalPacketAllocation P cs t)
    {f : LebesgueLp p} (hf : SupportedOn f (Set.Icc (-R) R)) :
    SupportedOn f (Set.Icc (-A.radius) A.radius) :=
  hf.mono (fun _ hx => ⟨by linarith [hx.1, A.radius_old], hx.2.trans A.radius_old⟩)

end SchauderTranslates.LpConstruction
