import Lean_Code.SchauderTranslates.Lp.PhysicalHistory
import Lean_Code.SchauderTranslates.Lp.StageBudget

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem prefix_getElem_eq {α : Type*} {xs ys : List α} (h : xs <+: ys)
    {i : ℕ} (hi : i < xs.length) : ys[i]'(hi.trans_le h.length_le) = xs[i] := by
  obtain ⟨zs, rfl⟩ := h
  exact List.getElem_append_left hi

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem PhysicalBranch.supported_mono (B : PhysicalBranch p) {R S : ℝ}
    (hB : B.Supported R) (hRS : R ≤ S) : B.Supported S := by
  have hI : Set.Icc (-R) R ⊆ Set.Icc (-S) S :=
    fun _ hx => ⟨by linarith [hx.1], hx.2.trans hRS⟩
  exact ⟨hB.1.mono hI, fun L hL i => (hB.2 L hL i).mono hI⟩

theorem PhysicalBranch.extend_supported (B : PhysicalBranch p) {R : ℝ} {v : LebesgueLp p}
    {old : Finset ℝ} {ε : ℝ} (P : PhysicalPacket p R v B.residual old ε)
    (t : ℕ) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (hB : B.Supported R)
    (cs : List (PermanentCell p)) (A : PhysicalPacketAllocation P cs t) :
    (B.extend P t hp0 hpfin hB).Supported A.radius := by
  refine ⟨A.old_support P cs hB.1, ?_⟩
  intro L hL i
  rcases List.mem_append.mp hL with hL | hL
  · exact A.old_support P cs (hB.2 L hL i)
  · have he := List.mem_singleton.mp hL
    subst L
    exact P.private_supported_in_radius cs A.partition i

theorem PhysicalBranch.extend_cells (B : PhysicalBranch p) {R : ℝ} {v : LebesgueLp p}
    {old : Finset ℝ} {ε : ℝ} (P : PhysicalPacket p R v B.residual old ε)
    (t : ℕ) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (hB : B.Supported R)
    (cs : List (PermanentCell p)) (A : PhysicalPacketAllocation P cs t)
    (hcs : ∀ L ∈ B.layers, ∀ i, L.cell i ∈ cs) :
    ∀ L ∈ (B.extend P t hp0 hpfin hB).layers, ∀ i, L.cell i ∈ A.cells P cs := by
  intro L hL i
  rcases List.mem_append.mp hL with hL | hL
  · exact (A.old_cells_prefix P cs).subset (hcs L hL i)
  · have he := List.mem_singleton.mp hL
    subst L
    apply (completeCells_prefix (cs ++ P.cells) A.radius).subset
    apply List.mem_append_right
    exact (P.cells_mem (P.cell i)).mpr ⟨i, rfl⟩

theorem PhysicalBirthLayer.births_parameters (L : PhysicalBirthLayer p) :
    (L.births.map BirthAtom.parameter).Nodup := by
  rw [PhysicalBirthLayer.births, List.map_ofFn, List.nodup_ofFn]
  exact L.parameter_injective

theorem packet_births_parameters {R : ℝ} {v h : LebesgueLp p} {old : Finset ℝ} {ε : ℝ}
    (P : PhysicalPacket p R v h old ε) (t : ℕ) (hh : ‖h‖ = 1) (hstep : IsCompactStep p h)
    (bs : List (BirthAtom p)) (hbs : (bs.map BirthAtom.parameter).Nodup)
    (hold : (bs.map BirthAtom.parameter).toFinset = old) :
    ((bs ++ (PhysicalBirthLayer.ofPacket P t hh hstep).births).map BirthAtom.parameter).Nodup := by
  classical
  rw [List.map_append, List.nodup_append]
  refine ⟨hbs, PhysicalBirthLayer.births_parameters _, ?_⟩
  intro a ha b hb hab
  obtain ⟨atom, hatom, rfl⟩ := List.mem_map.mp hb
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hatom
  have ha : a ∈ old := by rw [← hold]; exact List.mem_toFinset.mpr ha
  change a = P.parameter i at hab
  exact P.parameter_fresh i (hab ▸ ha)

end SchauderTranslates.LpConstruction
