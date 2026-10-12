import Lean_Code.SchauderTranslates.Lp.PermanentCell

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def permanentSupport {p : ℝ≥0∞} (cs : List (PermanentCell p)) : Set ℝ :=
  ⋃ c ∈ cs, c.support

theorem permanentSupport_append {p : ℝ≥0∞} (cs ds : List (PermanentCell p)) :
    permanentSupport (cs ++ ds) = permanentSupport cs ∪ permanentSupport ds := by
  ext x
  simp only [permanentSupport, Set.mem_iUnion, List.mem_append, Set.mem_union]
  constructor
  · rintro ⟨c, hc, hx⟩
    rcases hc with hc | hd
    · exact Or.inl ⟨c, hc, hx⟩
    · exact Or.inr ⟨c, hd, hx⟩
  · rintro (⟨c, hc, hx⟩ | ⟨c, hd, hx⟩)
    · exact ⟨c, Or.inl hc, hx⟩
    · exact ⟨c, Or.inr hd, hx⟩

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hpfin : p ≠ ∞)

def initialPrivateCell : PermanentCell p :=
  .privateCell (unitIntervalVector p (0, 1))
    (unitIntervalStepData p hp0 hpfin (0, 1) (by norm_num))
    (unitIntervalVector_norm p hp0 hpfin (0, 1) (by norm_num))

def initialOrdinaryCell : PermanentCell p := .ordinary (-1, 0) (by norm_num)

def initialCells : List (PermanentCell p) := [initialPrivateCell p hp0 hpfin, initialOrdinaryCell p]

include hp0 hpfin in
theorem initial_private_coordinate : unitIntervalVector p (0, 1) = intervalAtom p (0, 1) := by
  rw [unitIntervalVector, initial_generator_unit p hp0 hpfin, inv_one, one_smul]

theorem initialPrivateCell_support : (initialPrivateCell p hp0 hpfin).support = Set.Ico (0 : ℝ) 1 :=
  unitIntervalStepData_support p hp0 hpfin (0, 1) (by norm_num)

theorem initialOrdinaryCell_support : (initialOrdinaryCell p).support = Set.Ico (-1 : ℝ) 0 := rfl

theorem initialCells_disjoint :
    List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support) (initialCells p hp0 hpfin) := by
  have hd : Disjoint (initialPrivateCell p hp0 hpfin).support (initialOrdinaryCell p).support := by
    rw [initialPrivateCell_support, initialOrdinaryCell_support]
    exact Set.disjoint_left.mpr (fun _ hx hy => not_lt_of_ge hx.1 hy.2)
  apply List.pairwise_cons.mpr
  constructor
  · intro c hc
    have hc : c = initialOrdinaryCell p := List.mem_singleton.mp hc
    subst c
    exact hd
  · exact List.pairwise_singleton _ _

theorem initialCells_partition : permanentSupport (initialCells p hp0 hpfin) = Set.Ico (-1 : ℝ) 1 := by
  have hs : permanentSupport (initialCells p hp0 hpfin) =
      (initialPrivateCell p hp0 hpfin).support ∪ (initialOrdinaryCell p).support := by
    ext x
    simp [permanentSupport, initialCells]
  rw [hs, initialPrivateCell_support, initialOrdinaryCell_support, Set.union_comm,
    Set.Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)]

theorem initial_generator_supported : SupportedOn (intervalAtom p (0, 1)) (Set.Icc (-1 : ℝ) 1) :=
  intervalAtom_supported p (0, 1) 1 (by norm_num) (by norm_num)

end SchauderTranslates.LpConstruction
