import Lean_Code.PositiveBiorthogonal.PartitionOrder

/-! Adding a disjoint block of whole grid units to an admissible partition. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal BigOperators
namespace PositiveBiorthogonal

theorem UnitBlock.carrier_eq_units {m : ℕ} (F : UnitBlock m) :
    F.carrier = ⋃ z ∈ Finset.univ.image F.unit, (gridUnit z).carrier := by
  ext x
  simp [UnitBlock.carrier, UnitBlock.cell]

namespace ActivePartition
variable {m : ℕ}

def extendCells (P : ActivePartition) (F : UnitBlock m) : Fin (P.R + m) → IntervalCell :=
  Fin.addCases P.cell F.cell

theorem extendCells_disjoint (P : ActivePartition) (F : UnitBlock m)
    (hF : Disjoint F.carrier P.active) :
    Pairwise (fun i j => Disjoint (P.extendCells F i).carrier (P.extendCells F j).carrier) := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro hij
      simp only [extendCells, Fin.addCases_left]
      exact P.disjoint (fun he => hij (congrArg (Fin.castAdd m) he))
    · intro _
      simp only [extendCells, Fin.addCases_left, Fin.addCases_right]
      exact hF.symm.mono (P.cell_subset_active i) (F.cell_subset j)
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro _
      simp only [extendCells, Fin.addCases_left, Fin.addCases_right]
      exact hF.mono (F.cell_subset i) (P.cell_subset_active j)
    · intro hij
      simp only [extendCells, Fin.addCases_right]
      exact F.disjoint (fun he => hij (congrArg (Fin.natAdd P.R) he))

theorem extendCells_cover (P : ActivePartition) (F : UnitBlock m) :
    (⋃ i : Fin (P.R + m), (P.extendCells F i).carrier) = P.active ∪ F.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    revert hi
    refine Fin.addCases (fun i hi => ?_) (fun i hi => ?_) i
    · exact Or.inl (P.cell_subset_active i (by simpa [extendCells] using hi))
    · exact Or.inr (F.cell_subset i (by simpa [extendCells] using hi))
  · rintro (hx | hx)
    · have hu : x ∈ ⋃ i : Fin P.R, (P.cell i).carrier := by rw [P.cover]; exact hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hu
      exact mem_iUnion.mpr ⟨i.castAdd m, by simpa [extendCells] using hi⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i.natAdd P.R, by simpa [extendCells] using hi⟩

def extend (P : ActivePartition) (F : UnitBlock m) (hF : Disjoint F.carrier P.active) : ActivePartition where
  units := P.units ∪ Finset.univ.image F.unit
  units_nonempty := P.units_nonempty.mono Finset.subset_union_left
  R := P.R + m
  R_pos := by have h := P.R_pos; omega
  cell := P.extendCells F
  disjoint := P.extendCells_disjoint F hF
  cover := by
    rw [P.extendCells_cover, F.carrier_eq_units]
    simp only [active, Finset.mem_union, iUnion_or, iUnion_union_distrib]
  in_grid := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · obtain ⟨n, hn, hi⟩ := P.in_grid i
      exact ⟨n, Finset.mem_union_left _ hn, by simpa [extendCells] using hi⟩
    · refine ⟨F.unit i, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), ?_⟩
      simp [extendCells, UnitBlock.cell]

@[simp] theorem extend_count (P : ActivePartition) (F : UnitBlock m) (hF : Disjoint F.carrier P.active) :
    (P.extend F hF).R = P.R + m := rfl

theorem extend_active (P : ActivePartition) (F : UnitBlock m) (hF : Disjoint F.carrier P.active) :
    (P.extend F hF).active = P.active ∪ F.carrier := by
  rw [active, F.carrier_eq_units]
  change (⋃ z ∈ P.units ∪ Finset.univ.image F.unit, (gridUnit z).carrier) = _
  simp only [active, Finset.mem_union, iUnion_or, iUnion_union_distrib]

theorem extend_cell_cases (P : ActivePartition) (F : UnitBlock m) (hF : Disjoint F.carrier P.active)
    (j : Fin (P.extend F hF).R) :
    (∃ i : Fin P.R, (P.extend F hF).cell j = P.cell i) ∨
      ∃ i : Fin m, (P.extend F hF).cell j = F.cell i := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · left
    exact ⟨i, by simp [extend, extendCells]⟩
  · right
    exact ⟨i, by simp [extend, extendCells]⟩

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem extend_averageCLM (P : ActivePartition) (F : UnitBlock m) (hF : Disjoint F.carrier P.active) :
    (P.extend F hF).averageCLM (𝕜 := 𝕜) (p := p) (q := q) =
      P.averageCLM (q := q) + F.averageCLM (q := q) := by
  change (∑ i : Fin (P.R + m), (P.extendCells F i).averageCLM (𝕜 := 𝕜) (p := p) (q := q)) = _
  rw [Fin.sum_univ_add]
  simp only [extendCells, Fin.addCases_left, Fin.addCases_right, averageCLM, UnitBlock.averageCLM]

end ActivePartition
end PositiveBiorthogonal
