import Lean_Code.SchauderTranslates.Lp.HaarModel

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SchauderTranslates.LpConstruction

abbrev DyadicCell := Σ n, Fin (2 ^ n)

def dyadicCellSet (j : DyadicCell) : Set ℝ := dyadicInterval j.1 j.2

def dyadicCellsThrough (N : ℕ) : Finset DyadicCell :=
  (Finset.range (N + 1)).sigma (fun _ => Finset.univ : ∀ n, Finset (Fin (2 ^ n)))

@[simp] theorem mem_dyadicCellsThrough (N : ℕ) (j : DyadicCell) :
    j ∈ dyadicCellsThrough N ↔ j.1 ≤ N := by
  simp [dyadicCellsThrough]

theorem dyadicCellSet_nonempty (j : DyadicCell) : (dyadicCellSet j).Nonempty := by
  refine ⟨dyadicEndpoint j.1 j.2, le_rfl, ?_⟩
  exact dyadicEndpoint_strictMono j.1 (Nat.lt_succ_self _)

theorem dyadicCellSet_measurable (j : DyadicCell) : MeasurableSet (dyadicCellSet j) :=
  dyadicInterval_measurable _ _

theorem dyadicCellSet_subset_unit (j : DyadicCell) :
    dyadicCellSet j ⊆ Set.Ico (0 : ℝ) 1 := dyadicInterval_subset_unit _ _ j.2.isLt

theorem dyadicCellSet_nested_or_disjoint {i j : DyadicCell} (hij : i.1 ≤ j.1) :
    dyadicCellSet j ⊆ dyadicCellSet i ∨ Disjoint (dyadicCellSet j) (dyadicCellSet i) :=
  dyadicInterval_nested_or_disjoint hij _ _

theorem dyadicCellSet_disjoint_same {i j : DyadicCell} (hlevel : i.1 = j.1)
    (hne : i ≠ j) : Disjoint (dyadicCellSet i) (dyadicCellSet j) := by
  rcases i with ⟨n, k⟩
  rcases j with ⟨m, l⟩
  dsimp at hlevel
  subst m
  apply dyadicInterval_disjoint_same
  intro he
  have hkl : k = l := Fin.ext he
  subst l
  exact hne rfl

/-- The inclusion-maximal cells in a finite dyadic collection are exactly
those having no ancestor of smaller level in that collection. -/
def maximalDyadicCells (s : Finset DyadicCell) : Finset DyadicCell := by
  classical
  exact s.filter (fun j => ∀ i ∈ s, i.1 < j.1 → ¬dyadicCellSet j ⊆ dyadicCellSet i)

@[simp] theorem mem_maximalDyadicCells (s : Finset DyadicCell) (j : DyadicCell) :
    j ∈ maximalDyadicCells s ↔
      j ∈ s ∧ ∀ i ∈ s, i.1 < j.1 → ¬dyadicCellSet j ⊆ dyadicCellSet i := by
  classical
  simp [maximalDyadicCells]

theorem maximalDyadicCells_subset (s : Finset DyadicCell) : maximalDyadicCells s ⊆ s :=
  fun _ hj => (mem_maximalDyadicCells s _).mp hj |>.1

/-- Maximal selected dyadic cells are disjoint as actual half-open sets. -/
theorem maximalDyadicCells_disjoint (s : Finset DyadicCell) {i j : DyadicCell}
    (hi : i ∈ maximalDyadicCells s) (hj : j ∈ maximalDyadicCells s) (hne : i ≠ j) :
    Disjoint (dyadicCellSet i) (dyadicCellSet j) := by
  obtain ⟨his, himax⟩ := (mem_maximalDyadicCells s i).mp hi
  obtain ⟨hjs, hjmax⟩ := (mem_maximalDyadicCells s j).mp hj
  rcases lt_trichotomy i.1 j.1 with hij | hij | hji
  · rcases dyadicCellSet_nested_or_disjoint hij.le with hsub | hdis
    · exact ((hjmax i his hij) hsub).elim
    · exact hdis.symm
  · exact dyadicCellSet_disjoint_same hij hne
  · rcases dyadicCellSet_nested_or_disjoint hji.le with hsub | hdis
    · exact ((himax j hjs hji) hsub).elim
    · exact hdis

/-- Every member of a finite dyadic collection is contained in a selected
maximal cell. Minimizing the ancestor's level makes the selection finite. -/
theorem maximalDyadicCells_cover (s : Finset DyadicCell) {i : DyadicCell} (hi : i ∈ s) :
    ∃ j ∈ maximalDyadicCells s, j.1 ≤ i.1 ∧ dyadicCellSet i ⊆ dyadicCellSet j := by
  classical
  let ancestors := s.filter (fun j => dyadicCellSet i ⊆ dyadicCellSet j)
  have hia : i ∈ ancestors := Finset.mem_filter.mpr ⟨hi, Set.Subset.rfl⟩
  obtain ⟨j, hja, hmin⟩ := Finset.exists_min_image ancestors (fun j => j.1) ⟨i, hia⟩
  obtain ⟨hjs, hij⟩ := Finset.mem_filter.mp hja
  refine ⟨j, (mem_maximalDyadicCells s j).mpr ⟨hjs, ?_⟩, hmin i hia, hij⟩
  intro k hks hkj hsub
  have hka : k ∈ ancestors := Finset.mem_filter.mpr ⟨hks, hij.trans hsub⟩
  exact (not_le_of_gt hkj) (hmin k hka)

theorem maximalDyadicCells_union (s : Finset DyadicCell) :
    (⋃ j ∈ maximalDyadicCells s, dyadicCellSet j) = ⋃ j ∈ s, dyadicCellSet j := by
  apply Set.Subset.antisymm
  · exact Set.biUnion_subset_biUnion_left (maximalDyadicCells_subset s)
  · intro x hx
    obtain ⟨i, his, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨j, hj, _, hij⟩ := maximalDyadicCells_cover s his
    exact Set.mem_iUnion₂.mpr ⟨j, hj, hij hxi⟩

def dyadicCellParent : DyadicCell → DyadicCell
  | ⟨0, _⟩ => ⟨0, ⟨0, by norm_num⟩⟩
  | ⟨n + 1, k⟩ => ⟨n, ⟨(k : ℕ) / 2, by
      have hk : (k : ℕ) < 2 ^ n * 2 := by simpa only [pow_succ] using k.isLt
      omega⟩⟩

theorem dyadicCellParent_level_lt {j : DyadicCell} (hj : 0 < j.1) :
    (dyadicCellParent j).1 < j.1 := by
  rcases j with ⟨n, k⟩
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hj).elim
  | succ n => exact Nat.lt_succ_self n

theorem dyadicCell_subset_parent (j : DyadicCell) :
    dyadicCellSet j ⊆ dyadicCellSet (dyadicCellParent j) := by
  rcases j with ⟨n, k⟩
  cases n with
  | zero =>
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact Set.Subset.rfl
  | succ n => exact dyadicInterval_parent_subset n k

/-- A maximal non-root bad cell has a good parent; this supplies the
factor two in the Calderón–Zygmund good-part bound. -/
theorem maximalDyadicCell_parent_not_mem (s : Finset DyadicCell) {j : DyadicCell}
    (hj : j ∈ maximalDyadicCells s) (hlevel : 0 < j.1) : dyadicCellParent j ∉ s := by
  intro hp
  exact ((mem_maximalDyadicCells s j).mp hj).2 (dyadicCellParent j) hp
    (dyadicCellParent_level_lt hlevel) (dyadicCell_subset_parent j)

theorem dyadicCellParent_mem_through {N : ℕ} {j : DyadicCell}
    (hj : j ∈ dyadicCellsThrough N) : dyadicCellParent j ∈ dyadicCellsThrough N := by
  rw [mem_dyadicCellsThrough] at hj ⊢
  rcases j with ⟨n, k⟩
  cases n with
  | zero => exact hj
  | succ n => exact (Nat.le_succ n).trans hj

end SchauderTranslates.LpConstruction
