import Lean_Code.SchauderTranslates.Lp.RoundCells
import Lean_Code.SchauderTranslates.Lp.PrefixListLimit

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp2 : 2 < p) (hpfin : p ≠ ∞)

def permanentCellCatalog : PrefixListLimit (PermanentCell p) where
  list n := (roundStage p q hp2 hpfin n).cells
  nested := roundStage_cells_mono p q hp2 hpfin
  length_gt n := by have h := roundStage_cell_count_ge p q hp2 hpfin n; omega

def globalCell (n : ℕ) : PermanentCell p := (permanentCellCatalog p q hp2 hpfin).entry n

theorem globalCell_eq (i n : ℕ) (hi : i < (roundStage p q hp2 hpfin n).cells.length) :
    globalCell p q hp2 hpfin i = (roundStage p q hp2 hpfin n).cells[i] :=
  (permanentCellCatalog p q hp2 hpfin).entry_eq i n hi

theorem globalCell_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (globalCell p q hp2 hpfin i).support (globalCell p q hp2 hpfin j).support) :=
  (permanentCellCatalog p q hp2 hpfin).entry_pairwise (fun h => h.symm)
    (fun n => (roundStage p q hp2 hpfin n).cells_disjoint)

/-- The actual permanent cells, with their unchanged step data and root
systems, form a countable disjoint partition of the whole real line. -/
theorem globalCell_cover (x : ℝ) : ∃ i, x ∈ (globalCell p q hp2 hpfin i).support := by
  obtain ⟨n, hx⟩ := roundStage_committed_cover p q hp2 hpfin x
  rw [← (roundStage p q hp2 hpfin n).cells_partition] at hx
  obtain ⟨c, hc, hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨i, hi, he⟩ := (permanentCellCatalog p q hp2 hpfin).mem_iff n c |>.mp hc
  refine ⟨i, ?_⟩
  change x ∈ ((permanentCellCatalog p q hp2 hpfin).entry i).support
  rwa [he]

theorem globalCell_union : (⋃ i, (globalCell p q hp2 hpfin i).support) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact globalCell_cover p q hp2 hpfin x

def birthCatalog : PrefixListLimit (BirthAtom p) where
  list n := (roundStage p q hp2 hpfin n).births
  nested := roundStage_births_mono p q hp2 hpfin
  length_gt n := by have h := roundStage_birth_count_ge p q hp2 hpfin n; omega

def globalBirth (m : ℕ) : BirthAtom p := (birthCatalog p q hp2 hpfin).entry m

def globalParameter (m : ℕ) : ℝ := (globalBirth p q hp2 hpfin m).parameter

theorem globalBirth_eq (m n : ℕ) (hm : m < (roundStage p q hp2 hpfin n).births.length) :
    globalBirth p q hp2 hpfin m = (roundStage p q hp2 hpfin n).births[m] :=
  (birthCatalog p q hp2 hpfin).entry_eq m n hm

theorem globalBirth_initial : globalBirth p q hp2 hpfin 0 = initialBirth p := rfl

theorem globalParameter_injective : Function.Injective (globalParameter p q hp2 hpfin) :=
  (birthCatalog p q hp2 hpfin).map_entry_injective BirthAtom.parameter
    (fun n => (roundStage p q hp2 hpfin n).birth_parameters)

theorem globalBirth_isCompactStep (m : ℕ) : IsCompactStep p (globalBirth p q hp2 hpfin m).vector :=
  (birthCatalog p q hp2 hpfin).entry_property (fun n b hb => (roundStage p q hp2 hpfin n).birth_step b hb) m

theorem globalBirth_norm_lower (m : ℕ) : 1 ≤ ‖(globalBirth p q hp2 hpfin m).vector‖ :=
  (birthCatalog p q hp2 hpfin).entry_property (fun n b hb => (roundStage p q hp2 hpfin n).birth_unit_lower b hb) m

theorem globalBirth_initial_list (n : ℕ) :
    List.ofFn (fun i : Fin (roundStage p q hp2 hpfin n).births.length => globalBirth p q hp2 hpfin i.val) =
      (roundStage p q hp2 hpfin n).births := (birthCatalog p q hp2 hpfin).initial_list n

end SchauderTranslates.LpConstruction
