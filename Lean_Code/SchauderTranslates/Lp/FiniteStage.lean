import Lean_Code.SchauderTranslates.Lp.PhysicalStageLists

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def initialBirth (p : ℝ≥0∞) : BirthAtom p := ⟨0, 0, intervalAtom p (0, 1)⟩

theorem initialBirth_vector (p : ℝ≥0∞) : (initialBirth p).vector = intervalAtom p (0, 1) :=
  translate_zero p _

/-- A finite physical stage. Roots are tied to their permanent cell and
internal Haar index, and each branch retains its actual finite recursion.
Every reference atom retains its birth generator. -/
structure FiniteStage (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp2 : 2 < p) (hpfin : p ≠ ∞) where
  time : ℕ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  radius_time : (time : ℝ) ≤ radius
  generator : LebesgueLp p
  generator_step : IsCompactStep p generator
  generator_unit_lower : 1 ≤ ‖generator‖
  generator_support : SupportedOn generator (Set.Icc (-radius) radius)
  cells : List (PermanentCell p)
  initial_cells_prefix : initialCells p (ne_of_gt (lt_trans (by norm_num) hp2)) hpfin <+: cells
  cells_disjoint : List.Pairwise (fun c d : PermanentCell p => Disjoint c.support d.support) cells
  cells_partition : permanentSupport cells = Set.Ico (-radius) radius
  branches : List (PhysicalBranch p)
  branch_origins : (branches.map PhysicalBranch.origin).Nodup
  branch_root : ∀ B ∈ branches, ∃ hi : B.origin.1 < cells.length,
    B.root = (((cells[B.origin.1]).roots p q hp2 hpfin).root B.origin.2).val
  branch_support : ∀ B ∈ branches, B.Supported radius
  branch_cells : ∀ B ∈ branches, ∀ L ∈ B.layers, ∀ i, L.cell i ∈ cells
  births : List (BirthAtom p)
  birth_initial : births.head? = some (initialBirth p)
  birth_parameters : (births.map BirthAtom.parameter).Nodup
  birth_time : ∀ b ∈ births, b.time ≤ time
  birth_support : ∀ b ∈ births, SupportedOn b.vector (Set.Icc (-radius) radius)
  birth_step : ∀ b ∈ births, IsCompactStep p b.vector
  birth_unit_lower : ∀ b ∈ births, 1 ≤ ‖b.vector‖

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp2 : 2 < p) (hpfin : p ≠ ∞)

def FiniteStage.initial : FiniteStage p q hp2 hpfin := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hp2)
  refine {
    time := 0
    radius := 1
    radius_nonneg := by norm_num
    radius_time := by norm_num
    generator := intervalAtom p (0, 1)
    generator_step := intervalAtom_isCompactStep p (0, 1)
    generator_unit_lower := by rw [initial_generator_unit p hp0 hpfin]
    generator_support := initial_generator_supported p
    cells := initialCells p hp0 hpfin
    initial_cells_prefix := ⟨[], by simp⟩
    cells_disjoint := initialCells_disjoint p hp0 hpfin
    cells_partition := initialCells_partition p hp0 hpfin
    branches := []
    branch_origins := by simp
    branch_root := by simp
    branch_support := by simp
    branch_cells := by simp
    births := [initialBirth p]
    birth_initial := rfl
    birth_parameters := by simp
    birth_time := by simp [initialBirth]
    birth_support := ?_
    birth_step := ?_
    birth_unit_lower := ?_ }
  · intro b hb
    obtain rfl := List.mem_singleton.mp hb
    rw [initialBirth_vector]
    exact initial_generator_supported p
  · intro b hb
    obtain rfl := List.mem_singleton.mp hb
    rw [initialBirth_vector]
    exact intervalAtom_isCompactStep p (0, 1)
  · intro b hb
    obtain rfl := List.mem_singleton.mp hb
    rw [initialBirth_vector, initial_generator_unit p hp0 hpfin]

variable {p q hp2 hpfin}

theorem FiniteStage.generator_ne_zero (S : FiniteStage p q hp2 hpfin) : S.generator ≠ 0 :=
  norm_pos_iff.mp (zero_lt_one.trans_le S.generator_unit_lower)

theorem FiniteStage.old_count_pos (S : FiniteStage p q hp2 hpfin) : 1 ≤ S.births.length := by
  cases hbs : S.births with
  | nil =>
      have h := S.birth_initial
      simp [hbs] at h
  | cons b bs => simp [hbs]

def FiniteStage.parameters (S : FiniteStage p q hp2 hpfin) : Finset ℝ := by
  classical
  exact (S.births.map BirthAtom.parameter).toFinset

def FiniteStage.editBudget (S : FiniteStage p q hp2 hpfin) : ℝ :=
  stageEditBudget (haarStrongConstant q.toReal) (S.time + 1) S.births.length

theorem FiniteStage.editBudget_pos (S : FiniteStage p q hp2 hpfin) : 0 < S.editBudget :=
  stageEditBudget_pos (haarStrongConstant_ge_one (q := q) hp2 hpfin) _ S.old_count_pos

end SchauderTranslates.LpConstruction
