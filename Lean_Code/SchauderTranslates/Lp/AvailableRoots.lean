import Lean_Code.SchauderTranslates.Lp.Stages
import Lean_Code.SchauderTranslates.Lp.RootPriority

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {hp2 : 2 < p} {hpfin : p ≠ ∞}

theorem FiniteStage.cells_length_pos (S : FiniteStage p q hp2 hpfin) : 0 < S.cells.length := by
  have h := S.initial_cells_prefix.length_le
  simp only [initialCells, List.length_cons, List.length_nil] at h
  omega

def FiniteStage.AvailableRoot (S : FiniteStage p q hp2 hpfin) (ab : ℕ × ℕ) : Prop :=
  ab.1 < S.cells.length ∧ ab ∉ S.branches.map PhysicalBranch.origin

theorem FiniteStage.availableRoot_nonempty (S : FiniteStage p q hp2 hpfin) :
    ∃ ab, S.AvailableRoot ab := by
  classical
  let used := (S.branches.map PhysicalBranch.origin).toFinset
  let b := (∑ ab ∈ used, ab.2) + 1
  refine ⟨(0, b), S.cells_length_pos, ?_⟩
  intro hab
  have hab : (0, b) ∈ used := List.mem_toFinset.mpr hab
  have hsum : b ≤ ∑ ab ∈ used, ab.2 := Finset.single_le_sum
    (f := fun ab : ℕ × ℕ => ab.2) (fun ab _ => Nat.zero_le ab.2) hab
  dsimp [b] at hsum
  omega

theorem FiniteStage.exists_least_available (S : FiniteStage p q hp2 hpfin) :
    ∃ ab, S.AvailableRoot ab ∧ ∀ cd, S.AvailableRoot cd → rootPriority ab ≤ rootPriority cd := by
  classical
  have hn : ∃ n, ∃ ab, S.AvailableRoot ab ∧ rootPriority ab = n := by
    obtain ⟨ab, hab⟩ := S.availableRoot_nonempty
    exact ⟨rootPriority ab, ab, hab, rfl⟩
  obtain ⟨ab, hab, hpriority⟩ := Nat.find_spec hn
  refine ⟨ab, hab, ?_⟩
  intro cd hcd
  rw [hpriority]
  exact Nat.find_min' hn ⟨cd, hcd, rfl⟩

def FiniteStage.leastAvailable (S : FiniteStage p q hp2 hpfin) : ℕ × ℕ :=
  Classical.choose S.exists_least_available

theorem FiniteStage.leastAvailable_available (S : FiniteStage p q hp2 hpfin) :
    S.AvailableRoot S.leastAvailable := (Classical.choose_spec S.exists_least_available).1

theorem FiniteStage.leastAvailable_minimal (S : FiniteStage p q hp2 hpfin) (ab : ℕ × ℕ)
    (hab : S.AvailableRoot ab) : rootPriority S.leastAvailable ≤ rootPriority ab :=
  (Classical.choose_spec S.exists_least_available).2 ab hab

def FiniteStage.introduceLeast (S : FiniteStage p q hp2 hpfin) : FiniteStage p q hp2 hpfin :=
  S.introduceRoot ⟨S.leastAvailable.1, S.leastAvailable_available.1⟩ S.leastAvailable.2
    S.leastAvailable_available.2

theorem FiniteStage.introduceLeast_branch_count (S : FiniteStage p q hp2 hpfin) :
    S.introduceLeast.branches.length = S.branches.length + 1 := S.introduceRoot_branch_count _ _ _

end SchauderTranslates.LpConstruction
