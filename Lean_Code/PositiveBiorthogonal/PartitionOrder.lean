import Lean_Code.PositiveBiorthogonal.GridEnumeration
import Mathlib.Data.Fin.Tuple.Sort

/-! Reindexing and sorting an admissible partition preserve its averaging operator. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace PositiveBiorthogonal
namespace ActivePartition

def reindex (P : ActivePartition) (e : Equiv.Perm (Fin P.R)) : ActivePartition where
  units := P.units
  units_nonempty := P.units_nonempty
  R := P.R
  R_pos := P.R_pos
  cell i := P.cell (e i)
  disjoint := fun i j hij => P.disjoint (fun he => hij (e.injective he))
  cover := by
    rw [e.surjective.iUnion_comp (fun i => (P.cell i).carrier)]
    exact P.cover
  in_grid i := P.in_grid (e i)

@[simp] theorem reindex_active (P : ActivePartition) (e : Equiv.Perm (Fin P.R)) :
    (P.reindex e).active = P.active := rfl

def sorted (P : ActivePartition) : ActivePartition :=
  P.reindex (Tuple.sort (fun i : Fin P.R => (P.cell i).left))

@[simp] theorem sorted_count (P : ActivePartition) : P.sorted.R = P.R := rfl
@[simp] theorem sorted_units (P : ActivePartition) : P.sorted.units = P.units := rfl
@[simp] theorem sorted_active (P : ActivePartition) : P.sorted.active = P.active := rfl

theorem sorted_monotone (P : ActivePartition) : Monotone (fun i : Fin P.sorted.R => (P.sorted.cell i).left) :=
  Tuple.monotone_sort (fun i : Fin P.R => (P.cell i).left)

theorem sorted_cell (P : ActivePartition) (i : Fin P.sorted.R) : ∃ j : Fin P.R, P.sorted.cell i = P.cell j :=
  ⟨Tuple.sort (fun i : Fin P.R => (P.cell i).left) i, rfl⟩

theorem cell_sorted (P : ActivePartition) (i : Fin P.R) : ∃ j : Fin P.sorted.R, P.cell i = P.sorted.cell j := by
  refine ⟨(Tuple.sort (fun i : Fin P.R => (P.cell i).left)).symm i, ?_⟩
  simp only [sorted, reindex, Equiv.apply_symm_apply]

theorem sorted_refines (P : ActivePartition) : P.Refines P.sorted := by
  intro i
  obtain ⟨j, hj⟩ := P.sorted_cell i
  exact ⟨j, by rw [hj]⟩

theorem refines_sorted (P : ActivePartition) : P.sorted.Refines P := by
  intro i
  obtain ⟨j, hj⟩ := P.cell_sorted i
  exact ⟨j, by rw [hj]⟩

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem reindex_averageCLM (P : ActivePartition) (e : Equiv.Perm (Fin P.R)) :
    (P.reindex e).averageCLM (𝕜 := 𝕜) (p := p) (q := q) = P.averageCLM (q := q) :=
  Equiv.sum_comp e (fun i => (P.cell i).averageCLM (𝕜 := 𝕜) (p := p) (q := q))

theorem sorted_averageCLM (P : ActivePartition) :
    P.sorted.averageCLM (𝕜 := 𝕜) (p := p) (q := q) = P.averageCLM (q := q) :=
  P.reindex_averageCLM _

end ActivePartition
end PositiveBiorthogonal
