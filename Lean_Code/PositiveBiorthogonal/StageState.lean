import Lean_Code.PositiveBiorthogonal.PartitionExtension

/-! Numerical and admissible data at a recursive stage; previous data remain accessible by index. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace PositiveBiorthogonal

theorem RefinementTrace.units_eq_initial {N : ℕ} (T : RefinementTrace N) (i : Fin (N + 1)) :
    (T.state i).units = (T.state 0).units := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => rw [T.next]; exact ih

structure StageState where
  activeCount : ℕ
  activeCount_pos : 0 < activeCount
  part : ActivePartition
  units_eq : part.units = prefixUnits activeCount
  ordered : Monotone (fun i : Fin part.R => (part.cell i).left)
  totalCount : ℕ
  totalCount_pos : 0 < totalCount

def rootPartition : ActivePartition where
  units := {0}
  units_nonempty := Finset.singleton_nonempty _
  R := 1
  R_pos := by decide
  cell _ := gridUnit 0
  disjoint := by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _))
  cover := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_singleton]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨0, rfl, hi⟩
    · rintro ⟨n, rfl, hx⟩
      exact ⟨0, hx⟩
  in_grid _ := ⟨0, Finset.mem_singleton_self _, subset_rfl⟩

def initialStage : StageState where
  activeCount := 1
  activeCount_pos := by decide
  part := rootPartition
  units_eq := by simp [rootPartition, prefixUnits, Finset.range_one]
  ordered := fun _ _ _ => le_rfl
  totalCount := 1
  totalCount_pos := by decide

namespace StageState

theorem active_eq_block (S : StageState) : S.part.active = (enumeratedBlock 0 S.activeCount).carrier := by
  rw [prefix_block_carrier]
  simp only [ActivePartition.active, S.units_eq]

def fresh (S : StageState) (m : ℕ) : UnitBlock m := enumeratedBlock S.activeCount m

theorem fresh_disjoint (S : StageState) (m : ℕ) : Disjoint (S.fresh m).carrier S.part.active := by
  rw [S.active_eq_block]
  exact enumerated_fresh_disjoint _ _

def extendAfter (S : StageState) {N : ℕ} (T : RefinementTrace N) (hT : T.state 0 = S.part) : StageState := by
  let Q := T.state (Fin.last N)
  let F := S.fresh (2 * N)
  have hQA : Q.active = S.part.active := (T.active_eq_initial _).trans (congrArg ActivePartition.active hT)
  have hF : Disjoint F.carrier Q.active := by rw [hQA]; exact S.fresh_disjoint _
  exact
    { activeCount := S.activeCount + 2 * N
      activeCount_pos := by have h := S.activeCount_pos; omega
      part := (Q.extend F hF).sorted
      units_eq := by
        change Q.units ∪ Finset.univ.image F.unit = prefixUnits (S.activeCount + 2 * N)
        rw [prefixUnits_add]
        congr 1
        exact (T.units_eq_initial _).trans ((congrArg ActivePartition.units hT).trans S.units_eq)
      ordered := (Q.extend F hF).sorted_monotone
      totalCount := S.totalCount + 3 * N
      totalCount_pos := by have h := S.totalCount_pos; omega }

@[simp] theorem extendAfter_activeCount (S : StageState) {N : ℕ} (T : RefinementTrace N)
    (hT : T.state 0 = S.part) : (S.extendAfter T hT).activeCount = S.activeCount + 2 * N := rfl

@[simp] theorem extendAfter_totalCount (S : StageState) {N : ℕ} (T : RefinementTrace N)
    (hT : T.state 0 = S.part) : (S.extendAfter T hT).totalCount = S.totalCount + 3 * N := rfl

theorem extendAfter_count (S : StageState) {N : ℕ} (T : RefinementTrace N)
    (hT : T.state 0 = S.part) : (S.extendAfter T hT).part.R = (T.state (Fin.last N)).R + 2 * N := rfl

theorem extendAfter_active (S : StageState) {N : ℕ} (T : RefinementTrace N)
    (hT : T.state 0 = S.part) : (S.extendAfter T hT).part.active =
      S.part.active ∪ (S.fresh (2 * N)).carrier := by
  unfold extendAfter
  rw [ActivePartition.sorted_active, ActivePartition.extend_active, T.active_eq_initial, hT]

theorem extendAfter_old_cell {S : StageState} {N : ℕ} (T : RefinementTrace N) (hT : T.state 0 = S.part)
    (i : Fin (S.extendAfter T hT).part.R) :
    (∃ j : Fin (T.state (Fin.last N)).R, (S.extendAfter T hT).part.cell i = (T.state (Fin.last N)).cell j) ∨
      ∃ j : Fin (2 * N), (S.extendAfter T hT).part.cell i = (S.fresh (2 * N)).cell j := by
  obtain ⟨j, hj⟩ := ActivePartition.sorted_cell _ i
  change (S.extendAfter T hT).part.cell i = _ at hj
  rw [hj]
  exact ActivePartition.extend_cell_cases _ _ _ j

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem extendAfter_average (S : StageState) {N : ℕ} (T : RefinementTrace N)
    (hT : T.state 0 = S.part) :
    (S.extendAfter T hT).part.averageCLM (𝕜 := 𝕜) (p := p) (q := q) =
      (T.state (Fin.last N)).averageCLM (q := q) + (S.fresh (2 * N)).averageCLM (q := q) := by
  unfold extendAfter
  rw [ActivePartition.sorted_averageCLM, ActivePartition.extend_averageCLM]

end StageState
end PositiveBiorthogonal
