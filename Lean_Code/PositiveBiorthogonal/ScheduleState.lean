import Lean_Code.PositiveBiorthogonal.RefinementTrace

/-! States that retain each old cell's geometric remainder while appending removed pieces. -/
noncomputable section
set_option autoImplicit false
open Set
namespace PositiveBiorthogonal

theorem geometricSplit_initial_parent (D : IntervalCell) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    (geometricSplit D θ hθ hθ1 0).parent = D := by
  cases D
  simp [geometricSplit, geometricPoint]

structure GeometricState (P : ActivePartition) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) (n : ℕ) where
  part : ActivePartition
  count_eq : part.R = P.R + n
  root : Fin P.R → Fin part.R
  root_injective : Function.Injective root
  count : Fin P.R → ℕ
  root_cell : ∀ i, part.cell (root i) = (geometricSplit (P.cell i) θ hθ hθ1 (count i)).parent
  cell_cases : ∀ j : Fin part.R, (∃ i : Fin P.R, j = root i) ∨
    ∃ i : Fin P.R, ∃ k : ℕ, part.cell j = (geometricSplit (P.cell i) θ hθ hθ1 k).leftChild

namespace GeometricState
variable {P : ActivePartition} {θ : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1} {n : ℕ}

def initial (P : ActivePartition) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) : GeometricState P θ hθ hθ1 0 where
  part := P
  count_eq := by simp
  root := id
  root_injective := Function.injective_id
  count _ := 0
  root_cell i := (geometricSplit_initial_parent (P.cell i) θ hθ hθ1).symm
  cell_cases j := Or.inl ⟨j, rfl⟩

def step (S : GeometricState P θ hθ hθ1 n) (i : Fin P.R) : GeometricState P θ hθ hθ1 (n + 1) := by
  classical
  let G := geometricSplit (P.cell i) θ hθ hθ1 (S.count i)
  have hG : G.parent = S.part.cell (S.root i) := (S.root_cell i).symm
  exact
    { part := S.part.refine (S.root i) G hG
      count_eq := by
        change S.part.R + 1 = P.R + (n + 1)
        rw [S.count_eq]
        omega
      root := fun j => (S.root j).castSucc
      root_injective := fun j k he => S.root_injective (Fin.castSucc_inj.mp he)
      count := Function.update S.count i (S.count i + 1)
      root_cell := by
        intro j
        change S.part.splitCells (S.root i) G (S.root j).castSucc = _
        rw [S.part.splitCells_old]
        by_cases hji : j = i
        · subst j
          simp only [if_true, Function.update_self]
          exact geometricSplit_remainder (P.cell i) θ hθ hθ1 (S.count i)
        · have hr : S.root j ≠ S.root i := fun he => hji (S.root_injective he)
          rw [if_neg hr, Function.update_of_ne hji]
          exact S.root_cell j
      cell_cases := by
        intro k
        change Fin (S.part.R + 1) at k
        rcases Fin.eq_castSucc_or_eq_last k with ⟨l, rfl⟩ | rfl
        · by_cases hl : ∃ j : Fin P.R, l = S.root j
          · obtain ⟨j, hj⟩ := hl
            exact Or.inl ⟨j, congrArg Fin.castSucc hj⟩
          · obtain hroot | ⟨j, t, ht⟩ := S.cell_cases l
            · exact False.elim (hl hroot)
            · right
              refine ⟨j, t, ?_⟩
              change S.part.splitCells (S.root i) G l.castSucc = _
              rw [S.part.splitCells_old, if_neg (fun he => hl ⟨i, he⟩)]
              exact ht
        · right
          refine ⟨i, S.count i, ?_⟩
          change S.part.splitCells (S.root i) G (Fin.last S.part.R) = _
          rw [S.part.splitCells_last] }

@[simp] theorem step_count (S : GeometricState P θ hθ hθ1 n) (i j : Fin P.R) :
    (S.step i).count j = if j = i then S.count i + 1 else S.count j := by
  classical
  simp [step, Function.update_apply]

@[simp] theorem step_part (S : GeometricState P θ hθ hθ1 n) (i : Fin P.R) :
    (S.step i).part = S.part.refine (S.root i) (geometricSplit (P.cell i) θ hθ hθ1 (S.count i))
      (S.root_cell i).symm := rfl

def run (P : ActivePartition) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (visit : ℕ → Fin P.R) : ∀ n : ℕ, GeometricState P θ hθ hθ1 n
  | 0 => initial P θ hθ hθ1
  | n + 1 => (run P θ hθ hθ1 visit n).step (visit n)

theorem run_count (P : ActivePartition) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (visit : ℕ → Fin P.R) (n : ℕ) (i : Fin P.R) :
    (run P θ hθ hθ1 visit n).count i = ((Finset.range n).filter (fun k => visit k = i)).card := by
  classical
  induction n with
  | zero => simp [run, initial]
  | succ n ih =>
    rw [run, step_count]
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hi : visit n = i
    · simp [hi, ih, eq_comm]
    · simp [hi, ih, Ne.symm hi]

end GeometricState
end PositiveBiorthogonal
