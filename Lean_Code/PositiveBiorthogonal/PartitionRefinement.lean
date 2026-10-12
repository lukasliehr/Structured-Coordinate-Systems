import Lean_Code.PositiveBiorthogonal.SplittingGeometry
import Mathlib.Data.Fin.Tuple.Basic

/-! One admissible refinement: retain the remainder at the old index and append the removed cell. -/
noncomputable section
set_option autoImplicit false
open Set
namespace PositiveBiorthogonal
namespace ActivePartition

def splitCells (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit) : Fin (P.R + 1) → IntervalCell :=
  Fin.lastCases S.leftChild (fun i => if i = j then S.rightChild else P.cell i)

@[simp] theorem splitCells_last (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit) :
    P.splitCells j S (Fin.last P.R) = S.leftChild := by simp [splitCells]

@[simp] theorem splitCells_old (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit) (i : Fin P.R) :
    P.splitCells j S i.castSucc = if i = j then S.rightChild else P.cell i := by simp [splitCells]

theorem splitCells_old_subset (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit)
    (hS : S.parent = P.cell j) (i : Fin P.R) :
    (P.splitCells j S i.castSucc).carrier ⊆ (P.cell i).carrier := by
  rw [splitCells_old]
  by_cases hi : i = j
  · subst i
    simpa only [if_true, hS] using S.right_subset
  · simp only [hi, if_false, subset_refl]

theorem splitCells_last_disjoint_old (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit)
    (hS : S.parent = P.cell j) (i : Fin P.R) :
    Disjoint S.leftChild.carrier (P.splitCells j S i.castSucc).carrier := by
  rw [splitCells_old]
  by_cases hi : i = j
  · subst i
    simpa using S.children_disjoint
  · rw [if_neg hi]
    have hs : S.leftChild.carrier ⊆ (P.cell j).carrier := by simpa only [hS] using S.left_subset
    exact (P.disjoint (Ne.symm hi)).mono_left hs

theorem splitCells_disjoint (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit)
    (hS : S.parent = P.cell j) :
    Pairwise (fun a b => Disjoint (P.splitCells j S a).carrier (P.splitCells j S b).carrier) := by
  intro a b hab
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨k, rfl⟩ | rfl
    · have hik : i ≠ k := fun he => hab (congrArg Fin.castSucc he)
      exact (P.disjoint hik).mono (P.splitCells_old_subset j S hS i) (P.splitCells_old_subset j S hS k)
    · rw [splitCells_last]
      exact (P.splitCells_last_disjoint_old j S hS i).symm
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨k, rfl⟩ | rfl
    · rw [splitCells_last]
      exact P.splitCells_last_disjoint_old j S hS k
    · exact False.elim (hab rfl)

theorem splitCells_union (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit)
    (hS : S.parent = P.cell j) :
    (⋃ i : Fin (P.R + 1), (P.splitCells j S i).carrier) = ⋃ i : Fin P.R, (P.cell i).carrier := by
  ext x
  simp only [mem_iUnion, Fin.exists_iff_castSucc, splitCells_last]
  constructor
  · rintro (hx | ⟨i, hx⟩)
    · refine ⟨j, ?_⟩
      rw [← hS]
      exact S.left_subset hx
    · exact ⟨i, P.splitCells_old_subset j S hS i hx⟩
  · rintro ⟨i, hx⟩
    by_cases hi : i = j
    · subst i
      have hs : x ∈ S.leftChild.carrier ∪ S.rightChild.carrier := by
        rw [S.children_union, hS]
        exact hx
      rcases hs with hb | hc
      · exact Or.inl hb
      · exact Or.inr ⟨j, by simpa using hc⟩
    · exact Or.inr ⟨i, by simpa [hi] using hx⟩

def refine (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit) (hS : S.parent = P.cell j) : ActivePartition where
  units := P.units
  units_nonempty := P.units_nonempty
  R := P.R + 1
  R_pos := by omega
  cell := P.splitCells j S
  disjoint := P.splitCells_disjoint j S hS
  cover := (P.splitCells_union j S hS).trans P.cover
  in_grid i := by
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · obtain ⟨n, hn, hkn⟩ := P.in_grid k
      exact ⟨n, hn, (P.splitCells_old_subset j S hS k).trans hkn⟩
    · obtain ⟨n, hn, hjn⟩ := P.in_grid j
      refine ⟨n, hn, ?_⟩
      rw [splitCells_last]
      exact S.left_subset.trans (by simpa only [hS] using hjn)

@[simp] theorem refine_active (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit)
    (hS : S.parent = P.cell j) : (P.refine j S hS).active = P.active := rfl

@[simp] theorem refine_count (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit)
    (hS : S.parent = P.cell j) : (P.refine j S hS).R = P.R + 1 := rfl

end ActivePartition
end PositiveBiorthogonal
