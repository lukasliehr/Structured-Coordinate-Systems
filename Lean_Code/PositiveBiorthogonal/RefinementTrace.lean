import Lean_Code.PositiveBiorthogonal.HaarCrossPairings

/-! Finite refinement traces and biorthogonality of all their Haar pairs. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace PositiveBiorthogonal
namespace ActivePartition

def Refines (P Q : ActivePartition) : Prop :=
  ∀ i : Fin Q.R, ∃ j : Fin P.R, (Q.cell i).carrier ⊆ (P.cell j).carrier

theorem Refines.refl (P : ActivePartition) : P.Refines P := fun i => ⟨i, subset_rfl⟩

theorem Refines.trans {P Q R : ActivePartition} (hPQ : P.Refines Q) (hQR : Q.Refines R) : P.Refines R := by
  intro i
  obtain ⟨j, hij⟩ := hQR i
  obtain ⟨k, hjk⟩ := hPQ j
  exact ⟨k, hij.trans hjk⟩

theorem refine_refines (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit) (hS : S.parent = P.cell j) :
    P.Refines (P.refine j S hS) := by
  intro i
  change Fin (P.R + 1) at i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
  · exact ⟨k, P.splitCells_old_subset j S hS k⟩
  · refine ⟨j, ?_⟩
    change (P.splitCells j S (Fin.last P.R)).carrier ⊆ (P.cell j).carrier
    rw [P.splitCells_last, ← hS]
    exact S.left_subset

theorem split_separated_of_refines (P : ActivePartition) (j : Fin P.R) (S : IntervalSplit)
    (hS : S.parent = P.cell j) (R : ActivePartition) (hR : (P.refine j S hS).Refines R)
    (k : Fin R.R) (T : IntervalSplit) (hT : T.parent = R.cell k) : SplitSeparated S T := by
  obtain ⟨i, hi⟩ := hR k
  change Fin (P.R + 1) at i
  have ht : T.parent.carrier ⊆ (P.splitCells j S i).carrier := by
    rw [hT]
    exact hi
  rcases Fin.eq_castSucc_or_eq_last i with ⟨l, rfl⟩ | rfl
  · rw [P.splitCells_old] at ht
    by_cases hlj : l = j
    · rw [if_pos hlj] at ht
      exact Or.inr (Or.inr ht)
    · rw [if_neg hlj] at ht
      left
      rw [hS]
      exact (P.disjoint (Ne.symm hlj)).mono_right ht
  · rw [P.splitCells_last] at ht
    exact Or.inr (Or.inl ht)

end ActivePartition

/-- A finite trace records actual admissible refinements, rather than assuming Haar identities. -/
structure RefinementTrace (N : ℕ) where
  state : Fin (N + 1) → ActivePartition
  split : Fin N → IntervalSplit
  index : ∀ i : Fin N, Fin (state i.castSucc).R
  parent : ∀ i : Fin N, (split i).parent = (state i.castSucc).cell (index i)
  next : ∀ i : Fin N, state i.succ = (state i.castSucc).refine (index i) (split i) (parent i)

namespace RefinementTrace
variable {N : ℕ}

theorem adjacent_refines (T : RefinementTrace N) (i : Fin N) :
    (T.state i.castSucc).Refines (T.state i.succ) := by
  rw [T.next]
  exact (T.state i.castSucc).refine_refines _ _ _

theorem monotone_refines (T : RefinementTrace N) (i j : Fin (N + 1)) (hij : i ≤ j) :
    (T.state i).Refines (T.state j) := by
  revert hij
  induction j using Fin.induction with
  | zero =>
    intro hij
    have hi : i = 0 := Fin.ext (by have := i.isLt; exact Nat.eq_zero_of_le_zero hij)
    subst i
    exact ActivePartition.Refines.refl _
  | succ j ih =>
    intro hij
    by_cases he : i = j.succ
    · subst i
      exact ActivePartition.Refines.refl _
    · have hle : i ≤ j.castSucc := by
        change i.val ≤ j.val
        have hv : i.val ≠ j.val + 1 := fun hv => he (Fin.ext hv)
        change i.val ≤ j.val + 1 at hij
        omega
      exact (ih hle).trans (T.adjacent_refines j)

theorem separated (T : RefinementTrace N) (i j : Fin N) (hij : i < j) :
    SplitSeparated (T.split i) (T.split j) := by
  have hr := T.monotone_refines i.succ j.castSucc (by
    change i.val + 1 ≤ j.val
    exact hij)
  rw [T.next i] at hr
  exact (T.state i.castSucc).split_separated_of_refines (T.index i) (T.split i) (T.parent i)
    (T.state j.castSucc) hr (T.index j) (T.split j) (T.parent j)

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}
  [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem haar_biorthogonal (T : RefinementTrace N) (i j : Fin N) :
    pairing ((T.split i).haarH : L 𝕜 p) ((T.split j).haarPhi : L 𝕜 q) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using (T.split i).haar_biorthogonal (𝕜 := 𝕜) (p := p) (q := q)
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact (T.split i).pairing_earlier_later (T.split j) (T.separated i j hij)
    · exact (T.split j).pairing_later_earlier (T.split i) (T.separated j i hji)

theorem average_increment (T : RefinementTrace N) (i : Fin N) :
    (T.state i.succ).averageCLM (𝕜 := 𝕜) (p := p) (q := q) - (T.state i.castSucc).averageCLM (q := q) =
      (representedFunctional ((T.split i).haarPhi : L 𝕜 q)).smulRight (T.split i).haarH := by
  rw [T.next]
  exact (T.state i.castSucc).refine_average_increment _ _ _

end RefinementTrace
end PositiveBiorthogonal
