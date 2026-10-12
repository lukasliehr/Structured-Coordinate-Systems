import Mathlib

/-!
# Finite unions of half-open intervals

Set-level bookkeeping for the reference construction (`Machine/Stage.lean`).

* `GapList X` : the set `X ⊆ ℝ` is a finite union of pairwise disjoint nondegenerate
  half-open intervals `[a, b)`, `a < b` (an inductive predicate, so that no lists of
  intervals have to be manipulated);
* `Removable U` : removing `U` from such a set gives such a set again;
* `gapList_Ico`, `GapList.diff_Ico`, `removable_Ico`, `Removable.union`,
  `removable_iUnion` : half-open intervals and their finite unions are removable. The
  basic step is `Ico a b \ Ico c d = Ico a (min b c) ∪ Ico (max a (max c d)) b`.
-/

open Set

namespace StructuredBases.PositiveTranslates.Machine

/-- `X` is a finite union of pairwise disjoint nondegenerate half-open intervals. -/
inductive GapList : Set ℝ → Prop
  | empty : GapList ∅
  | cons (a b : ℝ) (X : Set ℝ) : a < b → Disjoint (Ico a b) X → GapList X →
      GapList (Ico a b ∪ X)

theorem GapList.congr {X Y : Set ℝ} (h : GapList X) (hXY : X = Y) : GapList Y := hXY ▸ h

/-- Adding an interval which may be degenerate. -/
theorem GapList.ico_union {X : Set ℝ} (h : GapList X) (a b : ℝ) (hd : Disjoint (Ico a b) X) :
    GapList (Ico a b ∪ X) := by
  by_cases hab : a < b
  · exact GapList.cons a b X hab hd h
  · exact h.congr (by rw [Ico_eq_empty hab, empty_union])

theorem gapList_Ico (u w : ℝ) : GapList (Ico u w) :=
  (GapList.empty.ico_union u w (disjoint_empty _)).congr (union_empty _)

/-- The basic step: `[a, b) \ [c, d) = [a, min b c) ∪ [max a (max c d), b)`. -/
theorem Ico_diff_Ico_eq (a b c d : ℝ) :
    Ico a b \ Ico c d = Ico a (min b c) ∪ Ico (max a (max c d)) b := by
  ext x
  simp only [mem_sdiff, mem_Ico, mem_union, not_and, not_lt, lt_min_iff, max_le_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    by_cases hc : x < c
    · exact Or.inl ⟨h1, h2, hc⟩
    · exact Or.inr ⟨⟨h1, not_lt.mp hc, h3 (not_lt.mp hc)⟩, h2⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨⟨h1, -, h3⟩, h2⟩)
    · exact ⟨⟨h1, h2⟩, fun h => absurd h3 (not_lt.mpr h)⟩
    · exact ⟨⟨h1, h2⟩, fun _ => h3⟩

/-- Removing a half-open interval from a finite disjoint union of half-open intervals. -/
theorem GapList.diff_Ico {X : Set ℝ} (h : GapList X) (c d : ℝ) : GapList (X \ Ico c d) := by
  induction h with
  | empty => exact GapList.empty.congr (empty_sdiff _).symm
  | cons a b X hab hdis _ ih =>
    have hY : X \ Ico c d ⊆ X := sdiff_subset
    have hd2 : Disjoint (Ico (max a (max c d)) b) (X \ Ico c d) :=
      hdis.mono (Ico_subset_Ico_left (le_max_left _ _)) hY
    have hd1 : Disjoint (Ico a (min b c)) (Ico (max a (max c d)) b ∪ X \ Ico c d) := by
      rw [disjoint_union_right]
      constructor
      · rw [Set.disjoint_left]
        intro x hx hx'
        have h1 : x < c := lt_of_lt_of_le hx.2 (min_le_right _ _)
        have h2 : c ≤ x := (le_max_left c d).trans ((le_max_right a _).trans hx'.1)
        exact absurd h1 (not_lt.mpr h2)
      · exact hdis.mono (Ico_subset_Ico_right (min_le_left _ _)) hY
    refine ((ih.ico_union _ _ hd2).ico_union _ _ hd1).congr ?_
    rw [union_sdiff_distrib, Ico_diff_Ico_eq, union_assoc]

/-- `U` can be removed from finite disjoint unions of half-open intervals. -/
def Removable (U : Set ℝ) : Prop := ∀ X : Set ℝ, GapList X → GapList (X \ U)

theorem removable_Ico (c d : ℝ) : Removable (Ico c d) := fun _ h => h.diff_Ico c d

theorem removable_empty : Removable (∅ : Set ℝ) := fun _ h => h.congr (sdiff_empty).symm

theorem Removable.union {U V : Set ℝ} (hU : Removable U) (hV : Removable V) :
    Removable (U ∪ V) := fun X h => (hV _ (hU X h)).congr sdiff_sdiff

theorem removable_biUnion_finset {ι : Type*} (s : Finset ι) {U : ι → Set ℝ}
    (h : ∀ i ∈ s, Removable (U i)) : Removable (⋃ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using removable_empty
  | insert i s _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (Finset.mem_insert_self i s)).union
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem removable_iUnion {ι : Type*} [Finite ι] {U : ι → Set ℝ} (h : ∀ i, Removable (U i)) :
    Removable (⋃ i, U i) := by
  cases nonempty_fintype ι
  have h' := removable_biUnion_finset (Finset.univ : Finset ι) (U := U) fun i _ => h i
  simpa using h'

/-- A finite union of half-open intervals removed from a half-open interval leaves a finite
disjoint union of nondegenerate half-open intervals. -/
theorem Removable.gapList_diff {U : Set ℝ} (hU : Removable U) (u w : ℝ) :
    GapList (Ico u w \ U) := hU _ (gapList_Ico u w)

end StructuredBases.PositiveTranslates.Machine
