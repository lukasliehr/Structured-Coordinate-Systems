import Lean_Code.SchauderTranslates.Lp.PhysicalStageLists

noncomputable section

namespace SchauderTranslates.LpConstruction

/-- Nested finite lists with an explicitly unbounded length. The nth
entry is read at the nth list; permanence proves independence of this
choice of reading stage. -/
structure PrefixListLimit (α : Type*) where
  list : ℕ → List α
  nested : ∀ {n m : ℕ}, n ≤ m → list n <+: list m
  length_gt : ∀ n, n < (list n).length

def PrefixListLimit.entry {α : Type*} (D : PrefixListLimit α) (n : ℕ) : α :=
  (D.list n)[n]'(D.length_gt n)

theorem PrefixListLimit.entry_eq {α : Type*} (D : PrefixListLimit α) (k n : ℕ)
    (hk : k < (D.list n).length) : D.entry k = (D.list n)[k] := by
  have hkn := D.nested (Nat.le_max_left k n)
  have hnn := D.nested (Nat.le_max_right k n)
  calc
    D.entry k = (D.list (max k n))[k]'((D.length_gt k).trans_le hkn.length_le) :=
      (prefix_getElem_eq hkn (D.length_gt k)).symm
    _ = (D.list n)[k] := prefix_getElem_eq hnn hk

theorem PrefixListLimit.initial_list {α : Type*} (D : PrefixListLimit α) (n : ℕ) :
    List.ofFn (fun i : Fin (D.list n).length => D.entry i.val) = D.list n := by
  have he : (fun i : Fin (D.list n).length => D.entry i.val) = fun i => (D.list n)[i.val] :=
    funext (fun i => D.entry_eq i.val n i.isLt)
  rw [he]
  exact List.ofFn_getElem

theorem PrefixListLimit.entry_mem {α : Type*} (D : PrefixListLimit α) (n : ℕ) : D.entry n ∈ D.list n :=
  List.getElem_mem (D.length_gt n)

theorem PrefixListLimit.mem_iff {α : Type*} (D : PrefixListLimit α) (n : ℕ) (x : α) :
    x ∈ D.list n ↔ ∃ k < (D.list n).length, D.entry k = x := by
  constructor
  · intro hx
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hx
    exact ⟨k, hk, (D.entry_eq k n hk).trans he⟩
  · rintro ⟨k, hk, he⟩
    exact List.mem_iff_getElem.mpr ⟨k, hk, (D.entry_eq k n hk).symm.trans he⟩

theorem PrefixListLimit.entry_property {α : Type*} (D : PrefixListLimit α) {P : α → Prop}
    (hP : ∀ n x, x ∈ D.list n → P x) (k : ℕ) : P (D.entry k) :=
  hP k (D.entry k) (D.entry_mem k)

theorem PrefixListLimit.map_entry_injective {α β : Type*} (D : PrefixListLimit α) (f : α → β)
    (hN : ∀ n, ((D.list n).map f).Nodup) : Function.Injective (fun k => f (D.entry k)) := by
  intro i j hij
  let n := max i j
  have hi : i < (D.list n).length := (D.length_gt i).trans_le (D.nested (Nat.le_max_left i j)).length_le
  have hj : j < (D.list n).length := (D.length_gt j).trans_le (D.nested (Nat.le_max_right i j)).length_le
  have hi' : i < ((D.list n).map f).length := by simpa only [List.length_map] using hi
  have hj' : j < ((D.list n).map f).length := by simpa only [List.length_map] using hj
  have he : ((D.list n).map f)[i]'hi' = ((D.list n).map f)[j]'hj' := by
    simp only [List.getElem_map]
    rw [← D.entry_eq i n hi, ← D.entry_eq j n hj]
    exact hij
  exact (hN n).getElem_inj_iff.mp he

theorem PrefixListLimit.entry_pairwise {α : Type*} (D : PrefixListLimit α) {R : α → α → Prop}
    (hR : ∀ {a b}, R a b → R b a) (hP : ∀ n, List.Pairwise R (D.list n)) :
    Pairwise (fun i j => R (D.entry i) (D.entry j)) := by
  have hlt (i j : ℕ) (hij : i < j) : R (D.entry i) (D.entry j) := by
    have hi : i < (D.list j).length := hij.trans (D.length_gt j)
    have hj : j < (D.list j).length := D.length_gt j
    have hr := (List.pairwise_iff_get.mp (hP j)) ⟨i, hi⟩ ⟨j, hj⟩ hij
    change R ((D.list j)[i]) ((D.list j)[j]) at hr
    rwa [← D.entry_eq i j hi, ← D.entry_eq j j hj] at hr
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hlt i j hij
  · exact hR (hlt j i hij)

end SchauderTranslates.LpConstruction
