import Lean_Code.SchauderTranslates.ActivatedScalarPrefixes

noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- Put the constant old row first, followed by the prescribed nonconstant row order. -/
def scalarRowEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by rintro (u | i); cases u; rfl; rfl
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem scalarRowEquiv_constant (n : ℕ) : scalarRowEquiv n (Sum.inl ()) = 0 := rfl
@[simp] theorem scalarRowEquiv_nonconstant {n : ℕ} (i : Fin n) :
    scalarRowEquiv n (Sum.inr i) = i.succ := rfl

/-- Sort any finite family by a finite row index. Tie-breaking is provided by a finite
enumeration of the family, so no order on its other data is needed. -/
theorem exists_finite_row_order {Q : Type*} [Fintype Q] {r : ℕ} (row : Q → Fin r) :
    ∃ e : Fin (Fintype.card Q) ≃ Q, Monotone (fun i => row (e i)) := by
  let code : Q → Fin (r * Fintype.card Q) :=
    fun q => finProdFinEquiv (row q, Fintype.equivFin Q q)
  have hcode : Function.Injective code := by
    intro q s h
    have he := finProdFinEquiv.injective h
    exact (Fintype.equivFin Q).injective (congrArg Prod.snd he)
  let : LinearOrder Q := LinearOrder.lift' code hcode
  let E : Fin (Fintype.card Q) ≃o Q := Fintype.orderIsoFinOfCardEq Q rfl
  refine ⟨E.toEquiv, ?_⟩
  intro i j hij
  have h := E.monotone hij
  change (code (E i)).val ≤ (code (E j)).val at h
  have hdiv := Nat.div_le_div_right (c := Fintype.card Q) h
  have he (q : Q) : (code q).val / Fintype.card Q = (row q).val := by
    have h := congrArg (fun p : Fin r × Fin (Fintype.card Q) => p.1.val)
      (finProdFinEquiv.symm_apply_apply (row q, Fintype.equivFin Q q))
    exact h
  rw [he, he] at hdiv
  exact hdiv

/-- An activated nonconstant list can always be ordered by old row, with the old constant
row first. The removed character is exactly the initial constant. -/
theorem exists_activation_row_order {ν : Type*} [Fintype ν] [DecidableEq ν]
    (n : ℕ) (a₀ : ν) :
    ∃ e : Fin (Fintype.card {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)}) ≃
        {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)},
      Monotone (fun i => scalarRowEquiv n (e i).1.1) :=
  exists_finite_row_order (fun q : {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)} =>
    scalarRowEquiv n q.1.1)

/-- The full old rows preceding a given old row. -/
def precedingScalarRows (n : ℕ) (j : Unit ⊕ Fin n) : Finset (Unit ⊕ Fin n) :=
  Finset.univ.filter (fun i => scalarRowEquiv n i < scalarRowEquiv n j)

@[simp] theorem mem_precedingScalarRows {n : ℕ} (i j : Unit ⊕ Fin n) :
    i ∈ precedingScalarRows n j ↔ scalarRowEquiv n i < scalarRowEquiv n j := by
  simp [precedingScalarRows]

@[simp] theorem not_mem_precedingScalarRows {n : ℕ} (j : Unit ⊕ Fin n) :
    j ∉ precedingScalarRows n j := by simp

/-- Any strict prefix of a row-ordered finite list consists of all earlier rows and a cut
inside its current row. This is the exact combinatorial interface for the activation estimate. -/
theorem row_ordered_prefix_mask {ν : Type*} [Fintype ν] [DecidableEq ν] {n m : ℕ}
    (a₀ : ν) (e : Fin m ≃ {q : (Unit ⊕ Fin n) × ν // q ≠ (Sum.inl (), a₀)})
    (he : Monotone (fun i => scalarRowEquiv n (e i).1.1)) (k : Fin m) :
    ∃ cut : Finset ν, ∀ i : Fin m,
      i < k ↔ (e i).1.1 ∈ precedingScalarRows n (e k).1.1 ∨
        ((e i).1.1 = (e k).1.1 ∧ (e i).1.2 ∈ cut) := by
  let cut := ((Finset.univ.filter (fun i : Fin m => i < k ∧ (e i).1.1 = (e k).1.1))).image
    (fun i => (e i).1.2)
  refine ⟨cut, ?_⟩
  intro i
  constructor
  · intro hik
    have hrow := he hik.le
    by_cases hlt : scalarRowEquiv n (e i).1.1 < scalarRowEquiv n (e k).1.1
    · exact Or.inl (mem_precedingScalarRows _ _ |>.mpr hlt)
    · have hr : (e i).1.1 = (e k).1.1 :=
        (scalarRowEquiv n).injective (le_antisymm hrow (le_of_not_gt hlt))
      exact Or.inr ⟨hr, Finset.mem_image.mpr ⟨i, by simp [hik, hr], rfl⟩⟩
  · rintro (hrow | ⟨hr, hcut⟩)
    · have hlt := (mem_precedingScalarRows _ _).mp hrow
      by_contra hik
      have hki := he (le_of_not_gt hik)
      exact (not_lt_of_ge hki) hlt
    · obtain ⟨j, hj, hmode⟩ := Finset.mem_image.mp hcut
      have hj' := Finset.mem_filter.mp hj |>.2
      have hji : j = i := e.injective (Subtype.ext (Prod.ext (hj'.2.trans hr.symm) hmode))
      simpa only [hji] using hj'.1

end SchauderTranslates
