import Lean_Code.SchauderTranslates.Lp.StepCellOrdering

noncomputable section
open scoped BigOperators

namespace SchauderTranslates.LpConstruction

/-- Positive masses of total one determine a genuine finite partition of
the half-open unit interval. -/
structure PositiveMassPartition (N : ℕ) where
  mass : Fin N → ℝ
  mass_pos : ∀ i, 0 < mass i
  total : ∑ i, mass i = 1

def PositiveMassPartition.endpoint {N : ℕ} (P : PositiveMassPartition N) (k : ℕ) : ℝ :=
  ∑ i : Fin N, if i.val < k then P.mass i else 0

theorem PositiveMassPartition.endpoint_zero {N : ℕ} (P : PositiveMassPartition N) :
    P.endpoint 0 = 0 := by simp [endpoint]

theorem PositiveMassPartition.endpoint_total {N : ℕ} (P : PositiveMassPartition N) :
    P.endpoint N = 1 := by simpa [endpoint] using P.total

theorem PositiveMassPartition.card_pos {N : ℕ} (P : PositiveMassPartition N) : 0 < N := by
  by_contra h
  have hN : N = 0 := by omega
  subst N
  have h := P.total
  simp at h

theorem PositiveMassPartition.endpoint_succ {N : ℕ} (P : PositiveMassPartition N)
    {k : ℕ} (hk : k < N) : P.endpoint (k + 1) = P.endpoint k + P.mass ⟨k, hk⟩ := by
  have hterm (i : Fin N) :
      (if i.val < k + 1 then P.mass i else 0) =
        (if i.val < k then P.mass i else 0) + (if i = ⟨k, hk⟩ then P.mass i else 0) := by
    by_cases hlt : i.val < k
    · have hne : i ≠ ⟨k, hk⟩ := by
        intro h
        have hv : i.val = k := congrArg Fin.val h
        omega
      simp [hlt, hne, show i.val < k + 1 by omega]
    · by_cases heq : i = ⟨k, hk⟩
      · subst i
        simp
      · have hne : i.val ≠ k := by intro h; exact heq (Fin.ext h)
        simp [hlt, heq, show ¬i.val < k + 1 by omega]
  simp_rw [endpoint, hterm]
  rw [Finset.sum_add_distrib]
  simp

theorem PositiveMassPartition.endpoint_nonneg {N : ℕ} (P : PositiveMassPartition N)
    (k : ℕ) : 0 ≤ P.endpoint k := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (P.mass_pos i).le
  · exact le_rfl

theorem PositiveMassPartition.endpoint_mono {N : ℕ} (P : PositiveMassPartition N) :
    Monotone P.endpoint := by
  intro k l hkl
  apply Finset.sum_le_sum
  intro i _
  by_cases hk : i.val < k
  · simp [hk, show i.val < l by omega]
  · simp only [hk, if_false]
    split_ifs
    · exact (P.mass_pos i).le
    · exact le_rfl

theorem PositiveMassPartition.endpoint_lt_succ {N : ℕ} (P : PositiveMassPartition N)
    {k : ℕ} (hk : k < N) : P.endpoint k < P.endpoint (k + 1) := by
  rw [P.endpoint_succ hk]
  exact lt_add_of_pos_right _ (P.mass_pos ⟨k, hk⟩)

def PositiveMassPartition.cell {N : ℕ} (P : PositiveMassPartition N) (i : Fin N) : Set ℝ :=
  Set.Ico (P.endpoint i.val) (P.endpoint (i.val + 1))

theorem PositiveMassPartition.cells_disjoint {N : ℕ} (P : PositiveMassPartition N)
    {i j : Fin N} (hij : i ≠ j) : Disjoint (P.cell i) (P.cell j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  change P.endpoint i.val ≤ x ∧ x < P.endpoint (i.val + 1) at hxi
  change P.endpoint j.val ≤ x ∧ x < P.endpoint (j.val + 1) at hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hle := P.endpoint_mono (show i.val + 1 ≤ j.val by exact h)
    linarith
  · have hle := P.endpoint_mono (show j.val + 1 ≤ i.val by exact h)
    linarith

theorem PositiveMassPartition.cell_subset_unit {N : ℕ} (P : PositiveMassPartition N)
    (i : Fin N) : P.cell i ⊆ Set.Ico (0 : ℝ) 1 := by
  intro x hx
  change P.endpoint i.val ≤ x ∧ x < P.endpoint (i.val + 1) at hx
  have hlo := P.endpoint_nonneg i.val
  have hhi := P.endpoint_mono (show i.val + 1 ≤ N from i.isLt)
  rw [P.endpoint_total] at hhi
  exact ⟨le_trans hlo hx.1, lt_of_lt_of_le hx.2 hhi⟩

theorem PositiveMassPartition.cells_cover_unit {N : ℕ} (P : PositiveMassPartition N)
    {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) : ∃ i : Fin N, x ∈ P.cell i := by
  have hex : ∃ k : ℕ, x < P.endpoint (k + 1) ∧ k < N := by
    refine ⟨N - 1, ?_, by have := P.card_pos; omega⟩
    rw [Nat.sub_add_cancel (show 1 ≤ N from P.card_pos), P.endpoint_total]
    exact hx.2
  let k := Nat.find hex
  have hk : x < P.endpoint (k + 1) ∧ k < N := Nat.find_spec hex
  refine ⟨⟨k, hk.2⟩, ?_, hk.1⟩
  change P.endpoint k ≤ x
  by_cases hk0 : k = 0
  · simpa [hk0, P.endpoint_zero] using hx.1
  · have hminimal := Nat.find_min hex (show k - 1 < k by omega)
    have hprevious : ¬x < P.endpoint k := by
      intro h
      apply hminimal
      constructor
      · simpa [Nat.sub_add_cancel (show 1 ≤ k by omega)] using h
      · omega
    exact le_of_not_gt hprevious

theorem PositiveMassPartition.cells_union {N : ℕ} (P : PositiveMassPartition N) :
    (⋃ i : Fin N, P.cell i) = Set.Ico (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i => P.cell_subset_unit i
  · intro x hx
    obtain ⟨i, hi⟩ := P.cells_cover_unit hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

end SchauderTranslates.LpConstruction
