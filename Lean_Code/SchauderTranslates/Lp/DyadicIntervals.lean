import Lean_Code.SchauderTranslates.Lp.StepFunctions

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SchauderTranslates.LpConstruction

def dyadicEndpoint (n k : ℕ) : ℝ := (k : ℝ) / (2 : ℝ) ^ n

/-- The Haar construction uses half-open cells, including the left endpoint. -/
def dyadicInterval (n k : ℕ) : Set ℝ :=
  Set.Ico (dyadicEndpoint n k) (dyadicEndpoint n (k + 1))

theorem dyadic_denominator_pos (n : ℕ) : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _

theorem dyadicEndpoint_nonneg (n k : ℕ) : 0 ≤ dyadicEndpoint n k :=
  div_nonneg (Nat.cast_nonneg k) (dyadic_denominator_pos n).le

theorem dyadicEndpoint_mono (n : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    dyadicEndpoint n k ≤ dyadicEndpoint n l :=
  div_le_div_of_nonneg_right (Nat.cast_le.mpr hkl) (dyadic_denominator_pos n).le

theorem dyadicEndpoint_strictMono (n : ℕ) : StrictMono (dyadicEndpoint n) := by
  intro k l hkl
  exact (div_lt_div_iff_of_pos_right (dyadic_denominator_pos n)).mpr (Nat.cast_lt.mpr hkl)

theorem dyadicEndpoint_length (n k : ℕ) :
    dyadicEndpoint n (k + 1) - dyadicEndpoint n k = 1 / (2 : ℝ) ^ n := by
  simp only [dyadicEndpoint, Nat.cast_add, Nat.cast_one]
  ring

theorem dyadicEndpoint_even (n k : ℕ) : dyadicEndpoint (n + 1) (2 * k) = dyadicEndpoint n k := by
  simp only [dyadicEndpoint, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

theorem dyadicEndpoint_midpoint (n k : ℕ) :
    dyadicEndpoint (n + 1) (2 * k + 1) =
      (dyadicEndpoint n k + dyadicEndpoint n (k + 1)) / 2 := by
  simp only [dyadicEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
  field_simp
  ring

theorem dyadicEndpoint_children_right (n k : ℕ) :
    dyadicEndpoint (n + 1) (2 * k + 1 + 1) = dyadicEndpoint n (k + 1) := by
  rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, dyadicEndpoint_even]

theorem dyadicEndpoint_top (n : ℕ) : dyadicEndpoint n (2 ^ n) = 1 := by
  simp [dyadicEndpoint, Nat.cast_pow, (dyadic_denominator_pos n).ne']

theorem dyadicInterval_measurable (n k : ℕ) : MeasurableSet (dyadicInterval n k) := measurableSet_Ico

theorem dyadicInterval_subset_unit (n k : ℕ) (hk : k < 2 ^ n) :
    dyadicInterval n k ⊆ Set.Ico (0 : ℝ) 1 := by
  intro x hx
  have hright : dyadicEndpoint n (k + 1) ≤ 1 := by
    rw [← dyadicEndpoint_top n]
    exact dyadicEndpoint_mono n (by omega)
  exact ⟨(dyadicEndpoint_nonneg n k).trans hx.1, hx.2.trans_le hright⟩

@[simp] theorem dyadicInterval_zero : dyadicInterval 0 0 = Set.Ico (0 : ℝ) 1 := by
  simp [dyadicInterval, dyadicEndpoint]

theorem dyadicInterval_disjoint_same (n : ℕ) {k l : ℕ} (hkl : k ≠ l) :
    Disjoint (dyadicInterval n k) (dyadicInterval n l) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have he := dyadicEndpoint_mono n (show k + 1 ≤ l by omega)
    exact (lt_irrefl x) (hx.2.trans_le (he.trans hy.1))
  · have he := dyadicEndpoint_mono n (show l + 1 ≤ k by omega)
    exact (lt_irrefl x) (hy.2.trans_le (he.trans hx.1))

theorem dyadicInterval_children_union (n k : ℕ) :
    dyadicInterval (n + 1) (2 * k) ∪ dyadicInterval (n + 1) (2 * k + 1) = dyadicInterval n k := by
  have hleft := dyadicEndpoint_strictMono (n + 1) (show 2 * k < 2 * k + 1 by omega)
  have hright := dyadicEndpoint_strictMono (n + 1) (show 2 * k + 1 < 2 * k + 1 + 1 by omega)
  rw [dyadicEndpoint_even] at hleft
  rw [dyadicEndpoint_children_right] at hright
  ext x
  simp only [dyadicInterval, Set.mem_union, Set.mem_Ico, dyadicEndpoint_even,
    dyadicEndpoint_children_right]
  constructor
  · rintro (hx | hx) <;> constructor <;> linarith
  · intro hx
    by_cases hxm : x < dyadicEndpoint (n + 1) (2 * k + 1)
    · exact Or.inl ⟨hx.1, hxm⟩
    · exact Or.inr ⟨le_of_not_gt hxm, hx.2⟩

theorem dyadicInterval_children_disjoint (n k : ℕ) :
    Disjoint (dyadicInterval (n + 1) (2 * k)) (dyadicInterval (n + 1) (2 * k + 1)) :=
  dyadicInterval_disjoint_same _ (by omega)

theorem dyadicInterval_child_left_subset (n k : ℕ) :
    dyadicInterval (n + 1) (2 * k) ⊆ dyadicInterval n k := by
  rw [← dyadicInterval_children_union n k]
  exact Set.subset_union_left

theorem dyadicInterval_child_right_subset (n k : ℕ) :
    dyadicInterval (n + 1) (2 * k + 1) ⊆ dyadicInterval n k := by
  rw [← dyadicInterval_children_union n k]
  exact Set.subset_union_right

theorem dyadicInterval_volume (n k : ℕ) :
    volume (dyadicInterval n k) = ENNReal.ofReal (1 / (2 : ℝ) ^ n) := by
  simp only [dyadicInterval, Real.volume_Ico, dyadicEndpoint_length]

theorem dyadicInterval_parent_subset (n k : ℕ) :
    dyadicInterval (n + 1) k ⊆ dyadicInterval n (k / 2) := by
  rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
  · have he : k = 2 * (k / 2) := by omega
    calc
      dyadicInterval (n + 1) k = dyadicInterval (n + 1) (2 * (k / 2)) := by rw [← he]
      _ ⊆ dyadicInterval n (k / 2) := dyadicInterval_child_left_subset n (k / 2)
  · have he : k = 2 * (k / 2) + 1 := by omega
    calc
      dyadicInterval (n + 1) k = dyadicInterval (n + 1) (2 * (k / 2) + 1) := by rw [← he]
      _ ⊆ dyadicInterval n (k / 2) := dyadicInterval_child_right_subset n (k / 2)

theorem dyadicInterval_nested_or_disjoint {n m : ℕ} (hnm : n ≤ m) (k l : ℕ) :
    dyadicInterval m l ⊆ dyadicInterval n k ∨ Disjoint (dyadicInterval m l) (dyadicInterval n k) := by
  induction m, hnm using Nat.le_induction generalizing l with
  | base =>
    by_cases hkl : k = l
    · subst l; exact Or.inl Set.Subset.rfl
    · exact Or.inr (dyadicInterval_disjoint_same n (Ne.symm hkl))
  | succ m hnm ih =>
    have hs := dyadicInterval_parent_subset m l
    rcases ih (l / 2) with hi | hi
    · exact Or.inl (hs.trans hi)
    · exact Or.inr (hi.mono_left hs)

theorem dyadicInterval_unit_cover (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ∃ k : ℕ, k < 2 ^ n ∧ x ∈ dyadicInterval n k := by
  induction n with
  | zero => exact ⟨0, by norm_num, by simpa using hx⟩
  | succ n ih =>
    obtain ⟨k, hk, hxi⟩ := ih
    rw [← dyadicInterval_children_union n k] at hxi
    rcases hxi with hl | hr
    · exact ⟨2 * k, by rw [pow_succ]; omega, hl⟩
    · exact ⟨2 * k + 1, by rw [pow_succ]; omega, hr⟩

end SchauderTranslates.LpConstruction
