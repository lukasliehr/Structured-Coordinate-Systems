import Mathlib

namespace SchauderTranslates

/-- One row of the Fejer difference count has either one admissible pair or none. -/
theorem fejer_difference_row (M k s : ℕ) :
    (∑ r ∈ Finset.range M, if (r : ℤ) - (s : ℤ) = (k : ℤ) then (1 : ℝ) else 0) =
      if s + k < M then 1 else 0 := by
  by_cases hsk : s + k < M
  · rw [if_pos hsk]
    rw [Finset.sum_eq_single (s + k)]
    · norm_num
    · intro r hr hne
      have he : ¬(r : ℤ) - (s : ℤ) = (k : ℤ) := by omega
      simp [he]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr hsk))
  · rw [if_neg hsk]
    apply Finset.sum_eq_zero
    intro r hr
    have he : ¬(r : ℤ) - (s : ℤ) = (k : ℤ) := by
      have hr' := Finset.mem_range.mp hr
      omega
    simp [he]

/-- The number of pairs in a finite interval with a prescribed nonnegative difference. -/
theorem fejer_difference_count_nat (M k : ℕ) :
    (∑ r ∈ Finset.range M, ∑ s ∈ Finset.range M,
      if (r : ℤ) - (s : ℤ) = (k : ℤ) then (1 : ℝ) else 0) = (M - k : ℕ) := by
  rw [Finset.sum_comm]
  simp_rw [fejer_difference_row]
  rw [← Finset.sum_filter]
  have he : (Finset.range M).filter (fun s => s + k < M) = Finset.range (M - k) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he]
  simp

/-- The triangular Fejer multiplier counts pairs of frequencies with their exact signed difference. -/
theorem fejer_difference_count (M : ℕ) (k : ℤ) :
    (∑ r ∈ Finset.range M, ∑ s ∈ Finset.range M,
      if (r : ℤ) - (s : ℤ) = k then (1 : ℝ) else 0) = (M - k.natAbs : ℕ) := by
  cases k with
  | ofNat k => exact fejer_difference_count_nat M k
  | negSucc k =>
      have he (r s : ℕ) : (r : ℤ) - (s : ℤ) = Int.negSucc k ↔
          (s : ℤ) - (r : ℤ) = ((k + 1 : ℕ) : ℤ) := by omega
      simp_rw [he]
      rw [Finset.sum_comm]
      exact fejer_difference_count_nat M (k + 1)

end SchauderTranslates
