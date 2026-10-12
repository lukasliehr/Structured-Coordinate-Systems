import Lean_Code.SchauderTranslates.Lp.SignAverages

noncomputable section
open scoped BigOperators ENNReal

namespace SchauderTranslates.LpConstruction

theorem signed_sum_coefficients {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℕ → E) (c : ℕ → ℂ) (n : ℕ) {v : E}
    (hv : v ∈ signedSums (fun j => c j • f j) n) :
    ∃ ε : ℕ → ℂ, (∀ j, ‖ε j‖ ≤ 1) ∧ v = ∑ j ∈ Finset.range n, (ε j * c j) • f j := by
  induction n generalizing v with
  | zero =>
    have hv0 : v = 0 := by simpa [signedSums] using hv
    exact ⟨fun _ => 0, by simp, by simp [hv0]⟩
  | succ n ih =>
    rcases Multiset.mem_add.mp hv with ha | hs
    · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp ha
      obtain ⟨ε, hε, he⟩ := ih hw
      refine ⟨Function.update ε n 1, ?_, ?_⟩
      · intro j
        by_cases hj : j = n
        · simp [hj]
        · simpa [Function.update_of_ne hj] using hε j
      · rw [Finset.sum_range_succ]
        have hsum : (∑ j ∈ Finset.range n, (Function.update ε n 1 j * c j) • f j) =
            ∑ j ∈ Finset.range n, (ε j * c j) • f j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Function.update_of_ne (ne_of_lt (Finset.mem_range.mp hj))]
        rw [hsum, Function.update_self, one_mul, ← he]
    · obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hs
      obtain ⟨ε, hε, he⟩ := ih hw
      refine ⟨Function.update ε n (-1), ?_, ?_⟩
      · intro j
        by_cases hj : j = n
        · simp [hj]
        · simpa [Function.update_of_ne hj] using hε j
      · rw [Finset.sum_range_succ]
        have hsum : (∑ j ∈ Finset.range n, (Function.update ε n (-1) j * c j) • f j) =
            ∑ j ∈ Finset.range n, (ε j * c j) • f j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Function.update_of_ne (ne_of_lt (Finset.mem_range.mp hj))]
        rw [hsum, Function.update_self, neg_one_mul, neg_smul, ← he, sub_eq_add_neg]

theorem multiset_norm_power_sum_le {E : Type*} [NormedAddCommGroup E] {P C : ℝ}
    (hP : 0 ≤ P) (s : Multiset E) (hbound : ∀ v ∈ s, ‖v‖ ≤ C) :
    (s.map (fun v => ‖v‖ ^ P)).sum ≤ (s.card : ℝ) * C ^ P := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons v s ih =>
    have hv := hbound v (Multiset.mem_cons_self _ _)
    have hs : ∀ w ∈ s, ‖w‖ ≤ C := fun w hw => hbound w (Multiset.mem_cons_of_mem hw)
    have hi := ih hs
    have hpw := Real.rpow_le_rpow (norm_nonneg v) hv hP
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- Finite coefficient estimate from a common bound for every signed partial sum. -/
theorem finite_root_coefficient_bound {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p) (hpfin : p ≠ ∞)
    (f : ℕ → LebesgueLp p) (hf : ∀ j, ‖f j‖ = 1) (c : ℕ → ℂ) (n : ℕ) {C : ℝ}
    (hsign : ∀ ε : ℕ → ℂ, (∀ j, ‖ε j‖ ≤ 1) →
      ‖∑ j ∈ Finset.range n, (ε j * c j) • f j‖ ≤ C) :
    (∑ j ∈ Finset.range n, ‖c j‖ ^ p.toReal) ≤ C ^ p.toReal := by
  have hpR := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hpfin
  have hlo := lp_signed_sum_power_lower hp hpfin (fun j => c j • f j) n
  simp only [norm_smul, hf, mul_one] at hlo
  have hbound : ∀ v ∈ signedSums (fun j => c j • f j) n, ‖v‖ ≤ C := by
    intro v hv
    obtain ⟨ε, hε, he⟩ := signed_sum_coefficients f c n hv
    rw [he]
    exact hsign ε hε
  have hhi := multiset_norm_power_sum_le hpR.le _ hbound
  rw [signedSums_card, Nat.cast_pow, Nat.cast_ofNat] at hhi
  exact (mul_le_mul_iff_right₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)).mp (hlo.trans hhi)

end SchauderTranslates.LpConstruction
