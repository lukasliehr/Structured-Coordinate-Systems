import Lean_Code.SchauderTranslates.ScalarData

noncomputable section
namespace SchauderTranslates

/-- Squared norm control for every initial cut of an ordered finite family. -/
def FinitePrefixSqBound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {n : ℕ} (u : Fin n → H) (q : ℝ) : Prop :=
  ∀ (k : ℕ) (c : Fin n → ℂ),
    ‖∑ i, if i.val < k then c i • u i else 0‖ ^ 2 ≤ q * ‖∑ i, c i • u i‖ ^ 2

theorem single_prefixSqBound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (u : Fin 1 → H) : FinitePrefixSqBound u 1 := by
  intro k c
  simp only [Fin.sum_univ_one, Fin.val_zero, one_mul]
  split_ifs
  · rfl
  · simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

theorem FinitePrefixSqBound.mono {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {n : ℕ} {u : Fin n → H} {q r : ℝ} (h : FinitePrefixSqBound u q) (hqr : q ≤ r) :
    FinitePrefixSqBound u r := by
  intro k c
  exact (h k c).trans (mul_le_mul_of_nonneg_right hqr (sq_nonneg _))

theorem single_prefixSqBound_iff {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (u : Fin 1 → H) (hu : u 0 ≠ 0) (q : ℝ) : FinitePrefixSqBound u q ↔ 1 ≤ q := by
  constructor
  · intro h
    have h₁ := h 1 (fun _ => 1)
    simp only [Fin.sum_univ_one, Fin.val_zero, Nat.zero_lt_one, if_true, one_smul] at h₁
    have hn := norm_pos_iff.mpr hu
    nlinarith [sq_pos_of_pos hn]
  · exact fun hq => (single_prefixSqBound u).mono hq

/-- Centering is in the weighted probability; the common mass factor cancels in prefix bounds. -/
def ScalarData.CenteredPrefixSqBound {d n : ℕ} (s : ScalarData d n) (q : ℝ) : Prop :=
  FinitePrefixSqBound s.centeredVector q

end SchauderTranslates
