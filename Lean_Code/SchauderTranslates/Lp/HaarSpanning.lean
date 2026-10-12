import Lean_Code.SchauderTranslates.Lp.HaarModel

noncomputable section
open scoped BigOperators ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

def haarAtomSpan (p : ℝ≥0∞) : Submodule ℂ (HaarLp p) :=
  Submodule.span ℂ (Set.range (haarAtom p))

theorem haar_child_left_recovery (p : ℝ≥0∞) (n k : ℕ) :
    haarIntervalAtom p (n + 1) (2 * k) = (1 / 2 : ℂ) •
      (haarIntervalAtom p n k + (haarScale n : ℂ)⁻¹ • haarFunction p n k) := by
  have hc : (haarScale n : ℂ) ≠ 0 := by exact_mod_cast (haarScale_pos n).ne'
  rw [haarIntervalAtom_children_sum p n k, haarFunction_eq_complex_smul p n k,
    smul_smul, inv_mul_cancel₀ hc, one_smul]
  module

theorem haar_child_right_recovery (p : ℝ≥0∞) (n k : ℕ) :
    haarIntervalAtom p (n + 1) (2 * k + 1) = (1 / 2 : ℂ) •
      (haarIntervalAtom p n k - (haarScale n : ℂ)⁻¹ • haarFunction p n k) := by
  have hc : (haarScale n : ℂ) ≠ 0 := by exact_mod_cast (haarScale_pos n).ne'
  rw [haarIntervalAtom_children_sum p n k, haarFunction_eq_complex_smul p n k,
    smul_smul, inv_mul_cancel₀ hc, one_smul]
  module

theorem haarIntervalAtom_mem_span (p : ℝ≥0∞) (n k : ℕ) (hk : k < 2 ^ n) :
    haarIntervalAtom p n k ∈ haarAtomSpan p := by
  induction n generalizing k with
  | zero =>
    have he : k = 0 := by simpa using hk
    subst k
    exact Submodule.subset_span ⟨none, rfl⟩
  | succ n ih =>
    have hparent : k / 2 < 2 ^ n := by rw [pow_succ] at hk; omega
    have hp := ih (k / 2) hparent
    have hh : haarFunction p n (k / 2) ∈ haarAtomSpan p :=
      Submodule.subset_span ⟨some ⟨n, ⟨k / 2, hparent⟩⟩, rfl⟩
    rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
    · have he : k = 2 * (k / 2) := by omega
      rw [he, haar_child_left_recovery]
      exact (haarAtomSpan p).smul_mem _ ((haarAtomSpan p).add_mem hp ((haarAtomSpan p).smul_mem _ hh))
    · have he : k = 2 * (k / 2) + 1 := by omega
      rw [he, haar_child_right_recovery]
      exact (haarAtomSpan p).smul_mem _ ((haarAtomSpan p).sub_mem hp ((haarAtomSpan p).smul_mem _ hh))

def haarDyadicStep (p : ℝ≥0∞) (n : ℕ) (c : Fin (2 ^ n) → ℂ) : HaarLp p :=
  ∑ k, c k • haarIntervalAtom p n k

/-- Every finite dyadic step function belongs to the algebraic Haar span. -/
theorem haarDyadicStep_mem_span (p : ℝ≥0∞) (n : ℕ) (c : Fin (2 ^ n) → ℂ) :
    haarDyadicStep p n c ∈ haarAtomSpan p := by
  apply Submodule.sum_mem
  intro k _
  exact (haarAtomSpan p).smul_mem _ (haarIntervalAtom_mem_span p n k k.isLt)

end SchauderTranslates.LpConstruction
