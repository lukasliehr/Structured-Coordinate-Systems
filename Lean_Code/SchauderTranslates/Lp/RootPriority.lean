import Lean_Code.SchauderTranslates.Lp.Contracts

noncomputable section
open scoped BigOperators

namespace SchauderTranslates.LpConstruction

def rootDiagonalStart : ℕ → ℕ
  | 0 => 0
  | n + 1 => rootDiagonalStart n + n + 1

def rootPriority (ab : ℕ × ℕ) : ℕ := rootDiagonalStart (ab.1 + ab.2) + ab.1

theorem rootDiagonalStart_double (n : ℕ) : 2 * rootDiagonalStart n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rootDiagonalStart]; nlinarith

theorem rootDiagonalStart_formula (n : ℕ) : rootDiagonalStart n = n * (n + 1) / 2 :=
  Nat.eq_div_of_mul_eq_right (by decide) (rootDiagonalStart_double n)

theorem rootDiagonalStart_mono : Monotone rootDiagonalStart := by
  apply monotone_nat_of_le_succ
  intro n
  rw [rootDiagonalStart]
  omega

theorem rootPriority_band (ab : ℕ × ℕ) :
    rootDiagonalStart (ab.1 + ab.2) ≤ rootPriority ab ∧
      rootPriority ab < rootDiagonalStart (ab.1 + ab.2 + 1) := by
  rw [rootDiagonalStart]
  unfold rootPriority
  omega

/-- The manuscript's triangular priority, with both labels shifted to
zero and the priority itself shifted to zero, is injective. -/
theorem rootPriority_injective : Function.Injective rootPriority := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hn : a + b = c + d := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hband := (rootPriority_band (a, b)).2
      have hmono := rootDiagonalStart_mono (Nat.succ_le_iff.mpr hlt)
      change rootDiagonalStart (a + b + 1) ≤ rootDiagonalStart (c + d) at hmono
      have hother := (rootPriority_band (c, d)).1
      simp only [Prod.fst, Prod.snd] at hband hother
      omega
    · have hband := (rootPriority_band (c, d)).2
      have hmono := rootDiagonalStart_mono (Nat.succ_le_iff.mpr hlt)
      change rootDiagonalStart (c + d + 1) ≤ rootDiagonalStart (a + b) at hmono
      have hother := (rootPriority_band (a, b)).1
      simp only [Prod.fst, Prod.snd] at hband hother
      omega
  change rootDiagonalStart (a + b) + a = rootDiagonalStart (c + d) + c at h
  rw [hn] at h
  have ha : a = c := Nat.add_left_cancel h
  have hb : b = d := by omega
  exact Prod.ext ha hb

theorem rootPriority_finite_initial (m : ℕ) : {ab : ℕ × ℕ | rootPriority ab < m}.Finite :=
  Set.Finite.preimage rootPriority_injective.injOn (Set.finite_lt_nat m)

theorem rootPriority_paper_formula (a b : ℕ) :
    rootPriority (a, b) + 1 = (a + b) * (a + b + 1) / 2 + (a + 1) := by
  rw [rootPriority, rootDiagonalStart_formula]
  simp only [Prod.fst, Prod.snd]
  omega

end SchauderTranslates.LpConstruction
