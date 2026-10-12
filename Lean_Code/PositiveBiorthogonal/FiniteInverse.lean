import Lean_Code.PositiveBiorthogonal.Definitions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! The nonnegative inverse coefficients of `lem:inverse-coefficients`. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace PositiveBiorthogonal

/-- The zero coefficient is unused and set to zero; positive coefficients follow the TEX recurrence. -/
def inverseCoefficient (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => a (n + 1) -
      ∑ k : Fin n, inverseCoefficient a (k.val + 1) * a (n - k.val)
termination_by n => n
decreasing_by omega

theorem inverseCoefficient_recurrence (a : ℕ → ℝ) (n : ℕ) :
    inverseCoefficient a (n + 1) = a (n + 1) -
      ∑ k : Fin n, inverseCoefficient a (k.val + 1) * a (n - k.val) := by
  rw [inverseCoefficient]

theorem inverseCoefficient_convolution (a : ℕ → ℝ) (ha0 : a 0 = 1) (n : ℕ) :
    (∑ k : Fin (n + 1), inverseCoefficient a (k.val + 1) * a (n - k.val)) = a (n + 1) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, ha0, mul_one]
  rw [inverseCoefficient_recurrence]
  ring

theorem inverseCoefficient_nonneg (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (hapos : ∀ n, 0 < a n) (hratio : Monotone (fun n => a (n + 1) / a n)) :
    ∀ n, 0 ≤ inverseCoefficient a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · rw [inverseCoefficient]
    rcases n with _ | m
    · rw [inverseCoefficient_recurrence]
      simpa only [Fin.sum_univ_zero, sub_zero] using (hapos 1).le
    rw [inverseCoefficient_recurrence]
    apply sub_nonneg.mpr
    have heq : ∑ k : Fin (m + 1), inverseCoefficient a (k.val + 1) * a (m - k.val) =
        a (m + 1) := inverseCoefficient_convolution a ha0 m
    calc
      (∑ k : Fin (m + 1), inverseCoefficient a (k.val + 1) * a (m + 1 - k.val)) ≤
          ∑ k : Fin (m + 1), inverseCoefficient a (k.val + 1) *
            (a (m + 2) / a (m + 1) * a (m - k.val)) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ (ih (k.val + 1) (by omega))
        have hr := hratio (show m - k.val ≤ m + 1 by omega)
        dsimp only at hr
        have hk : m - k.val + 1 = m + 1 - k.val := by omega
        rw [hk] at hr
        exact (div_le_iff₀ (hapos (m - k.val))).mp hr
      _ = (a (m + 2) / a (m + 1)) *
          ∑ k : Fin (m + 1), inverseCoefficient a (k.val + 1) * a (m - k.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = a (m + 2) := by rw [heq, div_mul_cancel₀ _ (hapos (m + 1)).ne']

theorem inverseCoefficient_sum_le_one (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (hapos : ∀ n, 0 < a n) (hanti : Antitone a)
    (hratio : Monotone (fun n => a (n + 1) / a n)) (n : ℕ) :
    (∑ k : Fin n, inverseCoefficient a (k.val + 1)) ≤ 1 := by
  rcases n with _ | n
  · simp
  have hle : a (n + 1) * (∑ k : Fin (n + 1), inverseCoefficient a (k.val + 1)) ≤
      a (n + 1) := by
    calc
      _ ≤ ∑ k : Fin (n + 1), inverseCoefficient a (k.val + 1) * a (n - k.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k _
        rw [mul_comm (a (n + 1))]
        exact mul_le_mul_of_nonneg_left (hanti (by omega))
          (inverseCoefficient_nonneg a ha0 hapos hratio _)
      _ = a (n + 1) := inverseCoefficient_convolution a ha0 n
  nlinarith [hapos (n + 1)]

/-- The Toeplitz coefficients, with the exceptional constant coefficient explicit. -/
def toeplitzCoefficient (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => α / (n + 2)

theorem toeplitzCoefficient_pos (α : ℝ) (hα : 0 < α) (n : ℕ) :
    0 < toeplitzCoefficient α n := by
  cases n <;> simp only [toeplitzCoefficient]
  · norm_num
  · positivity

theorem toeplitzCoefficient_antitone (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Antitone (toeplitzCoefficient α) := by
  apply antitone_nat_of_succ_le
  intro n
  cases n with
  | zero => simp only [toeplitzCoefficient, Nat.cast_zero, zero_add]; linarith
  | succ n =>
    simp only [toeplitzCoefficient, Nat.cast_add, Nat.cast_one]
    apply div_le_div_of_nonneg_left hα.le (by positivity) (by linarith)

theorem toeplitzCoefficient_ratio_succ (α : ℝ) (hα : α ≠ 0) (n : ℕ) :
    toeplitzCoefficient α (n + 2) / toeplitzCoefficient α (n + 1) =
      ((n : ℝ) + 2) / (n + 3) := by
  simp only [toeplitzCoefficient, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem toeplitzCoefficient_ratio_monotone (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    Monotone (fun n => toeplitzCoefficient α (n + 1) / toeplitzCoefficient α n) := by
  apply monotone_nat_of_le_succ
  intro n
  cases n with
  | zero =>
    rw [toeplitzCoefficient_ratio_succ α hα.ne' 0]
    norm_num [toeplitzCoefficient]
    linarith
  | succ n =>
    rw [toeplitzCoefficient_ratio_succ α hα.ne' n,
      toeplitzCoefficient_ratio_succ α hα.ne' (n + 1)]
    simp only [Nat.cast_add, Nat.cast_one]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith

theorem toeplitzInverse_nonneg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    0 ≤ inverseCoefficient (toeplitzCoefficient α) n :=
  inverseCoefficient_nonneg _ rfl (toeplitzCoefficient_pos α hα)
    (toeplitzCoefficient_ratio_monotone α hα hα1) n

theorem toeplitzInverse_sum_le_one (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    (∑ k : Fin n, inverseCoefficient (toeplitzCoefficient α) (k.val + 1)) ≤ 1 :=
  inverseCoefficient_sum_le_one _ rfl (toeplitzCoefficient_pos α hα)
    (toeplitzCoefficient_antitone α hα hα1) (toeplitzCoefficient_ratio_monotone α hα hα1) n

end PositiveBiorthogonal
