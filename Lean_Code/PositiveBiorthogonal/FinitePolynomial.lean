import Lean_Code.PositiveBiorthogonal.FiniteInverse
import Lean_Code.PositiveBiorthogonal.FiniteCoordinates
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Truncated convolution gives exact inverses at nilpotent shifts. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Polynomial ENNReal

namespace PositiveBiorthogonal

def inverseSequence (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else -inverseCoefficient a n

theorem inverseSequence_convolution (a : ℕ → ℝ) (ha0 : a 0 = 1) (n : ℕ) :
    (∑ k : Fin (n + 1), inverseSequence a k.val * a (n - k.val)) =
      if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [inverseSequence, ha0]
  | succ n =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, inverseSequence, Nat.sub_zero,
      Fin.val_succ, Nat.add_one_ne_zero, if_false, Nat.add_sub_add_right,
      neg_mul, Finset.sum_neg_distrib]
    rw [inverseCoefficient_convolution a ha0]
    simp

def truncatedPolynomial (a : ℕ → ℝ) (m : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range m, Polynomial.monomial k (a k)

theorem truncatedPolynomial_coeff (a : ℕ → ℝ) (m n : ℕ) :
    (truncatedPolynomial a m).coeff n = if n < m then a n else 0 := by
  simp [truncatedPolynomial, Polynomial.coeff_monomial]

theorem truncatedPolynomial_inverse_low_coeff (a : ℕ → ℝ) (ha0 : a 0 = 1)
    (m n : ℕ) (hn : n < m) :
    ((truncatedPolynomial (inverseSequence a) m) * truncatedPolynomial a m).coeff n =
      if n = 0 then 1 else 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range]
  have he : (∑ k : Fin (n + 1),
      (truncatedPolynomial (inverseSequence a) m).coeff k.val *
        (truncatedPolynomial a m).coeff (n - k.val)) =
      ∑ k : Fin (n + 1), inverseSequence a k.val * a (n - k.val) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [truncatedPolynomial_coeff, truncatedPolynomial_coeff,
      if_pos (show k.val < m by omega), if_pos (show n - k.val < m by omega)]
  rw [he]
  exact inverseSequence_convolution a ha0 n

theorem truncatedPolynomial_inverse_divisible (a : ℕ → ℝ) (ha0 : a 0 = 1) (m : ℕ) :
    (Polynomial.X : ℝ[X]) ^ m ∣
      truncatedPolynomial (inverseSequence a) m * truncatedPolynomial a m - 1 := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  rw [Polynomial.coeff_sub, truncatedPolynomial_inverse_low_coeff a ha0 m n hn]
  simp only [Polynomial.coeff_one]
  split_ifs <;> simp_all

theorem truncatedPolynomial_inverse_eval {A : Type*} [Ring A] [Algebra ℝ A]
    (a : ℕ → ℝ) (ha0 : a 0 = 1) (m : ℕ) (W : A) (hW : W ^ m = 0) :
    Polynomial.aeval W (truncatedPolynomial (inverseSequence a) m) *
      Polynomial.aeval W (truncatedPolynomial a m) = 1 := by
  obtain ⟨Q, hQ⟩ := truncatedPolynomial_inverse_divisible a ha0 m
  have he := congrArg (Polynomial.aeval W) hQ
  simp only [map_sub, map_mul, map_one, map_pow, Polynomial.aeval_X, hW, zero_mul] at he
  exact sub_eq_zero.mp he

theorem truncatedPolynomial_inverse_eval_right {A : Type*} [Ring A] [Algebra ℝ A]
    (a : ℕ → ℝ) (ha0 : a 0 = 1) (m : ℕ) (W : A) (hW : W ^ m = 0) :
    Polynomial.aeval W (truncatedPolynomial a m) *
      Polynomial.aeval W (truncatedPolynomial (inverseSequence a) m) = 1 := by
  rw [← map_mul, mul_comm, map_mul]
  exact truncatedPolynomial_inverse_eval a ha0 m W hW

theorem aeval_truncatedPolynomial {A : Type*} [Ring A] [Algebra ℝ A]
    (a : ℕ → ℝ) (m : ℕ) (W : A) :
    Polynomial.aeval W (truncatedPolynomial a m) = ∑ k ∈ Finset.range m, a k • W ^ k := by
  simp [truncatedPolynomial, Polynomial.aeval_monomial, Algebra.smul_def]

theorem toeplitzInverseSequence_sum_abs (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) :
    (∑ k ∈ Finset.range m, |inverseSequence (toeplitzCoefficient α) k|) ≤ 2 := by
  cases m with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ']
    have hz : inverseSequence (toeplitzCoefficient α) 0 = 1 := by simp [inverseSequence]
    rw [hz, abs_one]
    simp only [inverseSequence, Nat.add_one_ne_zero, if_false, abs_neg]
    have he : (∑ k ∈ Finset.range m, |inverseCoefficient (toeplitzCoefficient α) (k + 1)|) =
        ∑ k : Fin m, inverseCoefficient (toeplitzCoefficient α) (k.val + 1) := by
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro k _
      exact abs_of_nonneg (toeplitzInverse_nonneg α hα hα1 _)
    rw [he]
    linarith [toeplitzInverse_sum_le_one α hα hα1 m]

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

def finiteToeplitz (α : ℝ) (m : ℕ) : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m :=
  Polynomial.aeval (rightShift m) (truncatedPolynomial (toeplitzCoefficient α) m)

def finiteToeplitzInverse (α : ℝ) (m : ℕ) : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m :=
  Polynomial.aeval (rightShift m) (truncatedPolynomial (inverseSequence (toeplitzCoefficient α)) m)

theorem finiteToeplitz_inverse_left (α : ℝ) (m : ℕ) :
    finiteToeplitzInverse (𝕜 := 𝕜) (p := p) α m * finiteToeplitz α m = 1 :=
  truncatedPolynomial_inverse_eval _ rfl m _ (rightShift_nilpotent m)

theorem finiteToeplitz_inverse_right (α : ℝ) (m : ℕ) :
    finiteToeplitz (𝕜 := 𝕜) (p := p) α m * finiteToeplitzInverse α m = 1 :=
  truncatedPolynomial_inverse_eval_right _ rfl m _ (rightShift_nilpotent m)

theorem inversePolynomial_norm_le_two (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ)
    (W : FiniteLp 𝕜 p m →L[𝕜] FiniteLp 𝕜 p m) (hW : ∀ k : ℕ, ‖W ^ k‖ ≤ 1) :
    ‖Polynomial.aeval W (truncatedPolynomial (inverseSequence (toeplitzCoefficient α)) m)‖ ≤ 2 := by
  rw [aeval_truncatedPolynomial]
  calc
    ‖∑ k ∈ Finset.range m, inverseSequence (toeplitzCoefficient α) k • W ^ k‖ ≤
        ∑ k ∈ Finset.range m, ‖inverseSequence (toeplitzCoefficient α) k • W ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, |inverseSequence (toeplitzCoefficient α) k| := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul, Real.norm_eq_abs]
      simpa using mul_le_mul_of_nonneg_left (hW k) (abs_nonneg _)
    _ ≤ 2 := toeplitzInverseSequence_sum_abs α hα hα1 m

theorem finiteToeplitzInverse_norm_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) :
    ‖finiteToeplitzInverse (𝕜 := 𝕜) (p := p) α m‖ ≤ 2 :=
  inversePolynomial_norm_le_two α hα hα1 m (rightShift m) (rightShift_pow_norm_le m)

theorem finiteToeplitzInverse_opposite_norm_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (m : ℕ) :
    ‖Polynomial.aeval (leftShift (𝕜 := 𝕜) (p := p) m)
      (truncatedPolynomial (inverseSequence (toeplitzCoefficient α)) m)‖ ≤ 2 :=
  inversePolynomial_norm_le_two α hα hα1 m (leftShift m) (leftShift_pow_norm_le m)

theorem finitePolynomial_transpose_pairing {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a : ℕ → ℝ) (m : ℕ) (x : FiniteLp 𝕜 p m) (y : FiniteLp 𝕜 q m) :
    finitePairing (Polynomial.aeval (rightShift m) (truncatedPolynomial a m) x) y =
      finitePairing x (Polynomial.aeval (leftShift m) (truncatedPolynomial a m) y) := by
  rw [aeval_truncatedPolynomial, aeval_truncatedPolynomial]
  simp only [sum_apply, smul_apply,
    finitePairing_sum_left, finitePairing_sum_right,
    finitePairing_real_smul_left, finitePairing_real_smul_right, finite_shift_power_pairing]

theorem finiteToeplitz_formula (α : ℝ) (n : ℕ) :
    finiteToeplitz (𝕜 := 𝕜) (p := p) α (n + 1) =
      1 + ∑ k ∈ Finset.range n, (α / ((k : ℝ) + 2)) • (rightShift (n + 1)) ^ (k + 1) := by
  rw [finiteToeplitz, aeval_truncatedPolynomial, Finset.sum_range_succ']
  simp [toeplitzCoefficient, add_comm]

theorem finiteToeplitzInverse_formula (α : ℝ) (n : ℕ) :
    finiteToeplitzInverse (𝕜 := 𝕜) (p := p) α (n + 1) =
      1 - ∑ k ∈ Finset.range n,
        inverseCoefficient (toeplitzCoefficient α) (k + 1) • (rightShift (n + 1)) ^ (k + 1) := by
  rw [finiteToeplitzInverse, aeval_truncatedPolynomial, Finset.sum_range_succ']
  simp [inverseSequence, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg, add_comm]

end PositiveBiorthogonal
