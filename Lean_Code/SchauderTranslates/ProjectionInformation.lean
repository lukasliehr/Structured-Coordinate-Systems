import Lean_Code.SchauderTranslates.InformationResolvent

noncomputable section
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
section Algebra
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem orthogonal_idempotents_weighted_mul {P Q : A}
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (a b c d : ℂ) :
    (a • P + b • Q) * (c • P + d • Q) = (a * c) • P + (b * d) • Q := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hP, hQ, hPQ, hQP,
    smul_zero, smul_smul, add_zero, zero_add]
  congr 1 <;> congr 1 <;> ring

/-- Solving `J = K + JK` when capture is a sum of two orthogonal projections.
The inverse is constructed in the ambient algebra, including its identity complement. -/
theorem information_of_two_projection_capture {P Q J : A}
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (a b : ℂ) (ha : 1 - a ≠ 0) (hb : 1 - b ≠ 0)
    (hJ : J = a • P + b • Q + J * (a • P + b • Q)) :
    J = (a / (1 - a)) • P + (b / (1 - b)) • Q := by
  let K : A := a • P + b • Q
  let J₀ : A := (a / (1 - a)) • P + (b / (1 - b)) • Q
  have hca : a / (1 - a) = a + (a / (1 - a)) * a := by field_simp; ring
  have hcb : b / (1 - b) = b + (b / (1 - b)) * b := by field_simp; ring
  have hJ₀ : J₀ = K + J₀ * K := by
    dsimp only [J₀, K]
    rw [orthogonal_idempotents_weighted_mul hP hQ hPQ hQP]
    calc
      _ = (a + a / (1 - a) * a) • P + (b + b / (1 - b) * b) • Q := by rw [← hca, ← hcb]
      _ = _ := by simp only [add_smul]; abel
  have hcomm : K * J₀ = J₀ * K := by
    dsimp only [J₀, K]
    rw [orthogonal_idempotents_weighted_mul hP hQ hPQ hQP,
      orthogonal_idempotents_weighted_mul hP hQ hPQ hQP]
    congr 1 <;> congr 1 <;> ring
  have hinv : (1 - K) * (1 + J₀) = 1 := by
    calc
      _ = 1 + J₀ - (K + K * J₀) := by noncomm_ring
      _ = 1 := by rw [hcomm, ← hJ₀]; abel
  have hzero : (J - J₀) * (1 - K) = 0 := by
    calc
      _ = (J - J * K) - (J₀ - J₀ * K) := by noncomm_ring
      _ = 0 := by rw [sub_eq_iff_eq_add.mpr hJ, sub_eq_iff_eq_add.mpr hJ₀, sub_self]
  apply sub_eq_zero.mp
  change J - J₀ = 0
  calc
    _ = (J - J₀) * ((1 - K) * (1 + J₀)) := by rw [hinv, mul_one]
    _ = 0 := by rw [← mul_assoc, hzero, zero_mul]

end Algebra

theorem information_coefficient_normalize (M x : ℝ) (hM : M ≠ 0) (hx : M - x ≠ 0) :
    ((x : ℂ) / (M : ℂ)) / (1 - (x : ℂ) / (M : ℂ)) = (x / (M - x) : ℝ) := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hxC : (M : ℂ) - (x : ℂ) ≠ 0 := by exact_mod_cast hx
  push_cast
  field_simp

/-- The paper's normalized coefficients follow from the ambient operator equation. -/
theorem information_of_normalized_capture {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {P Q J : H →L[ℂ] H}
    (hP : P * P = P) (hQ : Q * Q = Q) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (M x y : ℝ) (hM : 0 < M) (hx : x < M) (hy : y < M)
    (hJ : J = ((x : ℂ) / (M : ℂ)) • P + ((y : ℂ) / (M : ℂ)) • Q +
      J * (((x : ℂ) / (M : ℂ)) • P + ((y : ℂ) / (M : ℂ)) • Q)) :
    J = ((x / (M - x) : ℝ) : ℂ) • P + ((y / (M - y) : ℝ) : ℂ) • Q := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hxc : 1 - (x : ℂ) / (M : ℂ) ≠ 0 := by
    rw [sub_ne_zero, ne_eq, eq_div_iff hMC]
    intro h
    have h' : M = x := by exact_mod_cast (by simpa using h : (M : ℂ) = x)
    exact hx.ne' h'
  have hyc : 1 - (y : ℂ) / (M : ℂ) ≠ 0 := by
    rw [sub_ne_zero, ne_eq, eq_div_iff hMC]
    intro h
    have h' : M = y := by exact_mod_cast (by simpa using h : (M : ℂ) = y)
    exact hy.ne' h'
  have h := information_of_two_projection_capture hP hQ hPQ hQP _ _ hxc hyc hJ
  rw [information_coefficient_normalize M x hM.ne' (sub_pos.mpr hx).ne',
    information_coefficient_normalize M y hM.ne' (sub_pos.mpr hy).ne'] at h
  exact h

end SchauderTranslates
