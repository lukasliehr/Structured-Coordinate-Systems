import Lean_Code.SchauderTranslates.InverseCompression

noncomputable section
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive symmetric quadratic bound controls the genuine Hilbert operator norm. -/
theorem positive_operator_norm_le (T : H →L[ℂ] H) {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    (hn : ∀ x, 0 ≤ (inner ℂ (T x) x).re)
    (hu : ∀ x, (inner ℂ (T x) x).re ≤ r * ‖x‖ ^ 2) : ‖T‖ ≤ r := by
  have hT : T.IsPositive := ⟨hs, hn⟩
  have hU : ((r : ℂ) • (1 : H →L[ℂ] H) - T).IsPositive := by
    constructor
    · intro x y
      change inner ℂ (((r : ℂ) • (1 : H →L[ℂ] H) - T) x) y =
        inner ℂ x (((r : ℂ) • (1 : H →L[ℂ] H) - T) y)
      simp only [sub_apply, smul_apply, one_apply_eq_self,
        inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal, hs]
    · intro x
      change 0 ≤ (inner ℂ (((r : ℂ) • (1 : H →L[ℂ] H) - T) x) x).re
      simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left, inner_smul_left,
        Complex.conj_ofReal, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      change 0 ≤ r * RCLike.re (inner ℂ x x) - (inner ℂ (T x) x).re
      rw [inner_self_eq_norm_sq]
      exact sub_nonneg.mpr (hu x)
  apply (CStarAlgebra.norm_le_iff_le_algebraMap T hr
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hT)).mpr
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive _).mpr hU
  change 0 ≤ algebraMap ℝ (H →L[ℂ] H) r - T at hp
  exact sub_nonneg.mp hp

omit [CompleteSpace H] in
/-- The inverse of a positive symmetric operator is positive and symmetric. -/
theorem inverse_operator_positive (B C : H →L[ℂ] H)
    (hs : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (hn : ∀ x, 0 ≤ (inner ℂ (B x) x).re)
    (hBC : ∀ x, B (C x) = x) : C.IsPositive := by
  constructor
  · intro x y
    calc
      inner ℂ (C x) y = inner ℂ (C x) (B (C y)) := by rw [hBC]
      _ = inner ℂ (B (C x)) (C y) := (hs _ _).symm
      _ = inner ℂ x (C y) := by rw [hBC]
  · intro x
    have h := hn (C x)
    rw [hBC] at h
    change 0 ≤ RCLike.re (inner ℂ x (C x)) at h
    rw [inner_re_symm] at h
    exact h

end SchauderTranslates
