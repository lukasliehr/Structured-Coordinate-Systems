import Lean_Code.SchauderTranslates.GramGeometry
import Lean_Code.SchauderTranslates.PositiveOperatorNorm

noncomputable section
open Matrix ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- A two-column Hilbert bound, with the trace constant and no dimension factor. -/
theorem norm_add_sq_le_trace {E : Type*} [SeminormedAddCommGroup E]
    (u v : E) {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hu : ‖u‖ ^ 2 ≤ a * r ^ 2) (hv : ‖v‖ ^ 2 ≤ b * s ^ 2) :
    ‖u + v‖ ^ 2 ≤ (a + b) * (r ^ 2 + s ^ 2) := by
  have ha2 := Real.sq_sqrt ha
  have hb2 := Real.sq_sqrt hb
  have hu' : ‖u‖ ≤ Real.sqrt a * r :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hr)).mp (by
      simpa only [mul_pow, ha2] using hu)
  have hv' : ‖v‖ ≤ Real.sqrt b * s :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hs)).mp (by
      simpa only [mul_pow, hb2] using hv)
  calc
    _ ≤ (Real.sqrt a * r + Real.sqrt b * s) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le u v).trans (add_le_add hu' hv')) 2
    _ ≤ _ := by
      have hid : (a + b) * (r ^ 2 + s ^ 2) -
          (Real.sqrt a * r + Real.sqrt b * s) ^ 2 =
          (Real.sqrt a * s - Real.sqrt b * r) ^ 2 := by
        nlinarith [mul_nonneg ha (sq_nonneg s), mul_nonneg hb (sq_nonneg r)]
      nlinarith [sq_nonneg (Real.sqrt a * s - Real.sqrt b * r)]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def augmentedLeft (x : EuclideanSpace ℂ (Unit ⊕ ι)) : EuclideanSpace ℂ (Unit ⊕ ι) :=
  WithLp.toLp 2 (Sum.elim (fun _ => x (Sum.inl ())) (fun _ => 0))

def augmentedRight (x : EuclideanSpace ℂ (Unit ⊕ ι)) : EuclideanSpace ℂ (Unit ⊕ ι) :=
  WithLp.toLp 2 (Sum.elim (fun _ => 0) (fun i => x (Sum.inr i)))

def augmentedTail (x : EuclideanSpace ℂ (Unit ⊕ ι)) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => x (Sum.inr i))

omit [Fintype ι] [DecidableEq ι] in
theorem augmentedLeft_add_right (x : EuclideanSpace ℂ (Unit ⊕ ι)) :
    augmentedLeft x + augmentedRight x = x := by
  ext (i | i)
  · cases i; simp [augmentedLeft, augmentedRight]
  · simp [augmentedLeft, augmentedRight]

omit [DecidableEq ι] in
theorem augmented_norm_sq (x : EuclideanSpace ℂ (Unit ⊕ ι)) :
    ‖x‖ ^ 2 = ‖x (Sum.inl ())‖ ^ 2 + ‖augmentedTail x‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, augmentedTail]

theorem coefficientQuadratic_augmentedLeft (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (x : EuclideanSpace ℂ (Unit ⊕ ι)) :
    coefficientQuadratic B (augmentedLeft x) =
      (B (Sum.inl ()) (Sum.inl ())).re * ‖x (Sum.inl ())‖ ^ 2 := by
  simp only [coefficientQuadratic_eq_dot, augmentedLeft, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Pi.star_apply, Sum.elim_inl, Sum.elim_inr,
    star_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.univ_unique, Finset.sum_singleton]
  have h : star (x (Sum.inl ())) * (B (Sum.inl ()) (Sum.inl ()) * x (Sum.inl ())) =
      B (Sum.inl ()) (Sum.inl ()) * (‖x (Sum.inl ())‖ ^ 2 : ℂ) := by
    rw [← Complex.conj_mul']
    simp only [Complex.star_def]
    ring
  rw [h, ← Complex.ofReal_pow]
  simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

theorem coefficientQuadratic_augmentedRight (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (x : EuclideanSpace ℂ (Unit ⊕ ι)) :
    coefficientQuadratic B (augmentedRight x) =
      coefficientQuadratic (B.submatrix Sum.inr Sum.inr) (augmentedTail x) := by
  simp [coefficientQuadratic_eq_dot, augmentedRight, augmentedTail, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type]

/-- A positive block matrix has norm at most its scalar diagonal plus a bound for its tail.
All norms and quadratic forms are taken in Euclidean Hilbert space. -/
theorem positive_augmented_norm_le (B : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℂ)
    (hB : B.PosSemidef) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hhead : (B (Sum.inl ()) (Sum.inl ())).re ≤ a)
    (htail : ∀ v : EuclideanSpace ℂ ι,
      coefficientQuadratic (B.submatrix Sum.inr Sum.inr) v ≤ b * ‖v‖ ^ 2) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ ι)) B‖ ≤ a + b := by
  apply positive_operator_norm_le ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Unit ⊕ ι)) B)
    (add_nonneg ha hb)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB.isHermitian)
  · intro x
    change 0 ≤ RCLike.re (inner ℂ (((Matrix.toEuclideanCLM (𝕜 := ℂ)) B) x) x)
    rw [inner_re_symm]
    exact (matrix_posSemidef_iff_quadratic hB.isHermitian).mp hB x
  · intro x
    change RCLike.re (inner ℂ (((Matrix.toEuclideanCLM (𝕜 := ℂ)) B) x) x) ≤ _
    rw [inner_re_symm, ← gramRoot_norm_sq hB]
    have hleft : ‖gramRoot B (augmentedLeft x)‖ ^ 2 ≤ a * ‖x (Sum.inl ())‖ ^ 2 := by
      rw [gramRoot_norm_sq hB]
      change coefficientQuadratic B (augmentedLeft x) ≤ _
      rw [coefficientQuadratic_augmentedLeft]
      exact mul_le_mul_of_nonneg_right hhead (sq_nonneg _)
    have hright : ‖gramRoot B (augmentedRight x)‖ ^ 2 ≤ b * ‖augmentedTail x‖ ^ 2 := by
      rw [gramRoot_norm_sq hB]
      exact (coefficientQuadratic_augmentedRight B x).le.trans (htail _)
    have h := norm_add_sq_le_trace _ _ ha hb (norm_nonneg _) (norm_nonneg _) hleft hright
    rw [← map_add, augmentedLeft_add_right, ← augmented_norm_sq] at h
    exact h

end SchauderTranslates
