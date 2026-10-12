import Lean_Code.SchauderTranslates.SeedParameters
import Lean_Code.SchauderTranslates.GramGeometry

noncomputable section
open Matrix
open scoped MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

/-- The unscaled two-dimensional seed Gram. -/
def seedPlane (a s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, s; s, a + s ^ 2]

def seedDiscriminant (a s : ℝ) : ℝ := (1 - a - s ^ 2) ^ 2 + 4 * s ^ 2

def seedUpperEigenvalue (a s : ℝ) : ℝ := (1 + a + s ^ 2 + Real.sqrt (seedDiscriminant a s)) / 2

def seedLowerEigenvalue (a s : ℝ) : ℝ := a / seedUpperEigenvalue a s

@[simp] theorem seedPlane_det (a s : ℝ) : (seedPlane a s).det = a := by
  simp [seedPlane, Matrix.det_fin_two]
  ring

@[simp] theorem seedPlane_trace (a s : ℝ) : (seedPlane a s).trace = 1 + a + s ^ 2 := by
  simp [seedPlane, Matrix.trace, Fin.sum_univ_two]
  ring

theorem seedDiscriminant_pos (a : ℝ) {s : ℝ} (hs : 0 < s) : 0 < seedDiscriminant a s := by
  unfold seedDiscriminant
  positivity

theorem seedUpperEigenvalue_gt_one (a : ℝ) {s : ℝ} (hs : 0 < s) : 1 < seedUpperEigenvalue a s := by
  have hd := Real.sq_sqrt (seedDiscriminant_pos a hs).le
  have hn := Real.sqrt_nonneg (seedDiscriminant a s)
  have hs2 := sq_pos_of_pos hs
  unfold seedUpperEigenvalue seedDiscriminant at *
  nlinarith [sq_nonneg (Real.sqrt ((1 - a - s ^ 2) ^ 2 + 4 * s ^ 2) + (1 - a - s ^ 2))]

theorem seedUpperEigenvalue_equation (a : ℝ) {s : ℝ} (hs : 0 < s) :
    seedUpperEigenvalue a s ^ 2 - (1 + a + s ^ 2) * seedUpperEigenvalue a s + a = 0 := by
  have hd := Real.sq_sqrt (seedDiscriminant_pos a hs).le
  unfold seedUpperEigenvalue seedDiscriminant at *
  nlinarith

theorem seedEigenvalues_product (a : ℝ) {s : ℝ} (hs : 0 < s) :
    seedLowerEigenvalue a s * seedUpperEigenvalue a s = a := by
  have hΓ : seedUpperEigenvalue a s ≠ 0 := ne_of_gt (zero_lt_one.trans (seedUpperEigenvalue_gt_one a hs))
  exact div_mul_cancel₀ a hΓ

theorem seedEigenvalues_sum (a : ℝ) {s : ℝ} (hs : 0 < s) :
    seedLowerEigenvalue a s + seedUpperEigenvalue a s = 1 + a + s ^ 2 := by
  have hΓ := zero_lt_one.trans (seedUpperEigenvalue_gt_one a hs)
  have he := seedUpperEigenvalue_equation a hs
  unfold seedLowerEigenvalue
  field_simp [hΓ.ne']
  nlinarith

theorem seedEigenvalues_bounds {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    0 < seedLowerEigenvalue a s ∧ seedLowerEigenvalue a s < 1 ∧
      1 < seedUpperEigenvalue a s ∧ seedLowerEigenvalue a s < seedUpperEigenvalue a s := by
  have hΓ := seedUpperEigenvalue_gt_one a hs
  have hΓ0 := zero_lt_one.trans hΓ
  have hγ0 : 0 < seedLowerEigenvalue a s := div_pos ha0 hΓ0
  have hγ1 : seedLowerEigenvalue a s < 1 := (div_lt_one hΓ0).mpr (ha1.trans hΓ)
  exact ⟨hγ0, hγ1, hΓ, hγ1.trans hΓ⟩

theorem seedUpperEigenvalue_trace_bounds {a s : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hs : 0 < s) :
    (1 + a + s ^ 2) / 2 ≤ seedUpperEigenvalue a s ∧ seedUpperEigenvalue a s ≤ 1 + a + s ^ 2 := by
  have hb := seedEigenvalues_bounds ha0 ha1 hs
  have hsum := seedEigenvalues_sum a hs
  constructor <;> linarith

/-- The characteristic polynomial vanishes as a matrix identity, without invoking an eigenvalue oracle. -/
theorem seedPlane_characteristic (a s : ℝ) :
    seedPlane a s * seedPlane a s - (1 + a + s ^ 2) • seedPlane a s + a • 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [seedPlane, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply] <;> ring

/-- The off-diagonal coupling equals the product of the spectral gaps from one. -/
theorem seedEigenvalue_gap_product {a s : ℝ} (hs : 0 < s) :
    (1 - seedLowerEigenvalue a s) * (seedUpperEigenvalue a s - 1) = s ^ 2 := by
  have hp := seedEigenvalues_product a hs
  have hsum := seedEigenvalues_sum a hs
  nlinarith

end SchauderTranslates
