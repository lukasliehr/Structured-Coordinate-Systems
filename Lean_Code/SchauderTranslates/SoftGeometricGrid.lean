import Lean_Code.SchauderTranslates.SelectiveGrid

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates

def softGrid (X R : ℝ) (k : ℕ) : ℝ := Real.exp (-2 * X) * R ^ k

def softGridCount (X R : ℝ) : ℕ := ⌈3 * X / (2 * Real.log R)⌉₊

theorem softGrid_pos (X : ℝ) {R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < softGrid X R k := by
  unfold softGrid
  positivity

theorem softGrid_mono (X : ℝ) {R : ℝ} (hR : 1 ≤ R) : Monotone (softGrid X R) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR hij) (Real.exp_pos _).le

@[simp] theorem softGrid_step (X R : ℝ) (k : ℕ) : softGrid X R (k + 1) = R * softGrid X R k := by
  simp only [softGrid, pow_succ]
  ring

theorem softGrid_exp (X : ℝ) {R : ℝ} (hR : 0 < R) (k : ℕ) :
    softGrid X R k = Real.exp (-2 * X + (k : ℝ) * Real.log R) := by
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hR]
  rfl

theorem softGridCount_bounds {X R : ℝ} (hX : 0 < X) (hR : 1 < R) :
    0 < softGridCount X R ∧
      3 * X / (2 * Real.log R) ≤ (softGridCount X R : ℝ) ∧
      (softGridCount X R : ℝ) ≤ 3 * X / (2 * Real.log R) + 1 := by
  have hl := Real.log_pos hR
  have hp : 0 < 3 * X / (2 * Real.log R) := by positivity
  exact ⟨Nat.one_le_ceil_iff.mpr hp, Nat.le_ceil _, (Nat.ceil_lt_add_one hp.le).le⟩

/-- The first grid point at or above the square-root scale is bounded by one further factor `R`. -/
theorem softGrid_end_bounds {X R : ℝ} (hX : 0 < X) (hR : 1 < R) :
    Real.exp (-X / 2) ≤ softGrid X R (softGridCount X R) ∧
      softGrid X R (softGridCount X R) ≤ R * Real.exp (-X / 2) := by
  have hl := Real.log_pos hR
  have h := softGridCount_bounds hX hR
  have hlow := (div_le_iff₀ (by positivity : 0 < 2 * Real.log R)).mp h.2.1
  have hhigh := mul_le_mul_of_nonneg_right h.2.2 hl.le
  have he : (3 * X / (2 * Real.log R) + 1) * Real.log R = 3 * X / 2 + Real.log R := by
    field_simp
  rw [he] at hhigh
  rw [softGrid_exp X (zero_lt_one.trans hR)]
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith
  · have hr : R * Real.exp (-X / 2) = Real.exp (Real.log R + -X / 2) := by
      rw [Real.exp_add, Real.exp_log (zero_lt_one.trans hR)]
    rw [hr]
    apply Real.exp_le_exp.mpr
    linarith

/-- The precise logarithmic margin from the blueprint implies the finite-grid drop margin. -/
theorem softGrid_gap {X R : ℝ} (hX : 0 < X) (hR : 1 < R)
    (hmargin : Real.log 4 + (17 / 16 : ℝ) * Real.log R < (5 / 32 : ℝ) * X) :
    R ^ ((softGridCount X R : ℝ) / 16) <
      Real.exp (-X / 4) / (4 * R * Real.exp (-X / 2)) := by
  have hR0 := zero_lt_one.trans hR
  have hl := Real.log_pos hR
  have hcount := (softGridCount_bounds hX hR).2.2
  have hhigh := mul_le_mul_of_nonneg_right hcount hl.le
  have he : (3 * X / (2 * Real.log R) + 1) * Real.log R = 3 * X / 2 + Real.log R := by
    field_simp
  rw [he] at hhigh
  apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos hR0 _) (by positivity)).mp
  rw [Real.log_rpow hR0, Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp,
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hR0.ne']
  nlinarith

end SchauderTranslates
