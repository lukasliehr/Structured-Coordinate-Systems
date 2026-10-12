import Lean_Code.SchauderTranslates.SeedMoments

noncomputable section
open MeasureTheory
namespace SchauderTranslates

/-- A uniform floor, also when the slow parameter varies. -/
theorem seedProduct_floor (L : ℕ) {a : ℂ} (ha : ‖a‖ ≤ 1 / 4)
    (z : UnitAddTorus (Fin L)) : (1 / 4 : ℝ) ^ L ≤ seedProduct L a z := by
  have h := Finset.prod_le_prod (s := Finset.univ)
    (f := fun _ : Fin L => (1 / 4 : ℝ)) (g := fun i => seedFactor a (z i))
    (fun _ _ => by norm_num) (fun i _ => (seedFactor_bounds ha (z i)).1)
  simpa only [seedProduct, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

def seedFloor (L : ℕ) (m : ℝ) : ℝ := m / (1 / 2 : ℝ) ^ L * (1 / 4 : ℝ) ^ L

theorem seedFloor_pos (L : ℕ) {m : ℝ} (hm : 0 < m) : 0 < seedFloor L m := by
  unfold seedFloor
  positivity

theorem seedKernel_uniform_bounds (L : ℕ) {m : ℝ} (hm : 0 ≤ m)
    {a : ℂ} (ha : ‖a‖ ≤ 1 / 4) (z : UnitAddTorus (Fin L)) :
    seedFloor L m ≤ seedKernel L m a z ∧ seedKernel L m a z ≤ m / (1 / 2 : ℝ) ^ L := by
  have hp : 0 ≤ m / (1 / 2 : ℝ) ^ L := by positivity
  exact ⟨mul_le_mul_of_nonneg_left (seedProduct_floor L ha z) hp,
    (mul_le_mul_of_nonneg_left (seedProduct_bounds L ha z).2 hp).trans_eq (mul_one _)⟩

@[simp] theorem seedKernel_zero_parameter (L : ℕ) (m : ℝ) (z : UnitAddTorus (Fin L)) :
    seedKernel L m 0 z = m := by
  have hp : (1 / 2 : ℝ) ^ L ≠ 0 := by positivity
  simp [seedKernel, seedProduct, seedFactor, div_mul_cancel₀ _ hp]

end SchauderTranslates
