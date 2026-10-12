import Lean_Code.SchauderTranslates.SeedBlock
import Lean_Code.SchauderTranslates.SeedSpectralLimits

noncomputable section
open Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two distinguished orthonormal columns: the carrier direction and normalized seed sum. -/
def seedPlaneInclusion (i₀ : ι) (L : ℕ) : Matrix (ι ⊕ Fin L) (Fin 2) ℂ
  | Sum.inl i, j => if i = i₀ ∧ j = 0 then 1 else 0
  | Sum.inr _, j => if j = 1 then (Real.sqrt (L : ℝ) : ℂ)⁻¹ else 0

theorem seedPlaneInclusion_carrier (i₀ : ι) (L : ℕ) (v : Fin 2 → ℂ) (i : ι) :
    (seedPlaneInclusion i₀ L *ᵥ v) (Sum.inl i) = if i = i₀ then v 0 else 0 := by
  by_cases h : i = i₀ <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, seedPlaneInclusion, h]

theorem seedPlaneInclusion_seed (i₀ : ι) (L : ℕ) (v : Fin 2 → ℂ) (i : Fin L) :
    (seedPlaneInclusion i₀ L *ᵥ v) (Sum.inr i) = (Real.sqrt (L : ℝ) : ℂ)⁻¹ * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, seedPlaneInclusion]

theorem seedPlaneInclusion_gram (i₀ : ι) {L : ℕ} (hL : 0 < L) :
    (seedPlaneInclusion i₀ L)ᴴ * seedPlaneInclusion i₀ L = 1 := by
  have hs : (Real.sqrt (L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hL : (0 : ℝ) < L)).ne'
  have hs2 : (Real.sqrt (L : ℝ) : ℂ) ^ 2 = (L : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg L)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, seedPlaneInclusion, Matrix.conjTranspose_apply,
      Complex.star_def, Matrix.one_apply, Finset.sum_ite_eq', mul_ite, ite_mul]
  field_simp
  exact hs2.symm

/-- The complex matrix of the real two-dimensional seed operator. -/
def seedComplexPlane (κ : ℝ) (L : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (seedPlane (1 - κ ^ 2) (seedCoupling κ L)).map Complex.ofReal

/-- The actual seed matrix preserves the displayed two-dimensional plane. -/
theorem seedBlock_plane (i₀ : ι) {L : ℕ} (hL : 0 < L) (κ : ℝ) :
    seedBlock i₀ L κ * seedPlaneInclusion i₀ L =
      seedPlaneInclusion i₀ L * seedComplexPlane κ L := by
  have hs : (Real.sqrt (L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hL : (0 : ℝ) < L)).ne'
  have hs2 : (Real.sqrt (L : ℝ) : ℂ) ^ 2 = (L : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg L)
  ext i j
  change (seedBlock i₀ L κ *ᵥ fun k => seedPlaneInclusion i₀ L k j) i = _
  cases i with
  | inl i =>
    rw [seedBlock_carrier_action]
    fin_cases j <;> by_cases hi : i = i₀ <;>
      simp [seedPlaneInclusion, hi, Matrix.mul_apply, Fin.sum_univ_two,
        seedComplexPlane, seedPlane, seedCoupling, Matrix.map_apply]
    push_cast
    field_simp
    rw [← hs2]
  | inr i =>
    rw [seedBlock_seed_action]
    fin_cases j <;>
      simp [seedPlaneInclusion, Matrix.mul_apply, Fin.sum_univ_two,
        seedComplexPlane, seedPlane, seedCoupling, Matrix.map_apply]
    · field_simp
    · push_cast
      field_simp
      rw [← hs2]

end SchauderTranslates
