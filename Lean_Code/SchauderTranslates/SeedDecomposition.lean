import Lean_Code.SchauderTranslates.SeedPlaneInclusion

noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every coefficient vector splits into the carrier complement, zero-sum seeds,
and the normalized distinguished plane. The formula also gives the full operator action. -/
theorem seedBlock_invariant_decomposition (i₀ : ι) {L : ℕ} (hL : 0 < L) (κ : ℝ)
    (v : ι ⊕ Fin L → ℂ) :
    ∃ (x : ι → ℂ) (y : Fin L → ℂ) (z : Fin 2 → ℂ),
      x i₀ = 0 ∧ (∑ j, y j) = 0 ∧
      v = Sum.elim x (0 : Fin L → ℂ) + Sum.elim (0 : ι → ℂ) y + seedPlaneInclusion i₀ L *ᵥ z ∧
      seedBlock i₀ L κ *ᵥ v = Sum.elim x (0 : Fin L → ℂ) +
        (1 - (κ : ℂ) ^ 2) • Sum.elim (0 : ι → ℂ) y +
        seedPlaneInclusion i₀ L *ᵥ (seedComplexPlane κ L *ᵥ z) := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hs : (Real.sqrt (L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hL : (0 : ℝ) < L)).ne'
  have hs2 : (Real.sqrt (L : ℝ) : ℂ) ^ 2 = (L : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg L)
  let t : ℂ := ∑ j, v (Sum.inr j)
  let x : ι → ℂ := fun i => if i = i₀ then 0 else v (Sum.inl i)
  let y : Fin L → ℂ := fun j => v (Sum.inr j) - t / L
  let z : Fin 2 → ℂ := ![v (Sum.inl i₀), (Real.sqrt (L : ℝ) : ℂ)⁻¹ * t]
  have hx : x i₀ = 0 := by simp [x]
  have hy : ∑ j, y j = 0 := by
    simp only [y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change t - (L : ℂ) * (t / L) = 0
    field_simp
    ring
  have hv : v = Sum.elim x (0 : Fin L → ℂ) + Sum.elim (0 : ι → ℂ) y + seedPlaneInclusion i₀ L *ᵥ z := by
    funext i
    cases i with
    | inl i => simp [seedPlaneInclusion_carrier, x, z]; split_ifs <;> simp_all
    | inr j =>
      simp only [Pi.add_apply, Sum.elim_inr, Pi.zero_apply, zero_add, seedPlaneInclusion_seed]
      dsimp only [y, z]
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← hs2]
      field_simp
      ring
  refine ⟨x, y, z, hx, hy, hv, ?_⟩
  rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, seedBlock_carrier_perp i₀ L κ x hx,
    seedBlock_seed_perp i₀ L κ y hy, Matrix.mulVec_mulVec, seedBlock_plane i₀ hL,
    ← Matrix.mulVec_mulVec]

/-- The carrier complement and zero-sum seed space are orthogonal by disjoint support. -/
theorem seedComplement_orthogonal (x : ι → ℂ) {L : ℕ} (y : Fin L → ℂ) :
    star (Sum.elim x (0 : Fin L → ℂ)) ⬝ᵥ Sum.elim (0 : ι → ℂ) y = 0 := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem seedCarrierPerp_plane_orthogonal (i₀ : ι) (L : ℕ) {x : ι → ℂ} (hx : x i₀ = 0)
    (z : Fin 2 → ℂ) :
    star (Sum.elim x (0 : Fin L → ℂ)) ⬝ᵥ (seedPlaneInclusion i₀ L *ᵥ z) = 0 := by
  simp [dotProduct, Fintype.sum_sum_type, seedPlaneInclusion_carrier, seedPlaneInclusion_seed,
    mul_ite, hx]

theorem seedPerp_plane_orthogonal (i₀ : ι) {L : ℕ} {y : Fin L → ℂ} (hy : ∑ j, y j = 0)
    (z : Fin 2 → ℂ) :
    star (Sum.elim (0 : ι → ℂ) y) ⬝ᵥ (seedPlaneInclusion i₀ L *ᵥ z) = 0 := by
  simp only [dotProduct, Fintype.sum_sum_type, Pi.star_apply, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add, seedPlaneInclusion_seed]
  rw [← Finset.sum_mul, ← star_sum, hy, star_zero, zero_mul]

end SchauderTranslates
