import Lean_Code.PositiveBiorthogonal.HaarNorms

/-! Support and unitwise cancellation of the Haar pairs. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal
namespace PositiveBiorthogonal

theorem gridUnit_disjoint {a b : ℤ} (hab : a ≠ b) : Disjoint (gridUnit a).carrier (gridUnit b).carrier := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  change (a : ℝ) < x ∧ x ≤ (a : ℝ) + 1 at hx
  change (b : ℝ) < x ∧ x ≤ (b : ℝ) + 1 at hy
  rcases lt_or_gt_of_ne hab with h | h
  · have he : (a : ℝ) + 1 ≤ b := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    linarith
  · have he : (b : ℝ) + 1 ≤ a := by exact_mod_cast (Int.add_one_le_iff.mpr h)
    linarith

variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}

theorem setIntegral_of_ae_supported (A U : Set ℝ) (hU : MeasurableSet U) (hAU : A ⊆ U)
    (f : L 𝕜 p) (hf : ∀ᵐ x : ℝ, x ∉ A → f x = 0) :
    (∫ x in U, f x) = ∫ x : ℝ, f x := by
  rw [← integral_indicator hU]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  by_cases hxu : x ∈ U
  · simp [hxu]
  · have hxa : x ∉ A := fun hxa => hxu (hAU hxa)
    simp [hxu, hx hxa]

theorem setIntegral_zero_of_ae_supported (A U : Set ℝ) (hU : MeasurableSet U) (hAU : Disjoint A U)
    (f : L 𝕜 p) (hf : ∀ᵐ x : ℝ, x ∉ A → f x = 0) : (∫ x in U, f x) = 0 := by
  rw [← integral_indicator hU]
  calc
    _ = ∫ _ : ℝ, (0 : 𝕜) := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      by_cases hxu : x ∈ U
      · have hxa : x ∉ A := fun ha => Set.disjoint_left.mp hAU ha hxu
        simp [hxu, hx hxa]
      · simp [hxu]
    _ = 0 := integral_zero _ _

theorem IntervalSplit.haarH_supported (S : IntervalSplit) :
    ∀ᵐ x : ℝ, x ∉ S.parent.carrier → (S.haarH : L 𝕜 p) x = 0 := by
  filter_upwards [S.leftChild.normalizedIndicator_supported (𝕜 := 𝕜) (p := p),
    S.rightChild.normalizedIndicator_supported (𝕜 := 𝕜) (p := p),
    Lp.coeFn_sub (S.leftChild.normalizedIndicator : L 𝕜 p) S.rightChild.normalizedIndicator]
    with x hb hc hs
  intro hx
  have hb' : x ∉ S.leftChild.carrier := fun h => hx (S.left_subset h)
  have hc' : x ∉ S.rightChild.carrier := fun h => hx (S.right_subset h)
  change (S.leftChild.normalizedIndicator - S.rightChild.normalizedIndicator : L 𝕜 p) x = 0
  rw [hs, Pi.sub_apply, hb hb', hc hc', sub_self]

theorem IntervalSplit.haarPhi_supported (S : IntervalSplit) :
    ∀ᵐ x : ℝ, x ∉ S.parent.carrier → (S.haarPhi : L 𝕜 p) x = 0 := by
  rw [S.haarPhi_multiple]
  filter_upwards [S.haarH_supported (𝕜 := 𝕜) (p := p),
    Lp.coeFn_smul ((S.ratio * (1 - S.ratio) * S.parent.length : ℝ) : 𝕜) (S.haarH : L 𝕜 p)] with x hh hs
  intro hx
  rw [hs, Pi.smul_apply, hh hx, smul_zero]

theorem IntervalSplit.haarH_unit_integral (S : IntervalSplit) (n : ℤ)
    (hn : S.parent.carrier ⊆ (gridUnit n).carrier) (m : ℤ) :
    (∫ x in (gridUnit m).carrier, (S.haarH : L 𝕜 p) x) = 0 := by
  by_cases hmn : m = n
  · subst m
    rw [setIntegral_of_ae_supported _ _ (gridUnit n).measurable hn _ S.haarH_supported, S.integral_haarH]
  · exact setIntegral_zero_of_ae_supported _ _ (gridUnit m).measurable
      ((gridUnit_disjoint (Ne.symm hmn)).mono_left hn) _ S.haarH_supported

theorem IntervalSplit.haarPhi_unit_integral (S : IntervalSplit) (n : ℤ)
    (hn : S.parent.carrier ⊆ (gridUnit n).carrier) (m : ℤ) :
    (∫ x in (gridUnit m).carrier, (S.haarPhi : L 𝕜 p) x) = 0 := by
  by_cases hmn : m = n
  · subst m
    rw [setIntegral_of_ae_supported _ _ (gridUnit n).measurable hn _ S.haarPhi_supported, S.integral_haarPhi]
  · exact setIntegral_zero_of_ae_supported _ _ (gridUnit m).measurable
      ((gridUnit_disjoint (Ne.symm hmn)).mono_left hn) _ S.haarPhi_supported

end PositiveBiorthogonal
