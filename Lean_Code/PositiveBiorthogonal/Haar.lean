import Lean_Code.PositiveBiorthogonal.PartitionRefinement
import Lean_Code.PositiveBiorthogonal.StepFunctions

/-! The Haar pair attached to one strict interval split. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal BigOperators ComplexOrder
namespace PositiveBiorthogonal
namespace IntervalCell
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}

theorem indicator_integrable (D : IntervalCell) : Integrable (D.indicator : L 𝕜 p) volume :=
  integrable_indicatorConstLp D.measurable D.measure_ne_top 1

theorem integral_indicator (D : IntervalCell) : (∫ x : ℝ, (D.indicator : L 𝕜 p) x) = (D.length : 𝕜) := by
  rw [indicator, integral_indicatorConstLp, D.volume_real, RCLike.real_smul_eq_coe_mul, mul_one]

def normalizedIndicator (D : IntervalCell) : L 𝕜 p := ((D.length : 𝕜)⁻¹) • D.indicator

theorem normalizedIndicator_integrable (D : IntervalCell) :
    Integrable (D.normalizedIndicator : L 𝕜 p) volume :=
  integrable_lp_smul _ _ D.indicator_integrable

theorem integral_normalizedIndicator (D : IntervalCell) :
    (∫ x : ℝ, (D.normalizedIndicator : L 𝕜 p) x) = 1 := by
  rw [normalizedIndicator, integral_lp_smul, D.integral_indicator, inv_mul_cancel₀]
  exact_mod_cast D.length_pos.ne'

end IntervalCell
namespace IntervalSplit

def ratio (S : IntervalSplit) : ℝ := S.leftChild.length / S.parent.length

theorem ratio_pos (S : IntervalSplit) : 0 < S.ratio := div_pos S.leftChild.length_pos S.parent.length_pos

theorem ratio_lt_one (S : IntervalSplit) : S.ratio < 1 := by
  apply (div_lt_one S.parent.length_pos).mpr
  linarith [S.lengths_add, S.rightChild.length_pos]

theorem left_length_eq (S : IntervalSplit) : S.leftChild.length = S.ratio * S.parent.length := by
  rw [ratio, div_mul_cancel₀ _ S.parent.length_pos.ne']

theorem right_length_eq (S : IntervalSplit) : S.rightChild.length = (1 - S.ratio) * S.parent.length := by
  have he := S.lengths_add
  rw [S.left_length_eq] at he
  linarith

variable {𝕜 : Type*} [RCLike 𝕜] {p q : ℝ≥0∞}

theorem indicator_children (S : IntervalSplit) :
    (S.parent.indicator : L 𝕜 p) = S.leftChild.indicator + S.rightChild.indicator := by
  have h := indicatorConstLp_disjoint_union (p := p) S.leftChild.measurable S.rightChild.measurable
    S.leftChild.measure_ne_top S.rightChild.measure_ne_top S.children_disjoint (1 : 𝕜)
  simpa only [S.children_union, IntervalCell.indicator] using h

def haarH (S : IntervalSplit) : L 𝕜 p := S.leftChild.normalizedIndicator - S.rightChild.normalizedIndicator

def haarPhi (S : IntervalSplit) : L 𝕜 p := S.leftChild.indicator - (S.ratio : 𝕜) • S.parent.indicator

theorem haarH_step (S : IntervalSplit) : CompactlySupportedStep (S.haarH : L 𝕜 p) :=
  step_sub (step_smul S.leftChild.indicator_step _) (step_smul S.rightChild.indicator_step _)

theorem haarPhi_step (S : IntervalSplit) : CompactlySupportedStep (S.haarPhi : L 𝕜 p) :=
  step_sub S.leftChild.indicator_step (step_smul S.parent.indicator_step _)

theorem haarH_integrable (S : IntervalSplit) : Integrable (S.haarH : L 𝕜 p) volume := by
  apply (S.leftChild.normalizedIndicator_integrable.sub S.rightChild.normalizedIndicator_integrable).congr
  exact (Lp.coeFn_sub _ _).symm

theorem haarPhi_integrable (S : IntervalSplit) : Integrable (S.haarPhi : L 𝕜 p) volume := by
  apply (S.leftChild.indicator_integrable.sub
    (integrable_lp_smul (S.ratio : 𝕜) _ S.parent.indicator_integrable)).congr
  exact (Lp.coeFn_sub _ _).symm

theorem integral_haarH (S : IntervalSplit) : (∫ x : ℝ, (S.haarH : L 𝕜 p) x) = 0 := by
  rw [haarH, integral_lp_sub _ _ S.leftChild.normalizedIndicator_integrable S.rightChild.normalizedIndicator_integrable,
    S.leftChild.integral_normalizedIndicator, S.rightChild.integral_normalizedIndicator, sub_self]

theorem integral_haarPhi (S : IntervalSplit) : (∫ x : ℝ, (S.haarPhi : L 𝕜 p) x) = 0 := by
  rw [haarPhi, integral_lp_sub _ _ S.leftChild.indicator_integrable
    (integrable_lp_smul (S.ratio : 𝕜) _ S.parent.indicator_integrable),
    S.leftChild.integral_indicator, integral_lp_smul, S.parent.integral_indicator,
    ← RCLike.ofReal_mul, ← S.left_length_eq, sub_self]

theorem haarPhi_expansion (S : IntervalSplit) :
    (S.haarPhi : L 𝕜 p) = (1 - (S.ratio : 𝕜)) • S.leftChild.indicator -
      (S.ratio : 𝕜) • S.rightChild.indicator := by
  rw [haarPhi, S.indicator_children]
  module

theorem haarPhi_lower (S : IntervalSplit) :
    ∀ᵐ x : ℝ, -(S.ratio : 𝕜) * (S.parent.indicator : L 𝕜 p) x ≤ (S.haarPhi : L 𝕜 p) x := by
  filter_upwards [Lp.coeFn_sub (S.leftChild.indicator : L 𝕜 p) ((S.ratio : 𝕜) • S.parent.indicator),
    Lp.coeFn_smul (S.ratio : 𝕜) (S.parent.indicator : L 𝕜 p),
    S.leftChild.indicator_nonnegative (𝕜 := 𝕜) (p := p)] with x hs hm hb
  change -(S.ratio : 𝕜) * (S.parent.indicator : L 𝕜 p) x ≤
    (S.leftChild.indicator - (S.ratio : 𝕜) • S.parent.indicator : L 𝕜 p) x
  rw [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, neg_mul, le_sub_iff_add_le, neg_add_cancel]
  exact hb

theorem normalized_parent_expansion (S : IntervalSplit) :
    (S.parent.normalizedIndicator : L 𝕜 p) = (S.ratio : 𝕜) • S.leftChild.normalizedIndicator +
      (1 - (S.ratio : 𝕜)) • S.rightChild.normalizedIndicator := by
  have hbR : S.ratio * S.leftChild.length⁻¹ = S.parent.length⁻¹ := by
    rw [S.left_length_eq]
    field_simp [S.ratio_pos.ne', S.parent.length_pos.ne']
  have hcR : (1 - S.ratio) * S.rightChild.length⁻¹ = S.parent.length⁻¹ := by
    rw [S.right_length_eq]
    field_simp [(sub_pos.mpr S.ratio_lt_one).ne', S.parent.length_pos.ne']
  have hb : (S.ratio : 𝕜) * (S.leftChild.length : 𝕜)⁻¹ = (S.parent.length : 𝕜)⁻¹ := by exact_mod_cast hbR
  have hc : (1 - (S.ratio : 𝕜)) * (S.rightChild.length : 𝕜)⁻¹ = (S.parent.length : 𝕜)⁻¹ := by exact_mod_cast hcR
  rw [IntervalCell.normalizedIndicator, IntervalCell.normalizedIndicator, IntervalCell.normalizedIndicator,
    S.indicator_children, smul_add, smul_smul, smul_smul, hb, hc]

theorem normalized_left_expansion (S : IntervalSplit) :
    (S.leftChild.normalizedIndicator : L 𝕜 p) = S.parent.normalizedIndicator + (1 - (S.ratio : 𝕜)) • S.haarH := by
  rw [S.normalized_parent_expansion, haarH]
  module

theorem normalized_right_expansion (S : IntervalSplit) :
    (S.rightChild.normalizedIndicator : L 𝕜 p) = S.parent.normalizedIndicator - (S.ratio : 𝕜) • S.haarH := by
  rw [S.normalized_parent_expansion, haarH]
  module

theorem haarPhi_multiple (S : IntervalSplit) :
    (S.haarPhi : L 𝕜 p) = ((S.ratio * (1 - S.ratio) * S.parent.length : ℝ) : 𝕜) • S.haarH := by
  have hbR : (S.ratio * (1 - S.ratio) * S.parent.length) * S.leftChild.length⁻¹ = 1 - S.ratio := by
    rw [S.left_length_eq]
    field_simp [S.ratio_pos.ne', S.parent.length_pos.ne']
  have hcR : (S.ratio * (1 - S.ratio) * S.parent.length) * S.rightChild.length⁻¹ = S.ratio := by
    rw [S.right_length_eq]
    field_simp [(sub_pos.mpr S.ratio_lt_one).ne', S.parent.length_pos.ne']
  have hb : ((S.ratio * (1 - S.ratio) * S.parent.length : ℝ) : 𝕜) * (S.leftChild.length : 𝕜)⁻¹ =
      1 - (S.ratio : 𝕜) := by exact_mod_cast hbR
  have hc : ((S.ratio * (1 - S.ratio) * S.parent.length : ℝ) : 𝕜) * (S.rightChild.length : 𝕜)⁻¹ =
      (S.ratio : 𝕜) := by exact_mod_cast hcR
  rw [haarPhi_expansion, haarH, IntervalCell.normalizedIndicator, IntervalCell.normalizedIndicator,
    smul_sub, smul_smul, smul_smul, hb, hc]

theorem haarH_multiple (S : IntervalSplit) :
    (S.haarH : L 𝕜 p) = (((S.ratio * (1 - S.ratio) * S.parent.length : ℝ) : 𝕜)⁻¹) • S.haarPhi := by
  rw [haarPhi_multiple, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (mul_pos (mul_pos S.ratio_pos (sub_pos.mpr S.ratio_lt_one)) S.parent.length_pos).ne'

section Pairing
variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem pairing_haarH_left (S : IntervalSplit) :
    pairing (S.haarH : L 𝕜 p) (S.leftChild.indicator : L 𝕜 q) = 1 := by
  rw [haarH, IntervalCell.normalizedIndicator, IntervalCell.normalizedIndicator,
    ← representedFunctional_apply, map_sub, map_smul, map_smul]
  simp only [representedFunctional_apply, smul_eq_mul]
  rw [S.leftChild.pairing_indicators, S.rightChild.pairing_indicators, Set.inter_self,
    Set.disjoint_iff_inter_eq_empty.mp S.children_disjoint.symm, S.leftChild.volume_real]
  simp only [measureReal_empty, RCLike.ofReal_zero, mul_zero, sub_zero]
  apply inv_mul_cancel₀
  exact_mod_cast S.leftChild.length_pos.ne'

theorem pairing_haarH_parent (S : IntervalSplit) :
    pairing (S.haarH : L 𝕜 p) (S.parent.indicator : L 𝕜 q) = 0 := by
  rw [haarH, IntervalCell.normalizedIndicator, IntervalCell.normalizedIndicator,
    ← representedFunctional_apply, map_sub, map_smul, map_smul]
  simp only [representedFunctional_apply, smul_eq_mul]
  rw [S.leftChild.pairing_indicators, S.rightChild.pairing_indicators,
    inter_eq_left.mpr S.left_subset, inter_eq_left.mpr S.right_subset,
    S.leftChild.volume_real, S.rightChild.volume_real,
    inv_mul_cancel₀ (by exact_mod_cast S.leftChild.length_pos.ne'),
    inv_mul_cancel₀ (by exact_mod_cast S.rightChild.length_pos.ne'), sub_self]

theorem haar_biorthogonal (S : IntervalSplit) : pairing (S.haarH : L 𝕜 p) (S.haarPhi : L 𝕜 q) = 1 := by
  rw [haarPhi, ← pairingCLM_apply, map_sub, map_smul]
  simp only [pairingCLM_apply, smul_eq_mul, S.pairing_haarH_left, S.pairing_haarH_parent, mul_zero, sub_zero]

end Pairing
end IntervalSplit
end PositiveBiorthogonal
