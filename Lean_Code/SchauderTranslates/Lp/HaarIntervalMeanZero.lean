import Lean_Code.SchauderTranslates.Lp.HaarIntervalEquiv

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

def haarIntervalMeanZero (a l : ℝ) (hl : 0 < l) : Submodule ℂ (HaarIntervalLp p a l) :=
  (haarMeanZero p q).map (haarIntervalEquiv p a l hl).toLinearMap

theorem haarIntervalMeanZero_mem_iff (a l : ℝ) (hl : 0 < l) (g : HaarIntervalLp p a l) :
    g ∈ haarIntervalMeanZero p q a l hl ↔ (∫ x, g x ∂haarIntervalMeasure a l) = 0 := by
  change g ∈ (haarMeanZero p q).map (haarIntervalEquiv p a l hl).toLinearMap ↔ _
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨f, hf, rfl⟩
    change (∫ x, haarIntervalEquiv p a l hl f x ∂haarIntervalMeasure a l) = 0
    rw [haarIntervalEquiv_integral, (haarMeanZero_mem_iff p q f).mp hf, mul_zero]
  · intro hg
    let U := haarIntervalEquiv p a l hl
    have hi := haarIntervalEquiv_integral p a l hl (U.symm g)
    change (∫ x, U (U.symm g) x ∂haarIntervalMeasure a l) = _ at hi
    rw [U.apply_symm_apply, hg] at hi
    have hK : (((l⁻¹ ^ p.toReal⁻¹) * l : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (mul_pos (Real.rpow_pos_of_pos (inv_pos.mpr hl) _) hl).ne'
    have hf : (∫ x, U.symm g x ∂haarMeasure) = 0 :=
      (mul_eq_zero.mp hi.symm).resolve_left hK
    exact ⟨U.symm g, (haarMeanZero_mem_iff p q _).mpr hf, U.apply_symm_apply g⟩

/-- Restriction of the affine isometry to the actual integral kernels. -/
def haarIntervalMeanZeroEquiv (a l : ℝ) (hl : 0 < l) :
    haarMeanZero p q ≃ₗᵢ[ℂ] haarIntervalMeanZero p q a l hl :=
  LinearIsometryEquiv.submoduleMap (haarMeanZero p q) (haarIntervalEquiv p a l hl)

end SchauderTranslates.LpConstruction
