import Lean_Code.SchauderTranslates.Lp.HaarMeanZeroBasis

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

theorem haarIntegral_norm_le (hp1 : 1 < p) (f : HaarLp p) : ‖haarIntegral p q f‖ ≤ ‖f‖ := by
  have hqfin : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp1).ne
  change ‖haarCoefficientMap p q none f‖ ≤ ‖f‖
  rw [← haarPairing_atom_right p q none f]
  calc
    _ ≤ ‖f‖ * ‖haarAtom q none‖ := haarPairing_norm_le p q f _
    _ = ‖f‖ := by
      change ‖f‖ * ‖haarConstant q‖ = _
      rw [norm_haarConstant q (ENNReal.HolderConjugate.ne_zero q p) hqfin, mul_one]

theorem haarIntegral_constant : haarIntegral p q (haarConstant p) = 1 := by
  change haarCoefficientMap p q none (haarAtom p none) = 1
  simp only [haarCoefficientMap_atom, ↓reduceIte]

theorem haarIntegral_norm (hp1 : 1 < p) (hpfin : p ≠ ∞) : ‖haarIntegral p q‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
      (fun f => by simpa using haarIntegral_norm_le p q hp1 f)
  · have h := (haarIntegral p q).le_opNorm (haarConstant p)
    simpa [haarIntegral_constant, norm_haarConstant p (ne_of_gt (lt_trans (by norm_num) hp1)) hpfin]
      using h

end SchauderTranslates.LpConstruction
