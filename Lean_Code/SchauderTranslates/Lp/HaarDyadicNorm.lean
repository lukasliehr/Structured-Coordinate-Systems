import Lean_Code.SchauderTranslates.Lp.HaarExponentBridge
import Lean_Code.SchauderTranslates.Lp.HaarStrongConstants

noncomputable section
open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haar_dyadic_strong_norm_bound {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp1 : 1 < p) (hp2 : p < 2) (N : ℕ)
    (c : Fin (2 ^ N) → ℂ) (t : Finset HaarIndex) (w : HaarIndex → ℂ)
    (hw : ∀ i ∈ t, ‖w i‖ ≤ 1) :
    ‖haarLpMultiplier p q t w (haarDyadicStep p N c)‖ ≤
      haarStrongConstant p.toReal * ‖haarDyadicStep p N c‖ := by
  have hpfin : p ≠ ∞ := ne_top_of_lt hp2
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans hp1)
  have hs1 : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by norm_num) hpfin).mpr hp1
  have hs2 : p.toReal < 2 := by
    simpa using (ENNReal.toReal_lt_toReal hpfin (by norm_num)).mpr hp2
  have hb : ‖haarLpMultiplier p q t w (haarDyadicStep p N c)‖ ^ p.toReal ≤
      haarStrongPower p.toReal * ‖haarDyadicStep p N c‖ ^ p.toReal := by
    calc
      _ = ∫ x, ‖haarLpMultiplier p q t w (haarDyadicStep p N c) x‖ ^ p.toReal ∂haarMeasure :=
        (integral_norm_rpow _ hp0 hpfin).symm
      _ = ∫ x, ‖haarL2Multiplier t w (haarDyadicStep 2 N c) x‖ ^ p.toReal ∂haarMeasure :=
        integral_congr_ae ((haarLpMultiplier_dyadic_ae (q := q) N c t w).fun_comp
          (fun z : ℂ => ‖z‖ ^ p.toReal))
      _ ≤ haarStrongPower p.toReal * ∫ x, ‖dyadicStepValue N c x‖ ^ p.toReal ∂haarMeasure :=
        haar_dyadic_strong_power_bound N c t w hw hs1 hs2
      _ = _ := by
        congr 1
        calc
          _ = ∫ x, ‖haarDyadicStep p N c x‖ ^ p.toReal ∂haarMeasure :=
            integral_congr_ae ((haarDyadicStep_ae_value p N c).symm.fun_comp
              (fun z : ℂ => ‖z‖ ^ p.toReal))
          _ = _ := integral_norm_rpow _ hp0 hpfin
  apply (Real.rpow_le_rpow_iff (norm_nonneg _)
    (mul_nonneg (haarStrongConstant_pos hs1 hs2).le (norm_nonneg _)) (by linarith : 0 < p.toReal)).mp
  rwa [Real.mul_rpow (haarStrongConstant_pos hs1 hs2).le (norm_nonneg _),
    haarStrongConstant_rpow hs1 hs2]

end SchauderTranslates.LpConstruction
