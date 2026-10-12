import Lean_Code.SchauderTranslates.Lp.HaarDistribution

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

theorem haar_l2_power_layercake {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (f : HaarLp 2) :
    (∫ x, ‖f x‖ ^ s ∂haarMeasure) = s *
      ∫ a in Set.Ioi (0 : ℝ), haarMeasure.real {x | a < ‖f x‖} * a ^ (s - 1) := by
  have hs0 : 0 ≤ s := le_trans zero_le_one hs1
  let : Fact (1 ≤ ENNReal.ofReal s) := ⟨ENNReal.one_le_ofReal.mpr hs1⟩
  have hp2 : ENNReal.ofReal s ≤ (2 : ℝ≥0∞) := by
    simpa using ENNReal.ofReal_le_ofReal hs2
  have hp0 : ENNReal.ofReal s ≠ 0 := by positivity
  have hpfin : ENNReal.ofReal s ≠ ∞ := ENNReal.ofReal_ne_top
  let hf := (Lp.memLp f).mono_exponent hp2
  let g := hf.toLp (f : ℝ → ℂ)
  have hgf : (g : ℝ → ℂ) =ᵐ[haarMeasure] f := MemLp.coeFn_toLp hf
  have hnorm : (∫ x, ‖g x‖ ^ s ∂haarMeasure) = ‖g‖ ^ s := by
    simpa only [ENNReal.toReal_ofReal hs0] using integral_norm_rpow g hp0 hpfin
  have hlevel (a : ℝ) : haarMeasure.real {x | a < ‖g x‖} = haarMeasure.real {x | a < ‖f x‖} := by
    apply measureReal_congr
    filter_upwards [hgf] with x hx
    change (a < ‖g x‖) = (a < ‖f x‖)
    rw [hx]
  have hlayer := haar_norm_power_layercake_real hp0 hpfin g
  simp only [ENNReal.toReal_ofReal hs0] at hlayer
  calc
    _ = ∫ x, ‖g x‖ ^ s ∂haarMeasure :=
      integral_congr_ae (hgf.symm.fun_comp (fun z : ℂ => ‖z‖ ^ s))
    _ = ‖g‖ ^ s := hnorm
    _ = _ := hlayer.trans (congrArg (fun z : ℝ => s * z) (integral_congr_ae
      (Eventually.of_forall fun a => by
        change haarMeasure.real {x | a < ‖g x‖} * a ^ (s - 1) = _
        rw [hlevel a])))

end SchauderTranslates.LpConstruction
