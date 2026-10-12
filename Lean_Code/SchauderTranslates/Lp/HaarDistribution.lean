import Lean_Code.SchauderTranslates.Lp.HaarDensity

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace SchauderTranslates.LpConstruction

/-- The layer-cake norm identity uses the actual Lᵖ norm and the same
strict level sets as the weak multiplier estimate. -/
theorem haar_norm_power_layercake {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (f : HaarLp p) :
    ENNReal.ofReal (‖f‖ ^ p.toReal) = ENNReal.ofReal p.toReal *
      ∫⁻ a in Set.Ioi (0 : ℝ), haarMeasure {x | a < ‖f x‖} * ENNReal.ofReal (a ^ (p.toReal - 1)) := by
  rw [← integral_norm_rpow f hp0 hpfin,
    ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow f hp0 hpfin)
      (Eventually.of_forall fun _ => Real.rpow_nonneg (norm_nonneg _) _)]
  exact lintegral_rpow_eq_lintegral_meas_lt_mul haarMeasure
    (Eventually.of_forall fun x => norm_nonneg (f x)) (Lp.aestronglyMeasurable f).norm.aemeasurable
    (ENNReal.toReal_pos hp0 hpfin)

theorem haar_norm_power_layercake_real {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hpfin : p ≠ ∞)
    (f : HaarLp p) :
    ‖f‖ ^ p.toReal = p.toReal *
      ∫ a in Set.Ioi (0 : ℝ), haarMeasure.real {x | a < ‖f x‖} * a ^ (p.toReal - 1) := by
  have htail : Measurable (fun a : ℝ => haarMeasure {x | a < ‖f x‖}) :=
    Antitone.measurable (fun _ _ hab => measure_mono (fun _ hx => hab.trans_lt hx))
  let kernel := fun a : ℝ => haarMeasure {x | a < ‖f x‖} * ENNReal.ofReal (a ^ (p.toReal - 1))
  have hk : AEMeasurable kernel (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (htail.mul (measurable_id.pow_const _).ennreal_ofReal).aemeasurable
  have hkfin : ∀ᵐ a ∂volume.restrict (Set.Ioi (0 : ℝ)), kernel a < ∞ :=
    Eventually.of_forall fun a => ENNReal.mul_lt_top (measure_lt_top haarMeasure _) ENNReal.ofReal_lt_top
  have h := congrArg ENNReal.toReal (haar_norm_power_layercake hp0 hpfin f)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg f) _),
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg] at h
  change ‖f‖ ^ p.toReal = p.toReal * (∫⁻ a in Set.Ioi (0 : ℝ), kernel a).toReal at h
  rw [← integral_toReal hk hkfin] at h
  refine h.trans (congrArg (fun z : ℝ => p.toReal * z) (integral_congr_ae ?_))
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with a ha
  exact ENNReal.toReal_mul.trans (congrArg (fun z => (haarMeasure {x | a < ‖f x‖}).toReal * z)
    (ENNReal.toReal_ofReal (Real.rpow_nonneg ha.le _)))

end SchauderTranslates.LpConstruction
