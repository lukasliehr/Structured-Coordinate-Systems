import Lean_Code.PositiveBiorthogonal.LocalPositive

/-! Essential-supremum normalization of nonzero nonnegative interval step functions. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators ComplexOrder
namespace PositiveBiorthogonal
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem CompactlySupportedStep.memLp_top {f : L 𝕜 p} (hf : CompactlySupportedStep f) :
    MemLp (f : ℝ → 𝕜) ∞ volume := by
  obtain ⟨m, a, b, c, h⟩ := hf
  apply memLp_top_of_bound (Lp.aestronglyMeasurable f) (∑ i, ‖c i‖)
  filter_upwards [h] with x hx
  rw [hx]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : x ∈ Ioc (a i) (b i)
  · simp [hx]
  · simp [hx]

def stepSup (f : L 𝕜 p) : ℝ := (eLpNorm f ∞ volume).toReal

theorem stepSup_pos {f : L 𝕜 p} (hf : CompactlySupportedStep f) (hne : f ≠ 0) : 0 < stepSup f := by
  have hnorm : eLpNorm f ∞ volume ≠ 0 := by
    intro h
    apply hne
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    exact (eLpNorm_eq_zero_iff (Lp.aestronglyMeasurable f) (by simp : (∞ : ℝ≥0∞) ≠ 0)).mp h
  exact ENNReal.toReal_pos hnorm hf.memLp_top.2.ne

theorem stepSup_bound {f : L 𝕜 p} (hf : CompactlySupportedStep f) :
    ∀ᵐ x : ℝ, ‖f x‖ ≤ stepSup f := by
  filter_upwards [ae_le_eLpNormEssSup (f := (f : ℝ → 𝕜)) (μ := volume)] with x hx
  have h := ENNReal.toReal_mono hf.memLp_top.2.ne hx
  simpa only [stepSup, eLpNorm_exponent_top, toReal_enorm] using h

def normalizeStep (f : L 𝕜 p) : L 𝕜 p := ((stepSup f : 𝕜)⁻¹) • f

theorem normalizeStep_step {f : L 𝕜 p} (hf : CompactlySupportedStep f) :
    CompactlySupportedStep (normalizeStep f) := step_smul hf _

theorem normalizeStep_nonnegative {f : L 𝕜 p} (hf : CompactlySupportedStep f)
    (hne : f ≠ 0) (hpos : Nonnegative f) : Nonnegative (normalizeStep f) := by
  apply nonnegative_smul hpos
  rw [← RCLike.ofReal_inv]
  exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (stepSup_pos hf hne).le)

theorem normalizeStep_bounds {f : L 𝕜 p} (hf : CompactlySupportedStep f)
    (hne : f ≠ 0) (hpos : Nonnegative f) :
    ∀ᵐ x : ℝ, 0 ≤ normalizeStep f x ∧ normalizeStep f x ≤ 1 := by
  have hc := stepSup_pos hf hne
  filter_upwards [normalizeStep_nonnegative hf hne hpos, hpos, stepSup_bound hf,
    Lp.coeFn_smul ((stepSup f : 𝕜)⁻¹) f] with x hn hp hb hs
  refine ⟨hn, ?_⟩
  change (((stepSup f : 𝕜)⁻¹) • f : L 𝕜 p) x ≤ 1
  rw [hs, Pi.smul_apply, smul_eq_mul, ← RCLike.norm_of_nonneg' hp,
    ← RCLike.ofReal_inv, ← RCLike.ofReal_mul]
  have h : (stepSup f)⁻¹ * ‖f x‖ ≤ 1 := by
    simpa only [div_eq_mul_inv, mul_comm] using (div_le_one hc).mpr hb
  exact_mod_cast h

theorem normalizeStep_sup {f : L 𝕜 p} (hf : CompactlySupportedStep f) (hne : f ≠ 0) :
    eLpNorm (normalizeStep f) ∞ volume = 1 := by
  have hc := stepSup_pos hf hne
  have he : ENNReal.ofReal (stepSup f) = eLpNorm f ∞ volume := ENNReal.ofReal_toReal hf.memLp_top.2.ne
  rw [normalizeStep, eLpNorm_congr_ae (Lp.coeFn_smul ((stepSup f : 𝕜)⁻¹) f),
    eLpNorm_const_smul, ← ofReal_norm, norm_inv, RCLike.norm_ofReal, abs_of_pos hc,
    ← he, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]

end PositiveBiorthogonal
