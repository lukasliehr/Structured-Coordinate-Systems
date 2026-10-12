import Lean_Code.SchauderTranslates.Lp.HaarMeanZeroBasis

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α : Type*} [MeasurableSpace α]

/-- Representative-safe copying to a finite scalar multiple of a measure. -/
def lpMeasureCopy (p : ℝ≥0∞) (μ : Measure α) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Lp ℂ p μ →ₗ[ℂ] Lp ℂ p (c • μ) where
  toFun f := ((Lp.memLp f).smul_measure hc).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).smul_measure hc),
      Lp.coeFn_add (((Lp.memLp f).smul_measure hc).toLp f)
        (((Lp.memLp g).smul_measure hc).toLp g),
      MemLp.coeFn_toLp ((Lp.memLp f).smul_measure hc),
      MemLp.coeFn_toLp ((Lp.memLp g).smul_measure hc),
      Measure.smul_absolutelyContinuous.ae_eq (Lp.coeFn_add f g)] with x hsum hadd hf hg hfg
    rw [hsum, hadd, Pi.add_apply, hf, hg, hfg, Pi.add_apply]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (a • f)).smul_measure hc),
      Lp.coeFn_smul a (((Lp.memLp f).smul_measure hc).toLp f),
      MemLp.coeFn_toLp ((Lp.memLp f).smul_measure hc),
      Measure.smul_absolutelyContinuous.ae_eq (Lp.coeFn_smul a f)] with x hsum hs hf haf
    simp only [RingHom.id_apply, hsum, hs, Pi.smul_apply, hf, haf]

theorem lpMeasureCopy_ae (p : ℝ≥0∞) (μ : Measure α) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (f : Lp ℂ p μ) : lpMeasureCopy p μ c hc f =ᵐ[c • μ] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).smul_measure hc)

theorem lpMeasureCopy_norm (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcfin : c ≠ ∞) (f : Lp ℂ p μ) :
    ‖lpMeasureCopy p μ c hcfin f‖ = c.toReal ^ p.toReal⁻¹ * ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (lpMeasureCopy_ae p μ c hcfin f),
    eLpNorm_smul_measure_of_ne_zero hc0 f p μ]
  change (c ^ (1 / p).toReal * eLpNorm f p μ).toReal = _
  simp only [ENNReal.toReal_mul, ENNReal.toReal_rpow, one_div,
    ENNReal.toReal_inv, Lp.norm_def]

/-- Multiplying copied representatives by c^(-1/p) removes precisely
the change in norm caused by multiplying the measure by c. -/
def lpMeasureScaleIsometry (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcfin : c ≠ ∞) :
    Lp ℂ p μ →ₗᵢ[ℂ] Lp ℂ p (c • μ) where
  toLinearMap := ((c.toReal ^ p.toReal⁻¹ : ℝ) : ℂ)⁻¹ • lpMeasureCopy p μ c hcfin
  norm_map' f := by
    have hK : 0 < c.toReal ^ p.toReal⁻¹ :=
      Real.rpow_pos_of_pos (ENNReal.toReal_pos hc0 hcfin) _
    simp only [LinearMap.smul_apply, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hK, lpMeasureCopy_norm p μ c hc0 hcfin]
    rw [← mul_assoc, inv_mul_cancel₀ hK.ne', one_mul]

theorem lpMeasureScaleIsometry_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcfin : c ≠ ∞) (f : Lp ℂ p μ) :
    lpMeasureScaleIsometry p μ c hc0 hcfin f =ᵐ[c • μ]
      fun x => ((c.toReal ^ p.toReal⁻¹ : ℝ) : ℂ)⁻¹ * f x := by
  filter_upwards [lpMeasureCopy_ae p μ c hcfin f,
    Lp.coeFn_smul ((c.toReal ^ p.toReal⁻¹ : ℝ) : ℂ)⁻¹ (lpMeasureCopy p μ c hcfin f)] with x hc hs
  change (((c.toReal ^ p.toReal⁻¹ : ℝ) : ℂ)⁻¹ • lpMeasureCopy p μ c hcfin f) x = _
  rw [hs, Pi.smul_apply, hc, smul_eq_mul]

theorem lpMeasureScaleIsometry_surjective (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcfin : c ≠ ∞) :
    Function.Surjective (lpMeasureScaleIsometry p μ c hc0 hcfin) := by
  intro g
  have hμ : μ ≤ c⁻¹ • (c • μ) := by
    rw [smul_smul, ENNReal.inv_mul_cancel hc0 hcfin, one_smul]
  have hg := (Lp.memLp g).of_measure_le_smul (ENNReal.inv_ne_top.mpr hc0) hμ
  let b : Lp ℂ p μ := hg.toLp g
  let K : ℂ := ((c.toReal ^ p.toReal⁻¹ : ℝ) : ℂ)
  have hK : K ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.rpow_pos_of_pos (ENNReal.toReal_pos hc0 hcfin) _).ne'
  refine ⟨K • b, ?_⟩
  apply Lp.ext
  filter_upwards [lpMeasureScaleIsometry_ae p μ c hc0 hcfin (K • b),
    Measure.smul_absolutelyContinuous.ae_eq (Lp.coeFn_smul K b),
    Measure.smul_absolutelyContinuous.ae_eq (MemLp.coeFn_toLp hg)] with x hs hb hg
  rw [hs, hb, Pi.smul_apply, hg, smul_eq_mul]
  change K⁻¹ * (K * g x) = g x
  rw [← mul_assoc, inv_mul_cancel₀ hK, one_mul]

def lpMeasureScaleEquiv (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure α)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcfin : c ≠ ∞) :
    Lp ℂ p μ ≃ₗᵢ[ℂ] Lp ℂ p (c • μ) :=
  LinearIsometryEquiv.ofSurjective (lpMeasureScaleIsometry p μ c hc0 hcfin)
    (lpMeasureScaleIsometry_surjective p μ c hc0 hcfin)

end SchauderTranslates.LpConstruction
