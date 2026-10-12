import Lean_Code.SchauderTranslates.Lp.LpDensityNorm

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α : Type*} [MeasurableSpace α]
variable (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpfin : p ≠ ∞) (μ : Measure α)
variable (w : α → ℂ) (hw : Measurable w) (hw0 : ∀ᵐ x ∂μ, w x ≠ 0)

def lpDensityMultiply : Lp ℂ p (μ.withDensity (lpPowerDensity p w)) →ₗ[ℂ] Lp ℂ p μ where
  toFun f := (memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp f)).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp (f + g))),
      Lp.coeFn_add ((memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp f)).toLp _)
        ((memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp g)),
      (lpPowerDensity_reverse_ac p hw hw0).ae_eq (Lp.coeFn_add f g)] with x hsum hadd hf hg hfg
    rw [hsum, hadd, Pi.add_apply, hf, hg]
    rw [hfg, Pi.add_apply, mul_add]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp (a • f))),
      Lp.coeFn_smul a ((memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp f)).toLp _),
      MemLp.coeFn_toLp (memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp f)),
      (lpPowerDensity_reverse_ac p hw hw0).ae_eq (Lp.coeFn_smul a f)] with x hsum hs hf haf
    simp only [RingHom.id_apply, hsum, hs, Pi.smul_apply, hf, haf, smul_eq_mul]
    ring

theorem lpDensityMultiply_ae (f : Lp ℂ p (μ.withDensity (lpPowerDensity p w))) :
    lpDensityMultiply p hp0 hpfin μ w hw hw0 f =ᵐ[μ] fun x => w x * f x :=
  MemLp.coeFn_toLp (memLp_mul_density hp0 hpfin μ hw hw0 (Lp.memLp f))

variable [Fact (1 ≤ p)]

theorem lpDensityMultiply_norm (f : Lp ℂ p (μ.withDensity (lpPowerDensity p w))) :
    ‖lpDensityMultiply p hp0 hpfin μ w hw hw0 f‖ = ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (lpDensityMultiply_ae p hp0 hpfin μ w hw hw0 f),
    eLpNorm_mul_density hp0 hpfin μ hw
      ((Lp.aestronglyMeasurable f).mono_ac (lpPowerDensity_reverse_ac p hw hw0)), Lp.norm_def]

def lpDensityIsometry : Lp ℂ p (μ.withDensity (lpPowerDensity p w)) →ₗᵢ[ℂ] Lp ℂ p μ where
  toLinearMap := lpDensityMultiply p hp0 hpfin μ w hw hw0
  norm_map' := lpDensityMultiply_norm p hp0 hpfin μ w hw hw0

include hp0 hpfin hw hw0 in
theorem memLp_inverse_density (f : Lp ℂ p μ) :
    MemLp (fun x => (w x)⁻¹ * f x) p (μ.withDensity (lpPowerDensity p w)) := by
  have hmeas : AEStronglyMeasurable (fun x => (w x)⁻¹ * f x) μ :=
    hw.fun_inv.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  refine ⟨hmeas.mono_ac (withDensity_absolutelyContinuous μ _), ?_⟩
  rw [← eLpNorm_mul_density hp0 hpfin μ hw hmeas]
  have hAE : (fun x => w x * ((w x)⁻¹ * f x)) =ᵐ[μ] f := by
    filter_upwards [hw0] with x hx
    rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]
  rw [eLpNorm_congr_ae hAE]
  exact (Lp.memLp f).eLpNorm_lt_top

theorem lpDensityIsometry_surjective : Function.Surjective (lpDensityIsometry p hp0 hpfin μ w hw hw0) := by
  intro f
  let g := (memLp_inverse_density p hp0 hpfin μ w hw hw0 f).toLp _
  refine ⟨g, ?_⟩
  apply Lp.ext
  filter_upwards [lpDensityMultiply_ae p hp0 hpfin μ w hw hw0 g,
    (lpPowerDensity_reverse_ac p hw hw0).ae_eq
      (MemLp.coeFn_toLp (memLp_inverse_density p hp0 hpfin μ w hw hw0 f)), hw0]
      with x hx hg hx0
  change lpDensityMultiply p hp0 hpfin μ w hw hw0 g x = f x
  rw [hx, hg]
  change w x * ((w x)⁻¹ * f x) = f x
  rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]

def lpDensityEquiv : Lp ℂ p (μ.withDensity (lpPowerDensity p w)) ≃ₗᵢ[ℂ] Lp ℂ p μ :=
  LinearIsometryEquiv.ofSurjective (lpDensityIsometry p hp0 hpfin μ w hw hw0)
    (lpDensityIsometry_surjective p hp0 hpfin μ w hw hw0)

theorem lpDensityEquiv_ae (f : Lp ℂ p (μ.withDensity (lpPowerDensity p w))) :
    lpDensityEquiv p hp0 hpfin μ w hw hw0 f =ᵐ[μ] fun x => w x * f x :=
  lpDensityMultiply_ae p hp0 hpfin μ w hw hw0 f

end SchauderTranslates.LpConstruction
