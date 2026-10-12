import Lean_Code.SchauderTranslates.WeightedIsometry

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped BigOperators Topology SchwartzMap InnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
open Construction

def translateL2 (a : ℝ) (f : LebesgueL2) : LebesgueL2 :=
  Lp.compMeasurePreserving (fun x : ℝ => x - a) (measurePreserving_sub_right volume a) f

theorem translateL2_ae (a : ℝ) (f : LebesgueL2) :
    (translateL2 a f : ℝ → ℂ) =ᵐ[volume] (fun t => f (t - a)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume a)

theorem continuous_translateL2 (a : ℝ) : Continuous (translateL2 a) :=
  (Lp.isometry_compMeasurePreserving (measurePreserving_sub_right volume a)).continuous

theorem character_mul_memLp (ξ : ℝ) (f : LebesgueL2) :
    MemLp (fun t => character ξ t * f t) 2 volume :=
  (Lp.memLp f).of_le ((continuous_character ξ).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable f)) (Eventually.of_forall (fun t => by simp))

def modulateL2 (ξ : ℝ) (f : LebesgueL2) : LebesgueL2 :=
  (character_mul_memLp ξ f).toLp (fun t => character ξ t * f t)

theorem modulateL2_ae (ξ : ℝ) (f : LebesgueL2) :
    (modulateL2 ξ f : ℝ → ℂ) =ᵐ[volume] (fun t => character ξ t * f t) :=
  (character_mul_memLp ξ f).coeFn_toLp

def modulateL2Linear (ξ : ℝ) : LebesgueL2 →ₗ[ℂ] LebesgueL2 where
  toFun := modulateL2 ξ
  map_add' f g := by
    apply Lp.ext
    filter_upwards [modulateL2_ae ξ (f + g), modulateL2_ae ξ f, modulateL2_ae ξ g,
      Lp.coeFn_add f g, Lp.coeFn_add (modulateL2 ξ f) (modulateL2 ξ g)]
      with t hfg hf hg hadd hsum
    simpa only [Pi.add_apply, hfg, hf, hg, hadd, mul_add] using hsum.symm
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [modulateL2_ae ξ (c • f), modulateL2_ae ξ f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (modulateL2 ξ f)] with t hcf hf hsmul hout
    simp only [RingHom.id_apply, hcf, hout, Pi.smul_apply, hsmul, hf, smul_eq_mul]
    ring

theorem modulateL2_norm (ξ : ℝ) (f : LebesgueL2) : ‖modulateL2 ξ f‖ = ‖f‖ := by
  have hs : ‖modulateL2 ξ f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [l2_norm_sq_eq_integral, l2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [modulateL2_ae ξ f] with t ht
    simp [ht]
  nlinarith [norm_nonneg (modulateL2 ξ f), norm_nonneg f]

def modulateL2Isometry (ξ : ℝ) : LebesgueL2 →ₗᵢ[ℂ] LebesgueL2 where
  toLinearMap := modulateL2Linear ξ
  norm_map' := modulateL2_norm ξ

theorem translateL2_schwartz (a : ℝ) (f : 𝓢(ℝ, ℂ)) :
    translateL2 a (f.toLp 2) = (f.compSubConstCLM ℂ a).toLp 2 := rfl

theorem fourier_function_translate (a t : ℝ) (f : ℝ → ℂ) :
    𝓕 (fun x => f (x - a)) t = character (-a) t * 𝓕 f t := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ ℝ) f (-a)) t
  have hphase : (Real.fourierChar ((innerₗ ℝ) (-a) t) : ℂ) = character (-a) t := by
    rw [Real.fourierChar_apply]
    change Complex.exp ((↑(2 * Real.pi * (t * (-a))) : ℂ) * Complex.I) = _
    unfold character
    congr 1
    push_cast
    ring
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
    (fun x => f (x - a)) t = character (-a) t *
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f t
  simpa only [Circle.smul_def, smul_eq_mul, hphase, Function.comp_def, ← sub_eq_add_neg] using h

theorem fourier_translate_schwartz (a : ℝ) (f : 𝓢(ℝ, ℂ)) :
    (Lp.fourierTransformₗᵢ ℝ ℂ) (translateL2 a (f.toLp 2)) =
      modulateL2 (-a) ((Lp.fourierTransformₗᵢ ℝ ℂ) (f.toLp 2)) := by
  change 𝓕 (translateL2 a (f.toLp 2)) = modulateL2 (-a) (𝓕 (f.toLp 2))
  rw [translateL2_schwartz, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (f.compSubConstCLM ℂ a)).coeFn_toLp 2,
    modulateL2_ae (-a) ((𝓕 f).toLp 2), (𝓕 f).coeFn_toLp 2] with t ht hm hf
  rw [ht, hm, hf]
  change 𝓕 (fun x => f (x - a)) t = character (-a) t * 𝓕 (f : ℝ → ℂ) t
  exact fourier_function_translate a t f

/-- The unitary L² Fourier transform sends g(x-a) to exp(-2πiat) times its transform. -/
theorem fourier_translate_L2 (a : ℝ) (f : LebesgueL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ) (translateL2 a f) =
      modulateL2 (-a) ((Lp.fourierTransformₗᵢ ℝ ℂ) f) := by
  refine (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ)
    (p := 2) ENNReal.ofNat_ne_top).induction_on f ?_ ?_
  · exact isClosed_eq
      ((Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (continuous_translateL2 a))
      ((modulateL2Isometry (-a)).continuous.comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous)
  · exact fourier_translate_schwartz a

theorem inverseFourier_modulate_L2 (μ : ℝ) (f : LebesgueL2) :
    (Lp.fourierTransformₗᵢ ℝ ℂ).symm (modulateL2 μ f) =
      translateL2 (-μ) ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f) := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, fourier_translate_L2, neg_neg]

end SchauderTranslates
