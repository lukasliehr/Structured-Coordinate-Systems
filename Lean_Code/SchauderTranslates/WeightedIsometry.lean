import Lean_Code.SchauderTranslates.Characters

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace

namespace SchauderTranslates
open Construction

abbrev LebesgueL2 := Lp ℂ 2 (volume : Measure ℝ)

theorem Construction.Weight.volume_absolutelyContinuous (w : Weight) : volume ≪ w.measure :=
  withDensity_absolutelyContinuous' w.measurable.ennreal_ofReal.aemeasurable
    (w.positive.mono (fun _ h => ENNReal.ofReal_ne_zero_iff.mpr h))

def weightRoot (w : Weight) (t : ℝ) : ℂ := (Real.sqrt (w.density t) : ℂ)

theorem weightRoot_measurable (w : Weight) : Measurable (weightRoot w) :=
  Complex.measurable_ofReal.comp w.measurable.sqrt

@[simp] theorem weightRoot_norm (w : Weight) (t : ℝ) :
    ‖weightRoot w t‖ = Real.sqrt (w.density t) := by
  simp [weightRoot, Complex.norm_real, Real.norm_eq_abs, Real.sqrt_nonneg]

theorem weightRoot_sq (w : Weight) :
    ∀ᵐ t ∂volume, ‖weightRoot w t‖ ^ 2 = (ENNReal.ofReal (w.density t)).toReal := by
  filter_upwards [w.positive] with t ht
  simp [Real.sq_sqrt ht.le, ENNReal.toReal_ofReal ht.le]

theorem weightRoot_ne_zero (w : Weight) : ∀ᵐ t ∂volume, weightRoot w t ≠ 0 := by
  filter_upwards [w.positive] with t ht
  unfold weightRoot
  exact_mod_cast (Real.sqrt_pos.mpr ht).ne'

theorem mul_weightRoot_memLp (w : Weight) (f : WeightedL2 w) :
    MemLp (fun t => weightRoot w t * f t) 2 volume := by
  have hm : AEStronglyMeasurable (fun t => weightRoot w t * f t) volume :=
    (weightRoot_measurable w).aestronglyMeasurable.mul
      (AEStronglyMeasurable.mono_ac w.volume_absolutelyContinuous (Lp.aestronglyMeasurable f))
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hi' := (integrable_withDensity_iff_integrable_smul'
    w.measurable.ennreal_ofReal (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp hi
  apply hi'.congr
  filter_upwards [weightRoot_sq w] with t ht
  simp only [smul_eq_mul, norm_mul, mul_pow, ht]

def removeWeight (w : Weight) (f : WeightedL2 w) : LebesgueL2 :=
  (mul_weightRoot_memLp w f).toLp (fun t => weightRoot w t * f t)

theorem removeWeight_ae (w : Weight) (f : WeightedL2 w) :
    (removeWeight w f : ℝ → ℂ) =ᵐ[volume] (fun t => weightRoot w t * f t) :=
  (mul_weightRoot_memLp w f).coeFn_toLp

def removeWeightLinear (w : Weight) : WeightedL2 w →ₗ[ℂ] LebesgueL2 where
  toFun := removeWeight w
  map_add' f g := by
    apply Lp.ext
    filter_upwards [removeWeight_ae w (f + g), removeWeight_ae w f, removeWeight_ae w g,
      w.ae_iff.mp (Lp.coeFn_add f g), Lp.coeFn_add (removeWeight w f) (removeWeight w g)]
      with t hfg hf hg hadd hsum
    simpa only [Pi.add_apply, hfg, hf, hg, hadd, mul_add] using hsum.symm
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [removeWeight_ae w (c • f), removeWeight_ae w f,
      w.ae_iff.mp (Lp.coeFn_smul c f), Lp.coeFn_smul c (removeWeight w f)]
      with t hcf hf hsmul hout
    simp only [RingHom.id_apply, hcf, hout, Pi.smul_apply, hsmul, hf, smul_eq_mul]
    ring

theorem l2_norm_sq_eq_integral {μ : Measure ℝ} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem removeWeight_norm (w : Weight) (f : WeightedL2 w) : ‖removeWeight w f‖ = ‖f‖ := by
  have hs : ‖removeWeight w f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [l2_norm_sq_eq_integral, l2_norm_sq_eq_integral]
    change (∫ t, ‖removeWeight w f t‖ ^ 2) =
      ∫ t, ‖f t‖ ^ 2 ∂volume.withDensity (fun t => ENNReal.ofReal (w.density t))
    rw [integral_withDensity_eq_integral_toReal_smul w.measurable.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards [removeWeight_ae w f, weightRoot_sq w] with t ht hw
    simp only [ht, norm_mul, mul_pow, hw, smul_eq_mul]
  nlinarith [norm_nonneg (removeWeight w f), norm_nonneg f]

def removeWeightIsometry (w : Weight) : WeightedL2 w →ₗᵢ[ℂ] LebesgueL2 where
  toLinearMap := removeWeightLinear w
  norm_map' := removeWeight_norm w

theorem div_weightRoot_memLp (w : Weight) (f : LebesgueL2) :
    MemLp (fun t => (weightRoot w t)⁻¹ * f t) 2 w.measure := by
  have hm₀ : AEStronglyMeasurable (fun t => (weightRoot w t)⁻¹ * f t) volume :=
    (weightRoot_measurable w).inv.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  have hm := AEStronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous volume (fun t => ENNReal.ofReal (w.density t))) hm₀
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (integrable_withDensity_iff_integrable_smul' w.measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  apply hi.congr
  filter_upwards [weightRoot_sq w, weightRoot_ne_zero w] with t hs hn
  simp only [smul_eq_mul, norm_mul, norm_inv, mul_pow, ← hs]
  field_simp

def restoreWeight (w : Weight) (f : LebesgueL2) : WeightedL2 w :=
  (div_weightRoot_memLp w f).toLp (fun t => (weightRoot w t)⁻¹ * f t)

theorem restoreWeight_ae (w : Weight) (f : LebesgueL2) :
    (restoreWeight w f : ℝ → ℂ) =ᵐ[w.measure] (fun t => (weightRoot w t)⁻¹ * f t) :=
  (div_weightRoot_memLp w f).coeFn_toLp

theorem removeWeight_restoreWeight (w : Weight) (f : LebesgueL2) :
    removeWeight w (restoreWeight w f) = f := by
  apply Lp.ext
  filter_upwards [removeWeight_ae w (restoreWeight w f),
    w.ae_iff.mp (restoreWeight_ae w f), weightRoot_ne_zero w] with t ht hi hn
  simp [ht, hi, hn]

/-- Multiplication by sqrt(w) is a complex linear isometric equivalence on full-line L². -/
def weightedL2_isometryEquiv (w : Weight) : WeightedL2 w ≃ₗᵢ[ℂ] LebesgueL2 :=
  LinearIsometryEquiv.ofSurjective (removeWeightIsometry w)
    (fun f => ⟨restoreWeight w f, removeWeight_restoreWeight w f⟩)

theorem weightedL2_isometryEquiv_ae (w : Weight) (f : WeightedL2 w) :
    (weightedL2_isometryEquiv w f : ℝ → ℂ) =ᵐ[volume]
      (fun t => weightRoot w t * f t) := removeWeight_ae w f

theorem weightedL2_isometryEquiv_character (w : Weight) (ξ : ℝ) :
    (weightedL2_isometryEquiv w (weightedCharacter w ξ) : ℝ → ℂ) =ᵐ[volume]
      (fun t => character ξ t * weightRoot w t) := by
  filter_upwards [weightedL2_isometryEquiv_ae w (weightedCharacter w ξ),
    w.ae_iff.mp (weightedCharacter_ae w ξ)] with t ht hc
  simp [ht, hc, mul_comm]

theorem weightedL2_isometryEquiv_constant (w : Weight) :
    (weightedL2_isometryEquiv w (weightedCharacter w 0) : ℝ → ℂ) =ᵐ[volume] weightRoot w := by
  simpa [character] using weightedL2_isometryEquiv_character w 0

end SchauderTranslates
