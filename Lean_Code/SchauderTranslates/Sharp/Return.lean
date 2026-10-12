import Lean_Code.SchauderTranslates.MainReduction
import Lean_Code.SchauderTranslates.Sharp.Contracts
import Lean_Code.Basis.Transport
import Lean_Code.Basis.RealScalars

/-!
# Returning to translates (sharp `L²` construction)

This file consumes the contract `SchauderTranslates.Sharp.WeightedExponentialBasisSharp C`
(an even weight `w` below the Gaussian `exp (-π t²)` and an injective frequency sequence
`μ` whose weighted characters form a Schauder basis of `L²(w)` with all finite prefix
inequalities bounded by `C`) and returns a Schauder basis of translates of `L²(ℝ)`
(paper: "Returning to translates", proof of the translate theorems for `p = 2`).

* `Return.fourierInv_toLp_ae`: on `L¹ ∩ L²` the unitary `L²` inverse Fourier transform
  agrees a.e. with the inverse Fourier integral. It is proved by testing against Schwartz
  functions: the `L²` transform agrees with the transform of tempered distributions
  (`MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq`), and the inverse Fourier integral
  is self-adjoint by Fubini (`VectorFourier.integral_bilin_fourierIntegral_eq_flip`).
* `Return.differentiable_fourierLaplace`: the Fourier–Laplace transform
  `z ↦ ∫ ρ(t) e^{2π i z t} dt` of a density with Gaussian decay is entire. This is Mathlib's
  holomorphy of the complex moment generating function
  (`ProbabilityTheory.differentiableOn_complexMGF`) for the measure with density `ρ`.
* `Return.generatorExt w` is the entire function `z ↦ ∫ √w(t) e^{2π i z t} dt` and
  `Return.generator w` its restriction to the real line, which is real-valued (and even)
  when `w` is even.
* `Return.returnIsometry w` is the unitary `L²(w) → L²(ℝ)`, multiplication by `√w`
  followed by the inverse Fourier transform. It sends the character with frequency `ξ` to the
  translate by `-ξ` of the generator.
* `translates_of_weightedExponentialBasisSharp`: the main statement.
-/

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped BigOperators Topology SchwartzMap ContDiff ComplexConjugate

namespace SchauderTranslates.Sharp
open SchauderTranslates Construction

namespace Return

/-! ### The `L²` inverse Fourier transform on `L¹ ∩ L²` -/

/-- The inverse Fourier integral of an integrable function is continuous. -/
theorem continuous_fourierInv_of_integrable {h : ℝ → ℂ} (h1 : Integrable h volume) :
    Continuous (𝓕⁻ h) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (continuous_inner.neg) h1

/-- For a function in `L¹ ∩ L²`, the `L²` inverse Fourier transform agrees almost everywhere
with the inverse Fourier integral. -/
theorem fourierInv_toLp_ae {h : ℝ → ℂ} (h1 : Integrable h volume) (h2 : MemLp h 2 volume) :
    ((Lp.fourierTransformₗᵢ ℝ ℂ).symm (h2.toLp h) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ h := by
  set H : Lp ℂ 2 (volume : Measure ℝ) := h2.toLp h with hH
  have hloc1 : LocallyIntegrable ((Lp.fourierTransformₗᵢ ℝ ℂ).symm H : ℝ → ℂ) volume :=
    (Lp.memLp _).locallyIntegrable (by norm_num)
  have hloc2 : LocallyIntegrable (𝓕⁻ h) volume :=
    (continuous_fourierInv_of_integrable h1).locallyIntegrable
  -- it suffices to test against smooth compactly supported real functions `φ`
  refine ae_eq_of_integral_contDiff_smul_eq hloc1 hloc2 fun φ φ_smooth φ_cpt => ?_
  have hφ₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := φ_cpt.comp_left rfl
  have hφ₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
  set ψ : 𝓢(ℝ, ℂ) := hφ₁.toSchwartzMap hφ₂ with hψdef
  have hψ : ∀ x, ψ x = (φ x : ℂ) := fun x => rfl
  have e1 : ∫ x, φ x • ((Lp.fourierTransformₗᵢ ℝ ℂ).symm H : ℝ → ℂ) x =
      ∫ x, ψ x • ((Lp.fourierTransformₗᵢ ℝ ℂ).symm H : ℝ → ℂ) x := by
    simp [hψ]
  have e2 : ∫ x, ψ x • ((Lp.fourierTransformₗᵢ ℝ ℂ).symm H : ℝ → ℂ) x =
      Lp.toTemperedDistribution ((Lp.fourierTransformₗᵢ ℝ ℂ).symm H) ψ :=
    (Lp.toTemperedDistribution_apply _ _).symm
  -- the `L²` transform is the transform of tempered distributions
  have e3 : Lp.toTemperedDistribution ((Lp.fourierTransformₗᵢ ℝ ℂ).symm H) ψ =
      Lp.toTemperedDistribution H (𝓕⁻ ψ) :=
    (congrArg (fun T : 𝓢'(ℝ, ℂ) => T ψ) (Lp.fourierInv_toTemperedDistribution_eq H)).symm
  have e4 : Lp.toTemperedDistribution H (𝓕⁻ ψ) = ∫ t, (𝓕⁻ ψ) t • H t :=
    Lp.toTemperedDistribution_apply _ _
  have e5 : ∫ t, (𝓕⁻ ψ) t • H t = ∫ t, (𝓕⁻ (ψ : ℝ → ℂ)) t • h t := by
    apply integral_congr_ae
    filter_upwards [h2.coeFn_toLp] with t ht
    rw [hH, ht, SchwartzMap.fourierInv_coe]
  -- Fubini: the inverse Fourier integral is self-adjoint
  have e6 : ∫ t, (𝓕⁻ (ψ : ℝ → ℂ)) t • h t = ∫ x, ψ x • (𝓕⁻ h) x := by
    have hflip : (-innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = -innerₗ ℝ := by
      ext
      simp
    have h6 := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.lsmul ℂ ℂ) (L := -innerₗ ℝ) (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) Real.continuous_fourierChar continuous_inner.neg
      ψ.integrable h1
    rw [hflip] at h6
    exact h6
  have e7 : ∫ x, ψ x • (𝓕⁻ h) x = ∫ x, φ x • (𝓕⁻ h) x := by
    simp [hψ]
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

/-! ### Entire extension of Fourier integrals with Gaussian decay -/

/-- A Gaussian times an exponential is integrable. -/
theorem integrable_exp_gauss_linear (s : ℝ) :
    Integrable (fun t : ℝ => Real.exp (-(Real.pi / 2) * t ^ 2 + s * t)) volume := by
  have h := (integrable_cexp_quadratic (b := ((Real.pi / 2 : ℝ) : ℂ))
    (by rw [Complex.ofReal_re]; positivity) (s : ℂ) 0).norm
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [pow_two]

/-- The Fourier–Laplace transform of a density with Gaussian decay is entire. -/
theorem differentiable_fourierLaplace {ρ : ℝ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (hρ : ∀ᵐ t ∂volume, ρ t ≤ Real.exp (-(Real.pi / 2) * t ^ 2)) :
    Differentiable ℂ (fun z : ℂ =>
      ∫ t : ℝ, (ρ t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * z * t)) := by
  set ν : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (ρ t)) with hν
  have hlt : ∀ᵐ t ∂(volume : Measure ℝ), ENNReal.ofReal (ρ t) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  -- every real exponential is integrable for the measure with density `ρ`
  have hall : ∀ s : ℝ, Integrable (fun t : ℝ => Real.exp (s * t)) ν := by
    intro s
    rw [hν, integrable_withDensity_iff_integrable_smul' hρm.ennreal_ofReal hlt]
    refine (integrable_exp_gauss_linear s).mono' (by fun_prop) ?_
    filter_upwards [hρ] with t ht
    rw [ENNReal.toReal_ofReal (hρ0 t), smul_eq_mul,
      Real.norm_of_nonneg (mul_nonneg (hρ0 t) (Real.exp_pos _).le), Real.exp_add]
    exact mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le
  -- the integral is a complex moment generating function
  have hF : ∀ z : ℂ, ∫ t : ℝ, (ρ t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * z * t) =
      ProbabilityTheory.complexMGF id ν (2 * Real.pi * Complex.I * z) := by
    intro z
    rw [ProbabilityTheory.complexMGF, hν,
      integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal hlt]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [ENNReal.toReal_ofReal (hρ0 t)]
  have hd : Differentiable ℂ (ProbabilityTheory.complexMGF id ν) := by
    intro z
    have huniv : ProbabilityTheory.integrableExpSet id ν = Set.univ :=
      Set.eq_univ_of_forall hall
    have hz : z ∈ {z : ℂ | z.re ∈ interior (ProbabilityTheory.integrableExpSet id ν)} := by
      simp [huniv]
    exact (ProbabilityTheory.differentiableOn_complexMGF z hz).differentiableAt
      ((isOpen_interior.preimage Complex.continuous_re).mem_nhds hz)
  have hcomp : (fun z : ℂ =>
      ∫ t : ℝ, (ρ t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * z * t)) =
      fun z => ProbabilityTheory.complexMGF id ν (2 * Real.pi * Complex.I * z) :=
    funext hF
  rw [hcomp]
  exact hd.comp (differentiable_id.const_mul _)

/-! ### The generator -/

/-- The entire extension of the generator: the Fourier–Laplace transform
`z ↦ ∫ √w(t) e^{2π i z t} dt` of `√w`. -/
def generatorExt (w : Weight) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (Real.sqrt (w.density t) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * z * t)

/-- The generator `x ↦ Re ∫ √w(t) e^{2π i x t} dt`; for an even weight the integral is
already real (`generatorExt_ofReal`). -/
def generator (w : Weight) (x : ℝ) : ℝ := (generatorExt w x).re

/-- Below the Gaussian `exp (-π t²)`, the root of the density is below `exp (-π t² / 2)`. -/
theorem sqrt_density_le_of_gauss {w : Weight}
    (hg : ∀ᵐ t ∂volume, w.density t ≤ LimitAssembly.gaussWeight.density t) :
    ∀ᵐ t ∂volume, Real.sqrt (w.density t) ≤ Real.exp (-(Real.pi / 2) * t ^ 2) := by
  filter_upwards [hg] with t ht
  calc Real.sqrt (w.density t) ≤ Real.sqrt (Real.exp (-Real.pi * t ^ 2)) :=
        Real.sqrt_le_sqrt ht
    _ = Real.exp (-(Real.pi / 2) * t ^ 2) := by
      rw [← Real.exp_half]
      congr 1
      ring

/-- The generator extends to an entire function. -/
theorem differentiable_generatorExt {w : Weight}
    (hg : ∀ᵐ t ∂volume, w.density t ≤ LimitAssembly.gaussWeight.density t) :
    Differentiable ℂ (generatorExt w) :=
  differentiable_fourierLaplace w.measurable.sqrt (fun _ => Real.sqrt_nonneg _)
    (sqrt_density_le_of_gauss hg)

theorem weightRoot_integrable {w : Weight}
    (hg : ∀ᵐ t ∂volume, w.density t ≤ LimitAssembly.gaussWeight.density t) :
    Integrable (weightRoot w) volume := by
  refine (integrable_exp_gauss_linear 0).mono' (weightRoot_measurable w).aestronglyMeasurable ?_
  filter_upwards [sqrt_density_le_of_gauss hg] with t ht
  simpa [weightRoot_norm] using ht

theorem weightRoot_memLp (w : Weight) : MemLp (weightRoot w) 2 volume :=
  (Lp.memLp (weightedL2_isometryEquiv w (weightedCharacter w 0))).ae_eq
    (weightedL2_isometryEquiv_constant w)

/-- On the real line the entire extension is the inverse Fourier integral of `√w`. -/
theorem fourierInv_weightRoot (w : Weight) (x : ℝ) :
    𝓕⁻ (weightRoot w) x = generatorExt w x := by
  rw [Real.fourierInv_eq', generatorExt]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [weightRoot, smul_eq_mul]
  rw [mul_comm]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

/-- For an even weight the entire extension is real on the real line. -/
theorem conj_generatorExt {w : Weight} (heven : ∀ t, w.density (-t) = w.density t) (x : ℝ) :
    conj (generatorExt w x) = generatorExt w x := by
  unfold generatorExt
  rw [← integral_conj, ← integral_neg_eq_self (fun t : ℝ => (Real.sqrt (w.density t) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * x * t)) volume]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [map_mul, Complex.conj_ofReal, heven, ← Complex.exp_conj, Complex.conj_ofNat,
    Complex.conj_I]
  congr 2
  push_cast
  ring

/-- For an even weight the entire extension restricts to the (real) generator. -/
theorem generatorExt_ofReal {w : Weight} (heven : ∀ t, w.density (-t) = w.density t) (x : ℝ) :
    generatorExt w x = ((generator w x : ℝ) : ℂ) :=
  (Complex.conj_eq_iff_re.mp (conj_generatorExt heven x)).symm

/-- For an even weight the entire extension is even. -/
theorem generatorExt_neg {w : Weight} (heven : ∀ t, w.density (-t) = w.density t) (z : ℂ) :
    generatorExt w (-z) = generatorExt w z := by
  unfold generatorExt
  rw [← integral_neg_eq_self (fun t : ℝ => (Real.sqrt (w.density t) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * z * t)) volume]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [heven]
  congr 2
  push_cast
  ring

/-- For an even weight the generator is even. -/
theorem generator_neg {w : Weight} (heven : ∀ t, w.density (-t) = w.density t) (x : ℝ) :
    generator w (-x) = generator w x := by
  unfold generator
  rw [Complex.ofReal_neg, generatorExt_neg heven]

/-! ### The unitary from `L²(w)` to `L²(ℝ)` -/

/-- The unitary `L²(w) → L²(ℝ)`: multiplication by `√w` followed by the inverse Fourier
transform. -/
def returnIsometry (w : Weight) : WeightedL2 w ≃ₗᵢ[ℂ] LebesgueL2 :=
  (weightedL2_isometryEquiv w).trans (Lp.fourierTransformₗᵢ ℝ ℂ).symm

theorem returnIsometry_apply (w : Weight) (u : WeightedL2 w) :
    returnIsometry w u =
      (Lp.fourierTransformₗᵢ ℝ ℂ).symm (weightedL2_isometryEquiv w u) := rfl

/-- The image of a weighted character is a translate of the image of the constant. -/
theorem returnIsometry_weightedCharacter (w : Weight) (ξ : ℝ) :
    returnIsometry w (weightedCharacter w ξ) =
      translateL2 (-ξ) (returnIsometry w (weightedCharacter w 0)) := by
  rw [returnIsometry_apply, returnIsometry_apply, weightedCharacter_image_eq_modulate,
    inverseFourier_modulate_L2]

/-- The image of the constant function is (the class of) the generator. -/
theorem returnIsometry_constant_ae {w : Weight} (heven : ∀ t, w.density (-t) = w.density t)
    (hg : ∀ᵐ t ∂volume, w.density t ≤ LimitAssembly.gaussWeight.density t) :
    (returnIsometry w (weightedCharacter w 0) : ℝ → ℂ) =ᵐ[volume]
      fun x => ((generator w x : ℝ) : ℂ) := by
  have hL : weightedL2_isometryEquiv w (weightedCharacter w 0) =
      (weightRoot_memLp w).toLp (weightRoot w) :=
    Lp.ext ((weightedL2_isometryEquiv_constant w).trans (MemLp.coeFn_toLp _).symm)
  rw [returnIsometry_apply, hL]
  filter_upwards [fourierInv_toLp_ae (weightRoot_integrable hg) (weightRoot_memLp w)] with x hx
  rw [hx, fourierInv_weightRoot, generatorExt_ofReal heven]

/-- The image of the character with frequency `ξ` is the translate by `-ξ` of the
generator. -/
theorem returnIsometry_weightedCharacter_ae {w : Weight}
    (heven : ∀ t, w.density (-t) = w.density t)
    (hg : ∀ᵐ t ∂volume, w.density t ≤ LimitAssembly.gaussWeight.density t) (ξ : ℝ) :
    (returnIsometry w (weightedCharacter w ξ) : ℝ → ℂ) =ᵐ[volume]
      fun x => ((generator w (x - -ξ) : ℝ) : ℂ) := by
  rw [returnIsometry_weightedCharacter]
  exact (translateL2_ae (-ξ) _).trans
    ((measurePreserving_sub_right volume (-ξ)).quasiMeasurePreserving.ae_eq_comp
      (returnIsometry_constant_ae heven hg))

end Return

open Return in
/-- **Returning to translates.** A sharp weighted exponential basis yields a real-valued
generator `f ∈ L²(ℝ)`, not a.e. zero and extending to an entire function, and an injective
sequence `lam` such that the translates `f (· - lam n)` form a Schauder basis of the complex
and of the real `L²(ℝ)`, with all partial sum projections bounded by `C`. -/
theorem translates_of_weightedExponentialBasisSharp {C : ℝ}
    (h : WeightedExponentialBasisSharp C) :
    ∃ (f : ℝ → ℝ) (lam : ℕ → ℝ), MemLp f 2 volume ∧ ¬ f =ᵐ[volume] 0 ∧
      (∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ x : ℝ, F x = f x) ∧ Function.Injective lam ∧
      (∃ b : SchauderBasis ℂ (Lp ℂ 2 (volume : Measure ℝ)),
        (∀ n, (b n : ℝ → ℂ) =ᵐ[volume] fun x => ((f (x - lam n) : ℝ) : ℂ)) ∧
        ∀ N, ‖b.proj N‖ ≤ C) ∧
      (∃ b : SchauderBasis ℝ (Lp ℝ 2 (volume : Measure ℝ)),
        (∀ n, (b n : ℝ → ℝ) =ᵐ[volume] fun x => f (x - lam n)) ∧
        ∀ N, ‖b.proj N‖ ≤ C) := by
  obtain ⟨w, μ, heven, hgauss, hμ, hdense, hprefix⟩ := h
  -- the Schauder basis of weighted characters in `L²(w)`
  have hne : ∀ n, weightedCharacter w (μ n) ≠ 0 := fun n =>
    LinearIndependent.ne_zero n (characters_linearIndependent w μ hμ)
  obtain ⟨b₀, hb₀, hb₀C⟩ := StructuredBases.exists_schauderBasis_of_prefix_bound
    (fun n => weightedCharacter w (μ n)) hne hdense
    (fun N a => by simpa only [SchauderTranslates.finitePrefix_apply] using hprefix N a)
  -- the generator is in `L²`, and not zero
  set g : LebesgueL2 := returnIsometry w (weightedCharacter w 0) with hgdef
  have hgF : (g : ℝ → ℂ) =ᵐ[volume] fun x => ((generator w x : ℝ) : ℂ) :=
    returnIsometry_constant_ae heven hgauss
  have hzero : weightedCharacter w 0 ≠ 0 :=
    LinearIndependent.ne_zero 0 (characters_linearIndependent w id Function.injective_id)
  have hg0 : g ≠ 0 := fun h0 =>
    hzero ((returnIsometry w).injective (h0.trans (map_zero _).symm))
  have hmemC : MemLp (fun x => ((generator w x : ℝ) : ℂ)) 2 volume := (Lp.memLp g).ae_eq hgF
  have hmem : MemLp (generator w) 2 volume := by simpa using hmemC.re
  have hnz : ¬ generator w =ᵐ[volume] 0 := by
    intro h0
    apply hg0
    apply Lp.ext
    filter_upwards [hgF, h0, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x h1 h2 h3
    rw [h1, h2, h3]
    simp
  -- the transported basis consists of translates of the generator
  let b : SchauderBasis ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
    StructuredBases.transport b₀ (returnIsometry w).toContinuousLinearEquiv
  have hb : ∀ n, (b n : ℝ → ℂ) =ᵐ[volume]
      fun x => ((generator w (x - -μ n) : ℝ) : ℂ) := by
    intro n
    have h1 : b n = returnIsometry w (weightedCharacter w (μ n)) := by
      change returnIsometry w (b₀ n) = _
      rw [hb₀]
    rw [h1]
    exact returnIsometry_weightedCharacter_ae heven hgauss (μ n)
  have hbC : ∀ N, ‖b.proj N‖ ≤ C := fun N =>
    (StructuredBases.norm_transport_proj b₀ (returnIsometry w) N).le.trans (hb₀C N)
  -- the same translates form a basis over the real scalars
  obtain ⟨b', hb', hb'C⟩ :=
    StructuredBases.exists_real_translate_basis (generator w) (fun n => -μ n) b hb
  exact ⟨generator w, fun n => -μ n, hmem, hnz,
    ⟨generatorExt w, differentiable_generatorExt hgauss, generatorExt_ofReal heven⟩,
    neg_injective.comp hμ, ⟨b, hb, hbC⟩, ⟨b', hb', fun N => (hb'C N).trans (hbC N)⟩⟩

end SchauderTranslates.Sharp
