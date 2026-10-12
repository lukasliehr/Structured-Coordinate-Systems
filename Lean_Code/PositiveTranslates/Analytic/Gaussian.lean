import Mathlib

/-!
# Gaussian smoothing of compactly supported integrable functions

For `σ > 0` let `φ_σ(z) = (√π σ)⁻¹ exp (-z²/σ²)` and, for an integrable function
`h : ℝ → ℂ`,
`H_σ(z) = ∫ h(u) φ_σ(z - u) du` (`gaussSmooth σ h z`), a function of the complex variable `z`.

Main facts (paper, subsection "Entire smoothing"):

* `differentiable_gaussSmooth`: `H_σ` is entire if `h` is integrable and vanishes a.e.
  outside a bounded interval;
* `gaussSmooth_nonneg`: `H_σ` is real and non-negative on `ℝ` if `h ≥ 0` a.e.;
* `norm_gaussSmooth_add_le`, `exists_gaussSmooth_tail`: the complex tail bound
  `sup_{|z| ≤ r} |H_σ(z + λ)| → 0` as `λ → +∞`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ComplexOrder BigOperators Real

namespace StructuredBases.PositiveTranslates

/-! ### The Gaussian density -/

/-- The real Gaussian density `φ_σ(s) = (√π σ)⁻¹ exp (-s²/σ²)`. -/
def gaussReal (σ s : ℝ) : ℝ := (√π * σ)⁻¹ * Real.exp (-(s ^ 2) / σ ^ 2)

theorem gaussReal_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (s : ℝ) : 0 ≤ gaussReal σ s := by
  unfold gaussReal
  positivity

theorem gaussReal_neg (σ s : ℝ) : gaussReal σ (-s) = gaussReal σ s := by
  simp [gaussReal]

theorem gaussReal_eq (σ s : ℝ) :
    gaussReal σ s = (√π * σ)⁻¹ * Real.exp (-(1 / σ ^ 2) * s ^ 2) := by
  unfold gaussReal
  congr 2
  ring

theorem continuous_gaussReal (σ : ℝ) : Continuous (gaussReal σ) := by
  unfold gaussReal
  fun_prop

theorem integrable_gaussReal {σ : ℝ} (hσ : 0 < σ) : Integrable (gaussReal σ) volume := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / σ ^ 2) (by positivity)).const_mul (√π * σ)⁻¹
  refine h.congr (Eventually.of_forall fun s => ?_)
  simp only [gaussReal_eq]

theorem integral_gaussReal {σ : ℝ} (hσ : 0 < σ) : ∫ s, gaussReal σ s = 1 := by
  simp_rw [gaussReal_eq]
  rw [integral_const_mul, integral_gaussian]
  have h : π / (1 / σ ^ 2) = (√π * σ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
    field_simp
  rw [h, Real.sqrt_sq (by positivity)]
  exact inv_mul_cancel₀ (by positivity)

/-- The Gaussian of a sum of two numbers of the same sign splits off one factor. -/
theorem gaussReal_add_le {σ : ℝ} (hσ : 0 < σ) {s t : ℝ} (hst : 0 ≤ s * t) :
    gaussReal σ (s + t) ≤ Real.exp (-(s ^ 2) / σ ^ 2) * gaussReal σ t := by
  unfold gaussReal
  rw [mul_left_comm, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

/-! ### The complex Gaussian kernel -/

/-- The complex Gaussian kernel `φ_σ(z) = (√π σ)⁻¹ exp (-z²/σ²)`. -/
def gaussKernel (σ : ℝ) (z : ℂ) : ℂ :=
  (((√π * σ)⁻¹ : ℝ) : ℂ) * Complex.exp (-(z ^ 2) / (σ : ℂ) ^ 2)

theorem gaussKernel_ofReal (σ s : ℝ) : gaussKernel σ (s : ℂ) = (gaussReal σ s : ℂ) := by
  simp [gaussKernel, gaussReal]

theorem norm_gaussKernel {σ : ℝ} (hσ : 0 < σ) (w : ℂ) :
    ‖gaussKernel σ w‖ = (√π * σ)⁻¹ * Real.exp ((w.im ^ 2 - w.re ^ 2) / σ ^ 2) := by
  unfold gaussKernel
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Complex.norm_exp]
  congr 2
  have h : (-(w ^ 2) / (σ : ℂ) ^ 2) = (((1 / σ ^ 2 : ℝ)) : ℂ) * (-(w ^ 2)) := by
    push_cast
    ring
  rw [h, Complex.re_ofReal_mul]
  simp only [sq, Complex.neg_re, Complex.mul_re]
  ring

theorem hasDerivAt_gaussKernel (σ : ℝ) (z : ℂ) :
    HasDerivAt (gaussKernel σ) (gaussKernel σ z * (-(2 * z) / (σ : ℂ) ^ 2)) z := by
  have h1 : HasDerivAt (fun z : ℂ => -(z ^ 2) / (σ : ℂ) ^ 2) (-(2 * z) / (σ : ℂ) ^ 2) z := by
    have := ((hasDerivAt_pow 2 z).neg).div_const ((σ : ℂ) ^ 2)
    simpa using this
  have h2 := (h1.cexp).const_mul (((√π * σ)⁻¹ : ℝ) : ℂ)
  refine h2.congr_deriv ?_
  unfold gaussKernel
  ring

theorem differentiable_gaussKernel (σ : ℝ) : Differentiable ℂ (gaussKernel σ) :=
  fun z => (hasDerivAt_gaussKernel σ z).differentiableAt

theorem continuous_gaussKernel (σ : ℝ) : Continuous (gaussKernel σ) :=
  (differentiable_gaussKernel σ).continuous

theorem norm_gaussKernel_sub_le {σ : ℝ} (hσ : 0 < σ) (z : ℂ) (u : ℝ) :
    ‖gaussKernel σ (z - u)‖ ≤ (√π * σ)⁻¹ * Real.exp (z.im ^ 2 / σ ^ 2) := by
  rw [norm_gaussKernel hσ]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ (by positivity)
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.sub_re, Complex.ofReal_re]
  nlinarith [sq_nonneg (z.re - u)]

/-! ### Gaussian smoothing -/

/-- Gaussian smoothing `H_σ(z) = ∫ h(u) φ_σ(z - u) du`, as a function on `ℂ`. -/
def gaussSmooth (σ : ℝ) (h : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u : ℝ, h u * gaussKernel σ (z - u)

theorem gaussSmooth_congr_ae {σ : ℝ} {h h' : ℝ → ℂ} (hh : h =ᵐ[volume] h') :
    gaussSmooth σ h = gaussSmooth σ h' := by
  funext z
  apply integral_congr_ae
  filter_upwards [hh] with u hu
  rw [hu]

theorem integrable_gaussSmooth_integrand {σ : ℝ} (hσ : 0 < σ) {h : ℝ → ℂ}
    (hh : Integrable h volume) (z : ℂ) :
    Integrable (fun u : ℝ => h u * gaussKernel σ (z - u)) volume := by
  refine hh.mul_bdd (c := (√π * σ)⁻¹ * Real.exp (z.im ^ 2 / σ ^ 2)) ?_
    (Eventually.of_forall fun u => norm_gaussKernel_sub_le hσ z u)
  exact ((continuous_gaussKernel σ).comp (by fun_prop)).aestronglyMeasurable

theorem gaussSmooth_zero (σ : ℝ) (z : ℂ) : gaussSmooth σ 0 z = 0 := by
  simp [gaussSmooth]

theorem gaussSmooth_add {σ : ℝ} (hσ : 0 < σ) {h₁ h₂ : ℝ → ℂ} (h₁i : Integrable h₁ volume)
    (h₂i : Integrable h₂ volume) (z : ℂ) :
    gaussSmooth σ (h₁ + h₂) z = gaussSmooth σ h₁ z + gaussSmooth σ h₂ z := by
  unfold gaussSmooth
  rw [← integral_add (integrable_gaussSmooth_integrand hσ h₁i z)
    (integrable_gaussSmooth_integrand hσ h₂i z)]
  congr 1
  funext u
  simp [add_mul]

theorem gaussSmooth_real_smul (σ c : ℝ) (h : ℝ → ℂ) (z : ℂ) :
    gaussSmooth σ (c • h) z = c * gaussSmooth σ h z := by
  unfold gaussSmooth
  rw [← integral_const_mul]
  congr 1
  funext u
  simp [mul_assoc]

/-- On the real line the smoothing of a non-negative function is a real integral. -/
theorem gaussSmooth_ofReal_eq {σ : ℝ} {h : ℝ → ℂ} (hpos : ∀ᵐ u ∂volume, 0 ≤ h u) (x : ℝ) :
    gaussSmooth σ h x = ((∫ u, (h u).re * gaussReal σ (x - u) : ℝ) : ℂ) := by
  unfold gaussSmooth
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hpos] with u hu
  have him : (h u).im = 0 := (Complex.nonneg_iff.mp hu).2.symm
  have hre : h u = ((h u).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [← Complex.ofReal_sub, gaussKernel_ofReal]
  conv_lhs => rw [hre]
  push_cast
  rfl

/-- The smoothing of a non-negative function is non-negative on the real line. -/
theorem gaussSmooth_nonneg {σ : ℝ} (hσ : 0 ≤ σ) {h : ℝ → ℂ} (hpos : ∀ᵐ u ∂volume, 0 ≤ h u)
    (x : ℝ) : 0 ≤ gaussSmooth σ h x := by
  rw [gaussSmooth_ofReal_eq hpos]
  apply Complex.zero_le_real.mpr
  apply integral_nonneg_of_ae
  filter_upwards [hpos] with u hu
  exact mul_nonneg (Complex.nonneg_iff.mp hu).1 (gaussReal_nonneg hσ _)

/-- The Gaussian smoothing of an integrable function vanishing a.e. outside a bounded
interval is entire. -/
theorem differentiable_gaussSmooth {σ R : ℝ} (hσ : 0 < σ) {h : ℝ → ℂ}
    (hh : Integrable h volume) (hsupp : ∀ᵐ u ∂volume, u ∉ Icc (-R) R → h u = 0) :
    Differentiable ℂ (gaussSmooth σ h) := by
  intro z₀
  set D : ℂ → ℂ := fun w => gaussKernel σ w * (-(2 * w) / (σ : ℂ) ^ 2) with hD
  have hDcont : Continuous D := (continuous_gaussKernel σ).mul (by fun_prop)
  have hcompact : IsCompact (Metric.closedBall z₀ 1 ×ˢ Icc (-R) R) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hcont2 : Continuous fun q : ℂ × ℝ => D (q.1 - q.2) := hDcont.comp (by fun_prop)
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont2.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (z : ℂ) (u : ℝ) => h u * gaussKernel σ (z - u))
    (F' := fun (z : ℂ) (u : ℝ) => h u * D (z - u)) (x₀ := z₀) (s := Metric.ball z₀ 1)
    (bound := fun u => C * ‖h u‖)
    (Metric.ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => (integrable_gaussSmooth_integrand hσ hh z).aestronglyMeasurable)
    (integrable_gaussSmooth_integrand hσ hh z₀)
    (hh.aestronglyMeasurable.mul
      (hDcont.comp (by fun_prop : Continuous fun u : ℝ => z₀ - (u : ℂ))).aestronglyMeasurable)
    (by
      filter_upwards [hsupp] with u hu z hz
      by_cases huR : u ∈ Icc (-R) R
      · rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (hC (z, u) ⟨Metric.ball_subset_closedBall hz, huR⟩) (norm_nonneg _)
      · simp [hu huR])
    (hh.norm.const_mul C)
    (Eventually.of_forall fun u z _ => by
      have h1 : HasDerivAt (fun z : ℂ => z - (u : ℂ)) 1 z := (hasDerivAt_id z).sub_const (u : ℂ)
      have h2 := ((hasDerivAt_gaussKernel σ (z - u)).comp z h1).const_mul (h u)
      simpa [hD, Function.comp_def] using h2)
  exact key.2.differentiableAt

/-- The explicit complex tail bound of the paper. -/
theorem norm_gaussSmooth_add_le {σ R r : ℝ} (hσ : 0 < σ) {h : ℝ → ℂ}
    (hh : Integrable h volume) (hsupp : ∀ᵐ u ∂volume, u ∉ Icc (-R) R → h u = 0)
    {z : ℂ} (hz : ‖z‖ ≤ r) {lam : ℝ} (hlam : r + R ≤ lam) :
    ‖gaussSmooth σ h (z + lam)‖ ≤
      (∫ u, ‖h u‖) * ((√π * σ)⁻¹ * Real.exp ((r ^ 2 - (lam - r - R) ^ 2) / σ ^ 2)) := by
  unfold gaussSmooth
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_mul_const]
  apply integral_mono_ae (integrable_gaussSmooth_integrand hσ hh _).norm (hh.norm.mul_const _)
  filter_upwards [hsupp] with u hu
  by_cases huR : u ∈ Icc (-R) R
  · simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_gaussKernel hσ]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hre : |z.re| ≤ r := (Complex.abs_re_le_norm z).trans hz
    have him : |z.im| ≤ r := (Complex.abs_im_le_norm z).trans hz
    have h1 : (z + (lam : ℂ) - (u : ℂ)).im = z.im := by simp
    have h2 : (z + (lam : ℂ) - (u : ℂ)).re = z.re + lam - u := by simp
    rw [h1, h2]
    have h3 : lam - r - R ≤ z.re + lam - u := by linarith [(abs_le.mp hre).1, huR.2]
    have h4 : 0 ≤ lam - r - R := by linarith
    have h5 : z.im ^ 2 ≤ r ^ 2 := sq_le_sq' (abs_le.mp him).1 (abs_le.mp him).2
    have h6 : (lam - r - R) ^ 2 ≤ (z.re + lam - u) ^ 2 := by nlinarith
    linarith
  · simp [hu huR]

/-- Far to the right the smoothing is uniformly small on every disc. -/
theorem exists_gaussSmooth_tail {σ R : ℝ} (hσ : 0 < σ) {h : ℝ → ℂ}
    (hh : Integrable h volume) (hsupp : ∀ᵐ u ∂volume, u ∉ Icc (-R) R → h u = 0)
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Λ₀ : ℝ, ∀ lam : ℝ, Λ₀ < lam → ∀ z : ℂ, ‖z‖ ≤ r → ‖gaussSmooth σ h (z + lam)‖ ≤ ε := by
  set A : ℝ := ∫ u, ‖h u‖ with hA
  have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  set c : ℝ := (√π * σ)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  set δ : ℝ := ε / (A * c + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set T : ℝ := |r ^ 2 - σ ^ 2 * Real.log δ| + 1 with hT
  have hT1 : 1 ≤ T := by
    have := abs_nonneg (r ^ 2 - σ ^ 2 * Real.log δ)
    linarith
  refine ⟨r + R + T, fun lam hlam z hz => ?_⟩
  refine (norm_gaussSmooth_add_le hσ hh hsupp hz (by linarith)).trans ?_
  have hexp : Real.exp ((r ^ 2 - (lam - r - R) ^ 2) / σ ^ 2) ≤ δ := by
    rw [← Real.exp_log hδ0]
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    have h1 : T ≤ lam - r - R := by linarith
    have h2 : T ≤ T ^ 2 := by nlinarith
    have h3 : T ^ 2 ≤ (lam - r - R) ^ 2 := by nlinarith
    have h4 : r ^ 2 - σ ^ 2 * Real.log δ ≤ T := by
      have := le_abs_self (r ^ 2 - σ ^ 2 * Real.log δ)
      linarith
    nlinarith
  calc
    A * (c * Real.exp ((r ^ 2 - (lam - r - R) ^ 2) / σ ^ 2)) ≤ A * (c * δ) := by gcongr
    _ = (A * c) * (ε / (A * c + 1)) := by rw [hδ]; ring
    _ ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hA0 hc0.le]

end StructuredBases.PositiveTranslates
