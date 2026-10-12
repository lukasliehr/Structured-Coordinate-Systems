import Lean_Code.PositiveTranslates.StageMachine
import Lean_Code.PositiveTranslates.Analytic.Gaussian

/-!
# Gaussian smoothing of compact step functions in `Lᵖ`

For an interval indicator `𝟙_[a,b)` the Gaussian smoothing satisfies the explicit pointwise
bound
`|H_σ(x) - 𝟙_[a,b)(x)| ≤ exp (-(x-a)²/σ²) + exp (-(x-b)²/σ²)`,
hence `‖H_σ - 𝟙_[a,b)‖_p ≤ 2 (σ √(π/p))^{1/p}`. By linearity, every compact step function
`h` satisfies `‖H_σ - h‖_p ≤ C σ^{1/p}`.

The final statement `exists_entire_smoothing` packages everything the analytic stages need.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ComplexOrder BigOperators Real

namespace StructuredBases.PositiveTranslates
open SchauderTranslates.LpConstruction

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### The pointwise bound for interval indicators -/

/-- The Gaussian bump `exp (-(x - c)²/σ²)`. -/
def gaussBump (σ c x : ℝ) : ℝ := Real.exp (-((x - c) ^ 2) / σ ^ 2)

theorem gaussBump_nonneg (σ c x : ℝ) : 0 ≤ gaussBump σ c x := (Real.exp_pos _).le

theorem continuous_gaussBump (σ c : ℝ) : Continuous (gaussBump σ c) := by
  unfold gaussBump
  fun_prop

/-- If exactly one of `x`, `u` lies in `[a,b)`, the Gaussian at `x - u` is dominated by
Gaussian bumps at the two endpoints. -/
theorem gaussReal_sub_le {σ : ℝ} (hσ : 0 < σ) {a b x u : ℝ}
    (hxu : u ∈ Ico a b ↔ x ∉ Ico a b) :
    gaussReal σ (x - u) ≤
      gaussBump σ a x * gaussReal σ (u - a) + gaussBump σ b x * gaussReal σ (u - b) := by
  have hA : ∀ c, 0 ≤ (x - c) * (c - u) →
      gaussReal σ (x - u) ≤ gaussBump σ c x * gaussReal σ (u - c) := by
    intro c hc
    have h := gaussReal_add_le hσ hc
    rw [show x - c + (c - u) = x - u by ring] at h
    rw [← gaussReal_neg σ (u - c), neg_sub]
    exact h
  have hnn : ∀ c, 0 ≤ gaussBump σ c x * gaussReal σ (u - c) := fun c =>
    mul_nonneg (gaussBump_nonneg σ c x) (gaussReal_nonneg hσ.le _)
  by_cases hx : x ∈ Ico a b
  · have hu : u ∉ Ico a b := fun h => (hxu.mp h) hx
    by_cases hua : u < a
    · have h := hA a (mul_nonneg (by linarith [hx.1]) (by linarith))
      linarith [hnn b]
    · have hub : b ≤ u := by
        by_contra h
        exact hu ⟨not_lt.mp hua, not_le.mp h⟩
      have h := hA b (by nlinarith [hx.2])
      linarith [hnn a]
  · have hu : u ∈ Ico a b := hxu.mpr hx
    by_cases hxa : x < a
    · have h := hA a (by nlinarith [hu.1])
      linarith [hnn b]
    · have hxb : b ≤ x := by
        by_contra h
        exact hx ⟨not_lt.mp hxa, not_le.mp h⟩
      have h := hA b (mul_nonneg (by linarith) (by linarith [hu.2]))
      linarith [hnn a]

theorem setIntegral_gaussReal_le {σ : ℝ} (hσ : 0 < σ) {a b x : ℝ} {D : Set ℝ}
    (hD : MeasurableSet D) (hDx : ∀ u ∈ D, (u ∈ Ico a b ↔ x ∉ Ico a b)) :
    ∫ u in D, gaussReal σ (x - u) ≤ gaussBump σ a x + gaussBump σ b x := by
  have hint : ∀ c, Integrable (fun u => gaussReal σ (u - c)) volume := fun c =>
    (integrable_gaussReal hσ).comp_sub_right c
  have hintx : Integrable (fun u => gaussReal σ (x - u)) volume :=
    (integrable_gaussReal hσ).comp_sub_left x
  have hR : Integrable (fun u => gaussBump σ a x * gaussReal σ (u - a) +
      gaussBump σ b x * gaussReal σ (u - b)) volume :=
    ((hint a).const_mul _).add ((hint b).const_mul _)
  calc
    ∫ u in D, gaussReal σ (x - u)
        ≤ ∫ u in D, (gaussBump σ a x * gaussReal σ (u - a) +
            gaussBump σ b x * gaussReal σ (u - b)) :=
      setIntegral_mono_on hintx.integrableOn hR.integrableOn hD
        (fun u hu => gaussReal_sub_le hσ (hDx u hu))
    _ ≤ ∫ u, (gaussBump σ a x * gaussReal σ (u - a) +
            gaussBump σ b x * gaussReal σ (u - b)) :=
      setIntegral_le_integral hR (Eventually.of_forall fun u => add_nonneg
        (mul_nonneg (gaussBump_nonneg σ a x) (gaussReal_nonneg hσ.le _))
        (mul_nonneg (gaussBump_nonneg σ b x) (gaussReal_nonneg hσ.le _)))
    _ = gaussBump σ a x + gaussBump σ b x := by
      rw [integral_add ((hint a).const_mul _) ((hint b).const_mul _), integral_const_mul,
        integral_const_mul, integral_sub_right_eq_self (gaussReal σ) a,
        integral_sub_right_eq_self (gaussReal σ) b, integral_gaussReal hσ]
      ring

/-- The smoothed indicator of `[a,b)` on the real line. -/
def atomSmooth (σ a b x : ℝ) : ℝ := ∫ u in Ico a b, gaussReal σ (x - u)

theorem abs_atomSmooth_sub_indicator_le {σ : ℝ} (hσ : 0 < σ) (a b x : ℝ) :
    |atomSmooth σ a b x - (Ico a b).indicator (fun _ => (1 : ℝ)) x| ≤
      gaussBump σ a x + gaussBump σ b x := by
  have hintx : Integrable (fun u => gaussReal σ (x - u)) volume :=
    (integrable_gaussReal hσ).comp_sub_left x
  have htot : ∫ u, gaussReal σ (x - u) = 1 := by
    rw [integral_sub_left_eq_self (gaussReal σ) volume x]
    exact integral_gaussReal hσ
  have hnn : ∀ D : Set ℝ, 0 ≤ ∫ u in D, gaussReal σ (x - u) := fun D =>
    integral_nonneg fun u => gaussReal_nonneg hσ.le _
  by_cases hx : x ∈ Ico a b
  · have hsplit := integral_add_compl (measurableSet_Ico (a := a) (b := b)) hintx
    rw [htot] at hsplit
    have hle := setIntegral_gaussReal_le hσ (measurableSet_Ico (a := a) (b := b)).compl
      (x := x) (fun u hu => ⟨fun h => absurd h hu, fun h => absurd hx h⟩)
    rw [Set.indicator_of_mem hx]
    have h : atomSmooth σ a b x - 1 = -∫ u in (Ico a b)ᶜ, gaussReal σ (x - u) := by
      unfold atomSmooth
      linarith
    rw [h, abs_neg, abs_of_nonneg (hnn _)]
    exact hle
  · have hle := setIntegral_gaussReal_le hσ (measurableSet_Ico (a := a) (b := b))
      (x := x) (fun u hu => ⟨fun _ => hx, fun _ => hu⟩)
    rw [Set.indicator_of_notMem hx, sub_zero]
    unfold atomSmooth
    rw [abs_of_nonneg (hnn _)]
    exact hle

theorem gaussSmooth_indicator (σ a b x : ℝ) :
    gaussSmooth σ ((Ico a b).indicator fun _ => (1 : ℂ)) x = (atomSmooth σ a b x : ℂ) := by
  unfold gaussSmooth atomSmooth
  rw [← integral_complex_ofReal, ← integral_indicator measurableSet_Ico]
  congr 1
  funext u
  by_cases hu : u ∈ Ico a b
  · simp [hu, ← Complex.ofReal_sub, gaussKernel_ofReal]
  · simp [hu]

/-! ### `Lᵖ` norms of Gaussian bumps -/

theorem toReal_pos_of_fact (hp : p ≠ ∞) : 0 < p.toReal :=
  ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp

theorem integrable_norm_gaussBump_rpow (hp : p ≠ ∞) {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    Integrable (fun x => ‖gaussBump σ c x‖ ^ p.toReal) volume ∧
      ∫ x, ‖gaussBump σ c x‖ ^ p.toReal = σ * √(π / p.toReal) := by
  have hP : 0 < p.toReal := toReal_pos_of_fact hp
  have hpow : ∀ x, ‖gaussBump σ c x‖ ^ p.toReal =
      Real.exp (-(p.toReal / σ ^ 2) * (x - c) ^ 2) := by
    intro x
    rw [Real.norm_of_nonneg (gaussBump_nonneg σ c x), gaussBump, ← Real.exp_mul]
    congr 1
    field_simp
  have hb : 0 < p.toReal / σ ^ 2 := by positivity
  constructor
  · simp_rw [hpow]
    exact (integrable_exp_neg_mul_sq hb).comp_sub_right c
  · simp_rw [hpow]
    rw [integral_sub_right_eq_self (fun x => Real.exp (-(p.toReal / σ ^ 2) * x ^ 2)) c,
      integral_gaussian]
    have h : π / (p.toReal / σ ^ 2) = σ ^ 2 * (π / p.toReal) := by
      field_simp
    rw [h, Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]

theorem memLp_gaussBump (hp : p ≠ ∞) {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    MemLp (gaussBump σ c) p volume :=
  (integrable_norm_rpow_iff (continuous_gaussBump σ c).aestronglyMeasurable
    (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp).mp
    (integrable_norm_gaussBump_rpow hp hσ c).1

theorem eLpNorm_gaussBump (hp : p ≠ ∞) {σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    eLpNorm (gaussBump σ c) p volume = ENNReal.ofReal ((σ * √(π / p.toReal)) ^ p.toReal⁻¹) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
    (memLp_gaussBump hp hσ c), (integrable_norm_gaussBump_rpow hp hσ c).2]

/-! ### Interval atoms -/

theorem integrable_indicator_Ico_one (a b : ℝ) :
    Integrable ((Ico a b).indicator fun _ => (1 : ℂ)) volume :=
  (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (by simp [Real.volume_Ico]))

theorem exists_gaussSmooth_atom (hp : p ≠ ∞) {σ : ℝ} (hσ : 0 < σ) (ab : ℝ × ℝ) :
    ∃ Hlp : LebesgueLp p,
      (Hlp : ℝ → ℂ) =ᵐ[volume] (fun x : ℝ => gaussSmooth σ (intervalAtom p ab) x) ∧
      ‖Hlp - intervalAtom p ab‖ ≤ 2 * (σ * √(π / p.toReal)) ^ p.toReal⁻¹ := by
  have heq : gaussSmooth σ (intervalAtom p ab) =
      gaussSmooth σ ((Ico ab.1 ab.2).indicator fun _ => (1 : ℂ)) :=
    gaussSmooth_congr_ae (intervalAtom_ae p ab)
  have hsupp : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ Icc (-(|ab.1| + |ab.2|)) (|ab.1| + |ab.2|) →
      (Ico ab.1 ab.2).indicator (fun _ => (1 : ℂ)) u = 0 := by
    refine Eventually.of_forall fun u hu => Set.indicator_of_notMem (fun h => hu ⟨?_, ?_⟩) _
    · linarith [neg_abs_le ab.1, abs_nonneg ab.2, h.1]
    · linarith [le_abs_self ab.2, abs_nonneg ab.1, h.2]
  have hdiff : Differentiable ℂ (gaussSmooth σ ((Ico ab.1 ab.2).indicator fun _ => (1 : ℂ))) :=
    differentiable_gaussSmooth hσ (integrable_indicator_Ico_one ab.1 ab.2) hsupp
  set dfun : ℝ → ℂ := fun x => gaussSmooth σ (intervalAtom p ab) x - intervalAtom p ab x
    with hdfun
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖dfun x‖ ≤ gaussBump σ ab.1 x + gaussBump σ ab.2 x := by
    filter_upwards [intervalAtom_ae p ab] with x hx
    have hind : (Ico ab.1 ab.2).indicator (fun _ => (1 : ℂ)) x =
        (((Ico ab.1 ab.2).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) := by
      by_cases hxm : x ∈ Ico ab.1 ab.2 <;> simp [hxm]
    simp only [hdfun]
    rw [heq, gaussSmooth_indicator, hx, hind, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_atomSmooth_sub_indicator_le hσ ab.1 ab.2 x
  have hmeas : AEStronglyMeasurable dfun volume := by
    refine AEStronglyMeasurable.sub ?_ (Lp.aestronglyMeasurable _)
    rw [heq]
    exact (hdiff.continuous.comp Complex.continuous_ofReal).aestronglyMeasurable
  have hmem : MemLp dfun p volume :=
    ((memLp_gaussBump hp hσ ab.1).add (memLp_gaussBump hp hσ ab.2)).mono' hmeas hbound
  refine ⟨hmem.toLp dfun + intervalAtom p ab, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add (hmem.toLp dfun) (intervalAtom p ab), hmem.coeFn_toLp]
      with x hx hd
    rw [hx, Pi.add_apply, hd]
    simp [hdfun]
  · rw [add_sub_cancel_right, Lp.norm_toLp]
    have hB0 : 0 ≤ (σ * √(π / p.toReal)) ^ p.toReal⁻¹ := by positivity
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    calc
      eLpNorm dfun p volume
          ≤ eLpNorm (fun x => gaussBump σ ab.1 x + gaussBump σ ab.2 x) p volume :=
        eLpNorm_mono_ae_real hbound
      _ ≤ eLpNorm (gaussBump σ ab.1) p volume + eLpNorm (gaussBump σ ab.2) p volume :=
        eLpNorm_add_le (continuous_gaussBump σ ab.1).aestronglyMeasurable
          (continuous_gaussBump σ ab.2).aestronglyMeasurable Fact.out
      _ = ENNReal.ofReal (2 * (σ * √(π / p.toReal)) ^ p.toReal⁻¹) := by
        rw [eLpNorm_gaussBump hp hσ, eLpNorm_gaussBump hp hσ, ← ENNReal.ofReal_add hB0 hB0,
          two_mul]

/-! ### Compact step functions -/

omit [Fact (1 ≤ p)] in
theorem integrable_of_isCompactStep {h : LebesgueLp p} (hh : IsCompactStep p h) :
    Integrable (h : ℝ → ℂ) volume := by
  change h ∈ Submodule.span ℝ (Set.range (intervalAtom p)) at hh
  induction hh using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨ab, rfl⟩ := hz
    exact (integrable_indicator_Ico_one ab.1 ab.2).congr (intervalAtom_ae p ab).symm
  | zero => exact (integrable_zero ℝ ℂ volume).congr (Lp.coeFn_zero ℂ p volume).symm
  | add x y _ _ hx hy => exact (hx.add hy).congr (Lp.coeFn_add x y).symm
  | smul a x _ hx => exact (hx.smul a).congr (Lp.coeFn_smul a x).symm

/-- Gaussian smoothing approximates every compact step function in `Lᵖ`, at the rate
`σ^{1/p}`. -/
theorem exists_gaussSmooth_approx_of_isCompactStep (hp : p ≠ ∞) {h : LebesgueLp p}
    (hh : IsCompactStep p h) :
    ∃ C : ℝ, ∀ σ : ℝ, 0 < σ → ∃ Hlp : LebesgueLp p,
      (Hlp : ℝ → ℂ) =ᵐ[volume] (fun x : ℝ => gaussSmooth σ h x) ∧
      ‖Hlp - h‖ ≤ C * σ ^ p.toReal⁻¹ := by
  change h ∈ Submodule.span ℝ (Set.range (intervalAtom p)) at hh
  induction hh using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨ab, rfl⟩ := hz
    refine ⟨2 * (√(π / p.toReal)) ^ p.toReal⁻¹, fun σ hσ => ?_⟩
    obtain ⟨Hlp, h1, h2⟩ := exists_gaussSmooth_atom hp hσ ab
    refine ⟨Hlp, h1, h2.trans (le_of_eq ?_)⟩
    rw [Real.mul_rpow hσ.le (Real.sqrt_nonneg _)]
    ring
  | zero =>
    refine ⟨0, fun σ hσ => ⟨0, ?_, by simp⟩⟩
    have hsm : gaussSmooth σ ((0 : LebesgueLp p) : ℝ → ℂ) = gaussSmooth σ 0 :=
      gaussSmooth_congr_ae (Lp.coeFn_zero ℂ p volume)
    filter_upwards [Lp.coeFn_zero ℂ p volume] with x hx
    rw [hx, hsm, gaussSmooth_zero]
    rfl
  | add f g hf hg ihf ihg =>
    obtain ⟨C₁, h₁⟩ := ihf
    obtain ⟨C₂, h₂⟩ := ihg
    refine ⟨C₁ + C₂, fun σ hσ => ?_⟩
    obtain ⟨F, hF1, hF2⟩ := h₁ σ hσ
    obtain ⟨G, hG1, hG2⟩ := h₂ σ hσ
    refine ⟨F + G, ?_, ?_⟩
    · have hsm : gaussSmooth σ ((f + g : LebesgueLp p) : ℝ → ℂ) =
          gaussSmooth σ ((f : ℝ → ℂ) + g) := gaussSmooth_congr_ae (Lp.coeFn_add f g)
      filter_upwards [Lp.coeFn_add F G, hF1, hG1] with x hx hFx hGx
      rw [hx, Pi.add_apply, hFx, hGx, hsm,
        gaussSmooth_add hσ (integrable_of_isCompactStep (p := p) hf)
          (integrable_of_isCompactStep (p := p) hg)]
    · calc
        ‖F + G - (f + g)‖ = ‖(F - f) + (G - g)‖ := by
          congr 1
          abel
        _ ≤ ‖F - f‖ + ‖G - g‖ := norm_add_le _ _
        _ ≤ C₁ * σ ^ p.toReal⁻¹ + C₂ * σ ^ p.toReal⁻¹ := add_le_add hF2 hG2
        _ = (C₁ + C₂) * σ ^ p.toReal⁻¹ := by ring
  | smul a f hf ihf =>
    obtain ⟨C, hC⟩ := ihf
    refine ⟨|a| * C, fun σ hσ => ?_⟩
    obtain ⟨F, hF1, hF2⟩ := hC σ hσ
    refine ⟨a • F, ?_, ?_⟩
    · have hsm : gaussSmooth σ ((a • f : LebesgueLp p) : ℝ → ℂ) =
          gaussSmooth σ (a • (f : ℝ → ℂ)) := gaussSmooth_congr_ae (Lp.coeFn_smul a f)
      filter_upwards [Lp.coeFn_smul a F, hF1] with x hx hFx
      rw [hx, Pi.smul_apply, hFx, hsm, gaussSmooth_real_smul, Complex.real_smul]
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
      exact mul_le_mul_of_nonneg_left hF2 (abs_nonneg _)

/-- **Entire smoothing.** Every non-negative compact step function `h` is approximated in
`Lᵖ` by the restriction to `ℝ` of an entire function `H` that is non-negative on `ℝ` and
uniformly small on far right translates of every disc. -/
theorem exists_entire_smoothing (hp : p ≠ ∞) {h : LebesgueLp p} (hh : IsCompactStep p h)
    (hpos : IsNonneg h) {ε : ℝ} (hε : 0 < ε) :
    ∃ (H : ℂ → ℂ) (Hlp : LebesgueLp p), Differentiable ℂ H ∧ (∀ x : ℝ, 0 ≤ H x) ∧
      (Hlp : ℝ → ℂ) =ᵐ[volume] (fun x : ℝ => H x) ∧ ‖Hlp - h‖ ≤ ε ∧
      ∀ (r : ℝ) (ε' : ℝ), 0 < ε' →
        ∃ Λ₀ : ℝ, ∀ lam : ℝ, Λ₀ < lam → ∀ z : ℂ, ‖z‖ ≤ r → ‖H (z + lam)‖ ≤ ε' := by
  have hP : 0 < p.toReal := toReal_pos_of_fact hp
  obtain ⟨C, hC⟩ := exists_gaussSmooth_approx_of_isCompactStep hp hh
  set q : ℝ := ε / (|C| + 1) with hq
  have hq0 : 0 < q := by positivity
  set σ : ℝ := q ^ p.toReal with hσdef
  have hσ : 0 < σ := Real.rpow_pos_of_pos hq0 _
  have hσq : σ ^ p.toReal⁻¹ = q := Real.rpow_rpow_inv hq0.le hP.ne'
  obtain ⟨Hlp, h1, h2⟩ := hC σ hσ
  obtain ⟨R, -, hsupp⟩ := hh.bounded_support
  have hint : Integrable (h : ℝ → ℂ) volume := integrable_of_isCompactStep hh
  refine ⟨gaussSmooth σ h, Hlp, differentiable_gaussSmooth hσ hint hsupp,
    fun x => gaussSmooth_nonneg hσ.le hpos x, h1, h2.trans ?_,
    fun r ε' hε' => exists_gaussSmooth_tail hσ hint hsupp r hε'⟩
  rw [hσq]
  calc
    C * q ≤ |C| * q := mul_le_mul_of_nonneg_right (le_abs_self C) hq0.le
    _ = |C| * ε / (|C| + 1) := by rw [hq]; ring
    _ ≤ ε := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg C]

end StructuredBases.PositiveTranslates
