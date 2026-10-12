import Lean_Code.PositiveBiorthogonal.BasicLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Positivity localizes support; a positive-measure supported space is not a line. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal Topology ComplexOrder

namespace PositiveBiorthogonal

theorem positive_support_measurable {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} (f : L 𝕜 p) :
    MeasurableSet {x : ℝ | 0 < RCLike.re (f x)} :=
  measurableSet_lt measurable_const
    (RCLike.continuous_re.comp_stronglyMeasurable (Lp.stronglyMeasurable f)).measurable

theorem positive_supported_on_positive_support {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}
    (f : L 𝕜 p) (hf : Nonnegative f) :
    ∀ᵐ x : ℝ, ¬ 0 < RCLike.re (f x) → f x = 0 := by
  filter_upwards [hf] with x hx he
  apply RCLike.ext
  · simpa only [RCLike.zero_re] using
      le_antisymm (le_of_not_gt he) (RCLike.nonneg_iff.mp hx).1
  · simpa only [RCLike.zero_im] using (RCLike.nonneg_iff.mp hx).2

theorem positive_support_measure_pos {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}
    (f : L 𝕜 p) (hf : Nonnegative f) (hf0 : f ≠ 0) :
    0 < volume {x : ℝ | 0 < RCLike.re (f x)} := by
  by_contra! hz
  have hae : ∀ᵐ x : ℝ, ¬ 0 < RCLike.re (f x) := by
    rw [ae_iff]
    simpa only [not_not] using le_antisymm hz bot_le
  apply hf0
  apply Lp.ext
  filter_upwards [positive_supported_on_positive_support f hf, hae,
    Lp.coeFn_zero 𝕜 p (volume : Measure ℝ)] with x hx he hzero
  rw [hzero, Pi.zero_apply, hx he]

theorem zero_product_on_positive {u v : ℝ → ℝ}
    (hu : ∀ᵐ x : ℝ, 0 ≤ u x) (hv : ∀ᵐ x : ℝ, 0 ≤ v x)
    (hi : Integrable (fun x => u x * v x) volume)
    (hz : ∫ x : ℝ, u x * v x = 0) :
    ∀ᵐ x : ℝ, 0 < u x → v x = 0 := by
  have hnonneg : 0 ≤ᵐ[volume] (fun x => u x * v x) := by
    filter_upwards [hu, hv] with x hx hy
    exact mul_nonneg hx hy
  have he := (integral_eq_zero_iff_of_nonneg_ae hnonneg hi).mp hz
  filter_upwards [he] with x hx hp
  exact (mul_eq_zero.mp hx).resolve_left hp.ne'

theorem zero_product_on_positive_rclike {𝕜 : Type*} [RCLike 𝕜] {u v : ℝ → 𝕜}
    (hu : ∀ᵐ x : ℝ, 0 ≤ u x) (hv : ∀ᵐ x : ℝ, 0 ≤ v x)
    (hi : Integrable (fun x => u x * v x) volume)
    (hz : ∫ x : ℝ, u x * v x = 0) :
    ∀ᵐ x : ℝ, 0 < RCLike.re (u x) → v x = 0 := by
  have hre : (fun x => RCLike.re (u x) * RCLike.re (v x)) =ᵐ[volume]
      (fun x => RCLike.re (u x * v x)) := by
    filter_upwards [hu, hv] with x hx hy
    simp [RCLike.mul_re, (RCLike.nonneg_iff.mp hx).2, (RCLike.nonneg_iff.mp hy).2]
  have hire := hi.re.congr hre.symm
  have hzre : ∫ x : ℝ, RCLike.re (u x) * RCLike.re (v x) = 0 := by
    rw [integral_congr_ae hre, integral_re hi, hz]
    simp
  have hzero := zero_product_on_positive
    (hu.mono fun _ hx => (RCLike.nonneg_iff.mp hx).1)
    (hv.mono fun _ hx => (RCLike.nonneg_iff.mp hx).1) hire hzre
  filter_upwards [hzero, hv] with x hx hvx hpos
  apply RCLike.ext
  · simpa using hx hpos
  · simpa using (RCLike.nonneg_iff.mp hvx).2

theorem supported_space_not_one_dimensional {𝕜 : Type*} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : Set ℝ) (hB : MeasurableSet B)
    (hpos : 0 < volume B) (v : L 𝕜 p) :
    ¬ ∀ f : L 𝕜 p, (∀ᵐ x : ℝ, x ∉ B → f x = 0) →
      f ∈ Submodule.span 𝕜 {v} := by
  obtain ⟨E₀, E₁, hm₀, hm₁, hsub₀, hsub₁, hdis, hpos₀, hfin₀, hpos₁, hfin₁⟩ :=
    two_positive_subsets B hB hpos
  let f₀ : L 𝕜 p := indicatorConstLp p hm₀ hfin₀.ne 1
  let f₁ : L 𝕜 p := indicatorConstLp p hm₁ hfin₁.ne 1
  have hs₀ : ∀ᵐ x : ℝ, x ∉ B → f₀ x = 0 := by
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hm₀)
      (hμs := hfin₀.ne) (c := (1 : 𝕜))] with x hx hn
    rw [hx]
    exact indicator_of_notMem (fun he => hn (hsub₀ he)) _
  have hs₁ : ∀ᵐ x : ℝ, x ∉ B → f₁ x = 0 := by
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hm₁)
      (hμs := hfin₁.ne) (c := (1 : 𝕜))] with x hx hn
    rw [hx]
    exact indicator_of_notMem (fun he => hn (hsub₁ he)) _
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (h f₀ hs₀)
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (h f₁ hs₁)
  have ha0 : a ≠ 0 := by
    intro hz
    have hf0 : f₀ = 0 := by simpa [hz] using ha.symm
    exact indicator_ne_zero E₀ hm₀ hfin₀.ne hpos₀ hf0
  apply disjoint_indicators_not_smul E₀ E₁ hm₀ hm₁ hfin₀.ne hfin₁.ne hdis hpos₁ (b / a)
  change f₁ = (b / a) • f₀
  rw [← ha, smul_smul, div_mul_cancel₀ b ha0]
  exact hb.symm

end PositiveBiorthogonal
