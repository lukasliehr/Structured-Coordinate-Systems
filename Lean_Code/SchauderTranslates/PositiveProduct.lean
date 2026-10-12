import Lean_Code.SchauderTranslates.Contracts

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace SchauderTranslates

theorem multipliable_of_summable_deficit (a : ℕ → ℝ)
    (ha : ∀ n, a n ≤ 1) (hs : Summable (fun n => 1 - a n)) : Multipliable a := by
  have hn : Summable (fun n => ‖a n - 1‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (ha _)), neg_sub] using hs
  simpa only [add_sub_cancel] using multipliable_one_add_of_summable hn

theorem tprod_pos_of_summable_deficit (a : ℕ → ℝ)
    (hpos : ∀ n, 0 < a n) (ha : ∀ n, a n ≤ 1)
    (hs : Summable (fun n => 1 - a n)) : 0 < ∏' n, a n := by
  have hn : Summable (fun n => ‖a n - 1‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (ha _)), neg_sub] using hs
  have hne : (∏' n, a n) ≠ 0 := by
    simpa only [add_sub_cancel] using
      tprod_one_add_ne_zero_of_summable
        (f := fun n => a n - 1) (fun n => by simpa using (hpos n).ne') hn
  exact lt_of_le_of_ne (tprod_nonneg (fun n => (hpos n).le)) hne.symm

theorem prod_range_bounds (a : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1) (N : ℕ) :
    0 ≤ ∏ n ∈ Finset.range N, a n ∧ (∏ n ∈ Finset.range N, a n) ≤ 1 :=
  ⟨Finset.prod_nonneg (fun n _ => hpos n),
    Finset.prod_le_one (fun n _ => hpos n) (fun n _ => ha n)⟩

theorem one_sub_prod_le_sum_deficit (a : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ a n) (ha : ∀ n, a n ≤ 1) (N : ℕ) :
    1 - ∏ n ∈ Finset.range N, a n ≤ ∑ n ∈ Finset.range N, (1 - a n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hp := (prod_range_bounds a hpos ha N).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr (ha N))]

/-- Tonelli in a form that is convenient for real integrable deficits. -/
theorem ae_summable_norm_of_integral_norm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : ℕ → α → ℝ)
    (hi : ∀ n, Integrable (f n) μ)
    (hs : Summable (fun n => ∫ x, ‖f n x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun n => ‖f n x‖) := by
  apply summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl (fun n => (hi n).1)
  simp_rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun x => norm_nonneg _)) hs]
  exact ENNReal.ofReal_ne_top

section Measure
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def partialWeight (w₀ : α → ℝ) (W : ℕ → α → ℝ) (N : ℕ) (x : α) : ℝ :=
  w₀ x * ∏ n ∈ Finset.range N, W n x

def limitWeight (w₀ : α → ℝ) (W : ℕ → α → ℝ) (x : α) : ℝ :=
  w₀ x * ∏' n, W n x

/-- Summable losses measured against a positive fixed reference weight yield pointwise
summable deficits with respect to the original measure. -/
theorem ae_summable_deficits
    (w₀ : α → ℝ) (W : ℕ → α → ℝ)
    (hw : Integrable w₀ μ) (hp : ∀ᵐ x ∂μ, 0 < w₀ x)
    (hW : ∀ n, Measurable (W n)) (hWpos : ∀ n x, 0 < W n x)
    (hWle : ∀ n x, W n x ≤ 1)
    {δ : ℕ → ℝ} (hδ : Summable δ)
    (hcost : ∀ n, ∫ x, w₀ x * (1 - W n x) ∂μ ≤ δ n) :
    ∀ᵐ x ∂μ, Summable (fun n => 1 - W n x) := by
  let D (n : ℕ) (x : α) := w₀ x * (1 - W n x)
  have hnonneg (n : ℕ) : ∀ᵐ x ∂μ, 0 ≤ D n x := by
    filter_upwards [hp] with x hx
    exact mul_nonneg hx.le (sub_nonneg.mpr (hWle n x))
  have hi (n : ℕ) : Integrable (D n) μ := by
    apply hw.mono' (hw.1.mul ((measurable_const.sub (hW n)).aestronglyMeasurable))
    filter_upwards [hp, hnonneg n] with x hx hd
    change ‖D n x‖ ≤ w₀ x
    rw [Real.norm_of_nonneg hd]
    dsimp [D]
    nlinarith [hWpos n x]
  have hn (n : ℕ) : ∫ x, ‖D n x‖ ∂μ = ∫ x, D n x ∂μ :=
    integral_congr_ae ((hnonneg n).mono (fun x hx => Real.norm_of_nonneg hx))
  have hs : Summable (fun n => ∫ x, ‖D n x‖ ∂μ) :=
    hδ.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
      (fun n => by rw [hn]; exact hcost n)
  filter_upwards [ae_summable_norm_of_integral_norm D hi hs, hp,
    ae_all_iff.mpr hnonneg] with x hx hpx hnpx
  have hx' : Summable (fun n => w₀ x * (1 - W n x)) := by
    simpa only [Real.norm_of_nonneg (hnpx _)] using hx
  exact (summable_mul_left_iff hpx.ne').mp hx'

theorem partialWeight_integrable
    (w₀ : α → ℝ) (W : ℕ → α → ℝ) (hw : Integrable w₀ μ)
    (hp : ∀ᵐ x ∂μ, 0 < w₀ x) (hW : ∀ n, Measurable (W n))
    (hWpos : ∀ n x, 0 < W n x) (hWle : ∀ n x, W n x ≤ 1) (N : ℕ) :
    Integrable (partialWeight w₀ W N) μ := by
  apply hw.mono'
  · exact hw.1.mul ((Finset.measurable_prod (Finset.range N)
      (fun n _ => hW n)).aestronglyMeasurable)
  filter_upwards [hp] with x hx
  change ‖w₀ x * ∏ n ∈ Finset.range N, W n x‖ ≤ w₀ x
  obtain ⟨h0, h1⟩ := prod_range_bounds (fun n => W n x)
    (fun n => (hWpos n x).le) (fun n => hWle n x) N
  rw [Real.norm_of_nonneg (mul_nonneg hx.le h0)]
  nlinarith

theorem partialWeight_tendsto
    (w₀ : α → ℝ) (W : ℕ → α → ℝ) (hWle : ∀ n x, W n x ≤ 1)
    (hs : ∀ᵐ x ∂μ, Summable (fun n => 1 - W n x)) :
    ∀ᵐ x ∂μ, Tendsto (fun N => partialWeight w₀ W N x) atTop (𝓝 (limitWeight w₀ W x)) := by
  filter_upwards [hs] with x hx
  exact tendsto_const_nhds.mul
    (multipliable_of_summable_deficit (fun n => W n x) (fun n => hWle n x) hx).hasProd.tendsto_prod_nat

theorem limitWeight_bounds
    (w₀ : α → ℝ) (W : ℕ → α → ℝ)
    (hp : ∀ᵐ x ∂μ, 0 < w₀ x)
    (hWpos : ∀ n x, 0 < W n x) (hWle : ∀ n x, W n x ≤ 1)
    (hs : ∀ᵐ x ∂μ, Summable (fun n => 1 - W n x)) :
    ∀ᵐ x ∂μ, 0 < limitWeight w₀ W x ∧ limitWeight w₀ W x ≤ w₀ x := by
  filter_upwards [hp, hs, partialWeight_tendsto w₀ W hWle hs] with x hx hsum hlim
  refine ⟨mul_pos hx (tprod_pos_of_summable_deficit _
    (fun n => hWpos n x) (fun n => hWle n x) hsum), ?_⟩
  apply le_of_tendsto' hlim
  intro N
  dsimp [partialWeight]
  have h1 := (prod_range_bounds (fun n => W n x)
    (fun n => (hWpos n x).le) (fun n => hWle n x) N).2
  nlinarith

theorem partialWeight_mass_lower
    (w₀ : α → ℝ) (W : ℕ → α → ℝ) (hw : Integrable w₀ μ)
    (hp : ∀ᵐ x ∂μ, 0 < w₀ x) (hW : ∀ n, Measurable (W n))
    (hWpos : ∀ n x, 0 < W n x) (hWle : ∀ n x, W n x ≤ 1)
    {δ : ℕ → ℝ} (hcost : ∀ n, ∫ x, w₀ x * (1 - W n x) ∂μ ≤ δ n)
    (N : ℕ) :
    (∫ x, w₀ x ∂μ) - ∑ n ∈ Finset.range N, δ n ≤ ∫ x, partialWeight w₀ W N x ∂μ := by
  have hi := partialWeight_integrable w₀ W hw hp hW hWpos hWle N
  have hD (n : ℕ) : Integrable (fun x => w₀ x * (1 - W n x)) μ := by
    apply hw.mono' (hw.1.mul ((measurable_const.sub (hW n)).aestronglyMeasurable))
    filter_upwards [hp] with x hx
    change ‖w₀ x * (1 - W n x)‖ ≤ w₀ x
    rw [Real.norm_of_nonneg (mul_nonneg hx.le (sub_nonneg.mpr (hWle n x)))]
    nlinarith [hWpos n x]
  have he : (∫ x, w₀ x - partialWeight w₀ W N x ∂μ) ≤
      ∫ x, ∑ n ∈ Finset.range N, w₀ x * (1 - W n x) ∂μ := by
    apply integral_mono_ae (hw.sub hi) (integrable_finsetSum _ (fun n _ => hD n))
    filter_upwards [hp] with x hx
    change w₀ x - partialWeight w₀ W N x ≤ _
    rw [← Finset.mul_sum]
    have hb := mul_le_mul_of_nonneg_left
      (one_sub_prod_le_sum_deficit (fun n => W n x)
        (fun n => (hWpos n x).le) (fun n => hWle n x) N) hx.le
    simpa only [mul_sub, mul_one, partialWeight] using hb
  rw [integral_sub hw hi, integral_finsetSum _ (fun n _ => hD n)] at he
  have hc := Finset.sum_le_sum (s := Finset.range N) (fun n _ => hcost n)
  linarith

/-- Full positive-product limit theorem, including the mass and L¹ bounds.
The measure is arbitrary; taking Lebesgue measure gives the paper's version. -/
theorem positive_limit_weight
    (w₀ : α → ℝ) (W : ℕ → α → ℝ) (hw : Integrable w₀ μ)
    (hp : ∀ᵐ x ∂μ, 0 < w₀ x) (hW : ∀ n, Measurable (W n))
    (hWpos : ∀ n x, 0 < W n x) (hWle : ∀ n x, W n x ≤ 1)
    {δ : ℕ → ℝ} (hδ : Summable δ) (hδpos : ∀ n, 0 ≤ δ n)
    (hcost : ∀ n, ∫ x, w₀ x * (1 - W n x) ∂μ ≤ δ n) :
    Integrable (limitWeight w₀ W) μ ∧
    (∀ᵐ x ∂μ, 0 < limitWeight w₀ W x ∧ limitWeight w₀ W x ≤ w₀ x) ∧
    (∫ x, w₀ x ∂μ) - ∑' n, δ n ≤ ∫ x, limitWeight w₀ W x ∂μ ∧
    Tendsto (fun N => ∫ x, ‖partialWeight w₀ W N x - limitWeight w₀ W x‖ ∂μ)
      atTop (𝓝 0) := by
  have hs := ae_summable_deficits w₀ W hw hp hW hWpos hWle hδ hcost
  have ht := partialWeight_tendsto w₀ W hWle hs
  have hb := limitWeight_bounds w₀ W hp hWpos hWle hs
  have hm : AEStronglyMeasurable (limitWeight w₀ W) μ :=
    hw.1.mul (Measurable.tprod hW).aestronglyMeasurable
  have hi : Integrable (limitWeight w₀ W) μ := hw.mono' hm (by
    filter_upwards [hb] with x hx
    simpa only [Real.norm_of_nonneg hx.1.le] using hx.2)
  have hpN (N : ℕ) : ∀ᵐ x ∂μ,
      0 ≤ partialWeight w₀ W N x ∧ partialWeight w₀ W N x ≤ w₀ x := by
    filter_upwards [hp] with x hx
    obtain ⟨h0, h1⟩ := prod_range_bounds (fun n => W n x)
      (fun n => (hWpos n x).le) (fun n => hWle n x) N
    exact ⟨mul_nonneg hx.le h0, by dsimp [partialWeight]; nlinarith⟩
  have hiN (N : ℕ) := partialWeight_integrable w₀ W hw hp hW hWpos hWle N
  have htI : Tendsto (fun N => ∫ x, partialWeight w₀ W N x ∂μ)
      atTop (𝓝 (∫ x, limitWeight w₀ W x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence w₀ (fun N => (hiN N).1) hw _ ht
    intro N
    filter_upwards [hpN N] with x hx
    simpa only [Real.norm_of_nonneg hx.1] using hx.2
  refine ⟨hi, hb, ?_, ?_⟩
  · apply ge_of_tendsto' htI
    intro N
    calc
      (∫ x, w₀ x ∂μ) - ∑' n, δ n ≤
          (∫ x, w₀ x ∂μ) - ∑ n ∈ Finset.range N, δ n :=
        sub_le_sub_left (hδ.sum_le_tsum _ (fun n _ => hδpos n)) _
      _ ≤ ∫ x, partialWeight w₀ W N x ∂μ :=
        partialWeight_mass_lower w₀ W hw hp hW hWpos hWle hcost N
  · have hc := tendsto_integral_of_dominated_convergence
      (μ := μ) (f := fun _ => (0 : ℝ)) w₀
      (fun N => ((hiN N).1.sub hm).norm) hw
      (fun N => ?_) (by
        filter_upwards [ht] with x hx
        simpa using (hx.sub (tendsto_const_nhds (x := limitWeight w₀ W x))).norm)
    · simpa using hc
    · filter_upwards [hpN N, hb] with x hx hy
      change ‖‖partialWeight w₀ W N x - limitWeight w₀ W x‖‖ ≤ w₀ x
      rw [Real.norm_of_nonneg (norm_nonneg _), Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hy.1]

end Measure
end SchauderTranslates
