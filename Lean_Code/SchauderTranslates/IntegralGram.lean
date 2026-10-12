import Lean_Code.SchauderTranslates.ScalarData

noncomputable section
open MeasureTheory Matrix
open scoped ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {S ι : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]

/-- A finite weighted Gram, written as integrals of actual representatives. -/
def integralGram (w : S → ℝ) (v : ι → S → ℂ) : Matrix ι ι ℂ :=
  fun i j => ∫ x, (w x : ℂ) * star (v i x) * v j x ∂μ

/-- A bounded measurable weight times two bounded measurable representatives is integrable. -/
theorem integralGram_integrand {w : S → ℝ} (hw : Measurable w) {C : ℝ}
    (hC : ∀ x, |w x| ≤ C) {v : ι → S → ℂ} (hv : ∀ i, Measurable (v i))
    (hb : ∀ i, ∃ B : ℝ, ∀ x, ‖v i x‖ ≤ B) (i j : ι) :
    Integrable (fun x => (w x : ℂ) * star (v i x) * v j x) μ := by
  obtain ⟨Bi, hi⟩ := hb i
  obtain ⟨Bj, hj⟩ := hb j
  have hvj : Integrable (v j) μ := Integrable.of_bound (hv j).aestronglyMeasurable Bj
    (Filter.Eventually.of_forall hj)
  have hij : Integrable (fun x => star (v i x) * v j x) μ := hvj.bdd_mul
    (continuous_star.measurable.comp (hv i)).aestronglyMeasurable (Filter.Eventually.of_forall (fun x => by simpa only [norm_star] using hi x))
  have hwC : AEStronglyMeasurable (fun x => (w x : ℂ)) μ :=
    (Complex.continuous_ofReal.measurable.comp hw).aestronglyMeasurable
  have h := hij.bdd_mul hwC
    (Filter.Eventually.of_forall (fun x => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hC x))
  simpa only [mul_assoc] using h

theorem sqrt_weight_memLp {w : S → ℝ} (hw : Measurable w) (h0 : ∀ x, 0 ≤ w x)
    {C : ℝ} (hC : ∀ x, w x ≤ C) {v : S → ℂ} (hv : Measurable v)
    {B : ℝ} (hB : ∀ x, ‖v x‖ ≤ B) :
    MemLp (fun x => (Real.sqrt (w x) : ℂ) * v x) 2 μ := by
  apply MemLp.of_bound (C := Real.sqrt C * B)
  · exact (Complex.continuous_ofReal.measurable.comp hw.sqrt).aestronglyMeasurable.mul hv.aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hC x)) (norm_nonneg (v x))).trans
      (mul_le_mul_of_nonneg_left (hB x) (Real.sqrt_nonneg C))

/-- A nonnegative bounded measurable weight gives a positive semidefinite Gram. -/
theorem integralGram_posSemidef [Fintype ι] {w : S → ℝ} (hw : Measurable w)
    (h0 : ∀ x, 0 ≤ w x) {C : ℝ} (hC : ∀ x, w x ≤ C)
    {v : ι → S → ℂ} (hv : ∀ i, Measurable (v i))
    (hb : ∀ i, ∃ B : ℝ, ∀ x, ‖v i x‖ ≤ B) : (integralGram μ w v).PosSemidef := by
  have hm (i : ι) : MemLp (fun x => (Real.sqrt (w x) : ℂ) * v i x) 2 μ := by
    obtain ⟨B, hB⟩ := hb i
    exact sqrt_weight_memLp μ hw h0 hC (hv i) hB
  let u (i : ι) := (hm i).toLp (fun x => (Real.sqrt (w x) : ℂ) * v i x)
  have he : integralGram μ w v = Matrix.gram ℂ u := by
    ext i j
    rw [Matrix.gram_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hm i).coeFn_toLp, (hm j).coeFn_toLp] with x hi hj
    change _ = inner ℂ (u i x) (u j x)
    rw [hi, hj]
    simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    have hs : (Real.sqrt (w x) : ℂ) ^ 2 = (w x : ℂ) := by exact_mod_cast Real.sq_sqrt (h0 x)
    rw [← hs]
    simp only [Complex.star_def]
    ring
  rw [he]
  exact Matrix.posSemidef_gram ℂ u

end SchauderTranslates
