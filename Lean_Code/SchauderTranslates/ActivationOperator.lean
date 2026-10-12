import Lean_Code.SchauderTranslates.LpIndicator

noncomputable section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Classical.propDecidable

namespace SchauderTranslates
variable {𝕜 α E : Type*} [RCLike 𝕜] [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `I + (B-I) ⊗ M_s`, represented on vector-valued L² instead of using a tensor product. -/
def activationOperator (s : Set α) (hs : MeasurableSet s) (B : E →L[𝕜] E) :
    Lp E 2 μ →L[𝕜] Lp E 2 μ :=
  1 + ((B - 1).compLpL 2 μ).comp (lpIndicatorCLM (𝕜 := 𝕜) s hs)

theorem activationOperator_ae (s : Set α) (hs : MeasurableSet s) (B : E →L[𝕜] E)
    (f : Lp E 2 μ) :
    (activationOperator s hs B f : α → E) =ᵐ[μ]
      (fun x => if x ∈ s then B (f x) else f x) := by
  change ((f + (B - 1).compLpL 2 μ (lpIndicatorCLM (𝕜 := 𝕜) s hs f) : Lp E 2 μ) : α → E) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_add f ((B - 1).compLpL 2 μ (lpIndicatorCLM (𝕜 := 𝕜) s hs f)),
    (B - 1).coeFn_compLpL (lpIndicatorCLM (𝕜 := 𝕜) s hs f),
    lpIndicatorCLM_ae (𝕜 := 𝕜) s hs f] with x ha hb hc
  rw [ha]
  simp only [Pi.add_apply, hb, hc, sub_apply, one_apply_eq_self]
  by_cases hx : x ∈ s <;> simp [hx]

/-- Composition multiplies only the active block. -/
theorem activationOperator_comp (s : Set α) (hs : MeasurableSet s) (B C : E →L[𝕜] E) :
    (activationOperator (μ := μ) s hs B).comp (activationOperator s hs C) =
      activationOperator s hs (B.comp C) := by
  ext1 f
  apply Lp.ext
  filter_upwards [activationOperator_ae s hs B (activationOperator s hs C f),
    activationOperator_ae s hs C f, activationOperator_ae s hs (B.comp C) f] with x hB hC hBC
  change activationOperator s hs B (activationOperator s hs C f) x =
    activationOperator s hs (B.comp C) f x
  rw [hB, hC, hBC]
  by_cases hx : x ∈ s <;> simp [hx]

theorem activationOperator_one (s : Set α) (hs : MeasurableSet s) :
    activationOperator (𝕜 := 𝕜) (E := E) (μ := μ) s hs 1 = 1 := by
  ext1 f
  apply Lp.ext
  filter_upwards [activationOperator_ae s hs (1 : E →L[𝕜] E) f] with x hx
  simpa only [one_apply_eq_self, ite_self] using hx

/-- A prescribed inverse remains an inverse after activation. -/
theorem activationOperator_inverse (s : Set α) (hs : MeasurableSet s) (B C : E →L[𝕜] E)
    (hBC : B.comp C = 1) (hCB : C.comp B = 1) :
    (activationOperator (μ := μ) s hs B).comp (activationOperator s hs C) = 1 ∧
      (activationOperator (μ := μ) s hs C).comp (activationOperator s hs B) = 1 := by
  rw [activationOperator_comp, activationOperator_comp, hBC, hCB,
    activationOperator_one]
  exact ⟨rfl, rfl⟩

theorem activationOperator_symmetric (s : Set α) (hs : MeasurableSet s) (B : E →L[𝕜] E)
    (hB : ∀ x y, inner 𝕜 (B x) y = inner 𝕜 x (B y)) (f g : Lp E 2 μ) :
    inner 𝕜 (activationOperator s hs B f) g = inner 𝕜 f (activationOperator s hs B g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [activationOperator_ae s hs B f, activationOperator_ae s hs B g] with x hf hg
  rw [hf, hg]
  by_cases hx : x ∈ s <;> simp [hx, hB]

theorem activationOperator_norm_le (s : Set α) (hs : MeasurableSet s) (B : E →L[𝕜] E) :
    ‖activationOperator (μ := μ) s hs B‖ ≤ max 1 ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (le_trans zero_le_one (le_max_left _ _))
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [activationOperator_ae s hs B f] with x hx
  rw [hx]
  split_ifs
  · exact (B.le_opNorm (f x)).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · exact le_trans (le_refl _) (by nlinarith [le_max_left (1 : ℝ) ‖B‖, norm_nonneg (f x)])

include 𝕜 in
/-- The vector-valued L² norm as the integral of the squared pointwise norm. -/
theorem lp_norm_sq_integral (f : Lp E 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  simp only [inner_self_eq_norm_sq]

/-- Pointwise coercive bounds survive activation, provided the inactive identity has the same bounds. -/
theorem activationOperator_quadratic_bounds (s : Set α) (hs : MeasurableSet s)
    (B : E →L[𝕜] E) {b c : ℝ} (hb : b ≤ 1) (hc : 1 ≤ c)
    (hlo : ∀ x, b * ‖x‖ ^ 2 ≤ RCLike.re (inner 𝕜 (B x) x))
    (hhi : ∀ x, RCLike.re (inner 𝕜 (B x) x) ≤ c * ‖x‖ ^ 2) (f : Lp E 2 μ) :
    b * ‖f‖ ^ 2 ≤ RCLike.re (inner 𝕜 (activationOperator s hs B f) f) ∧
      RCLike.re (inner 𝕜 (activationOperator s hs B f) f) ≤ c * ‖f‖ ^ 2 := by
  have hn : Integrable (fun x => ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hi := (L2.integrable_inner (𝕜 := 𝕜) (activationOperator s hs B f) f).re
  rw [lp_norm_sq_integral (𝕜 := 𝕜), L2.inner_def, ← integral_re
    (L2.integrable_inner (activationOperator s hs B f) f), ← integral_const_mul, ← integral_const_mul]
  constructor
  · apply integral_mono_ae (hn.const_mul b) hi
    filter_upwards [activationOperator_ae s hs B f] with x hx
    rw [hx]
    split_ifs
    · exact hlo _
    · simpa only [inner_self_eq_norm_sq, one_mul] using
        mul_le_mul_of_nonneg_right hb (sq_nonneg ‖f x‖)
  · apply integral_mono_ae hi (hn.const_mul c)
    filter_upwards [activationOperator_ae s hs B f] with x hx
    rw [hx]
    split_ifs
    · exact hhi _
    · simpa only [inner_self_eq_norm_sq, one_mul] using
        mul_le_mul_of_nonneg_right hc (sq_nonneg ‖f x‖)

end SchauderTranslates
