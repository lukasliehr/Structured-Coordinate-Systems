import Mathlib

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {𝕜 α E : Type*} [RCLike 𝕜] [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

def lpIndicator (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) : Lp E 2 μ :=
  (MemLp.indicator hs (Lp.memLp f)).toLp (s.indicator f)

theorem lpIndicator_ae (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    (lpIndicator s hs f : α → E) =ᵐ[μ] s.indicator f :=
  (MemLp.indicator hs (Lp.memLp f)).coeFn_toLp

theorem lpIndicator_norm_le (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    ‖lpIndicator s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [lpIndicator_ae s hs f] with x hx
  rw [hx]
  by_cases h : x ∈ s
  · simp [h]
  · simp [h]

def lpIndicatorLinear (s : Set α) (hs : MeasurableSet s) : Lp E 2 μ →ₗ[𝕜] Lp E 2 μ where
  toFun := lpIndicator s hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [lpIndicator_ae s hs (f + g), lpIndicator_ae s hs f,
      lpIndicator_ae s hs g, Lp.coeFn_add f g,
      Lp.coeFn_add (lpIndicator s hs f) (lpIndicator s hs g)] with x hfg hf hg ha hb
    change lpIndicator s hs (f + g) x = (lpIndicator s hs f + lpIndicator s hs g) x
    rw [hfg, hb]
    simp only [Pi.add_apply]
    rw [hf, hg]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, ha, Pi.add_apply]
    · simp only [Set.indicator_of_notMem hx, add_zero]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [lpIndicator_ae s hs (c • f), lpIndicator_ae s hs f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (lpIndicator s hs f)] with x hcf hf ha hb
    by_cases hx : x ∈ s <;> simp [hcf, hf, ha, hb, hx]

/-- Multiplication by an indicator is a contraction on the vector-valued L² space. -/
def lpIndicatorCLM (s : Set α) (hs : MeasurableSet s) : Lp E 2 μ →L[𝕜] Lp E 2 μ :=
  (lpIndicatorLinear s hs).mkContinuous 1 (fun f => by
    change ‖lpIndicator s hs f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using lpIndicator_norm_le s hs f)

theorem lpIndicatorCLM_ae (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    (lpIndicatorCLM (𝕜 := 𝕜) s hs f : α → E) =ᵐ[μ] s.indicator f :=
  lpIndicator_ae s hs f

theorem lpIndicatorCLM_norm_le (s : Set α) (hs : MeasurableSet s) :
    ‖lpIndicatorCLM (𝕜 := 𝕜) (E := E) (μ := μ) s hs‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖lpIndicator s hs f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using lpIndicator_norm_le s hs f

theorem lpIndicatorCLM_idempotent (s : Set α) (hs : MeasurableSet s) (f : Lp E 2 μ) :
    lpIndicatorCLM (𝕜 := 𝕜) s hs (lpIndicatorCLM (𝕜 := 𝕜) s hs f) = lpIndicatorCLM (𝕜 := 𝕜) s hs f := by
  apply Lp.ext
  filter_upwards [lpIndicatorCLM_ae (𝕜 := 𝕜) s hs f,
    lpIndicatorCLM_ae (𝕜 := 𝕜) s hs (lpIndicatorCLM (𝕜 := 𝕜) s hs f)] with x hf hff
  by_cases hx : x ∈ s <;> simp [hff, hf, hx]

/-- The indicator contraction is symmetric for both real and complex Hilbert spaces. -/
theorem lpIndicatorCLM_symmetric (s : Set α) (hs : MeasurableSet s) (f g : Lp E 2 μ) :
    inner 𝕜 (lpIndicatorCLM (𝕜 := 𝕜) s hs f) g =
      inner 𝕜 f (lpIndicatorCLM (𝕜 := 𝕜) s hs g) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpIndicatorCLM_ae (𝕜 := 𝕜) s hs f,
    lpIndicatorCLM_ae (𝕜 := 𝕜) s hs g] with x hf hg
  by_cases hx : x ∈ s <;> simp [hf, hg, hx]

end SchauderTranslates
