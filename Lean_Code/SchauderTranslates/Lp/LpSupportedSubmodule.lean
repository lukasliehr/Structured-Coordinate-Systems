import Lean_Code.SchauderTranslates.Lp.LpExtendByZero

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α : Type*} [MeasurableSpace α]
variable (p : ℝ≥0∞) (μ : Measure α) (s : Set α)

def supportedLpSubmodule : Submodule ℂ (Lp ℂ p μ) where
  carrier := {f | SupportedOn f s}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ p μ] with x hx
    intro _
    exact hx
  add_mem' hf hg := hf.add hg
  smul_mem' a f hf := by
    filter_upwards [hf, Lp.coeFn_smul a f] with x hx ha
    intro hout
    rw [ha, Pi.smul_apply, hx hout, smul_zero]

variable (hs : MeasurableSet s) [Fact (1 ≤ p)]

def lpSupportedIsometry : Lp ℂ p (μ.restrict s) →ₗᵢ[ℂ] supportedLpSubmodule p μ s where
  toLinearMap := (lpExtendByZero p μ s hs).codRestrict _ (lpExtendByZero_supported p μ s hs)
  norm_map' := lpExtendByZero_norm p μ s hs

theorem lpSupportedIsometry_surjective : Function.Surjective (lpSupportedIsometry p μ s hs) := by
  intro f
  have hm : MemLp (f.val : α → ℂ) p (μ.restrict s) := (Lp.memLp f.val).restrict s
  let g := hm.toLp f.val
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Lp.ext
  have hg : s.indicator (g : α → ℂ) =ᵐ[μ] s.indicator (f.val : α → ℂ) :=
    (ae_eq_restrict_iff_indicator_ae_eq hs).mp (MemLp.coeFn_toLp hm)
  filter_upwards [lpExtendByZero_ae p μ s hs g, hg, f.property] with x hx hg hf
  change lpExtendByZero p μ s hs g x = f.val x
  rw [hx, hg]
  by_cases hxs : x ∈ s
  · exact Set.indicator_of_mem hxs _
  · rw [Set.indicator_of_notMem hxs, hf hxs]

/-- Actual Lebesgue Lᵖ on a measurable set is isometrically the submodule
of whole-space classes vanishing almost everywhere outside that set. -/
def lpSupportedEquiv : Lp ℂ p (μ.restrict s) ≃ₗᵢ[ℂ] supportedLpSubmodule p μ s :=
  LinearIsometryEquiv.ofSurjective (lpSupportedIsometry p μ s hs)
    (lpSupportedIsometry_surjective p μ s hs)

theorem lpSupportedEquiv_ae (f : Lp ℂ p (μ.restrict s)) :
    (lpSupportedEquiv p μ s hs f).val =ᵐ[μ] s.indicator f :=
  lpExtendByZero_ae p μ s hs f

end SchauderTranslates.LpConstruction
