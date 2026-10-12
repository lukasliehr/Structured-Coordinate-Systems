import Lean_Code.SchauderTranslates.Lp.DisjointNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α : Type*} [MeasurableSpace α]
variable (p : ℝ≥0∞) (μ : Measure α) (s : Set α) (hs : MeasurableSet s)

include hs in
theorem lpExtend_memLp (f : Lp ℂ p (μ.restrict s)) :
    MemLp (s.indicator (f : α → ℂ)) p μ :=
  (memLp_indicator_iff_restrict (μ := μ) (p := p) (f := (f : α → ℂ)) hs).mpr (Lp.memLp f)

def lpExtendByZero : Lp ℂ p (μ.restrict s) →ₗ[ℂ] Lp ℂ p μ where
  toFun f := (lpExtend_memLp p μ s hs f).toLp _
  map_add' f g := by
    apply Lp.ext
    have hfg : ∀ᵐ x ∂μ, x ∈ s → (f + g) x = f x + g x :=
      (ae_restrict_iff' hs).mp (Lp.coeFn_add f g)
    filter_upwards [MemLp.coeFn_toLp (lpExtend_memLp p μ s hs (f + g)),
      Lp.coeFn_add ((lpExtend_memLp p μ s hs f).toLp _)
        ((lpExtend_memLp p μ s hs g).toLp _),
      MemLp.coeFn_toLp (lpExtend_memLp p μ s hs f),
      MemLp.coeFn_toLp (lpExtend_memLp p μ s hs g), hfg]
      with x hsum hadd hf hg hfg
    rw [hsum, hadd, Pi.add_apply, hf, hg]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      exact hfg hx
    · simp [Set.indicator_of_notMem hx]
  map_smul' a f := by
    apply Lp.ext
    have haf : ∀ᵐ x ∂μ, x ∈ s → (a • f) x = a • f x :=
      (ae_restrict_iff' hs).mp (Lp.coeFn_smul a f)
    filter_upwards [MemLp.coeFn_toLp (lpExtend_memLp p μ s hs (a • f)),
      Lp.coeFn_smul a ((lpExtend_memLp p μ s hs f).toLp _),
      MemLp.coeFn_toLp (lpExtend_memLp p μ s hs f), haf]
      with x hsum ha hf haf
    simp only [RingHom.id_apply, hsum, ha, Pi.smul_apply, hf]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx]
      exact haf hx
    · simp [Set.indicator_of_notMem hx]

theorem lpExtendByZero_ae (f : Lp ℂ p (μ.restrict s)) :
    lpExtendByZero p μ s hs f =ᵐ[μ] s.indicator f :=
  MemLp.coeFn_toLp (lpExtend_memLp p μ s hs f)

theorem lpExtendByZero_supported (f : Lp ℂ p (μ.restrict s)) :
    SupportedOn (lpExtendByZero p μ s hs f) s := by
  filter_upwards [lpExtendByZero_ae p μ s hs f] with x hx
  intro hout
  rw [hx, Set.indicator_of_notMem hout]

variable [Fact (1 ≤ p)]

theorem lpExtendByZero_norm (f : Lp ℂ p (μ.restrict s)) :
    ‖lpExtendByZero p μ s hs f‖ = ‖f‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (lpExtendByZero_ae p μ s hs f),
    eLpNorm_indicator_eq_eLpNorm_restrict hs, Lp.norm_def]

def lpExtendByZeroIsometry : Lp ℂ p (μ.restrict s) →ₗᵢ[ℂ] Lp ℂ p μ where
  toLinearMap := lpExtendByZero p μ s hs
  norm_map' := lpExtendByZero_norm p μ s hs

end SchauderTranslates.LpConstruction
