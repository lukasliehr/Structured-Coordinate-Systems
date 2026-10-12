import Lean_Code.SchauderTranslates.Lp.LpMeasurableEquiv

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.LpConstruction

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)] {μ : Measure α} {ν : Measure β}
variable {F : α → β} {G : β → α}
variable (hF : MeasurePreserving F μ ν) (hG : MeasurePreserving G ν μ)
variable (hGF : G ∘ F =ᵐ[μ] id)

include hF hG hGF

theorem lpMeasurePreserving_ae_inverse (f : Lp ℂ p μ) :
    Lp.compMeasurePreserving F hF (Lp.compMeasurePreserving G hG f) = f := by
  rw [← Lp.compMeasurePreserving_comp_apply f hG hF]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (hG.comp hF), hGF] with x hx hinv
  change Lp.compMeasurePreserving (G ∘ F) (hG.comp hF) f x = f x
  rw [hx]
  change f ((G ∘ F) x) = f x
  rw [hinv]
  rfl

theorem lpMeasurePreserving_ae_surjective :
    Function.Surjective (Lp.compMeasurePreservingₗᵢ ℂ F hF :
      Lp ℂ p ν →ₗᵢ[ℂ] Lp ℂ p μ) := by
  intro f
  exact ⟨Lp.compMeasurePreserving G hG f, lpMeasurePreserving_ae_inverse p hF hG hGF f⟩

/-- Pullback by an almost-everywhere invertible measure-preserving map is
an onto isometry. No global bijection across null complements is needed. -/
def lpMeasurePreservingAeEquiv : Lp ℂ p ν ≃ₗᵢ[ℂ] Lp ℂ p μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ F hF)
    (lpMeasurePreserving_ae_surjective p hF hG hGF)

theorem lpMeasurePreservingAeEquiv_ae (f : Lp ℂ p ν) :
    lpMeasurePreservingAeEquiv p hF hG hGF f =ᵐ[μ] f ∘ F :=
  Lp.coeFn_compMeasurePreserving f hF

theorem lpMeasurePreservingAeEquiv_symm_ae (f : Lp ℂ p μ) :
    (lpMeasurePreservingAeEquiv p hF hG hGF).symm f =ᵐ[ν] f ∘ G := by
  have h : lpMeasurePreservingAeEquiv p hF hG hGF (Lp.compMeasurePreserving G hG f) = f :=
    lpMeasurePreserving_ae_inverse p hF hG hGF f
  have hsymm : (lpMeasurePreservingAeEquiv p hF hG hGF).symm f =
      Lp.compMeasurePreserving G hG f := by
    calc
      _ = (lpMeasurePreservingAeEquiv p hF hG hGF).symm
          (lpMeasurePreservingAeEquiv p hF hG hGF (Lp.compMeasurePreserving G hG f)) :=
        congrArg (lpMeasurePreservingAeEquiv p hF hG hGF).symm h.symm
      _ = _ := LinearIsometryEquiv.symm_apply_apply _ _
  rw [hsymm]
  exact Lp.coeFn_compMeasurePreserving f hG

end SchauderTranslates.LpConstruction
