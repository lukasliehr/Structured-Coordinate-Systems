import Lean_Code.SchauderTranslates.PiKernel
import Lean_Code.SchauderTranslates.FiberMarginalCapture
import Lean_Code.SchauderTranslates.EngineInfo
import Lean_Code.SchauderTranslates.TagLift

/-!
# Atoms of conditionally independent engines

For finitely many fiber kernels over one slow space, every engine atom is lifted to the
product of all fresh variables. Its slow part is the pullback of the engine's own mean,
its centered part is orthogonal to the whole slow space, centered parts of different
engines are orthogonal, and within one engine the centered Gram is the engine's own.
This is the Hilbert-space content of blueprint `tag:engines`.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace FiberKernel

variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν]
variable {m : ℕ} (K : Fin m → FiberKernel S Y ν) (ρ : Measure S) [IsProbabilityMeasure ρ]

/-- The mean representative of a lifted atom is the engine's own mean representative. -/
theorem meanRepresentative_liftAt_toL2 (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) :
    ((piKernel K).meanRepresentative (liftAt c f)).toL2 ρ =
      ((K c).meanRepresentative f).toL2 ρ := by
  apply BoundedMeasurableComplex.toL2_congr
  exact Eventually.of_forall (fun s => mean_liftAt K c f s)

theorem meanRepresentative_liftAt_pullback_toL2 (c : Fin m)
    (f : BoundedMeasurableComplex (S × Y)) :
    (((piKernel K).meanRepresentative (liftAt c f)).pullbackFst (Fin m → Y)).toL2
        ((piKernel K).measure ρ) =
      (((K c).meanRepresentative f).pullbackFst (Fin m → Y)).toL2 ((piKernel K).measure ρ) := by
  apply BoundedMeasurableComplex.toL2_congr
  exact Eventually.of_forall (fun p => mean_liftAt K c f p.1)

/-- The lifted atom. -/
def engineAtom (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) :
    Lp ℂ 2 ((piKernel K).measure ρ) := (liftAt c f).toL2 ((piKernel K).measure ρ)

/-- Its slow part: the pullback of the engine mean. -/
def engineMean (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) :
    Lp ℂ 2 ((piKernel K).measure ρ) :=
  (((K c).meanRepresentative f).pullbackFst (Fin m → Y)).toL2 ((piKernel K).measure ρ)

/-- Its centered part. -/
def engineCentered (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) :
    Lp ℂ 2 ((piKernel K).measure ρ) := engineAtom K ρ c f - engineMean K ρ c f

theorem engineAtom_eq (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) :
    engineAtom K ρ c f = engineMean K ρ c f + engineCentered K ρ c f := by
  simp [engineCentered]

theorem engineMean_eq_slowLift (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) :
    engineMean K ρ c f = (piKernel K).slowLift ρ (((K c).meanRepresentative f).toL2 ρ) :=
  ((piKernel K).slowLift_bounded ρ _).symm

theorem engineMean_mem (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) :
    engineMean K ρ c f ∈ (piKernel K).slowSpace ρ :=
  (piKernel K).slow_mem ρ _

theorem engineCentered_orthogonal (c : Fin m) (f : BoundedMeasurableComplex (S × Y)) :
    engineCentered K ρ c f ∈ ((piKernel K).slowSpace ρ)ᗮ := by
  have h := (piKernel K).centered_mem_slow_orthogonal ρ (liftAt c f)
  rw [meanRepresentative_liftAt_pullback_toL2] at h
  exact h

theorem engineCentered_inner_slow (c : Fin m) (f : BoundedMeasurableComplex (S × Y))
    (s : Lp ℂ 2 ((piKernel K).measure ρ)) (hs : s ∈ (piKernel K).slowSpace ρ) :
    inner ℂ s (engineCentered K ρ c f) = 0 :=
  Submodule.inner_right_of_mem_orthogonal hs (engineCentered_orthogonal K ρ c f)

/-- Pairing of a mean with an atom of any engine. -/
theorem engineMean_inner_atom (c c' : Fin m) (f g : BoundedMeasurableComplex (S × Y)) :
    inner ℂ (engineMean K ρ c f) (engineAtom K ρ c' g) =
      inner ℂ (((K c).meanRepresentative f).toL2 ρ) (((K c').meanRepresentative g).toL2 ρ) := by
  unfold engineMean engineAtom
  rw [(piKernel K).slow_atom_inner ρ, meanRepresentative_liftAt_toL2]

theorem engineMean_inner_mean (c c' : Fin m) (f g : BoundedMeasurableComplex (S × Y)) :
    inner ℂ (engineMean K ρ c f) (engineMean K ρ c' g) =
      inner ℂ (((K c).meanRepresentative f).toL2 ρ) (((K c').meanRepresentative g).toL2 ρ) := by
  unfold engineMean
  rw [(piKernel K).slow_inner ρ]

/-- Centered parts of different engines are orthogonal. -/
theorem engineCentered_inner_ne {c c' : Fin m} (hcc : c ≠ c')
    (f g : BoundedMeasurableComplex (S × Y)) :
    inner ℂ (engineCentered K ρ c f) (engineCentered K ρ c' g) = 0 := by
  have hUU : inner ℂ (engineAtom K ρ c f) (engineAtom K ρ c' g) =
      inner ℂ (((K c).meanRepresentative f).toL2 ρ) (((K c').meanRepresentative g).toL2 ρ) :=
    inner_liftAt_ne K ρ hcc f g
  have hUT : inner ℂ (engineAtom K ρ c f) (engineMean K ρ c' g) =
      inner ℂ (((K c).meanRepresentative f).toL2 ρ) (((K c').meanRepresentative g).toL2 ρ) := by
    rw [← inner_conj_symm, engineMean_inner_atom, inner_conj_symm]
  simp only [engineCentered, inner_sub_left, inner_sub_right, hUU, hUT, engineMean_inner_atom,
    engineMean_inner_mean]
  ring

/-- Within one engine the centered Gram is the engine's own centered Gram. -/
theorem engineCentered_inner_same (c : Fin m) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → BoundedMeasurableComplex (S × Y)) (p p' : ι) :
    inner ℂ (engineCentered K ρ c (f p)) (engineCentered K ρ c (f p')) =
      inner ℂ ((K c).centered ρ f p) ((K c).centered ρ f p') := by
  have hUU : inner ℂ (engineAtom K ρ c (f p)) (engineAtom K ρ c (f p')) =
      inner ℂ ((f p).toL2 ((K c).measure ρ)) ((f p').toL2 ((K c).measure ρ)) :=
    inner_liftAt_same K ρ c (f p) (f p')
  have hUT : inner ℂ (engineAtom K ρ c (f p)) (engineMean K ρ c (f p')) =
      inner ℂ (((K c).meanRepresentative (f p)).toL2 ρ)
        (((K c).meanRepresentative (f p')).toL2 ρ) := by
    rw [← inner_conj_symm, engineMean_inner_atom, inner_conj_symm]
  have hsingle := congrFun (congrFun ((K c).atoms_gram_eq_centered_add_marginal ρ f) p) p'
  simp only [Matrix.gram_apply, Matrix.add_apply, atoms, marginalMeans] at hsingle
  simp only [engineCentered, inner_sub_left, inner_sub_right, hUU, hUT, engineMean_inner_atom,
    engineMean_inner_mean]
  rw [hsingle]
  ring

end FiberKernel

/-- Families with the same Gram have the same finite prefix bounds. -/
theorem finitePrefixSqBound_of_inner_eq {H H' : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {n : ℕ}
    (u : Fin n → H) (v : Fin n → H') (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j))
    {Q : ℝ} (hv : FinitePrefixSqBound v Q) : FinitePrefixSqBound u Q := by
  have hn (a : Fin n → ℂ) : ‖∑ i, a i • u i‖ ^ 2 = ‖∑ i, a i • v i‖ ^ 2 := by
    rw [norm_sq_sum_eq_inner, norm_sq_sum_eq_inner]
    simp only [h]
  intro k c
  have hk := hv k c
  have hcut (w : Fin n → H) : (∑ i, if i.val < k then c i • w i else 0) =
      ∑ i, (if i.val < k then c i else 0) • w i := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have hcut' : (∑ i, if i.val < k then c i • v i else 0) =
      ∑ i, (if i.val < k then c i else 0) • v i := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hcut, hn, hn c]
  rw [hcut'] at hk
  exact hk

/-- Families with the same Gram have syntheses of the same norm. -/
theorem norm_sum_of_inner_eq {ι H H' : Type*} [Fintype ι] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (u : ι → H) (v : ι → H') (h : ∀ i j, inner ℂ (u i) (u j) = inner ℂ (v i) (v j))
    (a : ι → ℂ) : ‖∑ i, a i • u i‖ = ‖∑ i, a i • v i‖ := by
  have hsq : ‖∑ i, a i • u i‖ ^ 2 = ‖∑ i, a i • v i‖ ^ 2 := by
    rw [norm_sq_sum_eq_inner, norm_sq_sum_eq_inner]
    simp only [h]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

end SchauderTranslates
