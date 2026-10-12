import Lean_Code.SchauderTranslates.FiberMeanInner
import Lean_Code.SchauderTranslates.Information

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
namespace FiberKernel
variable {S Y : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable {ν : Measure Y} [IsProbabilityMeasure ν] (K : FiberKernel S Y ν)
variable (ρ : Measure S) [IsFiniteMeasure ρ]

/-- The closed slow space inside the actual weighted joint L² space. -/
def slowSpace : Submodule ℂ (Lp ℂ 2 (K.measure ρ)) :=
  (Submodule.span ℂ (Set.range (fun h : BoundedMeasurableComplex S =>
    (h.pullbackFst Y).toL2 (K.measure ρ)))).topologicalClosure

instance slowSpace_complete : CompleteSpace (K.slowSpace ρ) := by
  unfold slowSpace
  infer_instance

theorem slow_mem (h : BoundedMeasurableComplex S) :
    (h.pullbackFst Y).toL2 (K.measure ρ) ∈ K.slowSpace ρ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨h, rfl⟩)

theorem centered_mem_slow_orthogonal (f : BoundedMeasurableComplex (S × Y)) :
    f.toL2 (K.measure ρ) - ((K.meanRepresentative f).pullbackFst Y).toL2 (K.measure ρ) ∈ (K.slowSpace ρ)ᗮ := by
  rw [slowSpace, Submodule.orthogonal_closure]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨h, rfl⟩ := hz
    exact K.centered_slow_inner ρ h f
  | zero => simp
  | add x y hx hy hix hiy => simp [inner_add_left, hix, hiy]
  | smul c x hx hix => simp [inner_smul_left, hix]

/-- Explicit fiber integration equals orthogonal projection onto the completed slow space. -/
theorem mean_eq_starProjection (f : BoundedMeasurableComplex (S × Y)) :
    (K.slowSpace ρ).starProjection (f.toL2 (K.measure ρ)) =
      ((K.meanRepresentative f).pullbackFst Y).toL2 (K.measure ρ) :=
  Submodule.eq_starProjection_of_mem_orthogonal (K.slow_mem ρ _) (K.centered_mem_slow_orthogonal ρ f)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def atoms (f : ι → BoundedMeasurableComplex (S × Y)) : ι → Lp ℂ 2 (K.measure ρ) :=
  fun i => (f i).toL2 (K.measure ρ)

def means (f : ι → BoundedMeasurableComplex (S × Y)) : ι → Lp ℂ 2 (K.measure ρ) :=
  fun i => ((K.meanRepresentative (f i)).pullbackFst Y).toL2 (K.measure ρ)

def centered (f : ι → BoundedMeasurableComplex (S × Y)) : ι → Lp ℂ 2 (K.measure ρ) :=
  fun i => K.atoms ρ f i - K.means ρ f i

theorem means_eq_atomMeans (f : ι → BoundedMeasurableComplex (S × Y)) :
    K.means ρ f = atomMeans (K.slowSpace ρ) (K.atoms ρ f) := by
  funext i
  exact (K.mean_eq_starProjection ρ (f i)).symm

theorem centered_eq_centeredAtoms (f : ι → BoundedMeasurableComplex (S × Y)) :
    K.centered ρ f = centeredAtoms (K.slowSpace ρ) (K.atoms ρ f) := by
  funext i
  simp only [centered, means, atoms, centeredAtoms, Submodule.starProjection_orthogonal_val, K.mean_eq_starProjection]

end FiberKernel

/-- Blueprint `info:identity`, with explicit fiber-integral means and the actual weighted
atom-span projection. The identity is stated on the ambient Hilbert space by extending
slow operators by zero on the orthogonal complement. -/
theorem information_capture_identity {S Y ι : Type*} [MeasurableSpace S] [MeasurableSpace Y]
    [Fintype ι] [DecidableEq ι] {ν : Measure Y} [IsProbabilityMeasure ν]
    (K : FiberKernel S Y ν) (ρ : Measure S) [IsFiniteMeasure ρ]
    (f : ι → BoundedMeasurableComplex (S × Y)) (hC : (Matrix.gram ℂ (K.centered ρ f)).PosDef) :
    Matrix.gram ℂ (K.atoms ρ f) = Matrix.gram ℂ (K.centered ρ f) + Matrix.gram ℂ (K.means ρ f) ∧
      IsUnit (1 + informationOperator (K.means ρ f) (Matrix.gram ℂ (K.centered ρ f))) ∧
      (K.slowSpace ρ).starProjection.comp ((atomSpan (K.atoms ρ f)).starProjection.comp (K.slowSpace ρ).starProjection) =
        captureOperator (K.means ρ f) (Matrix.gram ℂ (K.centered ρ f)) ∧
      captureOperator (K.means ρ f) (Matrix.gram ℂ (K.centered ρ f)) =
        informationOperator (K.means ρ f) (Matrix.gram ℂ (K.centered ρ f)) *
          Ring.inverse (1 + informationOperator (K.means ρ f) (Matrix.gram ℂ (K.centered ρ f))) := by
  rw [K.centered_eq_centeredAtoms] at hC ⊢
  rw [K.means_eq_atomMeans]
  have h := information_capture_resolvent (atomMeans (K.slowSpace ρ) (K.atoms ρ f)) hC
  exact ⟨centered_gram_sum _ _, h.1, slow_capture_projection _ _ hC, h.2⟩

end SchauderTranslates
