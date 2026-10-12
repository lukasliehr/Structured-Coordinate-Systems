import Lean_Code.SchauderTranslates.SelectiveSource
import Lean_Code.SchauderTranslates.NormalizedCapture

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates.FiberKernel
variable {S Y ι : Type*} [MeasurableSpace S] [MeasurableSpace Y]
variable [Fintype ι] [DecidableEq ι] {ν : Measure Y} [IsProbabilityMeasure ν]
variable (K : FiberKernel S Y ν) (ρ : Measure S) [IsFiniteMeasure ρ]

def marginalMeans (f : ι → BoundedMeasurableComplex (S × Y)) : ι → Lp ℂ 2 ρ :=
  fun i => (K.meanRepresentative (f i)).toL2 ρ

theorem means_gram_eq_marginal (f : ι → BoundedMeasurableComplex (S × Y)) :
    Matrix.gram ℂ (K.means ρ f) = Matrix.gram ℂ (K.marginalMeans ρ f) := by
  apply Matrix.ext
  intro i j
  exact K.slow_inner ρ _ _

theorem atoms_gram_eq_centered_add_marginal (f : ι → BoundedMeasurableComplex (S × Y)) :
    Matrix.gram ℂ (K.atoms ρ f) = Matrix.gram ℂ (K.centered ρ f) + Matrix.gram ℂ (K.marginalMeans ρ f) := by
  have h := centered_gram_sum (K.slowSpace ρ) (K.atoms ρ f)
  rw [← K.centered_eq_centeredAtoms, ← K.means_eq_atomMeans, K.means_gram_eq_marginal] at h
  exact h

theorem marginal_source (f : ι → BoundedMeasurableComplex (S × Y)) :
    ((hilbertSynthesis (K.atoms ρ f))†).comp (K.slowLift ρ).toContinuousLinearMap =
      (hilbertSynthesis (K.marginalMeans ρ f))† := by
  ext h i
  simp only [ContinuousLinearMap.comp_apply, hilbertSynthesis_adjoint_apply, WithLp.ofLp_toLp]
  exact K.atom_slowLift_inner ρ (f i) h

/-- The actual slow compression of the atom-span projection equals the capture
operator formed from explicit marginal means and the actual centered Gram. -/
theorem marginal_capture_projection (f : ι → BoundedMeasurableComplex (S × Y))
    (hC : (Matrix.gram ℂ (K.centered ρ f)).PosDef) :
    (((K.slowLift ρ).toContinuousLinearMap)†).comp
      ((atomSpan (K.atoms ρ f)).starProjection.comp (K.slowLift ρ).toContinuousLinearMap) =
        captureOperator (K.marginalMeans ρ f) (Matrix.gram ℂ (K.centered ρ f)) := by
  have hu : LinearIndependent ℂ (K.atoms ρ f) := by
    apply Matrix.posDef_gram_iff_linearIndependent.mp
    rw [K.atoms_gram_eq_centered_add_marginal]
    exact hC.add_posSemidef (Matrix.posSemidef_gram ℂ _)
  rw [compressed_projection_source _ hu, K.marginal_source, adjoint_adjoint,
    K.atoms_gram_eq_centered_add_marginal, euclideanMatrixOperator_square]
  rfl

end SchauderTranslates.FiberKernel
