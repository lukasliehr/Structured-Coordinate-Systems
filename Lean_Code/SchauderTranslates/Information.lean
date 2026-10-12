import Lean_Code.SchauderTranslates.InformationCentering
import Lean_Code.SchauderTranslates.InformationResolvent

noncomputable section
open Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProductSpace InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Compression of the actual atom-span projection to the closed slow space. -/
theorem slow_capture_projection (F : Submodule ℂ H) [F.HasOrthogonalProjection]
    (u : ι → H) (hC : (Matrix.gram ℂ (centeredAtoms F u)).PosDef) :
    F.starProjection.comp ((atomSpan u).starProjection.comp F.starProjection) =
      captureOperator (atomMeans F u) (Matrix.gram ℂ (centeredAtoms F u)) := by
  rw [atomSpan_projection_formula u (centered_posDef_implies_independent F u hC)]
  unfold captureOperator informationSandwich
  rw [← centered_gram_sum F u, atomMeans_synthesis_adjoint, atomMeans_synthesis]
  simp only [comp_assoc]

/-- Hilbert-space form of (I1). The means are the orthogonal slow components;
the fiber-integral bridge identifies these with the explicit conditional means. -/
theorem information_capture_hilbert (F : Submodule ℂ H) [F.HasOrthogonalProjection]
    (u : ι → H) (hC : (Matrix.gram ℂ (centeredAtoms F u)).PosDef) :
    Matrix.gram ℂ u = Matrix.gram ℂ (centeredAtoms F u) + Matrix.gram ℂ (atomMeans F u) ∧
      IsUnit (1 + informationOperator (atomMeans F u) (Matrix.gram ℂ (centeredAtoms F u))) ∧
      F.starProjection.comp ((atomSpan u).starProjection.comp F.starProjection) =
        informationOperator (atomMeans F u) (Matrix.gram ℂ (centeredAtoms F u)) *
          Ring.inverse (1 + informationOperator (atomMeans F u) (Matrix.gram ℂ (centeredAtoms F u))) := by
  have h := information_capture_resolvent (atomMeans F u) hC
  exact ⟨centered_gram_sum F u, h.1, (slow_capture_projection F u hC).trans h.2⟩

/-- The information operator has range in the slow space and vanishes on its orthogonal complement. -/
theorem information_slow_support (F : Submodule ℂ H) [F.HasOrthogonalProjection]
    (u : ι → H) (C : Matrix ι ι ℂ) :
    F.starProjection.comp (informationOperator (atomMeans F u) C) = informationOperator (atomMeans F u) C ∧
    (informationOperator (atomMeans F u) C).comp Fᗮ.starProjection = 0 := by
  have hP : F.starProjection.comp F.starProjection = F.starProjection := by
    ext x
    exact Submodule.starProjection_eq_self_iff.mpr (F.starProjection_apply_mem x)
  have hQ : F.starProjection.comp Fᗮ.starProjection = 0 := by
    ext x
    exact F.starProjection_apply_eq_zero_iff.mpr (Fᗮ.starProjection_apply_mem x)
  unfold informationOperator informationSandwich
  rw [atomMeans_synthesis_adjoint, atomMeans_synthesis]
  constructor
  · simp only [← comp_assoc]
    rw [hP]
  · simp only [comp_assoc]
    rw [hQ]
    simp

end SchauderTranslates
