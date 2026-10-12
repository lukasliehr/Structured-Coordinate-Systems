import Lean_Code.SchauderTranslates.CoordinateInformation
import Lean_Code.SchauderTranslates.InformationCentering

noncomputable section
open Matrix ContinuousLinearMap
open scoped ComplexOrder InnerProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SchauderTranslates
variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem familyCoordinateProjection_eq (φ : ι → H) (hφ : Matrix.gram ℂ φ = 1) (i₀ : ι) :
    familyCoordinateProjection φ i₀ = (ℂ ∙ φ i₀).starProjection := by
  have ho : Orthonormal ℂ φ := by
    rw [orthonormal_iff_ite]
    intro i j
    exact congrFun (congrFun hφ i) j
  ext h
  rw [familyCoordinateProjection_apply, Submodule.starProjection_unit_singleton ℂ (ho.norm_eq_one i₀)]

theorem familyCoordinate_sum (φ : ι → H) (hφ : Matrix.gram ℂ φ = 1) (i₀ : ι) :
    familyCoordinateComplement φ i₀ + familyCoordinateProjection φ i₀ = (atomSpan φ).starProjection := by
  have h := informationSandwich_two_values φ i₀ 1 1
  simp only [ite_self, Matrix.diagonal_one, one_smul] at h
  rw [← h]
  have hu : LinearIndependent ℂ φ := Matrix.posDef_gram_iff_linearIndependent.mp (hφ ▸ Matrix.PosDef.one)
  rw [atomSpan_projection_formula φ hu, hφ, inv_one]
  rfl

/-- Difference of nested finite-dimensional orthogonal projections is the projection
onto the larger space intersected with the smaller orthogonal complement. -/
theorem finite_projection_difference (F E : Submodule ℂ H)
    [FiniteDimensional ℂ F] [FiniteDimensional ℂ E] (hEF : E ≤ F) :
    (F ⊓ Eᗮ).starProjection = F.starProjection - E.starProjection := by
  ext x
  change (F ⊓ Eᗮ).starProjection x = F.starProjection x - E.starProjection x
  have hpair (K : Submodule ℂ H) [CompleteSpace K] (z : H) (hz : z ∈ K) :
      inner ℂ z (K.starProjection x) = inner ℂ z x := by
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hz]
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · constructor
    · exact F.sub_mem (F.starProjection_apply_mem x) (hEF (E.starProjection_apply_mem x))
    · intro z hz
      rw [inner_sub_right, hpair F z (hEF hz), hpair E z hz, sub_self]
  · intro z hz
    have he : inner ℂ z (E.starProjection x) = 0 :=
      inner_eq_zero_symm.mp (hz.2 _ (E.starProjection_apply_mem x))
    rw [inner_sub_right, inner_sub_right, hpair F z hz.1, he, sub_zero, sub_self]

theorem familyCoordinateComplement_eq (φ : ι → H) (hφ : Matrix.gram ℂ φ = 1) (i₀ : ι) :
    familyCoordinateComplement φ i₀ = (atomSpan φ ⊓ (ℂ ∙ φ i₀)ᗮ).starProjection := by
  have hE : (ℂ ∙ φ i₀) ≤ atomSpan φ := Submodule.span_le.mpr (by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Submodule.subset_span ⟨i₀, rfl⟩)
  rw [finite_projection_difference (atomSpan φ) (ℂ ∙ φ i₀) hE]
  apply eq_sub_iff_add_eq.mpr
  rw [← familyCoordinateProjection_eq φ hφ i₀]
  exact familyCoordinate_sum φ hφ i₀

end SchauderTranslates
